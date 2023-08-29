/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms

#align_import analysis.locally_convex.weak_dual from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Weak Dual in Topological Vector Spaces

We prove that the weak topology induced by a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` is locally
convex and we explicitly give a neighborhood basis in terms of the family of seminorms
`fun x => ‖B x y‖` for `y : F`.

## Main definitions

* `LinearMap.toSeminorm`: turn a linear form `f : E →ₗ[𝕜] 𝕜` into a seminorm `fun x => ‖f x‖`.
* `LinearMap.toSeminormFamily`: turn a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` into a map
`F → Seminorm 𝕜 E`.

## Main statements

* `LinearMap.hasBasis_weakBilin`: the seminorm balls of `B.toSeminormFamily` form a
neighborhood basis of `0` in the weak topology.
* `LinearMap.toSeminormFamily.withSeminorms`: the topology of a weak space is induced by the
family of seminorms `B.toSeminormFamily`.
* `WeakBilin.locallyConvexSpace`: a space endowed with a weak topology is locally convex.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

weak dual, seminorm
-/


variable {𝕜 E F ι : Type*}

open Topology

section BilinForm

namespace LinearMap

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- Construct a seminorm from a linear form `f : E →ₗ[𝕜] 𝕜` over a normed field `𝕜` by
`fun x => ‖f x‖` -/
def toSeminorm (f : E →ₗ[𝕜] 𝕜) : Seminorm 𝕜 E :=
  (normSeminorm 𝕜 𝕜).comp f
#align linear_map.to_seminorm LinearMap.toSeminorm

theorem coe_toSeminorm {f : E →ₗ[𝕜] 𝕜} : ⇑f.toSeminorm = fun x => ‖f x‖ :=
  rfl
#align linear_map.coe_to_seminorm LinearMap.coe_toSeminorm

@[simp]
theorem toSeminorm_apply {f : E →ₗ[𝕜] 𝕜} {x : E} : f.toSeminorm x = ‖f x‖ :=
  rfl
#align linear_map.to_seminorm_apply LinearMap.toSeminorm_apply

theorem toSeminorm_ball_zero {f : E →ₗ[𝕜] 𝕜} {r : ℝ} :
    Seminorm.ball f.toSeminorm 0 r = { x : E | ‖f x‖ < r } := by
  simp only [Seminorm.ball_zero_eq, toSeminorm_apply]
  -- 🎉 no goals
#align linear_map.to_seminorm_ball_zero LinearMap.toSeminorm_ball_zero

theorem toSeminorm_comp (f : F →ₗ[𝕜] 𝕜) (g : E →ₗ[𝕜] F) :
    f.toSeminorm.comp g = (f.comp g).toSeminorm := by
  ext
  -- ⊢ ↑(Seminorm.comp (toSeminorm f) g) x✝ = ↑(toSeminorm (comp f g)) x✝
  simp only [Seminorm.comp_apply, toSeminorm_apply, coe_comp, Function.comp_apply]
  -- 🎉 no goals
#align linear_map.to_seminorm_comp LinearMap.toSeminorm_comp

/-- Construct a family of seminorms from a bilinear form. -/
def toSeminormFamily (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : SeminormFamily 𝕜 E F := fun y =>
  (B.flip y).toSeminorm
#align linear_map.to_seminorm_family LinearMap.toSeminormFamily

@[simp]
theorem toSeminormFamily_apply {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {x y} : (B.toSeminormFamily y) x = ‖B x y‖ :=
  rfl
#align linear_map.to_seminorm_family_apply LinearMap.toSeminormFamily_apply

end LinearMap

end BilinForm

section Topology

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

variable [Nonempty ι]

variable {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜}

theorem LinearMap.hasBasis_weakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    (𝓝 (0 : WeakBilin B)).HasBasis B.toSeminormFamily.basisSets _root_.id := by
  let p := B.toSeminormFamily
  -- ⊢ Filter.HasBasis (𝓝 0) (SeminormFamily.basisSets (toSeminormFamily B)) _root_ …
  rw [nhds_induced, nhds_pi]
  -- ⊢ Filter.HasBasis (Filter.comap (fun x y => ↑(↑B x) y) (Filter.pi fun i => 𝓝 ( …
  simp only [map_zero, LinearMap.zero_apply]
  -- ⊢ Filter.HasBasis (Filter.comap (fun x y => ↑(↑B x) y) (Filter.pi fun i => 𝓝 0 …
  have h := @Metric.nhds_basis_ball 𝕜 _ 0
  -- ⊢ Filter.HasBasis (Filter.comap (fun x y => ↑(↑B x) y) (Filter.pi fun i => 𝓝 0 …
  have h' := Filter.hasBasis_pi fun _ : F => h
  -- ⊢ Filter.HasBasis (Filter.comap (fun x y => ↑(↑B x) y) (Filter.pi fun i => 𝓝 0 …
  have h'' := Filter.HasBasis.comap (fun x y => B x y) h'
  -- ⊢ Filter.HasBasis (Filter.comap (fun x y => ↑(↑B x) y) (Filter.pi fun i => 𝓝 0 …
  refine' h''.to_hasBasis _ _
  -- ⊢ ∀ (i : Set F × (F → ℝ)), (Set.Finite i.fst ∧ ∀ (i_1 : F), i_1 ∈ i.fst → 0 <  …
  · rintro (U : Set F × (F → ℝ)) hU
    -- ⊢ ∃ i', SeminormFamily.basisSets (toSeminormFamily B) i' ∧ _root_.id i' ⊆ (fun …
    cases' hU with hU₁ hU₂
    -- ⊢ ∃ i', SeminormFamily.basisSets (toSeminormFamily B) i' ∧ _root_.id i' ⊆ (fun …
    simp only [id.def]
    -- ⊢ ∃ i', SeminormFamily.basisSets (toSeminormFamily B) i' ∧ i' ⊆ (fun x y => ↑( …
    let U' := hU₁.toFinset
    -- ⊢ ∃ i', SeminormFamily.basisSets (toSeminormFamily B) i' ∧ i' ⊆ (fun x y => ↑( …
    by_cases hU₃ : U.fst.Nonempty
    -- ⊢ ∃ i', SeminormFamily.basisSets (toSeminormFamily B) i' ∧ i' ⊆ (fun x y => ↑( …
    · have hU₃' : U'.Nonempty := hU₁.toFinset_nonempty.mpr hU₃
      -- ⊢ ∃ i', SeminormFamily.basisSets (toSeminormFamily B) i' ∧ i' ⊆ (fun x y => ↑( …
      refine' ⟨(U'.sup p).ball 0 <| U'.inf' hU₃' U.snd, p.basisSets_mem _ <|
        (Finset.lt_inf'_iff _).2 fun y hy => hU₂ y <| hU₁.mem_toFinset.mp hy, fun x hx y hy => _⟩
      simp only [Set.mem_preimage, Set.mem_pi, mem_ball_zero_iff]
      -- ⊢ ‖↑(↑B x) y‖ < Prod.snd U y
      rw [Seminorm.mem_ball_zero] at hx
      -- ⊢ ‖↑(↑B x) y‖ < Prod.snd U y
      rw [← LinearMap.toSeminormFamily_apply]
      -- ⊢ ↑(toSeminormFamily B y) x < Prod.snd U y
      have hyU' : y ∈ U' := (Set.Finite.mem_toFinset hU₁).mpr hy
      -- ⊢ ↑(toSeminormFamily B y) x < Prod.snd U y
      have hp : p y ≤ U'.sup p := Finset.le_sup hyU'
      -- ⊢ ↑(toSeminormFamily B y) x < Prod.snd U y
      refine' lt_of_le_of_lt (hp x) (lt_of_lt_of_le hx _)
      -- ⊢ Finset.inf' U' hU₃' U.snd ≤ Prod.snd U y
      exact Finset.inf'_le _ hyU'
      -- 🎉 no goals
    rw [Set.not_nonempty_iff_eq_empty.mp hU₃]
    -- ⊢ ∃ i', SeminormFamily.basisSets (toSeminormFamily B) i' ∧ i' ⊆ (fun x y => ↑( …
    simp only [Set.empty_pi, Set.preimage_univ, Set.subset_univ, and_true_iff]
    -- ⊢ ∃ i', SeminormFamily.basisSets (toSeminormFamily B) i'
    exact Exists.intro ((p 0).ball 0 1) (p.basisSets_singleton_mem 0 one_pos)
    -- 🎉 no goals
  rintro U (hU : U ∈ p.basisSets)
  -- ⊢ ∃ i, (Set.Finite i.fst ∧ ∀ (i_1 : F), i_1 ∈ i.fst → 0 < Prod.snd i i_1) ∧ (( …
  rw [SeminormFamily.basisSets_iff] at hU
  -- ⊢ ∃ i, (Set.Finite i.fst ∧ ∀ (i_1 : F), i_1 ∈ i.fst → 0 < Prod.snd i i_1) ∧ (( …
  rcases hU with ⟨s, r, hr, hU⟩
  -- ⊢ ∃ i, (Set.Finite i.fst ∧ ∀ (i_1 : F), i_1 ∈ i.fst → 0 < Prod.snd i i_1) ∧ (( …
  rw [hU]
  -- ⊢ ∃ i, (Set.Finite i.fst ∧ ∀ (i_1 : F), i_1 ∈ i.fst → 0 < Prod.snd i i_1) ∧ (( …
  refine' ⟨(s, fun _ => r), ⟨by simp only [s.finite_toSet], fun y _ => hr⟩, fun x hx => _⟩
  -- ⊢ x ∈ _root_.id (Seminorm.ball (Finset.sup s p) 0 r)
  simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, mem_ball_zero_iff] at hx
  -- ⊢ x ∈ _root_.id (Seminorm.ball (Finset.sup s p) 0 r)
  simp only [id.def, Seminorm.mem_ball, sub_zero]
  -- ⊢ ↑(Finset.sup s (toSeminormFamily B)) x < r
  refine' Seminorm.finset_sup_apply_lt hr fun y hy => _
  -- ⊢ ↑(toSeminormFamily B y) x < r
  rw [LinearMap.toSeminormFamily_apply]
  -- ⊢ ‖↑(↑B x) y‖ < r
  exact hx y hy
  -- 🎉 no goals
#align linear_map.has_basis_weak_bilin LinearMap.hasBasis_weakBilin

theorem LinearMap.weakBilin_withSeminorms (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    WithSeminorms (LinearMap.toSeminormFamily B : F → Seminorm 𝕜 (WeakBilin B)) :=
  SeminormFamily.withSeminorms_of_hasBasis _ B.hasBasis_weakBilin
#align linear_map.weak_bilin_with_seminorms LinearMap.weakBilin_withSeminorms

end Topology

section LocallyConvex

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

variable [Nonempty ι] [NormedSpace ℝ 𝕜] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]

instance WeakBilin.locallyConvexSpace {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} :
    LocallyConvexSpace ℝ (WeakBilin B) :=
  B.weakBilin_withSeminorms.toLocallyConvexSpace

end LocallyConvex
