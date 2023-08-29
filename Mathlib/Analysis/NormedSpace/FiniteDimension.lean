/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.NormedSpace.AddTorsor
import Mathlib.Analysis.NormedSpace.AffineIsometry
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Analysis.NormedSpace.RieszLemma
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Instances.Matrix

#align_import analysis.normed_space.finite_dimension from "leanprover-community/mathlib"@"9425b6f8220e53b059f5a4904786c3c4b50fc057"

/-!
# Finite dimensional normed spaces over complete fields

Over a complete nontrivially normed field, in finite dimension, all norms are equivalent and all
linear maps are continuous. Moreover, a finite-dimensional subspace is always complete and closed.

## Main results:

* `FiniteDimensional.complete` : a finite-dimensional space over a complete field is complete. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution.
* `Submodule.closed_of_finiteDimensional` : a finite-dimensional subspace over a complete field is
  closed
* `FiniteDimensional.proper` : a finite-dimensional space over a proper field is proper. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution. It is however registered as an instance for `𝕜 = ℝ` and `𝕜 = ℂ`. As properness
  implies completeness, there is no need to also register `FiniteDimensional.complete` on `ℝ` or
  `ℂ`.
* `finiteDimensional_of_isCompact_closedBall`: Riesz' theorem: if the closed unit ball is
  compact, then the space is finite-dimensional.

## Implementation notes

The fact that all norms are equivalent is not written explicitly, as it would mean having two norms
on a single space, which is not the way type classes work. However, if one has a
finite-dimensional vector space `E` with a norm, and a copy `E'` of this type with another norm,
then the identities from `E` to `E'` and from `E'`to `E` are continuous thanks to
`LinearMap.continuous_of_finiteDimensional`. This gives the desired norm equivalence.
-/


universe u v w x

noncomputable section

open Set FiniteDimensional TopologicalSpace Filter Asymptotics Classical BigOperators Topology
  NNReal

namespace LinearIsometry

open LinearMap

variable {R : Type*} [Semiring R]

variable {F E₁ : Type*} [SeminormedAddCommGroup F] [NormedAddCommGroup E₁] [Module R E₁]

variable {R₁ : Type*} [Field R₁] [Module R₁ E₁] [Module R₁ F] [FiniteDimensional R₁ E₁]
  [FiniteDimensional R₁ F]

/-- A linear isometry between finite dimensional spaces of equal dimension can be upgraded
    to a linear isometry equivalence. -/
def toLinearIsometryEquiv (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) :
    E₁ ≃ₗᵢ[R₁] F where
  toLinearEquiv := li.toLinearMap.linearEquivOfInjective li.injective h
  norm_map' := li.norm_map'
#align linear_isometry.to_linear_isometry_equiv LinearIsometry.toLinearIsometryEquiv

@[simp]
theorem coe_toLinearIsometryEquiv (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) :
    (li.toLinearIsometryEquiv h : E₁ → F) = li :=
  rfl
#align linear_isometry.coe_to_linear_isometry_equiv LinearIsometry.coe_toLinearIsometryEquiv

@[simp]
theorem toLinearIsometryEquiv_apply (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F)
    (x : E₁) : (li.toLinearIsometryEquiv h) x = li x :=
  rfl
#align linear_isometry.to_linear_isometry_equiv_apply LinearIsometry.toLinearIsometryEquiv_apply

end LinearIsometry

namespace AffineIsometry

open AffineMap

variable {𝕜 : Type*} {V₁ V₂ : Type*} {P₁ P₂ : Type*} [NormedField 𝕜] [NormedAddCommGroup V₁]
  [SeminormedAddCommGroup V₂] [NormedSpace 𝕜 V₁] [NormedSpace 𝕜 V₂] [MetricSpace P₁]
  [PseudoMetricSpace P₂] [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]

variable [FiniteDimensional 𝕜 V₁] [FiniteDimensional 𝕜 V₂]

/-- An affine isometry between finite dimensional spaces of equal dimension can be upgraded
    to an affine isometry equivalence. -/
def toAffineIsometryEquiv [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) :
    P₁ ≃ᵃⁱ[𝕜] P₂ :=
  AffineIsometryEquiv.mk' li (li.linearIsometry.toLinearIsometryEquiv h)
    (Inhabited.default (α := P₁)) fun p => by simp
                                              -- 🎉 no goals
#align affine_isometry.to_affine_isometry_equiv AffineIsometry.toAffineIsometryEquiv

@[simp]
theorem coe_toAffineIsometryEquiv [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂)
    (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) : (li.toAffineIsometryEquiv h : P₁ → P₂) = li :=
  rfl
#align affine_isometry.coe_to_affine_isometry_equiv AffineIsometry.coe_toAffineIsometryEquiv

@[simp]
theorem toAffineIsometryEquiv_apply [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂)
    (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) (x : P₁) : (li.toAffineIsometryEquiv h) x = li x :=
  rfl
#align affine_isometry.to_affine_isometry_equiv_apply AffineIsometry.toAffineIsometryEquiv_apply

end AffineIsometry

section CompleteField

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {F' : Type x}
  [AddCommGroup F'] [Module 𝕜 F'] [TopologicalSpace F'] [TopologicalAddGroup F']
  [ContinuousSMul 𝕜 F'] [CompleteSpace 𝕜]

section Affine

variable {PE PF : Type*} [MetricSpace PE] [NormedAddTorsor E PE] [MetricSpace PF]
  [NormedAddTorsor F PF] [FiniteDimensional 𝕜 E]

theorem AffineMap.continuous_of_finiteDimensional (f : PE →ᵃ[𝕜] PF) : Continuous f :=
  AffineMap.continuous_linear_iff.1 f.linear.continuous_of_finiteDimensional
#align affine_map.continuous_of_finite_dimensional AffineMap.continuous_of_finiteDimensional

theorem AffineEquiv.continuous_of_finiteDimensional (f : PE ≃ᵃ[𝕜] PF) : Continuous f :=
  f.toAffineMap.continuous_of_finiteDimensional
#align affine_equiv.continuous_of_finite_dimensional AffineEquiv.continuous_of_finiteDimensional

/-- Reinterpret an affine equivalence as a homeomorphism. -/
def AffineEquiv.toHomeomorphOfFiniteDimensional (f : PE ≃ᵃ[𝕜] PF) : PE ≃ₜ PF where
  toEquiv := f.toEquiv
  continuous_toFun := f.continuous_of_finiteDimensional
  continuous_invFun :=
    haveI : FiniteDimensional 𝕜 F := f.linear.finiteDimensional
    f.symm.continuous_of_finiteDimensional
#align affine_equiv.to_homeomorph_of_finite_dimensional AffineEquiv.toHomeomorphOfFiniteDimensional

@[simp]
theorem AffineEquiv.coe_toHomeomorphOfFiniteDimensional (f : PE ≃ᵃ[𝕜] PF) :
    ⇑f.toHomeomorphOfFiniteDimensional = f :=
  rfl
#align affine_equiv.coe_to_homeomorph_of_finite_dimensional AffineEquiv.coe_toHomeomorphOfFiniteDimensional

@[simp]
theorem AffineEquiv.coe_toHomeomorphOfFiniteDimensional_symm (f : PE ≃ᵃ[𝕜] PF) :
    ⇑f.toHomeomorphOfFiniteDimensional.symm = f.symm :=
  rfl
#align affine_equiv.coe_to_homeomorph_of_finite_dimensional_symm AffineEquiv.coe_toHomeomorphOfFiniteDimensional_symm

end Affine

theorem ContinuousLinearMap.continuous_det : Continuous fun f : E →L[𝕜] E => f.det := by
  change Continuous fun f : E →L[𝕜] E => LinearMap.det (f : E →ₗ[𝕜] E)
  -- ⊢ Continuous fun f => ↑LinearMap.det ↑f
  -- Porting note: this could be easier with `det_cases`
  by_cases h : ∃ s : Finset E, Nonempty (Basis (↥s) 𝕜 E)
  -- ⊢ Continuous fun f => ↑LinearMap.det ↑f
  · rcases h with ⟨s, ⟨b⟩⟩
    -- ⊢ Continuous fun f => ↑LinearMap.det ↑f
    haveI : FiniteDimensional 𝕜 E := FiniteDimensional.of_fintype_basis b
    -- ⊢ Continuous fun f => ↑LinearMap.det ↑f
    simp_rw [LinearMap.det_eq_det_toMatrix_of_finset b]
    -- ⊢ Continuous fun f => Matrix.det (↑(LinearMap.toMatrix b b) ↑f)
    refine' Continuous.matrix_det _
    -- ⊢ Continuous fun f => ↑(LinearMap.toMatrix b b) ↑f
    exact
      ((LinearMap.toMatrix b b).toLinearMap.comp
          (ContinuousLinearMap.coeLM 𝕜)).continuous_of_finiteDimensional
  · -- Porting note: was `unfold LinearMap.det`
    rw [LinearMap.det_def]
    -- ⊢ Continuous fun f => ↑(if H : ∃ s, Nonempty (Basis { x // x ∈ s } 𝕜 E) then L …
    simpa only [h, MonoidHom.one_apply, dif_neg, not_false_iff] using continuous_const
    -- 🎉 no goals
#align continuous_linear_map.continuous_det ContinuousLinearMap.continuous_det

/-- Any `K`-Lipschitz map from a subset `s` of a metric space `α` to a finite-dimensional real
vector space `E'` can be extended to a Lipschitz map on the whole space `α`, with a slightly worse
constant `C * K` where `C` only depends on `E'`. We record a working value for this constant `C`
as `lipschitzExtensionConstant E'`. -/
irreducible_def lipschitzExtensionConstant (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] : ℝ≥0 :=
  let A := (Basis.ofVectorSpace ℝ E').equivFun.toContinuousLinearEquiv
  max (‖A.symm.toContinuousLinearMap‖₊ * ‖A.toContinuousLinearMap‖₊) 1
#align lipschitz_extension_constant lipschitzExtensionConstant

theorem lipschitzExtensionConstant_pos (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] : 0 < lipschitzExtensionConstant E' := by
  rw [lipschitzExtensionConstant]
  -- ⊢ 0 <
  exact zero_lt_one.trans_le (le_max_right _ _)
  -- 🎉 no goals
#align lipschitz_extension_constant_pos lipschitzExtensionConstant_pos

/-- Any `K`-Lipschitz map from a subset `s` of a metric space `α` to a finite-dimensional real
vector space `E'` can be extended to a Lipschitz map on the whole space `α`, with a slightly worse
constant `lipschitzExtensionConstant E' * K`. -/
theorem LipschitzOnWith.extend_finite_dimension {α : Type*} [PseudoMetricSpace α] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] {s : Set α} {f : α → E'}
    {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    ∃ g : α → E', LipschitzWith (lipschitzExtensionConstant E' * K) g ∧ EqOn f g s := by
  /- This result is already known for spaces `ι → ℝ`. We use a continuous linear equiv between
    `E'` and such a space to transfer the result to `E'`. -/
  let ι : Type _ := Basis.ofVectorSpaceIndex ℝ E'
  -- ⊢ ∃ g, LipschitzWith (lipschitzExtensionConstant E' * K) g ∧ EqOn f g s
  let A := (Basis.ofVectorSpace ℝ E').equivFun.toContinuousLinearEquiv
  -- ⊢ ∃ g, LipschitzWith (lipschitzExtensionConstant E' * K) g ∧ EqOn f g s
  have LA : LipschitzWith ‖A.toContinuousLinearMap‖₊ A := by apply A.lipschitz
  -- ⊢ ∃ g, LipschitzWith (lipschitzExtensionConstant E' * K) g ∧ EqOn f g s
  have L : LipschitzOnWith (‖A.toContinuousLinearMap‖₊ * K) (A ∘ f) s :=
    LA.comp_lipschitzOnWith hf
  obtain ⟨g, hg, gs⟩ :
    ∃ g : α → ι → ℝ, LipschitzWith (‖A.toContinuousLinearMap‖₊ * K) g ∧ EqOn (A ∘ f) g s :=
    L.extend_pi
  refine' ⟨A.symm ∘ g, _, _⟩
  -- ⊢ LipschitzWith (lipschitzExtensionConstant E' * K) (↑(ContinuousLinearEquiv.s …
  · have LAsymm : LipschitzWith ‖A.symm.toContinuousLinearMap‖₊ A.symm := by
      apply A.symm.lipschitz
    apply (LAsymm.comp hg).weaken
    -- ⊢ ‖↑(ContinuousLinearEquiv.symm A)‖₊ * (‖↑A‖₊ * K) ≤ lipschitzExtensionConstan …
    rw [lipschitzExtensionConstant, ← mul_assoc]
    -- ⊢ ‖↑(ContinuousLinearEquiv.symm A)‖₊ * ‖↑A‖₊ * K ≤
    refine' mul_le_mul' (le_max_left _ _) le_rfl
    -- 🎉 no goals
  · intro x hx
    -- ⊢ f x = (↑(ContinuousLinearEquiv.symm A) ∘ g) x
    have : A (f x) = g x := gs hx
    -- ⊢ f x = (↑(ContinuousLinearEquiv.symm A) ∘ g) x
    simp only [(· ∘ ·), ← this, A.symm_apply_apply]
    -- 🎉 no goals
#align lipschitz_on_with.extend_finite_dimension LipschitzOnWith.extend_finite_dimension

theorem LinearMap.exists_antilipschitzWith [FiniteDimensional 𝕜 E] (f : E →ₗ[𝕜] F)
    (hf : LinearMap.ker f = ⊥) : ∃ K > 0, AntilipschitzWith K f := by
  cases subsingleton_or_nontrivial E
  -- ⊢ ∃ K, K > 0 ∧ AntilipschitzWith K ↑f
  · exact ⟨1, zero_lt_one, AntilipschitzWith.of_subsingleton⟩
    -- 🎉 no goals
  · rw [LinearMap.ker_eq_bot] at hf
    -- ⊢ ∃ K, K > 0 ∧ AntilipschitzWith K ↑f
    let e : E ≃L[𝕜] LinearMap.range f := (LinearEquiv.ofInjective f hf).toContinuousLinearEquiv
    -- ⊢ ∃ K, K > 0 ∧ AntilipschitzWith K ↑f
    exact ⟨_, e.nnnorm_symm_pos, e.antilipschitz⟩
    -- 🎉 no goals
#align linear_map.exists_antilipschitz_with LinearMap.exists_antilipschitzWith

protected theorem LinearIndependent.eventually {ι} [Finite ι] {f : ι → E}
    (hf : LinearIndependent 𝕜 f) : ∀ᶠ g in 𝓝 f, LinearIndependent 𝕜 g := by
  cases nonempty_fintype ι
  -- ⊢ ∀ᶠ (g : ι → E) in 𝓝 f, LinearIndependent 𝕜 g
  simp only [Fintype.linearIndependent_iff'] at hf ⊢
  -- ⊢ ∀ᶠ (g : ι → E) in 𝓝 f, LinearMap.ker (↑(LinearMap.lsum 𝕜 (fun x => 𝕜) ℕ) fun …
  rcases LinearMap.exists_antilipschitzWith _ hf with ⟨K, K0, hK⟩
  -- ⊢ ∀ᶠ (g : ι → E) in 𝓝 f, LinearMap.ker (↑(LinearMap.lsum 𝕜 (fun x => 𝕜) ℕ) fun …
  have : Tendsto (fun g : ι → E => ∑ i, ‖g i - f i‖) (𝓝 f) (𝓝 <| ∑ i, ‖f i - f i‖) :=
    tendsto_finset_sum _ fun i _ =>
      Tendsto.norm <| ((continuous_apply i).tendsto _).sub tendsto_const_nhds
  simp only [sub_self, norm_zero, Finset.sum_const_zero] at this
  -- ⊢ ∀ᶠ (g : ι → E) in 𝓝 f, LinearMap.ker (↑(LinearMap.lsum 𝕜 (fun x => 𝕜) ℕ) fun …
  refine' (this.eventually (gt_mem_nhds <| inv_pos.2 K0)).mono fun g hg => _
  -- ⊢ LinearMap.ker (↑(LinearMap.lsum 𝕜 (fun x => 𝕜) ℕ) fun i => LinearMap.smulRig …
  replace hg : ∑ i, ‖g i - f i‖₊ < K⁻¹
  -- ⊢ ∑ i : ι, ‖g i - f i‖₊ < K⁻¹
  · rw [← NNReal.coe_lt_coe]
    -- ⊢ ↑(∑ i : ι, ‖g i - f i‖₊) < ↑K⁻¹
    push_cast
    -- ⊢ ∑ x : ι, ‖g x - f x‖ < (↑K)⁻¹
    exact hg
    -- 🎉 no goals
  rw [LinearMap.ker_eq_bot]
  -- ⊢ Function.Injective ↑(↑(LinearMap.lsum 𝕜 (fun x => 𝕜) ℕ) fun i => LinearMap.s …
  refine' (hK.add_sub_lipschitzWith (LipschitzWith.of_dist_le_mul fun v u => _) hg).injective
  -- ⊢ dist ((↑(↑(LinearMap.lsum 𝕜 (fun x => 𝕜) ℕ) fun i => LinearMap.smulRight Lin …
  simp only [dist_eq_norm, LinearMap.lsum_apply, Pi.sub_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.smulRight_apply, LinearMap.id_apply, ←
    Finset.sum_sub_distrib, ← smul_sub, ← sub_smul, NNReal.coe_sum, coe_nnnorm, Finset.sum_mul]
  refine' norm_sum_le_of_le _ fun i _ => _
  -- ⊢ ‖(v i - u i) • (g i - f i)‖ ≤ ‖g i - f i‖ * ‖v - u‖
  rw [norm_smul, mul_comm]
  -- ⊢ ‖g i - f i‖ * ‖v i - u i‖ ≤ ‖g i - f i‖ * ‖v - u‖
  gcongr
  -- ⊢ ‖v i - u i‖ ≤ ‖v - u‖
  exact norm_le_pi_norm (v - u) i
  -- 🎉 no goals
#align linear_independent.eventually LinearIndependent.eventually

theorem isOpen_setOf_linearIndependent {ι : Type*} [Finite ι] :
    IsOpen { f : ι → E | LinearIndependent 𝕜 f } :=
  isOpen_iff_mem_nhds.2 fun _ => LinearIndependent.eventually
#align is_open_set_of_linear_independent isOpen_setOf_linearIndependent

theorem isOpen_setOf_nat_le_rank (n : ℕ) :
    IsOpen { f : E →L[𝕜] F | ↑n ≤ (f : E →ₗ[𝕜] F).rank } := by
  simp only [LinearMap.le_rank_iff_exists_linearIndependent_finset, setOf_exists, ← exists_prop]
  -- ⊢ IsOpen (⋃ (i : Finset E) (_ : Finset.card i = n), {x | LinearIndependent 𝕜 f …
  refine' isOpen_biUnion fun t _ => _
  -- ⊢ IsOpen {x | LinearIndependent 𝕜 fun x_1 => ↑↑x ↑x_1}
  have : Continuous fun f : E →L[𝕜] F => fun x : (t : Set E) => f x :=
    continuous_pi fun x => (ContinuousLinearMap.apply 𝕜 F (x : E)).continuous
  exact isOpen_setOf_linearIndependent.preimage this
  -- 🎉 no goals
#align is_open_set_of_nat_le_rank isOpen_setOf_nat_le_rank

theorem Basis.op_nnnorm_le {ι : Type*} [Fintype ι] (v : Basis ι 𝕜 E) {u : E →L[𝕜] F} (M : ℝ≥0)
    (hu : ∀ i, ‖u (v i)‖₊ ≤ M) : ‖u‖₊ ≤ Fintype.card ι • ‖v.equivFunL.toContinuousLinearMap‖₊ * M :=
  u.op_nnnorm_le_bound _ fun e => by
    set φ := v.equivFunL.toContinuousLinearMap
    -- ⊢ ‖↑u e‖₊ ≤ Fintype.card ι • ‖φ‖₊ * M * ‖e‖₊
    calc
      ‖u e‖₊ = ‖u (∑ i, v.equivFun e i • v i)‖₊ := by rw [v.sum_equivFun]
      _ = ‖∑ i, v.equivFun e i • (u <| v i)‖₊ := by simp [u.map_sum, LinearMap.map_smul]
      _ ≤ ∑ i, ‖v.equivFun e i • (u <| v i)‖₊ := (nnnorm_sum_le _ _)
      _ = ∑ i, ‖v.equivFun e i‖₊ * ‖u (v i)‖₊ := by simp only [nnnorm_smul]
      _ ≤ ∑ i, ‖v.equivFun e i‖₊ * M := by gcongr; apply hu
      _ = (∑ i, ‖v.equivFun e i‖₊) * M := Finset.sum_mul.symm
      _ ≤ Fintype.card ι • (‖φ‖₊ * ‖e‖₊) * M := by
        gcongr
        calc
          ∑ i, ‖v.equivFun e i‖₊ ≤ Fintype.card ι • ‖φ e‖₊ := Pi.sum_nnnorm_apply_le_nnnorm _
          _ ≤ Fintype.card ι • (‖φ‖₊ * ‖e‖₊) := nsmul_le_nsmul_of_le_right (φ.le_op_nnnorm e) _
      _ = Fintype.card ι • ‖φ‖₊ * M * ‖e‖₊ := by simp only [smul_mul_assoc, mul_right_comm]
#align basis.op_nnnorm_le Basis.op_nnnorm_le

theorem Basis.op_norm_le {ι : Type*} [Fintype ι] (v : Basis ι 𝕜 E) {u : E →L[𝕜] F} {M : ℝ}
    (hM : 0 ≤ M) (hu : ∀ i, ‖u (v i)‖ ≤ M) :
    ‖u‖ ≤ Fintype.card ι • ‖v.equivFunL.toContinuousLinearMap‖ * M := by
  simpa using NNReal.coe_le_coe.mpr (v.op_nnnorm_le ⟨M, hM⟩ hu)
  -- 🎉 no goals
#align basis.op_norm_le Basis.op_norm_le

/-- A weaker version of `Basis.op_nnnorm_le` that abstracts away the value of `C`. -/
theorem Basis.exists_op_nnnorm_le {ι : Type*} [Finite ι] (v : Basis ι 𝕜 E) :
    ∃ C > (0 : ℝ≥0), ∀ {u : E →L[𝕜] F} (M : ℝ≥0), (∀ i, ‖u (v i)‖₊ ≤ M) → ‖u‖₊ ≤ C * M := by
  cases nonempty_fintype ι
  -- ⊢ ∃ C, C > 0 ∧ ∀ {u : E →L[𝕜] F} (M : ℝ≥0), (∀ (i : ι), ‖↑u (↑v i)‖₊ ≤ M) → ‖u …
  exact
    ⟨max (Fintype.card ι • ‖v.equivFunL.toContinuousLinearMap‖₊) 1,
      zero_lt_one.trans_le (le_max_right _ _), fun {u} M hu =>
      (v.op_nnnorm_le M hu).trans <| mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le M)⟩
#align basis.exists_op_nnnorm_le Basis.exists_op_nnnorm_le

/-- A weaker version of `Basis.op_norm_le` that abstracts away the value of `C`. -/
theorem Basis.exists_op_norm_le {ι : Type*} [Finite ι] (v : Basis ι 𝕜 E) :
    ∃ C > (0 : ℝ), ∀ {u : E →L[𝕜] F} {M : ℝ}, 0 ≤ M → (∀ i, ‖u (v i)‖ ≤ M) → ‖u‖ ≤ C * M := by
  obtain ⟨C, hC, h⟩ := v.exists_op_nnnorm_le (F := F)
  -- ⊢ ∃ C, C > 0 ∧ ∀ {u : E →L[𝕜] F} {M : ℝ}, 0 ≤ M → (∀ (i : ι), ‖↑u (↑v i)‖ ≤ M) …
  -- Porting note: used `Subtype.forall'` below
  refine ⟨C, hC, ?_⟩
  -- ⊢ ∀ {u : E →L[𝕜] F} {M : ℝ}, 0 ≤ M → (∀ (i : ι), ‖↑u (↑v i)‖ ≤ M) → ‖u‖ ≤ ↑C * M
  intro u M hM H
  -- ⊢ ‖u‖ ≤ ↑C * M
  simpa using h ⟨M, hM⟩ H
  -- 🎉 no goals
#align basis.exists_op_norm_le Basis.exists_op_norm_le

instance [FiniteDimensional 𝕜 E] [SecondCountableTopology F] :
    SecondCountableTopology (E →L[𝕜] F) := by
  set d := FiniteDimensional.finrank 𝕜 E
  -- ⊢ SecondCountableTopology (E →L[𝕜] F)
  suffices
    ∀ ε > (0 : ℝ), ∃ n : (E →L[𝕜] F) → Fin d → ℕ, ∀ f g : E →L[𝕜] F, n f = n g → dist f g ≤ ε from
    Metric.secondCountable_of_countable_discretization fun ε ε_pos =>
      ⟨Fin d → ℕ, by infer_instance, this ε ε_pos⟩
  intro ε ε_pos
  -- ⊢ ∃ n, ∀ (f g : E →L[𝕜] F), n f = n g → dist f g ≤ ε
  obtain ⟨u : ℕ → F, hu : DenseRange u⟩ := exists_dense_seq F
  -- ⊢ ∃ n, ∀ (f g : E →L[𝕜] F), n f = n g → dist f g ≤ ε
  let v := FiniteDimensional.finBasis 𝕜 E
  -- ⊢ ∃ n, ∀ (f g : E →L[𝕜] F), n f = n g → dist f g ≤ ε
  obtain
    ⟨C : ℝ, C_pos : 0 < C, hC :
      ∀ {φ : E →L[𝕜] F} {M : ℝ}, 0 ≤ M → (∀ i, ‖φ (v i)‖ ≤ M) → ‖φ‖ ≤ C * M⟩ :=
    v.exists_op_norm_le (E := E) (F := F)
  have h_2C : 0 < 2 * C := mul_pos zero_lt_two C_pos
  -- ⊢ ∃ n, ∀ (f g : E →L[𝕜] F), n f = n g → dist f g ≤ ε
  have hε2C : 0 < ε / (2 * C) := div_pos ε_pos h_2C
  -- ⊢ ∃ n, ∀ (f g : E →L[𝕜] F), n f = n g → dist f g ≤ ε
  have : ∀ φ : E →L[𝕜] F, ∃ n : Fin d → ℕ, ‖φ - (v.constrL <| u ∘ n)‖ ≤ ε / 2 := by
    intro φ
    have : ∀ i, ∃ n, ‖φ (v i) - u n‖ ≤ ε / (2 * C) := by
      simp only [norm_sub_rev]
      intro i
      have : φ (v i) ∈ closure (range u) := hu _
      obtain ⟨n, hn⟩ : ∃ n, ‖u n - φ (v i)‖ < ε / (2 * C) := by
        rw [mem_closure_iff_nhds_basis Metric.nhds_basis_ball] at this
        specialize this (ε / (2 * C)) hε2C
        simpa [dist_eq_norm]
      exact ⟨n, le_of_lt hn⟩
    choose n hn using this
    use n
    replace hn : ∀ i : Fin d, ‖(φ - (v.constrL <| u ∘ n)) (v i)‖ ≤ ε / (2 * C)
    · simp [hn]
    have : C * (ε / (2 * C)) = ε / 2 := by
      rw [eq_div_iff (two_ne_zero : (2 : ℝ) ≠ 0), mul_comm, ← mul_assoc,
        mul_div_cancel' _ (ne_of_gt h_2C)]
    specialize hC (le_of_lt hε2C) hn
    rwa [this] at hC
  choose n hn using this
  -- ⊢ ∃ n, ∀ (f g : E →L[𝕜] F), n f = n g → dist f g ≤ ε
  set Φ := fun φ : E →L[𝕜] F => v.constrL <| u ∘ n φ
  -- ⊢ ∃ n, ∀ (f g : E →L[𝕜] F), n f = n g → dist f g ≤ ε
  change ∀ z, dist z (Φ z) ≤ ε / 2 at hn
  -- ⊢ ∃ n, ∀ (f g : E →L[𝕜] F), n f = n g → dist f g ≤ ε
  use n
  -- ⊢ ∀ (f g : E →L[𝕜] F), n f = n g → dist f g ≤ ε
  intro x y hxy
  -- ⊢ dist x y ≤ ε
  calc
    dist x y ≤ dist x (Φ x) + dist (Φ x) y := dist_triangle _ _ _
    _ = dist x (Φ x) + dist y (Φ y) := by simp [hxy, dist_comm]
    _ ≤ ε := by linarith [hn x, hn y]

variable (𝕜 E)

theorem FiniteDimensional.complete [FiniteDimensional 𝕜 E] : CompleteSpace E := by
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ _ (finrank 𝕜 E)).symm
  -- ⊢ CompleteSpace E
  have : UniformEmbedding e.toLinearEquiv.toEquiv.symm := e.symm.uniformEmbedding
  -- ⊢ CompleteSpace E
  exact (completeSpace_congr this).1 (by infer_instance)
  -- 🎉 no goals
#align finite_dimensional.complete FiniteDimensional.complete

variable {𝕜 E}

/-- A finite-dimensional subspace is complete. -/
theorem Submodule.complete_of_finiteDimensional (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] :
    IsComplete (s : Set E) :=
  completeSpace_coe_iff_isComplete.1 (FiniteDimensional.complete 𝕜 s)
#align submodule.complete_of_finite_dimensional Submodule.complete_of_finiteDimensional

/-- A finite-dimensional subspace is closed. -/
theorem Submodule.closed_of_finiteDimensional (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] :
    IsClosed (s : Set E) :=
  s.complete_of_finiteDimensional.isClosed
#align submodule.closed_of_finite_dimensional Submodule.closed_of_finiteDimensional

theorem AffineSubspace.closed_of_finiteDimensional {P : Type*} [MetricSpace P]
    [NormedAddTorsor E P] (s : AffineSubspace 𝕜 P) [FiniteDimensional 𝕜 s.direction] :
    IsClosed (s : Set P) :=
  s.isClosed_direction_iff.mp s.direction.closed_of_finiteDimensional
#align affine_subspace.closed_of_finite_dimensional AffineSubspace.closed_of_finiteDimensional

section Riesz

/-- In an infinite dimensional space, given a finite number of points, one may find a point
with norm at most `R` which is at distance at least `1` of all these points. -/
theorem exists_norm_le_le_norm_sub_of_finset {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R)
    (h : ¬FiniteDimensional 𝕜 E) (s : Finset E) : ∃ x : E, ‖x‖ ≤ R ∧ ∀ y ∈ s, 1 ≤ ‖y - x‖ := by
  let F := Submodule.span 𝕜 (s : Set E)
  -- ⊢ ∃ x, ‖x‖ ≤ R ∧ ∀ (y : E), y ∈ s → 1 ≤ ‖y - x‖
  haveI : FiniteDimensional 𝕜 F :=
    Module.finite_def.2
      ((Submodule.fg_top _).2 (Submodule.fg_def.2 ⟨s, Finset.finite_toSet _, rfl⟩))
  have Fclosed : IsClosed (F : Set E) := Submodule.closed_of_finiteDimensional _
  -- ⊢ ∃ x, ‖x‖ ≤ R ∧ ∀ (y : E), y ∈ s → 1 ≤ ‖y - x‖
  have : ∃ x, x ∉ F := by
    contrapose! h
    have : (⊤ : Submodule 𝕜 E) = F := by
      ext x
      simp [h]
    have : FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 E) := by rwa [this]
    refine' Module.finite_def.2 ((Submodule.fg_top _).1 (Module.finite_def.1 this))
  obtain ⟨x, xR, hx⟩ : ∃ x : E, ‖x‖ ≤ R ∧ ∀ y : E, y ∈ F → 1 ≤ ‖x - y‖ :=
    riesz_lemma_of_norm_lt hc hR Fclosed this
  have hx' : ∀ y : E, y ∈ F → 1 ≤ ‖y - x‖ := by
    intro y hy
    rw [← norm_neg]
    simpa using hx y hy
  exact ⟨x, xR, fun y hy => hx' _ (Submodule.subset_span hy)⟩
  -- 🎉 no goals
#align exists_norm_le_le_norm_sub_of_finset exists_norm_le_le_norm_sub_of_finset

/-- In an infinite-dimensional normed space, there exists a sequence of points which are all
bounded by `R` and at distance at least `1`. For a version not assuming `c` and `R`, see
`exists_seq_norm_le_one_le_norm_sub`. -/
theorem exists_seq_norm_le_one_le_norm_sub' {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R)
    (h : ¬FiniteDimensional 𝕜 E) :
    ∃ f : ℕ → E, (∀ n, ‖f n‖ ≤ R) ∧ ∀ m n, m ≠ n → 1 ≤ ‖f m - f n‖ := by
  have : IsSymm E fun x y : E => 1 ≤ ‖x - y‖ := by
    constructor
    intro x y hxy
    rw [← norm_neg]
    simpa
  apply
    exists_seq_of_forall_finset_exists' (fun x : E => ‖x‖ ≤ R) fun (x : E) (y : E) => 1 ≤ ‖x - y‖
  rintro s -
  -- ⊢ ∃ y, ‖y‖ ≤ R ∧ ∀ (x : E), x ∈ s → 1 ≤ ‖x - y‖
  exact exists_norm_le_le_norm_sub_of_finset hc hR h s
  -- 🎉 no goals
#align exists_seq_norm_le_one_le_norm_sub' exists_seq_norm_le_one_le_norm_sub'

theorem exists_seq_norm_le_one_le_norm_sub (h : ¬FiniteDimensional 𝕜 E) :
    ∃ (R : ℝ) (f : ℕ → E), 1 < R ∧ (∀ n, ‖f n‖ ≤ R) ∧ ∀ m n, m ≠ n → 1 ≤ ‖f m - f n‖ := by
  obtain ⟨c, hc⟩ : ∃ c : 𝕜, 1 < ‖c‖ := NormedField.exists_one_lt_norm 𝕜
  -- ⊢ ∃ R f, 1 < R ∧ (∀ (n : ℕ), ‖f n‖ ≤ R) ∧ ∀ (m n : ℕ), m ≠ n → 1 ≤ ‖f m - f n‖
  have A : ‖c‖ < ‖c‖ + 1 := by linarith
  -- ⊢ ∃ R f, 1 < R ∧ (∀ (n : ℕ), ‖f n‖ ≤ R) ∧ ∀ (m n : ℕ), m ≠ n → 1 ≤ ‖f m - f n‖
  rcases exists_seq_norm_le_one_le_norm_sub' hc A h with ⟨f, hf⟩
  -- ⊢ ∃ R f, 1 < R ∧ (∀ (n : ℕ), ‖f n‖ ≤ R) ∧ ∀ (m n : ℕ), m ≠ n → 1 ≤ ‖f m - f n‖
  exact ⟨‖c‖ + 1, f, hc.trans A, hf.1, hf.2⟩
  -- 🎉 no goals
#align exists_seq_norm_le_one_le_norm_sub exists_seq_norm_le_one_le_norm_sub

variable (𝕜)

/-- **Riesz's theorem**: if a closed ball with center zero of positive radius is compact in a vector
space, then the space is finite-dimensional. -/
theorem finiteDimensional_of_isCompact_closed_ball₀ {r : ℝ} (rpos : 0 < r)
    (h : IsCompact (Metric.closedBall (0 : E) r)) : FiniteDimensional 𝕜 E := by
  by_contra hfin
  -- ⊢ False
  obtain ⟨R, f, Rgt, fle, lef⟩ :
    ∃ (R : ℝ) (f : ℕ → E), 1 < R ∧ (∀ n, ‖f n‖ ≤ R) ∧ ∀ m n, m ≠ n → 1 ≤ ‖f m - f n‖ :=
    exists_seq_norm_le_one_le_norm_sub hfin
  have rRpos : 0 < r / R := div_pos rpos (zero_lt_one.trans Rgt)
  -- ⊢ False
  obtain ⟨c, hc⟩ : ∃ c : 𝕜, 0 < ‖c‖ ∧ ‖c‖ < r / R := NormedField.exists_norm_lt _ rRpos
  -- ⊢ False
  let g := fun n : ℕ => c • f n
  -- ⊢ False
  have A : ∀ n, g n ∈ Metric.closedBall (0 : E) r := by
    intro n
    simp only [norm_smul, dist_zero_right, Metric.mem_closedBall]
    calc
      ‖c‖ * ‖f n‖ ≤ r / R * R := by gcongr; exact hc.2.le; apply fle
      _ = r := by field_simp [(zero_lt_one.trans Rgt).ne']
  -- Porting note: moved type ascriptions because of exists_prop changes
  obtain ⟨x : E, _ : x ∈ Metric.closedBall (0 : E) r, φ : ℕ → ℕ, φmono : StrictMono φ,
    φlim : Tendsto (g ∘ φ) atTop (𝓝 x)⟩ := h.tendsto_subseq A
  have B : CauchySeq (g ∘ φ) := φlim.cauchySeq
  -- ⊢ False
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → dist ((g ∘ φ) n) ((g ∘ φ) N) < ‖c‖ :=
    Metric.cauchySeq_iff'.1 B ‖c‖ hc.1
  apply lt_irrefl ‖c‖
  -- ⊢ ‖c‖ < ‖c‖
  calc
    ‖c‖ ≤ dist (g (φ (N + 1))) (g (φ N)) := by
      conv_lhs => rw [← mul_one ‖c‖]
      simp only [dist_eq_norm, ← smul_sub, norm_smul]
      gcongr
      apply lef _ _ (ne_of_gt _)
      exact φmono (Nat.lt_succ_self N)
    _ < ‖c‖ := hN (N + 1) (Nat.le_succ N)
#align finite_dimensional_of_is_compact_closed_ball₀ finiteDimensional_of_isCompact_closed_ball₀

/-- **Riesz's theorem**: if a closed ball of positive radius is compact in a vector space, then the
space is finite-dimensional. -/
theorem finiteDimensional_of_isCompact_closedBall {r : ℝ} (rpos : 0 < r) {c : E}
    (h : IsCompact (Metric.closedBall c r)) : FiniteDimensional 𝕜 E := by
  apply finiteDimensional_of_isCompact_closed_ball₀ 𝕜 rpos
  -- ⊢ IsCompact (Metric.closedBall 0 r)
  have : Continuous fun x => -c + x := continuous_const.add continuous_id
  -- ⊢ IsCompact (Metric.closedBall 0 r)
  simpa using h.image this
  -- 🎉 no goals
#align finite_dimensional_of_is_compact_closed_ball finiteDimensional_of_isCompact_closedBall

/-- If a function has compact multiplicative support, then either the function is trivial or the
space is finite-dimensional. -/
@[to_additive
      "If a function has compact support, then either the function is trivial or the space is
      finite-dimensional."]
theorem HasCompactMulSupport.eq_one_or_finiteDimensional {X : Type*} [TopologicalSpace X] [One X]
    [T2Space X] {f : E → X} (hf : HasCompactMulSupport f) (h'f : Continuous f) :
    f = 1 ∨ FiniteDimensional 𝕜 E := by
  by_cases h : ∀ x, f x = 1
  -- ⊢ f = 1 ∨ FiniteDimensional 𝕜 E
  · apply Or.inl
    -- ⊢ f = 1
    ext x
    -- ⊢ f x = OfNat.ofNat 1 x
    exact h x
    -- 🎉 no goals
  apply Or.inr
  -- ⊢ FiniteDimensional 𝕜 E
  push_neg at h
  -- ⊢ FiniteDimensional 𝕜 E
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 1 := h
  -- ⊢ FiniteDimensional 𝕜 E
  have : Function.mulSupport f ∈ 𝓝 x := h'f.isOpen_mulSupport.mem_nhds hx
  -- ⊢ FiniteDimensional 𝕜 E
  -- Porting note: moved type ascriptions because of exists_prop changes
  obtain ⟨r : ℝ, rpos : 0 < r, hr : Metric.closedBall x r ⊆ Function.mulSupport f⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.1 this
  have : IsCompact (Metric.closedBall x r) :=
    isCompact_of_isClosed_subset hf Metric.isClosed_ball (hr.trans (subset_mulTSupport _))
  exact finiteDimensional_of_isCompact_closedBall 𝕜 rpos this
  -- 🎉 no goals
#align has_compact_mul_support.eq_one_or_finite_dimensional HasCompactMulSupport.eq_one_or_finiteDimensional
#align has_compact_support.eq_zero_or_finite_dimensional HasCompactSupport.eq_zero_or_finiteDimensional

end Riesz

/-- An injective linear map with finite-dimensional domain is a closed embedding. -/
theorem LinearEquiv.closedEmbedding_of_injective {f : E →ₗ[𝕜] F} (hf : LinearMap.ker f = ⊥)
    [FiniteDimensional 𝕜 E] : ClosedEmbedding f :=
  let g := LinearEquiv.ofInjective f (LinearMap.ker_eq_bot.mp hf)
  { embedding_subtype_val.comp g.toContinuousLinearEquiv.toHomeomorph.embedding with
    closed_range := by
      haveI := f.finiteDimensional_range
      -- ⊢ IsClosed (range ↑f)
      simpa [LinearMap.range_coe f] using f.range.closed_of_finiteDimensional }
      -- 🎉 no goals
#align linear_equiv.closed_embedding_of_injective LinearEquiv.closedEmbedding_of_injective

theorem ContinuousLinearMap.exists_right_inverse_of_surjective [FiniteDimensional 𝕜 F]
    (f : E →L[𝕜] F) (hf : LinearMap.range f = ⊤) :
    ∃ g : F →L[𝕜] E, f.comp g = ContinuousLinearMap.id 𝕜 F :=
  let ⟨g, hg⟩ := (f : E →ₗ[𝕜] F).exists_rightInverse_of_surjective hf
  ⟨LinearMap.toContinuousLinearMap g, ContinuousLinearMap.ext <| LinearMap.ext_iff.1 hg⟩
#align continuous_linear_map.exists_right_inverse_of_surjective ContinuousLinearMap.exists_right_inverse_of_surjective

theorem closedEmbedding_smul_left {c : E} (hc : c ≠ 0) : ClosedEmbedding fun x : 𝕜 => x • c :=
  LinearEquiv.closedEmbedding_of_injective (LinearMap.ker_toSpanSingleton 𝕜 E hc)
#align closed_embedding_smul_left closedEmbedding_smul_left

-- `smul` is a closed map in the first argument.
theorem isClosedMap_smul_left (c : E) : IsClosedMap fun x : 𝕜 => x • c := by
  by_cases hc : c = 0
  -- ⊢ IsClosedMap fun x => x • c
  · simp_rw [hc, smul_zero]
    -- ⊢ IsClosedMap fun x => 0
    exact isClosedMap_const
    -- 🎉 no goals
  · exact (closedEmbedding_smul_left hc).isClosedMap
    -- 🎉 no goals
#align is_closed_map_smul_left isClosedMap_smul_left

open ContinuousLinearMap

/-- Continuous linear equivalence between continuous linear functions `𝕜ⁿ → E` and `Eⁿ`.
The spaces `𝕜ⁿ` and `Eⁿ` are represented as `ι → 𝕜` and `ι → E`, respectively,
where `ι` is a finite type. -/
def ContinuousLinearEquiv.piRing (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ((ι → 𝕜) →L[𝕜] E) ≃L[𝕜] ι → E :=
  { LinearMap.toContinuousLinearMap.symm.trans (LinearEquiv.piRing 𝕜 E ι 𝕜) with
    continuous_toFun := by
      refine' continuous_pi fun i => _
      -- ⊢ Continuous fun a => AddHom.toFun (↑{ toLinearMap := ↑src✝, invFun := src✝.in …
      exact (ContinuousLinearMap.apply 𝕜 E (Pi.single i 1)).continuous
      -- 🎉 no goals
    continuous_invFun := by
      simp_rw [LinearEquiv.invFun_eq_symm, LinearEquiv.trans_symm, LinearEquiv.symm_symm]
      -- ⊢ Continuous ↑(LinearEquiv.trans (LinearEquiv.symm (LinearEquiv.piRing 𝕜 E ι 𝕜 …
      -- Note: added explicit type and removed `change` that tried to achieve the same
      refine AddMonoidHomClass.continuous_of_bound
        (LinearMap.toContinuousLinearMap.toLinearMap.comp
            (LinearEquiv.piRing 𝕜 E ι 𝕜).symm.toLinearMap)
        (Fintype.card ι : ℝ) fun g => ?_
      rw [← nsmul_eq_mul]
      -- ⊢ ‖↑(LinearMap.comp ↑LinearMap.toContinuousLinearMap ↑(LinearEquiv.symm (Linea …
      refine op_norm_le_bound _ (nsmul_nonneg (norm_nonneg g) (Fintype.card ι)) fun t => ?_
      -- ⊢ ‖↑(↑(LinearMap.comp ↑LinearMap.toContinuousLinearMap ↑(LinearEquiv.symm (Lin …
      simp_rw [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
        LinearMap.coe_toContinuousLinearMap', LinearEquiv.piRing_symm_apply]
      apply le_trans (norm_sum_le _ _)
      -- ⊢ ∑ i : ι, ‖t i • g i‖ ≤ Fintype.card ι • ‖g‖ * ‖t‖
      rw [smul_mul_assoc]
      -- ⊢ ∑ i : ι, ‖t i • g i‖ ≤ Fintype.card ι • (‖g‖ * ‖t‖)
      refine' Finset.sum_le_card_nsmul _ _ _ fun i _ => _
      -- ⊢ ‖t i • g i‖ ≤ ‖g‖ * ‖t‖
      rw [norm_smul, mul_comm]
      -- ⊢ ‖g i‖ * ‖t i‖ ≤ ‖g‖ * ‖t‖
      gcongr <;> apply norm_le_pi_norm }
      -- ⊢ ‖g i‖ ≤ ‖g‖
                 -- 🎉 no goals
                 -- 🎉 no goals
#align continuous_linear_equiv.pi_ring ContinuousLinearEquiv.piRing

/-- A family of continuous linear maps is continuous on `s` if all its applications are. -/
theorem continuousOn_clm_apply {X : Type*} [TopologicalSpace X] [FiniteDimensional 𝕜 E]
    {f : X → E →L[𝕜] F} {s : Set X} : ContinuousOn f s ↔ ∀ y, ContinuousOn (fun x => f x y) s := by
  refine' ⟨fun h y => (ContinuousLinearMap.apply 𝕜 F y).continuous.comp_continuousOn h, fun h => _⟩
  -- ⊢ ContinuousOn f s
  let d := finrank 𝕜 E
  -- ⊢ ContinuousOn f s
  have hd : d = finrank 𝕜 (Fin d → 𝕜) := (finrank_fin_fun 𝕜).symm
  -- ⊢ ContinuousOn f s
  let e₁ : E ≃L[𝕜] Fin d → 𝕜 := ContinuousLinearEquiv.ofFinrankEq hd
  -- ⊢ ContinuousOn f s
  let e₂ : (E →L[𝕜] F) ≃L[𝕜] Fin d → F :=
    (e₁.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.comp.left_id f, ← e₂.symm_comp_self]
  -- ⊢ ContinuousOn ((↑(ContinuousLinearEquiv.symm e₂) ∘ ↑e₂) ∘ f) s
  exact e₂.symm.continuous.comp_continuousOn (continuousOn_pi.mpr fun i => h _)
  -- 🎉 no goals
#align continuous_on_clm_apply continuousOn_clm_apply

theorem continuous_clm_apply {X : Type*} [TopologicalSpace X] [FiniteDimensional 𝕜 E]
    {f : X → E →L[𝕜] F} : Continuous f ↔ ∀ y, Continuous fun x => f x y := by
  simp_rw [continuous_iff_continuousOn_univ, continuousOn_clm_apply]
  -- 🎉 no goals
#align continuous_clm_apply continuous_clm_apply

end CompleteField

section ProperField

variable (𝕜 : Type u) [NontriviallyNormedField 𝕜] (E : Type v) [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [ProperSpace 𝕜]

/-- Any finite-dimensional vector space over a proper field is proper.
We do not register this as an instance to avoid an instance loop when trying to prove the
properness of `𝕜`, and the search for `𝕜` as an unknown metavariable. Declare the instance
explicitly when needed. -/
theorem FiniteDimensional.proper [FiniteDimensional 𝕜 E] : ProperSpace E := by
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ _ (finrank 𝕜 E)).symm
  -- ⊢ ProperSpace E
  exact e.symm.antilipschitz.properSpace e.symm.continuous e.symm.surjective
  -- 🎉 no goals
#align finite_dimensional.proper FiniteDimensional.proper

end ProperField

/- Over the real numbers, we can register the previous statement as an instance as it will not
cause problems in instance resolution since the properness of `ℝ` is already known. -/
instance (priority := 900) FiniteDimensional.proper_real (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] : ProperSpace E :=
  FiniteDimensional.proper ℝ E
#align finite_dimensional.proper_real FiniteDimensional.proper_real

/-- If `E` is a finite dimensional normed real vector space, `x : E`, and `s` is a neighborhood of
`x` that is not equal to the whole space, then there exists a point `y ∈ frontier s` at distance
`Metric.infDist x sᶜ` from `x`. See also
`IsCompact.exists_mem_frontier_infDist_compl_eq_dist`. -/
theorem exists_mem_frontier_infDist_compl_eq_dist {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {x : E} {s : Set E} (hx : x ∈ s) (hs : s ≠ univ) :
    ∃ y ∈ frontier s, Metric.infDist x sᶜ = dist x y := by
  rcases Metric.exists_mem_closure_infDist_eq_dist (nonempty_compl.2 hs) x with ⟨y, hys, hyd⟩
  -- ⊢ ∃ y, y ∈ frontier s ∧ Metric.infDist x sᶜ = dist x y
  rw [closure_compl] at hys
  -- ⊢ ∃ y, y ∈ frontier s ∧ Metric.infDist x sᶜ = dist x y
  refine'
    ⟨y,
      ⟨Metric.closedBall_infDist_compl_subset_closure hx <| Metric.mem_closedBall.2 <| ge_of_eq _,
        hys⟩,
      hyd⟩
  rwa [dist_comm]
  -- 🎉 no goals
#align exists_mem_frontier_inf_dist_compl_eq_dist exists_mem_frontier_infDist_compl_eq_dist

/-- If `K` is a compact set in a nontrivial real normed space and `x ∈ K`, then there exists a point
`y` of the boundary of `K` at distance `Metric.infDist x Kᶜ` from `x`. See also
`exists_mem_frontier_infDist_compl_eq_dist`. -/
nonrec theorem IsCompact.exists_mem_frontier_infDist_compl_eq_dist {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] {x : E} {K : Set E} (hK : IsCompact K)
    (hx : x ∈ K) :
    ∃ y ∈ frontier K, Metric.infDist x Kᶜ = dist x y := by
  obtain hx' | hx' : x ∈ interior K ∪ frontier K := by
    rw [← closure_eq_interior_union_frontier]
    exact subset_closure hx
  · rw [mem_interior_iff_mem_nhds, Metric.nhds_basis_closedBall.mem_iff] at hx'
    -- ⊢ ∃ y, y ∈ frontier K ∧ Metric.infDist x Kᶜ = dist x y
    rcases hx' with ⟨r, hr₀, hrK⟩
    -- ⊢ ∃ y, y ∈ frontier K ∧ Metric.infDist x Kᶜ = dist x y
    have : FiniteDimensional ℝ E :=
      finiteDimensional_of_isCompact_closedBall ℝ hr₀
        (isCompact_of_isClosed_subset hK Metric.isClosed_ball hrK)
    exact exists_mem_frontier_infDist_compl_eq_dist hx hK.ne_univ
    -- 🎉 no goals
  · refine' ⟨x, hx', _⟩
    -- ⊢ Metric.infDist x Kᶜ = dist x x
    rw [frontier_eq_closure_inter_closure] at hx'
    -- ⊢ Metric.infDist x Kᶜ = dist x x
    rw [Metric.infDist_zero_of_mem_closure hx'.2, dist_self]
    -- 🎉 no goals
#align is_compact.exists_mem_frontier_inf_dist_compl_eq_dist IsCompact.exists_mem_frontier_infDist_compl_eq_dist

/-- In a finite dimensional vector space over `ℝ`, the series `∑ x, ‖f x‖` is unconditionally
summable if and only if the series `∑ x, f x` is unconditionally summable. One implication holds in
any complete normed space, while the other holds only in finite dimensional spaces. -/
theorem summable_norm_iff {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : α → E} : (Summable fun x => ‖f x‖) ↔ Summable f := by
  refine' ⟨summable_of_summable_norm, fun hf => _⟩
  -- ⊢ Summable fun x => ‖f x‖
  -- First we use a finite basis to reduce the problem to the case `E = Fin N → ℝ`
  suffices ∀ {N : ℕ} {g : α → Fin N → ℝ}, Summable g → Summable fun x => ‖g x‖ by
    obtain v := finBasis ℝ E
    set e := v.equivFunL
    have : Summable fun x => ‖e (f x)‖ := this (e.summable.2 hf)
    refine'
      summable_of_norm_bounded _ (this.mul_left ↑‖(e.symm : (Fin (finrank ℝ E) → ℝ) →L[ℝ] E)‖₊)
        fun i => _
    simpa using (e.symm : (Fin (finrank ℝ E) → ℝ) →L[ℝ] E).le_op_norm (e <| f i)
  clear! E
  -- ⊢ ∀ {N : ℕ} {g : α → Fin N → ℝ}, Summable g → Summable fun x => ‖g x‖
  -- Now we deal with `g : α → Fin N → ℝ`
  intro N g hg
  -- ⊢ Summable fun x => ‖g x‖
  have : ∀ i, Summable fun x => ‖g x i‖ := fun i => (Pi.summable.1 hg i).abs
  -- ⊢ Summable fun x => ‖g x‖
  refine'
    summable_of_norm_bounded _ (summable_sum fun i (_ : i ∈ Finset.univ) => this i) fun x => _
  rw [norm_norm, pi_norm_le_iff_of_nonneg]
  -- ⊢ ∀ (i : Fin N), ‖g x i‖ ≤ ∑ i : Fin N, ‖g x i‖
  · refine' fun i => Finset.single_le_sum (f := fun i => ‖g x i‖) (fun i _ => _) (Finset.mem_univ i)
    -- ⊢ 0 ≤ (fun i => ‖g x i‖) i
    exact norm_nonneg (g x i)
    -- 🎉 no goals
  · exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    -- 🎉 no goals
#align summable_norm_iff summable_norm_iff

theorem summable_of_isBigO' {ι E F : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : ι → E} {g : ι → F}
    (hg : Summable g) (h : f =O[cofinite] g) : Summable f :=
  summable_of_isBigO (summable_norm_iff.mpr hg) h.norm_right
set_option linter.uppercaseLean3 false in
#align summable_of_is_O' summable_of_isBigO'

theorem summable_of_isBigO_nat' {E F : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : ℕ → E} {g : ℕ → F}
    (hg : Summable g) (h : f =O[atTop] g) : Summable f :=
  summable_of_isBigO_nat (summable_norm_iff.mpr hg) h.norm_right
set_option linter.uppercaseLean3 false in
#align summable_of_is_O_nat' summable_of_isBigO_nat'

theorem summable_of_isEquivalent {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ι → E} {g : ι → E} (hg : Summable g) (h : f ~[cofinite] g) :
    Summable f :=
  hg.trans_sub (summable_of_isBigO' hg h.isLittleO.isBigO)
#align summable_of_is_equivalent summable_of_isEquivalent

theorem summable_of_isEquivalent_nat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ℕ → E} {g : ℕ → E} (hg : Summable g) (h : f ~[atTop] g) :
    Summable f :=
  hg.trans_sub (summable_of_isBigO_nat' hg h.isLittleO.isBigO)
#align summable_of_is_equivalent_nat summable_of_isEquivalent_nat

theorem IsEquivalent.summable_iff {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ι → E} {g : ι → E} (h : f ~[cofinite] g) :
    Summable f ↔ Summable g :=
  ⟨fun hf => summable_of_isEquivalent hf h.symm, fun hg => summable_of_isEquivalent hg h⟩
#align is_equivalent.summable_iff IsEquivalent.summable_iff

theorem IsEquivalent.summable_iff_nat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ℕ → E} {g : ℕ → E} (h : f ~[atTop] g) : Summable f ↔ Summable g :=
  ⟨fun hf => summable_of_isEquivalent_nat hf h.symm, fun hg => summable_of_isEquivalent_nat hg h⟩
#align is_equivalent.summable_iff_nat IsEquivalent.summable_iff_nat
