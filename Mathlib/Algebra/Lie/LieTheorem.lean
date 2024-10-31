/-
Copyright (c) 2024 Lucas Whitfield. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Whitfield, Johan Commelin
-/
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.AltWeights

/-!
# Lie's theorem for Solvable Lie algebras.

Lie's theorem asserts that Lie modules of solvable Lie algebras over fields of characteristic 0
have a common eigenvector for the action of all elements of the Lie algebra.
This result is named `LieModule.exists_forall_lie_eq_smul_of_isSolvable`.
-/

section

variable {k : Type*} [Field k]
variable {L : Type*} [LieRing L] [LieAlgebra k L]
variable {V : Type*} [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]

variable [CharZero k] [Module.Finite k V]

open LieModule Submodule in
theorem extend_weight [LieModule.IsTriangularizable k L V]
    (A : LieIdeal k L) (hA : IsCoatom A.toSubmodule)
    (χ₀ : Module.Dual k A) (v₀ : V) (hv₀ : v₀ ≠ 0) (hv₀A : ∀ (x : A), ⁅x, v₀⁆ = χ₀ x • v₀) :
    ∃ (χ : Module.Dual k L) (v : V), v ≠ 0 ∧ ∀ (x : L), ⁅x, v⁆ = χ x • v := by
  obtain ⟨z, -, hz⟩ := SetLike.exists_of_lt (hA.lt_top)
  let e : (k ∙ z) ≃ₗ[k] k := (LinearEquiv.toSpanNonzeroSingleton k L z <| by aesop).symm
  have he : ∀ x, e x • z = x := by simp [e]
  have hA : IsCompl A.toSubmodule (k ∙ z) := isCompl_span_of_iscoatom_of_not_mem _ _ hA hz
  let π₁ : L →ₗ[k] A       := A.toSubmodule.linearProjOfIsCompl (k ∙ z) hA
  let π₂ : L →ₗ[k] (k ∙ z) := (k ∙ z).linearProjOfIsCompl ↑A hA.symm

  set Vχ₀ := altWeightSpace (L := L) (V := V) χ₀
  obtain ⟨c, hc⟩ : ∃ c, (toEnd k _ Vχ₀ z).HasEigenvalue c := by
    have : Nontrivial Vχ₀ := nontrivial_of_ne ⟨v₀, hv₀A⟩ 0 <| Subtype.coe_ne_coe.mp hv₀
    apply Module.End.exists_hasEigenvalue_of_genEigenspace_eq_top
    exact LieModule.IsTriangularizable.maxGenEigenspace_eq_top z
  obtain ⟨⟨v, hv⟩, hvc⟩ := hc.exists_hasEigenvector

  use (χ₀.comp π₁) + c • (e.comp π₂), v
  constructor
  · simpa only [ne_eq, LieSubmodule.mk_eq_zero] using hvc.right
  · intro x
    have hπ : (π₁ x : L) + π₂ x = x := linear_proj_add_linearProjOfIsCompl_eq_self hA x
    suffices ⁅(π₂ x : L), v⁆ = (c • e (π₂ x)) • v by
      calc ⁅x, v⁆
          = ⁅π₁ x, v⁆       + ⁅(π₂ x : L), v⁆    := congr(⁅$hπ.symm, v⁆) ▸ add_lie _ _ _
        _ =  χ₀ (π₁ x) • v  + (c • e (π₂ x)) • v := by rw [hv (π₁ x), this]
        _ = _ := by simp [add_smul]
    calc ⁅(π₂ x : L), v⁆
        = e (π₂ x) • ↑(c • ⟨v, hv⟩ : Vχ₀) := by rw [← he, smul_lie, ← hvc.apply_eq_smul]; rfl
      _ = (c • e (π₂ x)) • v              := by rw [smul_assoc, smul_comm]; rfl

variable (k L V)
variable [Nontrivial V]

open LieAlgebra

-- This lemma is the central inductive argument in the proof of Lie's theorem below.
-- The statement is identical to `LieModule.exists_forall_lie_eq_smul_of_isSolvable`
-- except that it additionally assumes a finiteness hypothesis.
private lemma LieModule.exists_forall_lie_eq_smul_of_isSolvable_of_finite
    (L : Type*) [LieRing L] [LieAlgebra k L] [LieRingModule L V] [LieModule k L V]
    [IsSolvable k L] [LieModule.IsTriangularizable k L V] [Module.Finite k L] :
    ∃ χ : Module.Dual k L, ∃ v : V, v ≠ 0 ∧ ∀ x : L, ⁅x, v⁆ = χ x • v := by
  obtain H|⟨A, hA, hAL⟩ := eq_top_or_exists_le_coatom (derivedSeries k L 1).toSubmodule
  · obtain _|_ := subsingleton_or_nontrivial L
    · use 0
      simpa using exists_ne _
    · rw [LieSubmodule.coeSubmodule_eq_top_iff] at H
      exact ((derivedSeries_lt_top_of_solvable k L).ne H).elim
  lift A to LieIdeal k L
  · intros
    exact hAL <| LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)
  change LieIdeal k L at A -- remove this line when bug in `lift` is fixed (#15865)
  obtain ⟨χ', v, hv, hvA⟩ := exists_forall_lie_eq_smul_of_isSolvable_of_finite A
  exact extend_weight A hA χ' v hv hvA
termination_by Module.finrank k L
decreasing_by
  simp_wf
  rw [← finrank_top k L]
  apply Submodule.finrank_lt_finrank_of_lt
  exact hA.lt_top

local notation "π" => LieModule.toEnd k L V

/-- **Lie's theorem**: Lie modules of solvable Lie algebras over fields of characteristic 0
have a common eigenvector for the action of all elements of the Lie algebra. -/
theorem LieModule.exists_forall_lie_eq_smul_of_isSolvable
    [IsSolvable k L] [LieModule.IsTriangularizable k L V] :
    ∃ χ : Module.Dual k L, ∃ v : V, v ≠ 0 ∧ ∀ x : L, ⁅x, v⁆ = χ x • v := by
  let imL := (π).range
  let toEndo : L →ₗ[k] imL := LinearMap.codRestrict imL.toSubmodule π
      (fun x ↦ LinearMap.mem_range.mpr ⟨x, rfl⟩ : ∀ x : L, π x ∈ imL)
  have ⟨χ, v, hv, hχ⟩ := exists_forall_lie_eq_smul_of_isSolvable_of_finite k V imL
  use χ.comp toEndo, v, hv
  intro x
  have : ⁅x, v⁆ = ⁅toEndo x, v⁆ := rfl
  simpa [← hχ, toEndo] using this

end

