/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries.Basic
import Mathlib.Tactic.Tendsto.Multiseries.Basis

/-!
# Basic operations for multiseries: multiplication by constant and negation

-/

namespace TendstoTactic

namespace PreMS

open Stream'

/-- Multiplies all coefficient of the multiseries to `c`. -/
def mulConst {basis : Basis} (ms : PreMS basis) (c : ℝ) : PreMS basis :=
  match basis with
  | [] => ms * c
  | List.cons _ _ =>
    Seq.map (fun (exp, coef) => (exp, mulConst coef c)) ms

/-- Negates all coefficient of the multiseries. -/
def neg {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  ms.mulConst (-1)

/-- This instance is needed to create instance for `AddCommMonoid (PreMS basis)`, which is
necessary for using `abel` tactic in our proofs. -/
instance instNeg {basis : Basis} : Neg (PreMS basis) where
  neg := neg

/-- This instance is copy of the previous. But without it `Neg (PreMS (basis_hd :: basis_tl))` can
not be inferred. -/
instance {basis_hd : ℝ → ℝ} {basis_tl : Basis} : Neg (PreMS (basis_hd :: basis_tl)) := instNeg

-------------------- theorems

open Filter Asymptotics

@[simp]
theorem mulConst_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {c : ℝ} :
    @mulConst (basis_hd :: basis_tl) Seq.nil c = Seq.nil := by
  simp [mulConst]

@[simp]
theorem mulConst_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {c exp : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} :
    mulConst (basis := basis_hd :: basis_tl) (Seq.cons (exp, coef) tl) c =
    Seq.cons (exp, coef.mulConst c) (tl.mulConst c) := by
  simp [mulConst]

@[simp]
theorem mulConst_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)} {c : ℝ} :
    (mulConst ms c).leadingExp = ms.leadingExp := by
  cases ms <;> simp [mulConst]

@[simp]
theorem const_mulConst {basis : Basis} {x y : ℝ} :
    (const basis x).mulConst y = const basis (x * y) := by
  cases basis with
  | nil => simp [mulConst, const]
  | cons =>
    simp [mulConst, const]
    congr
    apply const_mulConst

/-- Multiplication by constant preserves well-orderedness. -/
theorem mulConst_WellOrdered {basis : Basis} {ms : PreMS basis} {c : ℝ}
    (h_wo : ms.WellOrdered) : (ms.mulConst c).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    let motive : (PreMS (basis_hd :: basis_tl)) → Prop := fun ms =>
      ∃ (X : PreMS (basis_hd :: basis_tl)), ms = X.mulConst c ∧ X.WellOrdered
    apply WellOrdered.coind motive
    · simp [motive]
      use ms
    · intro ms ih
      simp [motive] at ih
      obtain ⟨X, h_ms_eq, hX_wo⟩ := ih
      subst h_ms_eq
      cases' X with exp coef tl
      · left
        simp [mulConst]
      · obtain ⟨hX_coef_wo, hX_comp, hX_tl_wo⟩ := WellOrdered_cons hX_wo
        right
        use exp, coef.mulConst c, mulConst (basis := basis_hd :: basis_tl) tl c
        constructor
        · simp [mulConst]
        constructor
        · exact mulConst_WellOrdered hX_coef_wo
        constructor
        · simpa
        simp [motive]
        use tl

/-- If `ms` approximates `F`, then `ms.mulConst c` approximates `F * c`. -/
theorem mulConst_Approximates {basis : Basis} {ms : PreMS basis} {c : ℝ} {F : ℝ → ℝ}
    (h_approx : ms.Approximates F) :
    (ms.mulConst c).Approximates (fun x ↦ F x * c) := by
  cases basis with
  | nil =>
    simp [Approximates, mulConst] at *
    apply EventuallyEq.mul h_approx
    rfl
  | cons basis_hd basis_tl =>
    let motive : (ℝ → ℝ) → (PreMS (basis_hd :: basis_tl)) → Prop := fun f ms' =>
      ∃ (X : PreMS (basis_hd :: basis_tl)) (fX : ℝ → ℝ),
        ms' = X.mulConst c ∧ f =ᶠ[atTop] (fun x ↦ fX x * c) ∧
        X.Approximates fX
    apply Approximates.coind motive
    · simp only [motive]
      use ms, F
    · intro f ms ih
      simp only [motive] at ih
      obtain ⟨X, fX, h_ms_eq, hf_eq, hX_approx⟩ := ih
      cases' X with X_exp X_coef X_tl
      · left
        apply Approximates_nil at hX_approx
        simp [mulConst] at h_ms_eq
        constructor
        · exact h_ms_eq
        trans
        · exact hf_eq
        conv =>
          rhs
          ext x
          simp
          rw [← zero_mul c]
        apply EventuallyEq.mul hX_approx
        rfl
      · obtain ⟨XC, hX_coef, hX_maj, hX_tl⟩ := Approximates_cons hX_approx
        right
        simp [mulConst] at h_ms_eq
        use ?_, ?_, ?_, fun x ↦ XC x * c
        constructor
        · exact h_ms_eq
        constructor
        · exact mulConst_Approximates hX_coef
        constructor
        · apply majorated_of_EventuallyEq hf_eq
          exact mul_const_majorated hX_maj
        simp only [motive]
        use X_tl, fun x ↦ fX x - basis_hd x ^ X_exp * XC x
        constructor
        · rfl
        constructor
        · apply eventuallyEq_iff_sub.mpr
          eta_expand
          simp
          ring_nf!
          apply eventuallyEq_iff_sub.mp
          conv => rhs; ext; rw [mul_comm]
          exact hf_eq
        · exact hX_tl

@[simp]
theorem neg_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X : PreMS (basis_hd :: basis_tl)} :
    X.neg.leadingExp = X.leadingExp := by
  simp [neg]

theorem neg_WellOrdered {basis : Basis} {ms : PreMS basis}
    (h_wo : ms.WellOrdered) : ms.neg.WellOrdered :=
  mulConst_WellOrdered h_wo

theorem neg_Approximates {basis : Basis} {ms : PreMS basis} {F : ℝ → ℝ}
    (h_approx : ms.Approximates F) : ms.neg.Approximates (-F) := by
  rw [← mul_neg_one]
  eta_expand
  simp only [Pi.one_apply, Pi.neg_apply, Pi.mul_apply]
  apply mulConst_Approximates h_approx

@[simp]
theorem neg_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    neg (basis := basis_hd :: basis_tl) Seq.nil = Seq.nil := by
  simp [neg]

@[simp]
theorem neg_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} :
    neg (basis := basis_hd :: basis_tl) (Seq.cons (exp, coef) tl) =
    Seq.cons (exp, coef.neg) tl.neg := by
  simp [neg]

end PreMS

end TendstoTactic
