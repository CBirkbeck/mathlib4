import Mathlib.Tactic.Tendsto.Multiseries.BasicNew
import Mathlib.Tactic.Tendsto.TendstoM

namespace TendstoTactic

namespace PreMS

-- make basis explicit if further you will always have to specify it

inductive isFlatZero : {basis : Basis} → PreMS basis → Prop
| const {c : ℝ} (h : c = 0) : isFlatZero (basis := []) c
| nil {basis_hd : _} {basis_tl : _} : isFlatZero (basis := basis_hd :: basis_tl) CoList.nil

theorem isFlatZero_cons {basis_hd : _} {basis_tl : _} {deg : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} :
    ¬(isFlatZero (basis := (basis_hd :: basis_tl)) (CoList.cons (deg, coef) tl)) := by
  sorry

inductive isTrimmed : {basis : Basis} → PreMS basis → Prop
| const {c : ℝ} : isTrimmed (basis := []) c
| nil {basis_hd : _} {basis_tl : _} : isTrimmed (basis := basis_hd :: basis_tl) CoList.nil
| cons {basis_hd : _} {basis_tl : _} {deg : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
  (h_trimmed : coef.isTrimmed) (h_ne_flat_zero : ¬ coef.isFlatZero) : isTrimmed (basis := basis_hd :: basis_tl) (CoList.cons (deg, coef) tl)

theorem isTrimmed_cons {basis_hd : _} {basis_tl : _} {deg : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : isTrimmed (basis := basis_hd :: basis_tl) (CoList.cons (deg, coef) tl)) :
    coef.isTrimmed ∧ ¬ coef.isFlatZero := by
  apply h.casesOn (motive := fun {basis : Basis} (a : PreMS basis) (h_trimmed : a.isTrimmed) =>
    (h_basis : basis = basis_hd :: basis_tl) → (a = h_basis ▸ (CoList.cons (deg, coef) tl)) → coef.isTrimmed ∧ ¬ coef.isFlatZero)
  · intro _ h_basis
    simp at h_basis
  · intro _ _ h_basis h
    simp at h_basis
    obtain ⟨h_basis_hd, h_basis_tl⟩ := h_basis
    subst h_basis_hd h_basis_tl
    simp at h
    apply (CoList.noConfusion _ _ h.symm).elim
  · intro _ _ deg coef tl h_trimmed h_ne_flat_zero h_basis h
    simp at h_basis
    obtain ⟨h_basis_hd, h_basis_tl⟩ := h_basis
    subst h_basis_hd h_basis_tl
    simp at h
    obtain ⟨h_hd, _⟩ := CoList.cons_eq_cons h
    simp at h_hd
    rw [← h_hd.2]
    exact ⟨h_trimmed, h_ne_flat_zero⟩
  · rfl
  · rfl

inductive hasNegativeLeading : {basis : Basis} → (ms : PreMS basis) → Prop
| cons {basis_hd : ℝ → ℝ} {basis_tl : List (ℝ → ℝ)} {deg : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : deg < 0) : hasNegativeLeading (basis := basis_hd :: basis_tl) (.cons (deg, coef) tl)

def isPartiallyTrimmed {basis : Basis} (ms : PreMS basis) : Prop :=
  ms.hasNegativeLeading ∨ ms.isTrimmed

namespace Trimming

theorem PreMS.isApproximation_sub_zero {basis : Basis} {ms : PreMS basis} {F C : ℝ → ℝ}
    (h_approx : ms.isApproximation (F - C) basis) (h_C : C =ᶠ[Filter.atTop] 0) : ms.isApproximation F basis := by
  apply PreMS.isApproximation_of_EventuallyEq h_approx
  have := Filter.EventuallyEq.sub (Filter.EventuallyEq.refl _ F) h_C
  simpa using this

structure PreMS.TrimmingResult {basis : Basis} (ms : PreMS basis) where
  result : PreMS basis
  h_wo : ms.wellOrdered → result.wellOrdered
  h_approx : ∀ F, ms.isApproximation F basis → result.isApproximation F basis
  h_trimmed : result.isTrimmed

def maxUnfoldingSteps : ℕ := 20

def PreMS.trim {basis : Basis} (ms : PreMS basis) (stepsLeft := maxUnfoldingSteps) : TendstoM <| PreMS.TrimmingResult ms :=
  match stepsLeft with
  | 0 => do throw TendstoException.trimmingException
  | stepsLeftNext + 1 => do
    match basis with
    | [] => return {
        result := ms
        h_wo := by simp [PreMS.wellOrdered]
        h_approx := by simp
        h_trimmed := by constructor
      }
    | basis_hd :: basis_tl =>
      ms.casesOn (motive := fun x ↦ TendstoM (TrimmingResult (basis := basis_hd :: basis_tl) x))
        (nil := do return {
          result := .nil
          h_wo := by simp [PreMS.wellOrdered]
          h_approx := by simp
          h_trimmed := by constructor
        })
        (cons := fun (deg, coef) tl => do
          let coef_trimmed ← PreMS.trim coef stepsLeftNext
          match basis_tl with
          | [] =>
            match ← TendstoTactic.runOracle coef with
            | .zero h_c_zero =>
              let tl_trimmed ← PreMS.trim tl stepsLeftNext
              return {
                result := tl_trimmed.result
                h_wo := by
                  intro h_wo
                  replace h_wo := wellOrdered_cons h_wo
                  exact tl_trimmed.h_wo h_wo.right
                h_approx := by
                  intro F h_approx
                  replace h_approx := isApproximation_cons h_approx
                  obtain ⟨C, h_coef, h_comp, h_tl⟩ := h_approx
                  simp [isApproximation] at h_coef
                  subst h_c_zero
                  apply tl_trimmed.h_approx
                  apply isApproximation_sub_zero h_tl
                  have := Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ (fun x ↦ basis_hd x ^ deg)) h_coef
                  simpa using this
                h_trimmed := tl_trimmed.h_trimmed
              }
            | .pos h_c_pos => return {
                result := .cons (deg, coef_trimmed.result) tl
                h_wo := by
                  intro h_wo
                  replace h_wo := wellOrdered_cons h_wo
                  sorry
                  -- exact tl_trimmed.h_wo h_wo.right
                  -- simp [PreMS.wellOrdered] at h_wo
                  -- unfold PreMS.wellOrdered
                  -- constructor
                  -- · exact coef_trimmed.h_wo h_wo.left
                  -- · exact h_wo.right
                h_approx := by
                  intro F h_approx
                  replace h_approx := isApproximation_cons h_approx
                  obtain ⟨C, h_coef, h_comp, h_tl⟩ := h_approx
                  apply PreMS.isApproximation.cons C
                  · exact coef_trimmed.h_approx _ h_coef
                  · exact h_comp
                  · exact h_tl
                h_trimmed := by
                  -- simp [PreMS.isTrimmed]
                  constructor
                  · exact coef_trimmed.h_trimmed
                  · intro h
                    cases h with | const h =>
                    have : coef = 0 := by
                      have : isApproximation (fun x ↦ coef) [] coef_trimmed.result := by
                        apply coef_trimmed.h_approx (fun _ ↦ coef)
                        simp [isApproximation]
                      rw [h] at this
                      simp [isApproximation, Filter.EventuallyEq] at this
                      obtain ⟨w, this⟩ := this
                      specialize this (w + 1)
                      apply this
                      linarith
                    linarith
              }
            | .neg h_c_neg => return { -- copypaste from pos
                result := .cons (deg, coef_trimmed.result) tl
                h_wo := by
                  intro h_wo
                  replace h_wo := wellOrdered_cons h_wo
                  sorry
                  -- exact tl_trimmed.h_wo h_wo.right
                  -- simp [PreMS.wellOrdered] at h_wo
                  -- unfold PreMS.wellOrdered
                  -- constructor
                  -- · exact coef_trimmed.h_wo h_wo.left
                  -- · exact h_wo.right
                h_approx := by
                  intro F h_approx
                  replace h_approx := isApproximation_cons h_approx
                  obtain ⟨C, h_coef, h_comp, h_tl⟩ := h_approx
                  apply PreMS.isApproximation.cons C
                  · exact coef_trimmed.h_approx _ h_coef
                  · exact h_comp
                  · exact h_tl
                h_trimmed := by
                  -- simp [PreMS.isTrimmed]
                  constructor
                  · exact coef_trimmed.h_trimmed
                  · intro h
                    cases h with | const h =>
                    have : coef = 0 := by
                      have : isApproximation (fun x ↦ coef) [] coef_trimmed.result := by
                        apply coef_trimmed.h_approx (fun _ ↦ coef)
                        simp [isApproximation]
                      rw [h] at this
                      simp [isApproximation, Filter.EventuallyEq] at this
                      obtain ⟨w, this⟩ := this
                      specialize this (w + 1)
                      apply this
                      linarith
                    linarith
              }
          | basis_tl_hd :: basis_tl_tl =>
            coef_trimmed.result.casesOn (motive := fun x => coef_trimmed.result = x → TendstoM (TrimmingResult (basis := basis_hd :: basis_tl_hd :: basis_tl_tl) (CoList.cons (deg, coef) tl)))
              (nil := fun h_coef_trimmed => do
                let tl_trimmed ← PreMS.trim tl stepsLeftNext
                return {
                  result := tl_trimmed.result
                  h_wo := by
                    intro h_wo
                    replace h_wo := wellOrdered_cons h_wo
                    exact tl_trimmed.h_wo h_wo.right
                  h_approx := by
                    intro F h_approx
                    replace h_approx := isApproximation_cons h_approx
                    obtain ⟨C, h_coef, h_comp, h_tl⟩ := h_approx
                    -- simp [isApproximation] at h_coef
                    -- subst h_c_zero
                    apply tl_trimmed.h_approx
                    apply isApproximation_sub_zero h_tl
                    have hC : C =ᶠ[Filter.atTop] 0 := by
                      have := h_coef_trimmed ▸ coef_trimmed.h_approx C h_coef
                      exact isApproximation_nil this
                    have := Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ (fun x ↦ basis_hd x ^ deg)) hC
                    simpa using this
                  h_trimmed := tl_trimmed.h_trimmed
                }
              )
              (cons := fun (tl_deg, tl_coef) tl_tl => fun h_coef_trimmed => do
                return {
                  result := .cons (deg, coef_trimmed.result) tl
                  h_wo := by
                    intro h_wo
                    replace h_wo := wellOrdered_cons h_wo
                    sorry
                    -- exact tl_trimmed.h_wo h_wo.right
                    -- simp [PreMS.wellOrdered] at h_wo
                    -- unfold PreMS.wellOrdered
                    -- constructor
                    -- · exact coef_trimmed.h_wo h_wo.left
                    -- · exact h_wo.right
                  h_approx := by
                    intro F h_approx
                    replace h_approx := isApproximation_cons h_approx
                    obtain ⟨C, h_coef, h_comp, h_tl⟩ := h_approx
                    apply PreMS.isApproximation.cons C
                    · exact coef_trimmed.h_approx _ h_coef
                    · exact h_comp
                    · exact h_tl
                  h_trimmed := by
                    constructor
                    · exact coef_trimmed.h_trimmed
                    · rw [h_coef_trimmed]
                      apply isFlatZero_cons
                }
              )
              (by rfl)
        )

end Trimming

end PreMS

open PreMS.Trimming

def MS.isTrimmed (ms : MS) : Prop :=
  ms.val.isTrimmed

structure MS.TrimmingResult (ms : MS) where
  result : MS
  h_eq_basis : ms.basis = result.basis
  h_eq_F : ms.F = result.F
  h_trimmed : result.isTrimmed

def MS.trim (ms : MS) : TendstoM <| MS.TrimmingResult ms := do
  let r ← PreMS.trim ms.val
  return {
    result := {
      val := r.result
      basis := ms.basis
      F := ms.F
      h_wo := r.h_wo ms.h_wo
      h_approx := r.h_approx _ ms.h_approx
    }
    h_eq_basis := by rfl
    h_eq_F := by rfl
    h_trimmed := r.h_trimmed
  }

end TendstoTactic
