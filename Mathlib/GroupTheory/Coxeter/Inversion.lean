/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.GroupTheory.Coxeter.Length

/-!
# Reflections, inversions, and inversion sequences

Throughout this file, `B` is a type and `M : CoxeterMatrix B` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* M.group`, where `M.group` refers to the quotient of the free group on
`B` by the Coxeter relations given by the matrix `M`. See `Mathlib/GroupTheory/Coxeter/Basic.lean`
for more details.

We define a *reflection* (`CoxeterSystem.IsReflection`) to be an element of the form
$t = u s_i u^{-1}$, where $u \in W$ and $s_i$ is a simple reflection. We say that a reflection $t$
is a *left inversion* (`CoxeterSystem.IsLeftInversion`) of an element $w \in W$ if
$\ell(t w) < \ell(w)$, and we say it is a *right inversion* (`CoxeterSystem.IsRightInversion`) of
$w$ if $\ell(w t) > \ell(w)$. Here $\ell$ is the length function
(see `Mathlib/GroupTheory/Coxeter/Length.lean`).

Given a word, we define its *left inversion sequence* (`CoxeterSystem.leftInvSeq`) and its
*right inversion sequence* (`CoxeterSystem.rightInvSeq`). We prove that if a word is reduced, then
both of its inversion sequences contain no duplicates. In fact, the right (respectively, left)
inversion sequence of a reduced word for $w$ consists of all of the right (respectively, left)
inversions of $w$ in some order, but we do not prove that in this file.

## Main definitions

* `CoxeterSystem.IsReflection`
* `CoxeterSystem.IsLeftInversion`
* `CoxeterSystem.IsRightInversion`
* `CoxeterSystem.leftInvSeq`
* `CoxeterSystem.rightInvSeq`

## References

* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*](bjorner2005)

-/

namespace CoxeterSystem

open List Matrix Function

variable {B : Type*}
variable {W : Type*} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length

/-- The proposition that `t` is a reflection of the Coxeter system `cs`; i.e., it is of the form
$w s_i w^{-1}$, where $w \in W$ and $s_i$ is a simple reflection. -/
def IsReflection (t : W) : Prop := ∃ w i, t = w * s i * w⁻¹

theorem isReflection_simple (i : B) : cs.IsReflection (s i) := by use 1, i; simp

theorem pow_two_eq_one_of_isReflection {t : W} (ht : cs.IsReflection t) : t ^ 2 = 1 := by
  rcases ht with ⟨w, i, rfl⟩
  simp

theorem mul_self_eq_one_of_isReflection {t : W} (ht : cs.IsReflection t) : t * t = 1 := by
  rcases ht with ⟨w, i, rfl⟩
  simp

theorem inv_eq_self_of_isReflection {t : W} (ht : cs.IsReflection t) : t⁻¹ = t := by
  rcases ht with ⟨w, i, rfl⟩
  group
  simp

theorem length_reflection_odd {t : W} (ht : cs.IsReflection t) : Odd (ℓ t) := by
  rcases ht with ⟨w, i, rfl⟩
  rw [Nat.odd_iff, length_mul_mod_two, Nat.add_mod, length_mul_mod_two, ← Nat.add_mod,
      length_simple, length_inv, add_comm, ← add_assoc, ← two_mul, Nat.mul_add_mod]
  norm_num

alias odd_length_of_isReflection := length_reflection_odd

theorem length_mul_reflection_ne (w : W) {t : W} (ht : cs.IsReflection t) : ℓ (w * t) ≠ ℓ w := by
  apply_fun (· % 2)
  dsimp only
  rw [length_mul_mod_two]
  intro h
  have := h ▸ Nat.mod_two_add_add_odd_mod_two (ℓ w) (cs.length_reflection_odd ht)
  exact Nat.add_self_ne_one _ this

theorem length_reflection_mul_ne (w : W) {t : W} (ht : cs.IsReflection t) : ℓ (t * w) ≠ ℓ w := by
  apply_fun (· % 2)
  dsimp only
  rw [length_mul_mod_two]
  intro h
  have := h.symm ▸ Nat.mod_two_add_add_odd_mod_two (ℓ w) (cs.length_reflection_odd ht)
  exact Nat.add_self_ne_one _ (add_comm (ℓ t) _ ▸ this)

@[simp]
theorem isReflection_conjugate_iff (w t : W) :
    cs.IsReflection (w * t * w⁻¹) ↔ cs.IsReflection t := by
  constructor
  · rintro ⟨u, i, hi⟩
    use w⁻¹ * u, i
    apply mul_left_cancel (a := w)
    apply mul_right_cancel (b := w⁻¹)
    rw [hi]
    group
  · rintro ⟨u, i, rfl⟩
    use w * u, i
    group

/-- The proposition that `t` is a right inversion of `w`; i.e., `t` is a reflection and
$\ell (w t) < \ell(w)$. -/
def IsRightInversion (w t : W) : Prop := cs.IsReflection t ∧ ℓ (w * t) < ℓ w

/-- The proposition that `t` is a left inversion of `w`; i.e., `t` is a reflection and
$\ell (t w) < \ell(w)$. -/
def IsLeftInversion (w t : W) : Prop := cs.IsReflection t ∧ ℓ (t * w) < ℓ w

theorem isRightInversion_inv_iff {w t : W} :
    cs.IsRightInversion w⁻¹ t ↔ cs.IsLeftInversion w t := by
  apply and_congr_right
  intro ht
  rw [← length_inv, mul_inv_rev, inv_inv, cs.inv_eq_self_of_isReflection ht, cs.length_inv w]

theorem isLeftInversion_inv_iff {w t : W} :
    cs.IsLeftInversion w⁻¹ t ↔ cs.IsRightInversion w t := by
  convert cs.isRightInversion_inv_iff.symm
  simp

theorem isRightInversion_mul_iff_of_isReflection {w t : W} (ht : cs.IsReflection t) :
    cs.IsRightInversion (w * t) t ↔ ¬cs.IsRightInversion w t := by
  unfold IsRightInversion
  simp only [mul_assoc, cs.mul_self_eq_one_of_isReflection ht, mul_one, ht, true_and,
    not_lt]
  constructor
  · exact le_of_lt
  · exact (lt_of_le_of_ne' · (cs.length_mul_reflection_ne w ht))

theorem not_isRightInversion_mul_iff_of_isReflection {w t : W} (ht : cs.IsReflection t) :
    ¬cs.IsRightInversion (w * t) t ↔ cs.IsRightInversion w t :=
  (iff_not_comm.mp (cs.isRightInversion_mul_iff_of_isReflection ht)).symm

theorem isLeftInversion_mul_iff_of_isReflection {w t : W} (ht : cs.IsReflection t) :
    cs.IsLeftInversion (t * w) t ↔ ¬cs.IsLeftInversion w t := by
  unfold IsLeftInversion
  simp only [← mul_assoc, cs.mul_self_eq_one_of_isReflection ht, one_mul, ht, true_and,
    not_lt]
  constructor
  · exact le_of_lt
  · exact (lt_of_le_of_ne' · (cs.length_reflection_mul_ne w ht))

theorem not_isLeftInversion_mul_iff_of_isReflection {w t : W} (ht : cs.IsReflection t) :
    ¬cs.IsLeftInversion (t * w) t ↔ cs.IsLeftInversion w t :=
  (iff_not_comm.mp (cs.isLeftInversion_mul_iff_of_isReflection ht)).symm

@[simp]
theorem isRightInversion_simple_iff_isRightDescent (w : W) (i : B) :
    cs.IsRightInversion w (s i) ↔ cs.IsRightDescent w i := by
  unfold IsRightInversion IsRightDescent
  have := cs.isReflection_simple i
  tauto

@[simp]
theorem isLeftInversion_simple_iff_isLeftDescent (w : W) (i : B) :
    cs.IsLeftInversion w (s i) ↔ cs.IsLeftDescent w i := by
  unfold IsLeftInversion IsLeftDescent
  have := cs.isReflection_simple i
  tauto

/-- The right inversion sequence of `ω`. The right inversion sequence of a word
$s_{i_1} \cdots s_{i_\ell}$ is the sequence
$$s_{i_\ell}\cdots s_{i_1}\cdots s_{i_\ell}, \ldots,
    s_{i_{\ell}}s_{i_{\ell - 1}}s_{i_{\ell - 2}}s_{i_{\ell - 1}}s_{i_\ell}, \ldots,
    s_{i_{\ell}}s_{i_{\ell - 1}}s_{i_\ell}, s_{i_\ell}.$$
-/
def rightInvSeq (ω : List B) : List W :=
  match ω with
  | []          => []
  | i :: ω      => (π ω)⁻¹ * (s i) * (π ω) :: rightInvSeq ω

/-- The left inversion sequence of `ω`. The left inversion sequence of a word
$s_{i_1} \cdots s_{i_\ell}$ is the sequence
$$s_{i_1}, s_{i_1}s_{i_2}s_{i_1}, s_{i_1}s_{i_2}s_{i_3}s_{i_2}s_{i_1}, \ldots,
    s_{i_1}\cdots s_{i_\ell}\cdots s_{i_1}.$$
-/
def leftInvSeq (ω : List B) : List W :=
  match ω with
  | []          => []
  | i :: ω      => s i :: List.map (MulAut.conj (s i)) (leftInvSeq ω)

local prefix:100 "ris" => cs.rightInvSeq
local prefix:100 "lis" => cs.leftInvSeq

@[simp] theorem rightInvSeq_nil : ris [] = [] := rfl

@[simp] theorem leftInvSeq_nil : lis [] = [] := rfl

@[simp] theorem rightInvSeq_singleton (i : B) : ris [i] = [s i] := by simp [rightInvSeq]

@[simp] theorem leftInvSeq_singleton (i : B) : lis [i] = [s i] := rfl

theorem rightInvSeq_concat (ω : List B) (i : B) :
    ris (ω.concat i) = (List.map (MulAut.conj (s i)) (ris ω)).concat (s i) := by
  induction' ω with j ω ih
  · simp
  · dsimp [rightInvSeq]
    rw [ih]
    simp only [concat_eq_append, wordProd_append, wordProd_cons, wordProd_nil, mul_one, mul_inv_rev,
      inv_simple, cons_append, cons.injEq, and_true]
    group

theorem leftInvSeq_concat (ω : List B) (i : B) :
    lis (ω.concat i) = (lis ω).concat ((π ω) * (s i) * (π ω)⁻¹) := by
  induction' ω with j ω ih
  · simp
  · dsimp [leftInvSeq]
    rw [ih]
    simp only [concat_eq_append, map_append, map_cons, _root_.map_mul, MulAut.conj_apply,
      inv_simple, map_inv, mul_inv_rev, map_nil, wordProd_cons, cons_append, cons.injEq,
      append_cancel_left_eq, and_true, true_and]
    group
    simp [mul_assoc]

private theorem leftInvSeq_eq_reverse_rightInvSeq_reverse (ω : List B) :
    lis ω = (ris ω.reverse).reverse := by
  induction' ω with i ω ih
  · simp
  · rw [leftInvSeq, reverse_cons, ← concat_eq_append, rightInvSeq_concat, ih]
    simp [map_reverse]

theorem rightInvSeq_reverse (ω : List B) :
    ris (ω.reverse) = (lis ω).reverse := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

theorem leftInvSeq_reverse (ω : List B) :
    lis (ω.reverse) = (ris ω).reverse := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

@[simp] theorem length_rightInvSeq (ω : List B) : (ris ω).length = ω.length := by
  induction' ω with i ω ih
  · simp
  · simpa [rightInvSeq]

@[simp] theorem length_leftInvSeq (ω : List B) : (lis ω).length = ω.length := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

theorem getD_rightInvSeq (ω : List B) (j : ℕ) :
    (ris ω).getD j 1 = (π (ω.drop (j + 1)))⁻¹
        * (Option.map (cs.simple) (ω.get? j)).getD 1
        * π (ω.drop (j + 1)) := by
  induction' ω with i ω ih generalizing j
  · simp
  · dsimp only [rightInvSeq]
    rcases j with _ | j'
    · simp [getD_cons_zero]
    · simp [getD_cons_succ, ih j']

theorem getD_leftInvSeq (ω : List B) (j : ℕ) :
    (lis ω).getD j 1 = π (ω.take j)
        * (Option.map (cs.simple) (ω.get? j)).getD 1
        * (π (ω.take j))⁻¹ := by
  induction' ω with i ω ih generalizing j
  · simp
  · dsimp [leftInvSeq]
    rcases j with _ | j'
    · simp [getD_cons_zero]
    · rw [getD_cons_succ]
      rw [(by simp : 1 = ⇑(MulAut.conj (s i)) 1)]
      rw [getD_map]
      rw [ih j']
      simp [← mul_assoc, wordProd_cons]

theorem getD_rightInvSeq_mul_self (ω : List B) (j : ℕ) :
    ((ris ω).getD j 1) * ((ris ω).getD j 1) = 1 := by
  simp [getD_rightInvSeq, mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [get?_eq_get hj]
    simp [← mul_assoc]
  · rw [get?_eq_none.mpr (by linarith)]
    simp

theorem getD_leftInvSeq_mul_self (ω : List B) (j : ℕ) :
    ((lis ω).getD j 1) * ((lis ω).getD j 1) = 1 := by
  simp [getD_leftInvSeq, mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [get?_eq_get hj]
    simp [← mul_assoc]
  · rw [get?_eq_none.mpr (by linarith)]
    simp

theorem rightInvSeq_drop (ω : List B) (j : ℕ) :
    ris (ω.drop j) = (ris ω).drop j := by
  induction' j with j ih₁ generalizing ω
  · simp
  · induction' ω with k ω _
    · simp
    · rw [drop_succ_cons, ih₁ ω, rightInvSeq, drop_succ_cons]

theorem leftInvSeq_take (ω : List B) (j : ℕ) :
    lis (ω.take j) = (lis ω).take j := by
  rcases em (j ≤ ω.length) with le | gt
  · simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse]
    rw [List.reverse_take j (by simpa)]
    nth_rw 1 [← List.reverse_reverse ω]
    rw [List.reverse_take j (by simpa)]
    simp [rightInvSeq_drop]
  · have : ω.length ≤ j := by linarith
    rw [take_length_le this, take_length_le (by simpa)]

theorem isReflection_of_mem_rightInvSeq (ω : List B) {t : W} (ht : t ∈ ris ω) :
    cs.IsReflection t := by
  induction' ω with i ω ih
  · simp at ht
  · dsimp [rightInvSeq] at ht
    rcases ht with _ | ⟨_, mem⟩
    · use (π ω)⁻¹, i
      group
    · exact ih mem

theorem isReflection_of_mem_leftInvSeq (ω : List B) {t : W} (ht : t ∈ lis ω) :
    cs.IsReflection t := by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse, mem_reverse] at ht
  exact cs.isReflection_of_mem_rightInvSeq ω.reverse ht

theorem wordProd_mul_getD_rightInvSeq (ω : List B) (j : ℕ) :
    π ω * ((ris ω).getD j 1) = π (ω.eraseIdx j) := by
  rw [getD_rightInvSeq, eraseIdx_eq_take_drop_succ]
  nth_rw 1 [← take_append_drop (j + 1) ω]
  rw [take_succ]
  rcases em (j < ω.length) with hj | nhj
  · rw [get?_eq_get hj]
    simp only [wordProd_append, wordProd_cons, mul_assoc]
    simp
  · rw [get?_eq_none.mpr (by linarith)]
    simp

theorem getD_leftInvSeq_mul_wordProd (ω : List B) (j : ℕ) :
    ((lis ω).getD j 1) * π ω = π (ω.eraseIdx j) := by
  rw [getD_leftInvSeq, eraseIdx_eq_take_drop_succ]
  nth_rw 4 [← take_append_drop (j + 1) ω]
  rw [take_succ]
  rcases em (j < ω.length) with hj | nhj
  · rw [get?_eq_get hj]
    simp only [wordProd_append, wordProd_cons, mul_assoc]
    simp
  · rw [get?_eq_none.mpr (by linarith)]
    simp

theorem isRightInversion_of_mem_rightInvSeq {ω : List B} (hω : cs.IsReduced ω) {t : W}
    (ht : t ∈ ris ω) : cs.IsRightInversion (π ω) t := by
  constructor
  · exact cs.isReflection_of_mem_rightInvSeq ω ht
  · obtain ⟨⟨j, hj⟩, rfl⟩ := List.mem_iff_get.mp ht
    rw [← List.getD_eq_get _ 1 hj, wordProd_mul_getD_rightInvSeq]
    rw [cs.length_rightInvSeq] at hj
    calc
      ℓ (π (ω.eraseIdx j))
      _ ≤ (ω.eraseIdx j).length   := cs.length_wordProd_le _
      _ < ω.length                := by rw [← List.length_eraseIdx_add_one hj]; exact lt_add_one _
      _ = ℓ (π ω)                 := hω.symm

theorem isLeftInversion_of_mem_leftInvSeq {ω : List B} (hω : cs.IsReduced ω) {t : W}
    (ht : t ∈ lis ω) : cs.IsLeftInversion (π ω) t := by
  constructor
  · exact cs.isReflection_of_mem_leftInvSeq ω ht
  · obtain ⟨⟨j, hj⟩, rfl⟩ := List.mem_iff_get.mp ht
    rw [← List.getD_eq_get _ 1 hj, getD_leftInvSeq_mul_wordProd]
    rw [cs.length_leftInvSeq] at hj
    calc
      ℓ (π (ω.eraseIdx j))
      _ ≤ (ω.eraseIdx j).length   := cs.length_wordProd_le _
      _ < ω.length                := by rw [← List.length_eraseIdx_add_one hj]; exact lt_add_one _
      _ = ℓ (π ω)                 := hω.symm

theorem prod_rightInvSeq (ω : List B) : prod (ris ω) = (π ω)⁻¹ := by
  induction' ω with i ω ih
  · simp
  · simp [rightInvSeq, ih, wordProd_cons]

theorem prod_leftInvSeq (ω : List B) : prod (lis ω) = (π ω)⁻¹ := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse, prod_reverse_noncomm]
  have : List.map (fun x ↦ x⁻¹) (ris ω.reverse) = ris ω.reverse := calc
    List.map (fun x ↦ x⁻¹) (ris ω.reverse)
    _ = List.map id (ris ω.reverse)             := by
        apply List.map_congr
        intro t ht
        exact cs.inv_eq_self_of_isReflection (cs.isReflection_of_mem_rightInvSeq _ ht)
    _ = ris ω.reverse                           := map_id _
  rw [this]
  nth_rw 2 [← reverse_reverse ω]
  rw [wordProd_reverse]
  exact cs.prod_rightInvSeq _

theorem nodup_rightInvSeq_of_reduced {ω : List B} (rω : cs.IsReduced ω) : List.Nodup (ris ω) := by
  apply List.nodup_iff_get?_ne_get?.mpr
  intro j j' j_lt_j' j'_lt_length dup
  -- dup : get? (rightInvSeq cs ω) j = get? (rightInvSeq cs ω) j'
  -- ⊢ False
  simp at j'_lt_length
  -- j'_lt_length: j' < List.length ω
  rw [get?_eq_get (by simp; linarith), get?_eq_get (by simp; linarith)] at dup
  apply Option.some_injective at dup
  rw [← getD_eq_get _ 1, ← getD_eq_get _ 1] at dup
  set! t := (ris ω).getD j 1 with h₁
  set! t' := (ris (ω.eraseIdx j)).getD (j' - 1) 1 with h₂
  have h₃ : t' = (ris ω).getD j' 1                    := by
    rw [h₂]
    rw [cs.getD_rightInvSeq, cs.getD_rightInvSeq]
    rw [(Nat.sub_add_cancel (by linarith) : j' - 1 + 1 = j')]
    rw [eraseIdx_eq_take_drop_succ]
    rw [drop_append_eq_append_drop]
    rw [drop_length_le (by simp; left; linarith)]
    rw [length_take, drop_drop, nil_append]
    rw [min_eq_left_of_lt (j_lt_j'.trans j'_lt_length)]
    rw [Nat.succ_eq_add_one, ← add_assoc, Nat.sub_add_cancel (by linarith)]
    rw [mul_left_inj, mul_right_inj]
    congr 2
    -- ⊢ get? (take j ω ++ drop (j + 1) ω) (j' - 1) = get? ω j'
    rw [get?_append_right (by simp; left; exact Nat.le_sub_one_of_lt j_lt_j')]
    rw [get?_drop]
    congr
    -- ⊢ j + 1 + (j' - 1 - List.length (take j ω)) = j'
    rw [length_take]
    rw [min_eq_left_of_lt (j_lt_j'.trans j'_lt_length)]
    rw [Nat.sub_sub, add_comm 1, Nat.add_sub_cancel' (by linarith)]
  have h₄ : t * t' = 1                                := by
    rw [h₁, h₃, dup]
    exact cs.getD_rightInvSeq_mul_self _ _
  have h₅ := calc
    π ω   = π ω * t * t'                              := by rw [mul_assoc, h₄]; group
    _     = (π (ω.eraseIdx j)) * t'                   :=
        congrArg (· * t') (cs.wordProd_mul_getD_rightInvSeq _ _)
    _     = π ((ω.eraseIdx j).eraseIdx (j' - 1))      :=
        cs.wordProd_mul_getD_rightInvSeq _ _
  have h₆ := calc
    ω.length = ℓ (π ω)                                    := rω.symm
    _        = ℓ (π ((ω.eraseIdx j).eraseIdx (j' - 1)))   := congrArg cs.length h₅
    _        ≤ ((ω.eraseIdx j).eraseIdx (j' - 1)).length  := cs.length_wordProd_le _
  have h₇ := add_le_add_right (add_le_add_right h₆ 1) 1
  have h₈ : j' - 1 < List.length (eraseIdx ω j)           := by
    apply (@Nat.add_lt_add_iff_right 1).mp
    rw [Nat.sub_add_cancel (by linarith)]
    rw [length_eraseIdx_add_one (by linarith)]
    linarith
  rw [length_eraseIdx_add_one h₈] at h₇
  rw [length_eraseIdx_add_one (by linarith)] at h₇
  linarith

theorem nodup_leftInvSeq_of_reduced {ω : List B} (rω : cs.IsReduced ω) : List.Nodup (lis ω) := by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse, nodup_reverse]
  apply nodup_rightInvSeq_of_reduced
  rwa [isReduced_reverse]

end CoxeterSystem
