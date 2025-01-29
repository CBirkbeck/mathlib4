/-
Copyright (c) 2025 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Hill, Julian Berman, Austin Letson, Matej Penciak
-/
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.LinearAlgebra.Basis.Basic

/-!

# Polynomial sequences

We define polynomial sequences – sequences of polynomials `a₀, a₁, ...` such that the polynomial
`aᵢ` has degree `i`.

## Main definitions

* `Polynomial.Sequence R`: the type of polynomial sequences with coefficients in `R`

## Main statements

* `Polynomial.Sequence.basis`: a sequence is a basis for `R[X]`

## TODO

Generalize linear independence to:
  * just require coefficients are regular
  * arbitrary sets of polynomials which are pairwise different degree.
-/

open Submodule
open scoped Function

universe u

theorem IsSMulRegular.of_ne_zero {R M : Type u} [Ring R] [Zero M] [SMulWithZero R M]
  [NoZeroDivisors R]
  {a : R} {b : M} (hx : a • b ≠ 0) : IsSMulRegular R a := by
  intro w v hwv
  have hgwv : a • (w - v) = 0 := by rw [smul_sub, sub_eq_zero.mpr hwv]
  cases' smul_eq_zero.mp hgwv with ha hsub
  · exact hx (smul_eq_zero_of_left ha _) |>.elim
  · exact sub_eq_zero.mp hsub

open Polynomial in
theorem degree_smul_of_ne_zero
    {R : Type*} [Semiring R] {k : R} [NoZeroDivisors R] {p : R[X]} (hkp : k • p ≠ 0) :
    (k • p).degree = p.degree := by
  refine le_antisymm (degree_smul_le k p) ?_
  by_cases nezero : p = 0
  · simp [nezero]
  · by_contra! hdeg
    suffices hk : k = 0 by simp_all
    have h := coeff_eq_zero_of_natDegree_lt <| natDegree_lt_natDegree hkp hdeg
    simp only [coeff_smul, coeff_natDegree, smul_eq_mul, mul_eq_zero, leadingCoeff_eq_zero] at h
    exact h.resolve_right <| right_ne_zero_of_smul hkp

variable (R : Type u)

namespace Polynomial

/-- A sequence of polynomials such that the polynomial at index `i` has degree `i`. -/
structure Sequence [Semiring R] where
  /-- The `i`'th element in the sequence. Use `S i` instead, defined via `CoeFun`. -/
  protected elems' : ℕ → R[X]
  /-- The `i`'th element in the sequence has degree `i`. Use `S.degree_eq` instead, -/
  protected degree_eq' (i : ℕ) : (elems' i).degree = i

attribute [coe] Sequence.elems'

namespace Sequence

variable {R}

/-- Make `S i` mean `S.elems' i`. -/
instance coeFun [Semiring R] : CoeFun (Sequence R) (fun _ ↦  ℕ → R[X]) := ⟨Sequence.elems'⟩

section Semiring

variable [Semiring R] (S : Sequence R)

/-- `S i` has degree `i`. -/
@[simp]
lemma degree_eq (i : ℕ) : (S i).degree = i := S.degree_eq' i

/-- `S i` has `natDegree` `i`. -/
@[simp]
lemma natDegree_eq (i : ℕ) : (S i).natDegree = i := natDegree_eq_of_degree_eq_some <| S.degree_eq i

/-- No polynomial in the sequence is zero. -/
@[simp]
lemma ne_zero (i : ℕ) : S i ≠ 0 := degree_ne_bot.mp <| by simp [S.degree_eq i]

/-- No two elements in the sequence have the same degree. -/
lemma degree_ne {i j : ℕ} (h : i ≠ j) : (S i).degree ≠ (S j).degree := by
  simp [S.degree_eq i, S.degree_eq j, h]

/-- No two elements in the sequence have the same natural degree. -/
lemma natDegree_ne {i j : ℕ} (h : i ≠ j) : (S i).natDegree ≠ (S j).natDegree := by
  simp [S.natDegree_eq i, S.natDegree_eq j, h]

/-- No two elements in the sequence have the same degree. -/
lemma degree_inj : Function.Injective <| degree ∘ S := fun _ _  ↦ by simp

end Semiring

section Ring

variable [Ring R] (S : Sequence R)

/-- Polynomials in a polynomial sequence are linearly independent. -/
lemma linearIndependent [NoZeroDivisors R] :
    LinearIndependent R S := linearIndependent_iff'.mpr <| fun s g eqzero i hi ↦ by
  by_cases hsupzero : s.sup (fun i ↦ (g i • S i).degree) = ⊥
  · have le_sup := Finset.le_sup hi (f := fun i ↦ (g i • S i).degree)
    exact (smul_eq_zero_iff_left (S.ne_zero i)).mp <| degree_eq_bot.mp (eq_bot_mono le_sup hsupzero)
  · have hpairwise : {i | i ∈ s ∧ g i • S i ≠ 0}.Pairwise (Ne on fun i ↦ (g i • S i).degree) := by
      intro _ ⟨_, hx⟩ _ ⟨_, hy⟩ xney
      simpa [degree_smul_of_ne_zero hx, degree_smul_of_ne_zero hy] using S.degree_ne xney
    obtain ⟨n, hn⟩ : ∃ n, (s.sup fun i ↦ (g i • S i).degree) = n := exists_eq'
    refine degree_ne_bot.mp ?_ eqzero |>.elim
    have hsum := degree_sum_eq_of_disjoint _ s hpairwise |>.trans hn
    exact hsum.trans_ne <| (ne_of_ne_of_eq (hsupzero ·.symm) hn).symm

section Nontrivial

variable [Nontrivial R]

/-- A polynomial sequence spans `R[X]` if all of its elements' leading coefficients are units. -/
protected lemma span (hCoeff : ∀ i, IsUnit (S i).leadingCoeff) : span R (Set.range S) = ⊤ :=
  eq_top_iff'.mpr fun P ↦ by
  induction' hp : P.natDegree using Nat.strong_induction_on with n ih generalizing P
  by_cases p_ne_zero : P = 0
  · simp [p_ne_zero]

  obtain ⟨u, leftinv, rightinv⟩ := isUnit_iff_exists.mp <| hCoeff n

  let head := P.leadingCoeff • u • S n
  let tail := P - head

  have head_mem_span : head ∈ span R (Set.range S) := by
    have in_span : S n ∈ span R (Set.range S) := subset_span (by simp)
    have smul_span := smul_mem (span R (Set.range S)) (P.leadingCoeff • u) in_span
    rwa [smul_assoc] at smul_span

  by_cases tail_eq_zero : tail = 0
  · simp [head_mem_span, sub_eq_iff_eq_add.mp tail_eq_zero]
  · refine sub_mem_iff_left _ head_mem_span |>.mp ?_
    simp only [mem_top, forall_const] at ih
    refine ih tail.natDegree ?_ _ rfl

    have isRightRegular_smul_leadingCoeff : IsRightRegular (u • S n).leadingCoeff := by
      simp [leadingCoeff_smul_of_smul_regular _ <| IsSMulRegular.of_mul_eq_one leftinv, rightinv]
      exact isRegular_one.right

    have head_degree_eq := degree_smul_of_isRightRegular_leadingCoeff
      (leadingCoeff_ne_zero.mpr p_ne_zero) isRightRegular_smul_leadingCoeff

    have u_degree_same := degree_smul_of_isRightRegular_leadingCoeff
      (left_ne_zero_of_mul_eq_one rightinv) (hCoeff n).isRegular.right
    rw [u_degree_same, S.degree_eq n, ← hp, eq_comm,
        ← degree_eq_natDegree p_ne_zero, hp] at head_degree_eq

    have head_nonzero : head ≠ 0 := by
      by_cases n_eq_zero : n = 0
      · rw [n_eq_zero, ← coeff_natDegree, natDegree_eq] at rightinv
        dsimp [head]
        rwa [n_eq_zero, eq_C_of_natDegree_eq_zero <| S.natDegree_eq 0,
              smul_C, smul_eq_mul, map_mul, ← C_mul, rightinv, smul_C, smul_eq_mul,
              mul_one, C_eq_zero, leadingCoeff_eq_zero]
      · apply head.ne_zero_of_degree_gt
        rw [← head_degree_eq]
        exact natDegree_pos_iff_degree_pos.mp (by omega)

    have hPhead : P.leadingCoeff = head.leadingCoeff := by
      rw [degree_eq_natDegree, degree_eq_natDegree head_nonzero] at head_degree_eq
      nth_rw 2 [← coeff_natDegree]
      rw_mod_cast [← head_degree_eq, hp]
      dsimp [head]
      nth_rw 2 [← S.natDegree_eq n]
      rwa [coeff_smul, coeff_smul, coeff_natDegree, smul_eq_mul, smul_eq_mul, rightinv, mul_one]

    refine natDegree_lt_iff_degree_lt tail_eq_zero |>.mpr ?_
    have tail_degree_lt := P.degree_sub_lt head_degree_eq p_ne_zero hPhead
    rwa [degree_eq_natDegree p_ne_zero, hp] at tail_degree_lt

section NoZeroDivisors

variable [NoZeroDivisors R] (hCoeff : ∀ i, IsUnit (S i).leadingCoeff)

/-- Every polynomial sequence is a basis of `R[X]`. -/
noncomputable def basis : Basis ℕ R R[X] :=
  Basis.mk S.linearIndependent <| eq_top_iff.mp <| S.span hCoeff

/-- The `i`'th basis vector is the `i`'th polynomial in the sequence. -/
lemma basis_eq_self  (i : ℕ) : S.basis hCoeff i = S i := Basis.mk_apply _ _ _

/-- The `i`'th basis vector has degree `i`. -/
lemma basis_degree_eq (i : ℕ) : (S.basis hCoeff i).degree = i := by simp [basis_eq_self]

/-- The `i`'th basis vector has natural degree `i`. -/
lemma basis_natDegree_eq (i : ℕ) : (S.basis hCoeff i).natDegree = i := by simp [basis_eq_self]

end NoZeroDivisors

end Nontrivial

end Ring

end Sequence

end Polynomial
