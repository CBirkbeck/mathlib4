/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Polynomial.Smeval

/-!
# Binomial rings

In this file we introduce the binomial property as a Prop-valued mixin, and define the `multichoose`
and `choose` functions generalizing binomial coefficients.

According to our main reference [elliott2006binomial] (which lists many equivalent conditions), a
binomial ring is a torsion-free commutative ring `R` such that for any `x ∈ R` and any `k ∈ ℕ`, the
product `x(x-1)⋯(x-k+1)` is divisible by `k!`.  The torsion-free condition lets us divide by `k!`
unambiguously, so we get uniquely defined binomial coefficients.

The defining condition doesn't require commutativity or associativity, and we get a theory with
essentially the same power by replacing subtraction with addition.  Thus, we consider any
non-associative semiring `R` with notion of natural nunber exponents, in which multiplication by
factorials is injective, and demand that the evaluation of the ascending Pochhammer polynomial
`X(X+1)⋯(X+(k-1))` at any element is divisible by `k!`.  The quotient is called `multichoose r k`,
following the convention given for natural numbers.

## References

* [J. Elliott, *Binomial rings, integer-valued polynomials, and λ-rings*][elliott2006binomial]

## To Do

Replace Nat.multichoose with Ring.multichoose (or Nat.choose with adjusted parameters)

* Data.List.Sym done
* Data.Sym.Card done


-/

section Multichoose

open Function

/-- A mixin for multi-binomial coefficients. -/
class IsBinomialRing (R : Type*) [NonAssocSemiring R] [Pow R ℕ] where
  /-- Scalar multiplication by positive integers is injective. -/
nsmul_right_injective (n : ℕ) (h : n ≠ 0) : Injective (n • · : R → R)
  /-- A multichoose function, giving the quotient of Pochhammer by factorial -/
  multichoose : R → ℕ → R
  /-- The `n`th ascending Pochhammer polynomial evaluated at any element is divisible by `n!`. -/
  factorial_smul_multichoose : ∀ (r : R) (n : ℕ),
    n.factorial • multichoose r n = Polynomial.smeval r (ascPochhammer ℕ n)

namespace Ring

open Polynomial

theorem nsmul_right_injective (R : Type*) [NonAssocSemiring R] [Pow R ℕ] [IsBinomialRing R] (n : ℕ)
    (h : n ≠ 0) : Injective (n • · : R → R) := IsBinomialRing.nsmul_right_injective n h

variable {R : Type*} [NonAssocSemiring R] [Pow R ℕ] [IsBinomialRing R]

/-- This is a generalization of the combinatorial multichoose function, given by choosing with
replacement. -/
def multichoose (r : R) (n : ℕ) : R :=
  IsBinomialRing.multichoose r n

theorem factorial_smul_multichoose_eq_ascPochhammer (r : R) (n : ℕ) :
    n.factorial • multichoose r n = smeval r (ascPochhammer ℕ n) :=
  IsBinomialRing.factorial_smul_multichoose r n

theorem multichoose_zero_right' (r : R) : multichoose r 0 = r ^ 0 := by
  refine nsmul_right_injective R (Nat.factorial 0) (Nat.factorial_ne_zero 0) ?_
  simp only
  rw [factorial_smul_multichoose_eq_ascPochhammer, ascPochhammer_zero, smeval_one, Nat.factorial]

@[simp]
theorem multichoose_zero_right [NatPowAssoc R]
    (r : R) : multichoose r 0 = 1 := by
  rw [multichoose_zero_right', npow_zero]

@[simp]
theorem multichoose_zero_succ [NatPowAssoc R]
    (k : ℕ) : multichoose (0 : R) (k + 1) = 0 := by
  refine nsmul_right_injective R (Nat.factorial (k + 1)) (Nat.factorial_ne_zero (k + 1)) ?_
  simp only
  rw [factorial_smul_multichoose_eq_ascPochhammer, smul_zero, ascPochhammer_succ_left, smeval_X_mul,
    zero_mul]

theorem ascPochhammer_succ_succ [NatPowAssoc R] (r : R) (k : ℕ) :
    smeval (r + 1) (ascPochhammer ℕ (k + 1)) = Nat.factorial (k + 1) • multichoose (r + 1) k +
    smeval r (ascPochhammer ℕ (k + 1)) := by
  nth_rw 1 [ascPochhammer_succ_right, ascPochhammer_succ_left, mul_comm (ascPochhammer ℕ k)]
  simp only [smeval_mul, smeval_comp ℕ r, smeval_add, smeval_X]
  rw [Nat.factorial, mul_smul, factorial_smul_multichoose_eq_ascPochhammer]
  simp only [smeval_one, npow_one, npow_zero, one_smul]
  rw [← C_eq_nat_cast, smeval_C, npow_zero, add_assoc, add_mul, add_comm 1, @nsmul_one, add_mul]
  rw [← @nsmul_eq_mul, @add_rotate', @succ_nsmul', add_assoc]
  simp_all only [Nat.cast_id, nsmul_eq_mul, one_mul]

theorem multichoose_succ_succ [NatPowAssoc R] (r : R) (k : ℕ) :
    multichoose (r + 1) (k + 1) = multichoose r (k + 1) + multichoose (r + 1) k := by
  refine nsmul_right_injective R (Nat.factorial (k + 1)) (Nat.factorial_ne_zero (k + 1)) ?_
  simp only [factorial_smul_multichoose_eq_ascPochhammer, smul_add]
  rw [add_comm (smeval r (ascPochhammer ℕ (k+1)))]
  exact @ascPochhammer_succ_succ R _ _ _ _ r k

@[simp]
theorem multichoose_one [NatPowAssoc R] (k : ℕ) : multichoose (1 : R) k = 1 := by
  induction k with
  | zero => exact multichoose_zero_right 1
  | succ n ih =>
    rw [show (1 : R) = 0 + 1 by exact (@zero_add R _ 1).symm, multichoose_succ_succ,
      multichoose_zero_succ, zero_add, zero_add, ih]

@[simp]
theorem multichoose_two [NatPowAssoc R] (k : ℕ) : multichoose (2 : R) k = k + 1 := by
  induction k with
  | zero =>
    rw [multichoose_zero_right, Nat.cast_zero, zero_add]
  | succ n ih =>
    rw [one_add_one_eq_two.symm, multichoose_succ_succ, multichoose_one, one_add_one_eq_two, ih,
      Nat.cast_succ, add_comm]

@[simp]
theorem multichoose_one_right' (r : R) : multichoose r 1 = r ^ 1 := by
  refine nsmul_right_injective R (Nat.factorial 1) (Nat.factorial_ne_zero 1) ?_
  simp only
  rw [factorial_smul_multichoose_eq_ascPochhammer, ascPochhammer_one, smeval_X, Nat.factorial_one,
    one_smul]

theorem multichoose_one_right [NatPowAssoc R] (r : R) : multichoose r 1 = r := by
  rw[multichoose_one_right', npow_one]

end Ring

end Multichoose

section Nat_Int

namespace Ring

open Polynomial

instance naturals_binomial : IsBinomialRing ℕ := by
  refine IsBinomialRing.mk ?nsmul_right_injective ?multichoose ?factorial_mul_multichoose
  intro n npos r s h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero npos) h
  use fun n k => Nat.choose (n + k - 1) k
  intro n k
  rw [smul_eq_mul, ← Nat.descFactorial_eq_factorial_mul_choose,
    smeval_eq_eval (ascPochhammer ℕ k) n, ascPochhammer_nat_eq_descFactorial]

theorem multichoose_eq (n k : ℕ) : multichoose n k = (n + k - 1).choose k := rfl

theorem ascPochhammer_smeval_eq_eval {R : Type*} [Semiring R] (r : R) (k : ℕ) :
    smeval r (ascPochhammer ℕ k) = Polynomial.eval r (ascPochhammer R k) := by
  induction k with
  | zero =>
    rw [ascPochhammer_zero, ascPochhammer_zero, eval_one, smeval_one, nsmul_eq_mul, npow_zero,
      mul_one, Nat.cast_one]
  | succ n ih =>
    rw [ascPochhammer_succ_right, ascPochhammer_succ_right, smeval_mul ℕ r, ih,
      mul_add (ascPochhammer R n), smeval_add, smeval_X r, pow_one, ← C_eq_nat_cast, smeval_C,
      pow_zero, nsmul_one, Nat.cast_id, eval_add, eval_mul_X, ← Nat.cast_comm, eval_nat_cast_mul,
      mul_add, Nat.cast_comm]

instance integers_binomial_ring : IsBinomialRing ℤ := by
  refine IsBinomialRing.mk ?_ ?_ ?_
  intro n hn r s hmul
  exact nat_mul_inj' hmul hn
  intro r k
  cases r with
  | ofNat n =>
    use ((Nat.choose (n + k - 1) k):ℤ)
  | negSucc n =>
    use (-1)^k * Nat.choose n.succ k
  intro r k
  cases r with
  | ofNat n =>
    simp only [nsmul_eq_mul, Int.ofNat_eq_coe, Int.ofNat_mul_out]
    rw [← Nat.descFactorial_eq_factorial_mul_choose, @smeval_at_nat_cast,
      smeval_eq_eval (ascPochhammer ℕ k) n, ascPochhammer_nat_eq_descFactorial]
  | negSucc n =>
    rw [nsmul_eq_mul, mul_comm, mul_assoc, ← Nat.cast_mul, mul_comm _ (k.factorial),
      ← Nat.descFactorial_eq_factorial_mul_choose, ← descPochhammer_int_eq_descFactorial,
      ascPochhammer_smeval_eq_eval, ← Int.neg_ofNat_succ, ascPochhammer_eval_neg_eq_descPochhammer]

end Ring

end Nat_Int

section choose

namespace Ring

open Polynomial

variable {R : Type*}

variable [NonAssocRing R] [Pow R ℕ] [IsBinomialRing R]

theorem ascPochhammer_smeval_neg : ∀(n : ℕ),
    smeval (-n : ℤ) (ascPochhammer ℕ n) = (-1)^n * n.factorial
  | 0 => by
    rw [Nat.cast_zero, neg_zero, ascPochhammer_zero, Nat.factorial_zero, smeval_one, pow_zero,
      one_smul, pow_zero, Nat.cast_one, one_mul]
  | n + 1 => by
    rw [ascPochhammer_succ_left, smeval_X_mul, smeval_comp, smeval_add, smeval_X, smeval_one,
      pow_zero, pow_one, one_smul, Nat.cast_add, Nat.cast_one, neg_add_rev, neg_add_cancel_comm,
      ascPochhammer_smeval_neg n, ← mul_assoc, mul_comm _ ((-1) ^ n),
      show (-1 + -↑n = (-1 : ℤ) * (n + 1)) by linarith, ← mul_assoc, pow_add, pow_one,
      Nat.factorial, Nat.cast_mul, ← mul_assoc, Nat.cast_succ]

theorem ascPochhammer_succ_smeval_neg (n : ℕ) :
    smeval (-n : ℤ) (ascPochhammer ℕ (n + 1)) = 0 := by
  rw [ascPochhammer_succ_right, smeval_mul, smeval_add, smeval_X, ← C_eq_nat_cast, smeval_C,
    pow_zero, pow_one, Nat.cast_id, nsmul_eq_mul, mul_one, add_left_neg, mul_zero]

theorem ascPochhammer_smeval_neg_add (n : ℕ) : ∀(k : ℕ),
    smeval (-n : ℤ) (ascPochhammer ℕ (n + k + 1)) = 0
  | 0 => by
    rw [add_zero, ascPochhammer_succ_smeval_neg]
  | k + 1 => by
    rw [ascPochhammer_succ_right, smeval_mul, ← add_assoc, ascPochhammer_smeval_neg_add n k,
      zero_mul]

theorem ascPochhammer_smeval_neg_lt (n k : ℕ) (h : n < k) :
    smeval (-n : ℤ) (ascPochhammer ℕ k) = 0 := by
  have hk : k = n + (k - n - 1) + 1 := by
    rw [add_rotate, Nat.sub_sub, Nat.add_right_comm, Nat.add_assoc, Nat.sub_add_cancel h]
  rw [hk, ascPochhammer_smeval_neg_add]

theorem ascPochhammer_smeval_nat_cast [NatPowAssoc R] (n k : ℕ) :
    smeval (n : R) (ascPochhammer ℕ k) = smeval n (ascPochhammer ℕ k) := by
  rw [smeval_at_nat_cast (ascPochhammer ℕ k) n]

theorem multichoose_neg (n : ℕ) : multichoose (-n : ℤ) n = (-1)^n := by
    refine @nsmul_right_injective ℤ _ _ _ (Nat.factorial n) (Nat.factorial_ne_zero n)
      (multichoose (-n : ℤ) n) ((-1)^n) ?_
    simp only
    rw [factorial_smul_multichoose_eq_ascPochhammer, ascPochhammer_smeval_neg, nsmul_eq_mul,
      Nat.cast_comm]

theorem multichoose_succ_neg (n : ℕ) : multichoose (-n : ℤ) (n + 1) = 0 := by
  refine @nsmul_right_injective ℤ _ _ _ (Nat.factorial (n + 1)) (Nat.factorial_ne_zero (n + 1))
    (multichoose (-n : ℤ) (n + 1)) 0 ?_
  simp only
  rw [factorial_smul_multichoose_eq_ascPochhammer, ascPochhammer_succ_smeval_neg, smul_zero]

theorem multichoose_neg_add (n k : ℕ) : multichoose (-n : ℤ) (n + k + 1) = 0 := by
  refine nsmul_right_injective ℤ (Nat.factorial (n + k + 1)) (Nat.factorial_ne_zero (n + k + 1)) ?_
  simp only
  rw [factorial_smul_multichoose_eq_ascPochhammer, ascPochhammer_smeval_neg_add, smul_zero]

theorem multichoose_neg_lt (n k : ℕ) (h : n < k) : multichoose (-n : ℤ) k = 0 := by
  refine nsmul_right_injective ℤ (Nat.factorial k) (Nat.factorial_ne_zero k) ?_
  simp only
  rw [factorial_smul_multichoose_eq_ascPochhammer, ascPochhammer_smeval_neg_lt n k h, smul_zero]

theorem multichoose_succ_neg_cast [NatPowAssoc R] (n : ℕ) :
    multichoose (-n : R) (n + 1) = 0 := by
  refine nsmul_right_injective R (Nat.factorial (n + 1)) (Nat.factorial_ne_zero (n + 1)) ?_
  simp only
  rw [factorial_smul_multichoose_eq_ascPochhammer, smul_zero, smeval_at_neg_nat,
    ascPochhammer_succ_smeval_neg, Int.cast_zero]

theorem ascPochhammer_smeval_nat_int [NatPowAssoc R] (r : R) : ∀(n : ℕ),
    smeval r (ascPochhammer ℤ n) = smeval r (ascPochhammer ℕ n)
  | 0 => by
    simp only [ascPochhammer_zero, smeval_one]
  | n + 1 => by
    simp only [ascPochhammer_succ_right, smeval_mul]
    rw [ascPochhammer_smeval_nat_int r n]
    simp only [smeval_add, smeval_X, ← C_eq_nat_cast, smeval_C, coe_nat_zsmul, nsmul_eq_mul,
    Nat.cast_id]

/-- The binomial coefficient `choose r n` generalizes the natural number choose function,
  interpreted in terms of choosing without replacement. -/
noncomputable def choose {R: Type _} [NonAssocRing R] [Pow R ℕ] [IsBinomialRing R]
    (r : R) (n : ℕ): R :=
  multichoose (r-n+1) n

theorem descPochhammer_eq_factorial_smul_choose [NatPowAssoc R] (r : R) (n : ℕ) :
    smeval r (descPochhammer ℤ n) = n.factorial • choose r n := by
  unfold choose
  rw [factorial_smul_multichoose_eq_ascPochhammer, descPochhammer_eq_ascPochhammer, smeval_comp ℤ r,
    add_comm_sub, smeval_add, smeval_X, npow_one]
  have h : smeval r (1 - n : Polynomial ℤ) = 1 - n := by
    rw [← C_eq_nat_cast, ← C_1, ← C_sub, smeval_C]
    simp only [npow_zero, zsmul_eq_mul, Int.cast_sub, Int.cast_one, Int.cast_ofNat, zsmul_one]
  rw [h, ascPochhammer_smeval_nat_int, add_comm_sub]

theorem choose_zero_right' (r : R) : choose r 0 = (r + 1) ^ 0 := by
  unfold choose
  refine nsmul_right_injective R (Nat.factorial 0) (Nat.factorial_ne_zero 0) ?_
  simp only
  rw [factorial_smul_multichoose_eq_ascPochhammer, Nat.factorial_zero, ascPochhammer_zero,
    smeval_one, one_smul, one_smul, Nat.cast_zero, sub_zero]

theorem choose_zero_right [NatPowAssoc R] (r : R) : choose r 0 = 1 := by
  rw [choose_zero_right', npow_zero]

theorem choose_zero_succ (S : Type*) [NonAssocRing S] [Pow S ℕ] [NatPowAssoc S] [IsBinomialRing S]
    (n : ℕ) : choose (0 : S) (Nat.succ n) = 0 := by
  unfold choose
  rw [Nat.cast_succ, zero_sub, neg_add, neg_add_cancel_right, ← Nat.add_one,
    multichoose_succ_neg_cast]

theorem choose_zero_pos (S : Type*) [NonAssocRing S] [Pow S ℕ] [NatPowAssoc S] [IsBinomialRing S]
    (k : ℕ) (h_pos: 0 < k) : choose (0 : S) k = 0 := by
  rw [← Nat.succ_pred_eq_of_pos h_pos, choose_zero_succ]

theorem choose_zero_ite (S : Type*) [NonAssocRing S] [Pow S ℕ] [NatPowAssoc S] [IsBinomialRing S]
    (k : ℕ) : choose (0 : S) k = if k = 0 then 1 else 0 := by
  rw [eq_ite_iff]
  by_cases hk: k = 0
  constructor
  rw [hk, choose_zero_right, ← Prod.mk.inj_iff]
  right
  constructor
  exact hk
  rw [← @Nat.le_zero, Nat.not_le] at hk
  rw [choose_zero_pos S k hk]

theorem descPochhammer_succ_succ_smeval {S : Type*} [NonAssocRing S] [Pow S ℕ] [NatPowAssoc S]
    (r : S) (k : ℕ) : smeval (r + 1) (descPochhammer ℤ (Nat.succ k)) =
    (k + 1) • smeval r (descPochhammer ℤ k) + smeval r (descPochhammer ℤ (Nat.succ k)) := by
  nth_rw 1 [descPochhammer_succ_left]
  rw [descPochhammer_succ_right, mul_comm (descPochhammer ℤ k)]
  simp only [smeval_comp ℤ (r + 1), smeval_sub, smeval_add, smeval_mul, smeval_X, smeval_one,
    npow_one, npow_zero, one_smul, add_sub_cancel, sub_mul, add_mul, add_smul, one_mul]
  rw [← C_eq_nat_cast, smeval_C, npow_zero, add_comm (k • smeval r (descPochhammer ℤ k)) _,
    add_assoc, add_comm (k • smeval r (descPochhammer ℤ k)) _, ← add_assoc,  ← add_sub_assoc,
    nsmul_eq_mul, zsmul_one, Int.cast_ofNat, sub_add_cancel, add_comm]

theorem choose_succ_succ [NatPowAssoc R] (r:R) (k : ℕ) :
    choose (r+1) (Nat.succ k) = choose r k + choose r (Nat.succ k) := by
  refine nsmul_right_injective R (Nat.factorial (k + 1)) (Nat.factorial_ne_zero (k + 1)) ?_
  simp only [smul_add, ← descPochhammer_eq_factorial_smul_choose]
  rw [Nat.factorial_succ, mul_smul,
    ← descPochhammer_eq_factorial_smul_choose r, descPochhammer_succ_succ_smeval r k]

end Ring

end choose
