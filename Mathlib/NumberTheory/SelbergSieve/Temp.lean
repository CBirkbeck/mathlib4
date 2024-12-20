/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module aux_results
-/
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.Harmonic.Bounds

noncomputable section

open scoped BigOperators

open Nat ArithmeticFunction Finset

namespace ArithmeticFunction.IsMultiplicative

variable {R : Type*}

theorem map_lcm [CommGroupWithZero R] {f : ArithmeticFunction R}
    (h_mult : f.IsMultiplicative) {x y : ℕ} (hf : f (x.gcd y) ≠ 0) :
    f (x.lcm y) = f x * f y / f (x.gcd y) := by
  rw [←h_mult.lcm_apply_mul_gcd_apply]
  field_simp

theorem map_div_of_coprime [CommGroupWithZero R] {f : ArithmeticFunction R}
    (hf : IsMultiplicative f) {l d : ℕ} (hdl : d ∣ l) (hl : (l/d).Coprime d) (hd : f d ≠ 0) :
    f (l / d) = f l / f d := by
  apply (div_eq_of_eq_mul hd ..).symm
  rw [← hf.right, Nat.div_mul_cancel hdl]
  exact hl

theorem eq_zero_of_squarefree_of_dvd_eq_zero {f : ArithmeticFunction ℝ}
    (h_mult : IsMultiplicative f)
    {m n : ℕ}
    (h_sq : Squarefree n) (hmn : m ∣ n) (h_zero : f m = 0) : f n = 0 := by
  rcases hmn with ⟨k, rfl⟩
  simp only [MulZeroClass.zero_mul, eq_self_iff_true, h_mult.map_mul_of_coprime
    (coprime_of_squarefree_mul h_sq), h_zero]

end ArithmeticFunction.IsMultiplicative

--basic
theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d in n.divisors, f d = ∑ d in P.divisors, if d ∣ n then f d else 0 := by
  rw [←Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]

--temp
@[to_additive]
theorem ite_prod_one {R ι : Type*} [CommMonoid R] {p : Prop} [Decidable p] (s : Finset ι)
    (f : ι → R) :
    (if p then (∏ x in s, f x) else 1) = ∏ x in s, if p then f x else 1 := by
  split_ifs <;> simp

@[to_additive]
theorem prod_filter_prod {R ι ι' : Type*} [CommMonoid R] {p : ι → Prop}
    [DecidablePred p] (s : Finset ι) (t : ι → Finset ι')
    (f : ι → ι' → R) :
    ∏ x ∈ s with p x, ∏ y ∈ t x, f x y = ∏ x ∈ s, ∏ y ∈ t x with p x, f x y := by
  simp_rw [prod_filter, ite_prod_one]

@[to_additive]
theorem prod_filter_prod_filter {R ι ι' : Type*} [CommMonoid R] {p : ι → Prop} {q : ι → ι' → Prop}
    [DecidablePred p] [∀ i, DecidablePred (q i)] (s : Finset ι) (t : ι → Finset ι')
    (f : ι → ι' → R) :
    ∏ x ∈ s with p x, ∏ y ∈ t x with q x y, f x y = ∏ x ∈ s, ∏ y ∈ t x with q x y ∧ p x, f x y := by
  simp_rw [prod_filter_prod, Finset.filter_filter]

@[to_additive]
theorem prod_comm_filter {R ι ι' : Type*} [CommMonoid R] {p : ι → ι' → Prop}
    [∀ i, DecidablePred (p i)] (s : Finset ι) (t : Finset ι')
    (f : ι → ι' → R) :
    ∏ x ∈ s, ∏ y ∈ t with p x y, f x y = ∏ y ∈ t, ∏ x ∈ s with p x y, f x y := by
  simp_rw [prod_filter]
  rw [prod_comm]

--basic
theorem conv_lambda_sq_larger_sum (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors,
        ∑ d1 ∈ d.divisors,
          ∑ d2 ∈ d.divisors with d = Nat.lcm d1 d2, f d1 d2 d) =
      ∑ d ∈ n.divisors,
        ∑ d1 ∈ n.divisors,
          ∑ d2 ∈ n.divisors with d = Nat.lcm d1 d2, f d1 d2 d := by
  apply sum_congr rfl; intro d hd
  rw [mem_divisors] at hd
  simp_rw [←Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, Finset.filter_filter,
    sum_filter_sum_filter]
  congr with d1
  congr with d2
  refine ⟨fun ⟨⟨_, h⟩, _, _⟩ ↦ h, ?_⟩
  rintro rfl
  exact ⟨⟨Nat.dvd_lcm_right d1 d2, rfl⟩, Nat.dvd_lcm_left d1 d2⟩

--selberg
theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d in m.divisors, if l ∣ d then (μ d:ℤ) else 0) = if l = m then (μ l:ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero <| Squarefree.ne_zero hm
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on {n | Squarefree n}
    (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]--
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ←isMultiplicative_moebius.map_mul_of_coprime,
        hmul]

      apply coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw[if_neg hdl.symm, smul_zero]
    · intro h; rw[mem_divisors] at h; exfalso; exact h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩
  · rw [if_neg hl, sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]
    by_contra h; rw [←h] at hd; exact hl (dvd_of_mem_divisors hd)

/-- Same as `moebius_inv_dvd_lower_bound` except we're summing over divisors of some
`P` divisible by `m` -/
theorem moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d in P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) = if l = m then μ l else 0 := by
  rw [←moebius_inv_dvd_lower_bound _ _ (Squarefree.squarefree_of_dvd hm hP),
    sum_over_dvd_ite hP.ne_zero hm]
  simp_rw[ite_and, ←sum_filter, filter_comm]

theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d in P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) = if l = m then (μ l : ℝ) else 0
    := by
  norm_cast
  apply moebius_inv_dvd_lower_bound' hP l m hm

--basic
