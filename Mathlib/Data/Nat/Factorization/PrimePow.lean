/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Factorization.Basic

#align_import data.nat.factorization.prime_pow from "leanprover-community/mathlib"@"6ca1a09bc9aa75824bf97388c9e3b441fc4ccf3f"

/-!
# Prime powers and factorizations

This file deals with factorizations of prime powers.
-/


variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

theorem IsPrimePow.minFac_pow_factorization_eq {n : ℕ} (hn : IsPrimePow n) :
    n.minFac ^ n.factorization n.minFac = n := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hn
  -- ⊢ Nat.minFac (p ^ k) ^ ↑(Nat.factorization (p ^ k)) (Nat.minFac (p ^ k)) = p ^ k
  rw [← Nat.prime_iff] at hp
  -- ⊢ Nat.minFac (p ^ k) ^ ↑(Nat.factorization (p ^ k)) (Nat.minFac (p ^ k)) = p ^ k
  rw [hp.pow_minFac hk.ne', hp.factorization_pow, Finsupp.single_eq_same]
  -- 🎉 no goals
#align is_prime_pow.min_fac_pow_factorization_eq IsPrimePow.minFac_pow_factorization_eq

theorem isPrimePow_of_minFac_pow_factorization_eq {n : ℕ}
    (h : n.minFac ^ n.factorization n.minFac = n) (hn : n ≠ 1) : IsPrimePow n := by
  rcases eq_or_ne n 0 with (rfl | hn')
  -- ⊢ IsPrimePow 0
  · simp_all
    -- 🎉 no goals
  refine' ⟨_, _, (Nat.minFac_prime hn).prime, _, h⟩
  -- ⊢ 0 < ↑(Nat.factorization n) (Nat.minFac n)
  rw [pos_iff_ne_zero, ← Finsupp.mem_support_iff, Nat.factor_iff_mem_factorization,
    Nat.mem_factors_iff_dvd hn' (Nat.minFac_prime hn)]
  apply Nat.minFac_dvd
  -- 🎉 no goals
#align is_prime_pow_of_min_fac_pow_factorization_eq isPrimePow_of_minFac_pow_factorization_eq

theorem isPrimePow_iff_minFac_pow_factorization_eq {n : ℕ} (hn : n ≠ 1) :
    IsPrimePow n ↔ n.minFac ^ n.factorization n.minFac = n :=
  ⟨fun h => h.minFac_pow_factorization_eq, fun h => isPrimePow_of_minFac_pow_factorization_eq h hn⟩
#align is_prime_pow_iff_min_fac_pow_factorization_eq isPrimePow_iff_minFac_pow_factorization_eq

theorem isPrimePow_iff_factorization_eq_single {n : ℕ} :
    IsPrimePow n ↔ ∃ p k : ℕ, 0 < k ∧ n.factorization = Finsupp.single p k := by
  rw [isPrimePow_nat_iff]
  -- ⊢ (∃ p k, Nat.Prime p ∧ 0 < k ∧ p ^ k = n) ↔ ∃ p k, 0 < k ∧ Nat.factorization  …
  refine' exists₂_congr fun p k => _
  -- ⊢ Nat.Prime p ∧ 0 < k ∧ p ^ k = n ↔ 0 < k ∧ Nat.factorization n = Finsupp.sing …
  constructor
  -- ⊢ Nat.Prime p ∧ 0 < k ∧ p ^ k = n → 0 < k ∧ Nat.factorization n = Finsupp.sing …
  · rintro ⟨hp, hk, hn⟩
    -- ⊢ 0 < k ∧ Nat.factorization n = Finsupp.single p k
    exact ⟨hk, by rw [← hn, Nat.Prime.factorization_pow hp]⟩
    -- 🎉 no goals
  · rintro ⟨hk, hn⟩
    -- ⊢ Nat.Prime p ∧ 0 < k ∧ p ^ k = n
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp_all only [Finsupp.single_eq_zero, eq_comm, Nat.factorization_zero, hk.ne']
    rw [Nat.eq_pow_of_factorization_eq_single hn0 hn]
    -- ⊢ Nat.Prime p ∧ 0 < k ∧ p ^ k = p ^ k
    exact
      ⟨Nat.prime_of_mem_factorization (by simp [hn, hk.ne'] : p ∈ n.factorization.support), hk, rfl⟩
#align is_prime_pow_iff_factorization_eq_single isPrimePow_iff_factorization_eq_single

theorem isPrimePow_iff_card_support_factorization_eq_one {n : ℕ} :
    IsPrimePow n ↔ n.factorization.support.card = 1 := by
  simp_rw [isPrimePow_iff_factorization_eq_single, Finsupp.card_support_eq_one', exists_prop,
    pos_iff_ne_zero]
#align is_prime_pow_iff_card_support_factorization_eq_one isPrimePow_iff_card_support_factorization_eq_one

theorem IsPrimePow.exists_ord_compl_eq_one {n : ℕ} (h : IsPrimePow n) :
    ∃ p : ℕ, p.Prime ∧ ord_compl[p] n = 1 := by
  rcases eq_or_ne n 0 with (rfl | hn0); · cases not_isPrimePow_zero h
  -- ⊢ ∃ p, Nat.Prime p ∧ 0 / p ^ ↑(Nat.factorization 0) p = 1
                                          -- 🎉 no goals
  rcases isPrimePow_iff_factorization_eq_single.mp h with ⟨p, k, hk0, h1⟩
  -- ⊢ ∃ p, Nat.Prime p ∧ n / p ^ ↑(Nat.factorization n) p = 1
  rcases em' p.Prime with (pp | pp)
  -- ⊢ ∃ p, Nat.Prime p ∧ n / p ^ ↑(Nat.factorization n) p = 1
  · refine' absurd _ hk0.ne'
    -- ⊢ k = 0
    simp [← Nat.factorization_eq_zero_of_non_prime n pp, h1]
    -- 🎉 no goals
  refine' ⟨p, pp, _⟩
  -- ⊢ n / p ^ ↑(Nat.factorization n) p = 1
  refine' Nat.eq_of_factorization_eq (Nat.ord_compl_pos p hn0).ne' (by simp) fun q => _
  -- ⊢ ↑(Nat.factorization (n / p ^ ↑(Nat.factorization n) p)) q = ↑(Nat.factorizat …
  rw [Nat.factorization_ord_compl n p, h1]
  -- ⊢ ↑(Finsupp.erase p (Finsupp.single p k)) q = ↑(Nat.factorization 1) q
  simp
  -- 🎉 no goals
#align is_prime_pow.exists_ord_compl_eq_one IsPrimePow.exists_ord_compl_eq_one

theorem exists_ord_compl_eq_one_iff_isPrimePow {n : ℕ} (hn : n ≠ 1) :
    IsPrimePow n ↔ ∃ p : ℕ, p.Prime ∧ ord_compl[p] n = 1 := by
  refine' ⟨fun h => IsPrimePow.exists_ord_compl_eq_one h, fun h => _⟩
  -- ⊢ IsPrimePow n
  rcases h with ⟨p, pp, h⟩
  -- ⊢ IsPrimePow n
  rw [isPrimePow_nat_iff]
  -- ⊢ ∃ p k, Nat.Prime p ∧ 0 < k ∧ p ^ k = n
  rw [← Nat.eq_of_dvd_of_div_eq_one (Nat.ord_proj_dvd n p) h] at hn ⊢
  -- ⊢ ∃ p_1 k, Nat.Prime p_1 ∧ 0 < k ∧ p_1 ^ k = p ^ ↑(Nat.factorization n) p
  refine' ⟨p, n.factorization p, pp, _, by simp⟩
  -- ⊢ 0 < ↑(Nat.factorization n) p
  contrapose! hn
  -- ⊢ p ^ ↑(Nat.factorization n) p = 1
  simp [le_zero_iff.1 hn]
  -- 🎉 no goals
#align exists_ord_compl_eq_one_iff_is_prime_pow exists_ord_compl_eq_one_iff_isPrimePow

/-- An equivalent definition for prime powers: `n` is a prime power iff there is a unique prime
dividing it. -/
theorem isPrimePow_iff_unique_prime_dvd {n : ℕ} : IsPrimePow n ↔ ∃! p : ℕ, p.Prime ∧ p ∣ n := by
  rw [isPrimePow_nat_iff]
  -- ⊢ (∃ p k, Nat.Prime p ∧ 0 < k ∧ p ^ k = n) ↔ ∃! p, Nat.Prime p ∧ p ∣ n
  constructor
  -- ⊢ (∃ p k, Nat.Prime p ∧ 0 < k ∧ p ^ k = n) → ∃! p, Nat.Prime p ∧ p ∣ n
  · rintro ⟨p, k, hp, hk, rfl⟩
    -- ⊢ ∃! p_1, Nat.Prime p_1 ∧ p_1 ∣ p ^ k
    refine' ⟨p, ⟨hp, dvd_pow_self _ hk.ne'⟩, _⟩
    -- ⊢ ∀ (y : ℕ), (fun p_1 => Nat.Prime p_1 ∧ p_1 ∣ p ^ k) y → y = p
    rintro q ⟨hq, hq'⟩
    -- ⊢ q = p
    exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hq')
    -- 🎉 no goals
  rintro ⟨p, ⟨hp, hn⟩, hq⟩
  -- ⊢ ∃ p k, Nat.Prime p ∧ 0 < k ∧ p ^ k = n
  rcases eq_or_ne n 0 with (rfl | hn₀)
  -- ⊢ ∃ p k, Nat.Prime p ∧ 0 < k ∧ p ^ k = 0
  · cases (hq 2 ⟨Nat.prime_two, dvd_zero 2⟩).trans (hq 3 ⟨Nat.prime_three, dvd_zero 3⟩).symm
    -- 🎉 no goals
  refine' ⟨p, n.factorization p, hp, hp.factorization_pos_of_dvd hn₀ hn, _⟩
  -- ⊢ p ^ ↑(Nat.factorization n) p = n
  simp only [and_imp] at hq
  -- ⊢ p ^ ↑(Nat.factorization n) p = n
  apply Nat.dvd_antisymm (Nat.ord_proj_dvd _ _)
  -- ⊢ n ∣ p ^ ↑(Nat.factorization n) p
  -- We need to show n ∣ p ^ n.factorization p
  apply Nat.dvd_of_factors_subperm hn₀
  -- ⊢ Nat.factors n <+~ Nat.factors (p ^ ↑(Nat.factorization n) p)
  rw [hp.factors_pow, List.subperm_ext_iff]
  -- ⊢ ∀ (x : ℕ), x ∈ Nat.factors n → List.count x (Nat.factors n) ≤ List.count x ( …
  intro q hq'
  -- ⊢ List.count q (Nat.factors n) ≤ List.count q (List.replicate (↑(Nat.factoriza …
  rw [Nat.mem_factors hn₀] at hq'
  -- ⊢ List.count q (Nat.factors n) ≤ List.count q (List.replicate (↑(Nat.factoriza …
  cases hq _ hq'.1 hq'.2
  -- ⊢ List.count p (Nat.factors n) ≤ List.count p (List.replicate (↑(Nat.factoriza …
  simp
  -- 🎉 no goals
#align is_prime_pow_iff_unique_prime_dvd isPrimePow_iff_unique_prime_dvd

theorem isPrimePow_pow_iff {n k : ℕ} (hk : k ≠ 0) : IsPrimePow (n ^ k) ↔ IsPrimePow n := by
  simp only [isPrimePow_iff_unique_prime_dvd]
  -- ⊢ (∃! p, Nat.Prime p ∧ p ∣ n ^ k) ↔ ∃! p, Nat.Prime p ∧ p ∣ n
  apply exists_unique_congr
  -- ⊢ ∀ (a : ℕ), Nat.Prime a ∧ a ∣ n ^ k ↔ Nat.Prime a ∧ a ∣ n
  simp only [and_congr_right_iff]
  -- ⊢ ∀ (a : ℕ), Nat.Prime a → (a ∣ n ^ k ↔ a ∣ n)
  intro p hp
  -- ⊢ p ∣ n ^ k ↔ p ∣ n
  exact ⟨hp.dvd_of_dvd_pow, fun t => t.trans (dvd_pow_self _ hk)⟩
  -- 🎉 no goals
#align is_prime_pow_pow_iff isPrimePow_pow_iff

theorem Nat.coprime.isPrimePow_dvd_mul {n a b : ℕ} (hab : Nat.coprime a b) (hn : IsPrimePow n) :
    n ∣ a * b ↔ n ∣ a ∨ n ∣ b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  -- ⊢ n ∣ 0 * b ↔ n ∣ 0 ∨ n ∣ b
  · simp only [Nat.coprime_zero_left] at hab
    -- ⊢ n ∣ 0 * b ↔ n ∣ 0 ∨ n ∣ b
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
    -- 🎉 no goals
  rcases eq_or_ne b 0 with (rfl | hb)
  -- ⊢ n ∣ a * 0 ↔ n ∣ a ∨ n ∣ 0
  · simp only [Nat.coprime_zero_right] at hab
    -- ⊢ n ∣ a * 0 ↔ n ∣ a ∨ n ∣ 0
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
    -- 🎉 no goals
  refine'
    ⟨_, fun h =>
      Or.elim h (fun i => i.trans ((@dvd_mul_right a b a hab).mpr (dvd_refl a)))
          fun i => i.trans ((@dvd_mul_left a b b hab.symm).mpr (dvd_refl b))⟩
  obtain ⟨p, k, hp, _, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  -- ⊢ p ^ k ∣ a * b → p ^ k ∣ a ∨ p ^ k ∣ b
  simp only [hp.pow_dvd_iff_le_factorization (mul_ne_zero ha hb), Nat.factorization_mul ha hb,
    hp.pow_dvd_iff_le_factorization ha, hp.pow_dvd_iff_le_factorization hb, Pi.add_apply,
    Finsupp.coe_add]
  have : a.factorization p = 0 ∨ b.factorization p = 0 := by
    rw [← Finsupp.not_mem_support_iff, ← Finsupp.not_mem_support_iff, ← not_and_or, ←
      Finset.mem_inter]
    intro t -- porting note: used to be `exact` below, but the definition of `∈` has changed.
    simpa using (Nat.factorization_disjoint_of_coprime hab).le_bot t
  cases' this with h h <;> simp [h, imp_or]
  -- ⊢ k ≤ ↑(factorization a) p + ↑(factorization b) p → k ≤ ↑(factorization a) p ∨ …
                           -- 🎉 no goals
                           -- 🎉 no goals
#align nat.coprime.is_prime_pow_dvd_mul Nat.coprime.isPrimePow_dvd_mul

theorem Nat.mul_divisors_filter_prime_pow {a b : ℕ} (hab : a.coprime b) :
    (a * b).divisors.filter IsPrimePow = (a.divisors ∪ b.divisors).filter IsPrimePow := by
  rcases eq_or_ne a 0 with (rfl | ha)
  -- ⊢ Finset.filter IsPrimePow (divisors (0 * b)) = Finset.filter IsPrimePow (divi …
  · simp only [Nat.coprime_zero_left] at hab
    -- ⊢ Finset.filter IsPrimePow (divisors (0 * b)) = Finset.filter IsPrimePow (divi …
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
    -- 🎉 no goals
  rcases eq_or_ne b 0 with (rfl | hb)
  -- ⊢ Finset.filter IsPrimePow (divisors (a * 0)) = Finset.filter IsPrimePow (divi …
  · simp only [Nat.coprime_zero_right] at hab
    -- ⊢ Finset.filter IsPrimePow (divisors (a * 0)) = Finset.filter IsPrimePow (divi …
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
    -- 🎉 no goals
  ext n
  -- ⊢ n ∈ Finset.filter IsPrimePow (divisors (a * b)) ↔ n ∈ Finset.filter IsPrimeP …
  simp only [ha, hb, Finset.mem_union, Finset.mem_filter, Nat.mul_eq_zero, and_true_iff, Ne.def,
    and_congr_left_iff, not_false_iff, Nat.mem_divisors, or_self_iff]
  apply hab.isPrimePow_dvd_mul
  -- 🎉 no goals
#align nat.mul_divisors_filter_prime_pow Nat.mul_divisors_filter_prime_pow
