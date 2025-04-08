/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.RingTheory.Binomial

/-!

# Binomial Series

This file introduces the binomial series:
$$
\sum_{k=0}^{\infty} \; \binom{a}{k} \; x^k = 1 + a x + \frac{a(a-1)}{2!} x^2 +
  \frac{a(a-1)(a-2)}{3!} x^3 + \cdots
$$
where $a$ is an element of a normed field $\mathbb{K}$,
and $x$ is an element of a normed algebra over $\mathbb{K}$.

## Main Statements

* `binomialSeries_radius_eq_one`: The radius of convergence of the binomial series is `1`.
* `one_add_cpow_hasFPowerSeriesOnBall_zero`: The binomial series converges to `(1 + z)^a` for
  complex `a` and `|z| < 1`.

-/

open scoped Nat

universe u v

/-- Binomial series:
$$
\sum_{k=0}^{\infty} \; \binom{a}{k} \; x^k = 1 + a x + \frac{a(a-1)}{2!} x^2 +
  \frac{a(a-1)(a-2)}{3!} x^3 + \cdots
$$
-/
noncomputable def binomialSeries {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂] (𝔸 : Type v)
    [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] (a : 𝕂) :
    FormalMultilinearSeries 𝕂 𝔸 𝔸 := .ofScalars 𝔸 (Ring.choose a ·)

theorem binomialSeries_eq_ordinaryHypergeometricSeries {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂]
    {𝔸 : Type v} [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] {a b : 𝕂}
    (h : ∀ (k : ℕ), (k : 𝕂) ≠ -b) :
    binomialSeries 𝔸 a =
    (ordinaryHypergeometricSeries 𝔸 (-a) b b).compContinuousLinearMap (-(.id _ _)) := by
  simp [binomialSeries, ordinaryHypergeometricSeries]
  ext n v
  simp [FormalMultilinearSeries.ofScalars, ordinaryHypergeometricCoefficient]
  rw [mul_inv_cancel_right₀]
  swap
  · intro h_zero
    rw [ascPochhammer_eval_eq_zero_iff] at h_zero
    tauto
  have : ((-ContinuousLinearMap.id 𝕂 𝔸 : _) : 𝔸 → 𝔸) = Neg.neg := by
    ext
    simp
  rw [ascPochhammer_eval_neg_eq_descPochhammer, Ring.choose_eq_smul, ← List.map_ofFn, this,
    List.prod_map_neg (List.ofFn v), Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval, descPochhammer_eval_eq_ascPochhammer]
  simp
  -- hack
  by_cases h : (Even n)
  · rw [Even.neg_one_pow h, Even.neg_one_pow h]
    simp
  · rw [Nat.not_even_iff_odd] at h
    rw [Odd.neg_one_pow h, Odd.neg_one_pow h]
    simp

/-- The radius of convergence of `binomialSeries 𝔸 a` is `⊤` for natural `a`. -/
theorem binomialSeries_radius_eq_top_of_nat {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u}
    [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸] {a : ℕ} :
    (binomialSeries 𝔸 (a : 𝕂)).radius = ⊤ := by
  have : ∀ (k : ℕ), (k : 𝕂) ≠ -1 := by
    -- TODO: golf
    intro k h
    replace h : (k : ℝ) = -1 := by
      rwa [← RCLike.ofReal_natCast, ← RCLike.ofReal_one, ← RCLike.ofReal_neg,
        RCLike.ofReal_inj] at h
    linarith
  simp [binomialSeries_eq_ordinaryHypergeometricSeries this,
    ordinaryHypergeometric_radius_top_of_neg_nat₁]

/-- The radius of convergence of `binomialSeries 𝔸 a` is `1`, when `a` is not natural. -/
theorem binomialSeries_radius_eq_one {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u} [NormedDivisionRing 𝔸]
    [NormedAlgebra 𝕂 𝔸] {a : 𝕂} (ha : ∀ (k : ℕ), a ≠ k) : (binomialSeries 𝔸 a).radius = 1 := by
  have : ∀ (k : ℕ), (k : 𝕂) ≠ -1 := by
  -- TODO: golf
    intro k h
    replace h : (k : ℝ) = -1 := by
      rwa [← RCLike.ofReal_natCast, ← RCLike.ofReal_one, ← RCLike.ofReal_neg,
        RCLike.ofReal_inj] at h
    linarith
  simp [binomialSeries_eq_ordinaryHypergeometricSeries this]
  rw [ordinaryHypergeometricSeries_radius_eq_one]
  intro k
  simp only [neg_neg, ne_eq, one_div, and_self]
  exact ⟨(ha k).symm, this k⟩

theorem binomialSeries_radius_ge_one {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u} [NormedDivisionRing 𝔸]
    [NormedAlgebra 𝕂 𝔸] {a : 𝕂} : 1 ≤ (binomialSeries 𝔸 a).radius := by
  by_cases h : ∃ (k : ℕ), a = k
  · obtain ⟨k, h⟩ := h
    simp [h, binomialSeries_radius_eq_top_of_nat]
  · push_neg at h
    rw [binomialSeries_radius_eq_one h]

theorem one_add_cpow_hasFPowerSeriesOnBall_zero {a : ℂ} :
    HasFPowerSeriesOnBall (fun x ↦ (1 + x)^a) (binomialSeries ℂ a) 0 1 := by
  suffices (binomialSeries ℂ a = FormalMultilinearSeries.ofScalars ℂ
      fun n ↦ iteratedDeriv n (fun (x : ℂ) ↦ (1 + x) ^ a) 0 / n !) by
    convert AnalyticOnNhd.hasFPowerSeriesOnBall _ _ _
    · norm_num
    · apply AnalyticOnNhd.cpow
      · apply AnalyticOnNhd.add
        · exact analyticOnNhd_const
        · exact analyticOnNhd_id
      · exact analyticOnNhd_const
      · intro z hz
        apply Complex.mem_slitPlane_of_norm_lt_one
        rw [← ENNReal.ofReal_one, Metric.emetric_ball] at hz
        simpa using hz
    · rw [← this]
      exact binomialSeries_radius_ge_one
  simp only [binomialSeries, FormalMultilinearSeries.ofScalars_series_eq_iff]
  ext n
  rw [Ring.choose_eq_smul]
  field_simp
  congr
  let B := Metric.ball (0 : ℂ) 1
  suffices Set.EqOn (iteratedDerivWithin n (fun x ↦ (1 + x) ^ a) B)
      (fun x ↦ (descPochhammer ℤ n).smeval a * (1 + x)^(a - n)) B by
    specialize this (show 0 ∈ _ by simp [B])
    symm
    rw [iteratedDerivWithin_of_isOpen Metric.isOpen_ball (by simp [B])] at this
    simpa using this
  induction n with
  | zero =>simp [Set.EqOn]
  | succ n ih =>
    have : iteratedDerivWithin (n + 1) (fun (x : ℂ) ↦ (1 + x) ^ a) B =
        derivWithin (iteratedDerivWithin n (fun x ↦ (1 + x) ^ a) B) B := by
      ext z
      rw [iteratedDerivWithin_succ]
    rw [this]
    clear this
    have : Set.EqOn (derivWithin (iteratedDerivWithin n (fun (x : ℂ) ↦ (1 + x) ^ a) B) B)
        (derivWithin (fun x ↦ (descPochhammer ℤ n).smeval a * (1 + x) ^ (a - ↑n)) B) B := by
      intro z hz
      rw [derivWithin_congr]
      · intro z hz
        exact ih hz
      · exact ih hz
    apply Set.EqOn.trans this
    intro z hz
    simp only [Nat.cast_add, Nat.cast_one, B]
    rw [derivWithin_of_isOpen Metric.isOpen_ball hz]
    simp only [differentiableAt_const, deriv_const_mul_field', B]
    rw [deriv_cpow_const]
    rotate_left
    · fun_prop
    · apply Complex.mem_slitPlane_of_norm_lt_one
      simpa [B] using hz
    rw [deriv_const_add', deriv_id'', mul_one, show a - (n + 1) = a - n - 1 by ring, ← mul_assoc]
    congr
    simp [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_natCast]

theorem one_add_cpow_hasFPowerSeriesAt_zero {a : ℂ} :
    HasFPowerSeriesAt (fun x ↦ (1 + x)^a) (binomialSeries ℂ a) 0 := by
  apply HasFPowerSeriesOnBall.hasFPowerSeriesAt one_add_cpow_hasFPowerSeriesOnBall_zero

theorem one_add_rpow_hasFPowerSeriesOnBall_zero {a : ℝ} :
    HasFPowerSeriesOnBall (fun x ↦ (1 + x)^a) (binomialSeries ℝ a) 0 1 := by
  have h : HasFPowerSeriesOnBall (fun x ↦ (1 + x)^(a : ℂ)) (binomialSeries ℂ a) 0 1 := by
    have : binomialSeries ℂ a = (binomialSeries ℂ (a : ℂ)).restrictScalars (𝕜 := ℝ) := by
      ext n v
      simp only [binomialSeries, FormalMultilinearSeries.ofScalars,
        ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
        Complex.real_smul, FormalMultilinearSeries.restrictScalars,
        ContinuousMultilinearMap.coe_restrictScalars, smul_eq_mul, mul_eq_mul_right_iff,
        List.prod_eq_zero_iff, List.mem_ofFn]
      left
      -- ↑(Ring.choose a n) = Ring.choose (↑a) n
      simp only [Ring.choose_eq_smul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv,
        Complex.ofReal_natCast, mul_eq_mul_left_iff, inv_eq_zero, Nat.cast_eq_zero]
      left
      rw [Polynomial.smeval_def, Polynomial.smeval_def]
      simp only [Polynomial.sum, Complex.ofReal_sum]
      congr
      ext n
      simp [Polynomial.smul_pow]
    rw [this]
    exact HasFPowerSeriesOnBall.restrictScalars one_add_cpow_hasFPowerSeriesOnBall_zero
  rw [show 0 = Complex.ofRealCLM 0 by simp] at h
  apply HasFPowerSeriesOnBall.compContinuousLinearMap at h
  simp only [Complex.ofRealCLM_nnnorm, ENNReal.coe_one, div_one] at h
  have h' : Set.EqOn ((fun x ↦ (1 + x) ^ (a : ℂ)) ∘ ⇑Complex.ofRealCLM)
      (fun (x : ℝ) ↦ (Real.rpow (1 + x) a : ℂ)) (EMetric.ball 0 1) := by
    intro x hx
    simp only [Function.comp_apply, Complex.ofRealCLM_apply, Real.rpow_eq_pow]
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_cpow]
    rw [← ENNReal.ofReal_one, Metric.emetric_ball] at hx
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hx
    apply neg_lt_of_abs_lt at hx
    linarith
  replace h := ContinuousLinearMap.comp_hasFPowerSeriesOnBall Complex.reCLM (h.congr h')
  conv at h => arg 1; eta_expand; intro x; simp
  convert h
  ext n v
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, smul_eq_mul,
    ContinuousLinearMap.compFormalMultilinearSeries_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, Complex.real_smul,
    Complex.ofReal_prod, Complex.reCLM_apply]
  conv =>
    rhs; arg 1; arg 2
    unfold FormalMultilinearSeries.coeff
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
    simp only [binomialSeries, FormalMultilinearSeries.ofScalars, Pi.comp_one,
      Complex.ofRealCLM_apply, Complex.ofReal_one, Function.const_one,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
      Fin.prod_ofFn, Pi.one_apply, Finset.prod_const_one, Complex.real_smul, mul_one]
  rw [← Complex.ofReal_prod, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp [binomialSeries]

theorem one_add_rpow_hasFPowerSeriesAt_zero {a : ℝ} :
    HasFPowerSeriesAt (fun x ↦ (1 + x)^a) (binomialSeries ℝ a) 0 := by
  apply HasFPowerSeriesOnBall.hasFPowerSeriesAt one_add_rpow_hasFPowerSeriesOnBall_zero
