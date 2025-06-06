/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.MetricSpace.Polish

/-!
# Fernique's theorem for rotation-invariant measures

## Main definitions

* `IsGaussian`

## Main statements

* `fooBar_unique`

## References

* [Martin Hairer, *An introduction to stochastic PDEs*][hairer2009introduction]

-/

open MeasureTheory ProbabilityTheory Complex NormedSpace
open scoped ENNReal NNReal Real Topology

section Aux

lemma norm_add_sub_norm_sub_div_two_le {E : Type*} [NormedAddCommGroup E] (x y : E) :
    (‖x + y‖ - ‖x - y‖) / 2 ≤ ‖x‖ := by
  suffices ‖x + y‖ - ‖x - y‖ ≤ 2 * ‖x‖ by linarith
  calc ‖x + y‖ - ‖x - y‖
  _ = ‖x + x + y - x‖ - ‖x - y‖ := by congr; abel
  _ ≤ ‖x + x‖ + ‖y - x‖ - ‖x - y‖ := by gcongr; rw [add_sub_assoc]; exact norm_add_le _ _
  _ = ‖x + x‖ := by rw [norm_sub_rev]; abel
  _ ≤ ‖x‖ + ‖x‖ := norm_add_le _ _
  _ = 2 * ‖x‖ := by rw [two_mul]

lemma norm_add_sub_norm_sub_div_two_le_min {E : Type*} [NormedAddCommGroup E] (x y : E) :
    (‖x + y‖ - ‖x - y‖) / 2 ≤ min ‖x‖ ‖y‖ := by
  refine le_min (norm_add_sub_norm_sub_div_two_le x y) ?_
  rw [norm_sub_rev, add_comm]
  exact norm_add_sub_norm_sub_div_two_le _ _

lemma one_lt_sqrt_two : 1 < √2 := by rw [← Real.sqrt_one]; gcongr; simp

lemma sqrt_two_lt_three_halves : √2 < 3 / 2 := by
  suffices 2 * √2 < 3 by linarith
  rw [← sq_lt_sq₀ (by positivity) (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
  norm_num

open Filter in
lemma exists_between' {t : ℕ → ℝ} (ht_mono : StrictMono t) (ht_tendsto : Tendsto t atTop atTop)
    (x : ℝ) :
    x ≤ t 0 ∨ ∃ n, t n < x ∧ x ≤ t (n + 1) := by
  by_cases hx0 : x ≤ t 0
  · simp [hx0]
  simp only [hx0, false_or]
  have h : ∃ n, x ≤ t n := by
    simp [tendsto_atTop_atTop_iff_of_monotone ht_mono.monotone] at ht_tendsto
    exact ht_tendsto x
  have h' := Nat.find_spec h
  have h'' m := Nat.find_min h (m := m)
  simp only [not_le] at h'' hx0
  refine ⟨Nat.find h - 1, ?_, ?_⟩
  · refine h'' _ ?_
    simp [hx0]
  · convert h'
    rw [Nat.sub_add_cancel]
    simp [hx0]

lemma two_mul_mul_le_mul_add_div {a b ε : ℝ} (hε : 0 < ε) :
    2 * a * b ≤ ε * a ^ 2 + (1 / ε) * b ^ 2 := by
  have h : 2 * (ε * a) * b ≤ (ε * a) ^ 2 + b ^ 2 := two_mul_le_add_sq (ε * a) b
  calc 2 * a * b
  _ = (2 * (ε * a) * b) / ε := by field_simp; ring
  _ ≤ ((ε * a) ^ 2 + b ^ 2) / ε := by gcongr
  _ = ε * a ^ 2 + (1 / ε) * b ^ 2  := by field_simp; ring

lemma Nat.le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ, mul_two]
    gcongr
    exact Nat.one_le_two_pow

lemma aux {c : ℝ} (hc : c < 0) :
    ∑' i, .ofReal (rexp (c * 2 ^ i)) < ∞ := by
  calc ∑' i, .ofReal (rexp (c * 2 ^ i))
  _ ≤ ∑' i : ℕ, .ofReal (rexp (i * c)) := by
    simp_rw [mul_comm _ c]
    refine ENNReal.tsum_le_tsum fun i ↦ ?_
    refine ENNReal.ofReal_le_ofReal ?_
    refine Real.exp_monotone ?_
    refine mul_le_mul_of_nonpos_left ?_ hc.le
    exact mod_cast Nat.le_two_pow i
  _ < ∞ := by
    have h_sum : Summable fun i : ℕ ↦ rexp (i * c) := Real.summable_exp_nat_mul_iff.mpr hc
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) h_sum]
    simp

end Aux

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E}

section Fernique

variable [SecondCountableTopology E]

/-- The rotation in `E × E` with angle `θ`, as a continuous linear map. -/
noncomputable
def _root_.ContinuousLinearMap.rotation (θ : ℝ) : E × E →L[ℝ] E × E where
  toFun := fun x ↦ (Real.cos θ • x.1 + Real.sin θ • x.2, - Real.sin θ • x.1 + Real.cos θ • x.2)
  map_add' x y := by
    simp only [Prod.fst_add, smul_add, Prod.snd_add, neg_smul, Prod.mk_add_mk]
    abel_nf
  map_smul' c x := by simp [smul_comm c]
  cont := by fun_prop

lemma _root_.ContinuousLinearMap.rotation_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (θ : ℝ) (x : E × E) :
    ContinuousLinearMap.rotation θ x
     = (Real.cos θ • x.1 + Real.sin θ • x.2, - Real.sin θ • x.1 + Real.cos θ • x.2) := rfl

lemma measure_le_mul_measure_gt_le_of_map_rotation_eq_self [SFinite μ]
    (h : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ)
    (a b : ℝ) :
    μ {x | ‖x‖ ≤ a} * μ {x | b < ‖x‖} ≤ μ {x | (b - a) / √2 < ‖x‖} ^ 2 := by
  calc μ {x | ‖x‖ ≤ a} * μ {x | b < ‖x‖}
  _ = (μ.prod μ) ({x | ‖x‖ ≤ a} ×ˢ {y | b < ‖y‖}) := by rw [Measure.prod_prod]
    -- this is the measure of two bands in the plane (draw a picture!)
  _ = (μ.prod μ) {p | ‖p.1‖ ≤ a ∧ b < ‖p.2‖} := rfl
  _ = ((μ.prod μ).map (ContinuousLinearMap.rotation (- (π/4)))) {p | ‖p.1‖ ≤ a ∧ b < ‖p.2‖} := by
    -- we can rotate the bands since `μ.prod μ` is invariant under rotation
    rw [h]
  _ = (μ.prod μ) {p | ‖p.1 - p.2‖ / √2 ≤ a ∧ b < ‖p.1 + p.2‖ / √2} := by
    rw [Measure.map_apply (by fun_prop)]
    swap
    · refine MeasurableSet.inter ?_ ?_
      · change MeasurableSet {p : E × E | ‖p.1‖ ≤ a}
        exact measurableSet_le (by fun_prop) (by fun_prop)
      · change MeasurableSet {p : E × E | b < ‖p.2‖}
        exact measurableSet_lt (by fun_prop) (by fun_prop)
    congr 1
    simp only [Set.preimage_setOf_eq, ContinuousLinearMap.rotation_apply, Real.cos_neg,
      Real.cos_pi_div_four, Real.sin_neg, Real.sin_pi_div_four, neg_smul, neg_neg]
    have h_twos : ‖2⁻¹ * √2‖ = (√2)⁻¹ := by
      simp only [norm_mul, norm_inv, Real.norm_ofNat, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      nth_rw 1 [← Real.sq_sqrt (by simp : (0 : ℝ) ≤ 2)]
      rw [pow_two, mul_inv, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
    congr! with p
    · rw [← sub_eq_add_neg, ← smul_sub, norm_smul, div_eq_inv_mul, div_eq_inv_mul]
      congr
    · rw [← smul_add, norm_smul, div_eq_inv_mul, div_eq_inv_mul]
      congr
  _ ≤ (μ.prod μ) {p | (b - a) / √2 < ‖p.1‖ ∧ (b - a) / √2 < ‖p.2‖} := by
    -- the rotated bands are contained in quadrants.
    refine measure_mono fun p ↦ ?_
    simp only [Set.mem_setOf_eq, and_imp]
    intro hp1 hp2
    suffices (b - a) / √2 < min ‖p.1‖ ‖p.2‖ from lt_min_iff.mp this
    calc (b - a) / √2
    _ < (‖p.1 + p.2‖ - ‖p.1 - p.2‖) / 2 := by
      suffices b - a < ‖p.1 + p.2‖ / √2 - ‖p.1 - p.2‖ / √2 by
        calc (b - a) / √2
        _ < (‖p.1 + p.2‖ / √2 - ‖p.1 - p.2‖ / √2) / √2 := by gcongr
        _ = (‖p.1 + p.2‖ - ‖p.1 - p.2‖) / 2 := by
          rw [sub_div, div_div, div_div, ← pow_two, Real.sq_sqrt, sub_div]
          simp
      calc b - a
      _ < ‖p.1 + p.2‖ / √2 - a := by gcongr
      _ ≤ ‖p.1 + p.2‖ / √2 - ‖p.1 - p.2‖ / √2 := by gcongr
    _ ≤ min ‖p.1‖ ‖p.2‖ := norm_add_sub_norm_sub_div_two_le_min _ _
  _ = (μ.prod μ) ({x | (b - a) / √2 < ‖x‖} ×ˢ {y | (b - a) / √2 < ‖y‖}) := rfl
  _ ≤ μ {x | (b - a) / √2 < ‖x‖} ^ 2 := by rw [Measure.prod_prod, pow_two]

section ArithmeticGeometricSequence

variable {u : ℕ → ℝ} {a b : ℝ}

lemma todo1 (hu : ∀ n, u (n + 1) = a * u n + b) (ha : a ≠ 1) (n : ℕ) :
    u n = a ^ n * (u 0 - (b / (1 - a))) + b / (1 - a) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [hu, hn, pow_succ]
    have : 1 - a ≠ 0 := sub_ne_zero_of_ne ha.symm
    field_simp
    ring

open Filter in
lemma tendsto_todo_atTop (hu : ∀ n, u (n + 1) = a * u n + b) (ha : 1 < a) (h0 : b / (1 - a) < u 0) :
    Tendsto u atTop atTop := by
  have : u = fun n ↦ a ^ n * (u 0 - (b / (1 - a))) + b / (1 - a) := by ext; exact todo1 hu ha.ne' _
  rw [this]
  refine tendsto_atTop_add_const_right _ _ ?_
  refine Tendsto.atTop_mul_const (sub_pos.mpr h0) ?_
  exact tendsto_pow_atTop_atTop_of_one_lt ha

lemma lt_todo (hu : ∀ n, u (n + 1) = a * u n + b) (ha_pos : 0 < a) (ha_ne : a ≠ 1)
    (h0 : b / (1 - a) < u 0) (n : ℕ) :
    b / (1 - a) < u n := by
  induction n with
  | zero => exact h0
  | succ n hn =>
    rw [hu]
    calc b / (1 - a)
    _ = a * (b / (1 - a)) + b := by
      have : 1 - a ≠ 0 := sub_ne_zero_of_ne ha_ne.symm
      field_simp
      ring
    _ < a * u n + b := by gcongr

lemma todo_strictMono (hu : ∀ n, u (n + 1) = a * u n + b) (ha : 1 < a) (h0 : b / (1 - a) < u 0) :
    StrictMono u := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  rw [hu]
  have h_lt : b / (1 - a) < u n := lt_todo hu (by positivity) ha.ne' h0 n
  rw [div_lt_iff_of_neg (sub_neg.mpr ha)] at h_lt
  linarith

lemma todo_nonneg (hu : ∀ n, u (n + 1) = a * u n + b) (ha : 1 < a) (h0 : b / (1 - a) < u 0)
    (h0_nonneg : 0 ≤ u 0) (n : ℕ) :
    0 ≤ u n := by
  induction n with
  | zero => exact h0_nonneg
  | succ n =>
    calc 0 ≤ u 0 := h0_nonneg
    _ ≤ u (n + 1) := (todo_strictMono hu ha h0 (by positivity)).le

end ArithmeticGeometricSequence

open Metric Filter in
/-- Auxiliary lemma for `exists_integrable_exp_sq_of_map_rotation_eq_self`.
The assumption `h_meas_Ioo : ∃ a, 0 < a ∧ 2⁻¹ < μ {x | ‖x‖ ≤ a} ∧ μ {x | ‖x‖ ≤ a} < 1` is not
needed and will be removed in that more general theorem. -/
lemma exists_integrable_exp_sq_of_map_rotation_eq_self' [IsProbabilityMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ)
    (h_meas_Ioo : ∃ a, 0 < a ∧ 2⁻¹ < μ {x | ‖x‖ ≤ a} ∧ μ {x | ‖x‖ ≤ a} < 1) :
    ∃ C, 0 < C ∧ Integrable (fun x ↦ rexp (C * ‖x‖ ^ 2)) μ := by
  obtain ⟨a, ha_pos, hc_gt, hc_lt⟩ : ∃ a, 0 < a ∧ 2⁻¹ < μ {x | ‖x‖ ≤ a} ∧ μ {x | ‖x‖ ≤ a} < 1 :=
    h_meas_Ioo
  let c := μ {x | ‖x‖ ≤ a}
  replace hc_gt : 2⁻¹ < c := hc_gt
  have hc_pos : 0 < c := lt_of_lt_of_le (by simp) hc_gt.le
  replace hc_lt : c < 1 := hc_lt
  have hc_lt_top : c < ∞ := lt_top_of_lt hc_lt
  have hc_one_sub_lt_top : 1 - c < ∞ := lt_top_of_lt (b := 2) (tsub_le_self.trans_lt (by simp))
  have h_one_sub_lt_self : 1 - c < c := by
    refine ENNReal.sub_lt_of_lt_add hc_lt.le ?_
    rw [← two_mul]
    rwa [inv_eq_one_div, ENNReal.div_lt_iff, mul_comm] at hc_gt
    · simp
    · simp
  let C : ℝ := a⁻¹ ^ 2 * Real.log (c / (1 - c)).toReal / 24
  have hC_pos : 0 < C := by
    simp only [inv_pow, ENNReal.toReal_div, Nat.ofNat_pos, div_pos_iff_of_pos_right, C]
    refine mul_pos (by positivity) ?_
    rw [Real.log_pos_iff]
    · rw [one_lt_div_iff]
      left
      constructor
      · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hc_lt, true_and, C, hc_one_sub_lt_top]
      · gcongr
        exact hc_lt_top.ne
    · positivity
  refine ⟨C, hC_pos, ?_⟩
  -- main part of the proof: prove integrability by bounding the measure of a sequence of annuli
  refine ⟨by fun_prop, ?_⟩
  simp only [HasFiniteIntegral, ← ofReal_norm_eq_enorm, Real.norm_eq_abs, Real.abs_exp]
  -- `⊢ ∫⁻ (a : E), ENNReal.ofReal (rexp (C * ‖a‖ ^ 2)) ∂μ < ⊤`
  -- We introduce an increasing sequence `t n` and will cut the space into sets of the form
  -- `closedBall 0 (t (n + 1)) \ closedBall 0 (t n)`.
  let t : ℕ → ℝ := Nat.rec a fun n tn ↦ √2 * tn + a -- t 0 = a; t (n + 1) = √2 * t n + a
  have ht_succ_def n : t (n + 1) = √2 * t n + a := rfl
  have ht0 : a / (1 - √2) < t 0 := by
    simp only [Nat.rec_zero, t]
    calc a / (1 - √2)
    _ ≤ 0 := div_nonpos_of_nonneg_of_nonpos ha_pos.le (by simp)
    _ < a := ha_pos
  have ht_mono : StrictMono t := todo_strictMono ht_succ_def one_lt_sqrt_two ht0
  have ht_tendsto : Tendsto t atTop atTop := tendsto_todo_atTop ht_succ_def one_lt_sqrt_two ht0
  -- first, compute bounds on `t (n + 1)`
  have ht_eq n : t n = a * (1 + √2) * (√2 ^ (n + 1) - 1) := by
    rw [todo1 ht_succ_def (by simp), pow_succ]
    simp only [Nat.rec_zero, t]
    have : 1 - √2 ≠ 0 := sub_ne_zero_of_ne (Ne.symm (by simp))
    field_simp
    ring_nf
    have h3 : √2 ^ 3 = 2 * √2 := by rw [pow_succ, Real.sq_sqrt (by positivity)]
    rw [Real.sq_sqrt (by positivity), h3]
    ring
  have ht_succ_le n : t (n + 1) ^ 2 ≤ a ^ 2 * (1 + √2) ^ 2 * 2 ^ (n + 2) := by
    simp_rw [ht_eq, mul_pow, mul_assoc]
    gcongr
    calc (√2 ^ (n + 2) - 1) ^ 2
    _ ≤ (√2 ^ (n + 2)) ^ 2 := by
      gcongr
      · calc 0
        _ ≤ √2 ^ (0 + 2) - 1 := by simp
        _ ≤ √2 ^ (n + 2) - 1 := by gcongr <;> simp
      · exact sub_le_self _ (by simp)
    _ = 2 ^ (n + 2) := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by positivity)]
  -- get a bound on `μ {x | t n < ‖x‖}`
  have ht_meas_le n : μ {x | t n < ‖x‖} ≤ c * ((1 - c) / c) ^ (2 ^ n) := by
    induction n with
    | zero =>
      simp only [pow_zero, pow_one, C]
      rw [ENNReal.mul_div_cancel hc_pos.ne' hc_lt_top.ne]
      refine le_of_eq ?_
      rw [← prob_compl_eq_one_sub]
      · congr with x
        simp [t]
      · exact measurableSet_le (by fun_prop) (by fun_prop)
    | succ n hn =>
      have h_mul_le : c * μ {x | t (n + 1) < ‖x‖} ≤ μ {x | t n < ‖x‖} ^ 2 := by
        convert measure_le_mul_measure_gt_le_of_map_rotation_eq_self h_rot _ _
        rw [ht_succ_def]
        field_simp
      calc μ {x | t (n + 1) < ‖x‖}
      _ = c⁻¹ * (c * μ {x | t (n + 1) < ‖x‖}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc_pos.ne' hc_lt_top.ne, one_mul]
      _ ≤ c⁻¹ * μ {x | t n < ‖x‖} ^ 2 := by gcongr
      _ ≤ c⁻¹ * (c * ((1 - c) / c) ^ 2 ^ n) ^ 2 := by gcongr
      _ = c * ((1 - c) / c) ^ 2 ^ (n + 1) := by
        rw [mul_pow, ← pow_mul, ← mul_assoc, pow_two, ← mul_assoc,
          ENNReal.inv_mul_cancel hc_pos.ne' hc_lt_top.ne, one_mul]
        congr
  -- cut the space into annuli
  have h_iUnion : (Set.univ : Set E)
      = closedBall 0 (t 0) ∪ ⋃ n, closedBall 0 (t (n + 1)) \ closedBall 0 (t n) := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Metric.mem_closedBall, dist_zero_right, Set.mem_iUnion,
      Set.mem_diff, not_le, true_iff]
    simp_rw [and_comm (b := t _ < ‖x‖)]
    exact exists_between' ht_mono ht_tendsto _
  rw [← setLIntegral_univ, h_iUnion]
  have : ∫⁻ x in closedBall 0 (t 0) ∪ ⋃ n, closedBall 0 (t (n + 1)) \ closedBall 0 (t n),
        .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
      ≤ ∫⁻ x in closedBall 0 (t 0), .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ +
        ∑' i, ∫⁻ x in closedBall 0 (t (i + 1)) \ closedBall 0 (t i),
          .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ := by
    refine (lintegral_union_le _ _ _).trans ?_
    gcongr
    exact lintegral_iUnion_le _ _
  refine this.trans_lt ?_
  -- compute bounds on the integral over the annuli
  have ht_int_zero : ∫⁻ x in closedBall 0 (t 0), ENNReal.ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
      ≤ ENNReal.ofReal (rexp (C * t 0 ^ 2)) := by
    calc ∫⁻ x in closedBall 0 (t 0), ENNReal.ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
    _ ≤ ∫⁻ x in closedBall 0 (t 0), ENNReal.ofReal (rexp (C * t 0 ^ 2)) ∂μ := by
      refine setLIntegral_mono (by fun_prop) fun x hx ↦ ?_
      gcongr
      simpa using hx
    _ ≤ ∫⁻ x, ENNReal.ofReal (rexp (C * t 0 ^ 2)) ∂μ := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (rexp (C * t 0 ^ 2)) := by simp
  have ht_int_le n : ∫⁻ x in (closedBall 0 (t (n + 1)) \ closedBall 0 (t n)),
        .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
      ≤ .ofReal (rexp (C * t (n + 1) ^ 2)) * μ {x | t n < ‖x‖} := by
    calc ∫⁻ x in (closedBall 0 (t (n + 1)) \ closedBall 0 (t n)), .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
    _ ≤ ∫⁻ x in (closedBall 0 (t (n + 1)) \ closedBall 0 (t n)),
        .ofReal (rexp (C * t (n + 1) ^ 2)) ∂μ := by
      refine setLIntegral_mono (by fun_prop) fun x hx ↦ ?_
      gcongr
      simp only [Set.mem_diff, mem_closedBall, dist_zero_right, not_le] at hx
      exact hx.1
    _ = .ofReal (rexp (C * t (n + 1) ^ 2)) * μ (closedBall 0 (t (n + 1)) \ closedBall 0 (t n)) := by
      simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, C, t]
    _ ≤ .ofReal (rexp (C * t (n + 1) ^ 2)) * μ {x | t n < ‖x‖} := by
      gcongr
      intro x
      simp
  -- put everything together
  refine ENNReal.add_lt_top.mpr ⟨ht_int_zero.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  calc ∑' i, ∫⁻ x in closedBall 0 (t (i + 1)) \ closedBall 0 (t i),
      .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
  _ ≤ ∑' i, .ofReal (rexp (C * t (i + 1) ^ 2)) * μ {x | t i < ‖x‖} := by
    gcongr with i
    exact ht_int_le i
  _ ≤ ∑' i, .ofReal (rexp (C * (a ^ 2 * (1 + √2) ^ 2 * 2 ^ (i + 2))))
      * (c * ((1 - c) / c) ^ (2 ^ i)) := by
    gcongr with i
    · exact ht_succ_le i
    · exact ht_meas_le i
  _ = c * ∑' i, .ofReal (rexp (C * (a ^ 2 * (1 + √2) ^ 2 * 2 ^ (i + 2))))
      * ((1 - c) / c) ^ (2 ^ i) := by rw [← ENNReal.tsum_mul_left]; congr with i; ring
  _ = c * ∑' i, .ofReal (rexp ((C * a ^ 2 * (1 + √2) ^ 2 * 4 * 2 ^ i)
      + (- Real.log (c / (1 - c)).toReal * 2 ^ i))) := by
    congr with i
    rw [Real.exp_add, ENNReal.ofReal_mul (by positivity)]
    congr 3
    · ring
    · have h_pos : 0 < (1 - c).toReal / c.toReal := by
        refine div_pos ?_ ?_
        · simp [ENNReal.toReal_pos_iff, hc_lt, hc_one_sub_lt_top]
        · simp [ENNReal.toReal_pos_iff, hc_pos, hc_lt_top]
      rw [← Real.log_inv, mul_comm _ (2 ^ i), ← Real.log_rpow, Real.exp_log]
      · rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ENNReal.toReal_div, inv_div, ← ENNReal.toReal_div,  ENNReal.ofReal_toReal]
        · norm_cast
        · simp [ENNReal.div_eq_top, hc_pos.ne']
      · simp only [ENNReal.toReal_div, inv_div]
        refine Real.rpow_pos_of_pos h_pos _
      · simp only [ENNReal.toReal_div, inv_div, h_pos]
  _ = c * ∑' i, .ofReal (rexp ((((1 + √2) ^ 2 * 4 / 24) - 1)
      * Real.log (c / (1 - c)).toReal * 2 ^ i)) := by
    congr with i
    congr
    rw [← add_mul]
    congr
    field_simp [C]
    ring
  _ < ⊤ := by
    refine ENNReal.mul_lt_top hc_lt_top ?_
    refine aux ?_
    refine mul_neg_of_neg_of_pos ?_ ?_
    · have : (1 + √2) ^ 2 = 1 + 2 * √2 + √2 ^ 2 := by ring
      rw [Real.sq_sqrt (by positivity)] at this
      have : √2 < 3 / 2 := sqrt_two_lt_three_halves
      linarith
    · refine Real.log_pos ?_
      simp only [ENNReal.toReal_div, one_lt_div_iff, ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hc_lt,
        hc_one_sub_lt_top, and_self, ne_eq, ENNReal.sub_eq_top_iff, ENNReal.one_ne_top, false_and,
        not_false_eq_true, true_and]
      left
      rw [ENNReal.toReal_lt_toReal hc_one_sub_lt_top.ne hc_lt_top.ne]
      exact h_one_sub_lt_self

/-- Auxiliary lemma for `exists_integrable_exp_sq_of_map_rotation_eq_self`, in which we will replace
the assumption `IsProbabilityMeasure μ` by the weaker `IsFiniteMeasure μ`. -/
lemma exists_integrable_exp_sq_of_map_rotation_eq_self_of_isProbabilityMeasure
    [IsProbabilityMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ) :
    ∃ C, 0 < C ∧ Integrable (fun x ↦ rexp (C * ‖x‖ ^ 2)) μ := by
  by_cases h_meas_Ioo : ∃ a, 0 < a ∧ 2⁻¹ < μ {x | ‖x‖ ≤ a} ∧ μ {x | ‖x‖ ≤ a} < 1
  · exact exists_integrable_exp_sq_of_map_rotation_eq_self' h_rot h_meas_Ioo
  obtain ⟨b, hb⟩ : ∃ b, μ {x | ‖x‖ ≤ b} = 1 := by
    by_contra h_ne
    push_neg at h_meas_Ioo h_ne
    suffices μ .univ ≤ 2 ⁻¹ by simp at this
    have h_le a : μ {x | ‖x‖ ≤ a} ≤ 2⁻¹ := by
      have h_of_pos a' (ha : 0 < a') : μ {x | ‖x‖ ≤ a'} ≤ 2⁻¹ := by
        by_contra h_lt
        refine h_ne a' ?_
        exact le_antisymm prob_le_one (h_meas_Ioo a' ha (not_le.mp h_lt))
      rcases le_or_lt a 0 with ha | ha
      · calc μ {x | ‖x‖ ≤ a}
        _ ≤ μ {x | ‖x‖ ≤ 1} := measure_mono fun x hx ↦ hx.trans (ha.trans (by positivity))
        _ ≤ 2⁻¹ := h_of_pos _ (by positivity)
      · exact h_of_pos a ha
    have h_univ : (Set.univ : Set E) = ⋃ a : ℕ, {x | ‖x‖ ≤ a} := by
      ext x
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
      exact exists_nat_ge _
    rw [h_univ, Monotone.measure_iUnion]
    · simp [h_le]
    · intro a b hab x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      exact hx.trans (mod_cast hab)
  have hb' : ∀ᵐ x ∂μ, ‖x‖ ≤ b := by
    rw [ae_iff]
    change μ {x | ‖x‖ ≤ b}ᶜ = 0
    rw [prob_compl_eq_one_sub]
    · simp [hb]
    · exact measurableSet_le (by fun_prop) (by fun_prop)
  refine ⟨1, by positivity, ?_⟩
  refine integrable_of_le_of_le (g₁ := 0) (g₂ := fun _ ↦ rexp (b ^ 2)) (by fun_prop)
    ?_ ?_ (integrable_const _) (integrable_const _)
  · exact ae_of_all _ fun _ ↦ by positivity
  · filter_upwards [hb'] with x hx
    simp only [one_mul]
    gcongr

/-- Fernique's theorem for finite measures whose product is invariant by rotation: there exists
`C > 0` such that the function `x ↦ exp (C * ‖x‖ ^ 2)` is integrable. -/
theorem exists_integrable_exp_sq_of_map_rotation_eq_self [IsFiniteMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ) :
    ∃ C, 0 < C ∧ Integrable (fun x ↦ rexp (C * ‖x‖ ^ 2)) μ := by
  by_cases hμ_zero : μ = 0
  · exact ⟨1, by positivity, by simp [hμ_zero]⟩
  let μ' := cond μ .univ
  have hμ'_eq : μ' = (μ .univ)⁻¹ • μ := by simp [μ', cond]
  have hμ' : IsProbabilityMeasure μ' := cond_isProbabilityMeasure <| by simp [hμ_zero]
  have h_rot : (μ'.prod μ').map (ContinuousLinearMap.rotation (-(π / 4))) = μ'.prod μ' := by
    calc (μ'.prod μ').map (ContinuousLinearMap.rotation (-(π / 4)))
    _ = ((μ Set.univ)⁻¹ * (μ Set.univ)⁻¹)
        • (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) := by
      simp [hμ'_eq, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    _ = ((μ Set.univ)⁻¹ * (μ Set.univ)⁻¹) • (μ.prod μ) := by rw [h_rot]
    _ = μ'.prod μ' := by
      simp [hμ'_eq, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  obtain ⟨C, hC_pos, hC⟩ :=
    exists_integrable_exp_sq_of_map_rotation_eq_self_of_isProbabilityMeasure (μ := μ') h_rot
  refine ⟨C, hC_pos, ?_⟩
  rwa [hμ'_eq, integrable_smul_measure] at hC
  · simp [hμ_zero]
  · simp [hμ_zero]

end Fernique

end ProbabilityTheory
