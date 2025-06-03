/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/

import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Order.Interval.Finset.Box
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Uniform convergence of Eisenstein series

We show that the sum of `eisSummand` converges locally uniformly on `ℍ` to the Eisenstein series
of weight `k` and level `Γ(N)` with congruence condition `a : Fin 2 → ZMod N`.

## Outline of argument

The key lemma `r_mul_max_le` shows that, for `z ∈ ℍ` and `c, d ∈ ℤ` (not both zero),
`|c z + d|` is bounded below by `r z * max (|c|, |d|)`, where `r z` is an explicit function of `z`
(independent of `c, d`) satisfying `0 < r z < 1` for all `z`.

We then show in `summable_one_div_rpow_max` that the sum of `max (|c|, |d|) ^ (-k)` over
`(c, d) ∈ ℤ × ℤ` is convergent for `2 < k`. This is proved by decomposing `ℤ × ℤ` using the
`Finset.box` lemmas.
-/

noncomputable section

open Complex UpperHalfPlane Set Finset CongruenceSubgroup Topology Filter Asymptotics

open scoped UpperHalfPlane Topology BigOperators Nat


variable (z : ℍ)

namespace EisensteinSeries

lemma norm_eq_max_natAbs (x : Fin 2 → ℤ) : ‖x‖ = max (x 0).natAbs (x 1).natAbs := by
  rw [← coe_nnnorm, ← NNReal.coe_natCast, NNReal.coe_inj, Nat.cast_max]
  refine eq_of_forall_ge_iff fun c ↦ ?_
  simp only [pi_nnnorm_le_iff, Fin.forall_fin_two, max_le_iff, NNReal.natCast_natAbs]


lemma norm_symm (x y : ℤ) : ‖![x, y]‖ = ‖![y,x]‖ := by
  simp_rw [EisensteinSeries.norm_eq_max_natAbs]
  simp [max_comm]

theorem abs_le_left_of_norm (m n : ℤ) : |n| ≤ ‖![n, m]‖ := by
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Nat.cast_max, le_sup_iff]
  left
  rw [Int.abs_eq_natAbs]
  rfl

theorem le_left_of_norm (m n : ℤ) : n ≤ ‖![n, m]‖ := by
  apply le_trans _ (abs_le_left_of_norm m n)
  norm_cast
  exact le_abs_self n

theorem abs_le_right_of_norm (m n : ℤ) : |m| ≤ ‖![n, m]‖ := by
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Nat.cast_max, le_sup_iff]
  right
  rw [Int.abs_eq_natAbs]
  rfl

theorem le_right_of_norm (m n : ℤ) : m ≤ ‖![n, m]‖ := by
  apply le_trans _ (abs_le_right_of_norm m n)
  norm_cast
  exact le_abs_self m

section bounding_functions

/-- Auxiliary function used for bounding Eisenstein series, defined as
  `z.im ^ 2 / (z.re ^ 2 + z.im ^ 2)`. -/
def r1 : ℝ := z.im ^ 2 / (z.re ^ 2 + z.im ^ 2)

lemma r1_eq : r1 z = 1 / ((z.re / z.im) ^ 2 + 1) := by
  rw [div_pow, div_add_one (by positivity), one_div_div, r1]

lemma r1_pos : 0 < r1 z := by
  dsimp only [r1]
  positivity

/-- For `c, d ∈ ℝ` with `1 ≤ d ^ 2`, we have `r1 z ≤ |c * z + d| ^ 2`. -/
lemma r1_aux_bound (c : ℝ) {d : ℝ} (hd : 1 ≤ d ^ 2) :
    r1 z ≤ (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by
  have H1 : (c * z.re + d) ^ 2 + (c * z.im) ^ 2 =
    c ^ 2 * (z.re ^ 2 + z.im ^ 2) + d * 2 * c * z.re + d ^ 2 := by ring
  have H2 : (c ^ 2 * (z.re ^ 2 + z.im ^ 2) + d * 2 * c * z.re + d ^ 2) * (z.re ^ 2 + z.im ^ 2)
    - z.im ^ 2 = (c * (z.re ^ 2 + z.im ^ 2) + d * z.re) ^ 2 + (d ^ 2 - 1) * z.im ^ 2 := by ring
  rw [r1, H1, div_le_iff₀ (by positivity), ← sub_nonneg, H2]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg _))

/-- This function is used to give an upper bound on the summands in Eisenstein series; it is
defined by `z ↦ min z.im √(z.im ^ 2 / (z.re ^ 2 + z.im ^ 2))`. -/
def r : ℝ := min z.im √(r1 z)

lemma r_pos : 0 < r z := by
  simp only [r, lt_min_iff, im_pos, Real.sqrt_pos, r1_pos, and_self]

lemma r_lower_bound_on_verticalStrip {A B : ℝ} (h : 0 < B) (hz : z ∈ verticalStrip A B) :
    r ⟨⟨A, B⟩, h⟩ ≤ r z := by
  apply min_le_min hz.2
  rw [Real.sqrt_le_sqrt_iff (by apply (r1_pos z).le)]
  simp only [r1_eq, div_pow, one_div]
  rw [inv_le_inv₀ (by positivity) (by positivity), add_le_add_iff_right, ← even_two.pow_abs]
  gcongr
  exacts [hz.1, hz.2]

lemma auxbound1 {c : ℝ} (d : ℝ) (hc : 1 ≤ c ^ 2) : r z ≤ ‖c * (z : ℂ) + d‖ := by
  rcases z with ⟨z, hz⟩
  have H1 : z.im ≤ √((c * z.re + d) ^ 2 + (c * z).im ^ 2) := by
    rw [Real.le_sqrt' hz, im_ofReal_mul, mul_pow]
    exact (le_mul_of_one_le_left (sq_nonneg _) hc).trans <| le_add_of_nonneg_left (sq_nonneg _)
  simpa only [r, norm_def, normSq_apply, add_re, re_ofReal_mul, coe_re, ← pow_two, add_im, mul_im,
    coe_im, ofReal_im, zero_mul, add_zero, min_le_iff] using Or.inl H1

lemma auxbound2 (c : ℝ) {d : ℝ} (hd : 1 ≤ d ^ 2) : r z ≤ ‖c * (z : ℂ) + d‖ := by
  have H1 : √(r1 z) ≤ √((c * z.re + d) ^ 2 + (c * z.im) ^ 2) :=
    (Real.sqrt_le_sqrt_iff (by positivity)).mpr (r1_aux_bound _ _ hd)
  simpa only [r, norm_def, normSq_apply, add_re, re_ofReal_mul, coe_re, ofReal_re, ← pow_two,
    add_im, im_ofReal_mul, coe_im, ofReal_im, add_zero, min_le_iff] using Or.inr H1

lemma div_max_sq_ge_one (x : Fin 2 → ℤ) (hx : x ≠ 0) :
    1 ≤ (x 0 / ‖x‖) ^ 2 ∨ 1 ≤ (x 1 / ‖x‖) ^ 2 := by
  refine (max_choice (x 0).natAbs (x 1).natAbs).imp (fun H0 ↦ ?_) (fun H1 ↦ ?_)
  · have : x 0 ≠ 0 := by
      rwa [← norm_ne_zero_iff, norm_eq_max_natAbs, H0, Nat.cast_ne_zero, Int.natAbs_ne_zero] at hx
    simp only [norm_eq_max_natAbs, H0, Int.cast_natAbs, Int.cast_abs, div_pow, sq_abs, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Int.cast_eq_zero, this, div_self,
      le_refl]
  · have : x 1 ≠ 0 := by
      rwa [← norm_ne_zero_iff, norm_eq_max_natAbs, H1, Nat.cast_ne_zero, Int.natAbs_ne_zero] at hx
    simp only [norm_eq_max_natAbs, H1, Int.cast_natAbs, Int.cast_abs, div_pow, sq_abs, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Int.cast_eq_zero, this, div_self,
      le_refl]

lemma r_mul_max_le {x : Fin 2 → ℤ} (hx : x ≠ 0) : r z * ‖x‖ ≤ ‖x 0 * (z : ℂ) + x 1‖ := by
  have hn0 : ‖x‖ ≠ 0 := by rwa [norm_ne_zero_iff]
  have h11 : x 0 * (z : ℂ) + x 1 = (x 0 / ‖x‖ * z + x 1 / ‖x‖) * ‖x‖ := by
    rw [div_mul_eq_mul_div, ← add_div, div_mul_cancel₀ _ (mod_cast hn0)]
  rw [norm_eq_max_natAbs, h11, norm_mul, norm_real, norm_norm, norm_eq_max_natAbs]
  gcongr
  · rcases div_max_sq_ge_one x hx with H1 | H2
    · simpa only [norm_eq_max_natAbs, ofReal_div, ofReal_intCast] using auxbound1 z (x 1 / ‖x‖) H1
    · simpa only [norm_eq_max_natAbs, ofReal_div, ofReal_intCast] using auxbound2 z (x 0 / ‖x‖) H2

/-- Upper bound for the summand `|c * z + d| ^ (-k)`, as a product of a function of `z` and a
function of `c, d`. -/
lemma summand_bound {k : ℝ} (hk : 0 ≤ k) (x : Fin 2 → ℤ) :
    ‖x 0 * (z : ℂ) + x 1‖ ^ (-k) ≤ (r z) ^ (-k) * ‖x‖ ^ (-k) := by
  by_cases hx : x = 0
  · simp only [hx, Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, norm_zero]
    by_cases h : -k = 0
    · rw [h, Real.rpow_zero, Real.rpow_zero, one_mul]
    · rw [Real.zero_rpow h, mul_zero]
  · rw [← Real.mul_rpow (r_pos _).le (norm_nonneg _)]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos (r_pos _) (norm_pos_iff.mpr hx)) (r_mul_max_le z hx)
      (neg_nonpos.mpr hk)

variable {z} in
lemma summand_bound_of_mem_verticalStrip {k : ℝ} (hk : 0 ≤ k) (x : Fin 2 → ℤ)
    {A B : ℝ} (hB : 0 < B) (hz : z ∈ verticalStrip A B) :
    ‖x 0 * (z : ℂ) + x 1‖ ^ (-k) ≤ r ⟨⟨A, B⟩, hB⟩ ^ (-k) * ‖x‖ ^ (-k) := by
  refine (summand_bound z hk x).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact Real.rpow_le_rpow_of_nonpos (r_pos _) (r_lower_bound_on_verticalStrip z hB hz)
    (neg_nonpos.mpr hk)

lemma Eis_isBigO (m : ℤ) (z : ℍ) : (fun (n : ℤ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    (fun n => ((r z * ‖![n, m]‖))⁻¹) := by
    rw [Asymptotics.isBigO_iff']
    refine ⟨1, Real.zero_lt_one, ?_⟩
    filter_upwards with n
    have := EisensteinSeries.summand_bound z (k := 1) (by norm_num) ![m, n]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Real.rpow_neg_one, norm_inv, Nat.succ_eq_add_one, Nat.reduceAdd, mul_inv_rev, norm_mul,
      norm_norm, Real.norm_eq_abs, one_mul, ge_iff_le] at *
    apply le_trans this
    rw [abs_norm, mul_comm, show |r z| = r z by rw [abs_eq_self];  exact (r_pos z).le, norm_symm]

lemma linear_bigO2 (m : ℤ) (z : ℍ) : (fun (n : ℤ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    fun n => ((n : ℝ)⁻¹)  := by
  have h1 := Eis_isBigO m z
  apply  Asymptotics.IsBigO.trans h1
  rw [@Asymptotics.isBigO_iff']
  refine ⟨|(r z)|⁻¹, by simp [ne_of_gt (r_pos z)], ?_⟩
  rw [eventually_iff_exists_mem]
  refine ⟨{0}ᶜ, Set.Finite.compl_mem_cofinite (Set.finite_singleton 0), ?_⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Nat.succ_eq_add_one, Nat.reduceAdd,
    mul_inv_rev, norm_mul, norm_inv, norm_norm, Real.norm_eq_abs, abs_norm]
  intro n hn
  rw [mul_comm]
  gcongr
  simpa using abs_le_left_of_norm m n

lemma linear_bigO (m : ℤ) (z : ℍ) : (fun (n : ℤ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    fun n => (|(n : ℝ)|⁻¹)  := by
  have := Asymptotics.IsBigO.abs_right (linear_bigO2 m z)
  simp_rw [abs_inv] at this
  exact this

lemma linear_bigO_pow (m : ℤ) (z : ℍ) (k : ℕ) :
    (fun (n : ℤ) => ((((m : ℂ) * z + n)) ^ k )⁻¹) =O[cofinite] fun n => ((|(n : ℝ)| ^ k)⁻¹)  := by
  simp_rw [← inv_pow]
  apply Asymptotics.IsBigO.pow
  apply linear_bigO m z


lemma summable_hammerTime  {α : Type} [NormedField α] [CompleteSpace α] (f  : ℤ → α) (a : ℝ)
    (hab : 1 < a) (hf : (fun n => (f n)⁻¹) =O[cofinite] fun n => (|(n : ℝ)| ^ (a : ℝ))⁻¹) :
    Summable fun n => (f n)⁻¹ := by
  apply summable_of_isBigO _ hf
  have := Real.summable_abs_int_rpow hab
  apply this.congr
  intro b
  refine Real.rpow_neg ?_ a
  exact abs_nonneg (b : ℝ)

lemma G2_summable_aux (n : ℤ) (z : ℍ) (k : ℤ) (hk : 2 ≤ k) :
    Summable fun d : ℤ => ((((n : ℂ) * z) + d) ^ k)⁻¹ := by
  apply summable_hammerTime _ k
  · norm_cast
  · lift k to ℕ using (by linarith)
    have := linear_bigO_pow n z k
    norm_cast at *

lemma Asymptotics.IsBigO.map {α β ι γ : Type*} [Norm α] [Norm β] {f : ι → α} {g : ι → β}
  {p : Filter ι} (hf : f =O[p] g) (c : γ → ι)  :
    (fun (n : γ) => f (c n)) =O[p.comap c] fun n => g (c n) := by
  rw [Asymptotics.isBigO_iff ] at *
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, ?_⟩
  simp only [eventually_comap] at *
  filter_upwards [hC] with n hn
  exact fun a ha ↦ Eq.mpr (id (congrArg (fun _a ↦ ‖f _a‖ ≤ C * ‖g _a‖) ha)) hn

lemma Asymptotics.IsBigO.nat_of_int {α β: Type*} [Norm α] [SeminormedAddCommGroup β] {f : ℤ → α}
    {g : ℤ → β}  (hf : f =O[cofinite] g) :   (fun (n : ℕ) => f n) =O[cofinite] fun n => g n := by
  have := Asymptotics.IsBigO.map hf Nat.cast
  simp only [Int.cofinite_eq, isBigO_sup, comap_sup, Asymptotics.isBigO_sup] at *
  rw [Nat.cofinite_eq_atTop]
  simpa using this.2

end bounding_functions

section summability

/-- The function `ℤ ^ 2 → ℝ` given by `x ↦ ‖x‖ ^ (-k)` is summable if `2 < k`. We prove this by
splitting into boxes using `Finset.box`. -/
lemma summable_one_div_norm_rpow {k : ℝ} (hk : 2 < k) :
    Summable fun (x : Fin 2 → ℤ) ↦ ‖x‖ ^ (-k) := by
  rw [← (finTwoArrowEquiv _).symm.summable_iff, summable_partition _ Int.existsUnique_mem_box]
  · simp only [finTwoArrowEquiv_symm_apply, Function.comp_def]
    refine ⟨fun n ↦ (hasSum_fintype (β := box (α := ℤ × ℤ) n) _).summable, ?_⟩
    suffices Summable fun n : ℕ ↦ ∑' (_ : box (α := ℤ × ℤ) n), (n : ℝ) ^ (-k) by
      refine this.congr fun n ↦ tsum_congr fun p ↦ ?_
      simp only [← Int.mem_box.mp p.2, Nat.cast_max, norm_eq_max_natAbs, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]
    simp only [tsum_fintype, univ_eq_attach, sum_const, card_attach, nsmul_eq_mul]
    apply ((Real.summable_nat_rpow.mpr (by linarith : 1 - k < -1)).mul_left
      8).of_norm_bounded_eventually_nat
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    rw [Int.card_box hn.ne', Real.norm_of_nonneg (by positivity), sub_eq_add_neg,
      Real.rpow_add (Nat.cast_pos.mpr hn), Real.rpow_one, Nat.cast_mul, Nat.cast_ofNat, mul_assoc]
  · exact fun n ↦ Real.rpow_nonneg (norm_nonneg _) _

/-- The sum defining the Eisenstein series (of weight `k` and level `Γ(N)` with congruence
condition `a : Fin 2 → ZMod N`) converges locally uniformly on `ℍ`. -/
theorem eisensteinSeries_tendstoLocallyUniformly {k : ℤ} (hk : 3 ≤ k) {N : ℕ} (a : Fin 2 → ZMod N) :
    TendstoLocallyUniformly (fun (s : Finset (gammaSet N a)) ↦ (∑ x ∈ s, eisSummand k x ·))
      (eisensteinSeries a k ·) Filter.atTop := by
  have hk' : (2 : ℝ) < k := by norm_cast
  have p_sum : Summable fun x : gammaSet N a ↦ ‖x.val‖ ^ (-k) :=
    mod_cast (summable_one_div_norm_rpow hk').subtype (gammaSet N a)
  simp only [tendstoLocallyUniformly_iff_forall_isCompact, eisensteinSeries]
  intro K hK
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact hK
  refine (tendstoUniformlyOn_tsum (hu := p_sum.mul_left <| r ⟨⟨A, B⟩, hB⟩ ^ (-k : ℝ))
    (fun p z hz ↦ ?_)).mono HABK
  simpa only [eisSummand, one_div, ← zpow_neg, norm_zpow, ← Real.rpow_intCast,
    Int.cast_neg] using summand_bound_of_mem_verticalStrip (by positivity) p hB hz

/-- Variant of `eisensteinSeries_tendstoLocallyUniformly` formulated with maps `ℂ → ℂ`, which is
nice to have for holomorphicity later. -/
lemma eisensteinSeries_tendstoLocallyUniformlyOn {k : ℤ} {N : ℕ} (hk : 3 ≤ k)
    (a : Fin 2 → ZMod N) : TendstoLocallyUniformlyOn (fun (s : Finset (gammaSet N a )) ↦
      ↑ₕ(fun (z : ℍ) ↦ ∑ x ∈ s, eisSummand k x z)) (↑ₕ(eisensteinSeries_SIF a k).toFun)
          Filter.atTop {z : ℂ | 0 < z.im} := by
  rw [← Subtype.coe_image_univ {z : ℂ | 0 < z.im}]
  apply TendstoLocallyUniformlyOn.comp (s := ⊤) _ _ _ (PartialHomeomorph.continuousOn_symm _)
  · simp only [SlashInvariantForm.toFun_eq_coe, Set.top_eq_univ, tendstoLocallyUniformlyOn_univ]
    apply eisensteinSeries_tendstoLocallyUniformly hk
  · simp only [IsOpenEmbedding.toPartialHomeomorph_target, Set.top_eq_univ, mapsTo_range_iff,
    Set.mem_univ, forall_const]

end summability

end EisensteinSeries
