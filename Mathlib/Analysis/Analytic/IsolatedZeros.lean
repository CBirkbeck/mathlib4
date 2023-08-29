/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Dslope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Analytic.Uniqueness

#align_import analysis.analytic.isolated_zeros from "leanprover-community/mathlib"@"a3209ddf94136d36e5e5c624b10b2a347cc9d090"

/-!
# Principle of isolated zeros

This file proves the fact that the zeros of a non-constant analytic function of one variable are
isolated. It also introduces a little bit of API in the `HasFPowerSeriesAt` namespace that is
useful in this setup.

## Main results

* `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` is the main statement that if a function is
  analytic at `z₀`, then either it is identically zero in a neighborhood of `z₀`, or it does not
  vanish in a punctured neighborhood of `z₀`.
* `AnalyticOn.eqOn_of_preconnected_of_frequently_eq` is the identity theorem for analytic
  functions: if a function `f` is analytic on a connected set `U` and is zero on a set with an
  accumulation point in `U` then `f` is identically `0` on `U`.
-/


open scoped Classical

open Filter Function Nat FormalMultilinearSeries EMetric Set

open scoped Topology BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {s : E} {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → E} {n : ℕ} {z z₀ : 𝕜}
--  {y : Fin n → 𝕜} -- Porting note: This is used nowhere and creates problem since it is sometimes
-- automatically included as a hypothesis

namespace HasSum

variable {a : ℕ → E}

theorem hasSum_at_zero (a : ℕ → E) : HasSum (fun n => (0 : 𝕜) ^ n • a n) (a 0) := by
  convert hasSum_single (α := E) 0 fun b h => _ <;>
  -- ⊢ a 0 = 0 ^ 0 • a 0
    first
    | simp [Nat.pos_of_ne_zero h]
    | simp
#align has_sum.has_sum_at_zero HasSum.hasSum_at_zero

theorem exists_hasSum_smul_of_apply_eq_zero (hs : HasSum (fun m => z ^ m • a m) s)
    (ha : ∀ k < n, a k = 0) : ∃ t : E, z ^ n • t = s ∧ HasSum (fun m => z ^ m • a (m + n)) t := by
  obtain rfl | hn := n.eq_zero_or_pos
  -- ⊢ ∃ t, z ^ 0 • t = s ∧ HasSum (fun m => z ^ m • a (m + 0)) t
  · simpa
    -- 🎉 no goals
  by_cases h : z = 0
  -- ⊢ ∃ t, z ^ n • t = s ∧ HasSum (fun m => z ^ m • a (m + n)) t
  · have : s = 0 := hs.unique (by simpa [ha 0 hn, h] using hasSum_at_zero a)
    -- ⊢ ∃ t, z ^ n • t = s ∧ HasSum (fun m => z ^ m • a (m + n)) t
    exact ⟨a n, by simp [h, hn, this], by simpa [h] using hasSum_at_zero fun m => a (m + n)⟩
    -- 🎉 no goals
  · refine ⟨(z ^ n)⁻¹ • s, by field_simp [smul_smul], ?_⟩
    -- ⊢ HasSum (fun m => z ^ m • a (m + n)) ((z ^ n)⁻¹ • s)
    have h1 : ∑ i in Finset.range n, z ^ i • a i = 0 :=
      Finset.sum_eq_zero fun k hk => by simp [ha k (Finset.mem_range.mp hk)]
    have h2 : HasSum (fun m => z ^ (m + n) • a (m + n)) s := by
      simpa [h1] using (hasSum_nat_add_iff' n).mpr hs
    convert h2.const_smul (z⁻¹ ^ n) using 1
    -- ⊢ (fun m => z ^ m • a (m + n)) = fun i => z⁻¹ ^ n • z ^ (i + n) • a (i + n)
    · field_simp [pow_add, smul_smul]
      -- 🎉 no goals
    · simp only [inv_pow]
      -- 🎉 no goals
#align has_sum.exists_has_sum_smul_of_apply_eq_zero HasSum.exists_hasSum_smul_of_apply_eq_zero

end HasSum

namespace HasFPowerSeriesAt

theorem has_fpower_series_dslope_fslope (hp : HasFPowerSeriesAt f p z₀) :
    HasFPowerSeriesAt (dslope f z₀) p.fslope z₀ := by
  have hpd : deriv f z₀ = p.coeff 1 := hp.deriv
  -- ⊢ HasFPowerSeriesAt (dslope f z₀) (fslope p) z₀
  have hp0 : p.coeff 0 = f z₀ := hp.coeff_zero 1
  -- ⊢ HasFPowerSeriesAt (dslope f z₀) (fslope p) z₀
  simp only [hasFPowerSeriesAt_iff, apply_eq_pow_smul_coeff, coeff_fslope] at hp ⊢
  -- ⊢ ∀ᶠ (z : 𝕜) in 𝓝 0, HasSum (fun n => z ^ n • coeff p (n + 1)) (dslope f z₀ (z …
  refine hp.mono fun x hx => ?_
  -- ⊢ HasSum (fun n => x ^ n • coeff p (n + 1)) (dslope f z₀ (z₀ + x))
  by_cases h : x = 0
  -- ⊢ HasSum (fun n => x ^ n • coeff p (n + 1)) (dslope f z₀ (z₀ + x))
  · convert hasSum_single (α := E) 0 _ <;> intros <;> simp [*]
    -- ⊢ dslope f z₀ (z₀ + x) = x ^ 0 • coeff p (0 + 1)
                                           -- ⊢ dslope f z₀ (z₀ + x) = x ^ 0 • coeff p (0 + 1)
                                           -- ⊢ x ^ b'✝ • coeff p (b'✝ + 1) = 0
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
  · have hxx : ∀ n : ℕ, x⁻¹ * x ^ (n + 1) = x ^ n := fun n => by field_simp [h, _root_.pow_succ']
    -- ⊢ HasSum (fun n => x ^ n • coeff p (n + 1)) (dslope f z₀ (z₀ + x))
    suffices HasSum (fun n => x⁻¹ • x ^ (n + 1) • p.coeff (n + 1)) (x⁻¹ • (f (z₀ + x) - f z₀)) by
      simpa [dslope, slope, h, smul_smul, hxx] using this
    · simpa [hp0] using ((hasSum_nat_add_iff' 1).mpr hx).const_smul x⁻¹
      -- 🎉 no goals
#align has_fpower_series_at.has_fpower_series_dslope_fslope HasFPowerSeriesAt.has_fpower_series_dslope_fslope

theorem has_fpower_series_iterate_dslope_fslope (n : ℕ) (hp : HasFPowerSeriesAt f p z₀) :
    HasFPowerSeriesAt ((swap dslope z₀)^[n] f) (fslope^[n] p) z₀ := by
  induction' n with n ih generalizing f p
  -- ⊢ HasFPowerSeriesAt ((swap dslope z₀)^[zero] f) (fslope^[zero] p) z₀
  · exact hp
    -- 🎉 no goals
  · simpa using ih (has_fpower_series_dslope_fslope hp)
    -- 🎉 no goals
#align has_fpower_series_at.has_fpower_series_iterate_dslope_fslope HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope

theorem iterate_dslope_fslope_ne_zero (hp : HasFPowerSeriesAt f p z₀) (h : p ≠ 0) :
    (swap dslope z₀)^[p.order] f z₀ ≠ 0 := by
  rw [← coeff_zero (has_fpower_series_iterate_dslope_fslope p.order hp) 1]
  -- ⊢ ↑(fslope^[order p] p 0) 1 ≠ 0
  simpa [coeff_eq_zero] using apply_order_ne_zero h
  -- 🎉 no goals
#align has_fpower_series_at.iterate_dslope_fslope_ne_zero HasFPowerSeriesAt.iterate_dslope_fslope_ne_zero

theorem eq_pow_order_mul_iterate_dslope (hp : HasFPowerSeriesAt f p z₀) :
    ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ p.order • (swap dslope z₀)^[p.order] f z := by
  have hq := hasFPowerSeriesAt_iff'.mp (has_fpower_series_iterate_dslope_fslope p.order hp)
  -- ⊢ ∀ᶠ (z : 𝕜) in 𝓝 z₀, f z = (z - z₀) ^ order p • (swap dslope z₀)^[order p] f z
  filter_upwards [hq, hasFPowerSeriesAt_iff'.mp hp] with x hx1 hx2
  -- ⊢ f x = (x - z₀) ^ order p • (swap dslope z₀)^[order p] f x
  have : ∀ k < p.order, p.coeff k = 0 := fun k hk => by
    simpa [coeff_eq_zero] using apply_eq_zero_of_lt_order hk
  obtain ⟨s, hs1, hs2⟩ := HasSum.exists_hasSum_smul_of_apply_eq_zero hx2 this
  -- ⊢ f x = (x - z₀) ^ order p • (swap dslope z₀)^[order p] f x
  convert hs1.symm
  -- ⊢ (swap dslope z₀)^[order p] f x = s
  simp only [coeff_iterate_fslope] at hx1
  -- ⊢ (swap dslope z₀)^[order p] f x = s
  exact hx1.unique hs2
  -- 🎉 no goals
#align has_fpower_series_at.eq_pow_order_mul_iterate_dslope HasFPowerSeriesAt.eq_pow_order_mul_iterate_dslope

theorem locally_ne_zero (hp : HasFPowerSeriesAt f p z₀) (h : p ≠ 0) : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 := by
  rw [eventually_nhdsWithin_iff]
  -- ⊢ ∀ᶠ (x : 𝕜) in 𝓝 z₀, x ∈ {z₀}ᶜ → f x ≠ 0
  have h2 := (has_fpower_series_iterate_dslope_fslope p.order hp).continuousAt
  -- ⊢ ∀ᶠ (x : 𝕜) in 𝓝 z₀, x ∈ {z₀}ᶜ → f x ≠ 0
  have h3 := h2.eventually_ne (iterate_dslope_fslope_ne_zero hp h)
  -- ⊢ ∀ᶠ (x : 𝕜) in 𝓝 z₀, x ∈ {z₀}ᶜ → f x ≠ 0
  filter_upwards [eq_pow_order_mul_iterate_dslope hp, h3] with z e1 e2 e3
  -- ⊢ f z ≠ 0
  simpa [e1, e2, e3] using pow_ne_zero p.order (sub_ne_zero.mpr e3)
  -- 🎉 no goals
#align has_fpower_series_at.locally_ne_zero HasFPowerSeriesAt.locally_ne_zero

theorem locally_zero_iff (hp : HasFPowerSeriesAt f p z₀) : (∀ᶠ z in 𝓝 z₀, f z = 0) ↔ p = 0 :=
  ⟨fun hf => hp.eq_zero_of_eventually hf, fun h => eventually_eq_zero (by rwa [h] at hp )⟩
                                                                          -- 🎉 no goals
#align has_fpower_series_at.locally_zero_iff HasFPowerSeriesAt.locally_zero_iff

end HasFPowerSeriesAt

namespace AnalyticAt

/-- The *principle of isolated zeros* for an analytic function, local version: if a function is
analytic at `z₀`, then either it is identically zero in a neighborhood of `z₀`, or it does not
vanish in a punctured neighborhood of `z₀`. -/
theorem eventually_eq_zero_or_eventually_ne_zero (hf : AnalyticAt 𝕜 f z₀) :
    (∀ᶠ z in 𝓝 z₀, f z = 0) ∨ ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 := by
  rcases hf with ⟨p, hp⟩
  -- ⊢ (∀ᶠ (z : 𝕜) in 𝓝 z₀, f z = 0) ∨ ∀ᶠ (z : 𝕜) in 𝓝[{z₀}ᶜ] z₀, f z ≠ 0
  by_cases h : p = 0
  -- ⊢ (∀ᶠ (z : 𝕜) in 𝓝 z₀, f z = 0) ∨ ∀ᶠ (z : 𝕜) in 𝓝[{z₀}ᶜ] z₀, f z ≠ 0
  · exact Or.inl (HasFPowerSeriesAt.eventually_eq_zero (by rwa [h] at hp ))
    -- 🎉 no goals
  · exact Or.inr (hp.locally_ne_zero h)
    -- 🎉 no goals
#align analytic_at.eventually_eq_zero_or_eventually_ne_zero AnalyticAt.eventually_eq_zero_or_eventually_ne_zero

theorem eventually_eq_or_eventually_ne (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    (∀ᶠ z in 𝓝 z₀, f z = g z) ∨ ∀ᶠ z in 𝓝[≠] z₀, f z ≠ g z := by
  simpa [sub_eq_zero] using (hf.sub hg).eventually_eq_zero_or_eventually_ne_zero
  -- 🎉 no goals
#align analytic_at.eventually_eq_or_eventually_ne AnalyticAt.eventually_eq_or_eventually_ne

theorem frequently_zero_iff_eventually_zero {f : 𝕜 → E} {w : 𝕜} (hf : AnalyticAt 𝕜 f w) :
    (∃ᶠ z in 𝓝[≠] w, f z = 0) ↔ ∀ᶠ z in 𝓝 w, f z = 0 :=
  ⟨hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right, fun h =>
    (h.filter_mono nhdsWithin_le_nhds).frequently⟩
#align analytic_at.frequently_zero_iff_eventually_zero AnalyticAt.frequently_zero_iff_eventually_zero

theorem frequently_eq_iff_eventually_eq (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    (∃ᶠ z in 𝓝[≠] z₀, f z = g z) ↔ ∀ᶠ z in 𝓝 z₀, f z = g z := by
  simpa [sub_eq_zero] using frequently_zero_iff_eventually_zero (hf.sub hg)
  -- 🎉 no goals
#align analytic_at.frequently_eq_iff_eventually_eq AnalyticAt.frequently_eq_iff_eventually_eq

end AnalyticAt

namespace AnalyticOn

variable {U : Set 𝕜}

/-- The *principle of isolated zeros* for an analytic function, global version: if a function is
analytic on a connected set `U` and vanishes in arbitrary neighborhoods of a point `z₀ ∈ U`, then
it is identically zero in `U`.
For higher-dimensional versions requiring that the function vanishes in a neighborhood of `z₀`,
see `AnalyticOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero`. -/
theorem eqOn_zero_of_preconnected_of_frequently_eq_zero (hf : AnalyticOn 𝕜 f U)
    (hU : IsPreconnected U) (h₀ : z₀ ∈ U) (hfw : ∃ᶠ z in 𝓝[≠] z₀, f z = 0) : EqOn f 0 U :=
  hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h₀
    ((hf z₀ h₀).frequently_zero_iff_eventually_zero.1 hfw)
#align analytic_on.eq_on_zero_of_preconnected_of_frequently_eq_zero AnalyticOn.eqOn_zero_of_preconnected_of_frequently_eq_zero

theorem eqOn_zero_of_preconnected_of_mem_closure (hf : AnalyticOn 𝕜 f U) (hU : IsPreconnected U)
    (h₀ : z₀ ∈ U) (hfz₀ : z₀ ∈ closure ({z | f z = 0} \ {z₀})) : EqOn f 0 U :=
  hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU h₀
    (mem_closure_ne_iff_frequently_within.mp hfz₀)
#align analytic_on.eq_on_zero_of_preconnected_of_mem_closure AnalyticOn.eqOn_zero_of_preconnected_of_mem_closure

/-- The *identity principle* for analytic functions, global version: if two functions are
analytic on a connected set `U` and coincide at points which accumulate to a point `z₀ ∈ U`, then
they coincide globally in `U`.
For higher-dimensional versions requiring that the functions coincide in a neighborhood of `z₀`,
see `AnalyticOn.eqOn_of_preconnected_of_eventuallyEq`. -/
theorem eqOn_of_preconnected_of_frequently_eq (hf : AnalyticOn 𝕜 f U) (hg : AnalyticOn 𝕜 g U)
    (hU : IsPreconnected U) (h₀ : z₀ ∈ U) (hfg : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) : EqOn f g U := by
  have hfg' : ∃ᶠ z in 𝓝[≠] z₀, (f - g) z = 0 :=
    hfg.mono fun z h => by rw [Pi.sub_apply, h, sub_self]
  simpa [sub_eq_zero] using fun z hz =>
    (hf.sub hg).eqOn_zero_of_preconnected_of_frequently_eq_zero hU h₀ hfg' hz
#align analytic_on.eq_on_of_preconnected_of_frequently_eq AnalyticOn.eqOn_of_preconnected_of_frequently_eq

theorem eqOn_of_preconnected_of_mem_closure (hf : AnalyticOn 𝕜 f U) (hg : AnalyticOn 𝕜 g U)
    (hU : IsPreconnected U) (h₀ : z₀ ∈ U) (hfg : z₀ ∈ closure ({z | f z = g z} \ {z₀})) :
    EqOn f g U :=
  hf.eqOn_of_preconnected_of_frequently_eq hg hU h₀ (mem_closure_ne_iff_frequently_within.mp hfg)
#align analytic_on.eq_on_of_preconnected_of_mem_closure AnalyticOn.eqOn_of_preconnected_of_mem_closure

/-- The *identity principle* for analytic functions, global version: if two functions on a normed
field `𝕜` are analytic everywhere and coincide at points which accumulate to a point `z₀`, then
they coincide globally.
For higher-dimensional versions requiring that the functions coincide in a neighborhood of `z₀`,
see `AnalyticOn.eq_of_eventuallyEq`. -/
theorem eq_of_frequently_eq [ConnectedSpace 𝕜] (hf : AnalyticOn 𝕜 f univ) (hg : AnalyticOn 𝕜 g univ)
    (hfg : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) : f = g :=
  funext fun x =>
    eqOn_of_preconnected_of_frequently_eq hf hg isPreconnected_univ (mem_univ z₀) hfg (mem_univ x)
#align analytic_on.eq_of_frequently_eq AnalyticOn.eq_of_frequently_eq

end AnalyticOn
