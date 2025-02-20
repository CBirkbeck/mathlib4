/-
Copyright (c) 2023 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.CPolynomialDef

/-! # Properties of continuously polynomial functions

We expand the API around continuously polynomial functions. Notably, we show that this class is
stable under the usual operations (addition, subtraction, negation).

We also prove that continuous multilinear maps are continuously polynomial, and so
are continuous linear maps into continuous multilinear maps. In particular, such maps are
analytic.
-/

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open scoped Topology
open Set Filter Asymptotics NNReal ENNReal

variable {f g : E → F} {p pf pg : FormalMultilinearSeries 𝕜 E F} {x : E} {r r' : ℝ≥0∞} {n m : ℕ}

section FiniteFPowerSeries

/-- Given a function `f : E → F`, a formal multilinear series `p` and `n : ℕ`, we say that
`f` has `p` as a finite power series on the ball of radius `r > 0` around `x` if
`f (x + y) = ∑' pₘ yᵐ` for all `‖y‖ < r` and `pₙ = 0` for `n ≤ m`. -/
structure HasFiniteFPowerSeriesOnBall (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E)
    (n : ℕ) (r : ℝ≥0∞) : Prop extends HasFPowerSeriesOnBall f p x r where
  finite : ∀ (m : ℕ), n ≤ m → p m = 0

theorem HasFiniteFPowerSeriesOnBall.mk' {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    {n : ℕ} {r : ℝ≥0∞} (finite : ∀ (m : ℕ), n ≤ m → p m = 0) (pos : 0 < r)
    (sum_eq : ∀ y ∈ EMetric.ball 0 r, (∑ i ∈ Finset.range n, p i fun _ ↦ y) = f (x + y)) :
    HasFiniteFPowerSeriesOnBall f p x n r where
  r_le := p.radius_eq_top_of_eventually_eq_zero (Filter.eventually_atTop.mpr ⟨n, finite⟩) ▸ le_top
  r_pos := pos
  hasSum hy := sum_eq _ hy ▸ hasSum_sum_of_ne_finset_zero fun m hm ↦ by
    rw [Finset.mem_range, not_lt] at hm; rw [finite m hm]; rfl
  finite := finite

/-- Given a function `f : E → F`, a formal multilinear series `p` and `n : ℕ`, we say that
`f` has `p` as a finite power series around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `y` in a
neighborhood of `0`and `pₙ = 0` for `n ≤ m`. -/
def HasFiniteFPowerSeriesAt (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) (n : ℕ) :=
  ∃ r, HasFiniteFPowerSeriesOnBall f p x n r

theorem HasFiniteFPowerSeriesAt.toHasFPowerSeriesAt
    (hf : HasFiniteFPowerSeriesAt f p x n) : HasFPowerSeriesAt f p x :=
  let ⟨r, hf⟩ := hf
  ⟨r, hf.toHasFPowerSeriesOnBall⟩

theorem HasFiniteFPowerSeriesAt.finite (hf : HasFiniteFPowerSeriesAt f p x n) :
    ∀ m : ℕ, n ≤ m → p m = 0 := let ⟨_, hf⟩ := hf; hf.finite

variable (𝕜)

/-- Given a function `f : E → F`, we say that `f` is continuously polynomial (cpolynomial)
at `x` if it admits a finite power series expansion around `x`. -/
def CPolynomialAt (f : E → F) (x : E) :=
  ∃ (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ), HasFiniteFPowerSeriesAt f p x n

/-- Given a function `f : E → F`, we say that `f` is continuously polynomial on a set `s`
if it is continuously polynomial around every point of `s`. -/
def CPolynomialOn (f : E → F) (s : Set E) :=
  ∀ x, x ∈ s → CPolynomialAt 𝕜 f x

variable {𝕜}

theorem HasFiniteFPowerSeriesOnBall.hasFiniteFPowerSeriesAt
    (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    HasFiniteFPowerSeriesAt f p x n :=
  ⟨r, hf⟩

theorem HasFiniteFPowerSeriesAt.cPolynomialAt (hf : HasFiniteFPowerSeriesAt f p x n) :
    CPolynomialAt 𝕜 f x :=
  ⟨p, n, hf⟩

theorem HasFiniteFPowerSeriesOnBall.cPolynomialAt (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    CPolynomialAt 𝕜 f x :=
  hf.hasFiniteFPowerSeriesAt.cPolynomialAt

theorem CPolynomialAt.analyticAt (hf : CPolynomialAt 𝕜 f x) : AnalyticAt 𝕜 f x :=
  let ⟨p, _, hp⟩ := hf
  ⟨p, hp.toHasFPowerSeriesAt⟩

theorem CPolynomialAt.analyticWithinAt {s : Set E} (hf : CPolynomialAt 𝕜 f x) :
    AnalyticWithinAt 𝕜 f s x :=
  hf.analyticAt.analyticWithinAt

theorem CPolynomialOn.analyticOnNhd {s : Set E} (hf : CPolynomialOn 𝕜 f s) : AnalyticOnNhd 𝕜 f s :=
  fun x hx ↦ (hf x hx).analyticAt

theorem CPolynomialOn.analyticOn {s : Set E} (hf : CPolynomialOn 𝕜 f s) : AnalyticOn 𝕜 f s :=
  hf.analyticOnNhd.analyticOn

theorem HasFiniteFPowerSeriesOnBall.congr (hf : HasFiniteFPowerSeriesOnBall f p x n r)
    (hg : EqOn f g (EMetric.ball x r)) : HasFiniteFPowerSeriesOnBall g p x n r :=
  ⟨hf.1.congr hg, hf.finite⟩

/-- If a function `f` has a finite power series `p` around `x`, then the function
`z ↦ f (z - y)` has the same finite power series around `x + y`. -/
theorem HasFiniteFPowerSeriesOnBall.comp_sub (hf : HasFiniteFPowerSeriesOnBall f p x n r) (y : E) :
    HasFiniteFPowerSeriesOnBall (fun z => f (z - y)) p (x + y) n r :=
  ⟨hf.1.comp_sub y, hf.finite⟩

theorem HasFiniteFPowerSeriesOnBall.mono (hf : HasFiniteFPowerSeriesOnBall f p x n r)
    (r'_pos : 0 < r') (hr : r' ≤ r) : HasFiniteFPowerSeriesOnBall f p x n r' :=
  ⟨hf.1.mono r'_pos hr, hf.finite⟩

theorem HasFiniteFPowerSeriesAt.congr (hf : HasFiniteFPowerSeriesAt f p x n) (hg : f =ᶠ[𝓝 x] g) :
    HasFiniteFPowerSeriesAt g p x n :=
  Exists.imp (fun _ hg ↦ ⟨hg, hf.finite⟩) (hf.toHasFPowerSeriesAt.congr hg)

protected theorem HasFiniteFPowerSeriesAt.eventually (hf : HasFiniteFPowerSeriesAt f p x n) :
    ∀ᶠ r : ℝ≥0∞ in 𝓝[>] 0, HasFiniteFPowerSeriesOnBall f p x n r :=
  hf.toHasFPowerSeriesAt.eventually.mono fun _ h ↦ ⟨h, hf.finite⟩

theorem hasFiniteFPowerSeriesOnBall_const {c : F} {e : E} :
    HasFiniteFPowerSeriesOnBall (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e 1 ⊤ :=
  ⟨hasFPowerSeriesOnBall_const, fun n hn ↦ constFormalMultilinearSeries_apply (id hn : 0 < n).ne'⟩

theorem hasFiniteFPowerSeriesAt_const {c : F} {e : E} :
    HasFiniteFPowerSeriesAt (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e 1 :=
  ⟨⊤, hasFiniteFPowerSeriesOnBall_const⟩

theorem CPolynomialAt_const {v : F} : CPolynomialAt 𝕜 (fun _ => v) x :=
  ⟨constFormalMultilinearSeries 𝕜 E v, 1, hasFiniteFPowerSeriesAt_const⟩

theorem CPolynomialOn_const {v : F} {s : Set E} : CPolynomialOn 𝕜 (fun _ => v) s :=
  fun _ _ => CPolynomialAt_const

theorem HasFiniteFPowerSeriesOnBall.add (hf : HasFiniteFPowerSeriesOnBall f pf x n r)
    (hg : HasFiniteFPowerSeriesOnBall g pg x m r) :
    HasFiniteFPowerSeriesOnBall (f + g) (pf + pg) x (max n m) r :=
  ⟨hf.1.add hg.1, fun N hN ↦ by
    rw [Pi.add_apply, hf.finite _ ((le_max_left n m).trans hN),
        hg.finite _ ((le_max_right n m).trans hN), zero_add]⟩

theorem HasFiniteFPowerSeriesAt.add (hf : HasFiniteFPowerSeriesAt f pf x n)
    (hg : HasFiniteFPowerSeriesAt g pg x m) :
    HasFiniteFPowerSeriesAt (f + g) (pf + pg) x (max n m) := by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩

theorem CPolynomialAt.add (hf : CPolynomialAt 𝕜 f x) (hg : CPolynomialAt 𝕜 g x) :
    CPolynomialAt 𝕜 (f + g) x :=
  let ⟨_, _, hpf⟩ := hf
  let ⟨_, _, hqf⟩ := hg
  (hpf.add hqf).cPolynomialAt

theorem HasFiniteFPowerSeriesOnBall.neg (hf : HasFiniteFPowerSeriesOnBall f pf x n r) :
    HasFiniteFPowerSeriesOnBall (-f) (-pf) x n r :=
  ⟨hf.1.neg, fun m hm ↦ by rw [Pi.neg_apply, hf.finite m hm, neg_zero]⟩

theorem HasFiniteFPowerSeriesAt.neg (hf : HasFiniteFPowerSeriesAt f pf x n) :
    HasFiniteFPowerSeriesAt (-f) (-pf) x n :=
  let ⟨_, hrf⟩ := hf
  hrf.neg.hasFiniteFPowerSeriesAt

theorem CPolynomialAt.neg (hf : CPolynomialAt 𝕜 f x) : CPolynomialAt 𝕜 (-f) x :=
  let ⟨_, _, hpf⟩ := hf
  hpf.neg.cPolynomialAt

theorem HasFiniteFPowerSeriesOnBall.sub (hf : HasFiniteFPowerSeriesOnBall f pf x n r)
    (hg : HasFiniteFPowerSeriesOnBall g pg x m r) :
    HasFiniteFPowerSeriesOnBall (f - g) (pf - pg) x (max n m) r := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem HasFiniteFPowerSeriesAt.sub (hf : HasFiniteFPowerSeriesAt f pf x n)
    (hg : HasFiniteFPowerSeriesAt g pg x m) :
    HasFiniteFPowerSeriesAt (f - g) (pf - pg) x (max n m) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem CPolynomialAt.sub (hf : CPolynomialAt 𝕜 f x) (hg : CPolynomialAt 𝕜 g x) :
    CPolynomialAt 𝕜 (f - g) x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem CPolynomialOn.add {s : Set E} (hf : CPolynomialOn 𝕜 f s) (hg : CPolynomialOn 𝕜 g s) :
    CPolynomialOn 𝕜 (f + g) s :=
  fun z hz => (hf z hz).add (hg z hz)

theorem CPolynomialOn.sub {s : Set E} (hf : CPolynomialOn 𝕜 f s) (hg : CPolynomialOn 𝕜 g s) :
    CPolynomialOn 𝕜 (f - g) s :=
  fun z hz => (hf z hz).sub (hg z hz)


/-!
### Continuous multilinear maps

We show that continuous multilinear maps are continuously polynomial, and therefore analytic.
-/

namespace ContinuousMultilinearMap

variable {ι : Type*} {Em : ι → Type*} [∀ i, NormedAddCommGroup (Em i)] [∀ i, NormedSpace 𝕜 (Em i)]
  [Fintype ι] (f : ContinuousMultilinearMap 𝕜 Em F) {x : Π i, Em i} {s : Set (Π i, Em i)}

open FormalMultilinearSeries

protected theorem hasFiniteFPowerSeriesOnBall :
    HasFiniteFPowerSeriesOnBall f f.toFormalMultilinearSeries 0 (Fintype.card ι + 1) ⊤ :=
  .mk' (fun _ hm ↦ dif_neg (Nat.succ_le_iff.mp hm).ne) ENNReal.zero_lt_top fun y _ ↦ by
    rw [Finset.sum_eq_single_of_mem _ (Finset.self_mem_range_succ _), zero_add]
    · rw [toFormalMultilinearSeries, dif_pos rfl]; rfl
    · intro m _ ne; rw [toFormalMultilinearSeries, dif_neg ne.symm]; rfl

lemma cpolynomialAt  : CPolynomialAt 𝕜 f x :=
  f.hasFiniteFPowerSeriesOnBall.cPolynomialAt_of_mem
    (by simp only [Metric.emetric_ball_top, Set.mem_univ])

lemma cpolyomialOn : CPolynomialOn 𝕜 f s := fun _ _ ↦ f.cpolynomialAt

lemma analyticOnNhd : AnalyticOnNhd 𝕜 f s := f.cpolyomialOn.analyticOnNhd

lemma analyticOn : AnalyticOn 𝕜 f s := f.analyticOnNhd.analyticOn

@[deprecated (since := "2024-09-26")]
alias analyticWithinOn := analyticOn

lemma analyticAt : AnalyticAt 𝕜 f x := f.cpolynomialAt.analyticAt

lemma analyticWithinAt : AnalyticWithinAt 𝕜 f s x := f.analyticAt.analyticWithinAt

end ContinuousMultilinearMap


/-!
### Continuous linear maps into continuous multilinear maps

We show that a continuous linear map into continuous multilinear maps is continuously polynomial
(as a function of two variables, i.e., uncurried). Therefore, it is also analytic.
-/

namespace ContinuousLinearMap

variable {ι : Type*} {Em : ι → Type*} [∀ i, NormedAddCommGroup (Em i)] [∀ i, NormedSpace 𝕜 (Em i)]
  [Fintype ι] (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 Em F)
  {s : Set (G × (Π i, Em i))} {x : G × (Π i, Em i)}

/-- Formal multilinear series associated to a linear map into multilinear maps. -/
noncomputable def toFormalMultilinearSeriesOfMultilinear :
    FormalMultilinearSeries 𝕜 (G × (Π i, Em i)) F :=
  fun n ↦ if h : Fintype.card (Option ι) = n then
    (f.continuousMultilinearMapOption).domDomCongr (Fintype.equivFinOfCardEq h)
  else 0

protected theorem hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear :
    HasFiniteFPowerSeriesOnBall (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2)
      f.toFormalMultilinearSeriesOfMultilinear 0 (Fintype.card (Option ι) + 1) ⊤ := by
  apply HasFiniteFPowerSeriesOnBall.mk' ?_ ENNReal.zero_lt_top  ?_
  · intro m hm
    apply dif_neg
    exact Nat.ne_of_lt hm
  · intro y _
    rw [Finset.sum_eq_single_of_mem _ (Finset.self_mem_range_succ _), zero_add]
    · rw [toFormalMultilinearSeriesOfMultilinear, dif_pos rfl]; rfl
    · intro m _ ne; rw [toFormalMultilinearSeriesOfMultilinear, dif_neg ne.symm]; rfl

lemma cpolynomialAt_uncurry_of_multilinear :
    CPolynomialAt 𝕜 (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2) x :=
  f.hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear.cPolynomialAt_of_mem
    (by simp only [Metric.emetric_ball_top, Set.mem_univ])

lemma cpolyomialOn_uncurry_of_multilinear :
    CPolynomialOn 𝕜 (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2) s :=
  fun _ _ ↦ f.cpolynomialAt_uncurry_of_multilinear

lemma analyticOnNhd_uncurry_of_multilinear :
    AnalyticOnNhd 𝕜 (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2) s :=
  f.cpolyomialOn_uncurry_of_multilinear.analyticOnNhd

lemma analyticOn_uncurry_of_multilinear :
    AnalyticOn 𝕜 (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2) s :=
  f.analyticOnNhd_uncurry_of_multilinear.analyticOn

@[deprecated (since := "2024-09-26")]
alias analyticWithinOn_uncurry_of_multilinear := analyticOn_uncurry_of_multilinear

lemma analyticAt_uncurry_of_multilinear : AnalyticAt 𝕜 (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2) x :=
  f.cpolynomialAt_uncurry_of_multilinear.analyticAt

lemma analyticWithinAt_uncurry_of_multilinear :
    AnalyticWithinAt 𝕜 (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2) s x :=
  f.analyticAt_uncurry_of_multilinear.analyticWithinAt

end ContinuousLinearMap
