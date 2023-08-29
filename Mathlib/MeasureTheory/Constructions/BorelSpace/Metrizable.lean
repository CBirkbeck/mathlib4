/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Metrizable

#align_import measure_theory.constructions.borel_space.metrizable from "leanprover-community/mathlib"@"bf6a01357ff5684b1ebcd0f1a13be314fc82c0bf"

/-!
# Measurable functions in (pseudo-)metrizable Borel spaces
-/


open Filter MeasureTheory TopologicalSpace

open Classical Topology NNReal ENNReal MeasureTheory

variable {α β : Type*} [MeasurableSpace α]

section Limits

variable [TopologicalSpace β] [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]

open Metric

/-- A limit (over a general filter) of measurable `ℝ≥0∞` valued functions is measurable. -/
theorem measurable_of_tendsto_ennreal' {ι} {f : ι → α → ℝ≥0∞} {g : α → ℝ≥0∞} (u : Filter ι)
    [NeBot u] [IsCountablyGenerated u] (hf : ∀ i, Measurable (f i)) (lim : Tendsto f u (𝓝 g)) :
    Measurable g := by
  rcases u.exists_seq_tendsto with ⟨x, hx⟩
  -- ⊢ Measurable g
  rw [tendsto_pi_nhds] at lim
  -- ⊢ Measurable g
  have : (fun y => liminf (fun n => (f (x n) y : ℝ≥0∞)) atTop) = g := by
    ext1 y
    exact ((lim y).comp hx).liminf_eq
  rw [← this]
  -- ⊢ Measurable fun y => liminf (fun n => f (x n) y) atTop
  show Measurable fun y => liminf (fun n => (f (x n) y : ℝ≥0∞)) atTop
  -- ⊢ Measurable fun y => liminf (fun n => f (x n) y) atTop
  exact measurable_liminf fun n => hf (x n)
  -- 🎉 no goals
#align measurable_of_tendsto_ennreal' measurable_of_tendsto_ennreal'

/-- A sequential limit of measurable `ℝ≥0∞` valued functions is measurable. -/
theorem measurable_of_tendsto_ennreal {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    (lim : Tendsto f atTop (𝓝 g)) : Measurable g :=
  measurable_of_tendsto_ennreal' atTop hf lim
#align measurable_of_tendsto_ennreal measurable_of_tendsto_ennreal

/-- A limit (over a general filter) of measurable `ℝ≥0` valued functions is measurable. -/
theorem measurable_of_tendsto_nnreal' {ι} {f : ι → α → ℝ≥0} {g : α → ℝ≥0} (u : Filter ι) [NeBot u]
    [IsCountablyGenerated u] (hf : ∀ i, Measurable (f i)) (lim : Tendsto f u (𝓝 g)) :
    Measurable g := by
  simp_rw [← measurable_coe_nnreal_ennreal_iff] at hf ⊢
  -- ⊢ Measurable fun x => ↑(g x)
  refine' measurable_of_tendsto_ennreal' u hf _
  -- ⊢ Tendsto (fun i x => ↑(f i x)) u (𝓝 fun x => ↑(g x))
  rw [tendsto_pi_nhds] at lim ⊢
  -- ⊢ ∀ (x : α), Tendsto (fun i => ↑(f i x)) u (𝓝 ↑(g x))
  exact fun x => (ENNReal.continuous_coe.tendsto (g x)).comp (lim x)
  -- 🎉 no goals
#align measurable_of_tendsto_nnreal' measurable_of_tendsto_nnreal'

/-- A sequential limit of measurable `ℝ≥0` valued functions is measurable. -/
theorem measurable_of_tendsto_nnreal {f : ℕ → α → ℝ≥0} {g : α → ℝ≥0} (hf : ∀ i, Measurable (f i))
    (lim : Tendsto f atTop (𝓝 g)) : Measurable g :=
  measurable_of_tendsto_nnreal' atTop hf lim
#align measurable_of_tendsto_nnreal measurable_of_tendsto_nnreal

/-- A limit (over a general filter) of measurable functions valued in a (pseudo) metrizable space is
measurable. -/
theorem measurable_of_tendsto_metrizable' {ι} {f : ι → α → β} {g : α → β} (u : Filter ι) [NeBot u]
    [IsCountablyGenerated u] (hf : ∀ i, Measurable (f i)) (lim : Tendsto f u (𝓝 g)) :
    Measurable g := by
  letI : PseudoMetricSpace β := pseudoMetrizableSpacePseudoMetric β
  -- ⊢ Measurable g
  apply measurable_of_is_closed'
  -- ⊢ ∀ (s : Set β), IsClosed s → Set.Nonempty s → s ≠ Set.univ → MeasurableSet (g …
  intro s h1s h2s h3s
  -- ⊢ MeasurableSet (g ⁻¹' s)
  have : Measurable fun x => infNndist (g x) s := by
    suffices : Tendsto (fun i x => infNndist (f i x) s) u (𝓝 fun x => infNndist (g x) s)
    exact measurable_of_tendsto_nnreal' u (fun i => (hf i).infNndist) this
    rw [tendsto_pi_nhds] at lim ⊢
    intro x
    exact ((continuous_infNndist_pt s).tendsto (g x)).comp (lim x)
  have h4s : g ⁻¹' s = (fun x => infNndist (g x) s) ⁻¹' {0} := by
    ext x
    simp [h1s, ← h1s.mem_iff_infDist_zero h2s, ← NNReal.coe_eq_zero]
  rw [h4s]
  -- ⊢ MeasurableSet ((fun x => infNndist (g x) s) ⁻¹' {0})
  exact this (measurableSet_singleton 0)
  -- 🎉 no goals
#align measurable_of_tendsto_metrizable' measurable_of_tendsto_metrizable'

/-- A sequential limit of measurable functions valued in a (pseudo) metrizable space is
measurable. -/
theorem measurable_of_tendsto_metrizable {f : ℕ → α → β} {g : α → β} (hf : ∀ i, Measurable (f i))
    (lim : Tendsto f atTop (𝓝 g)) : Measurable g :=
  measurable_of_tendsto_metrizable' atTop hf lim
#align measurable_of_tendsto_metrizable measurable_of_tendsto_metrizable

theorem aemeasurable_of_tendsto_metrizable_ae {ι} {μ : Measure α} {f : ι → α → β} {g : α → β}
    (u : Filter ι) [hu : NeBot u] [IsCountablyGenerated u] (hf : ∀ n, AEMeasurable (f n) μ)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) u (𝓝 (g x))) : AEMeasurable g μ := by
  rcases u.exists_seq_tendsto with ⟨v, hv⟩
  -- ⊢ AEMeasurable g
  have h'f : ∀ n, AEMeasurable (f (v n)) μ := fun n => hf (v n)
  -- ⊢ AEMeasurable g
  set p : α → (ℕ → β) → Prop := fun x f' => Tendsto (fun n => f' n) atTop (𝓝 (g x))
  -- ⊢ AEMeasurable g
  have hp : ∀ᵐ x ∂μ, p x fun n => f (v n) x := by
    filter_upwards [h_tendsto]with x hx using hx.comp hv
  set aeSeqLim := fun x => ite (x ∈ aeSeqSet h'f p) (g x) (⟨f (v 0) x⟩ : Nonempty β).some
  -- ⊢ AEMeasurable g
  refine'
    ⟨aeSeqLim,
      measurable_of_tendsto_metrizable' atTop (aeSeq.measurable h'f p)
        (tendsto_pi_nhds.mpr fun x => _),
      _⟩
  · simp_rw [aeSeq]
    -- ⊢ Tendsto (fun i => if x ∈ aeSeqSet h'f fun x f' => Tendsto (fun n => f' n) at …
    split_ifs with hx
    -- ⊢ Tendsto (fun i => AEMeasurable.mk (f (v i)) (_ : AEMeasurable (f (v i))) x)  …
    · simp_rw [aeSeq.mk_eq_fun_of_mem_aeSeqSet h'f hx]
      -- ⊢ Tendsto (fun i => f (v i) x) atTop (𝓝 (g x))
      exact @aeSeq.fun_prop_of_mem_aeSeqSet _ α β _ _ _ _ _ h'f x hx
      -- 🎉 no goals
    · exact tendsto_const_nhds
      -- 🎉 no goals
  · exact
      (ite_ae_eq_of_measure_compl_zero g (fun x => (⟨f (v 0) x⟩ : Nonempty β).some) (aeSeqSet h'f p)
          (aeSeq.measure_compl_aeSeqSet_eq_zero h'f hp)).symm
#align ae_measurable_of_tendsto_metrizable_ae aemeasurable_of_tendsto_metrizable_ae

theorem aemeasurable_of_tendsto_metrizable_ae' {μ : Measure α} {f : ℕ → α → β} {g : α → β}
    (hf : ∀ n, AEMeasurable (f n) μ)
    (h_ae_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : AEMeasurable g μ :=
  aemeasurable_of_tendsto_metrizable_ae atTop hf h_ae_tendsto
#align ae_measurable_of_tendsto_metrizable_ae' aemeasurable_of_tendsto_metrizable_ae'

theorem aemeasurable_of_unif_approx {β} [MeasurableSpace β] [PseudoMetricSpace β] [BorelSpace β]
    {μ : Measure α} {g : α → β}
    (hf : ∀ ε > (0 : ℝ), ∃ f : α → β, AEMeasurable f μ ∧ ∀ᵐ x ∂μ, dist (f x) (g x) ≤ ε) :
    AEMeasurable g μ := by
  obtain ⟨u, -, u_pos, u_lim⟩ :
    ∃ u : ℕ → ℝ, StrictAnti u ∧ (∀ n : ℕ, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  choose f Hf using fun n : ℕ => hf (u n) (u_pos n)
  -- ⊢ AEMeasurable g
  have : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
    have : ∀ᵐ x ∂μ, ∀ n, dist (f n x) (g x) ≤ u n := ae_all_iff.2 fun n => (Hf n).2
    filter_upwards [this]
    intro x hx
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) hx u_lim
  exact aemeasurable_of_tendsto_metrizable_ae' (fun n => (Hf n).1) this
  -- 🎉 no goals
#align ae_measurable_of_unif_approx aemeasurable_of_unif_approx

theorem measurable_of_tendsto_metrizable_ae {μ : Measure α} [μ.IsComplete] {f : ℕ → α → β}
    {g : α → β} (hf : ∀ n, Measurable (f n))
    (h_ae_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Measurable g :=
  aemeasurable_iff_measurable.mp
    (aemeasurable_of_tendsto_metrizable_ae' (fun i => (hf i).aemeasurable) h_ae_tendsto)
#align measurable_of_tendsto_metrizable_ae measurable_of_tendsto_metrizable_ae

theorem measurable_limit_of_tendsto_metrizable_ae {ι} [Countable ι] [Nonempty ι] {μ : Measure α}
    {f : ι → α → β} {L : Filter ι} [L.IsCountablyGenerated] (hf : ∀ n, AEMeasurable (f n) μ)
    (h_ae_tendsto : ∀ᵐ x ∂μ, ∃ l : β, Tendsto (fun n => f n x) L (𝓝 l)) :
    ∃ (f_lim : α → β) (hf_lim_meas : Measurable f_lim),
      ∀ᵐ x ∂μ, Tendsto (fun n => f n x) L (𝓝 (f_lim x)) := by
  inhabit ι
  -- ⊢ ∃ f_lim hf_lim_meas, ∀ᵐ (x : α) ∂μ, Tendsto (fun n => f n x) L (𝓝 (f_lim x))
  rcases eq_or_neBot L with (rfl | hL)
  -- ⊢ ∃ f_lim hf_lim_meas, ∀ᵐ (x : α) ∂μ, Tendsto (fun n => f n x) ⊥ (𝓝 (f_lim x))
  · exact ⟨(hf default).mk _, (hf default).measurable_mk, eventually_of_forall fun x => tendsto_bot⟩
    -- 🎉 no goals
  let p : α → (ι → β) → Prop := fun x f' => ∃ l : β, Tendsto (fun n => f' n) L (𝓝 l)
  -- ⊢ ∃ f_lim hf_lim_meas, ∀ᵐ (x : α) ∂μ, Tendsto (fun n => f n x) L (𝓝 (f_lim x))
  have hp_mem : ∀ x ∈ aeSeqSet hf p, p x fun n => f n x := fun x hx =>
    aeSeq.fun_prop_of_mem_aeSeqSet hf hx
  have h_ae_eq : ∀ᵐ x ∂μ, ∀ n, aeSeq hf p n x = f n x := aeSeq.aeSeq_eq_fun_ae hf h_ae_tendsto
  -- ⊢ ∃ f_lim hf_lim_meas, ∀ᵐ (x : α) ∂μ, Tendsto (fun n => f n x) L (𝓝 (f_lim x))
  set f_lim : α → β := fun x => dite (x ∈ aeSeqSet hf p) (fun h => (hp_mem x h).choose)
    fun _ => (⟨f default x⟩ : Nonempty β).some
  have hf_lim : ∀ x, Tendsto (fun n => aeSeq hf p n x) L (𝓝 (f_lim x)) := by
    intro x
    simp only [aeSeq]
    split_ifs with h
    · refine' (hp_mem x h).choose_spec.congr fun n => _
      exact (aeSeq.mk_eq_fun_of_mem_aeSeqSet hf h n).symm
    · exact tendsto_const_nhds
  have h_ae_tendsto_f_lim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) L (𝓝 (f_lim x)) :=
    h_ae_eq.mono fun x hx => (hf_lim x).congr hx
  have h_f_lim_meas : Measurable f_lim :=
    measurable_of_tendsto_metrizable' L (aeSeq.measurable hf p)
      (tendsto_pi_nhds.mpr fun x => hf_lim x)
  exact ⟨f_lim, h_f_lim_meas, h_ae_tendsto_f_lim⟩
  -- 🎉 no goals
#align measurable_limit_of_tendsto_metrizable_ae measurable_limit_of_tendsto_metrizable_ae

end Limits

section TendstoIndicator

variable {α : Type _} [MeasurableSpace α] {A : Set α}
variable {ι : Type _} (L : Filter ι) [IsCountablyGenerated L] {As : ι → Set α}

/-- If the indicator functions of measurable sets `Aᵢ` converge to the indicator function of
a set `A` along a nontrivial countably generated filter, then `A` is also measurable. -/
lemma measurableSet_of_tendsto_indicator [NeBot L] (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : Tendsto (fun i ↦ (As i).indicator (1 : α → ℝ≥0∞)) L (𝓝 (A.indicator 1))) :
    MeasurableSet A := by
  simp_rw [← measurable_indicator_const_iff (1 : ℝ≥0∞)] at As_mble ⊢
  -- ⊢ Measurable (Set.indicator A fun x => 1)
  exact measurable_of_tendsto_ennreal' L As_mble h_lim
  -- 🎉 no goals

/-- If the indicator functions of a.e.-measurable sets `Aᵢ` converge a.e. to the indicator function
of a set `A` along a nontrivial countably generated filter, then `A` is also a.e.-measurable. -/
lemma nullMeasurableSet_of_tendsto_indicator [NeBot L] {μ : Measure α}
    (As_mble : ∀ i, NullMeasurableSet (As i) μ)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ (As i).indicator (1 : α → ℝ≥0∞) x)
      L (𝓝 (A.indicator 1 x))) :
    NullMeasurableSet A μ := by
  simp_rw [← aemeasurable_indicator_const_iff (1 : ℝ≥0∞)] at As_mble ⊢
  -- ⊢ AEMeasurable (Set.indicator A fun x => 1)
  exact aemeasurable_of_tendsto_metrizable_ae L As_mble h_lim
  -- 🎉 no goals

end TendstoIndicator
