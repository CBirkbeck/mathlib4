/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tangent cone

In this file, we define two predicates `UniqueDiffWithinAt 𝕜 s x` and `UniqueDiffOn 𝕜 s`
ensuring that, if a function has two derivatives, then they have to coincide. As a direct
definition of this fact (quantifying on all target types and all functions) would depend on
universes, we use a more intrinsic definition: if all the possible tangent directions to the set
`s` at the point `x` span a dense subset of the whole subset, it is easy to check that the
derivative has to be unique.

Therefore, we introduce the set of all tangent directions, named `tangentConeAt`,
and express `UniqueDiffWithinAt` and `UniqueDiffOn` in terms of it.
One should however think of this definition as an implementation detail: the only reason to
introduce the predicates `UniqueDiffWithinAt` and `UniqueDiffOn` is to ensure the uniqueness
of the derivative. This is why their names reflect their uses, and not how they are defined.

## Implementation details

Note that this file is imported by `Mathlib.Analysis.Calculus.FDeriv.Basic`. Hence, derivatives are
not defined yet. The property of uniqueness of the derivative is therefore proved in
`Mathlib.Analysis.Calculus.FDeriv.Basic`, but based on the properties of the tangent cone we prove
here.
-/

universe u v
open Function Filter Set Bornology
open scoped Topology Pointwise

section Defs

/-- The set of all tangent directions to the set `s` at the point `x`. -/
def tangentConeAt (𝕜 : Type*) {E : Type*} [AddCommMonoid E] [SMul 𝕜 E] [TopologicalSpace E]
    (s : Set E) (x : E) : Set E :=
  {y : E | MapClusterPt y ((⊤ : Filter 𝕜) ×ˢ 𝓝[(x + ·) ⁻¹' s] 0) (· • ·).uncurry}

variable (𝕜 : Type*) [Semiring 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- A property ensuring that the tangent cone to `s` at `x` spans a dense subset of the whole space.
The main role of this property is to ensure that the differential within `s` at `x` is unique,
hence this name. The uniqueness it asserts is proved in `UniqueDiffWithinAt.eq` in
`Mathlib.Analysis.Calculus.FDeriv.Basic`.
To avoid pathologies in dimension 0, we also require that `x` belongs to the closure of `s` (which
is automatic when `E` is not `0`-dimensional). -/
@[mk_iff]
structure UniqueDiffWithinAt (s : Set E) (x : E) : Prop where
  dense_tangentCone : Dense (Submodule.span 𝕜 (tangentConeAt 𝕜 s x) : Set E)
  mem_closure : x ∈ closure s

/-- A property ensuring that the tangent cone to `s` at any of its points spans a dense subset of
the whole space. The main role of this property is to ensure that the differential along `s` is
unique, hence this name. The uniqueness it asserts is proved in `UniqueDiffOn.eq` in
`Mathlib.Analysis.Calculus.FDeriv.Basic`. -/
def UniqueDiffOn (s : Set E) : Prop :=
  ∀ x ∈ s, UniqueDiffWithinAt 𝕜 s x

end Defs

variable {𝕜 E F G : Type*}

section TangentCone

section SMul

variable [AddCommMonoid E] [SMul 𝕜 E] [TopologicalSpace E] {s t : Set E} {x y : E}

theorem isClosed_tangentConeAt : IsClosed (tangentConeAt 𝕜 s x) :=
  isClosed_setOf_clusterPt

theorem mem_tangentConeAt_of_seq {α : Type*} {l : Filter α} [l.NeBot] {c : α → 𝕜} {d : α → E}
    (hd₀ : Tendsto d l (𝓝 0)) (hd : ∀ᶠ n in l, x + d n ∈ s)
    (hcd : Tendsto (fun n ↦ c n • d n) l (𝓝 y)) : y ∈ tangentConeAt 𝕜 s x := by
  refine .of_comp (tendsto_top.prod_mk <| tendsto_nhdsWithin_iff.mpr ⟨hd₀, ?_⟩)
    (by simpa [comp_def] using hcd.mapClusterPt)
  simpa [← preimage_vadd] using hd

@[gcongr]
theorem tangentConeAt_mono (h : s ⊆ t) : tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜 t x :=
  fun y hy ↦ hy.mono <| by gcongr

@[deprecated (since := "2025-03-06")]
alias tangentCone_mono := tangentConeAt_mono

variable [ContinuousAdd E]

theorem tangentConeAt_mono_nhds (h : 𝓝[s] x ≤ 𝓝[t] x) :
    tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜 t x := by
  refine fun y hy ↦ hy.mono ?_
  gcongr _ ×ˢ ?_
  refine le_inf inf_le_left <| ?_
  rw [le_principal_iff]
  have : Tendsto (x + ·) (𝓝 0) (𝓝 x) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  exact this.inf (mapsTo_preimage _ _).tendsto <| h self_mem_nhdsWithin

@[deprecated (since := "2025-03-06")]
alias tangentCone_mono_nhds := tangentConeAt_mono_nhds

/-- Tangent cone of `s` at `x` depends only on `𝓝[s] x`. -/
theorem tangentConeAt_congr (h : 𝓝[s] x = 𝓝[t] x) : tangentConeAt 𝕜 s x = tangentConeAt 𝕜 t x :=
  (tangentConeAt_mono_nhds h.le).antisymm (tangentConeAt_mono_nhds h.ge)

@[deprecated (since := "2025-03-06")]
alias tangentCone_congr := tangentConeAt_congr

/-- Intersecting with a neighborhood of the point does not change the tangent cone. -/
theorem tangentConeAt_inter_nhds (ht : t ∈ 𝓝 x) : tangentConeAt 𝕜 (s ∩ t) x = tangentConeAt 𝕜 s x :=
  tangentConeAt_congr (nhdsWithin_restrict' _ ht).symm

@[deprecated (since := "2025-03-06")]
alias tangentCone_inter_nhds := tangentConeAt_inter_nhds

theorem mem_closure_of_tangentConeAt_nonempty (h : (tangentConeAt 𝕜 s x).Nonempty) :
    x ∈ closure s := by
  rcases h with ⟨y, hy⟩
  have : 0 ∈ closure ((x + ·) ⁻¹' s) := by
    have := hy.neBot.mono inf_le_right
    simp_all [mem_closure_iff_nhdsWithin_neBot]
  simpa using map_mem_closure (by fun_prop) this (mapsTo_preimage _ _)

theorem tangentConeAt_of_not_mem_closure (h : x ∉ closure s) : tangentConeAt 𝕜 s x = ∅ := by
  contrapose! h
  exact mem_closure_of_tangentConeAt_nonempty h

end SMul

section AddCommMonoid

variable [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] {s : Set E} {x : E}

@[simp]
theorem tangentConeAt_univ [TopologicalSpace 𝕜] [NeBot (𝓝[{c | IsUnit c}] (0 : 𝕜))]
    [ContinuousSMul 𝕜 E] : tangentConeAt 𝕜 univ x = univ := by
  refine eq_univ_of_forall fun y ↦ ?_
  set l := 𝓝[{c | IsUnit c}] (0 : 𝕜)
  have hd : Tendsto (fun c : 𝕜 ↦ c • y) l (𝓝 0) :=
    .mono_left (Continuous.tendsto' (by fun_prop) _ _ (zero_smul _ y)) nhdsWithin_le_nhds
  have hcd : Tendsto (fun c : 𝕜 ↦ Ring.inverse c • c • y) l (𝓝 y) :=
    tendsto_const_nhds.congr' <| eventually_mem_nhdsWithin.mono fun c hc ↦ by
      simp [smul_smul, Ring.inverse_mul_cancel c hc]
  exact mem_tangentConeAt_of_seq hd (by simp) hcd

@[deprecated (since := "2025-03-06")]
alias tangentCone_univ := tangentConeAt_univ

variable [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] {t : Set F} {y : F}

/-- If a continuous linear map maps `s` to `t`,
then it maps the tangent cone of `s` at `x` to the tangent coen of `t` at `f x`. -/
theorem mapsTo_tangentConeAt (f : E →L[𝕜] F) (h : MapsTo f s t) :
    MapsTo f (tangentConeAt 𝕜 s x) (tangentConeAt 𝕜 t (f x)) := by
  intro z hz
  refine .of_comp (φ := Prod.map id f) ?_ <|
    ((hz.out.tendsto_comp f.continuous.continuousAt)).congrFun <| .of_forall <| by simp
  refine tendsto_id.prod_map <| .inf (f.continuous.tendsto' _ _ (map_zero f)) ?_
  rw [tendsto_principal_principal]
  intro a ha
  simpa using h ha

/-- The tangent cone of a product contains the tangent cone of its left factor.

This version assumes that `0` belongs to the closure of `{z | y + z ∈ t}`.
For a version assuming `y ∈ closure t`, see `mapsTo_inl_tangentConeAt` below. -/
theorem mapsTo_inl_tangentConeAt' [ContinuousConstSMul 𝕜 F] {t : Set F} {y : F}
    (ht : 0 ∈ closure ((y + ·) ⁻¹' t)) :
    Set.MapsTo (LinearMap.inl 𝕜 E F) (tangentConeAt 𝕜 s x) (tangentConeAt 𝕜 (s ×ˢ t) (x, y)) := by
  intro z hz
  refine ((basis_sets _).prod_nhds (basis_sets _)).mapClusterPt_iff_frequently.mpr ?_
  rintro ⟨U, V⟩ ⟨hzU : U ∈ 𝓝 z, hV₀ : V ∈ 𝓝 0⟩
  have : ⊤ ×ˢ 𝓝[((x, y) + ·) ⁻¹' s ×ˢ t] 0 =
      map (Equiv.prodAssoc 𝕜 E F) ((⊤ ×ˢ 𝓝[(x + ·) ⁻¹' s] 0) ×ˢ 𝓝[(y + ·) ⁻¹' t] 0) := by
    rw [Filter.prod_assoc, ← nhdsWithin_prod_eq]
    rfl
  rw [this, frequently_map]
  apply Frequently.of_curry
  refine (hz.out.frequently (eventually_mem_set.mpr hzU)).mono ?_
  suffices ∀ a : 𝕜, ∃ᶠ c in 𝓝[(y + ·) ⁻¹' t] 0, a • c ∈ V by simp [this]
  intro a
  rw [frequently_nhdsWithin_iff]
  refine Eventually.and_frequently ?_ (mem_closure_iff_frequently.mp ht)
  exact Continuous.tendsto' (by fun_prop) 0 0 (smul_zero a) hV₀
  
end AddCommMonoid

section AddCommGroup

variable [Semiring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] {s : Set E} {x : E}

@[simp]
theorem tangentConeAt_closure [ContinuousConstSMul 𝕜 E] [ContinuousAdd E] (s : Set E) (x : E) :
    tangentConeAt 𝕜 (closure s) x = tangentConeAt 𝕜 s x := by
  refine Subset.antisymm ?_ (tangentConeAt_mono subset_closure)
  intro y hy
  simp only [tangentConeAt, mem_setOf_eq, (nhds_basis_opens _).mapClusterPt_iff_frequently,
    top_prod, frequently_comap, frequently_nhdsWithin_iff, Prod.exists, exists_eq_left, uncurry,
    mem_preimage, (nhds_basis_opens _).frequently_iff] at hy ⊢
  rintro U ⟨hyU, hUo⟩ V ⟨hV₀, hVo⟩
  rcases hy U ⟨hyU, hUo⟩ V ⟨hV₀, hVo⟩ with ⟨z, hzV, ⟨c, hcU⟩, hzs⟩
  have : ∀ᶠ w in 𝓝 (x + z), c • (-x + w) ∈ U ∧ -x + w ∈ V := by
    apply Eventually.and
    · exact Continuous.tendsto' (by fun_prop) _ _ (by simp) |>.eventually (hUo.mem_nhds hcU)
    · exact Continuous.tendsto' (by fun_prop) _ _ (by simp) |>.eventually (hVo.mem_nhds hzV)
  rcases mem_closure_iff_nhds.mp hzs _ this with ⟨w, ⟨hwU, hwV⟩, hws⟩
  refine ⟨-x + w, hwV, ⟨c, hwU⟩, ?_⟩
  simpa

variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] {t : Set F} {y : F}

theorem mapsTo_inl_tangentConeAt (hy : y ∈ closure t) :
    MapsTo (·, 0) (tangentConeAt 𝕜 s x) (tangentConeAt 𝕜 (s ×ˢ t) (x, y)) := by
  intro z hz
  

end AddCommGroup

section Normed
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {x y : E} {s t : Set E}

/-- The tangent cone of a product contains the tangent cone of its left factor. -/
theorem subset_tangentCone_prod_left {t : Set F} {y : F} (ht : y ∈ closure t) :
    LinearMap.inl 𝕜 E F '' tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜 (s ×ˢ t) (x, y) := by
  rintro _ ⟨v, ⟨c, d, hd, hc, hy⟩, rfl⟩
  have : ∀ n, ∃ d', y + d' ∈ t ∧ ‖c n • d'‖ < ((1 : ℝ) / 2) ^ n := by
    intro n
    rcases mem_closure_iff_nhds.1 ht _
        (eventually_nhds_norm_smul_sub_lt (c n) y (pow_pos one_half_pos n)) with
      ⟨z, hz, hzt⟩
    exact ⟨z - y, by simpa using hzt, by simpa using hz⟩
  choose d' hd' using this
  refine ⟨c, fun n => (d n, d' n), ?_, hc, ?_⟩
  · show ∀ᶠ n in atTop, (x, y) + (d n, d' n) ∈ s ×ˢ t
    filter_upwards [hd] with n hn
    simp [hn, (hd' n).1]
  · apply Tendsto.prod_mk_nhds hy _
    refine squeeze_zero_norm (fun n => (hd' n).2.le) ?_
    exact tendsto_pow_atTop_nhds_zero_of_lt_one one_half_pos.le one_half_lt_one

/-- The tangent cone of a product contains the tangent cone of its right factor. -/
theorem subset_tangentCone_prod_right {t : Set F} {y : F} (hs : x ∈ closure s) :
    LinearMap.inr 𝕜 E F '' tangentConeAt 𝕜 t y ⊆ tangentConeAt 𝕜 (s ×ˢ t) (x, y) := by
  rintro _ ⟨w, ⟨c, d, hd, hc, hy⟩, rfl⟩
  have : ∀ n, ∃ d', x + d' ∈ s ∧ ‖c n • d'‖ < ((1 : ℝ) / 2) ^ n := by
    intro n
    rcases mem_closure_iff_nhds.1 hs _
        (eventually_nhds_norm_smul_sub_lt (c n) x (pow_pos one_half_pos n)) with
      ⟨z, hz, hzs⟩
    exact ⟨z - x, by simpa using hzs, by simpa using hz⟩
  choose d' hd' using this
  refine ⟨c, fun n => (d' n, d n), ?_, hc, ?_⟩
  · show ∀ᶠ n in atTop, (x, y) + (d' n, d n) ∈ s ×ˢ t
    filter_upwards [hd] with n hn
    simp [hn, (hd' n).1]
  · apply Tendsto.prod_mk_nhds _ hy
    refine squeeze_zero_norm (fun n => (hd' n).2.le) ?_
    exact tendsto_pow_atTop_nhds_zero_of_lt_one one_half_pos.le one_half_lt_one

/-- The tangent cone of a product contains the tangent cone of each factor. -/
theorem mapsTo_tangentCone_pi {ι : Type*} [DecidableEq ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] {s : ∀ i, Set (E i)} {x : ∀ i, E i}
    {i : ι} (hi : ∀ j ≠ i, x j ∈ closure (s j)) :
    MapsTo (LinearMap.single 𝕜 E i) (tangentConeAt 𝕜 (s i) (x i))
      (tangentConeAt 𝕜 (Set.pi univ s) x) := by
  rintro w ⟨c, d, hd, hc, hy⟩
  have : ∀ n, ∀ j ≠ i, ∃ d', x j + d' ∈ s j ∧ ‖c n • d'‖ < (1 / 2 : ℝ) ^ n := fun n j hj ↦ by
    rcases mem_closure_iff_nhds.1 (hi j hj) _
        (eventually_nhds_norm_smul_sub_lt (c n) (x j) (pow_pos one_half_pos n)) with
      ⟨z, hz, hzs⟩
    exact ⟨z - x j, by simpa using hzs, by simpa using hz⟩
  choose! d' hd's hcd' using this
  refine ⟨c, fun n => Function.update (d' n) i (d n), hd.mono fun n hn j _ => ?_, hc,
      tendsto_pi_nhds.2 fun j => ?_⟩
  · rcases em (j = i) with (rfl | hj) <;> simp [*]
  · rcases em (j = i) with (rfl | hj)
    · simp [hy]
    · suffices Tendsto (fun n => c n • d' n j) atTop (𝓝 0) by simpa [hj]
      refine squeeze_zero_norm (fun n => (hcd' n j hj).le) ?_
      exact tendsto_pow_atTop_nhds_zero_of_lt_one one_half_pos.le one_half_lt_one

/-- If a subset of a real vector space contains an open segment, then the direction of this
segment belongs to the tangent cone at its endpoints. -/
theorem mem_tangentCone_of_openSegment_subset {s : Set G} {x y : G} (h : openSegment ℝ x y ⊆ s) :
    y - x ∈ tangentConeAt ℝ s x := by
  refine mem_tangentConeAt_of_pow_smul one_half_pos.ne' (by norm_num) ?_
  refine (eventually_ne_atTop 0).mono fun n hn ↦ (h ?_)
  rw [openSegment_eq_image]
  refine ⟨(1 / 2) ^ n, ⟨?_, ?_⟩, ?_⟩
  · exact pow_pos one_half_pos _
  · exact pow_lt_one₀ one_half_pos.le one_half_lt_one hn
  · simp only [sub_smul, one_smul, smul_sub]; abel

/-- If a subset of a real vector space contains a segment, then the direction of this
segment belongs to the tangent cone at its endpoints. -/
theorem mem_tangentCone_of_segment_subset {s : Set G} {x y : G} (h : segment ℝ x y ⊆ s) :
    y - x ∈ tangentConeAt ℝ s x :=
  mem_tangentCone_of_openSegment_subset ((openSegment_subset_segment ℝ x y).trans h)

/-- The tangent cone at a non-isolated point contains `0`. -/
theorem zero_mem_tangentCone {s : Set E} {x : E} (hx : (𝓝[s \ {x}] x).NeBot) :
    0 ∈ tangentConeAt 𝕜 s x := by
  /- Take a sequence `d n` tending to `0` such that `x + d n ∈ s`. Taking `c n` of the order
  of `1 / (d n) ^ (1/2)`, then `c n` tends to infinity, but `c n • d n` tends to `0`. By definition,
  this shows that `0` belongs to the tangent cone. -/
  obtain ⟨u, -, u_pos, u_lim⟩ :
      ∃ u, StrictAnti u ∧ (∀ (n : ℕ), 0 < u n) ∧ Tendsto u atTop (𝓝 (0 : ℝ)) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  have A n : ((s \ {x}) ∩ Metric.ball x (u n * u n)).Nonempty :=
    NeBot.nonempty_of_mem hx (inter_mem_nhdsWithin _
      (Metric.ball_mem_nhds _ (mul_pos (u_pos n) (u_pos n))))
  choose v hv using A
  let d n := v n - x
  have M n : x + d n ∈ s \ {x} := by simpa [d] using (hv n).1
  let ⟨r, hr⟩ := exists_one_lt_norm 𝕜
  have W n := rescale_to_shell hr (u_pos n) (x := d n) (by simpa using (M n).2)
  choose c c_ne c_le le_c hc using W
  have c_lim : Tendsto (fun n ↦ ‖c n‖) atTop atTop := by
    suffices Tendsto (fun n ↦ ‖c n‖⁻¹ ⁻¹) atTop atTop by simpa
    apply tendsto_inv_nhdsGT_zero.comp
    simp only [nhdsWithin, tendsto_inf, tendsto_principal, mem_Ioi, norm_pos_iff, ne_eq,
      eventually_atTop, ge_iff_le]
    have B (n : ℕ) : ‖c n‖⁻¹ ≤ ‖r‖ * u n := calc
      ‖c n‖⁻¹
      _ ≤ (u n)⁻¹ * ‖r‖ * ‖d n‖ := hc n
      _ ≤ (u n)⁻¹ * ‖r‖ * (u n * u n) := by
        gcongr
        · exact mul_nonneg (by simp [(u_pos n).le]) (norm_nonneg _)
        · specialize hv n
          simp only [mem_inter_iff, mem_diff, mem_singleton_iff, Metric.mem_ball, dist_eq_norm]
            at hv
          simpa using hv.2.le
      _ = ‖r‖ * u n := by field_simp [(u_pos n).ne']; ring
    refine ⟨?_, 0, fun n hn ↦ by simpa using c_ne n⟩
    apply squeeze_zero (fun n ↦ by positivity) B
    simpa using u_lim.const_mul _
  refine ⟨c, d, Eventually.of_forall (fun n ↦ by simpa [d] using (hv n).1.1), c_lim, ?_⟩
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun n ↦ by positivity) (fun n ↦ (c_le n).le) u_lim

/-- In a proper space, the tangent cone at a non-isolated point is nontrivial. -/
theorem tangentCone_nonempty_of_properSpace [ProperSpace E]
    {s : Set E} {x : E} (hx : (𝓝[s \ {x}] x).NeBot) :
    (tangentConeAt 𝕜 s x ∩ {0}ᶜ).Nonempty := by
  /- Take a sequence `d n` tending to `0` such that `x + d n ∈ s`. Taking `c n` of the order
  of `1 / d n`. Then `c n • d n` belongs to a fixed annulus. By compactness, one can extract
  a subsequence converging to a limit `l`. Then `l` is nonzero, and by definition it belongs to
  the tangent cone. -/
  obtain ⟨u, -, u_pos, u_lim⟩ :
      ∃ u, StrictAnti u ∧ (∀ (n : ℕ), 0 < u n) ∧ Tendsto u atTop (𝓝 (0 : ℝ)) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  have A n : ((s \ {x}) ∩ Metric.ball x (u n)).Nonempty := by
    apply NeBot.nonempty_of_mem hx (inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ (u_pos n)))
  choose v hv using A
  let d := fun n ↦ v n - x
  have M n : x + d n ∈ s \ {x} := by simpa [d] using (hv n).1
  let ⟨r, hr⟩ := exists_one_lt_norm 𝕜
  have W n := rescale_to_shell hr zero_lt_one (x := d n) (by simpa using (M n).2)
  choose c c_ne c_le le_c hc using W
  have c_lim : Tendsto (fun n ↦ ‖c n‖) atTop atTop := by
    suffices Tendsto (fun n ↦ ‖c n‖⁻¹ ⁻¹ ) atTop atTop by simpa
    apply tendsto_inv_nhdsGT_zero.comp
    simp only [nhdsWithin, tendsto_inf, tendsto_principal, mem_Ioi, norm_pos_iff, ne_eq,
      eventually_atTop, ge_iff_le]
    have B (n : ℕ) : ‖c n‖⁻¹ ≤ 1⁻¹ * ‖r‖ * u n := by
      apply (hc n).trans
      gcongr
      specialize hv n
      simp only [mem_inter_iff, mem_diff, mem_singleton_iff, Metric.mem_ball, dist_eq_norm] at hv
      simpa using hv.2.le
    refine ⟨?_, 0, fun n hn ↦ by simpa using c_ne n⟩
    apply squeeze_zero (fun n ↦ by positivity) B
    simpa using u_lim.const_mul _
  obtain ⟨l, l_mem, φ, φ_strict, hφ⟩ :
      ∃ l ∈ Metric.closedBall (0 : E) 1 \ Metric.ball (0 : E) (1 / ‖r‖),
      ∃ (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto ((fun n ↦ c n • d n) ∘ φ) atTop (𝓝 l) := by
    apply IsCompact.tendsto_subseq _ (fun n ↦ ?_)
    · exact (isCompact_closedBall 0 1).diff Metric.isOpen_ball
    simp only [mem_diff, Metric.mem_closedBall, dist_zero_right, (c_le n).le,
      Metric.mem_ball, not_lt, true_and, le_c n]
  refine ⟨l, ?_, ?_⟩; swap
  · simp only [mem_compl_iff, mem_singleton_iff]
    contrapose! l_mem
    simp only [one_div, l_mem, mem_diff, Metric.mem_closedBall, dist_self, zero_le_one,
      Metric.mem_ball, inv_pos, norm_pos_iff, ne_eq, not_not, true_and]
    contrapose! hr
    simp [hr]
  refine ⟨c ∘ φ, d ∘ φ, ?_, ?_, hφ⟩
  · exact Eventually.of_forall (fun n ↦ by simpa [d] using (hv (φ n)).1.1)
  · exact c_lim.comp φ_strict.tendsto_atTop

/-- The tangent cone at a non-isolated point in dimension 1 is the whole space. -/
theorem tangentCone_eq_univ {s : Set 𝕜} {x : 𝕜} (hx : (𝓝[s \ {x}] x).NeBot) :
    tangentConeAt 𝕜 s x = univ := by
  apply eq_univ_iff_forall.2 (fun y ↦ ?_)
  -- first deal with the case of `0`, which has to be handled separately.
  rcases eq_or_ne y 0 with rfl | hy
  · exact zero_mem_tangentCone hx
  /- Assume now `y` is a fixed nonzero scalar. Take a sequence `d n` tending to `0` such
  that `x + d n ∈ s`. Let `c n = y / d n`. Then `‖c n‖` tends to infinity, and `c n • d n`
  converges to `y` (as it is equal to `y`). By definition, this shows that `y` belongs to the
  tangent cone. -/
  obtain ⟨u, -, u_pos, u_lim⟩ :
      ∃ u, StrictAnti u ∧ (∀ (n : ℕ), 0 < u n) ∧ Tendsto u atTop (𝓝 (0 : ℝ)) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  have A n : ((s \ {x}) ∩ Metric.ball x (u n)).Nonempty := by
    apply NeBot.nonempty_of_mem hx (inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ (u_pos n)))
  choose v hv using A
  let d := fun n ↦ v n - x
  have d_ne n : d n ≠ 0 := by
    simp only [mem_inter_iff, mem_diff, mem_singleton_iff, Metric.mem_ball, d] at hv
    simpa [d, sub_ne_zero] using (hv n).1.2
  refine ⟨fun n ↦ y * (d n)⁻¹, d, ?_, ?_, ?_⟩
  · exact Eventually.of_forall (fun n ↦ by simpa [d] using (hv n).1.1)
  · simp only [norm_mul, norm_inv]
    apply (tendsto_const_mul_atTop_of_pos (by simpa using hy)).2
    apply tendsto_inv_nhdsGT_zero.comp
    simp only [nhdsWithin, tendsto_inf, tendsto_principal, mem_Ioi, norm_pos_iff, ne_eq,
      eventually_atTop, ge_iff_le]
    have B (n : ℕ) : ‖d n‖ ≤ u n := by
      specialize hv n
      simp only [mem_inter_iff, mem_diff, mem_singleton_iff, Metric.mem_ball, dist_eq_norm] at hv
      simpa using hv.2.le
    refine ⟨?_, 0, fun n hn ↦ by simpa using d_ne n⟩
    exact squeeze_zero (fun n ↦ by positivity) B u_lim
  · convert tendsto_const_nhds (α := ℕ) (x := y) with n
    simp [mul_assoc, inv_mul_cancel₀ (d_ne n)]

end Normed

end TangentCone

section UniqueDiff

/-!
### Properties of `UniqueDiffWithinAt` and `UniqueDiffOn`

This section is devoted to properties of the predicates `UniqueDiffWithinAt` and `UniqueDiffOn`. -/

section TVS
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {x y : E} {s t : Set E}

theorem UniqueDiffOn.uniqueDiffWithinAt {s : Set E} {x} (hs : UniqueDiffOn 𝕜 s) (h : x ∈ s) :
    UniqueDiffWithinAt 𝕜 s x :=
  hs x h

theorem uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 univ x := by
  rw [uniqueDiffWithinAt_iff, tangentCone_univ]
  simp

theorem uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E) :=
  fun _ _ => uniqueDiffWithinAt_univ

theorem uniqueDiffOn_empty : UniqueDiffOn 𝕜 (∅ : Set E) :=
  fun _ hx => hx.elim

theorem UniqueDiffWithinAt.congr_pt (h : UniqueDiffWithinAt 𝕜 s x) (hy : x = y) :
    UniqueDiffWithinAt 𝕜 s y := hy ▸ h

end TVS

section Normed
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {x y : E} {s t : Set E}

theorem UniqueDiffWithinAt.mono_nhds (h : UniqueDiffWithinAt 𝕜 s x) (st : 𝓝[s] x ≤ 𝓝[t] x) :
    UniqueDiffWithinAt 𝕜 t x := by
  simp only [uniqueDiffWithinAt_iff] at *
  rw [mem_closure_iff_nhdsWithin_neBot] at h ⊢
  exact ⟨h.1.mono <| Submodule.span_mono <| tangentCone_mono_nhds st, h.2.mono st⟩

theorem UniqueDiffWithinAt.mono (h : UniqueDiffWithinAt 𝕜 s x) (st : s ⊆ t) :
    UniqueDiffWithinAt 𝕜 t x :=
  h.mono_nhds <| nhdsWithin_mono _ st

theorem uniqueDiffWithinAt_congr (st : 𝓝[s] x = 𝓝[t] x) :
    UniqueDiffWithinAt 𝕜 s x ↔ UniqueDiffWithinAt 𝕜 t x :=
  ⟨fun h => h.mono_nhds <| le_of_eq st, fun h => h.mono_nhds <| le_of_eq st.symm⟩

theorem uniqueDiffWithinAt_inter (ht : t ∈ 𝓝 x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x ↔ UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_congr <| (nhdsWithin_restrict' _ ht).symm

theorem UniqueDiffWithinAt.inter (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t ∈ 𝓝 x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x :=
  (uniqueDiffWithinAt_inter ht).2 hs

theorem uniqueDiffWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x ↔ UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_congr <| (nhdsWithin_restrict'' _ ht).symm

theorem UniqueDiffWithinAt.inter' (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t ∈ 𝓝[s] x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x :=
  (uniqueDiffWithinAt_inter' ht).2 hs

theorem uniqueDiffWithinAt_of_mem_nhds (h : s ∈ 𝓝 x) : UniqueDiffWithinAt 𝕜 s x := by
  simpa only [univ_inter] using uniqueDiffWithinAt_univ.inter h

theorem IsOpen.uniqueDiffWithinAt (hs : IsOpen s) (xs : x ∈ s) : UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_of_mem_nhds (IsOpen.mem_nhds hs xs)

theorem UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsOpen t) : UniqueDiffOn 𝕜 (s ∩ t) :=
  fun x hx => (hs x hx.1).inter (IsOpen.mem_nhds ht hx.2)

theorem IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 𝕜 s :=
  fun _ hx => IsOpen.uniqueDiffWithinAt hs hx

/-- The product of two sets of unique differentiability at points `x` and `y` has unique
differentiability at `(x, y)`. -/
theorem UniqueDiffWithinAt.prod {t : Set F} {y : F} (hs : UniqueDiffWithinAt 𝕜 s x)
    (ht : UniqueDiffWithinAt 𝕜 t y) : UniqueDiffWithinAt 𝕜 (s ×ˢ t) (x, y) := by
  rw [uniqueDiffWithinAt_iff] at hs ht ⊢
  rw [closure_prod_eq]
  refine ⟨?_, hs.2, ht.2⟩
  have : _ ≤ Submodule.span 𝕜 (tangentConeAt 𝕜 (s ×ˢ t) (x, y)) := Submodule.span_mono
    (union_subset (subset_tangentCone_prod_left ht.2) (subset_tangentCone_prod_right hs.2))
  rw [LinearMap.span_inl_union_inr, SetLike.le_def] at this
  exact (hs.1.prod ht.1).mono this

theorem UniqueDiffWithinAt.univ_pi (ι : Type*) [Finite ι] (E : ι → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] (s : ∀ i, Set (E i)) (x : ∀ i, E i)
    (h : ∀ i, UniqueDiffWithinAt 𝕜 (s i) (x i)) : UniqueDiffWithinAt 𝕜 (Set.pi univ s) x := by
  classical
  simp only [uniqueDiffWithinAt_iff, closure_pi_set] at h ⊢
  refine ⟨(dense_pi univ fun i _ => (h i).1).mono ?_, fun i _ => (h i).2⟩
  norm_cast
  simp only [← Submodule.iSup_map_single, iSup_le_iff, LinearMap.map_span, Submodule.span_le,
    ← mapsTo']
  exact fun i => (mapsTo_tangentCone_pi fun j _ => (h j).2).mono Subset.rfl Submodule.subset_span

theorem UniqueDiffWithinAt.pi (ι : Type*) [Finite ι] (E : ι → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] (s : ∀ i, Set (E i)) (x : ∀ i, E i)
    (I : Set ι) (h : ∀ i ∈ I, UniqueDiffWithinAt 𝕜 (s i) (x i)) :
    UniqueDiffWithinAt 𝕜 (Set.pi I s) x := by
  classical
  rw [← Set.univ_pi_piecewise_univ]
  refine UniqueDiffWithinAt.univ_pi ι E _ _ fun i => ?_
  by_cases hi : i ∈ I <;> simp [*, uniqueDiffWithinAt_univ]

/-- The product of two sets of unique differentiability is a set of unique differentiability. -/
theorem UniqueDiffOn.prod {t : Set F} (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t) :
    UniqueDiffOn 𝕜 (s ×ˢ t) :=
  fun ⟨x, y⟩ h => UniqueDiffWithinAt.prod (hs x h.1) (ht y h.2)

/-- The finite product of a family of sets of unique differentiability is a set of unique
differentiability. -/
theorem UniqueDiffOn.pi (ι : Type*) [Finite ι] (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] (s : ∀ i, Set (E i)) (I : Set ι)
    (h : ∀ i ∈ I, UniqueDiffOn 𝕜 (s i)) : UniqueDiffOn 𝕜 (Set.pi I s) :=
  fun x hx => UniqueDiffWithinAt.pi _ _ _ _ _ fun i hi => h i hi (x i) (hx i hi)

/-- The finite product of a family of sets of unique differentiability is a set of unique
differentiability. -/
theorem UniqueDiffOn.univ_pi (ι : Type*) [Finite ι] (E : ι → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] (s : ∀ i, Set (E i))
    (h : ∀ i, UniqueDiffOn 𝕜 (s i)) : UniqueDiffOn 𝕜 (Set.pi univ s) :=
  UniqueDiffOn.pi _ _ _ _ fun i _ => h i

end Normed

section RealNormed
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- In a real vector space, a convex set with nonempty interior is a set of unique
differentiability at every point of its closure. -/
theorem uniqueDiffWithinAt_convex {s : Set G} (conv : Convex ℝ s) (hs : (interior s).Nonempty)
    {x : G} (hx : x ∈ closure s) : UniqueDiffWithinAt ℝ s x := by
  rcases hs with ⟨y, hy⟩
  suffices y - x ∈ interior (tangentConeAt ℝ s x) by
    refine ⟨Dense.of_closure ?_, hx⟩
    simp [(Submodule.span ℝ (tangentConeAt ℝ s x)).eq_top_of_nonempty_interior'
        ⟨y - x, interior_mono Submodule.subset_span this⟩]
  rw [mem_interior_iff_mem_nhds]
  replace hy : interior s ∈ 𝓝 y := IsOpen.mem_nhds isOpen_interior hy
  apply mem_of_superset ((isOpenMap_sub_right x).image_mem_nhds hy)
  rintro _ ⟨z, zs, rfl⟩
  refine mem_tangentCone_of_openSegment_subset (Subset.trans ?_ interior_subset)
  exact conv.openSegment_closure_interior_subset_interior hx zs

/-- In a real vector space, a convex set with nonempty interior is a set of unique
differentiability. -/
theorem uniqueDiffOn_convex {s : Set G} (conv : Convex ℝ s) (hs : (interior s).Nonempty) :
    UniqueDiffOn ℝ s :=
  fun _ xs => uniqueDiffWithinAt_convex conv hs (subset_closure xs)

end RealNormed

section Real

theorem uniqueDiffOn_Ici (a : ℝ) : UniqueDiffOn ℝ (Ici a) :=
  uniqueDiffOn_convex (convex_Ici a) <| by simp only [interior_Ici, nonempty_Ioi]

theorem uniqueDiffOn_Iic (a : ℝ) : UniqueDiffOn ℝ (Iic a) :=
  uniqueDiffOn_convex (convex_Iic a) <| by simp only [interior_Iic, nonempty_Iio]

theorem uniqueDiffOn_Ioi (a : ℝ) : UniqueDiffOn ℝ (Ioi a) :=
  isOpen_Ioi.uniqueDiffOn

theorem uniqueDiffOn_Iio (a : ℝ) : UniqueDiffOn ℝ (Iio a) :=
  isOpen_Iio.uniqueDiffOn

theorem uniqueDiffOn_Icc {a b : ℝ} (hab : a < b) : UniqueDiffOn ℝ (Icc a b) :=
  uniqueDiffOn_convex (convex_Icc a b) <| by simp only [interior_Icc, nonempty_Ioo, hab]

theorem uniqueDiffOn_Ico (a b : ℝ) : UniqueDiffOn ℝ (Ico a b) :=
  if hab : a < b then
    uniqueDiffOn_convex (convex_Ico a b) <| by simp only [interior_Ico, nonempty_Ioo, hab]
  else by simp only [Ico_eq_empty hab, uniqueDiffOn_empty]

theorem uniqueDiffOn_Ioc (a b : ℝ) : UniqueDiffOn ℝ (Ioc a b) :=
  if hab : a < b then
    uniqueDiffOn_convex (convex_Ioc a b) <| by simp only [interior_Ioc, nonempty_Ioo, hab]
  else by simp only [Ioc_eq_empty hab, uniqueDiffOn_empty]

theorem uniqueDiffOn_Ioo (a b : ℝ) : UniqueDiffOn ℝ (Ioo a b) :=
  isOpen_Ioo.uniqueDiffOn

/-- The real interval `[0, 1]` is a set of unique differentiability. -/
theorem uniqueDiffOn_Icc_zero_one : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) :=
  uniqueDiffOn_Icc zero_lt_one

theorem uniqueDiffWithinAt_Ioo {a b t : ℝ} (ht : t ∈ Set.Ioo a b) :
    UniqueDiffWithinAt ℝ (Set.Ioo a b) t :=
  IsOpen.uniqueDiffWithinAt isOpen_Ioo ht

theorem uniqueDiffWithinAt_Ioi (a : ℝ) : UniqueDiffWithinAt ℝ (Ioi a) a :=
  uniqueDiffWithinAt_convex (convex_Ioi a) (by simp) (by simp)

theorem uniqueDiffWithinAt_Iio (a : ℝ) : UniqueDiffWithinAt ℝ (Iio a) a :=
  uniqueDiffWithinAt_convex (convex_Iio a) (by simp) (by simp)

/-- In one dimension, every point is either a point of unique differentiability, or isolated. -/
theorem uniqueDiffWithinAt_or_nhdsWithin_eq_bot (s : Set 𝕜) (x : 𝕜) :
    UniqueDiffWithinAt 𝕜 s x ∨ 𝓝[s \ {x}] x = ⊥ := by
  rcases eq_or_neBot (𝓝[s \ {x}] x) with h | h
  · exact Or.inr h
  refine Or.inl ⟨?_, ?_⟩
  · simp [tangentCone_eq_univ h]
  · simp only [mem_closure_iff_nhdsWithin_neBot]
    apply neBot_of_le (hf := h)
    exact nhdsWithin_mono _ diff_subset

end Real

end UniqueDiff
