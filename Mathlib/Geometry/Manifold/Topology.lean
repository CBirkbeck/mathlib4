/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

/-!
# Topological property of topological or smooth manifolds
In this file, we prove a few basic topological properties of manifolds.
Let $M$ be a topological manifold (not necessarily `C^n` or smooth).
* `locallyCompact_of_finiteDimensional_of_boundaryless`: If `M` is finite-dimensional, boundaryless
  and the underlying field `𝕜` is locally compact (such as ℝ, ℂ or the p-adic numbers),
  `M` is locally compact.
* `sigmaCompact_of_finiteDimensional_of_secondCountable_of_boundaryless`: In particular,
  if `M` is also secound countable, it is sigma-compact.
* `locallyPathConnected`, `locallyConnected`: A real manifold (without boundary?!) is
  locally path-connected and locally connected.
* `connected_iff_pathConnected`: In particular, `M` is path-connected if and only if it is connected.

**TODO:**
* adapt the argument to include manifolds with boundary; this probably requires a
stronger definition of boundary to show local compactness of the half-spaces
-/

open Set Topology

section Compactness
variable
  {E : Type*} {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- Let M be a topological manifold over the field 𝕜.
  [HasGroupoid M (contDiffGroupoid 0 I)]

/-- Auxiliary lemma for local compactness of `M`. -/
lemma localCompactness_aux [LocallyCompactSpace 𝕜] [FiniteDimensional 𝕜 E]
    (hI : ModelWithCorners.Boundaryless I) {x : M} {n : Set M} (hn : n ∈ 𝓝 x) :
    ∃ s : Set M, s∈ 𝓝 x ∧ s ⊆ n ∧ IsCompact s  := by
  -- Assume `n` is contained in some chart at x. (Choose the distinguished chart from our atlas.)
  let chart := chartAt H x
  let echart := extChartAt I x
  have hn : n ∩ echart.source ∈ 𝓝 x := Filter.inter_mem hn
    (chart.extend_source_mem_nhds _ (mem_chart_source H x))

  -- Apply the chart to obtain a neighbourhood `n'` of $echart x ∈ E$.
  let x' := echart x
  let n' := echart '' (n ∩ echart.source)
  have hn' : n' ∈ 𝓝 x' := by
    let r := chart.map_extend_nhds I (mem_chart_source H x)
    rw [I.range_eq_univ, nhdsWithin_univ, ← extChartAt] at r
    exact r ▸ Filter.image_mem_map hn
  -- Since 𝕜 is locally compact, so is E. In particular, x' has a compact neighbourhood s' ⊆ n'.
  have : ProperSpace E := FiniteDimensional.proper 𝕜 E
  have : LocallyCompactSpace E := by infer_instance
  rcases this.local_compact_nhds x' n' hn' with ⟨s', hs', hsn', hscompact⟩
  -- Transport back: s := echart ⁻¹ (s') is a compact neighbourhood of x.
  let s := echart.symm '' s'
  have hstarget : s' ⊆ echart.target := calc s'
    _ ⊆ n' := hsn'
    _ ⊆ echart '' (echart.source) := image_subset _ (inter_subset_right _ _)
    _ ⊆ echart.target := LocalEquiv.map_source'' echart
  refine ⟨s, ?_, ?_, ?_⟩
  · -- FIXME: (how to) avoid the additional rewrites?
    let r := chart.extend_image_mem_nhds_symm I hs' hstarget
    have : LocalHomeomorph.extend chart I = echart := rfl
    rw [this, ← image_eta, (extChartAt_to_inv I x)] at r
    apply r
  · calc s
      _ ⊆ echart.symm '' n' := image_subset echart.symm hsn'
      _ = (echart.symm ∘ echart) '' (n ∩ echart.source) := by rw [image_comp]
      _ = n ∩ echart.source := by
        rw [extChartAt_source]
        apply chart.extend_left_inv' _ (inter_subset_right _ _)
      _ ⊆ n := inter_subset_left _ _
  · apply hscompact.image_of_continuousOn ((chart.continuousOn_extend_symm I).mono hstarget)

/-- A finite-dimensional manifold without boundary modelled on a locally compact field
  (such as ℝ, ℂ or the p-adic numbers) is locally compact. -/
-- FIXME: make this an instance!
lemma Manifold.locallyCompact_of_finiteDimensional_of_boundaryless
    [LocallyCompactSpace 𝕜] [FiniteDimensional 𝕜 E] (hI : ModelWithCorners.Boundaryless I) :
    LocallyCompactSpace M := by
  exact { local_compact_nhds := fun x n hn ↦ localCompactness_aux I hI hn }

open TopologicalSpace
/-- A finite-dimensional second-countable manifold without boundary
  modelled on a locally compact field (such as ℝ, ℂ or the p-adic numbers) is σ-compact. -/
-- FIXME: make this an instance!
lemma Manifold.sigmaCompact_of_finiteDimensional_of_secondCountable_of_boundaryless
    [SecondCountableTopology M] [LocallyCompactSpace 𝕜] [FiniteDimensional 𝕜 E]
  (hI : ModelWithCorners.Boundaryless I) : SigmaCompactSpace M := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional_of_boundaryless I hI
  apply sigmaCompactSpace_of_locally_compact_second_countable
end Compactness

section Real
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- Let M be a real topological manifold.
  [HasGroupoid M (contDiffGroupoid 0 I)]

lemma locallyPathConnected_aux {x : M} {n : Set M} (hn: n ∈ 𝓝 x) :
    ∃ s : Set M, IsOpen s ∧ x ∈ s ∧ s ⊆ n ∧ IsPathConnected s := by
  sorry

/-- A real manifold is locally path-connected. -/
-- FIXME: make this an instance?
lemma Manifold.locallyPathConnected : LocPathConnectedSpace M := by
  have aux : ∀ (x : M), Filter.HasBasis (𝓝 x) (fun s ↦ s ∈ 𝓝 x ∧ IsPathConnected s) id := by
    intro x
    rw [Filter.hasBasis_iff]
    intro n
    refine ⟨fun hn ↦ ?_, fun ⟨i, ⟨hiopen, _, _⟩, hin⟩ ↦ Filter.mem_of_superset hiopen hin⟩
    obtain ⟨s, hsopen, hxs, hsn, hspconn⟩ := locallyPathConnected_aux hn
    exact ⟨s, ⟨hsopen.mem_nhds hxs, hspconn⟩, hsn⟩
  exact { path_connected_basis := aux }

-- TODO: does a path-connected space admit an open connected basis??

-- FIXME: make this an instance?
lemma LocallyConnected.ofLocallyPathConnected {X : Type*} [TopologicalSpace X]
    [hx: LocPathConnectedSpace X] : LocallyConnectedSpace X := by
  have : ∀ (x : X), Filter.HasBasis (𝓝 x) (fun s ↦ s ∈ 𝓝 x ∧ IsPathConnected s) id :=
    LocPathConnectedSpace.path_connected_basis (X := X)
  have aux : ∀ (x : X), Filter.HasBasis (𝓝 x) (fun s ↦ s ∈ 𝓝 x ∧ IsConnected s) id := by
    -- follows from this and IsPathConnected.isConnected
    intro x
    let h := this x
    rw [Filter.hasBasis_iff] at h ⊢
    intro t
    constructor
    · intro hyp
      obtain ⟨i, ⟨hin, hipconn⟩ , stuff⟩ := (h t).mp hyp
      refine ⟨i, ⟨hin, hipconn.isConnected⟩, stuff⟩
    · exact fun ⟨i, ⟨hin, hiconn⟩, hit⟩ ↦ Filter.mem_of_superset hin hit
  -- TODO: doesn't work, I need a basis of open **connected** sets.
  sorry --exact { open_connected_basis := aux }

/-- A real manifold is locally connected. -/
lemma Manifold.locallyConnected : LocallyConnectedSpace M := by
  have : LocPathConnectedSpace M := locallyPathConnected
  exact LocallyConnected.ofLocallyPathConnected

lemma Manifold.connected_iff_pathConnected : PathConnectedSpace M ↔ ConnectedSpace M := by
  have : LocPathConnectedSpace M := locallyPathConnected
  exact pathConnectedSpace_iff_connectedSpace

end Real
