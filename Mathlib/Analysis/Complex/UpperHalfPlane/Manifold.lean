/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Geometry.Manifold.MFDeriv.Basic

#align_import analysis.complex.upper_half_plane.manifold from "leanprover-community/mathlib"@"57f9349f2fe19d2de7207e99b0341808d977cdcf"

/-!
# Manifold structure on the upper half plane.

In this file we define the complex manifold structure on the upper half-plane.
-/

open Set Filter

open scoped UpperHalfPlane Manifold Topology

namespace UpperHalfPlane

noncomputable instance : ChartedSpace ℂ ℍ :=
  UpperHalfPlane.openEmbedding_coe.singletonChartedSpace

instance : SmoothManifoldWithCorners 𝓘(ℂ) ℍ :=
  UpperHalfPlane.openEmbedding_coe.singleton_smoothManifoldWithCorners 𝓘(ℂ)

/-- The inclusion map `ℍ → ℂ` is a smooth map of manifolds. -/
theorem smooth_coe : Smooth 𝓘(ℂ) 𝓘(ℂ) ((↑) : ℍ → ℂ) := fun _ => contMDiffAt_extChartAt
#align upper_half_plane.smooth_coe UpperHalfPlane.smooth_coe

/-- The inclusion map `ℍ → ℂ` is a differentiable map of manifolds. -/
theorem mdifferentiable_coe : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((↑) : ℍ → ℂ) :=
  smooth_coe.mdifferentiable
#align upper_half_plane.mdifferentiable_coe UpperHalfPlane.mdifferentiable_coe

local notation "↑ₕ" f => f ∘ (PartialHomeomorph.symm
          (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe))

lemma MDifferentiable_iff_extension_DifferentiableOn (f : ℍ → ℂ) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ↔
    DifferentiableOn ℂ (↑ₕf) (UpperHalfPlane.coe '' ⊤) := by
  constructor
  · intro h
    rw [MDifferentiable] at h
    intro z hz
    simp only [Set.top_eq_univ, Set.image_univ, Set.mem_range] at hz
    obtain ⟨y, _, hy⟩ := hz
    have H := h y
    rw [mdifferentiableAt_iff] at H
    simp only [writtenInExtChartAt, extChartAt, PartialHomeomorph.extend,
      PartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_source,
      PartialHomeomorph.singletonChartedSpace_chartAt_eq, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, PartialEquiv.refl_coe, OpenEmbedding.toPartialHomeomorph_source,
      PartialHomeomorph.coe_coe_symm, CompTriple.comp_eq, modelWithCornersSelf_coe, range_id,
      PartialHomeomorph.toFun_eq_coe, OpenEmbedding.toPartialHomeomorph_apply, top_eq_univ,
      image_univ] at *
    apply H.2.mono (Set.subset_univ _)
  · intro h
    rw [MDifferentiable]
    intro z
    have ha : UpperHalfPlane.coe '' ⊤ ∈ 𝓝 ↑z := by
      exact IsOpenMap.image_mem_nhds (OpenEmbedding.isOpenMap openEmbedding_coe)
        (by simp only [top_eq_univ, univ_mem])
    constructor
    · rw [continuousWithinAt_univ, PartialHomeomorph.continuousAt_iff_continuousAt_comp_right
        (e := (PartialHomeomorph.symm (OpenEmbedding.toPartialHomeomorph
        UpperHalfPlane.coe openEmbedding_coe)))]
      · exact ContinuousOn.continuousAt (h.continuousOn) ha
      · simp only [PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_target,
        OpenEmbedding.toPartialHomeomorph_source, mem_univ]
    · simp only [DifferentiableWithinAtProp, modelWithCornersSelf_coe,
      PartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_source,
      PartialHomeomorph.singletonChartedSpace_chartAt_eq, PartialHomeomorph.refl_apply,
      OpenEmbedding.toPartialHomeomorph_source, CompTriple.comp_eq, modelWithCornersSelf_coe_symm,
      preimage_univ, range_id, inter_self, OpenEmbedding.toPartialHomeomorph_apply, id_eq,
      differentiableWithinAt_univ]
      exact DifferentiableOn.differentiableAt (s := UpperHalfPlane.coe '' ⊤) h ha

end UpperHalfPlane
