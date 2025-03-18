/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Defs

/-! # Smooth immersions and embeddings

In this file, we define `C^k` immersions and embeddings between `C^k` manifolds.
The correct definition in the infinite-dimensional setting differs from the standard
finite-dimensional definition: we cannot prove the implication yet.

TODO complete this doc-string, once more details are clear.

-/

open scoped Manifold Topology ContDiff

open Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N'] {n : WithTop ℕ∞}

-- XXX: should the next three definitions be a class instead?
-- Are these slice charts canonical enough that we want the typeclass system to kick in?

variable (F I I' n) in
/-- `f : M → N` is a `C^k` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.

XXX: why in `maximalAtlas` and not merely atlas? to given ourselves extra freedom?
-/
def IsImmersionAt (f : M → M') (x : M) : Prop :=
  ∃ equiv : (E × F) ≃L[𝕜] E',
  ∃ domChart : PartialHomeomorph M H, ∃ codChart : PartialHomeomorph M' H',
    x ∈ domChart.source ∧ f x ∈ codChart.source ∧
    domChart ∈ IsManifold.maximalAtlas I n M ∧
    codChart ∈ IsManifold.maximalAtlas I' n M' ∧
    EqOn ((codChart.extend I') ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target

namespace IsImmersionAt

variable {f : M → M'} {x : M}

noncomputable def equiv (h : IsImmersionAt F I I' n f x) : (E × F) ≃L[𝕜] E' :=
  Classical.choose h

noncomputable def domChart (h : IsImmersionAt F I I' n f x) : PartialHomeomorph M H :=
  Classical.choose (Classical.choose_spec h)

noncomputable def codChart (h : IsImmersionAt F I I' n f x) : PartialHomeomorph M' H' :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec h))

noncomputable def mem_domChart_source (h : IsImmersionAt F I I' n f x) : x ∈ h.domChart.source :=
  (Classical.choose_spec ((Classical.choose_spec (Classical.choose_spec h)))).1

noncomputable def mem_codChart_source (h : IsImmersionAt F I I' n f x) : f x ∈ h.codChart.source :=
  (Classical.choose_spec ((Classical.choose_spec (Classical.choose_spec h)))).2.1

noncomputable def domChart_mem_maximalAtlas (h : IsImmersionAt F I I' n f x) :
    h.domChart ∈ IsManifold.maximalAtlas I n M :=
  (Classical.choose_spec ((Classical.choose_spec (Classical.choose_spec h)))).2.2.1

noncomputable def codChart_mem_maximalAtlas (h : IsImmersionAt F I I' n f x) :
    h.codChart ∈ IsManifold.maximalAtlas I' n M' :=
  (Classical.choose_spec ((Classical.choose_spec (Classical.choose_spec h)))).2.2.2.1

noncomputable def writtenInCharts (h : IsImmersionAt F I I' n f x) :
    EqOn ((h.codChart.extend I') ∘ f ∘ (h.domChart.extend I).symm) (h.equiv ∘ (·, 0))
      (h.domChart.extend I).target :=
  (Classical.choose_spec ((Classical.choose_spec (Classical.choose_spec h)))).2.2.2.2

/-- If `f` is an immersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is an immersion at `x`. -/
def congr_of_eventuallyEq {f g : M → M'} {x : M}
    (h : IsImmersionAt F I I' n f x) (h' : f =ᶠ[nhds x] g) : IsImmersionAt F I I' n g x := by
  choose s hxs hfg using h'.exists_mem
  -- TODO: need to shrink h.domChart until its source is contained in s
  use h.equiv, h.domChart, h.codChart
  refine ⟨mem_domChart_source h, ?_, h.domChart_mem_maximalAtlas, h.codChart_mem_maximalAtlas, ?_⟩
  · exact hfg (mem_of_mem_nhds hxs) ▸ mem_codChart_source h
  · have missing : EqOn ((h.codChart.extend I') ∘ g ∘ (h.domChart.extend I).symm)
        ((h.codChart.extend I') ∘ f ∘ (h.domChart.extend I).symm) (h.domChart.extend I).target := by
      -- after shrinking, this will be true
      sorry
    exact EqOn.trans missing h.writtenInCharts

/-- A `C^k` immersion at `x` is `C^k` at `x`. -/
-- continuity follows since we're in a chart, on an open set;
-- smoothness follows since domChart and codChart are compatible with the maximal atlas
theorem contMDiffAt (h : IsImmersionAt F I I' n f x) : ContMDiffAt I I' n f x := sorry

/-- If `f` is a `C^k` immersion at `x`, then `mfderiv x` is injective. -/
theorem mfderiv_injective {f : M → M'} {x : M}
    (h : IsImmersionAt F I I' n f x) : Injective (mfderiv I I' f x) :=
  /- Outline of proof:
  (1) `mfderiv` is injective iff `fderiv (writtenInExtChart) is injective`
  I have proven this for Sard's theorem; this depends on some sorries not in mathlib yet
  (2) the injectivity of `fderiv (writtenInExtChart)` is independent of the choice of chart
  in the atlas (in fact, even the rank of the resulting map is),
  as transition maps are linear equivalences.
  (3) (·, 0) has injective `fderiv` --- since it's linear, thus its own derivative. -/
  sorry

/- If `M` is finite-dimensional and `mfderiv x` is injective, then `f` is immersed at `x`.
Some sources call this condition `f is infinitesimally injective at x`. -/
def of_mfderiv_injective [FiniteDimensional 𝕜 E] {f : M → M'} {x : M}
    (hf : Injective (mfderiv I I' f x)) : IsImmersionAt F I I' n f x :=
  -- (1) if mfderiv I I' f x is injective, the same holds in a neighbourhood of x
  -- In particular, mfderiv I I' f x has (locally) constant rank: this suffices
  -- (2) If mfderiv I I' f x has constant rank for all x in a neighbourhood of x,
  -- then f is immersion at x.
  -- This step requires the inverse function theorem (and possibly shrinking the neighbourhood).
  sorry

end IsImmersionAt

variable (F I I' n) in
/-- `f : M → N` is a `C^k` immersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `u ↦ (u, 0)`.

In other words, `f` is an immersion at each `x ∈ M`.
-/
def IsImmersion (f : M → M')  : Prop := ∀ x, IsImmersionAt F I I' n f x

namespace IsImmersion

variable {f g : M → M'}

/-- If `f` is an immersion, it is an immersion at each point. -/
def isImmersionAt (h : IsImmersion F I I' n f) (x : M) : IsImmersionAt F I I' n f x := h x

/-- If `f` is a `C^k` immersion, there is a single equivalence with the properties we want. -/
-- Actually, is this true? If I'm allowed to tweak the model at every point, yes;
-- otherwise maybe not? But I don't seem to care about this, in fact...
noncomputable def foo [Nonempty M] (h : IsImmersion F I I' n f) :
    ∃ equiv : (E × F) ≃L[𝕜] E',
    ∃ domCharts : M → PartialHomeomorph M H, ∃ codCharts : M → PartialHomeomorph M' H',
    ∀ x, x ∈ (domCharts x).source ∧ ∀ x, f x ∈ (codCharts x).source ∧
    ∀ x, (domCharts x) ∈ IsManifold.maximalAtlas I n M ∧
    ∀ x, (codCharts x) ∈ IsManifold.maximalAtlas I' n M' ∧
    ∀ x, EqOn (((codCharts x).extend I') ∘ f ∘ ((domCharts x).extend I).symm) (equiv ∘ (·, 0))
      ((domCharts x).extend I).target := by
  inhabit M
  use (h Inhabited.default).equiv
  -- What's the math proof?
  sorry

/-- If `f = g` and `f` is an immersion, so is `g`. -/
theorem congr (h : IsImmersion F I I' n f) (heq : f = g) : IsImmersion F I I' n g :=
  fun x ↦ (h x).congr_of_eventuallyEq heq.eventuallyEq

/-- A `C^k` immersion is `C^k`. -/
theorem contMDiff (h : IsImmersion F I I' n f) : ContMDiff I I' n f := fun x ↦ (h x).contMDiffAt

/- If `M` is finite-dimensional, `f` is `C^k` and each `mfderiv x` is injective,
then `f` is a `C^k` immersion. -/
def of_mfderiv_injective [FiniteDimensional 𝕜 E] {f : M → M'}
    (hf : ContMDiff I I' n f) (hf' : ∀ x, Injective (mfderiv I I' f x)) : IsImmersion F I I' n f :=
  -- TODO: glue the equivalences/make a type parameters, otherwise easy from the above
  sorry

end IsImmersion

open Topology

variable (F I I' n) in
/-- A `C^k` map `f : M → M'` is a smooth `C^k` embedding if it is a topological embedding
and a `C^k` immersion. -/
def IsSmoothEmbedding (f : M → M') : Prop := IsImmersion F I I' n f ∧ IsEmbedding f

namespace IsSmoothEmbedding

variable {f : M → M'}

theorem contMDiff (h : IsSmoothEmbedding F I I' n f) : ContMDiff I I' n f := h.1.contMDiff

theorem isImmersion (h : IsSmoothEmbedding F I I' n f) : IsImmersion F I I' n f := h.1

theorem isEmbedding (h : IsSmoothEmbedding F I I' n f) : IsEmbedding f := h.2

def of_mfderiv_injective_of_compactSpace_of_T2Space
    [FiniteDimensional 𝕜 E] [CompactSpace M] [T2Space M'] {f : M → M'}
    (hf : ContMDiff I I' n f) (hf' : ∀ x, Injective (mfderiv I I' f x)) (hf'' : Injective f) :
    IsSmoothEmbedding F I I' n f :=
  ⟨.of_mfderiv_injective hf hf', (hf.continuous.isClosedEmbedding hf'').isEmbedding⟩

end IsSmoothEmbedding
