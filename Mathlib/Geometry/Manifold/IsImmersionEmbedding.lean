/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.MSplits

/-! # Smooth immersions and embeddings

In this file, we define `C^k` immersions and embeddings between `C^k` manifolds.
The correct definition in the infinite-dimensional setting differs from the standard
finite-dimensional definition: we cannot prove the implication yet.

TODO complete this doc-string, once more details are clear.

## TODO
- the product of two immersions

-/

open scoped Manifold Topology ContDiff

open Function Set

-- XXX: does NontriviallyNormedField also work? Splits seems to require more...
variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : WithTop ℕ∞} [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N]

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

variable {f g : M → M'} {x : M}

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
def congr_of_eventuallyEq {x : M} (h : IsImmersionAt F I I' n f x) (h' : f =ᶠ[nhds x] g) :
    IsImmersionAt F I I' n g x := by
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

/-- If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an immersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'} {x' : M'}
    (h : IsImmersionAt F I J n f x) (h' : IsImmersionAt F' I' J' n g x') :
    IsImmersionAt (F × F') (I.prod I') (J.prod J') n (Prod.map f g) (x, x') :=
  sorry

theorem continuousWithinAt (h : IsImmersionAt F I I' n f x) : ContinuousWithinAt f h.domChart.source x := by
  -- TODO: follows from the local description...
  sorry

/-- A `C^k` immersion at `x` is continuous at `x`. -/
theorem continuousAt (h : IsImmersionAt F I I' n f x) : ContinuousAt f x :=
  h.continuousWithinAt.continuousAt (h.domChart.open_source.mem_nhds (mem_domChart_source h))

/-- A `C^k` immersion at `x` is `C^k` at `x`. -/
-- continuity follows since we're in a chart, on an open set;
-- smoothness follows since domChart and codChart are compatible with the maximal atlas
theorem contMDiffAt (h : IsImmersionAt F I I' n f x) : ContMDiffAt I I' n f x := by
  suffices ContMDiffWithinAt I I' n f h.domChart.source x from
    this.contMDiffAt <| h.domChart.open_source.mem_nhds (mem_domChart_source h)
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas (e := h.domChart) (e' := h.codChart)]
  · refine ⟨h.continuousWithinAt, ?_⟩
    have aux := h.writtenInCharts
    have : ContDiffWithinAt 𝕜 n ((h.codChart.extend I') ∘ f ∘ ↑(h.domChart.extend I).symm)
        (h.domChart.extend I).target ((h.domChart.extend I) x) := by
      -- apply a congr lemma, and prove this for the inclusion
      sorry
    apply this.mono
    -- is this true? in any case, want the lemma below
    -- have aux2 : (h.domChart.extend I).symm ⁻¹' h.domChart.source =
    --   (h.domChart.extend I).target := sorry
    simp only [mfld_simps, inter_comm]
    gcongr
    sorry -- is this true? need to think!
  · exact h.domChart_mem_maximalAtlas
  · exact codChart_mem_maximalAtlas h
  · exact mem_domChart_source h
  · exact mem_codChart_source h

-- These are required to argue that `Splits` composes.
variable [CompleteSpace E'] [CompleteSpace E] [CompleteSpace F]

variable [IsManifold I 1 M] [IsManifold I' 1 M']

/-- If `f` is a `C^k` immersion at `x`, then `mfderiv I I' f x` splits. -/
theorem msplitsAt {x : M} (h : IsImmersionAt F I I' n f x) : MSplitsAt I I' f x := by
  -- The local representative of f in the nice charts at x, as a continuous linear map.
  let rhs : E →L[𝕜] E' := h.equiv.toContinuousLinearMap.comp ((ContinuousLinearMap.id _ _).prod 0)
  have : rhs.Splits := by
    apply h.equiv.splits.comp
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy
      simp at hxy; exact hxy
    · have hrange : range ((ContinuousLinearMap.id 𝕜 E).prod (0 : E →L[𝕜] F)) =
          Set.prod (Set.univ) {0} := by
        sorry
      rw [hrange]
      exact isClosed_univ.prod isClosed_singleton
    · have hrange : LinearMap.range ((ContinuousLinearMap.id 𝕜 E).prod (0 : E →L[𝕜] F)) =
          Submodule.prod ⊤ ⊥ := by
        -- rw [LinearMap.range_prod_eq] applies, but only partially
        sorry
      simp_rw [hrange]
      -- want: ClosedComplemented.prod, then use this for top and bottom
      sorry
  -- Since rhs is linear, it is smooth - and it equals its own fderiv.
  have : MSplitsAt (𝓘(𝕜, E)) (𝓘(𝕜, E')) rhs (I (h.domChart x)) := by
    refine ⟨rhs.differentiable.mdifferentiable.mdifferentiableAt, ?_⟩
    rw [mfderiv_eq_fderiv, rhs.fderiv]
    exact this
  have : MSplitsAt (𝓘(𝕜, E)) (𝓘(𝕜, E'))
      ((h.codChart.extend I') ∘ f ∘ (h.domChart.extend I).symm) ((h.domChart.extend I x)) := by
    apply this.congr
    apply Set.EqOn.eventuallyEq_of_mem h.writtenInCharts
    simp only [PartialHomeomorph.extend, PartialEquiv.trans_target, ModelWithCorners.target_eq,
      ModelWithCorners.toPartialEquiv_coe_symm, Filter.inter_mem_iff]
    -- This is close to true... but perhaps the neighbourhood in my definition is wrong!
    constructor <;> sorry

  have : MSplitsAt I (𝓘(𝕜, E'))
      ((h.codChart.extend I') ∘ f ∘ (h.domChart.extend I).symm ∘ (h.domChart.extend I)) x :=
    this.comp (MSplitsAt.extend h.domChart_mem_maximalAtlas (mem_chart_source _ x))
  have : MSplitsAt I (𝓘(𝕜, E')) ((h.codChart.extend I') ∘ f) x := by
    apply this.congr
    -- on some nbhd, an extended chart and its inverse cancel
    sorry
  have : MSplitsAt I I' ((h.codChart.extend I').symm ∘ (h.codChart.extend I') ∘ f) x := by
    refine MSplitsAt.comp ?_ this
    exact MSplitsAt.extend_symm h.codChart_mem_maximalAtlas (mem_chart_source _ (f x))
  apply this.congr
  sorry -- extended chart and its inverse cancel

/-- `f` is an immersion at `x` iff `mfderiv I I' f x` splits. -/
theorem _root_.isImmersionAt_iff_msplitsAt {x : M} :
    IsImmersionAt F I I' n f x ↔ MSplitsAt I I' f x := by
  refine ⟨fun h ↦ h.msplitsAt, fun h ↦ ?_⟩
  -- This direction uses the inverse function theorem: this is the hard part!
  sorry

/-- If `f` is an immersion at `x` and `g` is an immersion at `g x`,
then `g ∘ f` is an immersion at `x`. -/
def comp [CompleteSpace F'] {g : M' → N}
    (hg : IsImmersionAt F' I' J n g (f x)) (hf : IsImmersionAt F I I' n f x) :
    IsImmersionAt (F × F') I J n (g ∘ f) x := by
  --rw [isImmersionAt_iff_msplitsAt] at hf hg ⊢
  sorry --exact hg.comp hf

/-- If `f` is a `C^k` immersion at `x`, then `mfderiv x` is injective. -/
theorem mfderiv_injective {x : M} (h : IsImmersionAt F I I' n f x) : Injective (mfderiv I I' f x) :=
  h.msplitsAt.mfderiv_injective
--   /- Outline of proof:
--   (1) `mfderiv` is injective iff `fderiv (writtenInExtChart) is injective`
--   I have proven this for Sard's theorem; this depends on some sorries not in mathlib yet
--   (2) the injectivity of `fderiv (writtenInExtChart)` is independent of the choice of chart
--   in the atlas (in fact, even the rank of the resulting map is),
--   as transition maps are linear equivalences.
--   (3) (·, 0) has injective `fderiv` --- since it's linear, thus its own derivative. -/
--   sorry

/- If `M` is finite-dimensional, `f` is `C^n` at `x` and `mfderiv x` is injective,
then `f` is immersed at `x`.
Some sources call this condition `f is infinitesimally injective at x`. -/
def of_finiteDimensional_of_contMDiffAt_of_mfderiv_injective [FiniteDimensional 𝕜 E] {x : M}
    (hf : ContMDiffAt I I' n f x) (hf' : Injective (mfderiv I I' f x)) (hn : 1 ≤ n) :
    IsImmersionAt F I I' n f x := by
  rw [isImmersionAt_iff_msplitsAt]
  refine ⟨hf.mdifferentiableAt hn, ?_⟩
  convert ContinuousLinearMap.Splits.of_injective_of_finiteDimensional_dom hf'
  show FiniteDimensional 𝕜 E; assumption

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

/-- If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an immersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'}
    (h : IsImmersion F I J n f) (h' : IsImmersion F' I' J' n g) :
    IsImmersion (F × F') (I.prod I') (J.prod J') n (Prod.map f g) :=
  fun ⟨x, x'⟩ ↦ (h x).prodMap (h' x')

omit [IsManifold I n M] [IsManifold I' n M'] in
/-- If `f = g` and `f` is an immersion, so is `g`. -/
theorem congr (h : IsImmersion F I I' n f) (heq : f = g) : IsImmersion F I I' n g :=
  fun x ↦ (h x).congr_of_eventuallyEq heq.eventuallyEq

/-- A `C^k` immersion is `C^k`. -/
theorem contMDiff (h : IsImmersion F I I' n f) : ContMDiff I I' n f := fun x ↦ (h x).contMDiffAt

-- These are required to argue that `Splits` composes.
variable [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F] [CompleteSpace F']
variable [IsManifold I 1 M] [IsManifold I' 1 M']

/-- If `f` is a `C^k` immersion, each differential `mfderiv x` is injective. -/
theorem mfderiv_injective (h : IsImmersion F I I' n f) (x : M) : Injective (mfderiv I I' f x) :=
  (h x).mfderiv_injective

/- If `M` is finite-dimensional, `f` is `C^k` and each `mfderiv x` is injective,
then `f` is a `C^k` immersion. -/
theorem of_mfderiv_injective [FiniteDimensional 𝕜 E] (hf : ContMDiff I I' n f)
    (hf' : ∀ x, Injective (mfderiv I I' f x)) (hn : 1 ≤ n) : IsImmersion F I I' n f :=
  fun x ↦ IsImmersionAt.of_finiteDimensional_of_contMDiffAt_of_mfderiv_injective (hf x) (hf' x) hn

/-- The composition of two immersions is an immersion. -/
def comp [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    {g : M' → N} (hg : IsImmersion F' I' J n g) (hf : IsImmersion F I I' n f) :
    IsImmersion (F × F') I J n (g ∘ f) :=
  fun x ↦ (hg (f x)).comp (hf x)

end IsImmersion

open Topology

variable (F I I' n) in
/-- A `C^k` map `f : M → M'` is a smooth `C^k` embedding if it is a topological embedding
and a `C^k` immersion. -/
def IsSmoothEmbedding (f : M → M') : Prop := IsImmersion F I I' n f ∧ IsEmbedding f

namespace IsSmoothEmbedding

variable {f : M → M'}

theorem contMDiff (h : IsSmoothEmbedding F I I' n f) : ContMDiff I I' n f := h.1.contMDiff

omit [IsManifold I n M] [IsManifold I' n M'] in
theorem isImmersion (h : IsSmoothEmbedding F I I' n f) : IsImmersion F I I' n f := h.1

omit [IsManifold I n M] [IsManifold I' n M'] in
theorem isEmbedding (h : IsSmoothEmbedding F I I' n f) : IsEmbedding f := h.2

variable [IsManifold I 1 M] [IsManifold I' 1 M'] in
def of_mfderiv_injective_of_compactSpace_of_T2Space
    [FiniteDimensional 𝕜 E] [CompleteSpace E'] [CompleteSpace F] [CompactSpace M] [T2Space M']
    (hf : ContMDiff I I' n f) (hf' : ∀ x, Injective (mfderiv I I' f x))
    (hf'' : Injective f) (hn : 1 ≤ n) : IsSmoothEmbedding F I I' n f := by
  have := FiniteDimensional.complete (𝕜 := 𝕜) E
  exact ⟨.of_mfderiv_injective hf hf' hn, (hf.continuous.isClosedEmbedding hf'').isEmbedding⟩

/-- The composition of two smooth embeddings is a smooth embedding. -/
def comp [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F] [CompleteSpace F']
    {g : M' → N} (hg : IsSmoothEmbedding F' I' J n g) (hf : IsSmoothEmbedding F I I' n f) :
    IsSmoothEmbedding (F × F') I J n (g ∘ f) :=
  ⟨hg.1.comp hf.1, hg.2.comp hf.2⟩

end IsSmoothEmbedding
