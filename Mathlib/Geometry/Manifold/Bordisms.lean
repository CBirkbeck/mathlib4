/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.InteriorBoundary

/-!
# Unoriented bordism theory

In this file, we sketch the beginnings of unoriented bordism theory.
Not all of this might end up in mathlib already (depending on how many pre-requisites are missing),
but a fair number of pieces already can be upstreamed!

-/

/-
Missing API for this to work nicely:
- add disjoint union of top. spaces and induced maps: mathlib has this
- define the disjoint union of smooth manifolds, and the associated maps: show they are smooth
(perhaps prove as abstract nonsense? will see!)

- then: complete definition of unoriented cobordisms; complete constructions I had
- fight DTT hell: why is the product with an interval not recognised?

- define the bordism relation/how to define the set of equivalence classes?
equivalences work nicely in the standard design... that's a "how to do X in Lean" question
- postponed: transitivity of the bordism relation (uses the collar neighbourhood theorem)

- define induced maps between bordism groups (on singular n-manifolds is easy and done)
- functoriality: what exactly do I have to show? also DTT question

- prove some of the easy axioms of homology... perhaps all of it?
- does mathlib have a class "extraordinary homology theory"? this could be an interesting instance...
-/

open scoped Manifold
open Metric (sphere)
open FiniteDimensional Set

noncomputable section

-- Pre-requisite: the interval `Icc x y has boundary {x, y}`, and related results.
-- TODO: move to `Instances/Real`
section BoundaryIntervals

variable {x y : ℝ} [hxy : Fact (x < y)]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [BoundarylessManifold I M]

/-- A product `M × [x,y]` has boundary `M × {x,y}`. -/
lemma boundary_product : (I.prod (𝓡∂ 1)).boundary (M × Icc x y) = Set.prod univ {X, Y} := by
  have : (𝓡∂ 1).boundary (Icc x y) = {X, Y} := by rw [boundary_IccManifold]
  rw [I.boundary_of_boundaryless_left]
  rw [this]

end BoundaryIntervals

-- Let M, M' and W be smooth manifolds.
variable {E E' E'' E''' H H' H'' H''' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E'']  [NormedSpace ℝ E'']
  [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H''] [TopologicalSpace H''']

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A **singular `n`-manifold** on a topological space `X` consists of a
closed smooth `n`-manifold `M` and a continuous map `f : M → X`. -/
structure SingularNManifold (X : Type*) [TopologicalSpace X] (n : ℕ)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [SmoothManifoldWithCorners I M]
    [CompactSpace M] [BoundarylessManifold I M] [FiniteDimensional ℝ E] where
  [hdim : Fact (finrank ℝ E = n)]
  /-- The underlying map `M → X` of a singular `n`-manifold `(M,f)` on `X` -/
  f : M → X
  hf : Continuous f

namespace SingularNManifold

-- We declare these variables *after* the definition above, so `SingularNManifold` can have
-- its current order of arguments.
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {I' : ModelWithCorners ℝ E' H'} [SmoothManifoldWithCorners I' M'] {n : ℕ}
  [BoundarylessManifold I M] [CompactSpace M] [FiniteDimensional ℝ E]
  [BoundarylessManifold I' M'] [CompactSpace M'] [FiniteDimensional ℝ E']

/-- If `M` is `n`-dimensional and closed, it is a singular `n`-manifold over itself. -/
noncomputable def refl (hdim : finrank ℝ E = n) : SingularNManifold M n M I where
  hdim := Fact.mk hdim
  f := id
  hf := continuous_id

/-- A map of topological spaces induces a corresponding map of singular n-manifolds. -/
-- This is part of proving functoriality of the bordism groups.
noncomputable def map [Fact (finrank ℝ E = n)] (s : SingularNManifold X n M I)
    {φ : X → Y} (hφ : Continuous φ) : SingularNManifold Y n M I where
  f := φ ∘ s.f
  hf := hφ.comp s.hf

@[simp]
lemma map_f [Fact (finrank ℝ E = n)]
    (s : SingularNManifold X n M I) {φ : X → Y} (hφ : Continuous φ) : (s.map hφ).f = φ ∘ s.f :=
  rfl

/-- If `(M', f)` is a singular `n`-manifold on `X` and `M'` another `n`-dimensional smooth manifold,
a smooth map `φ : M → M'` induces a singular `n`-manifold structore on `M`. -/
noncomputable def comap [Fact (finrank ℝ E = n)] [Fact (finrank ℝ E' = n)]
    (s : SingularNManifold X n M' I')
    {φ : M → M'} (hφ : Smooth I I' φ) : SingularNManifold X n M I where
  f := s.f ∘ φ
  hf := s.hf.comp hφ.continuous

@[simp]
lemma comap_f [Fact (finrank ℝ E = n)] [Fact (finrank ℝ E' = n)] (s : SingularNManifold X n M' I')
    {φ : M → M'} (hφ : Smooth I I' φ) : (s.comap hφ).f = s.f ∘ φ :=
  rfl

/-- The canonical singular `n`-manifold associated to the empty set (seen as an `n`-dimensional
manifold, i.e. modelled on an `n`-dimensional space). -/
def empty [Fact (finrank ℝ E = n)] [IsEmpty M] : SingularNManifold X n M I where
  f := fun x ↦ (IsEmpty.false x).elim
  hf := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (IsEmpty.false x).elim

/-- An `n`-dimensional manifold induces a singular `n`-manifold on the one-point space. -/
def trivial [Fact (finrank ℝ E = n)] : SingularNManifold PUnit n M I where
  f := fun _ ↦ PUnit.unit
  hf := continuous_const

/-- The product of a singular `n`- and a `m`-manifold into a one-point space
is a singular `n+m`-manifold. -/
-- FUTURE: prove that this observation inducess a commutative ring structure
-- on the unoriented bordism group `Ω_n^O = Ω_n^O(pt)`.
def prod {m n : ℕ} [h : Fact (finrank ℝ E = m)] [k : Fact (finrank ℝ E' = n)] :
    SingularNManifold PUnit (m + n) (M × M') (I.prod I') where
  f := fun _ ↦ PUnit.unit
  hf := continuous_const
  hdim := Fact.mk (by rw [finrank_prod, h.out, k.out])

end SingularNManifold

section HasNiceBoundary

/-- All data defining a smooth manifold structure on the boundary of a smooth manifold:
a charted space structure on the boundary, a model with corners and a smooth manifold structure.
This need not exist (say, if `M` has corners); if `M` has no boundary or boundary and no corners,
such a structure is in fact canonically induced.
(Proving this requires more advanced results than we currently have.)
-/
structure BoundaryManifoldData (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [SmoothManifoldWithCorners I M] where
  E' : Type*
  [normedAddCommGroup : NormedAddCommGroup E']
  [normedSpace : NormedSpace ℝ E']
  H' : Type*
  [topologicalSpace : TopologicalSpace H']
  charts : ChartedSpace H' (I.boundary M)
  model : ModelWithCorners ℝ E' H'
  smoothManifold : SmoothManifoldWithCorners model (I.boundary M)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {J : ModelWithCorners ℝ E' H'} [SmoothManifoldWithCorners J N]

instance (d : BoundaryManifoldData M I) : TopologicalSpace d.H' := d.topologicalSpace

instance (d : BoundaryManifoldData M I) : NormedAddCommGroup d.E' := d.normedAddCommGroup

instance (d : BoundaryManifoldData M I) : NormedSpace ℝ d.E' := d.normedSpace

instance (d : BoundaryManifoldData M I) : ChartedSpace d.H' (I.boundary M) := d.charts

instance (d : BoundaryManifoldData M I) : SmoothManifoldWithCorners d.model (I.boundary M) :=
  d.smoothManifold

-- In general, constructing `BoundaryManifoldData` requires deep results: some cases and results
-- we can state already. Boundaryless manifolds have nice boundary, as do products.

/- n-dimensionality, however, requires a finite-dimensional model...
-- FIXME: is this the right design decision?
example {n : ℕ} [FiniteDimensional ℝ E] [IsEmpty M] : ClosedNManifold n M I where
  hdim := sorry -/

variable (M) in
/-- If `M` is boundaryless, its boundary manifold data is easy to construct. -/
def BoundaryManifoldData.of_boundaryless [BoundarylessManifold I M] : BoundaryManifoldData M I where
  E' := E
  H' := E
  charts := ChartedSpace.empty E (I.boundary M : Set M)
  model := modelWithCornersSelf ℝ E
  smoothManifold := by
    -- as-is, this errors with "failed to synthesize ChartedSpace E ↑(I.boundary M)" (which is fair)
    -- adding this line errors with "tactic 'apply' failed, failed to assign synthesized instance"
    --haveI := ChartedSpace.empty E (I.boundary M : Set M)
    sorry -- apply SmoothManifoldWithCorners.empty

-- another trivial case: modelWithCornersSelf on euclidean half space!

variable (M I) in
/-- If `M` is boundaryless and `N` has nice boundary, so does `M × N`. -/
def BoundaryManifoldData.prod_of_boundaryless_left [BoundarylessManifold I M]
    (bd : BoundaryManifoldData N J) : BoundaryManifoldData (M × N) (I.prod J) where
  E' := E × bd.E'
  H' := ModelProd H bd.H'
  charts := by
    haveI := bd.charts
    convert prodChartedSpace H M bd.H' (J.boundary N)
    -- TODO: convert between these... mathematically equivalent...
    -- ChartedSpace (ModelProd H bd.H') ↑((I.prod J).boundary (M × N)) =
    --   ChartedSpace (ModelProd H bd.H') (M × ↑(J.boundary N))
    sorry
  model := I.prod bd.model
  smoothManifold := by
    convert SmoothManifoldWithCorners.prod (I := I) (I' := bd.model) M (J.boundary N)
    -- same issue as above
    sorry

-- TODO: fix the details once I found a solution for the above
variable (N J) in
/-- If `M` has nice boundary and `N` is boundaryless, `M × N` has nice boundary. -/
def BoundaryManifoldData.prod_of_boundaryless_right (bd : BoundaryManifoldData M I)
    [BoundarylessManifold J N] : BoundaryManifoldData (M × N) (I.prod J) where
  E' := bd.E' × E'
  H' := ModelProd bd.H' H'
  charts := by
    haveI := bd.charts
    convert prodChartedSpace bd.H' (I.boundary M) H' N
    sorry -- same issue as above
  model := bd.model.prod J
  smoothManifold := sorry -- similar

/-- If `M` is modelled on finite-dimensional Euclidean half-space, it has nice boundary.
Proving this requires knowing homology groups of spheres (or similar). -/
def BoundaryManifoldData.of_Euclidean_halfSpace (n : ℕ) [Zero (Fin n)]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [SmoothManifoldWithCorners (𝓡∂ n) M] : BoundaryManifoldData M (𝓡∂ n) :=
  sorry

-- Another example: if E is a half-space in a Banach space, defined by a linear functional,
-- the boundary of B is also nice: this is proven in Roig-Dominguez' textbook

-- TODO: can/should this be HasNiceBoundary M I J instead?
/--  We say a smooth manifold `M` *has nice boundary* if its boundary (as a subspace)
is a smooth manifold such that the inclusion is smooth. (This condition is *not* automatic, for
instance manifolds with corners violate it, but it is satisfied in most cases of interest.

`HasNiceBoundary d` formalises this: the boundary of the manifold `M` modelled on `I`
has a charted space structure and model (included in `d`) which makes it a smooth manifold,
such that the inclusion `∂M → M` is smooth. -/
class HasNiceBoundary (bd : BoundaryManifoldData M I) where
  /-- The inclusion of `∂M` into `M` is smooth w.r.t. `d`. -/
  smooth_inclusion : ContMDiff bd.model I 1 ((fun ⟨x, _⟩ ↦ x) : (I.boundary M) → M)

/-- A manifold without boundary (trivially) has nice boundary. -/
instance [BoundarylessManifold I M] :
    HasNiceBoundary (BoundaryManifoldData.of_boundaryless (I := I) (M := M)) where
  smooth_inclusion :=
    have : I.boundary M = ∅ := ModelWithCorners.Boundaryless.boundary_eq_empty I
    fun p ↦ False.elim (IsEmpty.false p)

/-- If `M` has nice boundary and `N` is boundaryless, `M × N` also has nice boundary. -/
instance (bd : BoundaryManifoldData M I) [h : HasNiceBoundary bd] [BoundarylessManifold J N] :
    HasNiceBoundary (BoundaryManifoldData.prod_of_boundaryless_right N J bd) where
  smooth_inclusion := by
    let bd'' := BoundaryManifoldData.prod_of_boundaryless_right N J bd
    let I'' := bd''.model
    have h : ContMDiff bd.model I 1 ((fun ⟨x, _⟩ ↦ x) : (I.boundary M) → M) := h.smooth_inclusion
    have h' : ContMDiff J J 1 (fun x ↦ x : N → N) := contMDiff_id
    have : ContMDiff ((bd.model).prod J) (I.prod J) 1
        (fun (⟨x, _⟩, y) ↦ (x, y) : (I.boundary M) × N → M × N) := by
      -- TODO: how to apply prod with just two factors? let aux := ContMDiff.prod h h'
      sorry
    convert this
    -- xxx: add as API lemma, that bd''.model is what we think it is... simp only [bd''.model]
    -- TODO need to rewrite: boundary is the product of boundaries, f factors accordingly...
    sorry

/-- If `M` is boundaryless and `N` has nice boundary, `M × N` also has nice boundary. -/
instance (bd : BoundaryManifoldData N J) [HasNiceBoundary bd] [BoundarylessManifold I M] :
    HasNiceBoundary (BoundaryManifoldData.prod_of_boundaryless_left M I bd) where
  smooth_inclusion := sorry

end HasNiceBoundary

section DisjUnion

-- Let M, M' and M'' be smooth manifolds *over the same space* `H`.
-- TODO: need we also assume their models are literally the same? or on the same space E?
-- or can something weaker suffice?
variable {M : Type*} [TopologicalSpace M] [cm : ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {M' : Type*} [TopologicalSpace M'] [cm': ChartedSpace H M']
  /-{I' : ModelWithCorners ℝ E H}-/ [SmoothManifoldWithCorners I M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H M'']
  {I'' : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M'']

-- TODO: the construction below is bound to generalise... how far?
-- this should work: given an open subset U ⊆ M and a partial homeo U → H, do I get one M → H?
-- def PartialHomeomorph.extension {U : Set M} (hU : IsOpen U) (φ : PartialHomeomorph U H) :
--   PartialHomeomorph M H := by
--   refine ?e.disjointUnion ?e' ?Hs ?Ht
--   sorry

/-- Extend a partial homeomorphism from an open subset `U ⊆ M` to all of `M`. -/
-- experiment: does this work the same as foo?
def PartialHomeomorph.extend_subtype {U : Set M} [Nonempty H] (φ : PartialHomeomorph U H)
    (hU : IsOpen U) : PartialHomeomorph M H where
  toFun := Function.extend Subtype.val φ (Classical.arbitrary _)
  invFun := Subtype.val ∘ φ.symm
  left_inv' := by
    rintro x ⟨x', hx', hx'eq⟩
    rw [← hx'eq, Subtype.val_injective.extend_apply]
    dsimp
    congr
    exact PartialHomeomorph.left_inv φ hx'
  right_inv' x hx := by
    rw [Function.comp, Subtype.val_injective.extend_apply]
    exact φ.right_inv' hx
  source := Subtype.val '' φ.source
  target := φ.target
  map_source' := by
    rintro x ⟨x', hx', hx'eq⟩
    rw [← hx'eq, Subtype.val_injective.extend_apply]
    apply φ.map_source hx'
  map_target' x hx := ⟨φ.symm x, φ.map_target' hx, rfl⟩
  open_source := (hU.openEmbedding_subtype_val.open_iff_image_open).mp φ.open_source
  open_target := φ.open_target
  -- TODO: missing lemma, want a stronger version of `continuous_sum_elim`;
  -- perhaps use `continuous_sup_dom` to prove
  continuousOn_toFun := by
    dsimp
    -- TODO: why is the extension continuous? mathematically, there's not much to fuss about,
    -- `source` is open, also within U, so we can locally argue with that...
    -- in practice, this seems very annoying!
    refine ContinuousAt.continuousOn ?hcont
    rintro x ⟨x', hx', hx'eq⟩
    have : ContinuousAt φ x' := sorry -- is x', not x
    apply ContinuousAt.congr
    · sorry -- apply this--(φ.continuousOn_toFun).continuousAt (x := x') ?_
    sorry -- want to use toFun = φ on U...
    sorry
  continuousOn_invFun := sorry

/-- A partial homeomorphism `M → H` defines a partial homeomorphism `M ⊕ M' → H`. -/
def foo [h : Nonempty H] (φ : PartialHomeomorph M H) : PartialHomeomorph (M ⊕ M') H where
  -- TODO: this should be describable in terms of existing constructions!
  toFun := Sum.elim φ (Classical.arbitrary _)
  invFun := Sum.inl ∘ φ.symm
  source := Sum.inl '' φ.source
  target := φ.target
  map_source' := by
    rintro x ⟨x', hx', hx'eq⟩
    rw [← hx'eq, Sum.elim_inl]
    apply φ.map_source hx'
  map_target' x hx := ⟨φ.symm x, φ.map_target' hx, rfl⟩
  left_inv' := by
    rintro x ⟨x', hx', hx'eq⟩
    rw [← hx'eq, Sum.elim_inl]
    dsimp
    congr
    exact PartialHomeomorph.left_inv φ hx'
  right_inv' x hx := by
    rw [Function.comp, Sum.elim_inl]
    exact φ.right_inv' hx
  open_source := (openEmbedding_inl.open_iff_image_open).mp φ.open_source
  open_target := φ.open_target
  -- TODO: missing lemma, want a stronger version of `continuous_sum_elim`;
  -- perhaps use `continuous_sup_dom` to prove
  continuousOn_toFun := sorry
  continuousOn_invFun := sorry

lemma foo_source [Nonempty H] (φ : PartialHomeomorph M H) :
    (foo φ (M' := M')).source = Sum.inl '' φ.source := rfl

/-- A partial homeomorphism `M' → H` defines a partial homeomorphism `M ⊕ M' → H`. -/
def bar [Nonempty H] (φ : PartialHomeomorph M' H) : PartialHomeomorph (M ⊕ M') H where
  toFun := Sum.elim (Classical.arbitrary _) φ
  invFun := Sum.inr ∘ φ.symm
  left_inv' := by
    rintro x ⟨x', hx', hx'eq⟩
    rw [← hx'eq, Sum.elim_inr]
    dsimp
    congr
    exact PartialHomeomorph.left_inv φ hx'
  right_inv' x hx := by
    rw [Function.comp, Sum.elim_inr]
    exact φ.right_inv' hx
  source := Sum.inr '' φ.source
  target := φ.target
  map_source' := by
    rintro x ⟨x', hx', hx'eq⟩
    rw [← hx'eq, Sum.elim_inr]
    apply φ.map_source hx'
  map_target' x hx := ⟨φ.symm x, φ.map_target' hx, rfl⟩
  open_source := (openEmbedding_inr.open_iff_image_open).mp φ.open_source
  open_target := φ.open_target
  continuousOn_toFun := sorry
  continuousOn_invFun := sorry

lemma bar_source [Nonempty H] (φ : PartialHomeomorph M' H) :
    (bar φ (M := M)).source = Sum.inr '' φ.source := rfl

variable [Nonempty H] -- not sure if I really need this... will see

/-- The disjoint union of two charted spaces on `H` is a charted space over `H`. -/
instance ChartedSpace.sum : ChartedSpace H (M ⊕ M') where
  atlas := (foo '' cm.atlas) ∪ (bar '' cm'.atlas)
  -- At `x : M`, the chart is the chart in `M`; at `x' ∈ M'`, it is the chart in `M'`.
  chartAt := Sum.elim (fun x ↦ foo (cm.chartAt x)) (fun x ↦ bar (cm'.chartAt x))
  mem_chart_source p := by
    by_cases h : Sum.isLeft p
    · let x := Sum.getLeft p h
      rw [Sum.eq_left_getLeft_of_isLeft h]
      let aux := cm.mem_chart_source x
      dsimp
      rw [foo_source]
      use x
    · have h' : Sum.isRight p := Sum.not_isLeft.mp h
      let x := Sum.getRight p h'
      rw [Sum.eq_right_getRight_of_isRight h']
      let aux := cm'.mem_chart_source x
      dsimp
      rw [bar_source]
      use x
  chart_mem_atlas p := by
    by_cases h : Sum.isLeft p
    · let x := Sum.getLeft p h
      rw [Sum.eq_left_getLeft_of_isLeft h]
      dsimp
      left
      let aux := cm.chart_mem_atlas x
      use ChartedSpace.chartAt x
    · have h' : Sum.isRight p := Sum.not_isLeft.mp h
      let x := Sum.getRight p h'
      rw [Sum.eq_right_getRight_of_isRight h']
      dsimp
      right
      let aux := cm'.chart_mem_atlas x
      use ChartedSpace.chartAt x

/-- The disjoint union of two smooth manifolds modelled on `(E,H)`
is a smooth manifold modeled on `(E, H)`. -/
-- XXX. do I really need the same model twice??
instance SmoothManifoldWithCorners.sum : SmoothManifoldWithCorners I (M ⊕ M') := sorry

/-- The inclusion `M → M ⊕ M'` is smooth. -/
lemma ContMDiff.inl : ContMDiff I I ∞ (M' := M ⊕ M') Sum.inl := sorry

/-- The inclusion `M' → M ⊕ M'` is smooth. -/
lemma ContMDiff.inr : ContMDiff I I ∞ (M' := M ⊕ M') Sum.inr := sorry

variable {N J : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {J : ModelWithCorners ℝ E' H'} [SmoothManifoldWithCorners J N]
variable {N' : Type*} [TopologicalSpace N'] [ChartedSpace H' N'] [SmoothManifoldWithCorners J N']

lemma ContMDiff.sum_elim {f : M → N} {g : M' → N} (hf : Smooth I J f) (hg : Smooth I J g) :
    ContMDiff I J ∞ (Sum.elim f g) := sorry

-- actually, want an iff version here...
lemma ContMDiff.sum_map [Nonempty H'] {f : M → N} {g : M' → N'} (hf : Smooth I J f) (hg : Smooth I J g) :
    ContMDiff I J ∞ (Sum.map f g) := sorry

-- To what extent to these results exist abstractly?
def Sum.swapEquiv : M ⊕ M' ≃ M' ⊕ M where
  toFun := Sum.swap
  invFun := Sum.swap
  left_inv := Sum.swap_leftInverse
  right_inv := Sum.swap_leftInverse

lemma Continuous.swap : Continuous (@Sum.swap M M') :=
  Continuous.sum_elim continuous_inr continuous_inl

def Homeomorph.swap : M ⊕ M' ≃ₜ M' ⊕ M where
  toEquiv := Sum.swapEquiv
  continuous_toFun := Continuous.swap
  continuous_invFun := Continuous.swap

lemma ContMDiff.swap : ContMDiff I I ∞ (@Sum.swap M M') := ContMDiff.sum_elim inr inl

variable (I M M') in -- TODO: argument order is weird!
def Diffeomorph.swap : Diffeomorph I I (M ⊕ M') (M' ⊕ M) ∞ where
  toEquiv := Sum.swapEquiv
  contMDiff_toFun := ContMDiff.swap
  contMDiff_invFun := ContMDiff.swap

def Sum.assocLeft : M ⊕ (M' ⊕ N) → (M ⊕ M') ⊕ N :=
  Sum.elim (fun x ↦ Sum.inl (Sum.inl x)) (Sum.map Sum.inr id)

def Sum.assocRight : (M ⊕ M') ⊕ N → M ⊕ (M' ⊕ N) :=
  Sum.elim (Sum.map id Sum.inl) (fun x ↦ Sum.inr (Sum.inr x))

def Equiv.swapAssociativity : M ⊕ (M' ⊕ N) ≃ (M ⊕ M') ⊕ N where
  toFun := Sum.assocLeft
  invFun := Sum.assocRight
  left_inv x := by aesop
  right_inv x := by aesop

-- FUTURE: can fun_prop be powered up to solve these automatically? also for differentiability?
def Homeomorph.associativity : M ⊕ (M' ⊕ N) ≃ₜ (M ⊕ M') ⊕ N where
  toEquiv := Equiv.swapAssociativity
  continuous_toFun := by
    apply Continuous.sum_elim (by fun_prop)
    exact Continuous.sum_map continuous_inr continuous_id
  continuous_invFun := by
    apply Continuous.sum_elim (by fun_prop)
    exact Continuous.comp continuous_inr continuous_inr

variable (I M M') in
def Diffeomorph.associativity : Diffeomorph I I (M ⊕ (M' ⊕ M'')) ((M ⊕ M') ⊕ M'') ∞ where
  toEquiv := Equiv.swapAssociativity
  contMDiff_toFun := by
    apply ContMDiff.sum_elim
    · exact ContMDiff.comp ContMDiff.inl ContMDiff.inl -- xxx: can I power up fun_prop to do this?
    · exact ContMDiff.sum_map ContMDiff.inr contMDiff_id
  contMDiff_invFun := by
    apply ContMDiff.sum_elim
    · exact ContMDiff.sum_map contMDiff_id ContMDiff.inl
    · exact ContMDiff.comp ContMDiff.inr ContMDiff.inr

def Equiv.sum_empty {α β : Type*} [IsEmpty β] : α ⊕ β ≃ α where
  toFun := Sum.elim (@id α) fun x ↦ (IsEmpty.false x).elim
  invFun := Sum.inl
  left_inv x := by
    by_cases h : Sum.isLeft x
    · rw [Sum.eq_left_getLeft_of_isLeft h]
      dsimp only [Sum.elim_inl, id_eq]
    · have h' : Sum.isRight x := Sum.not_isLeft.mp h
      exact (IsEmpty.false (Sum.getRight x h')).elim
  right_inv x := by aesop

def Homeomorph.sum_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [IsEmpty Y] :
  X ⊕ Y ≃ₜ X where
  toEquiv := Equiv.sum_empty
  continuous_toFun := Continuous.sum_elim continuous_id (continuous_of_const fun _ ↦ congrFun rfl)
  continuous_invFun := continuous_inl

-- should be similar to the continuous version...
lemma contMDiff_of_const {f : M → N} (h : ∀ (x y : M), f x = f y) : ContMDiff I J ∞ f := by
  intro x
  have : f = fun _ ↦ f x := by ext y; exact h y x
  rw [this]
  apply contMDiff_const

def Diffeomorph.sum_empty [IsEmpty M'] : Diffeomorph I I (M ⊕ M') M ∞ where
  toEquiv := Equiv.sum_empty
  contMDiff_toFun := ContMDiff.sum_elim contMDiff_id (contMDiff_of_const (fun _ ↦ congrFun rfl))
  contMDiff_invFun := ContMDiff.inl

lemma sdfdsf : (Diffeomorph.swap M I M') ∘ Sum.inl = Sum.inr := by
  ext
  exact Sum.swap_inl

lemma hogehoge : (Diffeomorph.swap M I M') ∘ Sum.inr = Sum.inl := by
  ext
  exact Sum.swap_inr

end DisjUnion

namespace UnorientedCobordism

-- TODO: for now, assume all manifolds are modelled on the same chart and model space...
-- Is this necessary (`H` presumably is necessary for disjoint unions to work out...)?
-- How would that work in practice? Post-compose with a suitable equivalence of H resp. E?

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  /-{I' : ModelWithCorners ℝ E H}-/ [SmoothManifoldWithCorners I M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H M'']
  /-{I'' : ModelWithCorners ℝ E H}-/ [SmoothManifoldWithCorners I M''] {n : ℕ}
  [CompactSpace M] [BoundarylessManifold I M]
  [CompactSpace M'] [BoundarylessManifold I M'] [CompactSpace M''] [BoundarylessManifold I M'']
  [CompactSpace M] [FiniteDimensional ℝ E]
  [CompactSpace M'] [FiniteDimensional ℝ E'] [CompactSpace M''] [FiniteDimensional ℝ E'']

variable [Nonempty H]

/-- An **unoriented cobordism** between two singular `n`-manifolds `(M,f)` and `(N,g)` on `X`
is a compact smooth `n`-manifold `W` with a continuous map `F: W → X`
whose boundary is diffeomorphic to the disjoint union `M ⊔ N` such that `F` restricts to `f`
resp. `g` in the obvious way. -/
structure UnorientedCobordism (s : SingularNManifold X n M I)
    (t : SingularNManifold X n M' I) {W : Type*} [TopologicalSpace W]
    [ChartedSpace H'' W] {J : ModelWithCorners ℝ E'' H''} [SmoothManifoldWithCorners J W]
    (bd : BoundaryManifoldData W J) [HasNiceBoundary bd] where
  hW : CompactSpace W
  hW' : finrank ℝ E'' = n + 1
  F : W → X
  hF : Continuous F
  /-- The boundary of `W` is diffeomorphic to the disjoint union `M ⊔ M'`. -/
  φ : Diffeomorph bd.model I (J.boundary W) (M ⊕ M') ∞
  /-- `F` restricted to `M ↪ ∂W` equals `f`: this is formalised more nicely as
  `f = F ∘ ι ∘ φ⁻¹ : M → X`, where `ι : ∂W → W` is the inclusion. -/
  hFf : F ∘ (Subtype.val : J.boundary W → W) ∘ φ.symm ∘ Sum.inl = s.f
  /-- `F` restricted to `N ↪ ∂W` equals `g` -/
  hFg : F ∘ (Subtype.val : J.boundary W → W) ∘ φ.symm ∘ Sum.inr = t.f

variable {s : SingularNManifold X n M I}
  {t : SingularNManifold X n M' I} {W : Type*} [TopologicalSpace W] [ChartedSpace H'' W]
  {J : ModelWithCorners ℝ E'' H''} [SmoothManifoldWithCorners J W]
  {bd : BoundaryManifoldData W J} [HasNiceBoundary bd]

-- TODO: can I remove the `Fact`, concluding the empty set otherwise? or is this not useful?
variable {x y : ℝ} [Fact (x < y)] in
def _root_.boundaryData_IccManifold : BoundaryManifoldData ((Icc x y)) (𝓡∂ 1) := sorry

variable (x y : ℝ) [Fact (x < y)] (M I) in
abbrev foo  : BoundaryManifoldData (M × (Icc x y)) (I.prod (𝓡∂ 1)) :=
  BoundaryManifoldData.prod_of_boundaryless_left (M := M) (I := I)
    (boundaryData_IccManifold (x := x) (y := y))

variable {x y : ℝ} [Fact (x < y)] in
instance : HasNiceBoundary (foo M I x y) := sorry

/-- If `M` is boundaryless, `∂(M × [0,1])` is diffeomorphic to the disjoint union `M ⊔ M`. -/
-- XXX below is a definition, but that will surely *not* be nice to work with... can I get sth better?
def Diffeomorph.productInterval_sum : Diffeomorph ((foo M I 0 1).model) I
    ((I.prod (𝓡∂ 1)).boundary (M × (Icc (0 : ℝ) 1))) (M ⊕ M) ∞ where
  toFun := by
    rw [boundary_product]
    -- We send M × {0} to the first factor and M × {1} to the second.
    exact fun p ↦ if p.1.2 = 0 then Sum.inl p.1.1 else Sum.inr p.1.1
  invFun := by
    rw [boundary_product]
    exact Sum.elim (fun x ↦ ⟨(x, 0), trivial, by tauto⟩) (fun x ↦ ⟨(x, 1), trivial, by tauto⟩)
  left_inv := sorry
  right_inv := sorry
  contMDiff_toFun := by
    dsimp
    -- Several pieces still missing:
    -- f is C^n iff each restriction to M x {0} is C^n
    -- working with the actual terms.
    sorry
  contMDiff_invFun := by
    -- the following code errors...
    --suffices ContMDiff I (foo M I 0 1).model ∞ (Sum.elim (fun x ↦ ⟨(x, 0), trivial, by tauto⟩) (fun x ↦ ⟨(x, 1), trivial, by tauto⟩)) by
    --  sorry
    sorry

/-- Each singular `n`-manifold `(M,f)` is cobordant to itself. -/
def refl (s : SingularNManifold X n M I) : UnorientedCobordism s s (foo M I 0 1) where
  hW := by infer_instance
  hW' := by rw [finrank_prod, s.hdim.out, finrank_euclideanSpace_fin]
  F := s.f ∘ (fun p ↦ p.1)
  hF := s.hf.comp continuous_fst
  φ := Diffeomorph.productInterval_sum
  -- TODO: most of these proofs should become API lemmas about `Diffeomorph.productInterval_sum`
  hFf := sorry
  hFg := sorry

variable (s : SingularNManifold X n M I) (t : SingularNManifold X n M' I)
  {W : Type*} [TopologicalSpace W] [ChartedSpace H'' W]
  {J : ModelWithCorners ℝ E'' H''} [SmoothManifoldWithCorners J W]
  {bd : BoundaryManifoldData W J} [HasNiceBoundary bd]

/-- Being cobordant is symmetric. -/
def symm (φ : UnorientedCobordism s t bd) : UnorientedCobordism t s bd where
  hW := φ.hW
  hW' := φ.hW'
  F := φ.F
  hF := φ.hF
  φ := Diffeomorph.trans φ.φ (Diffeomorph.swap M I M')
  -- apply sdfdsf resp. hogehoge, and combine with φ.hFf and φ.hFg
  hFf := sorry
  hFg := sorry

-- Fleshing out the details for transitivity will take us too far: we merely sketch the necessary
-- pieces.
section transSketch

variable {u : SingularNManifold X n M'' I}
  {W' : Type*} [TopologicalSpace W'] [ChartedSpace H''' W']
  {J' : ModelWithCorners ℝ E''' H'''} [SmoothManifoldWithCorners J' W']
  {bd' : BoundaryManifoldData W' J'} [HasNiceBoundary bd']

-- Idea: glue the cobordisms W and W' along their common boundary M',
-- as identified by the diffeomorphism W → M' ← W'.
-- This could be formalised as an adjunction/attaching maps: these are a special case of pushouts
-- (in the category of topological spaces).
-- mathlib has abstract pushouts (and proved that TopCat has them);
-- `Topology/Category/TopCat/Limits/Pullbacks.lean` provides a concrete description of pullbacks
-- in TopCat. A good next step would be to adapt this argument to pushouts, and use this here.
-- TODO: can I remove the s and t variables from this definition?
def glue (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') : Type* := sorry

instance (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    TopologicalSpace (glue s t φ ψ) := sorry

-- This and the next item require the collar neighbourhood theorem.
instance (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    ChartedSpace H (glue s t φ ψ) := sorry

-- TODO: can I remove the s and t variables from this one?
def glueModel (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    ModelWithCorners ℝ E H := sorry

instance (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    SmoothManifoldWithCorners (glueModel s t φ ψ) (glue s t φ ψ) := sorry

-- TODO: can I remove the s and t variables from this one?
def glueBoundaryData (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    BoundaryManifoldData (glue s t φ ψ) (glueModel s t φ ψ) := sorry

instance (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    HasNiceBoundary (glueBoundaryData s t φ ψ) := sorry

noncomputable def trans (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    UnorientedCobordism s u (glueBoundaryData s t φ ψ) where
  hW := sorry
  hW' := sorry
  F := sorry
  hF := sorry
  φ := sorry
  hFf := sorry
  hFg := sorry

end transSketch

end UnorientedCobordism

-- how to encode this in Lean?
-- Two singular `n`-manifolds are cobordant iff there exists a smooth cobordism between them.
-- The unoriented `n`-bordism group `Ω_n^O(X)` of `X` is the set of all equivalence classes
-- of singular n-manifolds up to bordism.
-- then: functor between these...

-- prove: every element in Ω_n^O(X) has order two
