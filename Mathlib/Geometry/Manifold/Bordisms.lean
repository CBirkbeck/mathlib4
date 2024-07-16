/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.InteriorBoundary

/-!
# Unoriented bordism theory

In this file, we sketch the beginnings of unoriented bordism theory.
This is not ready for mathlib yet (as we still need the instance that the boundary
of a manifold is a manifold again, might might need some hypotheses to be true).
-/

/-
Missing API for this to work nicely:
- boundary of manifolds: add a typeclass "HasNiceBoundary" (or so) which says
  the boundary is a manifold, and the inclusion is smooth (perhaps with demanding "dimension one less")
  The current definition of boundary and corners will not satisfy this, but many nice manifolds
  will. Prove that boundaryless manifolds are of this form, or so.
- add disjoint union of top. spaces and induced maps: mathlib has this in abstract nonsense form
- define the disjoint union of smooth manifolds, and the associated maps: show they are smooth
(perhaps prove as abstract nonsense? will see!)

- then: complete definition of unoriented cobordisms; complete constructions I had
- fight DTT hell: why is the product with an interval not recognised?

- define the bordism relation/how to define the set of equivalence classes?
equivalences work nicely in the standard design... that's a "how to do X in Lean" question
- postponed: transitivity of the bordism relation (uses the collar neighbourhood theorem)

define induced maps between bordism groups (on singular n-manifolds is easy and done)
functoriality: what exactly do I have to show? also DTT question

prove some of the easy axioms of homology... perhaps all of it?
does mathlib have a class "extraordinary homology theory"? this could be an interesting instance...
-/

open scoped Manifold
open Metric (sphere)
open FiniteDimensional

noncomputable section

-- Some preliminaries, which should go in more basic files
section ClosedManifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H) [SmoothManifoldWithCorners I M]

/-- A topological manifold is called **closed** iff it is compact without boundary. -/
structure ClosedManifold [CompactSpace M] [I.Boundaryless]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (N : Type*) [TopologicalSpace N] [ChartedSpace H' N]
  (J : ModelWithCorners 𝕜 E' H') [SmoothManifoldWithCorners J N]

instance ClosedManifold.prod [CompactSpace M] [I.Boundaryless] [CompactSpace N] [J.Boundaryless] :
  ClosedManifold (M × N) (I.prod J) where

/-- An **n-manifold** is a smooth `n`-dimensional manifold. -/
structure NManifold (n : ℕ) [NormedAddCommGroup E]  [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {H : Type*} [TopologicalSpace H] (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners 𝕜 E H) [SmoothManifoldWithCorners I M] where
  hdim : finrank 𝕜 E = n

/-- The product of an `n`- and and an `m`-manifold is an `n+m`-manifold. -/
instance NManifold.prod {m n : ℕ} [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E']
    (s : NManifold m M I) (t : NManifold n N J) : NManifold (m + n) (M × N) (I.prod J) where
  hdim := by rw [s.hdim.symm, t.hdim.symm]; apply finrank_prod

structure ClosedNManifold (n : ℕ) [CompactSpace M] [I.Boundaryless] [FiniteDimensional 𝕜 E]
    extends ClosedManifold M I where
  hdim : finrank 𝕜 E = n

/-- The product of a closed `n`- and a closed closed `m`-manifold is a closed `n+m`-manifold. -/
instance ClosedNManifold.prod {m n : ℕ} [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E']
    [CompactSpace M] [I.Boundaryless] [CompactSpace N] [J.Boundaryless]
    (s : ClosedNManifold M I m) (t : ClosedNManifold N J n) :
    ClosedNManifold (M × N) (I.prod J) (m + n) where
  -- TODO: can I inherit this from NManifold.prod?
  hdim := by rw [s.hdim.symm, t.hdim.symm]; apply finrank_prod

section examples

-- Assume `M` is a finite-dimensional real manifold over the pair `(E, H)`.
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [SmoothManifoldWithCorners I M]

/-- The standard `n`-sphere is a closed manifold. -/
example {n : ℕ} [Fact (finrank ℝ E = n + 1)] : ClosedManifold (sphere (0 : E) 1) (𝓡 n) where

/-- The standard `2`-torus is a closed manifold. -/
example [Fact (finrank ℝ E = 1 + 1)] :
    ClosedManifold ((sphere (0 : E) 1) × (sphere (0 : E) 1)) ((𝓡 2).prod (𝓡 2)) where

-- The standard Euclidean space is an `n`-manifold. -/
example (n : ℕ) {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SmoothManifoldWithCorners (𝓡 n) M] : NManifold n M (𝓡 n) where
  hdim := finrank_euclideanSpace_fin

-- /-- The standard `n`-sphere is an `n`-manifold. -/
-- example (n : ℕ) [Fact (finrank ℝ E = n + 1)] :
--     (
--     haveI := EuclideanSpace.instChartedSpaceSphere; NManifold n (sphere (0 : E) 1) (𝓡 n)) where

--   --hdim := finrank_euclideanSpace_fin

-- the 2-torus is an n-manifold

end examples

end ClosedManifold

-- Lemmas about the interior and boundary of a product: move to `InteriorBoundary.lean`
section Boundary

variable {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [NormedAddCommGroup E'']  [NormedSpace ℝ E'']
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {I' : ModelWithCorners ℝ E' H'} [SmoothManifoldWithCorners I' M'] {x : M} {y : M'}

open Set hiding prod

/-- The interior of `M × N` is the product of the interiors of `M` and `N`. -/
lemma ModelWithCorners.interior_prod :
    (I.prod I').interior (M × M') = (I.interior M) ×ˢ (I'.interior M') := by
  ext p
  have aux : (interior (range ↑I)) ×ˢ (interior (range I')) = interior (range (I.prod I')) := by
    rw [← interior_prod_eq, ← Set.range_prod_map, modelWithCorners_prod_coe]
  constructor <;> intro hp
  · replace hp : (I.prod I').IsInteriorPoint p := hp
    rw [ModelWithCorners.IsInteriorPoint, ← aux] at hp
    exact hp
  · obtain ⟨h₁, h₂⟩ := Set.mem_prod.mp hp
    rw [ModelWithCorners.interior] at h₁ h₂
    show (I.prod I').IsInteriorPoint p
    rw [ModelWithCorners.IsInteriorPoint, ← aux]
    apply mem_prod.mpr; constructor; exacts [h₁, h₂]

/-- The boundary of `M × N` is `∂M × N ∪ (M × ∂N)`. -/
lemma ModelWithCorners.boundary_prod :
    (I.prod I').boundary (M × M') = Set.prod univ (I'.boundary M') ∪ Set.prod (I.boundary M) univ := by
  -- better proof: decompose M× M' into interior and boundary; show the latter is the complement!
  let h := calc (I.prod I').boundary (M × M')
    _ = ((I.prod I').interior (M × M'))ᶜ := (I.prod I').boundary_eq_complement_interior
    _ = ((I.interior M) ×ˢ (I'.interior M'))ᶜ := by rw [ModelWithCorners.interior_prod]
    _ = (I.interior M)ᶜ ×ˢ univ ∪ univ ×ˢ (I'.interior M')ᶜ := by rw [compl_prod_eq_union]
  rw [h, I.boundary_eq_complement_interior, I'.boundary_eq_complement_interior, union_comm]
  rfl

/-- If `M` is boundaryless, `∂(M×N) = M × ∂N`. -/
lemma boundary_of_boundaryless_left [I.Boundaryless] :
    (I.prod I').boundary (M × M') = Set.prod (univ : Set M) (I'.boundary M') := by
  rw [ModelWithCorners.boundary_prod, ModelWithCorners.Boundaryless.boundary_eq_empty I]
  have : Set.prod (∅ : Set M) (univ : Set M') = ∅ := by sorry -- how can this be so hard?
  rw [this, union_empty]

/-- If `N` is boundaryless, `∂(M×N) = ∂M × N`. -/
lemma boundary_of_boundaryless_right [I'.Boundaryless] :
    (I.prod I').boundary (M × M') = Set.prod (I.boundary M) (univ : Set M') := by
  rw [ModelWithCorners.boundary_prod, ModelWithCorners.Boundaryless.boundary_eq_empty I']
  have : Set.prod (univ : Set M) (∅ : Set M') = ∅ := by sorry -- how can this be so hard?
  rw [this, empty_union]

-- Corollary. If M is a smooth manifold without boundary, M x I has boundary M× {0,1};
--   this is diffeomorphic to M ⊔ M.

end Boundary

-- Let M, M' and W be smooth manifolds.
variable {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [NormedAddCommGroup E'']  [NormedSpace ℝ E'']
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']

/-- A **singular `n`-manifold** on a topological space `X` consists of a
closed smooth `n`-manifold `M` and a continuous map `f : M → X`. -/
structure SingularNManifold (X : Type*) [TopologicalSpace X] (n : ℕ)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [SmoothManifoldWithCorners I M]
    [CompactSpace M] [I.Boundaryless] [FiniteDimensional ℝ E] extends ClosedNManifold M I n where
  f : M → X
  hf : Continuous f

-- We declare these variables *after* the definition above, so `SingularNManifold` can have
-- its current order of arguments.
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {I' : ModelWithCorners ℝ E' H'} [SmoothManifoldWithCorners I' M'] {n : ℕ}
  [I.Boundaryless] [CompactSpace M] [FiniteDimensional ℝ E]

/-- If `M` is `n`-dimensional and closed, it is a singular `n`-manifold over itself. -/
noncomputable def SingularNManifold.refl (hdim : finrank ℝ E = n) : SingularNManifold M n M I where
  hdim := hdim
  f := id
  hf := continuous_id

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
-- functoriality: pre-step towards functoriality of the bordism groups
-- xxx: good name?
noncomputable def SingularNManifold.map (s : SingularNManifold X n M I)
    {φ : X → Y} (hφ : Continuous φ) : SingularNManifold Y n M I where
  hdim := s.hdim
  f := φ ∘ s.f
  hf := hφ.comp s.hf

@[simp]
lemma SingularNManifold.map_f (s : SingularNManifold X n M I) {φ : X → Y} (hφ : Continuous φ) :
    (s.map hφ).f = φ ∘ s.f := rfl

-- useful, or special case of the above?
lemma SingularNManifold.map_comp (s : SingularNManifold X n M I)
    {φ : X → Y} {ψ : Y → Z} (hφ : Continuous φ) (hψ : Continuous ψ):
    ((s.map hφ).map hψ).f = (s.map (hψ.comp hφ)).f := rfl

variable [CompactSpace M'] [I'.Boundaryless] [FiniteDimensional ℝ E']

/-- An **unoriented cobordism** between two singular `n`-manifolds (M,f) and (N,g) on `X`
is a compact smooth `n`-manifold `W` with a continuous map `F: W→ X` whose boundary is diffeomorphic
to the disjoint union M ⊔ N such that F restricts to f resp. g in the obvious way. -/
structure UnorientedCobordism (s : SingularNManifold X n M I) (t : SingularNManifold X n M' I')
    (W : Type*) [TopologicalSpace W] [ChartedSpace H'' W]
    (J : ModelWithCorners ℝ E'' H'') [SmoothManifoldWithCorners J W] where
  hW : CompactSpace W
  hW' : finrank E'' = n + 1
  F : W → X
  hF : Continuous F
  -- φ : Diffeomorph (∂ W) (induced J) (M ⊔ M') I.disjUnion I'
  -- hFf : F.restrict φ^{-1}(M) = s.f
  -- hFg : F.restrict φ^{-1}(N) = t.f

open Set

instance : ChartedSpace (EuclideanHalfSpace 1) (Icc 0 1) := by
  sorry -- apply IccManifold 0 1 almost does it!

-- instance : ChartedSpace (EuclideanHalfSpace (n + 1)) (M × (Icc 0 1)) := sorry

instance Icc_smooth_manifold2 : SmoothManifoldWithCorners (𝓡∂ 1) (Icc 0 1) := by
  sorry -- apply Icc_smooth_manifold 0 1 errors with
  /- tactic 'apply' failed, failed to unify
  SmoothManifoldWithCorners (modelWithCornersEuclideanHalfSpace 1) ↑(Icc (@OfNat.ofNat ℝ 0 Zero.toOfNat0) 1)
with
  SmoothManifoldWithCorners (modelWithCornersEuclideanHalfSpace 1) ↑(Icc (@OfNat.ofNat ℕ 0 (instOfNatNat 0)) 1) -/

/-- Each singular `n`-manifold (M,f)` is cobordant to itself. -/
noncomputable def UnorientedCobordism.refl (s : SingularNManifold X n M I) :
    UnorientedCobordism s s (M × (Icc 0 1)) (I.prod (𝓡∂ 1)) where
  hW := by infer_instance
  hW' := by sorry
    -- calc finrank (E × EuclideanSpace ℝ (Fin 1))
    --   _ = finrank E + (finrank (EuclideanSpace ℝ (Fin 1))) := sorry
    --   _ = n + (finrank (EuclideanSpace ℝ (Fin 1))) := sorry
    --   _ = n + 1 := sorry
      --let s := finrank_prod (R := ℝ) (M := E) (M' := EuclideanSpace ℝ (Fin 1))
    --rw [s]
    --sorry--apply? -- is n+1-dimensional
  F := s.f ∘ (fun p ↦ p.1)
  hF := s.hf.comp continuous_fst

variable (s : SingularNManifold X n M I) (t : SingularNManifold X n M' I')
  {W : Type*} [TopologicalSpace W] [ChartedSpace H'' W]
  {J : ModelWithCorners ℝ E'' H''} [SmoothManifoldWithCorners J W] {n : ℕ}

/-- Being cobordant is symmetric. -/
noncomputable def UnorientedCobordism.symm (φ : UnorientedCobordism s t W J) :
    UnorientedCobordism t s W J where
  hW := φ.hW
  hW' := φ.hW'
  F := φ.F
  hF := φ.hF
  -- TODO: boundary stuff...

-- next one: transitivity... will omit for now: really depends on boundary material,
-- and the collar neighbourhood theorem, which I don't want to formalise for now

-- how to encode this in Lean?
-- Two singular `n`-manifolds are cobordant iff there exists a smooth cobordism between them.
-- The unoriented `n`-bordism group `Ω_n^O(X)` of `X` is the set of all equivalence classes
-- of singular n-manifolds up to bordism.
-- then: functor between these...

-- prove: every element in Ω_n^O(X) has order two
