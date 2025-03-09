/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.HasSmoothBoundary

/-!
## (Unoriented) bordism theory

This file defines the beginnings of (unoriented) bordism theory. For the full definition of
smooth oriented bordism groups, a number of prerequisites are missing from mathlib. However,
a significant amount of this work is already possible.

Currently, this file only contains the definition of *singular *n*-manifolds*:
bordism classes are the equivalence classes of singular n-manifolds w.r.t. the (co)bordism relation
and will be added in a future PR, as well as the definition of the (unoriented) bordism groups.

## Main definitions

- **SingularNManifold**: a singular `n`-manifold on a topological space `X`, for `n ∈ ℕ`, is a pair
  `(M, f)` of a closed `n`-dimensional smooth manifold `M` together with a continuous map `M → X`.
  We don't assume `M` to be modelled on `ℝ^n`, but add the model topological space `H`,
  the vector space `E` and the model with corners `I` as type parameters.
- `SingularNManifold.map`: a map `X → Y` of topological spaces induces a map between the spaces
  of singular n-manifolds
- `SingularNManifold.comap`: if `(N,f)` is a singular n-manifold on `X`
  and `φ: M → N` is continuous, the `comap` of `(N,f)` and `φ`
  is the induced singular n-manifold `(M, f ∘ φ)` on `X`.
- `SingularNManifold.empty`: the empty set `M`, viewed as an `n`-manifold,
  as a singular `n`-manifold over any space `X`.
- `SingularNManifold.toPUnit`: an `n`-dimensional manifold induces a singular `n`-manifold
  on the one-point space.
- `SingularNManifold.prod`: the product of a singular `n`-manifold and a singular `m`-manifold
  on the one-point space, is a singular `n+m`-manifold on the one-point space.
- `SingularNManifold.sum`: the disjoint union of two singular `n`-manifolds
  is a singular `n`-manifold.

## Implementation notes

To be written! Document the design decisions and why they were made.

## TODO
- define cobordisms and the cobordism relation
- prove that the cobordisms relation is an equivalence relation
- define unoriented bordisms groups (as a set of equivalence classes),
prove they are a group
- define relative bordism groups (generalising the previous three points)
- prove that relative unoriented bordism groups define an extraordinary homology theory

## Tags

singular n-manifold, cobordism
-/

open scoped Manifold
open Module Set

suppress_compilation

/-- A **singular `n`-manifold** on a topological space `X`, for `n ∈ ℕ`, is a pair `(M, f)`
of a closed `n`-dimensional `C^k` manifold `M` together with a continuous map `M → X`.
We assume that `M` is a manifold over the pair `(E, H)` with model `I`.

In practice, one commonly wants to take `k=∞` (as then e.g. the intersection form is a powerful tool
to compute bordism groups; for the definition, this makes no difference.) -/
structure SingularNManifold.{u} (X : Type*) [TopologicalSpace X] (k : WithTop ℕ∞)
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) where
  /-- The manifold `M` of a singular `n`-manifold `(M, f)` -/
  M : Type u
  /-- The manifold `M` is a topological space. -/
  [topSpaceM : TopologicalSpace M]
  /-- The manifold `M` is a charted space over `H`. -/
  [chartedSpace : ChartedSpace H M]
  /-- `M` is a `C^k` manifold. -/
  [isManifold : IsManifold I k M]
  [compactSpace : CompactSpace M]
  [boundaryless : BoundarylessManifold I M]
  /-- The underlying map `M → X` of a singular `n`-manifold `(M, f)` on `X` -/
  f : M → X
  hf : Continuous f

namespace SingularNManifold

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {k : WithTop ℕ∞}
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I k M] [CompactSpace M] [BoundarylessManifold I M]

instance {s : SingularNManifold X k I} : TopologicalSpace s.M := s.topSpaceM

instance {s : SingularNManifold X k I} : ChartedSpace H s.M := s.chartedSpace

instance {s : SingularNManifold X k I} : IsManifold I k s.M := s.isManifold

instance {s : SingularNManifold X k I} : CompactSpace s.M := s.compactSpace

instance {s : SingularNManifold X k I} : BoundarylessManifold I s.M := s.boundaryless

/-- A map of topological spaces induces a corresponding map of singular n-manifolds. -/
-- This is part of proving functoriality of the bordism groups.
def map (s : SingularNManifold X k I)
    {φ : X → Y} (hφ : Continuous φ) : SingularNManifold Y k I where
  f := φ ∘ s.f
  hf := hφ.comp s.hf

@[simp]
lemma map_f (s : SingularNManifold X k I) {φ : X → Y} (hφ : Continuous φ) :
    (s.map hφ).f = φ ∘ s.f :=
  rfl

lemma map_comp (s : SingularNManifold X k I)
    {φ : X → Y} {ψ : Y → Z} (hφ : Continuous φ) (hψ : Continuous ψ) :
    ((s.map hφ).map hψ).f = (ψ ∘ φ) ∘ s.f := by
  simp [Function.comp_def]
  rfl

-- Let M' and W be real C^k manifolds.
variable {E' E'' E''' H' H'' H''' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E'']  [NormedSpace ℝ E'']
  [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [TopologicalSpace H'] [TopologicalSpace H''] [TopologicalSpace H''']

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {I' : ModelWithCorners ℝ E' H'} [IsManifold I' k M']
  [BoundarylessManifold I' M'] [CompactSpace M'] [FiniteDimensional ℝ E']

variable (M I) in
/-- If `M` is `n`-dimensional and closed, it is a singular `n`-manifold over itself.-/
noncomputable def refl : SingularNManifold M k I where
  f := id
  hf := continuous_id

/-- If `(N, f)` is a singular `n`-manifold on `X` and `M` another `n`-dimensional manifold,
a continuous map `φ : M → N` induces a singular `n`-manifold structure `(M, f ∘ φ)` on `X`. -/
noncomputable def comap (s : SingularNManifold X k I)
    {φ : M → s.M} (hφ : Continuous φ) : SingularNManifold X k I where
  f := s.f ∘ φ
  hf := s.hf.comp hφ

@[simp, mfld_simps]
lemma comap_M (s : SingularNManifold X k I) {φ : M → s.M} (hφ : Continuous φ) :
    (s.comap hφ).M = M := by
  rfl

@[simp, mfld_simps]
lemma comap_f (s : SingularNManifold X k I) {φ : M → s.M} (hφ : Continuous φ) :
    (s.comap hφ).f = s.f ∘ φ :=
  rfl

variable (X) in
/-- The canonical singular `n`-manifold associated to the empty set (seen as an `n`-dimensional
manifold, i.e. modelled on an `n`-dimensional space). -/
def empty (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I k M] [IsEmpty M] : SingularNManifold X k I where
  M := M
  f x := (IsEmpty.false x).elim
  hf := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (IsEmpty.false x).elim

omit [CompactSpace M] [BoundarylessManifold I M] in
@[simp, mfld_simps]
lemma empty_M [IsEmpty M] : (empty X M I (k := k)).M = M := rfl

instance [IsEmpty M] : IsEmpty (SingularNManifold.empty X M I (k := k)).M := by
  unfold SingularNManifold.empty
  infer_instance

variable (M I) in
/-- An `n`-dimensional manifold induces a singular `n`-manifold on the one-point space. -/
def toPUnit : SingularNManifold PUnit k I where
  M := M
  f := fun _ ↦ PUnit.unit
  hf := continuous_const

/-- The product of a singular `n`- and a singular `m`-manifold into a one-point space
is a singular `n+m`-manifold. -/
-- FUTURE: prove that this observation induces a commutative ring structure
-- on the unoriented bordism group `Ω_n^O = Ω_n^O(pt)`.
def prod (s : SingularNManifold PUnit k I) (t : SingularNManifold PUnit k I') :
    SingularNManifold PUnit k (I.prod I') where
  M := s.M × t.M
  f := fun _ ↦ PUnit.unit
  hf := continuous_const

variable (s t : SingularNManifold X k I)

/-- The disjoint union of two singular `n`-manifolds on `X` is a singular `n`-manifold on `X`. -/
-- We need to choose a model space for the disjoint union (as a priori `s` and `t` could be
-- modelled on very different spaces: for simplicity, we choose `ℝ^n`; all real work is contained
-- in the two instances above.
def sum (s t : SingularNManifold X k I) : SingularNManifold X k I where
  M := s.M ⊕ t.M
  f := Sum.elim s.f t.f
  hf := s.hf.sumElim t.hf

@[simp, mfld_simps]
lemma sum_M (s t : SingularNManifold X k I) : (s.sum t).M = (s.M ⊕ t.M) := rfl

@[simp, mfld_simps]
lemma sum_f (s t : SingularNManifold X k I) : (s.sum t).f = Sum.elim s.f t.f := rfl

end SingularNManifold

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

-- Let M and M' be smooth manifolds.
variable {E E' E'' E''' H H' H'' H''' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E'']  [NormedSpace ℝ E'']
  [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H''] [TopologicalSpace H''']

variable {k : WithTop ℕ∞}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I k M]
  -- {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  -- /-{I' : ModelWithCorners ℝ E H}-/ [IsManifold I k M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H M'']
  {I'' : ModelWithCorners ℝ E H} [IsManifold I k M'']
  [CompactSpace M] [BoundarylessManifold I M]
  --[CompactSpace M'] [BoundarylessManifold I M']
  [CompactSpace M''] [BoundarylessManifold I M'']
  [CompactSpace M] [FiniteDimensional ℝ E]
  --[CompactSpace M'] [FiniteDimensional ℝ E'] [CompactSpace M''] [FiniteDimensional ℝ E'']

variable (k) in
/-- An **unoriented cobordism** between two singular `n`-manifolds `(M,f)` and `(N,g)` on `X`
is a compact smooth `n`-manifold `W` with a continuous map `F: W → X`
whose boundary is diffeomorphic to the disjoint union `M ⊔ N` such that `F` restricts to `f`
resp. `g` in the obvious way.

We prescribe the model with corners of the underlying manifold `W` as part of this type,
as glueing arguments require matching models to work. -/
structure UnorientedCobordism.{v} (s : SingularNManifold X k I) (t : SingularNManifold X k I)
    (J : ModelWithCorners ℝ E' H') where
  /-- The underlying compact manifold of this unoriented cobordism -/
  W : Type v
  /-- The manifold `W` is a topological space. -/
  [topologicalSpace: TopologicalSpace W]
  [compactSpace : CompactSpace W]
  /-- The manifold `W` is a charted space over `H'`. -/
  [chartedSpace: ChartedSpace H' W]
  [isManifold: IsManifold J k W]
  /-- The presentation of the boundary `W` as a smooth manifold -/
  -- Future: we could allow bd.M₀ to be modelled on some other model, not necessarily I:
  -- we only care that this is fixed in the type.
  bd: BoundaryManifoldData W J k I
  /-- A continuous map `W → X` of the cobordism into the topological space we work on -/
  F : W → X
  hF : Continuous F
  /-- The boundary of `W` is diffeomorphic to the disjoint union `M ⊔ M'`. -/
  φ : Diffeomorph I I (s.M ⊕ t.M) bd.M₀ k
  /-- `F` restricted to `M ↪ ∂W` equals `f`: this is formalised more nicely as
  `f = F ∘ ι ∘ φ⁻¹ : M → X`, where `ι : ∂W → W` is the inclusion. -/
  hFf : F ∘ bd.f ∘ φ ∘ Sum.inl = s.f
  /-- `F` restricted to `N ↪ ∂W` equals `g` -/
  hFg : F ∘ bd.f ∘ φ ∘ Sum.inr = t.f

-- TODO: the checkUnivs linter complains that M and bd.M₀ only occur together

namespace UnorientedCobordism

variable {s s' t t' u : SingularNManifold X k I} {J : ModelWithCorners ℝ E' H'}

instance (φ : UnorientedCobordism k s t J) : TopologicalSpace φ.W := φ.topologicalSpace

instance (φ : UnorientedCobordism k s t J) : CompactSpace φ.W := φ.compactSpace

instance (φ : UnorientedCobordism k s t J) : ChartedSpace H' φ.W := φ.chartedSpace

instance (φ : UnorientedCobordism k s t J) : IsManifold J k φ.W := φ.isManifold

/-- The cobordism between two empty singular n-manifolds. -/
def SSs [IsEmpty M] [IsEmpty M''] : UnorientedCobordism k (SingularNManifold.empty X M I)
    (SingularNManifold.empty X M'' I) I where
  W := M
  -- XXX: generalise to any model J, by post-composing the boundary data
  bd := BoundaryManifoldData.of_boundaryless M I
  F x := (IsEmpty.false x).elim
  hF := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (IsEmpty.false x).elim
  φ := Diffeomorph.empty
  hFf := by ext x; exact (IsEmpty.false x).elim
  hFg := by ext x; exact (IsEmpty.false x).elim

/-- The disjoint union of two unoriented cobordisms (over the same model `J`). -/
noncomputable def sum (φ : UnorientedCobordism k s t J) (ψ : UnorientedCobordism k s' t' J) :
    UnorientedCobordism k (s.sum s') (t.sum t') J where
  W := φ.W ⊕ ψ.W
  bd := φ.bd.sum ψ.bd
  F := Sum.elim φ.F ψ.F
  hF := φ.hF.sumElim ψ.hF
  φ := Diffeomorph.trans (Diffeomorph.sumSumSumComm I s.M k t.M s'.M t'.M).symm
      (Diffeomorph.sumCongr φ.φ ψ.φ)
  hFf := by
    ext x
    cases x with
    | inl x =>
      set Φ := (Diffeomorph.sumSumSumComm I s.M k t.M s'.M t'.M).symm
      dsimp
      have : Φ (Sum.inl (Sum.inl x)) = Sum.inl (Sum.inl x) := sorry
      rw [this]
      simp --[φ.hFf]
      change (φ.F ∘ φ.bd.f ∘ φ.φ ∘ Sum.inl) x = s.f x
      rw [φ.hFf]
    | inr x =>
      set Φ := (Diffeomorph.sumSumSumComm I s.M k t.M s'.M t'.M).symm
      dsimp
      have : Φ (Sum.inl (Sum.inr x)) = Sum.inr (Sum.inl x) := sorry
      rw [this]
      simp --[φ.hFf]
      change (ψ.F ∘ ψ.bd.f ∘ ψ.φ ∘ Sum.inl) x = s'.f x
      rw [ψ.hFf]
  hFg := sorry -- analogous

/-- Suppose `W` is a cobordism between `M` and `N`.
Then a diffeomorphism `f : M'' → M` induces a cobordism between `M''` and `N`. -/
def comap_fst (φ : UnorientedCobordism k s t J) (f : Diffeomorph I I M'' s.M k) :
    UnorientedCobordism k (s.comap f.continuous) t J where
  bd := φ.bd
  F := φ.F
  hF := φ.hF
  φ := Diffeomorph.trans (f.sumCongr (Diffeomorph.refl _ _ _)) φ.φ
  hFf := by dsimp; rw [← φ.hFf]; congr
  hFg := by dsimp; rw [← φ.hFg]; congr

/-- Suppose `W` is a cobordism between `M` and `N`.
Then a diffeomorphism `f : N'' → N` induces a cobordism between `M` and `N''`. -/
def comap_snd (φ : UnorientedCobordism k s t J) (f : Diffeomorph I I M t.M k) :
    UnorientedCobordism k s (t.comap f.continuous) J where
  bd := φ.bd
  F := φ.F
  hF := φ.hF
  φ := Diffeomorph.trans ((Diffeomorph.refl _ _ _).sumCongr f) φ.φ
  hFf := by dsimp; rw [← φ.hFf]; congr
  hFg := by dsimp; rw [← φ.hFg]; congr

variable (s) in
/-- Each singular n-manifold is bordant to itself. -/
def refl : UnorientedCobordism k s s (I.prod (𝓡∂ 1)) where
  W := s.M × (Set.Icc (0 : ℝ) 1)
  -- TODO: I want boundary data modelled on I, not I × (∂[0,1])
  bd := sorry -- BoundaryManifoldData.prod_of_boundaryless_left s.M I (BoundaryManifoldData.Icc k)
  F := s.f ∘ (fun p ↦ p.1)
  hF := s.hf.comp continuous_fst
  φ := sorry
  hFf := sorry
  hFg := sorry

/-- Being cobordant is symmetric. -/
def symm (φ : UnorientedCobordism k s t J) : UnorientedCobordism k t s J where
  bd := φ.bd
  F := φ.F
  hF := φ.hF
  φ := (Diffeomorph.sumComm I t.M k s.M).trans φ.φ
  hFf := by rw [← φ.hFg]; congr
  hFg := by rw [← φ.hFf]; congr

-- XXX are there better names?
/-- Replace the first singular n-manifold in an unoriented bordism by an equivalent one:
useful to fix definitional equalities. -/
def copy_map_fst (φ : UnorientedCobordism k s t J)
    (eq : Diffeomorph I I s'.M s.M k) (h_eq : s'.f = s.f ∘ eq) :
    UnorientedCobordism k s' t J where
  W := φ.W
  bd := φ.bd
  F := φ.F
  hF := φ.hF
  φ := Diffeomorph.trans (Diffeomorph.sumCongr eq (Diffeomorph.refl I t.M k)) φ.φ
  hFf := by dsimp; rw [h_eq, ← φ.hFf]; congr
  hFg := by dsimp; rw [← φ.hFg]; congr

/-- Replace the second singular n-manifold in an unoriented bordism by an equivalent one:
useful to fix definitional equalities. -/
def copy_map_snd (φ : UnorientedCobordism k s t J)
    (eq : Diffeomorph I I t'.M t.M k) (h_eq : t'.f = t.f ∘ eq) :
    UnorientedCobordism k s t' J where
  W := φ.W
  bd := φ.bd
  F := φ.F
  hF := φ.hF
  φ := Diffeomorph.trans (Diffeomorph.sumCongr (Diffeomorph.refl I s.M k) eq) φ.φ
  hFf := by dsimp; rw [← φ.hFf]; congr
  hFg := by dsimp; rw [h_eq, ← φ.hFg]; congr

-- Note. The naive approach `almost` is not sufficient, as it would yield a cobordism
-- from s to `s.sum (SingularNManifold.empty X M I)`,
-- whereas I want `s.comap (Diffeomorph.sumEmpty)`... these are not *exactly* the same.

/-- Each singular n-manifold is bordant to itself plus the empty manifold. -/
def sumEmpty [IsEmpty M] :
    UnorientedCobordism k (s.sum (SingularNManifold.empty X M I)) s (I.prod (𝓡∂ 1)) :=
  letI almost := (refl s).comap_fst (Diffeomorph.sumEmpty I s.M (M' := M) k)
  almost.copy_map_fst (Diffeomorph.refl I _ k) (by
    ext x
    cases x with
    | inl x => dsimp
    | inr x => exact (IsEmpty.false x).elim)

/-- The direct sum of singular n-manifolds is commutative up to bordism. -/
def sumComm : UnorientedCobordism k (t.sum s) (s.sum t) (I.prod (𝓡∂ 1)) :=
  letI almost := (refl (s.sum t)).comap_fst (Diffeomorph.sumComm I s.M k t.M).symm
  almost.copy_map_fst (Diffeomorph.refl I _ k) (by
    ext x
    dsimp
    cases x <;> simp)

lemma foo {α β γ X : Type*} {f : α → X} {g : β → X} {h : γ → X} :
    Sum.elim (Sum.elim f g) h = Sum.elim f (Sum.elim g h) ∘ (Equiv.sumAssoc α β γ) := by
  aesop

/-- The direct sum of singular n-manifolds is associative up to bordism. -/
def sumAssoc : UnorientedCobordism k (s.sum (t.sum u)) ((s.sum t).sum u) (I.prod (𝓡∂ 1)) := by
  letI almost := (refl (s.sum (t.sum u))).comap_snd (Diffeomorph.sumAssoc I s.M k t.M u.M)
  exact almost.copy_map_snd (Diffeomorph.refl I _ k) (by
    simpa only [mfld_simps, CompTriple.comp_eq] using foo)

/-- The direct sum of a manifold with itself is null-bordant. -/
def sum_self [IsEmpty M] :
    UnorientedCobordism k (s.sum s) (SingularNManifold.empty X M I) (I.prod (𝓡∂ 1)) where
  -- This is the same manifold as for `refl`, but with a different map.
  W := s.M × (Set.Icc (0 : ℝ) 1)
  -- TODO: I want boundary data modelled on I, not I × (∂[0,1])
  bd := sorry -- BoundaryManifoldData.prod_of_boundaryless_left s.M I (BoundaryManifoldData.Icc k)
  F := s.f ∘ (fun p ↦ p.1)
  hF := s.hf.comp continuous_fst
  φ := sorry -- map everything into the left component
  hFf := sorry
  hFg := sorry

section collarNeighbourhood

variable {I₀ : ModelWithCorners ℝ E'' H''} [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'']

open Fact.Manifold

namespace _root_

/-- A `C^k` collar neighbourhood of a smooth finite-dimensional manifold `M` with smooth boundary
of co-dimension one. -/
structure CollarNeighbourhood (bd : BoundaryManifoldData M I k I₀) where
  ε : ℝ
  hε : 0 < ε
  -- XXX: I may want Ico instead; add if I need it
  φ : Set.Icc 0 ε × bd.M₀ → M
  contMDiff : haveI := Fact.mk hε; ContMDiff (((𝓡∂ 1)).prod I₀) I k φ
  isEmbedding: Topology.IsEmbedding φ
  isImmersion: haveI := Fact.mk hε; ∀ x, Function.Injective (mfderiv ((𝓡∂ 1).prod I₀) I φ x)

/- The collar neighbourhood theorem: if `M` is a compact finite-dimensional manifold
with smooth boundary of co-dimension one,
there exist some `ε > 0` and a smooth embedding `[0, ε) × ∂M → M`, which maps `{0}×∂M` to `∂M`.

Proof outline.
(1) construct a normal vector field `X` in a neighbourhood of `∂M`, pointing inwards
(In a chart on Euclidean half-space, we can just take the unit vector in the first component.
 These can be combined using e.g. a partition of unity.)
(1') It might simplify the next steps to `X` to a smooth global vector field on `M`, say be zero.
(2) Since `∂M` is compact, there is an `ε` such that the flow of `X` is defined for time `ε`.
  (This is not *exactly* the same as ongoing work, but should follow from the same ideas.)
(3) Thus, the flow of `X` defines a map `[0, ε) × ∂M → M`
(4) Shrinking `ε` if needed, we can assume `φ` is a (topological) embedding.
  Since `∂M` is compact and `M` is Hausdorff, it suffices to show injectivity (and continuity).
  Each `x∈∂M` has a neighbourhood `U_x` where the vector field looks like a flow box
  (by construction), hence the flow is injective on `U_x` for some time `ε_x`.
  Cover `∂M` with finitely many such neighbourhoods, then `ε := min ε_i` is positive, and
  each flow line does not self-intersect until time `ε`.
  Suppose the map `φ` is not injective, then `φ(x, t)=φ(x', t')`. Say `x ∈ U_i` and `x' ∈ U_j`,
  then `x, x' ∉ U_i ∩ U_j` by hypothesis, and `x, x'` lie inside separated closed sets:
  these are some positive distance apart. Now continuity and compactness yields a lower bound
  `ε_ij` for each pair, on which there is no intersection. (a bit sketchy, but mostly works)
(5) `φ` is smooth, since solutions of smooth ODEs depend smoothly on their initial conditions
(6) `φ` is an immersion... that should be obvious

Steps (4) and (5) definitely use ongoing work of Winston Yin; I don't know if the flow of a vector
field is already defined.
-/
def collar_neighbourhood_theorem (h : finrank ℝ E = finrank ℝ E'' + 1)
    (bd : BoundaryManifoldData M I k I₀) : CollarNeighbourhood bd := sorry

end _root_

end collarNeighbourhood

section trans

variable {n : ℕ} [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

/-- Being cobordant is transitive: two `n+1`-dimensional cobordisms with `n`-dimensional boundary
can be glued along their common boundary (thanks to the collar neighbourhood theorem). -/
-- The proof depends on the collar neighbourhood theorem.
-- TODO: do I need a stronger definition of cobordisms, including a *choice* of collars?
-- At least, I need to argue that one *can* choose matching collars...
def trans (φ : UnorientedCobordism k s t J) (ψ : UnorientedCobordism k t u J)
    (h : finrank ℝ E' = finrank ℝ E + 1) : UnorientedCobordism k t u J :=
  /- Outline of the proof:
    - using the collar neighbourhood theorem, choose matching collars for t in φ and ψ
      invert the first collar, to get a map (-ε, 0] × t.M → φ.W
    - let W be the attaching space, of φ.W and ψ.W along their common collar
      (i.e., we quotient the disjoint union φ.W ⊕ ψ.W along the identification by the collars)
    - the union of the collars defines an open neighbourhood of `t.M`:
      this is where the hypothesis `h` is used
    - the quotient is a smooth manifold: away from the boundary, the charts come from W and W';
      on the image of t.M, we define charts using the common map by the collars
      (smoothness is the tricky part: this requires the collars to *match*!)
    - prove: the inclusions of `φ.W` and `ψ.W` into this gluing are smooth
    - then, boundary data etc. are all easy to construct

  We could state a few more sorries, and provide more of an outline: we will not prove this in
  detail, this will be a larger project in itself. -/
  sorry

end trans

end UnorientedCobordism

variable {J : ModelWithCorners ℝ E' H'}

variable (X k I) in
/-- The "unordered bordism" equivalence relation: two singular n-manifolds modelled on `I`
are equivalent iff there exists an unoriented cobordism between them. -/
-- FIXME: remove the E' and H' arguments below, once J is actually used
def unorientedBordismRelation (_J : ModelWithCorners ℝ E' H') :
    SingularNManifold X k I → SingularNManifold X k I → Prop :=
  -- errors with: failed to infer universe levels in binder type
  -- XXX: shall we demand a relation between I and J here? for the equivalence, we need to!
  -- fun s t ↦ ∃ φ : UnorientedCobordism k s t J, True
  fun _ _ ↦ true

variable (X k I J) in -- dummy proofs, for now
lemma uBordismRelation /-[FiniteDimensional ℝ E'] (h : finrank ℝ E' = finrank ℝ E + 1)-/ :
    Equivalence (unorientedBordismRelation (H' := H') (E' := E') X k I J) := by
  apply Equivalence.mk
  · exact fun _s ↦ by trivial
  · intro _s _t h
    exact h
  · intro _s _t _u _hst _htu
    trivial

variable (X k I J) in
/-- The `Setoid` of singular n-manifolds, with the unoriented bordism relation. -/
def unorientedBordismSetoid : Setoid (SingularNManifold X k I) :=
  Setoid.mk _ (uBordismRelation X k I (H' := H') (E' := E') J)

variable (X k I J) in
/-- The type of unoriented `C^k` bordism classes on `X`. -/
-- TODO: need to impose a constraint in I and J!
abbrev uBordismClass := Quotient <| Setoid.mk _ <| uBordismRelation X k I (H' := H') (E' := E') J

variable (X k I J) in
/-- The bordism class of the empty set: the neutral element for the group operation -/
def empty : uBordismClass X k I (E' := E') (H' := H') J :=
  haveI := ChartedSpace.empty
  Quotient.mk _ (SingularNManifold.empty X Empty I)

variable (X k n) in
/-- The type of unoriented `n`-dimensional `C^k` bordism classes on `X`. -/
abbrev uBordismClassN (n : ℕ) := uBordismClass X k (𝓡 n) (𝓡 (n + 1))
