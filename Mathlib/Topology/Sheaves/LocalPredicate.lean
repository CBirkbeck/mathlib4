/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import Mathlib.Topology.Sheaves.SheafOfFunctions
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.LocalHomeomorph
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

#align_import topology.sheaves.local_predicate from "leanprover-community/mathlib"@"5dc6092d09e5e489106865241986f7f2ad28d4c8"

/-!
# Functions satisfying a local predicate form a sheaf.

At this stage, in `Mathlib/Topology/Sheaves/SheafOfFunctions.lean`
we've proved that not-necessarily-continuous functions from a topological space
into some type (or type family) form a sheaf.

Why do the continuous functions form a sheaf?
The point is just that continuity is a local condition,
so one can use the lifting condition for functions to provide a candidate lift,
then verify that the lift is actually continuous by using the factorisation condition for the lift
(which guarantees that on each open set it agrees with the functions being lifted,
which were assumed to be continuous).

This file abstracts this argument to work for
any collection of dependent functions on a topological space
satisfying a "local predicate".

As an application, we check that continuity is a local predicate in this sense, and provide
* `TopCat.sheafToTop`: continuous functions into a topological space form a sheaf

A sheaf constructed in this way has a natural map `stalkToFiber` from the stalks
to the types in the ambient type family.

We give conditions sufficient to show that this map is injective and/or surjective.
-/


universe v

noncomputable section

variable {X : TopCat.{v}}

variable (T : X → Type v)

open TopologicalSpace

open Opposite

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Limits.Types

namespace TopCat

/-- Given a topological space `X : TopCat` and a type family `T : X → Type`,
a `P : PrelocalPredicate T` consists of:
* a family of predicates `P.pred`, one for each `U : Opens X`, of the form `(Π x : U, T x) → Prop`
* a proof that if `f : Π x : V, T x` satisfies the predicate on `V : Opens X`, then
  the restriction of `f` to any open subset `U` also satisfies the predicate.
-/
structure PrelocalPredicate where
  /-- The underlying predicate of a prelocal predicate -/
  pred : ∀ {U : Opens X}, (∀ x : U, T x) → Prop
  /-- The underlying predicate should be invariant under restriction -/
  res : ∀ {U V : Opens X} (i : U ⟶ V) (f : ∀ x : V, T x) (_ : pred f), pred fun x : U => f (i x)
set_option linter.uppercaseLean3 false in
#align Top.prelocal_predicate TopCat.PrelocalPredicate

variable (X)

/-- Continuity is a "prelocal" predicate on functions to a fixed topological space `T`.
-/
@[simps!]
def continuousPrelocal (T : TopCat.{v}) : PrelocalPredicate fun _ : X => T where
  pred {_} f := Continuous f
  res {_ _} i _ h := Continuous.comp h (Opens.openEmbedding_of_le i.le).continuous
set_option linter.uppercaseLean3 false in
#align Top.continuous_prelocal TopCat.continuousPrelocal

/-- Satisfying the inhabited linter. -/
instance inhabitedPrelocalPredicate (T : TopCat.{v}) :
    Inhabited (PrelocalPredicate fun _ : X => T) :=
  ⟨continuousPrelocal X T⟩
set_option linter.uppercaseLean3 false in
#align Top.inhabited_prelocal_predicate TopCat.inhabitedPrelocalPredicate

variable {X}

/-- Given a topological space `X : TopCat` and a type family `T : X → Type`,
a `P : LocalPredicate T` consists of:
* a family of predicates `P.pred`, one for each `U : Opens X`, of the form `(Π x : U, T x) → Prop`
* a proof that if `f : Π x : V, T x` satisfies the predicate on `V : Opens X`, then
  the restriction of `f` to any open subset `U` also satisfies the predicate, and
* a proof that given some `f : Π x : U, T x`,
  if for every `x : U` we can find an open set `x ∈ V ≤ U`
  so that the restriction of `f` to `V` satisfies the predicate,
  then `f` itself satisfies the predicate.
-/
structure LocalPredicate extends PrelocalPredicate T where
  /-- A local predicate must be local --- provided that it is locally satisfied, it is also globally
    satisfied -/
  locality :
    ∀ {U : Opens X} (f : ∀ x : U, T x)
      (_ : ∀ x : U, ∃ (V : Opens X) (_ : x.1 ∈ V) (i : V ⟶ U),
        pred fun x : V => f (i x : U)), pred f
set_option linter.uppercaseLean3 false in
#align Top.local_predicate TopCat.LocalPredicate

variable (X)

/-- Continuity is a "local" predicate on functions to a fixed topological space `T`.
-/
def continuousLocal (T : TopCat.{v}) : LocalPredicate fun _ : X => T :=
  { continuousPrelocal X T with
    locality := fun {U} f w => by
      apply continuous_iff_continuousAt.2
      -- ⊢ ∀ (x : { x // x ∈ U }), ContinuousAt f x
      intro x
      -- ⊢ ContinuousAt f x
      specialize w x
      -- ⊢ ContinuousAt f x
      rcases w with ⟨V, m, i, w⟩
      -- ⊢ ContinuousAt f x
      dsimp at w
      -- ⊢ ContinuousAt f x
      rw [continuous_iff_continuousAt] at w
      -- ⊢ ContinuousAt f x
      specialize w ⟨x, m⟩
      -- ⊢ ContinuousAt f x
      simpa using (Opens.openEmbedding_of_le i.le).continuousAt_iff.1 w }
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.continuous_local TopCat.continuousLocal

/-- Satisfying the inhabited linter. -/
instance inhabitedLocalPredicate (T : TopCat.{v}) : Inhabited (LocalPredicate fun _ : X => T) :=
  ⟨continuousLocal X T⟩
set_option linter.uppercaseLean3 false in
#align Top.inhabited_local_predicate TopCat.inhabitedLocalPredicate

variable {X T}

/-- Given a `P : PrelocalPredicate`, we can always construct a `LocalPredicate`
by asking that the condition from `P` holds locally near every point.
-/
def PrelocalPredicate.sheafify {T : X → Type v} (P : PrelocalPredicate T) : LocalPredicate T where
  pred {U} f := ∀ x : U, ∃ (V : Opens X) (_ : x.1 ∈ V) (i : V ⟶ U), P.pred fun x : V => f (i x : U)
  res {V U} i f w x := by
    specialize w (i x)
    -- ⊢ ∃ V_1 x i_1, pred P fun x => (fun x => f ((fun x => { val := ↑x, property := …
    rcases w with ⟨V', m', i', p⟩
    -- ⊢ ∃ V_1 x i_1, pred P fun x => (fun x => f ((fun x => { val := ↑x, property := …
    refine' ⟨V ⊓ V', ⟨x.2, m'⟩, Opens.infLELeft _ _, _⟩
    -- ⊢ pred P fun x => (fun x => f ((fun x => { val := ↑x, property := (_ : ↑x ∈ ↑U …
    convert P.res (Opens.infLERight V V') _ p
    -- 🎉 no goals
  locality {U} f w x := by
    specialize w x
    -- ⊢ ∃ V x i, pred P fun x => f ((fun x => { val := ↑x, property := (_ : ↑x ∈ ↑U) …
    rcases w with ⟨V, m, i, p⟩
    -- ⊢ ∃ V x i, pred P fun x => f ((fun x => { val := ↑x, property := (_ : ↑x ∈ ↑U) …
    specialize p ⟨x.1, m⟩
    -- ⊢ ∃ V x i, pred P fun x => f ((fun x => { val := ↑x, property := (_ : ↑x ∈ ↑U) …
    rcases p with ⟨V', m', i', p'⟩
    -- ⊢ ∃ V x i, pred P fun x => f ((fun x => { val := ↑x, property := (_ : ↑x ∈ ↑U) …
    exact ⟨V', m', i' ≫ i, p'⟩
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.prelocal_predicate.sheafify TopCat.PrelocalPredicate.sheafify

theorem PrelocalPredicate.sheafifyOf {T : X → Type v} {P : PrelocalPredicate T} {U : Opens X}
    {f : ∀ x : U, T x} (h : P.pred f) : P.sheafify.pred f := fun x =>
  ⟨U, x.2, 𝟙 _, by convert h⟩
                   -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.prelocal_predicate.sheafify_of TopCat.PrelocalPredicate.sheafifyOf

/-- The subpresheaf of dependent functions on `X` satisfying the "pre-local" predicate `P`.
-/
@[simps!]
def subpresheafToTypes (P : PrelocalPredicate T) : Presheaf (Type v) X where
  obj U := { f : ∀ x : U.unop , T x // P.pred f }
  map {U V} i f := ⟨fun x => f.1 (i.unop x), P.res i.unop f.1 f.2⟩
set_option linter.uppercaseLean3 false in
#align Top.subpresheaf_to_Types TopCat.subpresheafToTypes

namespace subpresheafToTypes

variable (P : PrelocalPredicate T)

/-- The natural transformation including the subpresheaf of functions satisfying a local predicate
into the presheaf of all functions.
-/
def subtype : subpresheafToTypes P ⟶ presheafToTypes X T where app U f := f.1
set_option linter.uppercaseLean3 false in
#align Top.subpresheaf_to_Types.subtype TopCat.subpresheafToTypes.subtype

open TopCat.Presheaf

/-- The functions satisfying a local predicate satisfy the sheaf condition.
-/
theorem isSheaf (P : LocalPredicate T) : (subpresheafToTypes P.toPrelocalPredicate).IsSheaf :=
  Presheaf.isSheaf_of_isSheafUniqueGluing_types.{v} _ fun ι U sf sf_comp => by
    -- We show the sheaf condition in terms of unique gluing.
    -- First we obtain a family of sections for the underlying sheaf of functions,
    -- by forgetting that the predicate holds
    let sf' : ∀ i : ι, (presheafToTypes X T).obj (op (U i)) := fun i => (sf i).val
    -- ⊢ ∃! s, IsGluing (subpresheafToTypes P.toPrelocalPredicate) U sf s
    -- Since our original family is compatible, this one is as well
    have sf'_comp : (presheafToTypes X T).IsCompatible U sf' := fun i j =>
      congr_arg Subtype.val (sf_comp i j)
    -- So, we can obtain a unique gluing
    obtain ⟨gl, gl_spec, gl_uniq⟩ := (sheafToTypes X T).existsUnique_gluing U sf' sf'_comp
    -- ⊢ ∃! s, IsGluing (subpresheafToTypes P.toPrelocalPredicate) U sf s
    refine' ⟨⟨gl, _⟩, _, _⟩
    · -- Our first goal is to show that this chosen gluing satisfies the
      -- predicate. Of course, we use locality of the predicate.
      apply P.locality
      -- ⊢ ∀ (x : { x // x ∈ (op (iSup U)).unop }), ∃ V x i, PrelocalPredicate.pred P.t …
      rintro ⟨x, mem⟩
      -- ⊢ ∃ V x i, PrelocalPredicate.pred P.toPrelocalPredicate fun x => gl ((fun x => …
      -- Once we're at a particular point `x`, we can select some open set `x ∈ U i`.
      choose i hi using Opens.mem_iSup.mp mem
      -- ⊢ ∃ V x i, PrelocalPredicate.pred P.toPrelocalPredicate fun x => gl ((fun x => …
      -- We claim that the predicate holds in `U i`
      use U i, hi, Opens.leSupr U i
      -- ⊢ PrelocalPredicate.pred P.toPrelocalPredicate fun x => gl ((fun x => { val := …
      -- This follows, since our original family `sf` satisfies the predicate
      convert (sf i).property using 1
      -- ⊢ (fun x => gl ((fun x => { val := ↑x, property := (_ : ↑x ∈ ↑(op (iSup U)).un …
      exact gl_spec i
      -- 🎉 no goals

    -- It remains to show that the chosen lift is really a gluing for the subsheaf and
    -- that it is unique. Both of which follow immediately from the corresponding facts
    -- in the sheaf of functions without the local predicate.
    · exact fun i => Subtype.ext (gl_spec i)
      -- 🎉 no goals
    · intro gl' hgl'
      -- ⊢ gl' = { val := gl, property := (_ : PrelocalPredicate.pred P.toPrelocalPredi …
      refine Subtype.ext ?_
      -- ⊢ ↑gl' = ↑{ val := gl, property := (_ : PrelocalPredicate.pred P.toPrelocalPre …
      exact gl_uniq gl'.1 fun i => congr_arg Subtype.val (hgl' i)
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.subpresheaf_to_Types.is_sheaf TopCat.subpresheafToTypes.isSheaf

end subpresheafToTypes

/-- The subsheaf of the sheaf of all dependently typed functions satisfying the local predicate `P`.
-/
@[simps]
def subsheafToTypes (P : LocalPredicate T) : Sheaf (Type v) X :=
  ⟨subpresheafToTypes P.toPrelocalPredicate, subpresheafToTypes.isSheaf P⟩
set_option linter.uppercaseLean3 false in
#align Top.subsheaf_to_Types TopCat.subsheafToTypes

/-- There is a canonical map from the stalk to the original fiber, given by evaluating sections.
-/
def stalkToFiber (P : LocalPredicate T) (x : X) : (subsheafToTypes P).presheaf.stalk x ⟶ T x := by
  refine'
    colimit.desc _
      { pt := T x
        ι :=
          { app := fun U f => _
            naturality := _ } }
  · exact f.1 ⟨x, (unop U).2⟩
    -- 🎉 no goals
  · aesop
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.stalk_to_fiber TopCat.stalkToFiber

-- Porting note : removed `simp` attribute, due to left hand side is not in simple normal form.
theorem stalkToFiber_germ (P : LocalPredicate T) (U : Opens X) (x : U) (f) :
    stalkToFiber P x ((subsheafToTypes P).presheaf.germ x f) = f.1 x := by
  dsimp [Presheaf.germ, stalkToFiber]
  -- ⊢ colimit.desc ((OpenNhds.inclusion ↑x).op ⋙ subpresheafToTypes P.toPrelocalPr …
  cases x
  -- ⊢ colimit.desc ((OpenNhds.inclusion ↑{ val := val✝, property := property✝ }).o …
  simp
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.stalk_to_fiber_germ TopCat.stalkToFiber_germ

/-- The `stalkToFiber` map is surjective at `x` if
every point in the fiber `T x` has an allowed section passing through it.
-/
theorem stalkToFiber_surjective (P : LocalPredicate T) (x : X)
    (w : ∀ t : T x, ∃ (U : OpenNhds x) (f : ∀ y : U.1, T y) (_ : P.pred f), f ⟨x, U.2⟩ = t) :
    Function.Surjective (stalkToFiber P x) := fun t => by
  rcases w t with ⟨U, f, h, rfl⟩
  -- ⊢ ∃ a, stalkToFiber P x a = f { val := x, property := (_ : x ∈ U.obj) }
  fconstructor
  -- ⊢ Presheaf.stalk (Sheaf.presheaf (subsheafToTypes P)) x
  · exact (subsheafToTypes P).presheaf.germ ⟨x, U.2⟩ ⟨f, h⟩
    -- 🎉 no goals
  · exact stalkToFiber_germ _ U.1 ⟨x, U.2⟩ ⟨f, h⟩
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.stalk_to_fiber_surjective TopCat.stalkToFiber_surjective

/-- The `stalkToFiber` map is injective at `x` if any two allowed sections which agree at `x`
agree on some neighborhood of `x`.
-/
theorem stalkToFiber_injective (P : LocalPredicate T) (x : X)
    (w :
      ∀ (U V : OpenNhds x) (fU : ∀ y : U.1, T y) (_ : P.pred fU) (fV : ∀ y : V.1, T y)
        (_ : P.pred fV) (_ : fU ⟨x, U.2⟩ = fV ⟨x, V.2⟩),
        ∃ (W : OpenNhds x) (iU : W ⟶ U) (iV : W ⟶ V), ∀ w : W.1,
          fU (iU w : U.1) = fV (iV w : V.1)) :
    Function.Injective (stalkToFiber P x) := fun tU tV h => by
  -- We promise to provide all the ingredients of the proof later:
  let Q :
    ∃ (W : (OpenNhds x)ᵒᵖ) (s : ∀ w : (unop W).1, T w) (hW : P.pred s),
      tU = (subsheafToTypes P).presheaf.germ ⟨x, (unop W).2⟩ ⟨s, hW⟩ ∧
        tV = (subsheafToTypes P).presheaf.germ ⟨x, (unop W).2⟩ ⟨s, hW⟩ :=
    ?_
  · choose W s hW e using Q
    -- ⊢ tU = tV
    exact e.1.trans e.2.symm
    -- 🎉 no goals
  -- Then use induction to pick particular representatives of `tU tV : stalk x`
  obtain ⟨U, ⟨fU, hU⟩, rfl⟩ := jointly_surjective'.{v, v} tU
  -- ⊢ ∃ W s hW, colimit.ι (((whiskeringLeft (OpenNhds x)ᵒᵖ (Opens ↑X)ᵒᵖ (Type v)). …
  obtain ⟨V, ⟨fV, hV⟩, rfl⟩ := jointly_surjective'.{v, v} tV
  -- ⊢ ∃ W s hW, colimit.ι (((whiskeringLeft (OpenNhds x)ᵒᵖ (Opens ↑X)ᵒᵖ (Type v)). …
  · -- Decompose everything into its constituent parts:
    dsimp
    -- ⊢ ∃ W s hW, colimit.ι ((OpenNhds.inclusion x).op ⋙ subpresheafToTypes P.toPrel …
    simp only [stalkToFiber, Types.Colimit.ι_desc_apply'] at h
    -- ⊢ ∃ W s hW, colimit.ι ((OpenNhds.inclusion x).op ⋙ subpresheafToTypes P.toPrel …
    specialize w (unop U) (unop V) fU hU fV hV h
    -- ⊢ ∃ W s hW, colimit.ι ((OpenNhds.inclusion x).op ⋙ subpresheafToTypes P.toPrel …
    rcases w with ⟨W, iU, iV, w⟩
    -- ⊢ ∃ W s hW, colimit.ι ((OpenNhds.inclusion x).op ⋙ subpresheafToTypes P.toPrel …
    -- and put it back together again in the correct order.
    refine' ⟨op W, fun w => fU (iU w : (unop U).1), P.res _ _ hU, _⟩
    -- ⊢ (op W).unop.obj ⟶ U.unop.obj
    rcases W with ⟨W, m⟩
    -- ⊢ (op { obj := W, property := m }).unop.obj ⟶ U.unop.obj
    · exact iU
      -- 🎉 no goals
    · exact ⟨colimit_sound iU.op (Subtype.eq rfl), colimit_sound iV.op (Subtype.eq (funext w).symm)⟩
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.stalk_to_fiber_injective TopCat.stalkToFiber_injective

/-- Some repackaging:
the presheaf of functions satisfying `continuousPrelocal` is just the same thing as
the presheaf of continuous functions.
-/
def subpresheafContinuousPrelocalIsoPresheafToTop (T : TopCat.{v}) :
    subpresheafToTypes (continuousPrelocal X T) ≅ presheafToTop X T :=
  NatIso.ofComponents fun X =>
    { hom := by rintro ⟨f, c⟩; exact ⟨f, c⟩
                -- ⊢ (presheafToTop X✝ T).obj X
                               -- 🎉 no goals
      inv := by rintro ⟨f, c⟩; exact ⟨f, c⟩ }
                -- ⊢ (subpresheafToTypes (continuousPrelocal X✝ T)).obj X
                               -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.subpresheaf_continuous_prelocal_iso_presheaf_to_Top TopCat.subpresheafContinuousPrelocalIsoPresheafToTop

/-- The sheaf of continuous functions on `X` with values in a space `T`.
-/
def sheafToTop (T : TopCat.{v}) : Sheaf (Type v) X :=
  ⟨presheafToTop X T,
    Presheaf.isSheaf_of_iso (subpresheafContinuousPrelocalIsoPresheafToTop T)
      (subpresheafToTypes.isSheaf (continuousLocal X T))⟩
set_option linter.uppercaseLean3 false in
#align Top.sheaf_to_Top TopCat.sheafToTop

end TopCat
