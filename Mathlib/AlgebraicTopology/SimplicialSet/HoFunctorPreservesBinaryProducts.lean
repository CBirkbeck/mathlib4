/-
Copyright (c) 2025 Emily Riehl and Dominic Verity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl, Dominic Verity
-/
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
import Mathlib.CategoryTheory.Monoidal.Functor
/-!

# The homotopy category functor preserves finite products.

The functor `hoFunctor : SSet.{u} ⥤ Cat.{u, u}` is the left adjoint of a reflective subcategory
inclusion, whose right adjoint is the fully faithful `nerveFunctor : Cat ⥤ SSet`;
see `nerveAdjunction : hoFunctor ⊣ nerveFunctor`.

Both `Cat.{u, u}` and `SSet.{u}` are cartesian closed categories. This files proves that
`hoFunctor` preserves finite cartesian products; note it fails to preserve infinite products.

-/

-- Where do these belong?
-- BM: `Mathlib.CategoryTheory.Category.Preorder`
namespace OrderHom

open CategoryTheory Functor SSet

-- BM: golfed this, at the cost of being a bit less explicit
def toFunctor {X Y} [Preorder X] [Preorder Y] (f : X →o Y) : X ⥤ Y := f.monotone.functor

def ofFunctor {X Y} [Preorder X] [Preorder Y] (F : X ⥤ Y) : (X →o Y) where
  toFun := F.obj
  monotone' := monotone F

def isoFunctor {X Y} [Preorder X] [Preorder Y] : (X →o Y) ≅ (X ⥤ Y) where
  hom := toFunctor
  inv := ofFunctor

end OrderHom

namespace CategoryTheory

universe u v

open Category Functor Limits Opposite SimplexCategory Simplicial SSet Nerve

def SimplexCategory.homEquivOrderHom {a b : SimplexCategory} :
    (a ⟶ b) ≃ (Fin (a.len + 1) →o Fin (b.len + 1)) where
  toFun := Hom.toOrderHom
  invFun := Hom.mk
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl

def OrderHom.uliftMapIso {α β : Type*} [Preorder α] [Preorder β] :
    (ULift α →o ULift β) ≃ (α →o β) where
  toFun f := ⟨fun x ↦ (f ⟨x⟩).down, fun _ _ h ↦ f.monotone (by simpa)⟩
  invFun := OrderHom.uliftMap
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl

-- set_option pp.universes true

-- def SimplexCategory.homIsoOrderHomULift {a b : SimplexCategory} :
--     (a ⟶ b) ≅ (ULift.{u} (Fin (a.len + 1)) →o ULift (Fin (b.len + 1))) where
--   hom := _
--   inv := _


-- what's the policy on defining short-but-convenient compositions?
def SimplexCategory.homIsoFunctor {a b : SimplexCategory} :
    (a ⟶ b) ≃ (Fin (a.len + 1) ⥤ Fin (b.len + 1)) :=
  Equiv.trans SimplexCategory.homEquivOrderHom OrderHom.isoFunctor.toEquiv

def SimplexCategory.homIsoFunctor' {a b : SimplexCategory} :
    (a ⟶ b) ≃ (Fin (a.len + 1) ⥤ ULiftFin (b.len + 1)) :=
  Equiv.trans SimplexCategory.homIsoFunctor sorry

/-- Nerves of finite non-empty ordinals are representable functors. -/
def nerve.RepresentableBySimplex (n : ℕ) : (nerve (Fin (n + 1))).RepresentableBy ⦋n⦌ where
  homEquiv := SimplexCategory.homIsoFunctor
  homEquiv_comp {_ _} _ _ := rfl

-- /-- The Yoneda embedding from the `SimplexCategory` into simplicial sets is naturally
-- isomorphic to `SimplexCategory.toCat ⋙ nerveFunctor` with component isomorphisms
-- `Δ[n] ≅ nerve (Fin (n + 1))`. -/
-- -- def simplexIsNerve (n : ℕ) : Δ[n] ≅ nerve (Fin (n + 1)) := NatIso.ofComponents <| fun n ↦
-- --     Equiv.toIso stdSimplex.objEquiv ≪≫ SimplexCategory.homIsoFunctor

-- -- Alternate definition:
-- -- `:= SSet.stdSimplex.isoOfRepresentableBy <| nerve.RepresentableBySimplex n`
-- -- Though slightly shorter, this would essentially have us convert to an equiv then back to an iso.

-- set_option pp.universes true

def simplexIsNerve' (n : ℕ) : Δ[n] ≅ nerve (ULiftFin.{u} (n + 1)) :=
  NatIso.ofComponents
    (fun i ↦ Equiv.toIso (stdSimplex.objEquiv.trans SimplexCategory.homIsoFunctor'))
    sorry

section preservesTerminal


noncomputable def hoFunctor.terminalIso : (hoFunctor.obj (⊤_ SSet)) ≅ (⊤_ Cat) :=
  hoFunctor.mapIso (terminalIsoIsTerminal isTerminalDeltaZero) ≪≫
    hoFunctor.mapIso (simplexIsNerve' 0) ≪≫
    nerveFunctorCompHoFunctorIso.app (Cat.of (ULiftFin 1)) ≪≫
    ULiftFinDiscretePUnitIso ≪≫ TerminalCatDiscretePUnitIso.symm

instance hoFunctor.preservesTerminal : PreservesLimit (empty.{0} SSet) hoFunctor :=
  preservesTerminal_of_iso hoFunctor hoFunctor.terminalIso

instance hoFunctor.preservesTerminal' :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) hoFunctor :=
  preservesLimitsOfShape_pempty_of_preservesTerminal _

end preservesTerminal


/-- Via the whiskered counit (or unit) of `nerveAdjunction`, the triple composite
`nerveFunctor ⋙ hoFunctor ⋙ nerveFunctor` is naturally isomorphic to `nerveFunctor`.
As `nerveFunctor` is a right adjoint, this functor preserves binary products.
Note Mathlib does not seem to recognize that `Cat.{v, u}` has binary products. -/
instance nerveHoNerve.binaryProductIsIso (C D : Type v) [Category.{v} C] [Category.{v} D] :
    IsIso (prodComparison (nerveFunctor ⋙ hoFunctor ⋙ nerveFunctor)
      (Cat.of C) (Cat.of D)) := by
  sorry

-- This proof can probably be golfed.
instance hoFunctor.binaryProductNerveIsIso (C D : Type v) [Category.{v} C] [Category.{v} D] :
    IsIso (prodComparison hoFunctor (nerve C) (nerve D)) := by
  have : IsIso (nerveFunctor.map (prodComparison hoFunctor (nerve C) (nerve D))) := by
    have : IsIso (prodComparison (hoFunctor ⋙ nerveFunctor) (nerve C) (nerve D)) := by
      have eq := prodComparison_comp
        nerveFunctor (hoFunctor ⋙ nerveFunctor) (A := Cat.of C) (B := Cat.of D)
      exact IsIso.of_isIso_fac_left eq.symm
    exact IsIso.of_isIso_fac_right (prodComparison_comp hoFunctor nerveFunctor).symm
  apply isIso_of_fully_faithful nerveFunctor

/-- By `simplexIsNerve` this is isomorphic to a map of the form
`hoFunctor.binaryProductNerveIsIso`. -/
instance hoFunctor.binarySimplexProductIsIso (n m : ℕ) :
    IsIso (prodComparison hoFunctor Δ[n] Δ[m]) :=
  IsIso.of_isIso_fac_right
    (prodComparison_natural hoFunctor (simplexIsNerve' n).hom (simplexIsNerve' m).hom).symm

/-- Modulo composing with a symmetry on both ends, the natural transformation
`prodComparisonNatTrans hofunctor Δ[m]` is a natural transformation between cocontinuous
functors whose component at `X : SSet` is `prodComparison hoFunctor X Δ[m]`. This makes use
of cartesian closure of both `SSet.{u}` and `Cat.{u,u}` to establish cocontinuity of the
product functors on both categories.

Using the colimit `Presheaf.colimitOfRepresentable (C := SimplexCategory) X` this reduces to
the result proven in `hoFunctor.binarySimplexProductIsIso`.
-/
instance hoFunctor.binaryProductWithSimplexIsIso (X : SSet) (m : ℕ) :
    IsIso (prodComparison hoFunctor X Δ[m]) := by
  have Xcolim := Presheaf.colimitOfRepresentable (C := ULiftHom SimplexCategory)
    (ULiftHom.down.op ⋙ X)
  sorry

/-- The natural transformation `prodComparisonNatTrans hofunctor X` is a natural
transformation between cocontinuous functors whose component at `Y : SSet` is
`prodComparison hoFunctor X Y`. This makes use of cartesian closure of both `SSet.{u}`
and `Cat.{u,u}` to establish cocontinuity of the product functors on both categories.

Using the colimit `Presheaf.colimitOfRepresentable (C := SimplexCategory) Y` this reduces to
the result proven in `hoFunctor.binaryProductWithSimplexIsIso`.
-/
instance hoFunctor.binaryProductIsIso (X Y : SSet):
    IsIso (prodComparison hoFunctor X Y) := by
  unfold SSet SimplicialObject at X Y
  have Ycolim := Presheaf.colimitOfRepresentable (C := ULiftHom SimplexCategory)
    (ULiftHom.down.op ⋙ Y)
  have := prodComparisonNatTrans hoFunctor X
  sorry

/-- The functor `hoFunctor : SSet ⥤ Cat` preserves binary products of simplicial sets
`X` and `Y`. -/
instance hoFunctor.preservesBinaryProducts (X Y : SSet) :
    PreservesLimit (pair X Y) hoFunctor :=
  PreservesLimitPair.of_iso_prod_comparison hoFunctor X Y

/-- The functor `hoFunctor : SSet ⥤ Cat` preserves binary products of functors
out of `Discrete Limits.WalkingPair`. -/
instance hoFunctor.preservesBinaryProducts' :
    PreservesLimitsOfShape (Discrete Limits.WalkingPair) hoFunctor where
  preservesLimit :=
    fun {F} ↦ preservesLimit_of_iso_diagram hoFunctor (id (diagramIsoPair F).symm)

instance hoFunctor.preservesFiniteProducts : PreservesFiniteProducts hoFunctor :=
  Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal _

/-- A product preserving functor between cartesian closed categories is lax monoidal. -/
noncomputable instance hoFunctor.laxMonoidal : LaxMonoidal hoFunctor :=
  (Monoidal.ofChosenFiniteProducts hoFunctor).toLaxMonoidal

/--
QCat is the category of quasi-categories defined as the full subcategory of the category of `SSet`.
-/
def QCat := ObjectProperty.FullSubcategory Quasicategory
instance : Category QCat := ObjectProperty.FullSubcategory.category Quasicategory

/-- As objects characterized by a right lifting property, it is straightforward to directly
verify that. -/
instance QCat.hasBinaryProducts : HasBinaryProducts QCat := sorry

/-- The construction above should form the product in the category `SSet` and verify that this
object is a quasi-category. -/
instance QCat.inclusionPreservesBinaryProducts :
    PreservesLimitsOfShape (Discrete Limits.WalkingPair) (ObjectProperty.ι Quasicategory) := sorry

end CategoryTheory
