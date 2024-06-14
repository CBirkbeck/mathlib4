/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Functor.HomFunctor
import Mathlib.Tactic.ApplyFun

/-!
# Functors to Type are closed.

Show that `C ⥤ Type max w v u` is monoidal closed for `C` a category in `Type u` with morphisms in
`Type v`, where `u`, `v`, and `w` are arbitrary universes.

## TODO
It should be shown that `C ⥤ Type max w v u` is also cartesian closed.
-/


namespace CategoryTheory

universe w v u

open MonoidalCategory

variable {C : Type u} [Category.{v} C]

namespace Functor

abbrev ihom (F G : C ⥤ Type max w v u) : C ⥤ Type max w v u := functorHom F G

end Functor

namespace FunctorToTypes

/-- Given a morphism `f : G ⟶ H`, and object `(c : C)`, and an element of `(F.ihom G).obj c`,
construct an element of `(F.ihom H).obj c`. -/
def rightAdj_map {F G H : C ⥤ Type (max w v u)} (f : G ⟶ H) (c : C) (a : (F.ihom G).obj c) :
    (F.ihom H).obj c where
      app := fun d b ↦ (a.app d b) ≫ (f.app d)
      naturality g h := by
        have := a.naturality g h
        change (F.map g ≫ a.app _ (h ≫ g)) ≫ _ = _
        aesop

/-- A right adjoint of `tensorLeft F`. -/
def rightAdj (F : C ⥤ Type max w v u) : (C ⥤ Type max w v u) ⥤ C ⥤ Type max w v u where
  obj G := F.ihom G
  map f := { app := rightAdj_map f }

variable {F G H : C ⥤ Type max w v u}

/-- The bijection between morphisms `F ⊗ G ⟶ H` and morphisms `G ⟶ F.ihom H`. -/
def homEquiv (F G H : C ⥤ Type max w v u) : (F ⊗ G ⟶ H) ≃ (G ⟶ F.ihom H) :=
  ((Functor.HomEquiv F _ _).trans (Functor.prodhomequiv F _ _)).symm

/-- The adjunction `tensorLeft F ⊣ rightAdj F`. -/
def adj (F : C ⥤ Type max w v u) : tensorLeft F ⊣ rightAdj F where
  homEquiv _ _ := homEquiv _ _ _
  unit := {
    app := fun G ↦ (homEquiv _ _ _).toFun (𝟙 _)
    naturality := fun G H f ↦ by
      ext c y
      dsimp [rightAdj, homEquiv, Functor.HomEquiv]
      ext d
      dsimp only [Monoidal.tensorObj_obj, comp, Monoidal.whiskerLeft_app, whiskerLeft_apply]
      rw [Eq.symm (FunctorToTypes.naturality G H f _ y)]
      rfl
  }
  counit := { app := fun G ↦ (homEquiv _ _ _).invFun (𝟙 _) }

instance closed (F : C ⥤ Type max w v u) : Closed F where
  adj := adj F

instance monoidalClosed : MonoidalClosed (C ⥤ Type max w v u) where

end FunctorToTypes

end CategoryTheory
