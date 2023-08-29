/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monad.Basic

#align_import category_theory.monad.kleisli from "leanprover-community/mathlib"@"545f0fb9837ce297da8eae0fec799d70191e97d4"

/-! # Kleisli category on a (co)monad

This file defines the Kleisli category on a monad `(T, η_ T, μ_ T)` as well as the co-Kleisli
category on a comonad `(U, ε_ U, δ_ U)`. It also defines the Kleisli adjunction which gives rise to
the monad `(T, η_ T, μ_ T)` as well as the co-Kleisli adjunction which gives rise to the comonad
`(U, ε_ U, δ_ U)`.

## References
* [Riehl, *Category theory in context*, Definition 5.2.9][riehl2017]
-/


namespace CategoryTheory

universe v u

-- morphism levels before object levels. See note [CategoryTheory universes].
variable {C : Type u} [Category.{v} C]

/-- The objects for the Kleisli category of the monad `T : Monad C`, which are the same
thing as objects of the base category `C`.
-/
@[nolint unusedArguments]
def Kleisli (_T : Monad C) :=
  C
#align category_theory.kleisli CategoryTheory.Kleisli

namespace Kleisli

variable (T : Monad C)

instance [Inhabited C] (T : Monad C) : Inhabited (Kleisli T) :=
  ⟨(default : C)⟩

/-- The Kleisli category on a monad `T`.
    cf Definition 5.2.9 in [Riehl][riehl2017]. -/
instance Kleisli.category : Category (Kleisli T) where
  Hom := fun X Y : C => X ⟶ (T : C ⥤ C).obj Y
  id X := T.η.app X
  comp {X} {Y} {Z} f g := f ≫ (T : C ⥤ C).map g ≫ T.μ.app Z
  id_comp {X} {Y} f := by
    dsimp -- Porting note: unfold comp
    -- ⊢ NatTrans.app (Monad.η T) X ≫ T.map f ≫ NatTrans.app (Monad.μ T) Y = f
    rw [← T.η.naturality_assoc f, T.left_unit]
    -- ⊢ (𝟭 C).map f ≫ 𝟙 (T.obj Y) = f
    apply Category.comp_id
    -- 🎉 no goals
  assoc f g h := by
    simp only [Functor.map_comp, Category.assoc, Monad.assoc]
    -- ⊢ f ≫ T.map g ≫ NatTrans.app (Monad.μ T) Y✝ ≫ T.map h ≫ NatTrans.app (Monad.μ  …
    erw [T.μ.naturality_assoc]
    -- 🎉 no goals
#align category_theory.kleisli.kleisli.category CategoryTheory.Kleisli.Kleisli.category

namespace Adjunction

/-- The left adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`. -/
@[simps]
def toKleisli : C ⥤ Kleisli T where
  obj X := (X : Kleisli T)
  map {X} {Y} f := (f ≫ T.η.app Y : X ⟶ T.obj Y)
  map_comp {X} {Y} {Z} f g := by
    -- Porting note: hack for missing unfold_projs tactic
    change _ = (f ≫ (Monad.η T).app Y) ≫ T.map (g ≫ (Monad.η T).app Z) ≫ T.μ.app Z
    -- ⊢ { obj := fun X => X, map := fun {X Y} f => f ≫ NatTrans.app (Monad.η T) Y }. …
    simp [← T.η.naturality g]
    -- 🎉 no goals
#align category_theory.kleisli.adjunction.to_kleisli CategoryTheory.Kleisli.Adjunction.toKleisli

/-- The right adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`. -/
@[simps]
def fromKleisli : Kleisli T ⥤ C where
  obj X := T.obj X
  map {_} {Y} f := T.map f ≫ T.μ.app Y
  map_id X := T.right_unit _
  map_comp {X} {Y} {Z} f g := by
    -- Porting note: hack for missing unfold_projs tactic
    change T.map (f ≫ T.map g ≫ T.μ.app Z) ≫ T.μ.app Z = _
    -- ⊢ T.map (f ≫ T.map g ≫ NatTrans.app (Monad.μ T) Z) ≫ NatTrans.app (Monad.μ T)  …
    simp only [Functor.map_comp, Category.assoc]
    -- ⊢ T.map f ≫ T.map (T.map g) ≫ T.map (NatTrans.app (Monad.μ T) Z) ≫ NatTrans.ap …
    erw [← T.μ.naturality_assoc g, T.assoc]
    -- ⊢ T.map f ≫ T.map (T.map g) ≫ NatTrans.app (Monad.μ T) (T.obj Z) ≫ NatTrans.ap …
    rfl
    -- 🎉 no goals
#align category_theory.kleisli.adjunction.from_kleisli CategoryTheory.Kleisli.Adjunction.fromKleisli

/-- The Kleisli adjunction which gives rise to the monad `(T, η_ T, μ_ T)`.
    cf Lemma 5.2.11 of [Riehl][riehl2017]. -/
def adj : toKleisli T ⊣ fromKleisli T :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => Equiv.refl (X ⟶ T.obj Y)
      homEquiv_naturality_left_symm := fun {X} {Y} {Z} f g => by
        -- Porting note: used to be unfold_projs; dsimp
        change f ≫ g = (f ≫ T.η.app Y) ≫ T.map g ≫ T.μ.app Z
        -- ⊢ f ≫ g = (f ≫ NatTrans.app (Monad.η T) Y) ≫ T.map g ≫ NatTrans.app (Monad.μ T …
        rw [Category.assoc, ← T.η.naturality_assoc g, Functor.id_map]
        -- ⊢ f ≫ g = f ≫ g ≫ NatTrans.app (Monad.η T) ((fromKleisli T).obj Z) ≫ NatTrans. …
        dsimp
        -- ⊢ f ≫ g = f ≫ g ≫ NatTrans.app (Monad.η T) (T.obj Z) ≫ NatTrans.app (Monad.μ T …
        simp [Monad.left_unit] }
        -- 🎉 no goals
#align category_theory.kleisli.adjunction.adj CategoryTheory.Kleisli.Adjunction.adj

/-- The composition of the adjunction gives the original functor. -/
def toKleisliCompFromKleisliIsoSelf : toKleisli T ⋙ fromKleisli T ≅ T :=
  NatIso.ofComponents fun X => Iso.refl _
#align category_theory.kleisli.adjunction.to_kleisli_comp_from_kleisli_iso_self CategoryTheory.Kleisli.Adjunction.toKleisliCompFromKleisliIsoSelf

end Adjunction

end Kleisli

/-- The objects for the co-Kleisli category of the comonad `U : Comonad C`, which are the same
thing as objects of the base category `C`.
-/
@[nolint unusedArguments]
def Cokleisli (_U : Comonad C) :=
  C
#align category_theory.cokleisli CategoryTheory.Cokleisli

namespace Cokleisli

variable (U : Comonad C)

instance [Inhabited C] (U : Comonad C) : Inhabited (Cokleisli U) :=
  ⟨(default : C)⟩

/-- The co-Kleisli category on a comonad `U`.-/
instance Cokleisli.category : Category (Cokleisli U) where
  Hom := fun X Y : C => (U : C ⥤ C).obj X ⟶ Y
  id X := U.ε.app X
  comp {X} {Y} {Z} f g := U.δ.app X ≫ (U : C ⥤ C).map f ≫ g
  id_comp f := by dsimp; rw [U.right_counit_assoc]
                  -- ⊢ NatTrans.app (Comonad.δ U) X✝ ≫ U.map (NatTrans.app (Comonad.ε U) X✝) ≫ f = f
                         -- 🎉 no goals
  assoc {X} {Y} {Z} {W} f g h := by
    -- Porting note: working around lack of unfold_projs
    change U.δ.app X ≫ U.map (U.δ.app X ≫ U.map f ≫ g) ≫ h =
      U.δ.app X ≫ U.map f ≫ (U.δ.app Y ≫ U.map g ≫ h)
    -- Porting note: something was broken here and was easier just to redo from scratch
    simp only [Functor.map_comp, ← Category.assoc, eq_whisker]
    -- ⊢ (((NatTrans.app (Comonad.δ U) X ≫ U.map (NatTrans.app (Comonad.δ U) X)) ≫ U. …
    simp only [Category.assoc, U.δ.naturality, Functor.comp_map, U.coassoc_assoc]
    -- 🎉 no goals
#align category_theory.cokleisli.cokleisli.category CategoryTheory.Cokleisli.Cokleisli.category

namespace Adjunction

/-- The right adjoint of the adjunction which induces the comonad `(U, ε_ U, δ_ U)`. -/
@[simps]
def toCokleisli : C ⥤ Cokleisli U where
  obj X := (X : Cokleisli U)
  map {X} {_} f := (U.ε.app X ≫ f : _)
  map_comp {X} {Y} {_} f g := by
    -- Porting note: working around lack of unfold_projs
    change U.ε.app X ≫ f ≫ g = U.δ.app X ≫ U.map (U.ε.app X ≫ f) ≫ U.ε.app Y ≫ g
    -- ⊢ NatTrans.app (Comonad.ε U) X ≫ f ≫ g = NatTrans.app (Comonad.δ U) X ≫ U.map  …
    simp [← U.ε.naturality g]
    -- 🎉 no goals
#align category_theory.cokleisli.adjunction.to_cokleisli CategoryTheory.Cokleisli.Adjunction.toCokleisli

/-- The left adjoint of the adjunction which induces the comonad `(U, ε_ U, δ_ U)`. -/
@[simps]
def fromCokleisli : Cokleisli U ⥤ C where
  obj X := U.obj X
  map {X} {_} f := U.δ.app X ≫ U.map f
  map_id X := U.right_counit _
  map_comp {X} {Y} {_} f g := by
    -- Porting note: working around lack of unfold_projs
    change U.δ.app X ≫ U.map (U.δ.app X ≫ U.map f ≫ g) =
      (U.δ.app X ≫ U.map f) ≫ (U.δ.app Y ≫ U.map g)
    simp only [Functor.map_comp, ← Category.assoc]
    -- ⊢ ((NatTrans.app (Comonad.δ U) X ≫ U.map (NatTrans.app (Comonad.δ U) X)) ≫ U.m …
    rw [Comonad.coassoc]
    -- ⊢ ((NatTrans.app (Comonad.δ U) X ≫ NatTrans.app (Comonad.δ U) (U.obj X)) ≫ U.m …
    simp only [Category.assoc, NatTrans.naturality, Functor.comp_map]
    -- 🎉 no goals
#align category_theory.cokleisli.adjunction.from_cokleisli CategoryTheory.Cokleisli.Adjunction.fromCokleisli

/-- The co-Kleisli adjunction which gives rise to the monad `(U, ε_ U, δ_ U)`. -/
def adj : fromCokleisli U ⊣ toCokleisli U :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => Equiv.refl (U.obj X ⟶ Y)
      homEquiv_naturality_right := fun {X} {Y} {_} f g => by
        -- Porting note: working around lack of unfold_projs
        change f ≫ g = U.δ.app X ≫ U.map f ≫ U.ε.app Y ≫ g
        -- ⊢ f ≫ g = NatTrans.app (Comonad.δ U) X ≫ U.map f ≫ NatTrans.app (Comonad.ε U)  …
        erw [← Category.assoc (U.map f), U.ε.naturality]; dsimp
        -- ⊢ f ≫ g = NatTrans.app (Comonad.δ U) X ≫ (NatTrans.app (Comonad.ε U) ((fromCok …
                                                          -- ⊢ f ≫ g = NatTrans.app (Comonad.δ U) X ≫ (NatTrans.app (Comonad.ε U) (U.obj X) …
        simp only [← Category.assoc, Comonad.left_counit, Category.id_comp] }
        -- 🎉 no goals
#align category_theory.cokleisli.adjunction.adj CategoryTheory.Cokleisli.Adjunction.adj

/-- The composition of the adjunction gives the original functor. -/
def toCokleisliCompFromCokleisliIsoSelf : toCokleisli U ⋙ fromCokleisli U ≅ U :=
  NatIso.ofComponents fun X => Iso.refl _
#align category_theory.cokleisli.adjunction.to_cokleisli_comp_from_cokleisli_iso_self CategoryTheory.Cokleisli.Adjunction.toCokleisliCompFromCokleisliIsoSelf

end Adjunction

end Cokleisli

end CategoryTheory
