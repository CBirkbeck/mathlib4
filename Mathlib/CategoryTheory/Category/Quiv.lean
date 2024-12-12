/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# The category of quivers

The category of (bundled) quivers, and the free/forgetful adjunction between `Cat` and `Quiv`.
-/

universe v u

namespace CategoryTheory

-- intended to be used with explicit universe parameters
/-- Category of quivers. -/
@[nolint checkUnivs]
def Quiv :=
  Bundled Quiver.{v + 1, u}

namespace Quiv

instance : CoeSort Quiv (Type u) where coe := Bundled.α

instance str' (C : Quiv.{v, u}) : Quiver.{v + 1, u} C :=
  C.str

/-- Construct a bundled `Quiv` from the underlying type and the typeclass. -/
def of (C : Type u) [Quiver.{v + 1} C] : Quiv.{v, u} :=
  Bundled.of C

instance : Inhabited Quiv :=
  ⟨Quiv.of (Quiver.Empty PEmpty)⟩

/-- Category structure on `Quiv` -/
instance category : LargeCategory.{max v u} Quiv.{v, u} where
  Hom C D := Prefunctor C D
  id C := Prefunctor.id C
  comp F G := Prefunctor.comp F G

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forget : Cat.{v, u} ⥤ Quiv.{v, u} where
  obj C := Quiv.of C
  map F := F.toPrefunctor

/-- The identity in the category of quivers equals the identity prefunctor.-/
theorem id_eq_id (X : Quiv) : 𝟙 X = 𝟭q X := rfl

/-- Composition in the category of quivers equals prefunctor composition.-/
theorem comp_eq_comp {X Y Z : Quiv} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙q G := rfl

end Quiv

namespace Cat

/-- The functor sending each quiver to its path category. -/
@[simps]
def free : Quiv.{v, u} ⥤ Cat.{max u v, u} where
  obj V := Cat.of (Paths V)
  map F :=
    { obj := fun X => F.obj X
      map := fun f => F.mapPath f
      map_comp := fun f g => F.mapPath_comp f g }
  map_id V := by
    change (show Paths V ⥤ _ from _) = _
    ext
    · rfl
    · exact eq_conj_eqToHom _
  map_comp {U _ _} F G := by
    change (show Paths U ⥤ _ from _) = _
    ext
    · rfl
    · exact eq_conj_eqToHom _

end Cat

namespace Quiv

def isoOfEquiv {V W : Type u } [Quiver.{v + 1, u} V] [Quiver.{v + 1, u} W]
    (e : V ≃ W) (he : ∀ X Y : V, (X ⟶ Y) ≃ (e X ⟶ e Y)) : Quiv.of V ≅ Quiv.of W where
      hom := Prefunctor.mk e (he _ _)
      inv := {
        obj := e.symm
        map {X' Y'} f' := (he _ _).symm
          (Eq.recOn (e.right_inv Y').symm
            (Eq.recOn (e.right_inv X').symm f') : e.toFun (e.invFun X') ⟶ e.toFun (e.invFun Y'))
      }
      hom_inv_id := by
        rw [Quiv.id_eq_id, Quiv.comp_eq_comp]
        refine Prefunctor.ext e.left_inv ?_
        · intro X Y f
          have H1 {X Y Y' : V} (f' : e X ⟶ e Y) (h : Y = Y') :
            (he _ _).symm (Eq.recOn h f' : e X ⟶ e Y') = Eq.recOn h ((he _ _).symm f') := by
              cases h; rfl
          have H2 {X' X Y : V} (f' : e X ⟶ e Y) (h : X = X') :
            (he _ _).symm (Eq.recOn h f' : e X' ⟶ e Y) = Eq.recOn h ((he _ _).symm f') := by
              cases h; rfl
          have H3 {X Y : V} (f : X ⟶ Y) :
            (he _ _).symm
              (Eq.recOn (e.right_inv (e Y)).symm (Eq.recOn (e.right_inv (e X)).symm (he _ _ f)) ) =
              Eq.recOn (e.left_inv Y).symm (Eq.recOn (e.left_inv X).symm f) := sorry
          simp only [Prefunctor.id_map, Prefunctor.comp_map]
          sorry
      inv_hom_id := by
        rw [Quiv.id_eq_id]
        refine Prefunctor.ext e.right_inv ?_
        · intro X' Y' f'
          simp only [Equiv.invFun_as_coe, Equiv.toFun_as_coe, Prefunctor.id_obj, Prefunctor.id_map]
          sorry

/-- Any prefunctor into a category lifts to a functor from the path category. -/
@[simps]
def lift {V : Type u} [Quiver.{v + 1} V] {C : Type*} [Category C] (F : Prefunctor V C) :
    Paths V ⥤ C where
  obj X := F.obj X
  map f := composePath (F.mapPath f)

-- We might construct `of_lift_iso_self : Paths.of ⋙ lift F ≅ F`
-- (and then show that `lift F` is initial amongst such functors)
-- but it would require lifting quite a bit of machinery to quivers!
/--
The adjunction between forming the free category on a quiver, and forgetting a category to a quiver.
-/
def adj : Cat.free ⊣ Quiv.forget :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun V C =>
        { toFun := fun F => Paths.of.comp F.toPrefunctor
          invFun := fun F => @lift V _ C _ F
          left_inv := fun F => Paths.ext_functor rfl (by simp)
          right_inv := by
            rintro ⟨obj, map⟩
            dsimp only [Prefunctor.comp]
            congr
            funext X Y f
            exact Category.id_comp _ }
      homEquiv_naturality_left_symm := fun {V _ _} f g => by
        change (show Paths V ⥤ _ from _) = _
        ext
        · rfl
        · apply eq_conj_eqToHom }

end Quiv

end CategoryTheory
