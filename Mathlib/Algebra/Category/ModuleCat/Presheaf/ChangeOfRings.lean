/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf

/-!
# Change of presheaf of rings

In this file, we define the restriction of scalars functor
`restrictScalars α : PresheafOfModules.{v} R' ⥤ PresheafOfModules.{v} R`
attached to a morphism of presheaves of rings `α : R ⟶ R'`.

-/

universe v v' u u'

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {R R' : Cᵒᵖ ⥤ RingCat.{u}}

open ModuleCat.restrictScalars

/-- The restriction of scalars of presheaves of modules, on objects. -/
@[simps]
noncomputable def restrictScalarsObj (M' : PresheafOfModules.{v} R') (α : R ⟶ R') :
    PresheafOfModules R where
  obj := fun X ↦ (ModuleCat.restrictScalars (α.app X)).obj (M'.obj X)
  map := fun {X Y} f ↦ ModuleCat.ofHom
    { toFun x := into _ (into _ (out _ ((M'.map f).hom (out _ x))))
      map_add' _ _ := by simp
      map_smul' r x := by
        ext
        dsimp
        rw [smul_def, out_into, M'.map_smul, smul_def]
        have eq := RingHom.congr_fun (α.naturality f) r
        dsimp at eq
        rw [← eq]
        simp }

/-- The restriction of scalars functor `PresheafOfModules R' ⥤ PresheafOfModules R`
induced by a morphism of presheaves of rings `R ⟶ R'`. -/
@[simps]
noncomputable def restrictScalars (α : R ⟶ R') :
    PresheafOfModules.{v} R' ⥤ PresheafOfModules.{v} R where
  obj M' := M'.restrictScalarsObj α
  map φ' :=
    { app := fun X ↦ (ModuleCat.restrictScalars (α.app X)).map (Hom.app φ' X)
      naturality := fun {X Y} f ↦ by
        ext x
        exact congr_arg (into _) (naturality_apply φ' f (out _ x)) }

instance (α : R ⟶ R') : (restrictScalars.{v} α).Additive where

/-- The isomorphism `restrictScalars α ⋙ toPresheaf R ≅ toPresheaf R'` for any
morphism of presheaves of rings `α : R ⟶ R'`. -/
noncomputable def restrictScalarsCompToPresheaf (α : R ⟶ R') :
    restrictScalars.{v} α ⋙ toPresheaf R ≅ toPresheaf R' where
  hom.app X := { app M := AddCommGrp.ofHom <|
    (Module.RestrictScalars.outAddEquiv _ _).toAddMonoidHom }
  inv.app X := { app M := AddCommGrp.ofHom <|
    (Module.RestrictScalars.outAddEquiv _ _).symm.toAddMonoidHom }

def restrictScalarsId : 𝟭 (PresheafOfModules R) ≅ restrictScalars (𝟙 R) where
  hom.app X := { app M := ModuleCat.ofHom <| Module.RestrictScalars.idEquiv.symm.toLinearMap }
  inv.app X := { app M := ModuleCat.ofHom <| Module.RestrictScalars.idEquiv.toLinearMap }

instance : (restrictScalars (𝟙 R)).Full :=
  CategoryTheory.Functor.Full.of_iso (F := (𝟭 _)) restrictScalarsId

instance (α : R ⟶ R') : (restrictScalars α).Faithful :=
  have _ : (restrictScalars α ⋙ toPresheaf R).Faithful := Functor.Faithful.of_iso
    (restrictScalarsCompToPresheaf _).symm
  Functor.Faithful.of_comp (restrictScalars α) (toPresheaf R)

end PresheafOfModules
