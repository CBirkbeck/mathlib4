import Mathlib.CategoryTheory.ExactCategory.Basic
import Mathlib.CategoryTheory.Subobject.Basic

open CategoryTheory Category Limits

variable (C : Type _) [Category C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]

namespace CategoryTheory

namespace ExactCategory

structure Q where
  obj : C

namespace Q

variable {C}

structure Hom (X Y : Q C) where
  i : Subobject Y.obj
  hi : AdmissibleMono i.arrow
  j : (i : C) ⟶ X.obj
  hj : AdmissibleEpi j

attribute [instance] Hom.hi Hom.hj

noncomputable def Hom.mk' (X Y : Q C) {Z : C} (j : Z ⟶ X.obj) (i : Z ⟶ Y.obj)
  (hi : AdmissibleMono i) (hj : AdmissibleEpi j) : Hom X Y where
  i := Subobject.mk i
  hi := by
    have eq := Subobject.underlyingIso_arrow i
    rw [Iso.inv_comp_eq] at eq
    rw [eq]
    infer_instance
  j := (Subobject.underlyingIso i).hom ≫ j
  hj := inferInstance

noncomputable def Hom.id (X : Q C) : Hom X X :=
  Hom.mk' X X (𝟙 _) (𝟙 _) inferInstance inferInstance

/-
def Hom.comp {X Y Z : Q C} (α : Hom X Y) (β : Hom Y Z) : Hom X Z := by
  refine' Hom.mk' X Z (pullback.fst ≫ α.j : pullback α.i.arrow β.j ⟶ _) (pullback.snd ≫ β.i.arrow) _ inferInstance
  have : AdmissibleMono (pullback.snd : pullback (Subobject.arrow α.i) β.j ⟶ _) := sorry
  infer_instance-/

end Q

end ExactCategory

end CategoryTheory
