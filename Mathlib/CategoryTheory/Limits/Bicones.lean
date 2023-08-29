/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.FinCategory

#align_import category_theory.limits.bicones from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Bicones

Given a category `J`, a walking `Bicone J` is a category whose objects are the objects of `J` and
two extra vertices `Bicone.left` and `Bicone.right`. The morphisms are the morphisms of `J` and
`left ⟶ j`, `right ⟶ j` for each `j : J` such that `(· ⟶ j)` and `(· ⟶ k)` commutes with each
`f : j ⟶ k`.

Given a diagram `F : J ⥤ C` and two `Cone F`s, we can join them into a diagram `Bicone J ⥤ C` via
`biconeMk`.

This is used in `CategoryTheory.Functor.Flat`.
-/


universe v₁ u₁

noncomputable section

open CategoryTheory.Limits

open Classical

namespace CategoryTheory

section Bicone

/-- Given a category `J`, construct a walking `Bicone J` by adjoining two elements. -/
inductive Bicone (J : Type u₁)
  | left : Bicone J
  | right : Bicone J
  | diagram (val : J) : Bicone J
  deriving DecidableEq
#align category_theory.bicone CategoryTheory.Bicone

variable (J : Type u₁)

instance : Inhabited (Bicone J) :=
  ⟨Bicone.left⟩

instance finBicone [Fintype J] : Fintype (Bicone J)
    where
  elems := [Bicone.left, Bicone.right].toFinset ∪ Finset.image Bicone.diagram Fintype.elems
  complete j := by
    cases j <;> simp
                -- 🎉 no goals
                -- 🎉 no goals
                -- ⊢ val✝ ∈ Fintype.elems
    apply Fintype.complete
    -- 🎉 no goals
#align category_theory.fin_bicone CategoryTheory.finBicone

variable [Category.{v₁} J]

/-- The homs for a walking `Bicone J`. -/
inductive BiconeHom : Bicone J → Bicone J → Type max u₁ v₁
  | left_id : BiconeHom Bicone.left Bicone.left
  | right_id : BiconeHom Bicone.right Bicone.right
  | left (j : J) : BiconeHom Bicone.left (Bicone.diagram j)
  | right (j : J) : BiconeHom Bicone.right (Bicone.diagram j)
  | diagram {j k : J} (f : j ⟶ k) : BiconeHom (Bicone.diagram j) (Bicone.diagram k)
#align category_theory.bicone_hom CategoryTheory.BiconeHom

instance : Inhabited (BiconeHom J Bicone.left Bicone.left) :=
  ⟨BiconeHom.left_id⟩

instance BiconeHom.decidableEq {j k : Bicone J} : DecidableEq (BiconeHom J j k) := fun f g => by
  cases f <;> cases g <;> simp <;> infer_instance
              -- ⊢ Decidable (left_id = left_id)
              -- ⊢ Decidable (right_id = right_id)
              -- ⊢ Decidable (left j✝ = left j✝)
              -- ⊢ Decidable (right j✝ = right j✝)
              -- ⊢ Decidable (diagram f✝¹ = diagram f✝)
                          -- ⊢ Decidable True
                          -- ⊢ Decidable True
                          -- ⊢ Decidable True
                          -- ⊢ Decidable True
                          -- ⊢ Decidable (f✝¹ = f✝)
                                   -- 🎉 no goals
                                   -- 🎉 no goals
                                   -- 🎉 no goals
                                   -- 🎉 no goals
                                   -- 🎉 no goals
#align category_theory.bicone_hom.decidable_eq CategoryTheory.BiconeHom.decidableEq

@[simps]
instance biconeCategoryStruct : CategoryStruct (Bicone J)
    where
  Hom := BiconeHom J
  id j := Bicone.casesOn j BiconeHom.left_id BiconeHom.right_id fun k => BiconeHom.diagram (𝟙 k)
  comp f g := by
    rcases f with (_ | _ | _ | _ | f)
    · exact g
      -- 🎉 no goals
    · exact g
      -- 🎉 no goals
    · cases g
      -- ⊢ Bicone.left ⟶ Bicone.diagram k✝
      apply BiconeHom.left
      -- 🎉 no goals
    · cases g
      -- ⊢ Bicone.right ⟶ Bicone.diagram k✝
      apply BiconeHom.right
      -- 🎉 no goals
    · rcases g with (_|_|_|_|g)
      -- ⊢ Bicone.diagram j✝ ⟶ Bicone.diagram k✝
      exact BiconeHom.diagram (f ≫ g)
      -- 🎉 no goals
#align category_theory.bicone_category_struct CategoryTheory.biconeCategoryStruct

instance biconeCategory : Category (Bicone J)
    where
  id_comp f := by cases f <;> simp
                              -- 🎉 no goals
                              -- 🎉 no goals
                              -- 🎉 no goals
                              -- 🎉 no goals
                              -- 🎉 no goals
  comp_id f := by cases f <;> simp
                              -- 🎉 no goals
                              -- 🎉 no goals
                              -- 🎉 no goals
                              -- 🎉 no goals
                              -- 🎉 no goals
  assoc f g h := by cases f <;> cases g <;> cases h <;> simp
                                -- ⊢ (BiconeHom.left_id ≫ BiconeHom.left_id) ≫ h = BiconeHom.left_id ≫ BiconeHom. …
                                -- ⊢ (BiconeHom.right_id ≫ BiconeHom.right_id) ≫ h = BiconeHom.right_id ≫ BiconeH …
                                -- ⊢ (BiconeHom.left j✝ ≫ BiconeHom.diagram f✝) ≫ h = BiconeHom.left j✝ ≫ BiconeH …
                                -- ⊢ (BiconeHom.right j✝ ≫ BiconeHom.diagram f✝) ≫ h = BiconeHom.right j✝ ≫ Bicon …
                                -- ⊢ (BiconeHom.diagram f✝¹ ≫ BiconeHom.diagram f✝) ≫ h = BiconeHom.diagram f✝¹ ≫ …
                                            -- ⊢ (BiconeHom.left_id ≫ BiconeHom.left_id) ≫ BiconeHom.left_id = BiconeHom.left …
                                            -- ⊢ (BiconeHom.left_id ≫ BiconeHom.left j✝) ≫ BiconeHom.diagram f✝ = BiconeHom.l …
                                            -- ⊢ (BiconeHom.right_id ≫ BiconeHom.right_id) ≫ BiconeHom.right_id = BiconeHom.r …
                                            -- ⊢ (BiconeHom.right_id ≫ BiconeHom.right j✝) ≫ BiconeHom.diagram f✝ = BiconeHom …
                                            -- ⊢ (BiconeHom.left j✝ ≫ BiconeHom.diagram f✝¹) ≫ BiconeHom.diagram f✝ = BiconeH …
                                            -- ⊢ (BiconeHom.right j✝ ≫ BiconeHom.diagram f✝¹) ≫ BiconeHom.diagram f✝ = Bicone …
                                            -- ⊢ (BiconeHom.diagram f✝² ≫ BiconeHom.diagram f✝¹) ≫ BiconeHom.diagram f✝ = Bic …
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
#align category_theory.bicone_category CategoryTheory.biconeCategory

end Bicone

section SmallCategory

variable (J : Type v₁) [SmallCategory J]

/-- Given a diagram `F : J ⥤ C` and two `Cone F`s, we can join them into a diagram `Bicone J ⥤ C`.
-/
@[simps]
def biconeMk {C : Type u₁} [Category.{v₁} C] {F : J ⥤ C} (c₁ c₂ : Cone F) : Bicone J ⥤ C
    where
  obj X := Bicone.casesOn X c₁.pt c₂.pt fun j => F.obj j
  map f := by
    rcases f with (_|_|_|_|f)
    · exact 𝟙 _
      -- 🎉 no goals
    · exact 𝟙 _
      -- 🎉 no goals
    · exact c₁.π.app _
      -- 🎉 no goals
    · exact c₂.π.app _
      -- 🎉 no goals
    · exact F.map f
      -- 🎉 no goals
  map_id X := by cases X <;> simp
                             -- 🎉 no goals
                             -- 🎉 no goals
                             -- 🎉 no goals
  map_comp f g := by
    rcases f with (_|_|_|_|_)
    · exact (Category.id_comp _).symm
      -- 🎉 no goals
    · exact (Category.id_comp _).symm
      -- 🎉 no goals
    · cases g
      -- ⊢ { obj := fun X => Bicone.casesOn X c₁.pt c₂.pt fun j => F.obj j, map := fun  …
      exact (Category.id_comp _).symm.trans (c₁.π.naturality _)
      -- 🎉 no goals
    · cases g
      -- ⊢ { obj := fun X => Bicone.casesOn X c₁.pt c₂.pt fun j => F.obj j, map := fun  …
      exact (Category.id_comp _).symm.trans (c₂.π.naturality _)
      -- 🎉 no goals
    · cases g
      -- ⊢ { obj := fun X => Bicone.casesOn X c₁.pt c₂.pt fun j => F.obj j, map := fun  …
      apply F.map_comp
      -- 🎉 no goals
#align category_theory.bicone_mk CategoryTheory.biconeMk

instance finBiconeHom [FinCategory J] (j k : Bicone J) : Fintype (j ⟶ k) := by
  cases j <;> cases k
  · exact
      { elems := {BiconeHom.left_id}
        complete := fun f => by cases f; simp }
  · exact
    { elems := ∅
      complete := fun f => by cases f }
  · exact
    { elems := {BiconeHom.left _}
      complete := fun f => by cases f; simp }
  · exact
    { elems := ∅
      complete := fun f => by cases f }
  · exact
      { elems := {BiconeHom.right_id}
        complete := fun f => by cases f; simp }
  · exact
    { elems := {BiconeHom.right _}
      complete := fun f => by cases f; simp }
  · exact
    { elems := ∅
      complete := fun f => by cases f }
  · exact
    { elems := ∅
      complete := fun f => by cases f }
  · exact
    { elems := Finset.image BiconeHom.diagram Fintype.elems
      complete := fun f => by
        rcases f with (_|_|_|_|f)
        simp only [Finset.mem_image]
        use f
        simpa using Fintype.complete _ }
#align category_theory.fin_bicone_hom CategoryTheory.finBiconeHom

instance biconeSmallCategory : SmallCategory (Bicone J) :=
  CategoryTheory.biconeCategory J
#align category_theory.bicone_small_category CategoryTheory.biconeSmallCategory

instance biconeFinCategory [FinCategory J] : FinCategory (Bicone J) where
#align category_theory.bicone_fin_category CategoryTheory.biconeFinCategory

end SmallCategory

end CategoryTheory
