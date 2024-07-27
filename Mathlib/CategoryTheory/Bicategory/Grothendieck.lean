/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat

/-!
# The fibered category associated to a pseudofunctor

Given a category `𝒮` and any pseudofunctor valued in `Cat` we associate to it a fibered category
category `F.toFibered ⥤ 𝒮`.

The category `F.toFibered` is defined as follows:
* Objects: pairs `(S, a)` where `S` is an object of the base category and `a` is an object of the
  category `F(S)`
* Morphisms: morphisms `(R, b) ⟶ (S, a)` are defined as pairs `(f, h)` where `f : R ⟶ S` is a
  morphism in `𝒮` and `h : b ⟶ F(f)(a)`

The projection functor `F.toFibered ⥤ 𝒮` is then given by projecting to the first factors, i.e.
* On objects, it sends `(S, a)` to `S`
* On morphisms, it sends `(f, h)` to `f`

We also provide a `HasFibers` instance `F.toFibered`, such that the fiber over `S` is the category `F(S)`.

## References
[Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by
Angelo Vistoli

-/

/-
TODO:
- Fix "↑F.toPrelaxFunctor.obj" instead of "F.obj"
- Fix naming
- (Later) splittings & functoriality
- Make `presheaf.lean` a special instance of the above
  - Isomorphism between the overcategory and fibered category associated to the corresponding
  presheaf?
-/

namespace CategoryTheory

universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Functor Category Opposite Discrete Bicategory

section mathlib_lemmas

-- already in mathlib!
@[simp]
lemma Quiver.Hom.eqToHom_toLoc {C : Type u₁} [Category.{v₁} C] {a b : C}
    (h : a = b) : (eqToHom h).toLoc = eqToHom (congrArg LocallyDiscrete.mk h) := by
  subst h; rfl

end mathlib_lemmas

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}

/-- The type of objects in the fibered category associated to a presheaf valued in types. -/
def Pseudofunctor.toFibered (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) :=
  (S : 𝒮) × (F.obj ⟨op S⟩)

namespace Pseudofunctor.toFibered

@[simps]
instance CategoryStruct : CategoryStruct F.toFibered where
  Hom X Y := (f : X.1 ⟶ Y.1) × (X.2 ⟶ (F.map f.op.toLoc).obj Y.2)
  id X := ⟨𝟙 X.1, (F.mapId ⟨op X.1⟩).inv.app X.2⟩
  comp {_ _ Z} f g := ⟨f.1 ≫ g.1, f.2 ≫ (F.map f.1.op.toLoc).map g.2 ≫
    (F.mapComp g.1.op.toLoc f.1.op.toLoc).inv.app Z.2⟩

section

variable {a b : F.toFibered} (f : a ⟶ b)

@[ext]
lemma hom_ext (g : a ⟶ b) (hfg₁ : f.1 = g.1) (hfg₂ : f.2 = g.2 ≫ eqToHom (hfg₁ ▸ rfl)) :
    f = g := by
  apply Sigma.ext hfg₁
  rw [← conj_eqToHom_iff_heq _ _ rfl (hfg₁ ▸ rfl)]
  simp only [hfg₂, eqToHom_refl, id_comp]

-- Might not need this lemma in the end
lemma hom_ext_iff (g : a ⟶ b) : f = g ↔ ∃ (hfg : f.1 = g.1), f.2 = g.2 ≫ eqToHom (hfg ▸ rfl) where
  mp := fun hfg => ⟨by rw [hfg], by simp [hfg]⟩
  mpr := fun ⟨hfg₁, hfg₂⟩ => hom_ext f g hfg₁ hfg₂

protected lemma id_comp : 𝟙 a ≫ f = f := by
  ext
  · simp
  dsimp
  rw [F.mapComp_id_right_ofStrict_inv f.1.op.toLoc]
  rw [← (F.mapId ⟨op a.1⟩).inv.naturality_assoc f.2]
  slice_lhs 2 3 =>
    rw [← Cat.whiskerLeft_app, ← NatTrans.comp_app, ← assoc]
    rw [← Bicategory.whiskerLeft_comp, Iso.inv_hom_id]
  simp

protected lemma comp_id : f ≫ 𝟙 b = f := by
  ext
  · simp
  dsimp
  rw [← Cat.whiskerRight_app, ← NatTrans.comp_app]
  rw [F.mapComp_id_left_ofStrict_inv f.1.op.toLoc]
  nth_rw 1 [← assoc]
  rw [← Bicategory.comp_whiskerRight, Iso.inv_hom_id]
  simp

end

protected lemma assoc {a b c d : F.toFibered} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (f ≫ g) ≫ h = f ≫ g ≫ h := by
  ext
  · simp
  dsimp
  slice_lhs 3 5 =>
    rw [← (F.mapComp g.1.op.toLoc f.1.op.toLoc).inv.naturality_assoc h.2]
    rw [← Cat.whiskerLeft_app, ← NatTrans.comp_app]
    rw [F.map₂_associator_ofStrict_inv h.1.op.toLoc g.1.op.toLoc f.1.op.toLoc]
    rw [NatTrans.comp_app, NatTrans.comp_app, eqToHom_app, eqToHom_app, eqToHom_refl, id_comp]
  simp only [Cat.comp_obj, Cat.comp_map, map_comp, assoc]
  congr 3
  rw [← Cat.whiskerRight_app, NatTrans.comp_app]
  simp only [Cat.comp_obj, assoc]


/-- The category structure on the fibered category associated to a presheaf valued in types. -/
instance : Category (F.toFibered) where
  toCategoryStruct := Pseudofunctor.toFibered.CategoryStruct
  id_comp := Pseudofunctor.toFibered.id_comp
  comp_id := Pseudofunctor.toFibered.comp_id
  assoc := Pseudofunctor.toFibered.assoc

/-- The projection `F.toFibered ⥤ 𝒮` given by projecting both objects and homs to the first
factor -/
@[simps]
def π (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) : F.toFibered ⥤ 𝒮 where
  obj := fun X => X.1
  map := fun f => f.1
