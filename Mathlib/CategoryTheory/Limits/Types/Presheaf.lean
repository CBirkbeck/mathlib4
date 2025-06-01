/-
Copyright (c) 2025 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet
-/
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Natural transformations of presheaves as limits

Let `C` be a category and `F, G : Cᵒᵖ ⥤ Type w` two presheaves over `C`.
We give the natural isomorphism between natural transformations `F ⟶ G` and objects of the limit of
sections of `G` over sections of `F`.
-/

universe u v w

open CategoryTheory

section sectionOver

variable {C : Type u} [Category.{v,u} C] (F : C ⥤ Type w)

def sectionOver : Type max u w :=  (X : C) × F.obj X

@[ext]
structure sectionOverMorphism (s s' : sectionOver F) where
  fst : s.fst ⟶ s'.fst
  w : F.map fst s.snd = s'.snd := by aesop_cat

attribute [simp] sectionOverMorphism.w

instance sectionOverCategory : Category (sectionOver F) where
  Hom := sectionOverMorphism F
  id s := {fst := 𝟙 s.fst}
  comp f g := {fst := f.fst ≫ g.fst}

namespace sectionOver

section

variable {s s' s'' : sectionOver F} (f : s ⟶ s') (g : s' ⟶ s'')

@[ext]
lemma hom_ext (f g : s ⟶ s') (h : f.fst = g.fst) : f = g :=
  sectionOverMorphism.ext h

@[simp]
lemma id_fst : (𝟙 s : sectionOverMorphism F s s).fst = 𝟙 (s.fst) := rfl

@[simp]
lemma comp_fst : (f ≫ g).fst = f.fst ≫ g.fst := rfl

end

end sectionOver

section

variable (G : C ⥤ Type w)

def sectionOverFunctor : sectionOver F ⥤ Type w where
  obj s := G.obj s.fst
  map f := G.map f.fst

def morphismsEquivSectionsSectionOverFunctor :
    (F ⟶ G) ≃ (sectionOverFunctor F G).sections where
  toFun α := ⟨
      fun s => α.app s.fst s.snd,
      fun {s s'} f => by
        show (α.app s.fst ≫ G.map f.fst) s.snd = α.app s'.fst s'.snd
        rw [← α.naturality]
        simp
    ⟩
  invFun σ := {
      app X x := σ.val (⟨X, x⟩ : sectionOver F),
      naturality {X Y} f := by
        ext x
        simp only [types_comp_apply,
          ← σ.prop ({fst := f} : sectionOverMorphism F ⟨X, x⟩ ⟨Y, F.map f x⟩)]
        rfl
    }
  left_inv _ := rfl
  right_inv _ := rfl

def morphismsEquivLimitSectionOver [UnivLE.{max w u, w}] :
    (F ⟶ G) ≃ Limits.limit (sectionOverFunctor F G) :=
  sorry

end

end sectionOver


/-
section

variable {C : Type u} [Category.{v,u} C] (F G : Cᵒᵖ ⥤ Type v)

def Over.IsRepresentable : ObjectProperty (Over F) :=
  fun X : Over F => Functor.IsRepresentable X.left

def sectionsOverCategory := (Over.IsRepresentable F).FullSubcategory

instance useless : Category (sectionsOverCategory F) :=
  ObjectProperty.FullSubcategory.category (Over.IsRepresentable F)

noncomputable def sectionsOverFunctor : (sectionsOverCategory F)ᵒᵖ ⥤ Type v where
  obj s := G.obj (Opposite.op (s.unop.obj.left.reprX (hF := s.unop.property)))
  map {s s'} f :=
    have : Functor.IsRepresentable s'.unop.obj.left := s'.unop.property
    have : Functor.IsRepresentable s.unop.obj.left := s.unop.property
    G.map ((Yoneda.fullyFaithful.preimage
      (s'.unop.obj.left.reprW.hom ≫ f.unop.left ≫ s.unop.obj.left.reprW.inv)).op)
  map_id s := by
    have : CommaMorphism.left (𝟙 s.unop) = 𝟙 (s.unop.obj.left) := rfl
    simp [this]
  map_comp {s s' s''} f g := by
    rw [← G.map_comp, ← op_comp, ← Yoneda.fullyFaithful.preimage_comp]
    have : (g.unop ≫ f.unop).left = g.unop.left ≫ f.unop.left := rfl
    simp [this]

/- def morphismsEquivSections :
    (F ⟶ G) ≃ Limits.limit (sectionsOverFunctor F G) -/

end-/
