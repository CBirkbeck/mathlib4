/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Oplax

/-!
# Oplax natural transformations

Just as there are natural transformations between functors, there are oplax natural transformations
between oplax functors. The equality in the naturality of natural transformations is replaced by a
specified 2-morphism `F.map f ≫ app b ⟶ app a ≫ G.map f` in the case of oplax natural
transformations.

## Main definitions

* `OplaxNatTrans F G` : oplax natural transformations between oplax functors `F` and `G`
* `OplaxNatTrans.vcomp η θ` : the vertical composition of oplax natural transformations `η`
  and `θ`
* `OplaxNatTrans.category F G` : the category structure on the oplax natural transformations
  between `F` and `G`
-/

namespace CategoryTheory

open Category Bicategory

open scoped Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- If `η` is an oplax natural transformation between `F` and `G`, we have a 1-morphism
`η.app a : F.obj a ⟶ G.obj a` for each object `a : B`. We also have a 2-morphism
`η.naturality f : F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism `f : a ⟶ b`.
These 2-morphisms satisfies the naturality condition, and preserve the identities and
the compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
structure OplaxNatTrans (F G : OplaxFunctor B C) where
  app (a : B) : F.obj a ⟶ G.obj a
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ⟶ app a ≫ G.map f
  naturality_naturality :
    ∀ {a b : B} {f g : a ⟶ b} (η : f ⟶ g),
      F.map₂ η ▷ app b ≫ naturality g = naturality f ≫ app a ◁ G.map₂ η := by
    aesop_cat
  naturality_id :
    ∀ a : B,
      naturality (𝟙 a) ≫ app a ◁ G.mapId a =
        F.mapId a ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv := by
    aesop_cat
  naturality_comp :
    ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
      naturality (f ≫ g) ≫ app a ◁ G.mapComp f g =
        F.mapComp f g ▷ app c ≫
          (α_ _ _ _).hom ≫
            F.map f ◁ naturality g ≫ (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom := by
    aesop_cat

attribute [nolint docBlame] CategoryTheory.OplaxNatTrans.app
  CategoryTheory.OplaxNatTrans.naturality
  CategoryTheory.OplaxNatTrans.naturality_naturality
  CategoryTheory.OplaxNatTrans.naturality_id
  CategoryTheory.OplaxNatTrans.naturality_comp

attribute [reassoc (attr := simp)] OplaxNatTrans.naturality_naturality OplaxNatTrans.naturality_id
  OplaxNatTrans.naturality_comp

namespace OplaxNatTrans

section

variable (F : OplaxFunctor B C)

/-- The identity oplax natural transformation. -/
@[simps]
def id : OplaxNatTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {a b} f := (ρ_ (F.map f)).hom ≫ (λ_ (F.map f)).inv

instance : Inhabited (OplaxNatTrans F F) :=
  ⟨id F⟩

variable {F} {G H : OplaxFunctor B C} (η : OplaxNatTrans F G) (θ : OplaxNatTrans G H)

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ θ.naturality h =
      f ◁ θ.naturality g ≫ f ◁ θ.app a ◁ H.map₂ β := by
  simp_rw [← whiskerLeft_comp, naturality_naturality]

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') :
    F.map₂ β ▷ η.app b ▷ h ≫ η.naturality g ▷ h =
      η.naturality f ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h ≫ (α_ _ _ _).inv := by
  rw [← comp_whiskerRight, naturality_naturality, comp_whiskerRight, whisker_assoc]

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
    f ◁ θ.naturality (g ≫ h) ≫ f ◁ θ.app a ◁ H.mapComp g h =
      f ◁ G.mapComp g h ▷ θ.app c ≫
        f ◁ (α_ _ _ _).hom ≫
          f ◁ G.map g ◁ θ.naturality h ≫
            f ◁ (α_ _ _ _).inv ≫ f ◁ θ.naturality g ▷ H.map h ≫ f ◁ (α_ _ _ _).hom := by
  simp_rw [← whiskerLeft_comp, naturality_comp]

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
    η.naturality (f ≫ g) ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapComp f g ▷ h =
      F.mapComp f g ▷ η.app c ▷ h ≫
        (α_ _ _ _).hom ▷ h ≫
          (α_ _ _ _).hom ≫
            F.map f ◁ η.naturality g ▷ h ≫
              (α_ _ _ _).inv ≫
                (α_ _ _ _).inv ▷ h ≫
                  η.naturality f ▷ G.map g ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom := by
  rw [← associator_naturality_middle, ← comp_whiskerRight_assoc, naturality_comp]; simp

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_id (f : a' ⟶ G.obj a) :
    f ◁ θ.naturality (𝟙 a) ≫ f ◁ θ.app a ◁ H.mapId a =
      f ◁ G.mapId a ▷ θ.app a ≫ f ◁ (λ_ (θ.app a)).hom ≫ f ◁ (ρ_ (θ.app a)).inv := by
  simp_rw [← whiskerLeft_comp, naturality_id]

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_id (f : G.obj a ⟶ a') :
    η.naturality (𝟙 a) ▷ f ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapId a ▷ f =
    F.mapId a ▷ η.app a ▷ f ≫ (λ_ (η.app a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫ (α_ _ _ _).hom := by
  rw [← associator_naturality_middle, ← comp_whiskerRight_assoc, naturality_id]; simp

end

/-- Vertical composition of oplax natural transformations. -/
@[simps]
def vcomp (η : OplaxNatTrans F G) (θ : OplaxNatTrans G H) : OplaxNatTrans F H where
  app a := η.app a ≫ θ.app a
  naturality {a b} f :=
    (α_ _ _ _).inv ≫
      η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom ≫ η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv
  naturality_comp {a b c} f g := by
    calc
      _ =
          ?_ ≫
            F.mapComp f g ▷ η.app c ▷ θ.app c ≫
              ?_ ≫
                F.map f ◁ η.naturality g ▷ θ.app c ≫
                  ?_ ≫
                    (F.map f ≫ η.app b) ◁ θ.naturality g ≫
                      η.naturality f ▷ (θ.app b ≫ H.map g) ≫
                        ?_ ≫ η.app a ◁ θ.naturality f ▷ H.map g ≫ ?_ :=
        ?_
      _ = _ := ?_
    · exact (α_ _ _ _).inv
    · exact (α_ _ _ _).hom ▷ _ ≫ (α_ _ _ _).hom
    · exact _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv
    · exact (α_ _ _ _).hom ≫ _ ◁ (α_ _ _ _).inv
    · exact _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv
    · rw [whisker_exchange_assoc]
      simp
    · simp

variable (B C)

@[simps id comp]
instance : CategoryStruct (OplaxFunctor B C) where
  Hom := OplaxNatTrans
  id := OplaxNatTrans.id
  comp := OplaxNatTrans.vcomp

end

/-- A structure on an Oplax natural transformation that promotes it to a strong natural
transformation.

See `StrongNatTrans.mkOfOplax`. -/
structure StrongCore {F G : OplaxFunctor B C} (η : OplaxNatTrans F G) where
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ η.app b ≅ η.app a ≫ G.map f
  naturality_hom {a b : B} (f : a ⟶ b) : (naturality f).hom = η.naturality f := by aesop_cat

attribute [nolint docBlame] CategoryTheory.OplaxNatTrans.StrongCore.naturality
  CategoryTheory.OplaxNatTrans.StrongCore.naturality_hom

attribute [simp] StrongCore.naturality_hom

end OplaxNatTrans

/-- A strong natural transformation between oplax functors `F` and `G` is a natural transformation
that is "natural up to 2-isomorphisms".

More precisely, it consists of the following:
* a 1-morphism `η.app a : F.obj a ⟶ G.obj a` for each object `a : B`.
* a 2-isomorphism `η.naturality f : F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism
`f : a ⟶ b`.
* These 2-isomorphisms satisfy the naturality condition, and preserve the identities and the
compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
structure StrongOplaxNatTrans (F G : OplaxFunctor B C) where
  app (a : B) : F.obj a ⟶ G.obj a
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ≅ app a ≫ G.map f
  naturality_naturality :
    ∀ {a b : B} {f g : a ⟶ b} (η : f ⟶ g),
      F.map₂ η ▷ app b ≫ (naturality g).hom = (naturality f).hom ≫ app a ◁ G.map₂ η := by
    aesop_cat
  naturality_id :
    ∀ a : B,
      (naturality (𝟙 a)).hom ≫ app a ◁ G.mapId a =
        F.mapId a ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv := by
    aesop_cat
  naturality_comp :
    ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
      (naturality (f ≫ g)).hom ≫ app a ◁ G.mapComp f g =
        F.mapComp f g ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫
        (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom := by
    aesop_cat

attribute [nolint docBlame] CategoryTheory.StrongOplaxNatTrans.app
  CategoryTheory.StrongOplaxNatTrans.naturality
  CategoryTheory.StrongOplaxNatTrans.naturality_naturality
  CategoryTheory.StrongOplaxNatTrans.naturality_id
  CategoryTheory.StrongOplaxNatTrans.naturality_comp

attribute [reassoc (attr := simp)] StrongOplaxNatTrans.naturality_naturality
  StrongOplaxNatTrans.naturality_id StrongOplaxNatTrans.naturality_comp

namespace StrongOplaxNatTrans

section

/-- The underlying oplax natural transformation of a strong natural transformation. -/
@[simps]
def toOplax {F G : OplaxFunctor B C} (η : StrongOplaxNatTrans F G) : OplaxNatTrans F G where
  app := η.app
  naturality f := (η.naturality f).hom

/-- Construct a strong natural transformation from an oplax natural transformation whose
naturality 2-cell is an isomorphism. -/
def mkOfOplax {F G : OplaxFunctor B C} (η : OplaxNatTrans F G) (η' : OplaxNatTrans.StrongCore η) :
    StrongOplaxNatTrans F G where
  app := η.app
  naturality := η'.naturality

/-- Construct a strong natural transformation from an oplax natural transformation whose
naturality 2-cell is an isomorphism. -/
noncomputable def mkOfOplax' {F G : OplaxFunctor B C} (η : OplaxNatTrans F G)
    [∀ a b (f : a ⟶ b), IsIso (η.naturality f)] : StrongOplaxNatTrans F G where
  app := η.app
  naturality := fun f => asIso (η.naturality _)

variable (F : OplaxFunctor B C)


/-- The identity strong natural transformation. -/
@[simps!]
def id : StrongOplaxNatTrans F F :=
  mkOfOplax (OplaxNatTrans.id F) { naturality := λ f ↦ (ρ_ (F.map f)) ≪≫ (λ_ (F.map f)).symm }

@[simp]
lemma id.toOplax : (id F).toOplax = OplaxNatTrans.id F :=
  rfl

instance : Inhabited (StrongOplaxNatTrans F F) :=
  ⟨id F⟩

variable {F} {G H : OplaxFunctor B C} (η : StrongOplaxNatTrans F G) (θ : StrongOplaxNatTrans G H)

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ (θ.naturality h).hom =
      f ◁ (θ.naturality g).hom ≫ f ◁ θ.app a ◁ H.map₂ β := by
  apply θ.toOplax.whiskerLeft_naturality_naturality

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') :
    F.map₂ β ▷ η.app b ▷ h ≫ (η.naturality g).hom ▷ h =
      (η.naturality f).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h ≫ (α_ _ _ _).inv := by
  apply η.toOplax.whiskerRight_naturality_naturality

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
    f ◁ (θ.naturality (g ≫ h)).hom ≫ f ◁ θ.app a ◁ H.mapComp g h =
      f ◁ G.mapComp g h ▷ θ.app c ≫
        f ◁ (α_ _ _ _).hom ≫
          f ◁ G.map g ◁ (θ.naturality h).hom ≫
            f ◁ (α_ _ _ _).inv ≫ f ◁ (θ.naturality g).hom ▷ H.map h ≫ f ◁ (α_ _ _ _).hom := by
  apply θ.toOplax.whiskerLeft_naturality_comp

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
    (η.naturality (f ≫ g)).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapComp f g ▷ h =
      F.mapComp f g ▷ η.app c ▷ h ≫
        (α_ _ _ _).hom ▷ h ≫
          (α_ _ _ _).hom ≫
            F.map f ◁ (η.naturality g).hom ▷ h ≫
              (α_ _ _ _).inv ≫
                (α_ _ _ _).inv ▷ h ≫
                 (η.naturality f).hom ▷ G.map g ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom := by
  apply η.toOplax.whiskerRight_naturality_comp

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_id (f : a' ⟶ G.obj a) :
    f ◁ (θ.naturality (𝟙 a)).hom ≫ f ◁ θ.app a ◁ H.mapId a =
      f ◁ G.mapId a ▷ θ.app a ≫ f ◁ (λ_ (θ.app a)).hom ≫ f ◁ (ρ_ (θ.app a)).inv := by
  apply θ.toOplax.whiskerLeft_naturality_id

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_id (f : G.obj a ⟶ a') :
    (η.naturality (𝟙 a)).hom ▷ f ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapId a ▷ f =
    F.mapId a ▷ η.app a ▷ f ≫ (λ_ (η.app a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫
    (α_ _ _ _).hom := by
  apply η.toOplax.whiskerRight_naturality_id

end

/-- Vertical composition of strong natural transformations. -/
@[simps!]
def vcomp (η : StrongOplaxNatTrans F G) (θ : StrongOplaxNatTrans G H) : StrongOplaxNatTrans F H :=
  mkOfOplax (OplaxNatTrans.vcomp η.toOplax θ.toOplax)
    { naturality := λ {a b} f ↦
        (α_ _ _ _).symm ≪≫ whiskerRightIso (η.naturality f) (θ.app b) ≪≫
        (α_ _ _ _) ≪≫ whiskerLeftIso (η.app a) (θ.naturality f) ≪≫ (α_ _ _ _).symm }
end

end StrongOplaxNatTrans

end CategoryTheory
