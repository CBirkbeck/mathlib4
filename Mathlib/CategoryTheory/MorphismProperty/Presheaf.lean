/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
-/

import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!

# Representable morphisms of presheaves

In this file we define and develop basic results on the representability of morphisms of presheaves.

## Main definitions

* `Presheaf.representable` is a `MorphismProperty` expressing the fact that a morphism of presheaves
  is representable.
* `MorphismProperty.presheaf`: given a `P : MorphismProperty C`, we say that a morphism of
  presheaves `f : F ⟶ G` satisfies `P.presheaf` if it is representable, and the property `P`
  holds for the preimage under yoneda of pullbacks of `f` by morphisms `g : yoneda.obj X ⟶ G`.

## API


## Main results
* `representable_isStableUnderComposition`: Being representable is stable under composition.
* `representable_stableUnderBaseChange`: Being representable is stable under base change.
* `representable_ofIso`: Isomorphisms are representable

* `presheaf_yoneda_map`: If `f : X ⟶ Y` satisfies `P`, and `P` is stable under compostions,
  then `yoneda.map f` satisfies `P.presheaf`.

For the following results, we assume that `P : MorphismProperty C` is stable under base change:
* `presheaf_stableUnderBaseChange`: `P.presheaf` is stable under base change
* `presheaf_respectsIso`: `P.presheaf` respects isomorphisms
* `presheaf_isStableUnderComp`: If `P` is stable under composition, then so is `P.presheaf`

-/


namespace CategoryTheory

open Category Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- A morphism of presheaves `f : F ⟶ G` is representable if for any `X : C`, and any morphism
`g : yoneda.obj X ⟶ G`, there exists a pullback square
```
yoneda.obj Y --yoneda.map snd--> yoneda.obj X
    |                                |
   fst                               g
    |                                |
    v                                v
    F ------------ f --------------> G
``` -/
def Presheaf.representable : MorphismProperty (Cᵒᵖ ⥤ Type v) :=
  fun F G f ↦ ∀ ⦃X : C⦄ (g : yoneda.obj X ⟶ G), ∃ (Y : C) (snd : Y ⟶ X)
    (fst : yoneda.obj Y ⟶ F), IsPullback fst (yoneda.map snd) f g

namespace Presheaf.representable

section

variable {F G : Cᵒᵖ ⥤ Type v} {f : F ⟶ G} (hf : Presheaf.representable f)
  {Y : C} {f' : yoneda.obj Y ⟶ G} (hf' : Presheaf.representable f')
  {X : C} (g : yoneda.obj X ⟶ G) (hg : Presheaf.representable g)

/-- Let `f : F ⟶ G` be a representable morphism in the category of presheaves of types on
a category `C`. Then, for any `g : yoneda.obj X ⟶ G`, `hf.pullback g` denotes the (choice of) a
corresponding object in `C` such that `yoneda.obj (hf.pullback g)` forms a categorical pullback
of `f` and `g` in the category of presheaves. -/
noncomputable def pullback : C :=
  (hf g).choose

/-- Given a representable morphism `f : F ⟶ G`, then for any `g : yoneda.obj X ⟶ G`, `hf.snd g`
denotes the morphism in `C` whose image under `yoneda` is the second projection in the choice of a
pullback square given by the defining property of `f` being representable. -/
noncomputable abbrev snd : hf.pullback g ⟶ X :=
  (hf g).choose_spec.choose

/-- Given a representable morphism `f : F ⟶ G`, then for any `g : yoneda.obj X ⟶ G`, `hf.fst g`
denotes the first projection in the choice of a pullback square given by the defining property of
`f` being representable. -/
noncomputable abbrev fst : yoneda.obj (hf.pullback g) ⟶ F :=
  (hf g).choose_spec.choose_spec.choose

/-- Given a representable morphism `f' : yoneda.obj Y ⟶ G`, `hf'.fst' g` denotes the preimage of
`hf'.fst g` under yoneda. -/
noncomputable abbrev fst' : hf'.pullback g ⟶ Y :=
  Yoneda.fullyFaithful.preimage (hf'.fst g)

lemma yoneda_map_fst' : yoneda.map (hf'.fst' g) = hf'.fst g :=
  Functor.FullyFaithful.map_preimage _ _

lemma isPullback : IsPullback (hf.fst g) (yoneda.map (hf.snd g)) f g :=
  (hf g).choose_spec.choose_spec.choose_spec

/-- Variant of the pullback square when the first projection lies in the image of yoneda. -/
lemma isPullback' : IsPullback (yoneda.map (hf'.fst' g)) (yoneda.map (hf'.snd g)) f' g :=
  (hf'.yoneda_map_fst' _) ▸ (hf' g).choose_spec.choose_spec.choose_spec


-- TODO should be isPullbackPre (& then get w from IsPullback.w?).
/-- Given a representable morphism `f' :  yoneda.obj Y ⟶ yoneda.obj Z`, and a morphism
`g : ....`, this is a .....

Variant of `hf'.i` when all vertices of the pullback square lie in the image of yoneda. -/
@[reassoc]
lemma w' {X Y Z : C} {f : X ⟶ Z} (g : yoneda.obj Y ⟶ yoneda.obj Z)
    (hf : Presheaf.representable (yoneda.map f)) :
      hf.fst' g ≫ f = hf.snd g ≫ (Yoneda.fullyFaithful.preimage g) :=
  yoneda.map_injective <| by simp [(hf.isPullback g).w]

variable {g}

/-- Two morphisms `a b : Z ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf.snd g : hf.pullback  ⟶ X` are equal.
* The compositions of `yoneda.map a` and `yoneda.map b` with `hf.fst g` are equal. -/
@[ext 100]
lemma hom_ext {Z : C} {a b : Z ⟶ hf.pullback g}
    (h₁ : yoneda.map a ≫ hf.fst g = yoneda.map b ≫ hf.fst g)
    (h₂ : a ≫ hf.snd g = b ≫ hf.snd g) : a = b :=
  yoneda.map_injective <|
    PullbackCone.IsLimit.hom_ext (hf.isPullback g).isLimit h₁ (by simpa using yoneda.congr_map h₂)

/-- In the case of a representable morphism `f' : yoneda.obj Y ⟶ G`, whose codomain lies
in the image of yoneda, we get that two morphism `a b : Z ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf'.snd g : hf.pullback  ⟶ X` are equal.
* Their compositions (in `C`) with `hf'.fst' g : hf.pullback  ⟶ Y` are equal. -/
@[ext]
lemma hom_ext' {Z : C} {a b : Z ⟶ hf'.pullback g} (h₁ : a ≫ hf'.fst' g = b ≫ hf'.fst' g)
    (h₂ : a ≫ hf'.snd g = b ≫ hf'.snd g) : a = b :=
  hf'.hom_ext (by simpa [yoneda_map_fst'] using yoneda.congr_map h₁) h₂

section

variable {Z : C} (i : yoneda.obj Z ⟶ F) (h : Z ⟶ X) (hi : i ≫ f = yoneda.map h ≫ g)

/-- The lift (in `C`) obtained from the universal property of `yoneda.obj (hf.pullback g)`, in the
case when the cone point is in the image of `yoneda.obj`. -/
noncomputable def lift : Z ⟶ hf.pullback g :=
  Yoneda.fullyFaithful.preimage <| PullbackCone.IsLimit.lift (hf.isPullback g).isLimit _ _ hi

@[reassoc (attr := simp)]
lemma lift_fst : yoneda.map (hf.lift i h hi) ≫ hf.fst g = i := by
  simpa [lift] using PullbackCone.IsLimit.lift_fst _ _ _ _


@[reassoc (attr := simp)]
lemma lift_snd : hf.lift i h hi ≫ hf.snd g = h :=
  yoneda.map_injective <| by simpa [lift] using PullbackCone.IsLimit.lift_snd _ _ _ _

end

section

variable {Z : C} (i : Z ⟶ Y) (h : Z ⟶ X) (hi : (yoneda.map i) ≫ f' = yoneda.map h ≫ g)

/-- Variant of `lift` in the case when the domain of `f` lies in the image of `yoneda.obj`. Thus,
in this case, one can obtain the lift directly by giving two morphisms in `C`. -/
noncomputable def lift' : Z ⟶ hf'.pullback g := hf'.lift _ _ hi

@[reassoc (attr := simp)]
lemma lift'_fst : hf'.lift' i h hi ≫ hf'.fst' g = i :=
  yoneda.map_injective (by simp [yoneda_map_fst', lift'])

@[reassoc (attr := simp)]
lemma lift'_snd : hf'.lift' i h hi ≫ hf'.snd g = h := by
  simp [lift']

end

/-- Given two representable morphisms `f' : yoneda.obj Y ⟶ G` and `g : yoneda.obj X ⟶ G`, we
obtain an isomorphism `hf'.pullback g ⟶ hg.pullback f'`. -/
noncomputable def symmetry : hf'.pullback g ⟶ hg.pullback f' :=
  hg.lift' (hf'.snd g) (hf'.fst' g) (hf'.isPullback' _).w.symm

@[reassoc (attr := simp)]
lemma symmetry_fst : hf'.symmetry hg ≫ hg.fst' f' = hf'.snd g := by simp [symmetry]

@[reassoc (attr := simp)]
lemma symmetry_snd : hf'.symmetry hg ≫ hg.snd f' = hf'.fst' g := by simp [symmetry]

@[reassoc (attr := simp)]
lemma symmetry_symmetry : hf'.symmetry hg ≫ hg.symmetry hf' = 𝟙 _ := by aesop_cat

/-- The isomorphism given by `Presheaf.representable.symmetry`. -/
@[simps]
noncomputable def symmetryIso : hf'.pullback g ≅ hg.pullback f' where
  hom := hf'.symmetry hg
  inv := hg.symmetry hf'

instance : IsIso (hf'.symmetry hg) :=
  (hf'.symmetryIso hg).isIso_hom

end

/-- When `C` has pullbacks, then `yoneda.map f` is representable for any `f : X ⟶ Y`. -/
lemma yoneda_map [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    Presheaf.representable (yoneda.map f) := fun Z g ↦ by
  obtain ⟨g, rfl⟩ := yoneda.map_surjective g
  refine ⟨Limits.pullback f g, Limits.pullback.snd f g, yoneda.map (Limits.pullback.fst f g), ?_⟩
  apply yoneda.map_isPullback <| IsPullback.of_hasPullback f g

end Presheaf.representable

namespace MorphismProperty

variable {F G : Cᵒᵖ ⥤ Type v} (P : MorphismProperty C)

/-- Given a morphism property `P` in a category `C`, a morphism `f : F ⟶ G` of presheaves in the
category `Cᵒᵖ ⥤ Type v` satisfies the morphism property `P.presheaf` iff:
* The morphism is representable.
* The property `P` holds for the (choice of a) representable pullback of `f`, along any morphism
`g : yoneda.obj X ⟶ G`.

See `presheaf.property'` for the fact that `P` holds for *any* representable pullback of `f` by a
morphism `g : yoneda.obj X ⟶ G`. -/
def presheaf : MorphismProperty (Cᵒᵖ ⥤ Type v) :=
  fun F G f ↦ Presheaf.representable f ∧
    ∀ ⦃X Y : C⦄ (g : yoneda.obj X ⟶ G) (fst : yoneda.obj Y ⟶ F) (snd : Y ⟶ X)
      (_ : IsPullback fst (yoneda.map snd) f g), P snd

variable {P}

/-- A morphism satisfying `P.presheaf` is representable. -/
lemma presheaf.rep {f : F ⟶ G} (hf : P.presheaf f) : Presheaf.representable f :=
  hf.1

lemma presheaf.property {f : F ⟶ G} (hf : P.presheaf f) :
    ∀ ⦃X Y : C⦄ (g : yoneda.obj X ⟶ G) (fst : yoneda.obj Y ⟶ F) (snd : Y ⟶ X)
    (_ : IsPullback fst (yoneda.map snd) f g), P snd :=
  hf.2

lemma presheaf.property_snd {f : F ⟶ G} (hf : P.presheaf f) {X : C} (g : yoneda.obj X ⟶ G) :
    P (hf.rep.snd g) :=
  hf.property g _ _ (hf.rep.isPullback g)

lemma presheaf_of_exists [P.RespectsIso] {f : F ⟶ G} (hf : Presheaf.representable f)
    (h₀ : ∀ ⦃X : C⦄ (g : yoneda.obj X ⟶ G), ∃ (Y : C) (fst : yoneda.obj Y ⟶ F) (snd : Y ⟶ X)
    (_ : IsPullback fst (yoneda.map snd) f g), P snd) : P.presheaf f := by
  refine ⟨hf, fun X Y g fst snd h ↦ ?_⟩
  obtain ⟨Y, g_fst, g_snd, BC, H⟩ := h₀ g
  refine (P.arrow_mk_iso_iff ?_).2 H
  exact Arrow.isoMk (Yoneda.fullyFaithful.preimageIso (h.isoIsPullback BC)) (Iso.refl _)
    (yoneda.map_injective (by simp))

lemma presheaf_of_snd [P.RespectsIso] {f : F ⟶ G} (hf : Presheaf.representable f)
    (h : ∀ ⦃X : C⦄ (g : yoneda.obj X ⟶ G), P (hf.snd g)) : P.presheaf f :=
  presheaf_of_exists hf (fun _ g ↦ ⟨hf.pullback g, hf.fst g, hf.snd g, hf.isPullback g, h g⟩)

/-- If `P : MorphismProperty C` is stable under base change, then for any `f : X ⟶ Y` in `C`,
`yoneda.map f` satisfies `P.presheaf` if `f` does. -/
-- TODO: converse!
lemma presheaf_yoneda_map [HasPullbacks C] (hP : StableUnderBaseChange P) {X Y : C} {f : X ⟶ Y}
    (hf : P f) : P.presheaf (yoneda.map f) := by
  have := StableUnderBaseChange.respectsIso hP
  apply presheaf_of_snd (Presheaf.representable.yoneda_map f)
  intro Z g
  apply hP (f := (Yoneda.fullyFaithful.preimage g))
    (f' := (Presheaf.representable.yoneda_map f).fst' g)  _ hf
  apply IsPullback.of_map yoneda ((Presheaf.representable.yoneda_map f).w' g)
  simpa using (Presheaf.representable.yoneda_map f).isPullback g

lemma presheaf_of_yoneda {X Y : C} {f : X ⟶ Y} (hf : P.presheaf (yoneda.map f)) : P f :=
  hf.property (𝟙 _) (𝟙 _) f (IsPullback.id_horiz (yoneda.map f))

/-- Morphisms satisfying `(monomorphism C).presheaf` are in particular monomorphisms.-/
lemma presheaf_monomorphisms_le_monomorphisms :
    (monomorphisms C).presheaf ≤ monomorphisms _ := fun F G f hf ↦ by
  suffices ∀ {X : C} {a b : yoneda.obj X ⟶ F}, a ≫ f = b ≫ f → a = b from
    ⟨fun _ _ h ↦ hom_ext_yoneda (fun _ _ ↦ this (by simp only [assoc, h]))⟩
  intro X a b h
  /- It suffices to show that the lifts of `a` and `b` to morphisms
  `X ⟶ hf.rep.pullback g` are equal, where `g = a ≫ f = a ≫ f`. -/
  suffices hf.rep.lift (g := a ≫ f) a (𝟙 X) (by simp) =
      hf.rep.lift b (𝟙 X) (by simp [← h]) by
    simpa using yoneda.congr_map this =≫ (hf.rep.fst (a ≫ f))
  -- This follows from the fact that the induced maps `hf.rep.pullback g ⟶ X` are Mono.
  have : Mono (hf.rep.snd (a ≫ f)) := hf.property_snd (a ≫ f)
  simp only [← cancel_mono (hf.rep.snd (a ≫ f)),
    Presheaf.representable.lift_snd]

/-- If `P' : MorphismProperty C` is satisfied whenever `P` is, then also `P'.presheaf` is
satisfied whenever `P.presheaf` is. -/
lemma presheaf_monotone {P' : MorphismProperty C} (h : P ≤ P') :
    P.presheaf ≤ P'.presheaf := fun _ _ _ hf ↦
  ⟨hf.rep, fun _ _ g fst snd BC ↦ h _ (hf.property g fst snd BC)⟩

instance representable_isStableUnderComposition :
    IsStableUnderComposition (Presheaf.representable (C := C)) where
  comp_mem {F G H} f g hf hg := fun X h ↦
    ⟨hf.pullback (hg.fst h), hf.snd (hg.fst h) ≫ hg.snd h, hf.fst (hg.fst h),
      by simpa using IsPullback.paste_vert (hf.isPullback (hg.fst h)) (hg.isPullback h)⟩

lemma representable_stableUnderBaseChange :
    StableUnderBaseChange (Presheaf.representable (C := C)) := by
  intro F G G' H f g f' g' P₁ hg X h
  refine ⟨hg.pullback (h ≫ f), hg.snd (h ≫ f), ?_, ?_⟩
  apply P₁.lift (hg.fst (h ≫ f)) (yoneda.map (hg.snd (h ≫ f)) ≫ h) (hg.isPullback (h ≫ f)).w
  apply IsPullback.of_right' (hg.isPullback (h ≫ f)) P₁

lemma representable_ofIsIso {F G : Cᵒᵖ ⥤ Type v} (f : F ⟶ G) [IsIso f] :
    Presheaf.representable f :=
  fun X g ↦ ⟨X, 𝟙 X, g ≫ inv f, IsPullback.of_vert_isIso ⟨by simp⟩⟩

lemma representable_isomorphisms_le :
    MorphismProperty.isomorphisms (Cᵒᵖ ⥤ Type v) ≤ Presheaf.representable :=
  fun _ _ f hf ↦ letI : IsIso f := hf; representable_ofIsIso f

lemma representable_respectsIso : RespectsIso (Presheaf.representable (C:=C)) :=
  representable_stableUnderBaseChange.respectsIso

section

variable (P)

lemma presheaf_stableUnderBaseChange : StableUnderBaseChange P.presheaf :=
  fun _ _ _ _ _ _ _ _ hfBC hg ↦
  ⟨representable_stableUnderBaseChange hfBC hg.rep,
    fun _ _ _ _ _ BC ↦ hg.property _ _ _ (IsPullback.paste_horiz BC hfBC)⟩

instance presheaf_isStableUnderComposition' [P.IsStableUnderComposition] :
    IsStableUnderComposition P.presheaf where
  comp_mem {F G H} f g hf hg := by
    refine ⟨comp_mem _ _ _ hf.1 hg.1, fun Z X p fst snd h ↦ ?_⟩
    rw [← hg.1.lift_snd (fst ≫ f) snd (by simpa using h.w)]
    refine comp_mem _ _ _ (hf.property (hg.1.fst p) fst _
      (IsPullback.of_bot ?_ ?_ (hg.1.isPullback p))) (hg.property_snd p)
    · rw [← Functor.map_comp, Presheaf.representable.lift_snd]
      exact h
    · symm
      apply hg.1.lift_fst

instance presheaf_respectsIso : RespectsIso P.presheaf :=
  (presheaf_stableUnderBaseChange P).respectsIso

end

end MorphismProperty

end CategoryTheory
