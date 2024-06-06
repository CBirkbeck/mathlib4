import Mathlib.CategoryTheory.GroupObjects.PreservesFiniteProducts
import Mathlib.CategoryTheory.GroupObjects.StupidLemmas
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Bicategory.Functor

open CategoryTheory Limits

noncomputable section

universe v u

namespace FullSubcategory

variable {C : Type u} [Category.{v,u} C] (P : C → Prop) {X Y : FullSubcategory P} (f : X.1 ≅ Y.1)

@[simp]
def isoOfAmbientIso : X ≅ Y :=
  {hom := f.hom, inv := f.inv, hom_inv_id := f.hom_inv_id, inv_hom_id := f.inv_hom_id}

end FullSubcategory

namespace CategoryTheory.Bicategory

variable (C : Type*) [Category C] (P : C → Prop) (X Y : C) (f : X ≅ Y) (hX : P X) (hY : P Y)

example : (⟨X, hX⟩ : FullSubcategory P) ≅ ⟨Y, hY⟩ := by
  refine {hom := f.hom, inv := f.inv, hom_inv_id := ?_, inv_hom_id := ?_}
  exact f.hom_inv_id
  exact f.inv_hom_id

instance CatBicat : Bicategory Cat.{v,u} where
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  associator := Functor.associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  whiskerLeft_id := whiskerLeft_id
  whiskerLeft_comp := whiskerLeft_comp
  id_whiskerLeft := id_whiskerLeft
  comp_whiskerLeft := comp_whiskerLeft
  id_whiskerRight := id_whiskerRight
  comp_whiskerRight := comp_whiskerRight
  whiskerRight_id := whiskerRight_id
  whiskerRight_comp := whiskerRight_comp
  whisker_assoc := by
    intro A B C D F G G' α H
    simp only [whisker_assoc, Strict.associator_eqToIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
      Category.id_comp]
    change (_ : F ⋙ G ⋙ H ⟶ (F ⋙ G') ⋙ H) = _
    ext
    simp only [Cat.comp_obj]
    rw [NatTrans.comp_app, NatTrans.id_app]; erw [Category.comp_id, whiskerRight_app]
    rw [NatTrans.comp_app, NatTrans.comp_app]; erw [whiskerRight_app];
    rw [Functor.associator_hom_app, Functor.associator_inv_app]
    erw [Category.id_comp, Category.comp_id]
  whisker_exchange := by
    intro C D E F F' G G' α β
    simp only
    change (_ : F ⋙ G ⟶ F' ⋙ G') = _
    ext
    simp only [Functor.comp_obj, NatTrans.comp_app, Cat.comp_obj]
    erw [NatTrans.comp_app, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      whiskerRight_app, whiskerLeft_app F' β]
    simp only [Functor.comp_obj, Cat.comp_obj, NatTrans.naturality]
  pentagon := Functor.pentagon

  instance CatFiniteProducts : Bicategory {C : Cat.{v,u} // HasFiniteProducts C} where
  Hom C D := FullSubcategory (fun (F : C ⥤ D) ↦ Nonempty (PreservesFiniteProducts F))
  id C := ⟨Functor.id C.1, Nonempty.intro inferInstance⟩
  comp F G := ⟨F.1 ⋙ G.1, Nonempty.intro (@Limits.compPreservesFiniteProducts _ _ _ _
      _ _ F.1 G.1 (Classical.choice F.2) (Classical.choice G.2))⟩
  homCategory C D := FullSubcategory.category (fun F ↦ Nonempty (PreservesFiniteProducts F))
  whiskerLeft := by
    intro C D E F G H α
    exact CategoryTheory.whiskerLeft F.1 (α : G.1 ⟶ H.1)
  whiskerRight α H := CategoryTheory.whiskerRight α H.1
  associator F G H := FullSubcategory.isoOfAmbientIso _ (Functor.associator F.1 G.1 H.1)
  leftUnitor F := FullSubcategory.isoOfAmbientIso _ (Functor.leftUnitor F.1)
  rightUnitor F := FullSubcategory.isoOfAmbientIso _ (Functor.rightUnitor F.1)
  whiskerLeft_id := by
    intro C D E F G
    change CategoryTheory.whiskerLeft F.1 (NatTrans.id G.1) = _
    rw [CategoryTheory.whiskerLeft_id F.1 (G := G.1)]
    rfl
  whiskerLeft_comp := by
    intro C D E F G₁ G₂ G₃ α β
    exact CategoryTheory.whiskerLeft_comp F.1 α β
  id_whiskerLeft := by
    intro C D F G α
    simp only [FullSubcategory.isoOfAmbientIso]
    change (_ : 𝟭 ↑↑C ⋙ F.obj ⟶ 𝟭 ↑↑C ⋙ G.obj) = _
    ext
    simp only [Functor.comp_obj, Functor.id_obj, whiskerLeft_app]
    erw [NatTrans.comp_app, NatTrans.comp_app]
    rw [Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app, Category.comp_id]
    erw [Category.id_comp]
  comp_whiskerLeft := by
    intro A B C D F G H H' α
    simp only [FullSubcategory.isoOfAmbientIso, whiskerLeft_twice]
    change (_ : (F.1 ⋙ G.1) ⋙ H.1 ⟶ (F.1 ⋙ G.1) ⋙ H'.1) = _
    ext
    simp only [Functor.comp_obj, whiskerLeft_app]
    erw [NatTrans.comp_app, NatTrans.comp_app]
    rw [Functor.associator_hom_app, Functor.associator_inv_app]
    rw [Category.comp_id, Category.id_comp]
    simp only [whiskerLeft_app, Functor.comp_obj]
  id_whiskerRight := by
    intro C D E F G
    exact CategoryTheory.whiskerRight_id' G.1 (G := F.1)
  comp_whiskerRight := by
    intro C D E F G H α β γ
    change (_ : F.obj ⋙ γ.obj ⟶ H.obj ⋙ γ.obj) = _
    ext
    simp only [Functor.comp_obj, whiskerRight_app]
    erw [NatTrans.comp_app, NatTrans.comp_app]
    rw [whiskerRight_app, whiskerRight_app]
    simp only [Functor.map_comp, Functor.comp_obj]
  whiskerRight_id := by
    intro C D F G α
    simp only [FullSubcategory.isoOfAmbientIso]
    change (_ : F.obj ⋙ 𝟭 ↑↑D ⟶ G.obj ⋙ 𝟭 ↑↑D) = _
    ext
    simp only [Functor.comp_obj, Functor.id_obj, whiskerRight_app, Functor.id_map]
    erw [NatTrans.comp_app, NatTrans.comp_app]
    rw [Functor.rightUnitor_hom_app, Functor.rightUnitor_inv_app, Category.comp_id]
    erw [Category.id_comp]
  whiskerRight_comp := by
    intro A B C D F F' α G H
    simp only [FullSubcategory.isoOfAmbientIso, whiskerRight_twice]
    change (_ : F.1 ⋙ G.1 ⋙ H.1 ⟶ F'.1 ⋙ G.1 ⋙ H.1) = _
    ext
    simp only [Functor.comp_obj, whiskerRight_app, Functor.comp_map]
    repeat (erw [NatTrans.comp_app])
    rw [whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app]
    rw [Category.comp_id, Category.id_comp]
    simp only [Functor.comp_map]
  whisker_assoc := by
    intro A B C D F G G' α H
    simp only [FullSubcategory.isoOfAmbientIso]
    change (_ : (F.1 ⋙ G.1) ⋙ H.1 ⟶ (F.1 ⋙ G'.1) ⋙ H.1) = _
    ext
    simp only [Functor.comp_obj, whiskerRight_app, whiskerLeft_app]
    repeat (erw [NatTrans.comp_app])
    rw [Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
      Category.id_comp]
    simp only [whiskerLeft_app, whiskerRight_app]
  whisker_exchange := by
    intro C D E F F' G G' α β
    change (_ : F.1 ⋙ G.1 ⟶ F'.1 ⋙ G'.1) = _
    ext
    simp only [Functor.comp_obj]
    repeat (erw [NatTrans.comp_app])
    rw [whiskerLeft_app, whiskerRight_app, whiskerRight_app, whiskerLeft_app]
    simp only [Functor.comp_obj, NatTrans.naturality]
  pentagon := by
    intro C₁ C₂ C₃ C₄ C₅ F G H I
    simp only [FullSubcategory.isoOfAmbientIso]
    change (_ : ((F.1 ⋙ G.1) ⋙ H.1) ⋙ I.1 ⟶ F.1 ⋙ G.1 ⋙ H.1 ⋙ I.1) = _
    exact Functor.pentagon F.1 G.1 H.1 I.1
  triangle := by
    intro C D E F G
    simp only [FullSubcategory.isoOfAmbientIso]
    change (_ : (F.1 ⋙ 𝟭 _) ⋙ G.1 ⟶ F.1 ⋙ G.1) = _
    exact Functor.triangle F.1 G.1

end CategoryTheory.Bicategory

namespace CategoryTheory.GroupObject
open Bicategory

@[simp]
def oplaxFunctor_map {C D : {C : Cat.{v, u} // HasFiniteProducts C}} (F : C ⟶ D) :
    Cat.of (@GroupObject C.1 _ C.2) ⟶ Cat.of (@GroupObject D.1 _ D.2) :=
  @Functor.mapGroupObject C.1 _ D.1 _ C.2 D.2 F.1 (Classical.choice F.2)

@[simp]
def opLaxFunctor_mapId (C : {C : Cat.{v, u} // HasFiniteProducts C}) :
    @Functor.mapGroupObject C.1 _ C.1 _ C.2 C.2 (𝟙 C : C ⟶ C).1 (Classical.choice (𝟙 C : C ⟶ C).2)
    ⟶ CategoryTheory.CategoryStruct.id (Cat.of (@GroupObject C.1 _ C.2)) := by
    have := C.2
    change (_ : GroupObject C.1 ⥤ GroupObject C.1) ⟶ _
    refine {app := ?_, naturality := ?_}
    · intro X
      refine {hom := 𝟙 X.X, one_hom := ?_, mul_hom := ?_, inv_hom := ?_}
      · simp only [Functor.mapGroupObject_obj, Functor.mapGroupObjectObj_X,
        Functor.mapGroupObjectObj_one, PreservesTerminal.iso_inv, Category.assoc,
        IsIso.inv_comp_eq]
        erw [Category.comp_id]
        have : X.one = 𝟙 _ ≫ X.one := by simp only [Category.id_comp]
        change X.one = _ ≫ X.one ; rw [this]; congr 1
        exact Subsingleton.elim _ _
      · simp only [Functor.mapGroupObject_obj, Functor.mapGroupObjectObj_X,
        Functor.mapGroupObjectObj_mul, PreservesLimitPair.iso_inv, Category.assoc,
        IsIso.inv_comp_eq]
        erw [Category.comp_id]; rw [← Category.assoc]
        have : X.mul = 𝟙 _ ≫ X.mul := by simp only [Category.id_comp]
        change X.mul = _ ≫ X.mul;
        rw [this]; congr 1; erw [← prodComparison_natural]; rw [Limits.prod.map_id_id]
        erw [Category.id_comp]
        ext
        · erw [prodComparison_fst]; rw [Category.id_comp]; rfl
        · erw [prodComparison_snd]; rw [Category.id_comp]; rfl
      · simp only [Functor.mapGroupObject_obj, Functor.mapGroupObjectObj_X,
        Functor.mapGroupObjectObj_inv]
        erw [Category.comp_id, Category.id_comp]
        rfl
    · intro X Y f
      ext
      simp only [Functor.mapGroupObject_obj, Functor.mapGroupObjectObj_X,
        Functor.mapGroupObject_map, GroupObject.comp_hom', Functor.mapGroupObjectMap_hom,
        Cat.id_map]
      erw [Category.comp_id, Category.id_comp]; rfl

@[simp]
def opLaxFunctor_mapComp {C D E : {C : Cat.{v, u} // HasFiniteProducts C}} (F : C ⟶ D)
    (G : D ⟶ E) : oplaxFunctor_map (F ≫ G) ⟶ oplaxFunctor_map F ≫ oplaxFunctor_map G := by
    have := C.2; have := D.2; have := E.2
    refine {app := ?_, naturality := ?_}
    · intro X
      refine {hom := 𝟙 _, one_hom := ?_, mul_hom := ?_, inv_hom := ?_}
      · simp only [oplaxFunctor_map, Cat.comp_obj, Functor.mapGroupObject_obj,
        Functor.mapGroupObjectObj_X, Functor.mapGroupObjectObj_one, PreservesTerminal.iso_inv,
        Category.comp_id, Functor.map_comp, Functor.map_inv]
        rw [← Category.assoc]; congr 1
        simp only [IsIso.eq_comp_inv, IsIso.inv_comp_eq]
        exact Subsingleton.elim _ _
      · simp only [oplaxFunctor_map, Functor.mapGroupObject_obj, Functor.mapGroupObjectObj_X,
        Cat.comp_obj, Functor.mapGroupObjectObj_mul, PreservesLimitPair.iso_inv, Category.comp_id,
        prod.map_id_id, Functor.map_comp, Functor.map_inv, Category.id_comp]
        rw [← Category.assoc]; congr 1
        simp only [IsIso.eq_comp_inv, IsIso.inv_comp_eq]
        ext
        · rw [prodComparison_fst, Category.assoc]; erw [prodComparison_fst]
          rw [← Functor.map_comp, prodComparison_fst]
          rfl
        · rw [prodComparison_snd, Category.assoc]; erw [prodComparison_snd]
          rw [← Functor.map_comp, prodComparison_snd]
          rfl
      · simp only [id_eq, Functor.mapGroupObject_obj, Functor.mapGroupObjectObj_X, Cat.comp_obj,
        Functor.mapGroupObjectObj_inv, Category.comp_id, Category.id_comp]
        rfl
    · intro X Y f
      simp only [oplaxFunctor_map, Functor.mapGroupObject_obj, Cat.comp_obj,
        Functor.mapGroupObject_map, Functor.mapGroupObjectObj_X, Cat.comp_map]
      simp only [Functor.mapGroupObjectMap, oplaxFunctor_map, Functor.mapGroupObject_obj,
        Cat.comp_obj, Functor.mapGroupObjectObj_X]
      change GroupObject.comp _ _ = GroupObject.comp _ _
      ext
      simp only [Functor.mapGroupObjectObj_X, oplaxFunctor_map, Functor.mapGroupObject_obj,
        Cat.comp_obj, GroupObject.comp_hom, Category.comp_id, Category.id_comp]
      rfl

@[simp]
def oplaxFunctor_map₂ {C D : {C : Cat.{v, u} // HasFiniteProducts C}} {F G : C ⟶ D}
    (α : F ⟶ G) : oplaxFunctor_map F ⟶ oplaxFunctor_map G :=
  @Functor.mapGroupObject_natTrans C.1 _ D.1 _ C.2 D.2 F.1 G.1 (Classical.choice F.2)
      (Classical.choice G.2) α

lemma opLaxFunctor_mapComp_naturality_left {C D E : {C : Cat.{v, u} // HasFiniteProducts C}}
    {F F' : C ⟶ D} (α : F ⟶ F') (G : D ⟶ E) :
    oplaxFunctor_map₂ (Bicategory.whiskerRight α G) ≫ opLaxFunctor_mapComp F' G =
    opLaxFunctor_mapComp F G ≫ Bicategory.whiskerRight (oplaxFunctor_map₂ α)
    (oplaxFunctor_map G) := by
  have := E.2
  simp only [oplaxFunctor_map, oplaxFunctor_map₂, opLaxFunctor_mapComp, Functor.mapGroupObject_obj,
    Cat.comp_obj, Functor.mapGroupObjectObj_X]
  simp only [Functor.mapGroupObject, Functor.mapGroupObject_natTrans, id_eq, oplaxFunctor_map,
    Cat.comp_obj]
  change _ = _ ≫ CategoryTheory.whiskerRight _ _
  ext
  simp only [Functor.mapGroupObjectObj_X, Cat.comp_obj, oplaxFunctor_map,
    Functor.mapGroupObject_obj, NatTrans.comp_app, Functor.comp_obj, whiskerRight_app,
    GroupObject.comp_hom', Functor.mapGroupObjectMap_hom, Category.id_comp]
  erw [NatTrans.comp_app]; simp only [Cat.comp_obj, oplaxFunctor_map, Functor.mapGroupObject_obj,
    GroupObject.comp_hom', Functor.mapGroupObjectObj_X, Category.comp_id]
  erw [whiskerRight_app]

lemma opLaxFunctor_mapComp_naturality_right {C D E : {C : Cat.{v, u} // HasFiniteProducts C}}
    (F : C ⟶ D) {G G' : D ⟶ E} (α : G ⟶ G') :
    oplaxFunctor_map₂ (Bicategory.whiskerLeft F α) ≫ opLaxFunctor_mapComp F G' =
    opLaxFunctor_mapComp F G ≫ Bicategory.whiskerLeft (oplaxFunctor_map F) (oplaxFunctor_map₂ α)
    := by
  have := E.2
  simp only [oplaxFunctor_map, oplaxFunctor_map₂, opLaxFunctor_mapComp, Functor.mapGroupObject_obj,
    Cat.comp_obj, Functor.mapGroupObjectObj_X]
  simp only [Functor.mapGroupObject, Functor.mapGroupObject_natTrans, id_eq, oplaxFunctor_map,
    Cat.comp_obj]
  change _ = _ ≫ CategoryTheory.whiskerLeft _ _
  ext
  simp only [Functor.mapGroupObjectObj_X, Cat.comp_obj, oplaxFunctor_map,
    Functor.mapGroupObject_obj, NatTrans.comp_app, Functor.comp_obj, whiskerLeft_app,
    GroupObject.comp_hom', Category.id_comp]
  erw [NatTrans.comp_app]; simp only [Cat.comp_obj, oplaxFunctor_map, Functor.mapGroupObject_obj,
    GroupObject.comp_hom', Functor.mapGroupObjectObj_X, Category.comp_id]
  erw [whiskerLeft_app]

lemma oplaxFunctor_map₂_id {C D : {C : Cat.{v, u} // HasFiniteProducts C}} (F : C ⟶ D) :
    oplaxFunctor_map₂ (𝟙 F) = 𝟙 (oplaxFunctor_map F) := by
    simp only [oplaxFunctor_map, Functor.mapGroupObject, oplaxFunctor_map₂,
      Functor.mapGroupObject_natTrans, id_eq]
    change _ = NatTrans.id _
    ext
    simp only [Functor.mapGroupObject_obj, Functor.mapGroupObjectObj_X, NatTrans.id_app',
      GroupObject.id_hom']
    rfl

lemma oplaxFunctor_map₂_comp {C D : {C : Cat.{v, u} // HasFiniteProducts C}} {F G H : C ⟶ D}
    (α : F ⟶ G) (β : G ⟶ H) :
    oplaxFunctor_map₂ (α ≫ β) = oplaxFunctor_map₂ α ≫ oplaxFunctor_map₂ β := by
  have := D.2
  simp only [oplaxFunctor_map, oplaxFunctor_map₂, Functor.mapGroupObject_natTrans,
    Functor.mapGroupObject_obj, id_eq]
  change _ = (_ : NatTrans _ _)
  ext
  simp only [Functor.mapGroupObject_obj, Functor.mapGroupObjectObj_X]
  erw [NatTrans.comp_app, NatTrans.comp_app]; simp only [Functor.mapGroupObject_obj,
    GroupObject.comp_hom', Functor.mapGroupObjectObj_X]

lemma oplaxFunctor_map₂_associator {A B C D : {C : Cat.{v, u} // HasFiniteProducts C}}
    (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
    oplaxFunctor_map₂ (Bicategory.associator F G H).hom ≫ (opLaxFunctor_mapComp F (G ≫ H) ≫
    Bicategory.whiskerLeft (oplaxFunctor_map F) (opLaxFunctor_mapComp G H)) =
    opLaxFunctor_mapComp (F ≫ G) H ≫ (Bicategory.whiskerRight (opLaxFunctor_mapComp F G)
    (oplaxFunctor_map H) ≫ (Bicategory.associator (oplaxFunctor_map F) (oplaxFunctor_map G)
    (oplaxFunctor_map H)).hom) := by
  simp only [oplaxFunctor_map, oplaxFunctor_map₂, opLaxFunctor_mapComp,
    Functor.mapGroupObject_obj, Cat.comp_obj, Functor.mapGroupObjectObj_X,
    Strict.associator_eqToIso, eqToIso_refl, Iso.refl_hom, Category.comp_id]
  simp only [Functor.mapGroupObject, Functor.mapGroupObject_natTrans, id_eq, oplaxFunctor_map,
    Cat.comp_obj]
  change (_ : NatTrans _ _) = _
  ext
  simp only [Cat.comp_obj, oplaxFunctor_map, Functor.mapGroupObject_obj]
  erw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app]
  simp only [Cat.comp_obj, oplaxFunctor_map, Functor.mapGroupObject_obj]
  erw [whiskerRight_app, whiskerLeft_app]
  simp only [oplaxFunctor_map, Functor.mapGroupObject_obj, Cat.comp_obj,
    Functor.mapGroupObjectObj_X]
  have := D.2
  change GroupObject.comp _ (GroupObject.comp _ _) = GroupObject.comp _ _
  ext
  simp only [Functor.mapGroupObjectObj_X, oplaxFunctor_map, Functor.mapGroupObject_obj,
    Cat.comp_obj, GroupObject.comp_hom, Category.comp_id, Functor.mapGroupObjectMap_hom,
    Functor.map_id]
  erw [Functor.associator_hom_app]
  rfl

lemma oplaxFunctor_map₂_leftUnitor {C D : {C : Cat.{v, u} // HasFiniteProducts C}} (F : C ⟶ D) :
    oplaxFunctor_map₂ (Bicategory.leftUnitor F).hom = opLaxFunctor_mapComp (𝟙 C) F ≫
    (Bicategory.whiskerRight (opLaxFunctor_mapId C) (oplaxFunctor_map F) ≫
    (Bicategory.leftUnitor (oplaxFunctor_map F)).hom) := by
  simp only [oplaxFunctor_map, oplaxFunctor_map₂, opLaxFunctor_mapComp, Functor.mapGroupObject_obj,
    Cat.comp_obj, Functor.mapGroupObjectObj_X, opLaxFunctor_mapId, Strict.leftUnitor_eqToIso,
    eqToIso_refl, Iso.refl_hom, Category.comp_id]
  simp only [Functor.mapGroupObject, Functor.mapGroupObject_natTrans, id_eq, oplaxFunctor_map,
    Cat.comp_obj]
  change (_ : NatTrans _ _) = _
  ext
  simp only [Functor.mapGroupObject_obj, oplaxFunctor_map, Cat.comp_obj]
  erw [NatTrans.comp_app]; simp only [Functor.mapGroupObject_obj, Cat.comp_obj, oplaxFunctor_map]
  erw [whiskerRight_app]; simp only [oplaxFunctor_map, Functor.mapGroupObject_obj, Cat.comp_obj]
  simp only [oplaxFunctor_map, Functor.mapGroupObject_obj, Cat.comp_obj, Functor.mapGroupObjectMap,
    Functor.mapGroupObjectObj_X]
  have := D.2
  change _ = GroupObject.comp _ _
  ext
  simp only [Functor.mapGroupObjectObj_X, oplaxFunctor_map, Functor.mapGroupObject_obj,
    Cat.comp_obj, GroupObject.comp_hom, Category.id_comp]
  erw [Functor.leftUnitor_hom_app, Functor.map_id]
  rfl

lemma oplaxFunctor_map₂_rightUnitor {C D : {C : Cat.{v, u} // HasFiniteProducts C}} (F : C ⟶ D) :
    oplaxFunctor_map₂ (Bicategory.rightUnitor F).hom = opLaxFunctor_mapComp F (𝟙 D) ≫
    (Bicategory.whiskerLeft (oplaxFunctor_map F) (opLaxFunctor_mapId D) ≫
    (Bicategory.rightUnitor (oplaxFunctor_map F)).hom) := by
  simp only [oplaxFunctor_map, Functor.mapGroupObject, oplaxFunctor_map₂,
    Functor.mapGroupObject_natTrans, id_eq, opLaxFunctor_mapComp, Cat.comp_obj,
    Functor.mapGroupObjectObj_X, opLaxFunctor_mapId, Strict.rightUnitor_eqToIso, eqToIso_refl,
    Iso.refl_hom, Category.comp_id]
  change (_ : NatTrans _ _) = _
  ext
  simp only [Functor.mapGroupObject_obj, oplaxFunctor_map, Cat.comp_obj]
  erw [NatTrans.comp_app]; simp only [Functor.mapGroupObject_obj, Cat.comp_obj, oplaxFunctor_map]
  erw [whiskerLeft_app]; simp only [oplaxFunctor_map, Functor.mapGroupObject_obj, Cat.comp_obj,
    Functor.mapGroupObjectObj_X]
  have := D.2
  change _ = GroupObject.comp _ _
  ext
  simp only [Functor.mapGroupObjectObj_X, oplaxFunctor_map, Functor.mapGroupObject_obj,
    Cat.comp_obj, GroupObject.comp_hom, Category.id_comp]
  erw [Functor.rightUnitor_hom_app]

@[simp]
def oplaxFunctor : OplaxFunctor {C : Cat.{v, u} // HasFiniteProducts C} Cat.{v, max v u} where
  obj C := Cat.of (@GroupObject C.1 _ C.2)
  map := oplaxFunctor_map
  map₂ := oplaxFunctor_map₂
  mapId := opLaxFunctor_mapId
  mapComp := opLaxFunctor_mapComp
  mapComp_naturality_left := opLaxFunctor_mapComp_naturality_left
  mapComp_naturality_right := opLaxFunctor_mapComp_naturality_right
  map₂_id := oplaxFunctor_map₂_id
  map₂_comp := oplaxFunctor_map₂_comp
  map₂_associator := oplaxFunctor_map₂_associator
  map₂_leftUnitor := oplaxFunctor_map₂_leftUnitor
  map₂_rightUnitor := oplaxFunctor_map₂_rightUnitor

def oplaxFunctor_pseudoCore_mapIdIso (C : {C : Cat.{v, u} // HasFiniteProducts C}) :
    oplaxFunctor_map (𝟙 C) ≅ 𝟙 (oplaxFunctor.obj C) := by
  have := C.2
  simp only [oplaxFunctor, oplaxFunctor_map, Functor.mapGroupObject]
  refine NatIso.ofComponents ?_ ?_
  · intro X
    refine GroupObject.isoOfIso (Iso.refl _) ?_ ?_ ?_
    · simp only [Functor.mapGroupObjectObj_X, Functor.mapGroupObjectObj_one,
      PreservesTerminal.iso_inv, Iso.refl_hom, Category.comp_id, IsIso.inv_comp_eq]
      change X.one = _ ≫ X.one
      rw [Subsingleton.elim (terminalComparison (𝟙 C : C ⟶ C).1) (𝟙 _)]
      erw [Category.id_comp]
    · simp only [Functor.mapGroupObjectObj_X, Functor.mapGroupObjectObj_mul,
      PreservesLimitPair.iso_inv, Iso.refl_hom, Category.comp_id, prod.map_id_id,
      Category.id_comp, IsIso.inv_comp_eq]
      change X.mul = _ ≫ X.mul
      suffices h : prodComparison (𝟙 C : C ⟶ C).1 X.X X.X = 𝟙 _ by
        rw [h]; erw [Category.id_comp]
      ext
      · simp only [prodComparison_fst, Category.id_comp]; rfl
      · simp only [prodComparison_snd, Category.id_comp]; rfl
    · simp only [Functor.mapGroupObjectObj_X, Functor.mapGroupObjectObj_inv, Iso.refl_hom,
      Category.comp_id, Category.id_comp]; rfl
  · intro X Y f
    simp only [Functor.mapGroupObjectMap, Functor.mapGroupObjectObj_X, Cat.id_map]
    simp only [GroupObject.isoOfIso, Functor.mapGroupObjectObj_X, Iso.refl_hom, Iso.refl_inv]
    change GroupObject.comp _ _ = GroupObject.comp _ _
    ext
    simp only [Functor.mapGroupObjectObj_X, GroupObject.comp_hom, Category.comp_id,
    Category.id_comp]
    rfl

def oplaxFunctor_pseudoCore_mapCompIso {C D E : {C : Cat.{v, u} // HasFiniteProducts C}}
    (F : C ⟶ D) (G : D ⟶ E) :
    oplaxFunctor_map (F ≫ G) ≅ oplaxFunctor_map F ≫ oplaxFunctor_map G := by
  have := E.2
  refine NatIso.ofComponents ?_ ?_
  · intro X
    refine GroupObject.isoOfIso (Iso.refl _) ?_ ?_ ?_
    · simp only [oplaxFunctor_map, Cat.comp_obj, Functor.mapGroupObject_obj,
      Functor.mapGroupObjectObj, PreservesTerminal.iso_inv, Iso.refl_hom, Category.comp_id,
      Functor.map_comp, Functor.map_inv]
      rw [← Category.assoc]; congr 1
      simp only [IsIso.eq_comp_inv, IsIso.inv_comp_eq]
      exact Subsingleton.elim _ _
    · simp only [oplaxFunctor_map, Functor.mapGroupObject_obj, Functor.mapGroupObjectObj,
      Cat.comp_obj, PreservesLimitPair.iso_inv, Iso.refl_hom, Category.comp_id, prod.map_id_id,
      Functor.map_comp, Functor.map_inv, Category.id_comp]
      rw [← Category.assoc]; congr 1
      simp only [IsIso.eq_comp_inv, IsIso.inv_comp_eq]
      ext
      · simp only [Category.assoc, prodComparison_fst]
        erw [prodComparison_fst]; rw [← Functor.map_comp, prodComparison_fst]
        rfl
      · simp only [Category.assoc, prodComparison_snd]
        erw [prodComparison_snd]; rw [← Functor.map_comp, prodComparison_snd]
        rfl
    · simp only [oplaxFunctor_map, Functor.mapGroupObject_obj, Functor.mapGroupObjectObj,
      Cat.comp_obj, Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
  · intro X Y f
    simp only [oplaxFunctor_map, Functor.mapGroupObject_obj, Cat.comp_obj,
      Functor.mapGroupObject_map, GroupObject.isoOfIso, Functor.mapGroupObjectObj_X, Iso.refl_hom,
      Iso.refl_inv, Cat.comp_map]
    simp only [Functor.mapGroupObjectMap, oplaxFunctor_map, Functor.mapGroupObject_obj,
      Cat.comp_obj, Functor.mapGroupObjectObj_X]
    change GroupObject.comp _ _ = GroupObject.comp _ _
    ext
    simp only [Functor.mapGroupObjectObj_X, oplaxFunctor_map, Functor.mapGroupObject_obj,
      Cat.comp_obj, GroupObject.comp_hom, Category.comp_id, Category.id_comp]
    rfl

def oplaxFunctor_pseudoCore : OplaxFunctor.PseudoCore oplaxFunctor where
  mapIdIso := oplaxFunctor_pseudoCore_mapIdIso
  mapCompIso := oplaxFunctor_pseudoCore_mapCompIso

def pseudofunctor : Pseudofunctor {C : Cat.{v, u} // HasFiniteProducts C} Cat.{v, max v u} :=
  Pseudofunctor.mkOfOplax oplaxFunctor oplaxFunctor_pseudoCore

end CategoryTheory.GroupObject
