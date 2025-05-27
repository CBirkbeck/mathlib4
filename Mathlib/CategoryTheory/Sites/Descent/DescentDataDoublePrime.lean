/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import Mathlib.CategoryTheory.Sites.Descent.DescentDataAsCoalgebra
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj

/-!
# Descent data ...

-/

namespace CategoryTheory

open Opposite Limits Bicategory

namespace Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type*} [Category C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) (Adj Cat))

instance {X Y : C} (f : X ⟶ Y) [IsIso f] (F : Pseudofunctor (LocallyDiscrete C) (Adj Cat)) :
    (F.map (.toLoc f)).l.IsEquivalence := by
  change ((F.comp Adj.forget₁).map f.toLoc).IsEquivalence
  infer_instance

instance (X : LocallyDiscrete C)  (F : Pseudofunctor (LocallyDiscrete C) (Adj Cat)) :
    (F.map (𝟙 X)).l.IsEquivalence := by
  obtain ⟨X⟩ := X
  change (F.map (𝟙 X).toLoc).l.IsEquivalence
  infer_instance

-- TODO: add `Pseudofunctor.comp_mapComp'`
lemma mapComp'_comp_forget₁_hom {C : Type*} [Bicategory C] [Strict C]
    (F : Pseudofunctor C (Adj Cat))
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : f ≫ g = fg) :
    ((F.comp Adj.forget₁).mapComp' f g fg hfg).hom =
      (F.mapComp' f g fg hfg).hom.τl := by
  simp [Adj.comp_forget₁_mapComp']

lemma mapComp'_comp_forget₁_inv {C : Type*} [Bicategory C] [Strict C]
    (F : Pseudofunctor C (Adj Cat))
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : f ≫ g = fg) :
    ((F.comp Adj.forget₁).mapComp' f g fg hfg).inv =
      (F.mapComp' f g fg hfg).inv.τl := by
  simp [Adj.comp_forget₁_mapComp']

section

variable {C B : Type*} [Bicategory C] [Strict C] [Bicategory B]
    (F : Pseudofunctor C (Adj B))

end

variable {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))

namespace DescentData''

variable {F sq}
section

variable {obj : ∀ (i : ι), (F.obj (.mk (op (X i)))).obj}
  (hom : ∀ (i₁ i₂ : ι), obj i₁ ⟶ (F.map (sq i₁ i₂).p₁.op.toLoc).r.obj
    ((F.map (sq i₁ i₂).p₂.op.toLoc).l.obj (obj i₂)))

def homComp (i₁ i₂ i₃ : ι) : obj i₁ ⟶ (F.map (sq₃ i₁ i₂ i₃).p₁.op.toLoc).r.obj
      ((F.map (sq₃ i₁ i₂ i₃).p₃.op.toLoc).l.obj (obj i₃)) :=
  hom i₁ i₂ ≫ (F.map (sq i₁ i₂).p₁.op.toLoc).r.map
      ((F.map (sq i₁ i₂).p₂.op.toLoc).l.map (hom i₂ i₃)) ≫
        (F.map (sq i₁ i₂).p₁.op.toLoc).r.map
          ((F.baseChange (sq₃ i₁ i₂ i₃).isPullback₂.toCommSq.flip.op.toLoc).app _) ≫
    (Adj.rIso (F.mapComp' (sq i₁ i₂).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc
          (sq₃ i₁ i₂ i₃).p₁.op.toLoc (by aesoptoloc))).inv.app _ ≫
    (F.map (sq₃ i₁ i₂ i₃).p₁.op.toLoc).r.map
      ((Adj.lIso (F.mapComp' (sq i₂ i₃).p₂.op.toLoc (sq₃ i₁ i₂ i₃).p₂₃.op.toLoc
          (sq₃ i₁ i₂ i₃).p₃.op.toLoc (by aesoptoloc))).inv.app _)

end

section

variable {X₁₂ X₁ X₂ : C}
  {obj₁ : (F.obj (.mk (op X₁))).obj} {obj₂ : (F.obj (.mk (op X₂))).obj}
  {p₁ : X₁₂ ⟶ X₁} {p₂ : X₁₂ ⟶ X₂}
  (hom : obj₁ ⟶ (F.map p₁.op.toLoc).r.obj ((F.map p₂.op.toLoc).l.obj obj₂))

def pullHom'' ⦃Y₁₂ : C⦄ (p₁₂ : Y₁₂ ⟶ X₁₂) (q₁ : Y₁₂ ⟶ X₁) (q₂ : Y₁₂ ⟶ X₂)
    (hq₁ : p₁₂ ≫ p₁ = q₁ := by aesop_cat) (hq₂ : p₁₂ ≫ p₂ = q₂ := by aesop_cat) :
    obj₁ ⟶ (F.map q₁.op.toLoc).r.obj ((F.map q₂.op.toLoc).l.obj obj₂) :=
  hom ≫ (F.map p₁.op.toLoc).r.map ((F.map p₁₂.op.toLoc).adj.unit.app _) ≫
    (Adj.rIso (F.mapComp' p₁.op.toLoc p₁₂.op.toLoc q₁.op.toLoc (by aesoptoloc))).inv.app _ ≫
      (F.map q₁.op.toLoc).r.map
    ((Adj.lIso (F.mapComp' p₂.op.toLoc p₁₂.op.toLoc q₂.op.toLoc (by aesoptoloc))).inv.app _)

end

@[reassoc]
lemma mapComp'_τl_τr_compatibility
    ⦃X Y Z : C⦄ (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : f ≫ g = fg)
    (obj : (F.obj (.mk (op Y))).obj) :
    (F.map fg.op.toLoc).l.map
      ((F.map g.op.toLoc).r.map ((F.map f.op.toLoc).adj.unit.app obj)) ≫
      (F.map fg.op.toLoc).l.map
        ((F.mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by aesoptoloc)).hom.τr.app
          (((F.map f.op.toLoc).l.obj obj))) ≫
      (F.map fg.op.toLoc).adj.counit.app ((F.map f.op.toLoc).l.obj obj) =
    (F.mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by aesoptoloc)).hom.τl.app _ ≫
      (F.map f.op.toLoc).l.map ((F.map g.op.toLoc).adj.counit.app obj) := by
  simpa [Cat.associator_hom_app, Cat.associator_inv_app, Cat.rightUnitor_inv_app,
    Cat.leftUnitor_hom_app] using
    NatTrans.congr_app
      (Adj.unit_comp_mapComp'_hom_τr_comp_counit F g.op.toLoc f.op.toLoc fg.op.toLoc
        (by aesoptoloc)) obj

lemma homEquiv_symm_pullHom'' ⦃X₁ X₂ : C⦄
    ⦃obj₁ : (F.obj (.mk (op X₁))).obj⦄ ⦃obj₂ : (F.obj (.mk (op X₂))).obj⦄
    ⦃X₁₂ : C⦄ ⦃p₁ : X₁₂ ⟶ X₁⦄ ⦃p₂ : X₁₂ ⟶ X₂⦄
    (hom : obj₁ ⟶ (F.map p₁.op.toLoc).r.obj ((F.map p₂.op.toLoc).l.obj obj₂))
    ⦃Y₁₂ : C⦄ (g : Y₁₂ ⟶ X₁₂) (gp₁ : Y₁₂ ⟶ X₁) (gp₂ : Y₁₂ ⟶ X₂)
    (hgp₁ : g ≫ p₁ = gp₁) (hgp₂ : g ≫ p₂ = gp₂) :
    ((F.map gp₁.op.toLoc).adj.toCategory.homEquiv _ _ ).symm (pullHom'' hom g gp₁ gp₂ hgp₁ hgp₂) =
      pullHom (F := F.comp Adj.forget₁)
        ((((F.map p₁.op.toLoc).adj.toCategory).homEquiv _ _ ).symm hom) g gp₁ gp₂ hgp₁ hgp₂ := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  dsimp [pullHom'', pullHom]
  simp only [Functor.map_comp, Category.assoc, Adj.comp_forget₁_mapComp', Adj.lIso_hom,
    Adj.lIso_inv]
  erw [← NatTrans.naturality_assoc]
  dsimp
  congr 1
  have := (F.map gp₁.op.toLoc).adj.toCategory.counit.naturality
    ((F.mapComp' p₂.op.toLoc g.op.toLoc gp₂.op.toLoc (by aesoptoloc)).inv.τl.app obj₂)
  dsimp at this
  rw [this, mapComp'_τl_τr_compatibility_assoc _ _ _ hgp₁]

section

variable
    ⦃X₁₂ X X S : C⦄ ⦃p₁ : X₁₂ ⟶ X⦄ ⦃p₂ : X₁₂ ⟶ X⦄ ⦃f : X ⟶ S⦄
    (sq : CommSq p₁ p₂ f f) (obj : (F.obj (.mk (op X))).obj)

@[reassoc]
lemma map_baseChange_comp_counit (g : X ⟶ X₁₂) (hg₁ : g ≫ p₁ = 𝟙 X) (hg₂ : g ≫ p₂ = 𝟙 X) :
    (F.map g.op.toLoc).l.map
      ((F.map p₁.op.toLoc).l.map ((F.baseChange sq.flip.op.toLoc).app obj)) ≫
    (F.map g.op.toLoc).l.map
       ((F.map p₁.op.toLoc).adj.counit.app _) =
    (F.mapComp' p₁.op.toLoc g.op.toLoc (𝟙 _) (by aesoptoloc)).inv.τl.app
      ((F.map f.op.toLoc).l.obj ((F.map f.op.toLoc).r.obj obj)) ≫
      (F.map (𝟙 _)).l.map ((F.map f.op.toLoc).adj.counit.app _) ≫
      (F.mapComp' p₂.op.toLoc g.op.toLoc (𝟙 _) (by aesoptoloc)).hom.τl.app obj := by
  have := NatTrans.congr_app
    (F.whiskerRight_whiskerBaseChange_self_self _ _ _ sq.flip.op.toLoc g.op.toLoc (by aesoptoloc)
      (by aesoptoloc)) obj
  simp [Cat.associator_inv_app, Cat.associator_hom_app, Cat.leftUnitor_hom_app,
    Adj.comp_forget₁_mapComp', whiskerBaseChange_eq',
    Adjunction.homEquiv₂_symm_apply] at this
  rw [this]
  erw [← NatTrans.naturality_assoc]
  rfl

end


end DescentData''

open DescentData'' in
structure DescentData'' where
  obj (i : ι) : (F.obj (.mk (op (X i)))).obj
  hom (i₁ i₂ : ι) : obj i₁ ⟶
    (F.map (sq i₁ i₂).p₁.op.toLoc).r.obj
      ((F.map (sq i₁ i₂).p₂.op.toLoc).l.obj (obj i₂))
  hom_self (i : ι) (δ : (sq i i).Diagonal) :
    pullHom'' (hom i i) δ.f (𝟙 _) (𝟙 _) = (F.map (𝟙 (.mk (op (X i))))).adj.unit.app _
  hom_comp (i₁ i₂ i₃ : ι) :
    homComp sq₃ hom i₁ i₂ i₃ = pullHom'' (hom i₁ i₃) (sq₃ i₁ i₂ i₃).p₁₃ _ _

namespace DescentData''

variable {F} {sq} {obj : ∀ (i : ι), (F.obj (.mk (op (X i)))).obj}
  (hom : ∀ i₁ i₂, obj i₁ ⟶ (F.map (sq i₁ i₂).p₁.op.toLoc).r.obj
    ((F.map (sq i₁ i₂).p₂.op.toLoc).l.obj (obj i₂)))

section

def dataEquivDescentData' :
    (∀ i₁ i₂, obj i₁ ⟶ (F.map (sq i₁ i₂).p₁.op.toLoc).r.obj
      ((F.map (sq i₁ i₂).p₂.op.toLoc).l.obj (obj i₂))) ≃
    (∀ i₁ i₂, (F.map (sq i₁ i₂).p₁.op.toLoc).l.obj (obj i₁) ⟶
      (F.map (sq i₁ i₂).p₂.op.toLoc).l.obj (obj i₂)) :=
  Equiv.piCongrRight (fun i₁ ↦ Equiv.piCongrRight (fun i₂ ↦
    (((F.map (sq i₁ i₂).p₁.op.toLoc).adj.toCategory).homEquiv _ _).symm))

lemma hom_self_iff_dataEquivDescentData' ⦃i : ι⦄ (δ : (sq i i).Diagonal) :
    pullHom'' (hom i i) δ.f (𝟙 _) (𝟙 _) = (F.map (𝟙 (.mk (op (X i))))).adj.unit.app _ ↔
    DescentData'.pullHom' (F := F.comp Adj.forget₁)
        (dataEquivDescentData' hom) (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _ := by
  trans ((F.map (𝟙 (.mk (op (X i))))).adj.toCategory.homEquiv _ _).symm
    (pullHom'' (hom i i) δ.f (𝟙 (X i)) (𝟙 (X i))) = 𝟙 _
  · dsimp
    rw [← Adjunction.toCategory_unit, ← Adjunction.homEquiv_id,
      Equiv.apply_eq_iff_eq_symm_apply, Equiv.symm_symm]
  · convert Iff.rfl using 2
    have := homEquiv_symm_pullHom'' (hom _ _) δ.f (𝟙 _) (𝟙 _) (by simp) (by simp)
    dsimp at this ⊢
    rw [this]
    apply DescentData'.pullHom'_eq_pullHom <;> simp

lemma homEquiv_symm_pullHom''_eq_pullHom'_dataEquivDescentData' (i₁ i₂ i₃ : ι) :
    (((F.map (sq₃ i₁ i₂ i₃).p₁.op.toLoc).adj.toCategory).homEquiv _ _).symm
      (pullHom'' (hom i₁ i₃) (sq₃ i₁ i₂ i₃).p₁₃ _ _) =
        DescentData'.pullHom' (F := F.comp Adj.forget₁)
          (dataEquivDescentData' hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ := by
  rw [homEquiv_symm_pullHom'', dataEquivDescentData']
  simp only [comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
    PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, Adj.forget₁_obj,
    Prefunctor.comp_map, Adj.forget₁_map]
  rw [DescentData'.pullHom'_eq_pullHom _ (sq₃ i₁ i₂ i₃).p _ _ _ _ (sq₃ i₁ i₂ i₃).p₁₃]
  · rfl
  · simp
  · simp

variable (i₁ i₂ i₃ : ι)

@[reassoc]
lemma map_p₁₂_baseChange_comp_counit (i₁ i₂ i₃ : ι) (M) :
    (F.map (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc).l.map
      ((F.baseChange (sq₃ i₁ i₂ i₃).isPullback₂.toCommSq.flip.op.toLoc).app M) ≫
      (F.map (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc).adj.counit.app _ =
    (F.mapComp' (sq i₁ i₂).p₂.op.toLoc (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc
        (sq₃ i₁ i₂ i₃).p₂.op.toLoc (by aesoptoloc)).inv.τl.app _ ≫
      (F.mapComp' (sq i₂ i₃).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₂₃.op.toLoc
        (sq₃ i₁ i₂ i₃).p₂.op.toLoc (by aesoptoloc)).hom.τl.app _ ≫
      (F.map (sq₃ i₁ i₂ i₃).p₂₃.op.toLoc).l.map
        ((F.map (sq i₂ i₃).p₁.op.toLoc).adj.counit.app _) ≫
        (by dsimp; exact eqToHom rfl) := by
  have h1 := congr($(F.whiskerBaseChange_eq_whiskerRight_baseChange
    (sq₃ i₁ i₂ i₃).isPullback₂.toCommSq.flip.op.toLoc).app M)
  have h2 := congr($(F.whiskerBaseChange_eq_whiskerLeft_isoMapOfCommSq
    (sq₃ i₁ i₂ i₃).isPullback₂.toCommSq.flip.op.toLoc).app M)
  dsimp at h1 h2
  rw [h2] at h1
  simp [Cat.associator_hom_app, Cat.associator_inv_app, Cat.rightUnitor_inv_app,
    Cat.leftUnitor_hom_app, Cat.rightUnitor_hom_app] at h1
  rw [← h1]
  simp only [Cat.comp_obj, Cat.id_obj, Adj.comp_l, eqToHom_refl, id_eq, Category.comp_id]
  rw [F.isoMapOfCommSq_eq _ (sq₃ i₁ i₂ i₃).p₂.op.toLoc (by aesoptoloc)]
  simp

-- TODO: fix the name, this has nothing to do with `baseChange`, could maybe even be inlined by
-- adding some more lemmas
@[reassoc]
lemma baseChange_eq'' (i₁ i₂ i₃ : ι) (M)
    (f : (F.map (sq i₁ i₂).p₂.op.toLoc).l.obj ((F.map (sq i₂ i₃).p₁.op.toLoc).r.obj M) ⟶
      (F.map (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc).r.obj ((F.map (sq₃ i₁ i₂ i₃).p₂₃.op.toLoc).l.obj M)) :
    (F.map (sq₃ i₁ i₂ i₃).p₁.op.toLoc).l.map
    ((F.map (sq i₁ i₂).p₁.op.toLoc).r.map f) ≫
      (F.map (sq₃ i₁ i₂ i₃).p₁.op.toLoc).l.map
        ((F.mapComp' _ _ (sq₃ i₁ i₂ i₃).p₁.op.toLoc (by aesoptoloc)).hom.τr.app _) ≫
      (F.map (sq₃ i₁ i₂ i₃).p₁.op.toLoc).adj.counit.app _ =
      ((F.mapComp' (sq i₁ i₂).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc
        (sq₃ i₁ i₂ i₃).p₁.op.toLoc (by aesoptoloc)).hom.τl.app _) ≫
        (F.map (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc).l.map
          ((F.map (sq i₁ i₂).p₁.op.toLoc).adj.counit.app _) ≫
    (F.map (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc).l.map f ≫
      (F.map (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc).adj.counit.app _ := by
  have := Adj.counit_map_of_comp F (sq i₁ i₂).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc
    (sq₃ i₁ i₂ i₃).p₁.op.toLoc (by aesoptoloc)
  rw [this]
  simp [Cat.associator_hom_app, Cat.associator_inv_app, Cat.rightUnitor_inv_app,
    Cat.leftUnitor_hom_app]
  congr 1
  rw [← (F.map (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc).l.map_comp_assoc]
  rw [← (F.map (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc).l.map_comp_assoc]
  rw [Category.assoc]
  rw [← (F.map (sq i₁ i₂).p₁.op.toLoc).l.map_comp]
  rw [← NatTrans.comp_app]
  rw [Adj.hom_inv_id_τr]
  simp only [Adj.comp_r, Cat.id_app, Cat.comp_obj, Functor.map_id, Category.comp_id]
  rw [← (F.map (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc).l.map_comp_assoc]
  erw [(F.map (sq i₁ i₂).p₁.op.toLoc).adj.counit.naturality]
  simp

-- TODO: clean this up, it's an `erw`-massacre
lemma homEquiv_symm_homComp (i₁ i₂ i₃ : ι) :
    (((F.map (sq₃ i₁ i₂ i₃).p₁.op.toLoc).adj.toCategory).homEquiv _ _).symm
      (homComp sq₃ hom i₁ i₂ i₃) =
        DescentData'.pullHom' (F := F.comp Adj.forget₁)
        (dataEquivDescentData' hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
      DescentData'.pullHom'
        (dataEquivDescentData' hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ := by
  rw [DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃]
  rw [DescentData'.pullHom'₂₃_eq_pullHom_of_chosenPullback₃]
  rw [dataEquivDescentData']
  dsimp only [comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
    PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, Adj.forget₁_obj,
    Prefunctor.comp_map, Adj.forget₁_map, Equiv.piCongrRight_apply, Pi.map_apply]
  simp_rw [Adjunction.homEquiv_counit]
  dsimp only [Adjunction.toCategory_counit]
  rw [homComp]
  simp only [Cat.comp_obj, Adj.comp_r, Adj.rIso_inv, Adj.comp_l, Adj.lIso_inv, Functor.map_comp,
    Category.assoc, pullHom, comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
    PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, Adj.forget₁_obj,
    Prefunctor.comp_map, Adj.forget₁_map]
  erw [(F.map (sq₃ i₁ i₂ i₃).p₁.op.toLoc).adj.counit.naturality]
  dsimp only [Cat.comp_obj, Cat.id_obj, Cat.id_map]
  rw [baseChange_eq''_assoc]
  rw [map_p₁₂_baseChange_comp_counit_assoc]
  simp only [Cat.comp_obj, Adj.comp_l, Cat.id_obj, eqToHom_refl, id_eq, Category.id_comp,
    NatTrans.naturality_assoc, Cat.comp_map]
  rw [mapComp'_comp_forget₁_hom]
  rw [mapComp'_comp_forget₁_hom]
  rw [mapComp'_comp_forget₁_inv]
  rw [mapComp'_comp_forget₁_inv]
  congr 2
  rw [← (F.map (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc).l.map_comp_assoc]
  erw [(F.map (sq i₁ i₂).p₁.op.toLoc).adj.counit.naturality]
  simp only [Cat.comp_obj, Cat.id_obj, Cat.id_map, Functor.map_comp, Category.assoc]
  erw [(F.mapComp' _ _ _ _).inv.τl.naturality_assoc]
  simp

lemma hom_comp_iff_dataEquivDescentData' (i₁ i₂ i₃ : ι) :
    homComp sq₃ hom i₁ i₂ i₃ = pullHom'' (hom i₁ i₃) (sq₃ i₁ i₂ i₃).p₁₃ _ _ ↔
      DescentData'.pullHom' (F := F.comp Adj.forget₁)
        (dataEquivDescentData' hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
      DescentData'.pullHom'
        (dataEquivDescentData' hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
      DescentData'.pullHom'
        (dataEquivDescentData' hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ := by
  rw [← homEquiv_symm_pullHom''_eq_pullHom'_dataEquivDescentData', ← homEquiv_symm_homComp]
  simp

end

section

variable [∀ i₁ i₂, IsIso (F.baseChange (sq i₁ i₂).isPullback.toCommSq.flip.op.toLoc)]
-- should require the same for `(sq₃ i₁ i₂ i₃).isPullback₂`.

noncomputable def dataEquivCoalgebra
  [∀ i₁ i₂, IsIso (F.baseChange (sq i₁ i₂).isPullback.toCommSq.flip.op.toLoc)] :
    (∀ i₁ i₂, obj i₁ ⟶ (F.map (sq i₁ i₂).p₁.op.toLoc).r.obj
      ((F.map (sq i₁ i₂).p₂.op.toLoc).l.obj (obj i₂))) ≃
    (∀ i₁ i₂, obj i₁ ⟶ (F.map (f i₁).op.toLoc).l.obj ((F.map (f i₂).op.toLoc).r.obj (obj i₂))) :=
  Equiv.piCongrRight (fun i₁ ↦ Equiv.piCongrRight (fun i₂ ↦
    Iso.homCongr (Iso.refl _)
      ((asIso (F.baseChange (sq i₁ i₂).isPullback.toCommSq.flip.op.toLoc)).symm.app _)))

lemma hom_self_iff_dataEquivCoalgebra ⦃i : ι⦄ (δ : (sq i i).Diagonal):
    pullHom'' (hom i i) δ.f (𝟙 _) (𝟙 _) = (F.map (𝟙 (.mk (op (X i))))).adj.unit.app _ ↔
    dataEquivCoalgebra hom i i ≫ (F.map (f i).op.toLoc).adj.counit.app _ = 𝟙 _ := by
  obtain ⟨hom, rfl⟩ := dataEquivCoalgebra.symm.surjective hom
  rw [Equiv.apply_symm_apply]
  dsimp [dataEquivCoalgebra]
  rw [Category.id_comp,
    ← ((F.map (𝟙 (X i)).op.toLoc).adj.toCategory.homEquiv _ _ ).symm.injective.eq_iff,
    homEquiv_symm_pullHom'']
  dsimp
  rw [← Adjunction.toCategory_unit, ← Adjunction.homEquiv_id, Equiv.symm_apply_apply]
  trans (F.map (𝟙 { as := op (X i) })).l.map
      (hom i i ≫ (F.map (f i).op.toLoc).adj.counit.app (obj i)) = 𝟙 _ ; swap
  · rw [← Functor.map_id]
    have : Functor.Faithful (F.map (𝟙 { as := op (X i) })).l := inferInstance
    rw [Functor.map_injective_iff]
  · convert Iff.rfl using 2
    dsimp [pullHom]
    simp [Adjunction.homEquiv_counit]
    erw [← NatTrans.naturality_assoc]
    congr 1
    simp [Adj.comp_forget₁_mapComp']
    rw [map_baseChange_comp_counit_assoc (sq i i).commSq (obj i) δ.f (by simp) (by simp)]
    dsimp
    rw [← Adj.lIso_hom, ← Adj.lIso_inv, Iso.hom_inv_id_app_assoc,
      ← Adj.lIso_hom, ← Adj.lIso_inv, Iso.hom_inv_id_app, Category.comp_id]

lemma hom_comp_iff_dataEquivCoalgebra (i₁ i₂ i₃ : ι) :
    homComp sq₃ hom i₁ i₂ i₃ = pullHom'' (hom i₁ i₃) (sq₃ i₁ i₂ i₃).p₁₃ _ _ ↔
    dataEquivCoalgebra hom i₁ i₂ ≫ (F.map (f i₁).op.toLoc).l.map
      ((F.map (f i₂).op.toLoc).r.map (dataEquivCoalgebra hom i₂ i₃)) =
    dataEquivCoalgebra hom i₁ i₃ ≫
      (F.map (f i₁).op.toLoc).l.map ((F.map (f i₂).op.toLoc).adj.unit.app _) := by
  sorry

end

end DescentData''

end Pseudofunctor

end CategoryTheory
