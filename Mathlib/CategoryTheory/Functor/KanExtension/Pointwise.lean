/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Pointwise Kan extensions

In this file, we define the notion of pointwise (left) Kan extension. Given two functors
`L : C ⥤ D` and `F : C ⥤ H`, and `E : LeftExtension L F`, we introduce a cocone
`E.coconeAt Y` for the functor `CostructuredArrow.proj L Y ⋙ F : CostructuredArrow L Y ⥤ H`
the point of which is `E.right.obj Y`, and the type `E.IsPointwiseLeftKanExtensionAt Y`
which expresses that `E.coconeAt Y` is colimit. When this holds for all `Y : D`,
we may say that `E` is a pointwise left Kan extension (`E.IsPointwiseLeftKanExtension`).

Conversely, when `CostructuredArrow.proj L Y ⋙ F` has a colimit, we say that
`F` has a pointwise left Kan extension at `Y : D` (`HasPointwiseLeftKanExtensionAt L F Y`),
and if this holds for all `Y : D`, we construct a functor
`pointwiseLeftKanExtension L F : D ⥤ H` and show it is a pointwise Kan extension.

## TODO

* obtain similar results for right Kan extensions
* refactor the file `CategoryTheory.Limits.KanExtension` using this new general API

## References
* https://ncatlab.org/nlab/show/Kan+extension

-/

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D D' H H' : Type*} [Category C] [Category D] [Category D']
  [Category H] (L : C ⥤ D) (L' : C ⥤ D') (F : C ⥤ H)

/-- The condition that a functor `F` has a pointwise left Kan extension along `L` at `Y`.
It means that the functor `CostructuredArrow.proj L Y ⋙ F : CostructuredArrow L Y ⥤ H`
has a colimit. -/
abbrev HasPointwiseLeftKanExtensionAt (Y : D) :=
  HasColimit (CostructuredArrow.proj L Y ⋙ F)

/-- The condition that a functor `F` has a pointwise left Kan extension along `L`: it means
that it has a pointwise left Kan extension at any object. -/
abbrev HasPointwiseLeftKanExtension := ∀ (Y : D), HasPointwiseLeftKanExtensionAt L F Y

lemma hasPointwiseLeftKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) :
    HasPointwiseLeftKanExtensionAt L F Y₁ ↔
      HasPointwiseLeftKanExtensionAt L F Y₂ := by
  revert Y₁ Y₂ e
  suffices ∀ ⦃Y₁ Y₂ : D⦄ (_ : Y₁ ≅ Y₂) [HasPointwiseLeftKanExtensionAt L F Y₁],
      HasPointwiseLeftKanExtensionAt L F Y₂ from
    fun Y₁ Y₂ e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro Y₁ Y₂ e _
  change HasColimit ((CostructuredArrow.mapIso e.symm).functor ⋙ CostructuredArrow.proj L Y₁ ⋙ F)
  infer_instance

variable {L}

lemma hasPointwiseLeftKanExtensionAt_iff_of_iso' {L' : C ⥤ D} (e : L ≅ L') (Y : D) :
    HasPointwiseLeftKanExtensionAt L F Y ↔
      HasPointwiseLeftKanExtensionAt L' F Y := by
  revert L L' e
  suffices ∀ ⦃L L' : C ⥤ D⦄ (_ : L ≅ L') [HasPointwiseLeftKanExtensionAt L F Y],
      HasPointwiseLeftKanExtensionAt L' F Y from
    fun L L' e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro L L' e _
  let Φ : CostructuredArrow L' Y ≌ CostructuredArrow L Y := Comma.mapLeftIso _ e.symm
  have : HasColimit (Φ.functor ⋙ CostructuredArrow.proj L Y ⋙ F) := inferInstance
  let e' : CostructuredArrow.proj L' Y ⋙ F ≅
    Φ.functor ⋙ CostructuredArrow.proj L Y ⋙ F := Iso.refl _
  exact hasColimitOfIso e'

variable (L)

lemma hasPointwiseLeftKanExtensionAt_of_equivalence
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y')
    [HasPointwiseLeftKanExtensionAt L F Y] :
    HasPointwiseLeftKanExtensionAt L' F Y' := by
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_iso' F eL,
    hasPointwiseLeftKanExtensionAt_iff_of_iso _ F e.symm]
  let Φ := CostructuredArrow.post L E.functor Y
  have : IsEquivalence Φ := CostructuredArrow.isEquivalencePost _ _ _
  have : HasColimit ((asEquivalence Φ).functor ⋙
    CostructuredArrow.proj (L ⋙ E.functor) (E.functor.obj Y) ⋙ F) :=
    (inferInstance : HasPointwiseLeftKanExtensionAt L F Y)
  exact hasColimit_of_equivalence_comp (asEquivalence Φ)

lemma hasPointwiseLeftKanExtensionAt_iff_of_equivalence
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y') :
    HasPointwiseLeftKanExtensionAt L F Y ↔
      HasPointwiseLeftKanExtensionAt L' F Y' := by
  constructor
  · intro
    exact hasPointwiseLeftKanExtensionAt_of_equivalence L L' F E eL Y Y' e
  · intro
    exact hasPointwiseLeftKanExtensionAt_of_equivalence L' L F E.symm
      (isoWhiskerRight eL.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft L E.unitIso.symm ≪≫ L.rightUnitor) Y' Y
      (E.inverse.mapIso e.symm ≪≫ E.unitIso.symm.app Y)

namespace LeftExtension

variable {F L} (E : LeftExtension L F)

/-- The cocone for `CostructuredArrow.proj L Y ⋙ F` attached to `E : LeftExtension L F`.
The point is this cocone is `E.right.obj Y` -/
@[simps]
def coconeAt (Y : D) : Cocone (CostructuredArrow.proj L Y ⋙ F) where
  pt := E.right.obj Y
  ι :=
    { app := fun g => E.hom.app g.left ≫ E.right.map g.hom
      naturality := fun g₁ g₂ φ => by
        dsimp
        rw [← CostructuredArrow.w φ]
        simp only [assoc, NatTrans.naturality_assoc, Functor.comp_map,
          Functor.map_comp, comp_id] }

/-- A left extension `E : LeftExtension L F` is a pointwise left Kan extension at `Y` when
`E.coconeAt Y` is a colimit cocone. -/
def IsPointwiseLeftKanExtensionAt (Y : D) := IsColimit (E.coconeAt Y)

variable {E}

lemma IsPointwiseLeftKanExtensionAt.hasPointwiseLeftKanExtensionAt
    {E : LeftExtension L F} {Y : D} (h : E.IsPointwiseLeftKanExtensionAt Y) :
    HasPointwiseLeftKanExtensionAt L F Y := ⟨_, h⟩

variable (E) in
/-- A left extension `E : LeftExtension L F` is a pointwise left Kan extension when
it is a pointwise left Kan extension at any object. -/
abbrev IsPointwiseLeftKanExtension := ∀ (Y : D), E.IsPointwiseLeftKanExtensionAt Y

variable (h : E.IsPointwiseLeftKanExtension)

lemma IsPointwiseLeftKanExtension.hasPointwiseLeftKanExtension :
    HasPointwiseLeftKanExtension L F :=
  fun Y => (h Y).hasPointwiseLeftKanExtensionAt

/-- The (unique) morphism from a pointwise left Kan extension. -/
def IsPointwiseLeftKanExtension.homFrom (G : LeftExtension L F) : E ⟶ G :=
  StructuredArrow.homMk
    { app := fun Y => (h Y).desc (LeftExtension.coconeAt G Y)
      naturality := fun Y₁ Y₂ φ => (h Y₁).hom_ext (fun X => by
        rw [(h Y₁).fac_assoc (coconeAt G Y₁) X]
        simpa using (h Y₂).fac (coconeAt G Y₂) ((CostructuredArrow.map φ).obj X)) }
    (by
      ext X
      simpa using (h (L.obj X)).fac (LeftExtension.coconeAt G _) (CostructuredArrow.mk (𝟙 _)))

lemma IsPointwiseLeftKanExtension.hom_ext {G : LeftExtension L F} {f₁ f₂ : E ⟶ G} : f₁ = f₂ := by
  ext Y
  apply (h Y).hom_ext
  intro X
  have eq₁ := congr_app (StructuredArrow.w f₁) X.left
  have eq₂ := congr_app (StructuredArrow.w f₂) X.left
  dsimp at eq₁ eq₂ ⊢
  simp only [assoc, NatTrans.naturality]
  rw [reassoc_of% eq₁, reassoc_of% eq₂]

/-- A pointwise left Kan extension is universal, i.e. it is a left Kan extension. -/
def IsPointwiseLeftKanExtension.isUniversal : E.IsUniversal :=
  IsInitial.ofUniqueHom h.homFrom (fun _ _ => h.hom_ext)

lemma IsPointwiseLeftKanExtension.isLeftKanExtension :
    E.right.IsLeftKanExtension E.hom where
  nonempty_isUniversal := ⟨h.isUniversal⟩

lemma IsPointwiseLeftKanExtension.hasLeftKanExtension :
    HasLeftKanExtension L F :=
  have := h.isLeftKanExtension
  HasLeftKanExtension.mk E.right E.hom

@[simps!]
def coconeAtIso {Y Y' : D} (e : Y ≅ Y') :
    (E.coconeAt Y').whisker (CostructuredArrow.mapIso e).functor ≅ E.coconeAt Y :=
  Cocones.ext (E.right.mapIso e.symm) (fun j => by
    dsimp
    simp only [assoc, ← map_comp, e.hom_inv_id, comp_id])

variable (L F)

@[simps]
def coconeAtFunctor (Y : D) : LeftExtension L F ⥤ Cocone (CostructuredArrow.proj L Y ⋙ F) where
  obj E := E.coconeAt Y
  map {E E'} φ := CoconeMorphism.mk (φ.right.app Y) (fun G => by
    dsimp
    rw [← StructuredArrow.w φ]
    simp only [assoc, NatTrans.naturality, const_obj_obj, whiskeringLeft_obj_obj, whiskeringLeft_obj_map,
      NatTrans.comp_app, comp_obj, whiskerLeft_app])

variable {L F E'}

def isPointwiseLeftKanExtensionAtEquivOfIso (e : E ≅ E') (Y : D) :
    E.IsPointwiseLeftKanExtensionAt Y ≃ E'.IsPointwiseLeftKanExtensionAt Y where
  toFun h := IsColimit.ofIsoColimit h ((coconeAtFunctor L F Y).mapIso e)
  invFun h := IsColimit.ofIsoColimit h ((coconeAtFunctor L F Y).mapIso e.symm)
  left_inv h := by
    dsimp only [IsPointwiseLeftKanExtensionAt]
    apply Subsingleton.elim
  right_inv h := by
    dsimp only [IsPointwiseLeftKanExtensionAt]
    apply Subsingleton.elim

def isPointwiseLeftKanExtensionEquivOfIso (e : E ≅ E') :
    E.IsPointwiseLeftKanExtension ≃ E'.IsPointwiseLeftKanExtension where
  toFun h := fun Y => (isPointwiseLeftKanExtensionAtEquivOfIso e Y) (h Y)
  invFun h := fun Y => (isPointwiseLeftKanExtensionAtEquivOfIso e Y).symm (h Y)
  left_inv h := by aesop_cat
  right_inv h := by aesop

def isPointwiseLeftKanExtensionAtOfIso'
    {Y : D} (hY : E.IsPointwiseLeftKanExtensionAt Y) {Y' : D} (e : Y ≅ Y') :
    E.IsPointwiseLeftKanExtensionAt Y' :=
  IsColimit.ofIsoColimit (hY.whiskerEquivalence _) (E.coconeAtIso e.symm)

def isPointwiseLeftKanExtensionAtEquivOfIso' {Y Y' : D} (e : Y ≅ Y') :
    E.IsPointwiseLeftKanExtensionAt Y ≃ E.IsPointwiseLeftKanExtensionAt Y' where
  toFun h := E.isPointwiseLeftKanExtensionAtOfIso' h e
  invFun h := E.isPointwiseLeftKanExtensionAtOfIso' h e.symm
  left_inv h := by
    dsimp only [IsPointwiseLeftKanExtensionAt]
    apply Subsingleton.elim
  right_inv h := by
    dsimp only [IsPointwiseLeftKanExtensionAt]
    apply Subsingleton.elim

variable (E E')

def isUniversalOfPointwise (h : E.IsPointwiseLeftKanExtension) :
    E.IsUniversal :=
  IsInitial.ofUniqueHom (fun G => StructuredArrow.homMk
        { app := fun Y => (h Y).desc (LeftExtension.coconeAt G Y)
          naturality := fun Y₁ Y₂ φ => by
            apply (h Y₁).hom_ext
            intro X
            rw [(h Y₁).fac_assoc (coconeAt G Y₁) X]
            simpa using (h Y₂).fac (coconeAt G Y₂) ((CostructuredArrow.map φ).obj X) }
      (by
        ext X
        simpa using (h (L.obj X)).fac (LeftExtension.coconeAt G _) (CostructuredArrow.mk (𝟙 _))))
    (fun G => by
      suffices ∀ (m₁ m₂ : E ⟶ G), m₁ = m₂ by intros; apply this
      intro m₁ m₂
      ext Y
      apply (h Y).hom_ext
      intro X
      have eq₁ := congr_app (StructuredArrow.w m₁) X.left
      have eq₂ := congr_app (StructuredArrow.w m₂) X.left
      dsimp at eq₁ eq₂ ⊢
      simp only [assoc, NatTrans.naturality]
      rw [reassoc_of% eq₁, reassoc_of% eq₂])

end LeftExtension

section

variable [HasPointwiseLeftKanExtension L F]

/-- The constructed pointwise left Kan extension when `HasPointwiseLeftKanExtension L F` holds. -/
@[simps]
noncomputable def pointwiseLeftKanExtension : D ⥤ H where
  obj Y := colimit (CostructuredArrow.proj L Y ⋙ F)
  map {Y₁ Y₂} f :=
    colimit.desc (CostructuredArrow.proj L Y₁ ⋙ F)
      (Cocone.mk (colimit (CostructuredArrow.proj L Y₂ ⋙ F))
        { app := fun g => colimit.ι (CostructuredArrow.proj L Y₂ ⋙ F)
            ((CostructuredArrow.map f).obj g)
          naturality := fun g₁ g₂ φ => by
            simpa using colimit.w (CostructuredArrow.proj L Y₂ ⋙ F)
              ((CostructuredArrow.map f).map φ) })
  map_id Y := colimit.hom_ext (fun j => by
    dsimp
    simp only [colimit.ι_desc, comp_id]
    congr
    apply CostructuredArrow.map_id)
  map_comp {Y₁ Y₂ Y₃} f f' := colimit.hom_ext (fun j => by
    dsimp
    simp only [colimit.ι_desc, colimit.ι_desc_assoc, comp_obj, CostructuredArrow.proj_obj]
    congr 1
    apply CostructuredArrow.map_comp)

/-- The unit of the constructed pointwise left Kan extension when
`HasPointwiseLeftKanExtension L F` holds. -/
@[simps]
noncomputable def pointwiseLeftKanExtensionUnit : F ⟶ L ⋙ pointwiseLeftKanExtension L F where
  app X := colimit.ι (CostructuredArrow.proj L (L.obj X) ⋙ F)
    (CostructuredArrow.mk (𝟙 (L.obj X)))
  naturality {X₁ X₂} f := by
    simp only [comp_obj, pointwiseLeftKanExtension_obj, comp_map,
      pointwiseLeftKanExtension_map, colimit.ι_desc, CostructuredArrow.map_mk]
    rw [id_comp]
    let φ : CostructuredArrow.mk (L.map f) ⟶ CostructuredArrow.mk (𝟙 (L.obj X₂)) :=
      CostructuredArrow.homMk f
    exact colimit.w (CostructuredArrow.proj L (L.obj X₂) ⋙ F) φ

/-- The functor `pointwiseLeftKanExtension L F` is a pointwise left Kan
extension of `F` along `L`. -/
noncomputable def pointwiseLeftKanExtensionIsPointwiseLeftKanExtension :
    (LeftExtension.mk _ (pointwiseLeftKanExtensionUnit L F)).IsPointwiseLeftKanExtension :=
  fun X => IsColimit.ofIsoColimit (colimit.isColimit _) (Cocones.ext (Iso.refl _) (fun j => by
    dsimp
    simp only [comp_id, colimit.ι_desc, CostructuredArrow.map_mk]
    congr 1
    rw [id_comp, ← CostructuredArrow.eq_mk]))

/-- The functor `pointwiseLeftKanExtension L F` is a left Kan extension of `F` along `L`. -/
noncomputable def pointwiseLeftKanExtensionIsUniversal :
    (LeftExtension.mk _ (pointwiseLeftKanExtensionUnit L F)).IsUniversal :=
  (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L F).isUniversal

instance : (pointwiseLeftKanExtension L F).IsLeftKanExtension
    (pointwiseLeftKanExtensionUnit L F) where
  nonempty_isUniversal := ⟨pointwiseLeftKanExtensionIsUniversal L F⟩

instance : HasLeftKanExtension L F :=
  HasLeftKanExtension.mk _ (pointwiseLeftKanExtensionUnit L F)

variable {F L}

noncomputable def isPointwiseLeftKanExtensionOfIsLeftKanExtension (F' : D ⥤ H) (α : F ⟶ L ⋙ F')
    [F'.IsLeftKanExtension α] :
    (LeftExtension.mk _ α).IsPointwiseLeftKanExtension :=
  LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
    (IsColimit.coconePointUniqueUpToIso (pointwiseLeftKanExtensionIsUniversal L F)
      (F'.isUniversalOfIsLeftKanExtension α))
    (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L F)

end

end Functor

end CategoryTheory
