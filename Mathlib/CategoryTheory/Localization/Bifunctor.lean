import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.CategoryTheory.Functor.Currying

namespace CategoryTheory

variable {C₁ C₂ D₁ D₂ E E' : Type*} [Category C₁] [Category C₂]
  [Category D₁] [Category D₂] [Category E] [Category E']

@[simps!]
def curryObjProdComp (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (G : D₁ × D₂ ⥤ E) :
    curry.obj ((F₁.prod F₂).comp G) ≅
      F₁ ⋙ curry.obj G ⋙ (whiskeringLeft C₂ D₂ E).obj F₂ :=
  NatIso.ofComponents (fun X₁ => NatIso.ofComponents (fun X₂ => Iso.refl _))

@[simps!]
def whiskeringLeft₂ObjObj (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (E : Type*) [Category E] :
    (D₁ ⥤ D₂ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ E) :=
  (whiskeringRight D₁ (D₂ ⥤ E) (C₂ ⥤ E)).obj ((whiskeringLeft C₂ D₂ E).obj F₂) ⋙
    (whiskeringLeft C₁ D₁ (C₂ ⥤ E)).obj F₁

-- whiskeringRight₂ should be given a better name
variable (C₁ C₂) in
@[simps!]
def whiskeringRight₂' (G : E ⥤ E') :
    (C₁ ⥤ C₂ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ E' :=
  (whiskeringRight C₁ (C₂ ⥤ E) (C₂ ⥤ E')).obj ((whiskeringRight C₂ E E').obj G)

namespace MorphismProperty

def IsInvertedBy₂ (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    (F : C₁ ⥤ C₂ ⥤ E) : Prop :=
  (W₁.prod W₂).IsInvertedBy (uncurry.obj F)

end MorphismProperty

namespace Localization

section

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)

class Lifting₂ (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    (F : C₁ ⥤ C₂ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ E) where
  iso' : (whiskeringLeft₂ObjObj L₁ L₂ E).obj F' ≅ F

variable (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  (F : C₁ ⥤ C₂ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ E) [Lifting₂ L₁ L₂ W₁ W₂ F F']

noncomputable def Lifting₂.iso : (whiskeringLeft₂ObjObj L₁ L₂ E).obj F' ≅ F :=
  Lifting₂.iso' W₁ W₂

noncomputable def Lifting₂.fst (X₁ : C₁) :
    Lifting L₂ W₂ (F.obj X₁) (F'.obj (L₁.obj X₁)) where
  iso' := ((evaluation _ _).obj X₁).mapIso (Lifting₂.iso L₁ L₂ W₁ W₂ F F')

noncomputable instance Lifting₂.flip : Lifting₂ L₂ L₁ W₂ W₁ F.flip F'.flip where
  iso' := (flipFunctor _ _ _).mapIso (Lifting₂.iso L₁ L₂ W₁ W₂ F F')

noncomputable def Lifting₂.snd (X₂ : C₂) :
    Lifting L₁ W₁ (F.flip.obj X₂) (F'.flip.obj (L₂.obj X₂)) :=
  Lifting₂.fst L₂ L₁ W₂ W₁ F.flip F'.flip X₂

noncomputable instance Lifting₂.uncurry [Lifting₂ L₁ L₂ W₁ W₂ F F'] :
    Lifting (L₁.prod L₂) (W₁.prod W₂) (uncurry.obj F) (uncurry.obj F') where
  iso' := uncurry.mapIso (Lifting₂.iso L₁ L₂ W₁ W₂ F F')

end

section

variable (F : C₁ ⥤ C₂ ⥤ E) {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  (hF : MorphismProperty.IsInvertedBy₂ W₁ W₂ F)
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities]

noncomputable def lift₂ : D₁ ⥤ D₂ ⥤ E :=
  curry.obj (lift (uncurry.obj F) hF (L₁.prod L₂))

noncomputable instance : Lifting₂ L₁ L₂ W₁ W₂ F (lift₂ F hF L₁ L₂) where
  iso' := (curryObjProdComp _ _ _).symm ≪≫
    curry.mapIso (fac (uncurry.obj F) hF (L₁.prod L₂)) ≪≫
    currying.unitIso.symm.app F

noncomputable instance (X₁ : C₁) :
    Lifting L₂ W₂ (F.obj X₁) ((lift₂ F hF L₁ L₂).obj (L₁.obj X₁)) :=
  Lifting₂.fst _ _ W₁ _ _ _ _

noncomputable instance (X₂ : C₂) :
    Lifting L₁ W₁ (F.flip.obj X₂) ((lift₂ F hF L₁ L₂).flip.obj (L₂.obj X₂)) :=
  Lifting₂.snd _ _ _ W₂ _ _ _

lemma lift₂_iso_hom_app_app₁ (X₁ : C₁) (X₂ : C₂) :
    ((Lifting₂.iso L₁ L₂ W₁ W₂ F (lift₂ F hF L₁ L₂)).hom.app X₁).app X₂ =
      (Lifting.iso L₂ W₂ (F.obj X₁) ((lift₂ F hF L₁ L₂).obj (L₁.obj X₁))).hom.app X₂ :=
  rfl

lemma lift₂_iso_hom_app_app₂ (X₁ : C₁) (X₂ : C₂) :
    ((Lifting₂.iso L₁ L₂ W₁ W₂ F (lift₂ F hF L₁ L₂)).hom.app X₁).app X₂ =
      (Lifting.iso L₁ W₁ (F.flip.obj X₂) ((lift₂ F hF L₁ L₂).flip.obj (L₂.obj X₂))).hom.app X₁ :=
  rfl

noncomputable def lift₂NatIso' {F₁ F₂ : C₁ ⥤ C₂ ⥤ E} (F₁' F₂' : D₁ ⥤ D₂ ⥤ E)
    [Lifting₂ L₁ L₂ W₁ W₂ F₁ F₁'] [Lifting₂ L₁ L₂ W₁ W₂ F₂ F₂'] (e : F₁ ≅ F₂) : F₁' ≅ F₂' := by
  let i := (liftNatIso (L₁.prod L₂) (W₁.prod W₂) _ _ (uncurry.obj F₁') ((uncurry.obj F₂'))
    (uncurry.mapIso e))
  have : (uncurry (C := D₁) (D := D₂) (E := E)).IsEquivalence :=
    inferInstanceAs currying.functor.IsEquivalence
  exact uncurry.preimageIso i

noncomputable abbrev lift₂NatIso {F₁ F₂ : C₁ ⥤ C₂ ⥤ E}
    (hF₁ : W₁.IsInvertedBy₂ W₂ F₁)
    (hF₂ : W₁.IsInvertedBy₂ W₂ F₂)
    (e : F₁ ≅ F₂) : lift₂ _ hF₁ L₁ L₂  ≅ lift₂ _ hF₂ L₁ L₂ :=
  curry.mapIso (liftNatIso (L₁.prod L₂) (W₁.prod W₂) _ _ _ _ (uncurry.mapIso e))

end

section

end

end Localization

end CategoryTheory
