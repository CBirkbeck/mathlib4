import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.CatCommSq
import Mathlib.CategoryTheory.Localization.Equivalence

universe v₁ v₂ v₃ v₄ v₄' v₅ v₅' v₆ u₁ u₂ u₃ u₄ u₄' u₅ u₅' u₆

namespace CategoryTheory

open Localization Category

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  {D₁ : Type u₄} {D₂ : Type u₅} {D₃ : Type u₆}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  [Category.{v₄} D₁] [Category.{v₅} D₂] [Category.{v₆} D₂]
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)

/-- If `W₁ : MorphismProperty C₁` and `W₂ : MorphismProperty C₂`, a `LocalizorMorphism W₁ W₂`
is the datum of a functor `C₁ ⥤ C₂` which sends morphisms in `W₁` to morphisms in `W₂` -/
structure LocalizorMorphism where
  /-- a functor between the two categories -/
  functor : C₁ ⥤ C₂
  /-- the functor is compatible with the `MorphismProperty` -/
  map : W₁ ⊆ W₂.inverseImage functor

namespace LocalizorMorphism

@[simps]
def id : LocalizorMorphism W₁ W₁ where
  functor := 𝟭 C₁
  map _ _ _ hf := hf

variable {W₁ W₂ W₃}

@[simps]
def comp (Φ : LocalizorMorphism W₁ W₂) (Ψ : LocalizorMorphism W₂ W₃) :
    LocalizorMorphism W₁ W₃ where
  functor := Φ.functor ⋙ Ψ.functor
  map _ _ _ hf := Ψ.map _ (Φ.map _ hf)

variable (Φ : LocalizorMorphism W₁ W₂) (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]

lemma inverts : W₁.IsInvertedBy (Φ.functor ⋙ L₂) :=
  fun _ _ _ hf => Localization.inverts L₂ W₂ _ (Φ.map _ hf)

/-- When `Φ : LocalizorMorphism W₁ W₂` and that `L₁` and `L₂` are localization functors
for `W₁` and `W₂`, then `Φ.localizedFunctor L₁ L₂` is the induced functor on the
localized categories. --/
noncomputable def localizedFunctor : D₁ ⥤ D₂ :=
  lift (Φ.functor ⋙ L₂) (Φ.inverts _) L₁

noncomputable instance : Lifting L₁ W₁ (Φ.functor ⋙ L₂) (Φ.localizedFunctor L₁ L₂) := by
  dsimp [localizedFunctor]
  infer_instance

/-- The 2-commutative square expressing that `Φ.localizedFunctor L₁ L₂` lifts the
functor `Φ.functor`  -/
noncomputable instance catCommSq : CatCommSq Φ.functor L₁ L₂ (Φ.localizedFunctor L₁ L₂) :=
  CatCommSq.mk (Lifting.iso _ W₁ _ _).symm

variable (G : D₁ ⥤ D₂)

section

variable [c : CatCommSq Φ.functor L₁ L₂ G]
  {D₁' : Type u₄'} {D₂' : Type u₅'}
  [Category.{v₄'} D₁'] [Category.{v₅'} D₂']
  (L₁' : C₁ ⥤ D₁') (L₂' : C₂ ⥤ D₂') [L₁'.IsLocalization W₁] [L₂'.IsLocalization W₂]
  (G' : D₁' ⥤ D₂') [c' : CatCommSq Φ.functor L₁' L₂' G']

/-- If a localizor morphism induces an equivalence on some choice of localized categories,
it will be so for any choice of localized categoriees. -/
noncomputable def isEquivalence_imp [IsEquivalence G] :
  IsEquivalence G' := by
    let E₁ := Localization.uniq L₁ L₁' W₁
    let E₂ := Localization.uniq L₂ L₂' W₂
    letI : Lifting L₁ W₁ (Φ.functor ⋙ L₂') (G ⋙ E₂.functor) :=
      Lifting.mk ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (Iso.symm c.iso) _ ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (compUniqFunctor L₂ L₂' W₂))
    letI : Lifting L₁ W₁ (L₁' ⋙ G') (E₁.functor ⋙ G') :=
      Lifting.mk ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (compUniqFunctor L₁ L₁' W₁) _)
    have φ : CatCommSq G E₁.functor E₂.functor G' :=
      CatCommSq.mk (liftNatIso L₁ W₁ (Φ.functor ⋙ L₂') (L₁' ⋙ G') _ _ c'.iso)
    exact IsEquivalence.cancelCompLeft E₁.functor G' inferInstance
      (IsEquivalence.ofIso φ.iso inferInstance)

lemma nonempty_isEquivalence_iff : Nonempty (IsEquivalence G) ↔ Nonempty (IsEquivalence G') := by
  constructor
  . rintro ⟨e⟩
    exact ⟨Φ.isEquivalence_imp L₁ L₂ G L₁' L₂' G'⟩
  . rintro ⟨e'⟩
    exact ⟨Φ.isEquivalence_imp L₁' L₂' G' L₁ L₂ G⟩

end

/-- condition that `LocalizorMorphism` induces an equivalence of localized categories -/
class IsLocalizedEquivalence : Prop :=
  /-- the induced functor on the constructed localized categories is an equivalence -/
  nonempty_isEquivalence : Nonempty (IsEquivalence (Φ.localizedFunctor W₁.Q W₂.Q))

lemma IsLocalizedEquivalence.mk' [CatCommSq Φ.functor L₁ L₂ G] [IsEquivalence G] :
    Φ.IsLocalizedEquivalence where
  nonempty_isEquivalence := by
    rw [Φ.nonempty_isEquivalence_iff W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) L₁ L₂ G]
    exact ⟨inferInstance⟩

/-- If a `LocalizorMorphism` is a localized equivalence, then any compatible functor
on the localized categories is an equivalence. -/
noncomputable def isEquivalence [h : Φ.IsLocalizedEquivalence] [CatCommSq Φ.functor L₁ L₂ G] :
    IsEquivalence G := by
  apply Nonempty.some
  rw [Φ.nonempty_isEquivalence_iff L₁ L₂ G W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q)]
  exact h.nonempty_isEquivalence

/-- If a `LocalizorMorphism` is a localized equivalence, then the induced functor on
the localized categories is an equivalence -/
noncomputable instance localizedFunctor_isEquivalence [Φ.IsLocalizedEquivalence] :
    IsEquivalence (Φ.localizedFunctor L₁ L₂) :=
  Φ.isEquivalence L₁ L₂ _

lemma IsLocalizedEquivalence.of_isLocalization_of_isLocalization
    [(Φ.functor ⋙ L₂).IsLocalization W₁] :
    IsLocalizedEquivalence Φ := by
  have : CatCommSq Φ.functor (Φ.functor ⋙ L₂) L₂ (𝟭 D₂) :=
    CatCommSq.mk (Functor.rightUnitor _).symm
  exact IsLocalizedEquivalence.mk' Φ (Φ.functor ⋙ L₂) L₂ (𝟭 D₂)

lemma IsLocalizedEquivalence.of_equivalence [IsEquivalence Φ.functor]
    (h : W₂ ⊆ W₁.map Φ.functor) : IsLocalizedEquivalence Φ := by
  haveI : Functor.IsLocalization (Φ.functor ⋙ MorphismProperty.Q W₂) W₁ := by
    refine' Functor.IsLocalization.of_equivalence_source W₂.Q W₂ (Φ.functor ⋙ W₂.Q) W₁
      (Functor.asEquivalence Φ.functor).symm _ (Φ.inverts W₂.Q)
      ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight ((Equivalence.unitIso _).symm) _ ≪≫
      Functor.leftUnitor _)
    erw [MorphismProperty.inverseImage_functorInv W₁ Φ.functor]
    exact h
  exact IsLocalizedEquivalence.of_isLocalization_of_isLocalization Φ W₂.Q

end LocalizorMorphism

end CategoryTheory
