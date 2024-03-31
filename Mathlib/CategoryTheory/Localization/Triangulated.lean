<<<<<<< HEAD
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Localization.Preadditive
import Mathlib.CategoryTheory.Adjunction.Limits

namespace CategoryTheory

open Category Limits Pretriangulated

section

variable {C : Type _} [Category C]
  [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
    [∀ (n : ℤ), (shiftFunctor C n).Additive ] [Pretriangulated C]

class MorphismProperty.IsCompatibleWithTriangulation (W : MorphismProperty C) : Prop :=
  condition : ∀ (T₁ T₂ : Triangle C) (_ : T₁ ∈ distTriang C) (_ : T₂ ∈ distTriang C)
  (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (_ : W a) (_ : W b)
  (_ : T₁.mor₁ ≫ b = a ≫ T₂.mor₁), ∃ (c : T₁.obj₃ ⟶ T₂.obj₃) (_ : W c),
  (T₁.mor₂ ≫ c = b ≫ T₂.mor₂) ∧ (T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃)

end

namespace Functor

variable {C D : Type _} [Category C] [Category D]
  [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [HasShift D ℤ]
  (L : C ⥤ D) [CommShift L ℤ]

=======
/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.ComposableArrowsTwo
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Shift.Localization

/-! # Localization of triangulated categories

If `L : C ⥤ D` is a localization functor for a class of morphisms `W` that is compatible
with the triangulation on the category `C` and admits left and right calculus of fractions,
it is shown in this file that `D` can be equipped with a pretriangulated category structure,
and that it is triangulated.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

namespace CategoryTheory

open Category Limits Pretriangulated Localization

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
  [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasShift D ℤ] [L.CommShift ℤ]

namespace MorphismProperty

/-- Given `W` is a class of morphisms in a pretriangulated category `C`, this is the condition
that `W` is compatible with the triangulation on `C`. -/
class IsCompatibleWithTriangulation (W : MorphismProperty C)
    extends W.IsCompatibleWithShift ℤ : Prop where
  compatible_with_triangulation (T₁ T₂ : Triangle C)
    (_ : T₁ ∈ distTriang C) (_ : T₂ ∈ distTriang C)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (_ : W a) (_ : W b)
    (_ : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
      ∃ (c : T₁.obj₃ ⟶ T₂.obj₃) (_ : W c),
        (T₁.mor₂ ≫ c = b ≫ T₂.mor₂) ∧ (T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃)

export IsCompatibleWithTriangulation (compatible_with_triangulation)

end MorphismProperty

namespace Functor

/-- Given a functor `C ⥤ D` from a pretriangulated category, this is the set of
triangles in `D` that are in the essential image of distinguished triangles of `C`. -/
>>>>>>> origin/derived-category
def essImageDistTriang : Set (Triangle D) :=
  fun T => ∃ (T' : Triangle C) (_ : T ≅ L.mapTriangle.obj T'), T' ∈ distTriang C

lemma essImageDistTriang_mem_of_iso {T₁ T₂ : Triangle D} (e : T₂ ≅ T₁)
    (h : T₁ ∈ L.essImageDistTriang) : T₂ ∈ L.essImageDistTriang := by
  obtain ⟨T', e', hT'⟩ := h
  exact ⟨T', e ≪≫ e', hT'⟩

lemma contractible_mem_essImageDistTriang [EssSurj L] [HasZeroObject D]
    [HasZeroMorphisms D] [L.PreservesZeroMorphisms] (X : D) :
    contractibleTriangle X ∈ L.essImageDistTriang := by
<<<<<<< HEAD
  refine' ⟨contractibleTriangle (L.objPreimage X), _, Pretriangulated.contractible_distinguished _⟩
=======
  refine' ⟨contractibleTriangle (L.objPreimage X), _, contractible_distinguished _⟩
>>>>>>> origin/derived-category
  exact ((contractibleTriangleFunctor D).mapIso (L.objObjPreimageIso X)).symm ≪≫
    Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) L.mapZeroObject.symm (by simp) (by simp) (by simp)

lemma rotate_essImageDistTriang [Preadditive D] [L.Additive]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] (T : Triangle D) :
  T ∈ L.essImageDistTriang ↔ T.rotate ∈ L.essImageDistTriang := by
  constructor
  · rintro ⟨T', e', hT'⟩
    exact ⟨T'.rotate, (rotate D).mapIso e' ≪≫ L.mapTriangleRotateIso.app T',
      rot_of_distTriang T' hT'⟩
  · rintro ⟨T', e', hT'⟩
    exact ⟨T'.invRotate, (triangleRotation D).unitIso.app T ≪≫ (invRotate D).mapIso e' ≪≫
<<<<<<< HEAD
      L.mapTriangleInvRotateIso.app T',  inv_rot_of_distTriang T' hT'⟩
=======
      L.mapTriangleInvRotateIso.app T', inv_rot_of_distTriang T' hT'⟩

lemma complete_distinguished_essImageDistTriang_morphism
    (H : ∀ (T₁' T₂' : Triangle C) (_ : T₁' ∈ distTriang C) (_ : T₂' ∈ distTriang C)
      (a : L.obj (T₁'.obj₁) ⟶ L.obj (T₂'.obj₁)) (b : L.obj (T₁'.obj₂) ⟶ L.obj (T₂'.obj₂))
      (_ : L.map T₁'.mor₁ ≫ b = a ≫ L.map T₂'.mor₁),
      ∃ (φ : L.mapTriangle.obj T₁' ⟶ L.mapTriangle.obj T₂'), φ.hom₁ = a ∧ φ.hom₂ = b)
    (T₁ T₂ : Triangle D)
    (hT₁ : T₁ ∈ Functor.essImageDistTriang L) (hT₂ : T₂ ∈ L.essImageDistTriang)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨T₁', e₁, hT₁'⟩ := hT₁
  obtain ⟨T₂', e₂, hT₂'⟩ := hT₂
  have comm₁ := e₁.inv.comm₁
  have comm₁' := e₂.hom.comm₁
  have comm₂ := e₁.hom.comm₂
  have comm₂' := e₂.hom.comm₂
  have comm₃ := e₁.inv.comm₃
  have comm₃' := e₂.hom.comm₃
  dsimp at comm₁ comm₁' comm₂ comm₂' comm₃ comm₃'
  simp only [assoc] at comm₃
  obtain ⟨φ, hφ₁, hφ₂⟩ := H T₁' T₂' hT₁' hT₂' (e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁)
    (e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂)
    (by simp only [assoc, ← comm₁', ← reassoc_of% fac, ← reassoc_of% comm₁])
  have h₂ := φ.comm₂
  have h₃ := φ.comm₃
  dsimp at h₂ h₃
  simp only [assoc] at h₃
  refine' ⟨e₁.hom.hom₃ ≫ φ.hom₃ ≫ e₂.inv.hom₃, _, _⟩
  · rw [reassoc_of% comm₂, reassoc_of% h₂, hφ₂, assoc, assoc,
      Iso.hom_inv_id_triangle_hom₂_assoc, ← reassoc_of% comm₂',
      Iso.hom_inv_id_triangle_hom₃, comp_id]
  · rw [assoc, assoc, ← cancel_epi e₁.inv.hom₃, ← reassoc_of% comm₃,
      Iso.inv_hom_id_triangle_hom₃_assoc, ← cancel_mono (e₂.hom.hom₁⟦(1 : ℤ)⟧'),
      assoc, assoc, assoc, assoc, assoc, ← Functor.map_comp, ← Functor.map_comp, ← hφ₁,
      h₃, comm₃', Iso.inv_hom_id_triangle_hom₃_assoc]
>>>>>>> origin/derived-category

end Functor

namespace Triangulated

namespace Localization

<<<<<<< HEAD
section

variable {C D : Type _} [Category C] [Category D]
  [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.IsCompatibleWithShift ℤ] [W.IsCompatibleWithTriangulation]
    [W.HasLeftCalculusOfFractions] [W.HasRightCalculusOfFractions]
    [HasShift D ℤ] [L.CommShift ℤ]

section

variable [Preadditive D] [HasZeroObject D]
=======
variable (W : MorphismProperty C) [L.IsLocalization W]
  [W.IsCompatibleWithTriangulation] [W.HasLeftCalculusOfFractions]
  [Preadditive D] [HasZeroObject D]
>>>>>>> origin/derived-category
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [L.Additive]

lemma distinguished_cocone_triangle {X Y : D} (f : X ⟶ Y) :
    ∃ (Z : D) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ L.essImageDistTriang := by
<<<<<<< HEAD
  have := Localization.essSurj_mapArrow_of_hasLeftCalculusofFractions L W
=======
  have := essSurj_mapArrow_of_hasLeftCalculusofFractions L W
>>>>>>> origin/derived-category
  obtain ⟨φ, ⟨e⟩⟩ : ∃ (φ : Arrow C), Nonempty (L.mapArrow.obj φ ≅ Arrow.mk f) :=
    ⟨_, ⟨Functor.objObjPreimageIso _ _⟩⟩
  obtain ⟨Z, g, h, H⟩ := Pretriangulated.distinguished_cocone_triangle φ.hom
  refine' ⟨L.obj Z, e.inv.right ≫ L.map g,
    L.map h ≫ (L.commShiftIso (1 : ℤ)).hom.app _ ≫ e.hom.left⟦(1 : ℤ)⟧', _, _, H⟩
  refine' Triangle.isoMk _ _ (Arrow.leftFunc.mapIso e.symm) (Arrow.rightFunc.mapIso e.symm)
    (Iso.refl _) e.inv.w.symm (by simp) _
  dsimp
  simp only [assoc, id_comp, ← Functor.map_comp, ← Arrow.comp_left, e.hom_inv_id, Arrow.id_left,
    Functor.mapArrow_obj_left, Functor.map_id, comp_id]

lemma complete_distinguished_triangle_morphism (T₁ T₂ : Triangle D)
<<<<<<< HEAD
    (hT₁ : T₁ ∈ Functor.essImageDistTriang L) (hT₂ : T₂ ∈ Functor.essImageDistTriang L)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  suffices ∀ (T₁' T₂' : Triangle C) (_ : T₁' ∈ distTriang C) (_ : T₂' ∈ distTriang C)
      (a : L.obj (T₁'.obj₁) ⟶ L.obj (T₂'.obj₁)) (b : L.obj (T₁'.obj₂) ⟶ L.obj (T₂'.obj₂))
      (_ : L.map T₁'.mor₁ ≫ b = a ≫ L.map T₂'.mor₁),
      ∃ (φ : L.mapTriangle.obj T₁' ⟶ L.mapTriangle.obj T₂'), φ.hom₁ = a ∧ φ.hom₂ = b by
    obtain ⟨T₁', e₁, hT₁'⟩ := hT₁
    obtain ⟨T₂', e₂, hT₂'⟩ := hT₂
    have comm₁ := e₁.inv.comm₁
    have comm₁' := e₂.hom.comm₁
    have comm₂ := e₁.hom.comm₂
    have comm₂' := e₂.hom.comm₂
    have comm₃ := e₁.inv.comm₃
    have comm₃' := e₂.hom.comm₃
    dsimp at comm₁ comm₁' comm₂ comm₂' comm₃ comm₃'
    simp only [assoc] at comm₃
    obtain ⟨φ, hφ₁, hφ₂⟩ := this T₁' T₂' hT₁' hT₂' (e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁)
      (e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂)
      (by simp only [assoc, ← comm₁', ← reassoc_of% fac, ← reassoc_of% comm₁])
    have h₂ := φ.comm₂
    have h₃ := φ.comm₃
    dsimp at h₂ h₃
    simp only [assoc] at h₃
    refine' ⟨e₁.hom.hom₃ ≫ φ.hom₃ ≫ e₂.inv.hom₃, _, _⟩
    · rw [reassoc_of% comm₂, reassoc_of% h₂, hφ₂, assoc, assoc,
        Iso.hom_inv_id_triangle_hom₂_assoc, ← reassoc_of% comm₂',
        Iso.hom_inv_id_triangle_hom₃, comp_id]
    · rw [assoc, assoc, ← cancel_epi e₁.inv.hom₃, ← reassoc_of% comm₃,
        Iso.inv_hom_id_triangle_hom₃_assoc, ← cancel_mono (e₂.hom.hom₁⟦(1 : ℤ)⟧'),
        assoc, assoc, assoc, assoc, assoc, ← Functor.map_comp, ← Functor.map_comp, ← hφ₁,
        h₃, comm₃', Iso.inv_hom_id_triangle_hom₃_assoc]
  clear a b fac hT₁ hT₂ T₁ T₂
  intro T₁ T₂ hT₁ hT₂ a b fac
  obtain ⟨α, hα⟩ := Localization.exists_leftFraction L W a
  obtain ⟨β, hβ⟩ := (MorphismProperty.RightFraction.mk α.s α.hs T₂.mor₁).exists_leftFraction
  obtain ⟨γ, hγ⟩ := Localization.exists_leftFraction L W (b ≫ L.map β.s)
  have := Localization.inverts L W β.s β.hs
  have := Localization.inverts L W γ.s γ.hs
=======
    (hT₁ : T₁ ∈ L.essImageDistTriang) (hT₂ : T₂ ∈ L.essImageDistTriang)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  refine L.complete_distinguished_essImageDistTriang_morphism ?_ T₁ T₂ hT₁ hT₂ a b fac
  clear a b fac hT₁ hT₂ T₁ T₂
  intro T₁ T₂ hT₁ hT₂ a b fac
  obtain ⟨α, hα⟩ := exists_leftFraction L W a
  obtain ⟨β, hβ⟩ := (MorphismProperty.RightFraction.mk α.s α.hs T₂.mor₁).exists_leftFraction
  obtain ⟨γ, hγ⟩ := exists_leftFraction L W (b ≫ L.map β.s)
  have := inverts L W β.s β.hs
  have := inverts L W γ.s γ.hs
>>>>>>> origin/derived-category
  dsimp at hβ
  obtain ⟨Z₂, σ, hσ, fac⟩ := (MorphismProperty.map_eq_iff_postcomp L W
    (α.f ≫ β.f ≫ γ.s) (T₁.mor₁ ≫ γ.f)).1 (by
      rw [← cancel_mono (L.map β.s), assoc, assoc, hγ, ← cancel_mono (L.map γ.s),
        assoc, assoc, assoc, hα, MorphismProperty.LeftFraction.map_comp_map_s,
        ← Functor.map_comp] at fac
      rw [fac, ← Functor.map_comp_assoc, hβ, Functor.map_comp, Functor.map_comp,
        Functor.map_comp, assoc, MorphismProperty.LeftFraction.map_comp_map_s_assoc])
  simp only [assoc] at fac
  obtain ⟨Y₃, g, h, hT₃⟩ := Pretriangulated.distinguished_cocone_triangle (β.f ≫ γ.s ≫ σ)
  let T₃ := Triangle.mk (β.f ≫ γ.s ≫ σ) g h
  change T₃ ∈ distTriang C at hT₃
  have hβγσ : W (β.s ≫ γ.s ≫ σ) := W.comp_mem _ _ β.hs (W.comp_mem _ _ γ.hs hσ)
<<<<<<< HEAD
  obtain ⟨ψ₃, hψ₃, hψ₁, hψ₂⟩ := MorphismProperty.IsCompatibleWithTriangulation.condition
    T₂ T₃ hT₂ hT₃ α.s (β.s ≫ γ.s ≫ σ) α.hs hβγσ (by dsimp [T₃]; rw [reassoc_of% hβ])
  let ψ : T₂ ⟶ T₃ := Triangle.homMk _ _ α.s (β.s ≫ γ.s ≫ σ) ψ₃ (by dsimp [T₃]; rw [reassoc_of% hβ]) hψ₁ hψ₂
  have : IsIso (L.mapTriangle.map ψ) := Triangle.isIso_of_isIsos _
    (Localization.inverts L W α.s α.hs) (Localization.inverts L W _ hβγσ)
    (Localization.inverts L W ψ₃ hψ₃)
  refine' ⟨L.mapTriangle.map (completeDistinguishedTriangleMorphism T₁ T₃ hT₁ hT₃ α.f (γ.f ≫ σ) fac.symm) ≫ inv (L.mapTriangle.map ψ), _, _⟩
=======
  obtain ⟨ψ₃, hψ₃, hψ₁, hψ₂⟩ := MorphismProperty.compatible_with_triangulation
    T₂ T₃ hT₂ hT₃ α.s (β.s ≫ γ.s ≫ σ) α.hs hβγσ (by dsimp [T₃]; rw [reassoc_of% hβ])
  let ψ : T₂ ⟶ T₃ := Triangle.homMk _ _ α.s (β.s ≫ γ.s ≫ σ) ψ₃
    (by dsimp [T₃]; rw [reassoc_of% hβ]) hψ₁ hψ₂
  have : IsIso (L.mapTriangle.map ψ) := Triangle.isIso_of_isIsos _
    (inverts L W α.s α.hs) (inverts L W _ hβγσ) (inverts L W ψ₃ hψ₃)
  refine' ⟨L.mapTriangle.map (completeDistinguishedTriangleMorphism T₁ T₃ hT₁ hT₃ α.f
      (γ.f ≫ σ) fac.symm) ≫ inv (L.mapTriangle.map ψ), _, _⟩
>>>>>>> origin/derived-category
  · rw [← cancel_mono (L.mapTriangle.map ψ).hom₁, ← comp_hom₁, assoc, IsIso.inv_hom_id, comp_id]
    dsimp [ψ]
    rw [hα, MorphismProperty.LeftFraction.map_comp_map_s]
  · rw [← cancel_mono (L.mapTriangle.map ψ).hom₂, ← comp_hom₂, assoc, IsIso.inv_hom_id, comp_id]
    dsimp [ψ]
    simp only [Functor.map_comp, reassoc_of% hγ,
      MorphismProperty.LeftFraction.map_comp_map_s_assoc]

<<<<<<< HEAD
=======
/-- The pretriangulated structure on the localized category. -/
>>>>>>> origin/derived-category
def pretriangulated : Pretriangulated D where
  distinguishedTriangles := L.essImageDistTriang
  isomorphic_distinguished _ hT₁ _ e := L.essImageDistTriang_mem_of_iso e hT₁
  contractible_distinguished :=
<<<<<<< HEAD
    have := Localization.essSurj L W ; L.contractible_mem_essImageDistTriang
=======
    have := essSurj L W; L.contractible_mem_essImageDistTriang
>>>>>>> origin/derived-category
  distinguished_cocone_triangle f := distinguished_cocone_triangle L W f
  rotate_distinguished_triangle := L.rotate_essImageDistTriang
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism L W

lemma isTriangulated_functor :
<<<<<<< HEAD
    letI : Pretriangulated D := pretriangulated L W ; L.IsTriangulated :=
    letI : Pretriangulated D := pretriangulated L W ; ⟨fun T hT => ⟨T, Iso.refl _, hT⟩⟩

lemma essSurj_mapArrow : EssSurj L.mapArrow :=
  Localization.essSurj_mapArrow_of_hasLeftCalculusofFractions L W

lemma isTriangulated_of_exists_lifting_composable_morphisms [Pretriangulated D]
    [L.IsTriangulated] [IsTriangulated C]
    (hF : ∀ ⦃X₁ X₂ X₃ : D⦄ (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃),
      ∃ (Y₁ Y₂ Y₃ : C) (f' : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃)
        (e₁ : L.obj Y₁ ≅ X₁) (e₂ : L.obj Y₂ ≅ X₂) (e₃ : L.obj Y₃ ≅ X₃),
        L.map f' ≫ e₂.hom = e₁.hom ≫ f ∧ L.map g' ≫ e₃.hom = e₂.hom ≫ g) :
    IsTriangulated D := by
  apply IsTriangulated.mk'
  intro X₁ X₂ X₃ f g
  obtain ⟨Y₁, Y₂, Y₃, f', g', e₁, e₂, e₃, comm₁, comm₂⟩ := hF f g
  obtain ⟨Z₁₂, v₁₂, w₁₂, h₁₂⟩ := Pretriangulated.distinguished_cocone_triangle f'
  obtain ⟨Z₂₃, v₂₃, w₂₃, h₂₃⟩ := Pretriangulated.distinguished_cocone_triangle g'
  obtain ⟨Z₁₃, v₁₃, w₁₃, h₁₃⟩ := Pretriangulated.distinguished_cocone_triangle (f' ≫ g')
  let H := Triangulated.someOctahedron rfl h₁₂ h₂₃ h₁₃
  let T₁₃' := Triangle.mk (L.map f' ≫ L.map g') (L.map v₁₃) (L.map w₁₃ ≫ (L.commShiftIso (1 : ℤ)).hom.app Y₁)
  have h₁₃' : T₁₃' ∈ distTriang D := isomorphic_distinguished _ (L.map_distinguished _ h₁₃) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [T₁₃']) (by simp [T₁₃']) (by simp [T₁₃']))
  refine' ⟨L.obj Y₁, L.obj Y₂, L.obj Y₃, L.obj Z₁₂, L.obj Z₂₃, L.obj Z₁₃, L.map f', L.map g',
    e₁.symm, e₂.symm, e₃.symm, _, _,
      _, _, L.map_distinguished _ h₁₂,
      _, _, L.map_distinguished _ h₂₃,
      _, _, h₁₃', ⟨_⟩⟩
  · dsimp
    simp only [← cancel_epi e₁.hom, ← reassoc_of% comm₁, Iso.hom_inv_id,
      Iso.hom_inv_id_assoc, comp_id]
  · dsimp
    simp only [← cancel_epi e₂.hom, ← reassoc_of% comm₂, Iso.hom_inv_id,
      Iso.hom_inv_id_assoc, comp_id]
  · exact
    { m₁ := L.map H.m₁
      m₃ := L.map H.m₃
      comm₁ := by simpa using L.congr_map H.comm₁
      comm₂ := by simpa using L.congr_map H.comm₂ =≫ (L.commShiftIso 1).hom.app Y₁
      comm₃ := by simpa using L.congr_map H.comm₃
      comm₄ := by simpa using L.congr_map H.comm₄ =≫ (L.commShiftIso 1).hom.app Y₂
      mem := isomorphic_distinguished _ (L.map_distinguished _ H.mem) _
        (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp) (by simp) (by simp)) }

lemma isTriangulated [Pretriangulated D] [L.IsTriangulated] [IsTriangulated C] :
    IsTriangulated D := by
  have := Localization.essSurj L W
  apply isTriangulated_of_exists_lifting_composable_morphisms L
  intros X₁ X₂ X₃ f g
  obtain ⟨φ₁, hφ₁⟩ := Localization.exists_rightFraction L W
    ((L.objObjPreimageIso X₁).hom ≫ f ≫ (L.objObjPreimageIso X₂).inv)
  obtain ⟨φ₂, hφ₂⟩ := Localization.exists_leftFraction L W
    ((L.objObjPreimageIso X₂).hom ≫ g ≫ (L.objObjPreimageIso X₃).inv)
  refine' ⟨_, _, _, φ₁.f, φ₂.f,
    (Localization.isoOfHom L W φ₁.s φ₁.hs) ≪≫ L.objObjPreimageIso X₁,
    L.objObjPreimageIso X₂,
    (Localization.isoOfHom L W φ₂.s φ₂.hs).symm ≪≫ L.objObjPreimageIso X₃, _, _⟩
  · dsimp
    rw [← cancel_mono (L.objObjPreimageIso X₂).inv, assoc, assoc, assoc, hφ₁,
      Iso.hom_inv_id, comp_id, MorphismProperty.RightFraction.map_s_comp_map]
  · dsimp
    rw [← cancel_mono (L.objObjPreimageIso X₃).inv, assoc, assoc, assoc, hφ₂,
      Iso.hom_inv_id, comp_id, MorphismProperty.LeftFraction.map_eq]

end

noncomputable example : HasShift W.Localization ℤ := inferInstance
noncomputable example : W.Q.CommShift ℤ := inferInstance

variable
  [HasFiniteProducts C]
  [W.IsStableUnderFiniteProducts]
  [W.HasLocalization]

example : HasTerminal W.Localization := inferInstance
example : HasFiniteProducts W.Localization := inferInstance
noncomputable example : PreservesFiniteProducts W.Q := inferInstance

instance : HasZeroObject W.Localization :=
  Limits.hasZeroObject_of_additive_functor W.Q

instance : HasZeroObject W.Localization' :=
  Limits.hasZeroObject_of_additive_functor W.Q'

noncomputable instance (n : ℤ) :
    PreservesFiniteProducts (shiftFunctor (MorphismProperty.Localization W) n) := by
  constructor
  intros
  infer_instance

noncomputable instance (n : ℤ) :
    PreservesFiniteProducts (shiftFunctor (MorphismProperty.Localization' W) n) := by
  constructor
  intros
  infer_instance

instance (n : ℤ) : (shiftFunctor W.Localization n).Additive :=
  Functor.additive_of_preserves_finite_products _

instance (n : ℤ) : (shiftFunctor W.Localization' n).Additive :=
  Functor.additive_of_preserves_finite_products _

noncomputable instance : Pretriangulated W.Localization := pretriangulated W.Q W
noncomputable instance : Pretriangulated W.Localization' := pretriangulated W.Q' W
noncomputable instance : W.Q.IsTriangulated := isTriangulated_functor W.Q W
noncomputable instance : W.Q'.IsTriangulated := isTriangulated_functor W.Q' W

instance : EssSurj W.Q.mapArrow := essSurj_mapArrow W.Q W
instance : EssSurj W.Q'.mapArrow := essSurj_mapArrow W.Q' W

noncomputable instance [IsTriangulated C] : IsTriangulated W.Localization := isTriangulated W.Q W
noncomputable instance [IsTriangulated C] : IsTriangulated W.Localization' := isTriangulated W.Q' W

end

section

variable {C D : Type _} [Category C] [Category D] [HasZeroObject C] [HasZeroObject D]
  [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [EssSurj L.mapArrow]
  [L.CommShift ℤ] [L.IsTriangulated]

lemma distTriang_iff (T : Triangle D) :
    (T ∈ distTriang D) ↔ T ∈ L.essImageDistTriang := by
  constructor
  · intro hT
    let f := L.mapArrow.objPreimage T.mor₁
    obtain ⟨Z, g : f.right ⟶ Z, h : Z ⟶ f.left⟦(1 : ℤ)⟧, mem⟩ :=
      Pretriangulated.distinguished_cocone_triangle f.hom
    exact ⟨_, (exists_iso_of_arrow_iso T _ hT (L.map_distinguished _ mem)
      (L.mapArrow.objObjPreimageIso T.mor₁).symm).choose, mem⟩
  · rintro ⟨T₀, e, hT₀⟩
    exact isomorphic_distinguished _ (L.map_distinguished _ hT₀) _ e
=======
    letI : Pretriangulated D := pretriangulated L W; L.IsTriangulated :=
    letI : Pretriangulated D := pretriangulated L W; ⟨fun T hT => ⟨T, Iso.refl _, hT⟩⟩

lemma essSurj_mapArrow : EssSurj L.mapArrow :=
  essSurj_mapArrow_of_hasLeftCalculusofFractions L W

lemma isTriangulated [W.HasRightCalculusOfFractions] [Pretriangulated D]
    [L.IsTriangulated] [IsTriangulated C] :
    IsTriangulated D := by
  have := essSurj_mapComposableArrows_two L W
  exact isTriangulated_of_essSurj_mapComposableArrows_two L

instance (n : ℤ) : (shiftFunctor (W.Localization) n).Additive := by
  rw [Localization.functor_additive_iff W.Q W]
  exact Functor.additive_of_iso (W.Q.commShiftIso n)

instance : Pretriangulated W.Localization := pretriangulated W.Q W

section

variable [W.HasLocalization]

instance (n : ℤ) : (shiftFunctor (W.Localization') n).Additive := by
  rw [Localization.functor_additive_iff W.Q' W]
  exact Functor.additive_of_iso (W.Q'.commShiftIso n)

instance : Pretriangulated W.Localization' := pretriangulated W.Q' W
>>>>>>> origin/derived-category

end

end Localization

end Triangulated

end CategoryTheory
