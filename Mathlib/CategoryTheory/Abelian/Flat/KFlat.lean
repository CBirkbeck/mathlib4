/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.BifunctorColimits
import Mathlib.Algebra.Homology.HomotopyCategory.Monoidal
import Mathlib.Algebra.Homology.HomotopyCategory.Devissage
import Mathlib.Algebra.Homology.LeftResolutions.CochainComplex
import Mathlib.Algebra.Homology.LeftResolutions.DerivabilityStructure
import Mathlib.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.KFlat

/-!
# Flat objects and K-flat complexes

-/

open CategoryTheory MonoidalCategory Limits Opposite ZeroObject

section

@[simps obj]
def Antitone.functor {α β : Type*} [Preorder α] [Preorder β]
    {f : α → β} (hf : Antitone f) :
    αᵒᵖ ⥤ β where
  obj a := f a.unop
  map φ := homOfLE (hf (leOfHom φ.unop))

lemma Int.antitone_neg : Antitone (fun (n : ℤ) ↦ -n) := fun _ _ _ ↦ by dsimp; omega

@[simps]
def Int.opEquivalence : ℤᵒᵖ ≌ ℤ where
  functor := Int.antitone_neg.functor
  inverse := Int.antitone_neg.functor.rightOp
  unitIso := NatIso.ofComponents (fun n ↦ eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun n ↦ eqToIso (by simp))

end

universe v u

variable (A : Type u) [Category.{v} A] [Abelian A]
  [MonoidalCategory A] [MonoidalPreadditive A]
  [∀ (j : ℤ), HasColimitsOfShape
    (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j})) A]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

namespace CochainComplex

open HomologicalComplex

abbrev KFlat := (quasiIso A (.up ℤ)).KFlat
abbrev ιKFlat : KFlat A ⥤ CochainComplex A ℤ := MorphismProperty.ιKFlat _

variable {A}

lemma kFlat_iff_preservesQuasiIso (K : CochainComplex A ℤ) :
    (quasiIso A (.up ℤ)).kFlat K ↔
      preservesQuasiIso (tensorLeft K) ∧ preservesQuasiIso (tensorRight K) := Iff.rfl

instance : (quasiIso A (.up ℤ)).kFlat.ContainsZero where
  exists_zero := ⟨_, isZero_zero _, by
    rw [kFlat_iff_preservesQuasiIso]
    constructor
    · apply ObjectProperty.prop_of_isZero
      rw [IsZero.iff_id_eq_zero]
      ext K : 2
      dsimp
      rw [← tensor_id, id_zero, MonoidalPreadditive.zero_tensor]
    · apply ObjectProperty.prop_of_isZero
      rw [IsZero.iff_id_eq_zero]
      ext K : 2
      dsimp
      rw [← tensor_id, id_zero, MonoidalPreadditive.tensor_zero]⟩

instance : (quasiIso A (.up ℤ)).kFlat.IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K hK ↦ by
    rw [ObjectProperty.prop_shift_iff, kFlat_iff_preservesQuasiIso]
    constructor
    · exact (preservesQuasiIso.prop_iff_of_iso
        (bifunctorMapHomologicalComplexObjShiftIso (curriedTensor A) K n)).2
          (hK.1.comp (preservesQuasiIso_shiftFunctor A n))
    · exact (preservesQuasiIso.prop_iff_of_iso
        (bifunctorMapHomologicalComplexFlipObjShiftIso (curriedTensor A) K n)).2
          (hK.2.comp (preservesQuasiIso_shiftFunctor A n))⟩

lemma kFlat_shift_iff (K : CochainComplex A ℤ) (n : ℤ) :
    (quasiIso A (.up ℤ)).kFlat (K⟦n⟧) ↔ (quasiIso A (.up ℤ)).kFlat K := by
  apply ObjectProperty.prop_shift_iff_of_isStableUnderShift

variable (A) in
lemma closedUnderColimitsOfShape_kFlat (J : Type*) [Category J]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A]
    [∀ (X : A), PreservesColimitsOfShape J ((curriedTensor A).flip.obj X)]
    [∀ (X : A), PreservesColimitsOfShape J ((curriedTensor A).obj X)] :
    ClosedUnderColimitsOfShape J (quasiIso A (.up ℤ)).kFlat := by
  intro F c hc hF
  rw [kFlat_iff_preservesQuasiIso]
  have hJ := isStableUnderColimitsOfShape_preservesQuasiIso A A (.up ℤ) (.up ℤ) J
  constructor
  · have : PreservesColimitsOfShape J (curriedTensor (CochainComplex A ℤ)) :=
      inferInstanceAs (PreservesColimitsOfShape _
        (Functor.bifunctorMapHomologicalComplex _ _ _ _))
    exact hJ (isColimitOfPreserves (curriedTensor _) hc) (fun j ↦ (hF j).1)
  · have : PreservesColimitsOfShape J (curriedTensor (CochainComplex A ℤ)).flip :=
      inferInstanceAs (PreservesColimitsOfShape _
        (Functor.bifunctorMapHomologicalComplex _ _ _ _).flip)
    exact hJ (isColimitOfPreserves (curriedTensor _).flip hc) (fun j ↦ (hF j).2)

end CochainComplex

namespace HomotopyCategory

variable {A}

lemma kFlat_iff_preservesQuasiIso (K : HomotopyCategory A (.up ℤ)) :
    (quasiIso A (.up ℤ)).kFlat K ↔
      preservesQuasiIso (tensorLeft K) ∧ preservesQuasiIso (tensorRight K) := Iff.rfl

lemma kFlat_quotient_obj_iff (K : CochainComplex A ℤ) :
    (quasiIso A (.up ℤ)).kFlat ((quotient _ _).obj K) ↔
      (HomologicalComplex.quasiIso A (.up ℤ)).kFlat K := by
  rw [kFlat_iff_preservesQuasiIso, CochainComplex.kFlat_iff_preservesQuasiIso]
  apply and_congr <;> exact Functor.preservesQuasiIso_iff_of_factors (Iso.refl _)

instance : (quasiIso A (.up ℤ)).kFlat.ContainsZero where
  exists_zero := ⟨(quotient _ _).obj 0, Functor.map_isZero _ (isZero_zero _), by
    rw [kFlat_quotient_obj_iff]
    exact ObjectProperty.prop_zero _⟩

instance : (quasiIso A (.up ℤ)).kFlat.IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K hK ↦ by
    obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
    rw [kFlat_quotient_obj_iff] at hK
    rw [ObjectProperty.prop_shift_iff]
    refine ((quasiIso A (ComplexShape.up ℤ)).kFlat.prop_iff_of_iso
      (((quotient A (.up ℤ)).commShiftIso n).app K)).1 ?_
    dsimp
    rw [kFlat_quotient_obj_iff]
    exact (HomologicalComplex.quasiIso A (.up ℤ)).kFlat.le_shift n _ hK⟩

end HomotopyCategory

namespace CochainComplex

variable {A}

open HomologicalComplex

lemma kFlat_single_obj_iff_flat (X : A) (n : ℤ) :
    (quasiIso A (.up ℤ)).kFlat ((single _ _ n).obj X) ↔ ObjectProperty.flat X := by
  trans (quasiIso A (.up ℤ)).kFlat ((single _ _ 0).obj X)
  · rw [← kFlat_shift_iff ((single _ _ 0).obj X) (-n)]
    exact ((quasiIso A (ComplexShape.up ℤ)).kFlat.prop_iff_of_iso
      (((CochainComplex.singleFunctors A).shiftIso (-n) n 0 (by simp)).app X).symm)
  · simp only [kFlat_iff_preservesQuasiIso, ObjectProperty.flat,
      Functor.exactFunctor_iff_preservesQuasiIso _ (.up ℤ) (i₀ := 0) rfl (by simp)]
    apply and_congr
    · exact preservesQuasiIso.prop_iff_of_iso
        (bifunctorMapHomologicalComplexObjSingleIso (curriedTensor A) X)
    · exact preservesQuasiIso.prop_iff_of_iso
        (bifunctorMapHomologicalComplexFlipObjSingleIso (curriedTensor A) X)

instance : (ObjectProperty.flat (A := A)).ContainsZero where
  exists_zero := ⟨0, isZero_zero A, by
    rw [← kFlat_single_obj_iff_flat _ 0]
    apply ObjectProperty.prop_of_isZero
    apply Functor.map_isZero
    apply Limits.isZero_zero⟩

-- TODO: prove it
variable [(HomotopyCategory.quasiIso A (.up ℤ)).kFlat.IsTriangulatedClosed₂]

instance : (HomotopyCategory.quasiIso A (.up ℤ)).kFlat.IsTriangulated where

lemma kFlat_of_bounded_of_flat (K : CochainComplex A ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hK : ∀ n, ObjectProperty.flat (K.X n)) :
    (quasiIso A (.up ℤ)).kFlat K := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff]
  apply HomotopyCategory.mem_subcategory_of_strictly_bounded _ K a b
  intro n _ _
  replace hK := hK n
  rw [← kFlat_single_obj_iff_flat _ 0,
    ← HomotopyCategory.kFlat_quotient_obj_iff] at hK
  exact ObjectProperty.prop_of_iso _
    ((HomotopyCategory.singleFunctorPostcompQuotientIso A 0).symm.app (K.X n)) hK

section

variable (K : CochainComplex A ℤ)

@[simps]
noncomputable def coconeStupidFiltrationGE :
    Cocone K.stupidFiltrationGE where
  pt := K
  ι := { app n := K.ιStupidTrunc _ }

noncomputable def isColimitCoconeStupidFiltrationGE :
    IsColimit K.coconeStupidFiltrationGE :=
  HomologicalComplex.isColimitOfEval _ _ (fun n ↦ by
    apply isColimitOfIsEventuallyConstant _ (op n)
    rintro ⟨j⟩ ⟨h⟩
    obtain ⟨i, rfl⟩ := Int.le.dest (leOfHom h)
    exact isIso_ιStupidTrunc_f _ _ rfl)

variable [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]

lemma kFlat_of_isStrictlyLE_of_flat (b : ℤ) [K.IsStrictlyLE b]
    [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
    (hK : ∀ n, ObjectProperty.flat (K.X n)) :
    (quasiIso A (.up ℤ)).kFlat K := by
  apply (closedUnderColimitsOfShape_kFlat A ℤ)
    (K.isColimitCoconeStupidFiltrationGE.whiskerEquivalence
      Int.opEquivalence.symm)
  intro i
  apply kFlat_of_bounded_of_flat (K.stupidTrunc (ComplexShape.embeddingUpIntGE (-i))) (-i) b
  intro n
  by_cases hn : -i ≤ n
  · obtain ⟨k, hk⟩ := Int.le.dest hn
    let φ := (ιStupidTrunc K (ComplexShape.embeddingUpIntGE (-i))).f n
    have : IsIso φ := isIso_ιStupidTrunc_f K _ (i := k) (by dsimp; omega)
    exact ObjectProperty.prop_of_iso _ (asIso φ).symm (hK n)
  · apply ObjectProperty.prop_of_isZero
    apply isZero_stupidTrunc_X K (ComplexShape.embeddingUpIntGE (-i)) n
    intro
    dsimp
    omega

variable (A) in
lemma cochainComplexMinus_flat_le_kFlat
    [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A] :
    ObjectProperty.flat.cochainComplexMinus ≤ (quasiIso A (.up ℤ)).kFlat := by
  rintro K ⟨hK, n, h₂⟩
  exact kFlat_of_isStrictlyLE_of_flat K n hK

end

end CochainComplex

namespace CategoryTheory.Abelian

variable {A} {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasFiniteCoproducts C]
  [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
  {ι : C ⥤ A} [ι.Full] [ι.Faithful] [ι.Additive]
  (Λ : LeftResolutions ι) [Λ.F.PreservesZeroMorphisms]
  (hι : ι.essImage ≤ ObjectProperty.flat)

-- TODO: prove it
variable [(HomotopyCategory.quasiIso A (.up ℤ)).kFlat.IsTriangulatedClosed₂]
variable [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]

namespace LeftResolutions

noncomputable def colimitOfShapeFlatResolutionFunctorObj (K : CochainComplex A ℤ) :
    ObjectProperty.flat.cochainComplexMinus.ColimitOfShape ℤ (Λ.resolutionFunctor.obj K) :=
  (Λ.colimitOfShapeResolutionFunctorObj K).ofLE
    (ObjectProperty.monotone_cochainComplexMinus hι)

include hι in
lemma kFlat_resolutionFunctor_obj (K : CochainComplex A ℤ) :
    (HomologicalComplex.quasiIso A (.up ℤ)).kFlat (Λ.resolutionFunctor.obj K) := by
  let e := (Λ.colimitOfShapeResolutionFunctorObj K).ofLE
    ((ObjectProperty.monotone_cochainComplexMinus hι).trans
      (CochainComplex.cochainComplexMinus_flat_le_kFlat A))
  exact CochainComplex.closedUnderColimitsOfShape_kFlat A ℤ e.isColimit e.hF

noncomputable def kFlatResolutionFunctor : CochainComplex A ℤ ⥤ CochainComplex.KFlat A :=
  ObjectProperty.lift _ Λ.resolutionFunctor (Λ.kFlat_resolutionFunctor_obj hι)

noncomputable def kFlatResolutionNatTrans :
    Λ.kFlatResolutionFunctor hι ⋙ CochainComplex.ιKFlat A ⟶ 𝟭 _ :=
  Λ.resolutionNatTrans

instance (K : CochainComplex A ℤ) : QuasiIso ((Λ.kFlatResolutionNatTrans hι).app K) := by
  dsimp [kFlatResolutionNatTrans]
  infer_instance

include Λ hι

lemma cochainComplex_kFlat_isLeftDerivabilityStructure :
    (HomologicalComplex.quasiIso A (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure :=
  HomologicalComplex.isLeftDerivabilityStructure_of_functorial_left_resolutions _ rfl
    (Λ.kFlatResolutionNatTrans hι)

/-lemma homotopyCategory_kFlat_isLeftDerivabilityStructure :
    (HomotopyCategory.quasiIso A (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure :=
  sorry-/

end LeftResolutions

end CategoryTheory.Abelian
