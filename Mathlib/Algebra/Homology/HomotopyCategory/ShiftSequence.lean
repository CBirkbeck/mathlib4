import Mathlib.CategoryTheory.Shift.InducedShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

open CategoryTheory Category Preadditive

variable (C : Type _) [Category C] [Preadditive C]

namespace CochainComplex

open HomologicalComplex

attribute [local simp] XIsoOfEq_hom_naturality zsmul_comp comp_zsmul smul_smul

@[simps!]
def shiftEval (n i i' : ℤ) (hi : n + i = i') :
    (CategoryTheory.shiftFunctor (CochainComplex C ℤ) n) ⋙
      HomologicalComplex.eval C (ComplexShape.up ℤ) i ≅
      HomologicalComplex.eval C (ComplexShape.up ℤ) i' :=
  NatIso.ofComponents
    (fun K => K.XIsoOfEq (by dsimp ; rw [← hi, add_comm i])) (fun _ => by
      dsimp
      simp only [XIsoOfEq_hom_naturality])

@[simps!]
def shiftShortComplexFunctor' (n i j k i' j' k' : ℤ)
    (hi : n + i = i') (hj : n + j = j') (hk : n + k = k') :
  (CategoryTheory.shiftFunctor (CochainComplex C ℤ) n) ⋙ shortComplexFunctor' C _ i j k ≅
    shortComplexFunctor' C _ i' j' k' :=
  NatIso.ofComponents (fun K => ShortComplex.isoMk
    (mulIso ((-1 : Units ℤ)^n) ((shiftEval C n i i' hi).app K))
    ((shiftEval C n j j' hj).app K) (mulIso ((-1 : Units ℤ)^n) ((shiftEval C n k k' hk).app K))
    (by
      dsimp
      simp only [zsmul_comp, XIsoOfEq_hom_comp_d, d_comp_XIsoOfEq_hom])
    (by
      dsimp
      simp only [XIsoOfEq_hom_comp_d, comp_zsmul, zsmul_comp,
        d_comp_XIsoOfEq_hom, smul_smul, mul_ε_self, one_smul]))
      (fun _ => by
        ext <;> dsimp <;> simp only [comp_zsmul, XIsoOfEq_hom_naturality, zsmul_comp])

@[simps!]
noncomputable def shiftShortComplexFunctorIso (n i i' : ℤ) (hi : n + i = i') :
  shiftFunctor C n ⋙ shortComplexFunctor C _ i ≅ shortComplexFunctor C _ i' :=
  shiftShortComplexFunctor' C n _ i _ _ i' _ (by simp ; linarith) hi (by simp ; linarith)

variable {C}

lemma shiftShortComplexFunctorIso_zero_add_hom_app (a : ℤ) (K : CochainComplex C ℤ) :
  (shiftShortComplexFunctorIso C 0 a a (zero_add a)).hom.app K =
    (shortComplexFunctor C (ComplexShape.up ℤ) a).map
      ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K) := by
  ext <;> dsimp <;> simp [one_smul, shiftFunctorZero_hom_app_f]

lemma shiftShortComplexFunctorIso_add'_hom_app
    (n m mn : ℤ) (hmn : m + n = mn) (a a' a'' : ℤ) (ha' : n + a = a') (ha'' : m + a' = a'')
    (K : CochainComplex C ℤ) :
    (shiftShortComplexFunctorIso C mn a a'' (by rw [← ha'', ← ha', ← add_assoc, hmn])).hom.app K =
      (shortComplexFunctor C (ComplexShape.up ℤ) a).map
        ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) m n mn hmn).hom.app K) ≫ (shiftShortComplexFunctorIso C n a a' ha').hom.app (K⟦m⟧) ≫
        (shiftShortComplexFunctorIso C m a' a'' ha'' ).hom.app K := by
  ext <;> dsimp <;>
    simp only [comp_zsmul, zsmul_comp, smul_smul,
      shiftFunctorAdd'_hom_app_f', ← hmn, ε_add,
      XIsoOfEq_shift, XIsoOfEq_hom_comp_XIsoOfEq_hom]

variable [CategoryWithHomology C]

namespace ShiftSequence

variable (C)

noncomputable def shiftIso (n a a' : ℤ) (ha' : n + a = a') :
  (CategoryTheory.shiftFunctor _ n) ⋙ homologyFunctor C (ComplexShape.up ℤ) a ≅
    homologyFunctor C (ComplexShape.up ℤ) a' :=
  isoWhiskerLeft _ (homologyFunctorIso C (ComplexShape.up ℤ) a) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (shiftShortComplexFunctorIso C n a a' ha') (ShortComplex.homologyFunctor C) ≪≫
    (homologyFunctorIso C (ComplexShape.up ℤ) a').symm

variable {C}

lemma shiftIso_hom_app (n a a' : ℤ) (ha' : n + a = a') (K : CochainComplex C ℤ):
    (shiftIso C n a a' ha').hom.app K =
      ShortComplex.homologyMap ((shiftShortComplexFunctorIso C n a a' ha').hom.app K) := by
  dsimp [shiftIso]
  erw [id_comp, id_comp, comp_id]

lemma shiftIso_inv_app (n a a' : ℤ) (ha' : n + a = a') (K : CochainComplex C ℤ):
    (shiftIso C n a a' ha').inv.app K =
      ShortComplex.homologyMap ((shiftShortComplexFunctorIso C n a a' ha').inv.app K) := by
  dsimp [shiftIso]
  erw [id_comp, comp_id, comp_id]

end ShiftSequence

noncomputable instance :
    (homologyFunctor C (ComplexShape.up ℤ) 0).ShiftSequence ℤ where
  sequence n := homologyFunctor C (ComplexShape.up ℤ) n
  isoZero := Iso.refl _
  shiftIso n a a' ha' := ShiftSequence.shiftIso C n a a' ha'
  shiftIso_zero a := by
    ext K
    dsimp [homologyMap]
    simp only [ShiftSequence.shiftIso_hom_app, comp_id,
      shiftShortComplexFunctorIso_zero_add_hom_app]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext K
    dsimp [homologyMap]
    simp only [ShiftSequence.shiftIso_hom_app, id_comp,
      ← ShortComplex.homologyMap_comp, shiftFunctorAdd'_eq_shiftFunctorAdd,
      shiftShortComplexFunctorIso_add'_hom_app n m _ rfl a a' a'' ha' ha'' K]

end CochainComplex

namespace HomotopyCategory

variable [CategoryWithHomology C]

noncomputable instance :
    (homologyFunctor C (ComplexShape.up ℤ) 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.induced (homologyFunctorFactors C (ComplexShape.up ℤ) 0) ℤ
    (homologyFunctor C (ComplexShape.up ℤ))
    (homologyFunctorFactors C (ComplexShape.up ℤ))
    ⟨⟨Quotient.full_whiskeringLeft_quotient_functor _ _⟩,
      Quotient.faithful_whiskeringLeft_quotient_functor _ _⟩

lemma homologyShiftIso_hom_app (n a a' : ℤ) (ha' : n + a = a') (K : CochainComplex C ℤ) :
  ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso n a a' ha').hom.app
    ((quotient _ _).obj K) =
      (homologyFunctor _ _ a).map
        (((quotient _ _).commShiftIso n).inv.app K) ≫
        (homologyFunctorFactors _ _ a).hom.app (K⟦n⟧) ≫
        ((HomologicalComplex.homologyFunctor _ _ 0).shiftIso n a a' ha').hom.app K ≫
        (homologyFunctorFactors _ _ a').inv.app K := by
  apply Functor.ShiftSequence.induced_shiftIso_hom_app_obj

end HomotopyCategory
