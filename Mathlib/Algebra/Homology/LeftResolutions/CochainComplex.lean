/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.LeftResolutions.CochainComplexMinus
import Mathlib.Algebra.Homology.Embedding.CochainComplexTrunc
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Resolutions of unbounded complexes

-/

open CategoryTheory Limits

namespace CochainComplex

variable {A : Type*} [Category A] [Abelian A]
  [HasColimitsOfShape ℤ A]
  (L : Minus A ⥤ CochainComplex A ℤ)

noncomputable def leftResolution : CochainComplex A ℤ ⥤ CochainComplex A ℤ :=
  filtrationLEMinusFunctor A ⋙ (whiskeringRight _ _ _).obj L ⋙ colim

variable {L} (α : L ⟶ Minus.ι _)

noncomputable def leftResolutionπ :
    leftResolution L ⟶ 𝟭 _ :=
  whiskerLeft _ (whiskerRight ((whiskeringRight _ _ _).map α) _) ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (filtrationLEMinusFunctorCompWhiskeringRightObjιIso A).hom _ ≫
    (filtrationLEFunctorCompColimIso A).hom

/-instance quasiIso_leftResolutionπ_app [∀ K, QuasiIso (α.app K)] (K : CochainComplex A ℤ) :
    QuasiIso ((leftResolutionπ α).app K) := by
  have H : (HomologicalComplex.quasiIso A (.up ℤ)).IsStableUnderColimitsOfShape ℤ := by
    sorry
  dsimp only [leftResolutionπ]
  apply (config := { allowSynthFailures := true } ) quasiIso_comp
  simp only [Functor.comp_obj, filtrationLEMinusFunctor_obj, whiskeringRight_obj_obj, colim_obj,
    whiskerLeft_app, whiskerRight_app, colim_map]
  apply H.colimMap
  intro n
  dsimp
  simp only [HomologicalComplex.mem_quasiIso_iff]
  infer_instance-/

end CochainComplex
