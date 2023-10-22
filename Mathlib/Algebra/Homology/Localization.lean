import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.CategoryTheory.Localization.HasLocalization
import Mathlib.CategoryTheory.Localization.Composition

open CategoryTheory Limits

section

variable (C : Type*) [Category C] {ι : Type*} (c : ComplexShape ι) [HasZeroMorphisms C]
  [CategoryWithHomology C] [(HomologicalComplex.qis C c).HasLocalization]

abbrev HomologicalComplexUpToQis := (HomologicalComplex.qis C c).Localization'

variable {C c}

abbrev HomologicalComplexUpToQis.Q :
    HomologicalComplex C c ⥤ HomologicalComplexUpToQis C c :=
  (HomologicalComplex.qis C c).Q'

variable (C c)

lemma HomologicalComplex.homologyFunctor_inverts_qis (i : ι) :
    (qis C c).IsInvertedBy (homologyFunctor C c i) := fun _ _ _ hf => hf i

namespace HomologicalComplexUpToQis

noncomputable def homologyFunctor (i : ι) : HomologicalComplexUpToQis C c ⥤ C :=
  Localization.lift _ (HomologicalComplex.homologyFunctor_inverts_qis C c i) Q

noncomputable def homologyFunctorFactors (i : ι) :
    Q ⋙ homologyFunctor C c i ≅ HomologicalComplex.homologyFunctor C c i :=
  Localization.fac _ (HomologicalComplex.homologyFunctor_inverts_qis C c i) Q

variable {C c}

lemma isIso_Q_map_iff {K L : HomologicalComplex C c} (f : K ⟶ L) :
    IsIso (Q.map f) ↔ HomologicalComplex.qis C c f := by
  constructor
  · intro _ i
    refine' (NatIso.isIso_map_iff (homologyFunctorFactors C c i) f).1 _
    dsimp
    infer_instance
  · intro h
    exact Localization.inverts Q (HomologicalComplex.qis C c) _ h

end HomologicalComplexUpToQis

end

class ComplexShape.QFactorsThroughHomotopy {ι : Type*} (c : ComplexShape ι)
    (C : Type*) [Category C] [Preadditive C]
    [CategoryWithHomology C] [(HomologicalComplex.qis C c).HasLocalization] : Prop where
  factors {K L : HomologicalComplex C c} {f g : K ⟶ L} (h : Homotopy f g) :
    HomologicalComplexUpToQis.Q.map f = HomologicalComplexUpToQis.Q.map g

section

variable (C : Type*) [Category C] {ι : Type*} (c : ComplexShape ι) [Preadditive C]
  [DecidableRel c.Rel]
  [CategoryWithHomology C] [(HomologicalComplex.qis C c).HasLocalization]
  [c.QFactorsThroughHomotopy C]

lemma HomologicalComplexUpToQis.Q_inverts_homotopyEquivalences :
    (HomologicalComplex.homotopyEquivalences C c).IsInvertedBy
      HomologicalComplexUpToQis.Q :=
  MorphismProperty.IsInvertedBy.of_subset _ _ _
    (Localization.inverts Q (HomologicalComplex.qis C c))
    (HomologicalComplex.homotopyEquivalences_subset_qis C c)

namespace HomotopyCategory

def qis : MorphismProperty (HomotopyCategory C c) :=
  fun _ _ f => ∀ (i : ι), IsIso ((HomotopyCategory.homologyFunctor C c i).map f)

def respectsIso_qis : (qis C c).RespectsIso := by
  apply MorphismProperty.RespectsIso.of_respects_arrow_iso
  intro f g e hf i
  exact ((MorphismProperty.RespectsIso.isomorphisms C).arrow_mk_iso_iff
    ((homologyFunctor C c i).mapArrow.mapIso e)).1 (hf i)

lemma homologyFunctor_inverts_qis (i : ι) :
    (qis C c).IsInvertedBy (homologyFunctor C c i) := fun _ _ _ hf => hf i

variable {C c}

lemma mem_qis_iff {X Y : HomotopyCategory C c} (f : X ⟶ Y) :
    qis C c f ↔ ∀ (n : ι), IsIso ((homologyFunctor _ _ n).map f) := by
  rfl

lemma quotient_map_mem_qis_iff {K L : HomologicalComplex C c} (f : K ⟶ L) :
    qis C c ((quotient C c).map f) ↔ HomologicalComplex.qis C c f := by
  dsimp [qis, HomologicalComplex.qis]
  have eq := fun (i : ι) => NatIso.isIso_map_iff (homologyFunctorFactors C c i) f
  dsimp at eq
  simp only [eq]

variable (C c)

lemma qis_eq_qis_map_quotient :
    qis C c = (HomologicalComplex.qis C c).map (quotient C c) := by
  ext ⟨K⟩ ⟨L⟩ f
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective f
  constructor
  · intro hf
    rw [quotient_map_mem_qis_iff] at hf
    exact MorphismProperty.map_mem_map _ _ _ hf
  · rintro ⟨K', L', g, h, ⟨e⟩⟩
    rw [← quotient_map_mem_qis_iff] at h
    exact ((respectsIso_qis C c).arrow_mk_iso_iff e).1 h

end HomotopyCategory

namespace HomologicalComplexUpToQis

variable {C c}

def Qh : HomotopyCategory C c ⥤ HomologicalComplexUpToQis C c :=
  CategoryTheory.Quotient.lift _ HomologicalComplexUpToQis.Q (by
    intro K L f g ⟨h⟩
    exact ComplexShape.QFactorsThroughHomotopy.factors h)

variable (C c)

def quotientCompQhIso : HomotopyCategory.quotient C c ⋙ Qh ≅ Q := by
  apply Quotient.lift.isLift

lemma Qh_inverts_qis : (HomotopyCategory.qis C c).IsInvertedBy Qh := by
  rintro ⟨K⟩ ⟨L⟩ φ
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective φ
  rw [HomotopyCategory.quotient_map_mem_qis_iff φ,
    ← HomologicalComplexUpToQis.isIso_Q_map_iff]
  exact (NatIso.isIso_map_iff (quotientCompQhIso C c) φ).2

instance :
    (HomotopyCategory.quotient C c ⋙ Qh).IsLocalization (HomologicalComplex.qis C c) :=
  Functor.IsLocalization.of_iso _ (quotientCompQhIso C c).symm

noncomputable def homologyFunctorFactorsh (i : ι ): Qh ⋙ homologyFunctor C c i ≅
    HomotopyCategory.homologyFunctor C c i :=
  Quotient.natIsoLift _ ((Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (quotientCompQhIso C c) _ ≪≫
    homologyFunctorFactors C c i  ≪≫ (HomotopyCategory.homologyFunctorFactors C c i).symm)

section

variable [(HomotopyCategory.quotient C c).IsLocalization
  (HomologicalComplex.homotopyEquivalences C c)]

-- this shall apply to cochain complexes because of the main result in
-- `Algebra.Homology.HomotopyCategory.Cylinder`
instance : HomologicalComplexUpToQis.Qh.IsLocalization (HomotopyCategory.qis C c) :=
  Functor.IsLocalization.of_comp (HomotopyCategory.quotient C c)
    Qh (HomologicalComplex.homotopyEquivalences C c)
    (HomotopyCategory.qis C c) (HomologicalComplex.qis C c)
    (HomologicalComplex.homotopyEquivalences_subset_qis C c)
    (HomotopyCategory.qis_eq_qis_map_quotient C c)

end

end HomologicalComplexUpToQis

end
