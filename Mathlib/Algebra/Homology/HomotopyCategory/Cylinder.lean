import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Homology.HomologicalComplexLimits

open CategoryTheory Category Limits

variable {C : Type _} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  [HasBinaryBiproducts (CochainComplex C ℤ)]

namespace CochainComplex

instance : HasBinaryBiproducts (CochainComplex C ℤ) := by
  apply HasBinaryBiproducts.of_hasBinaryProducts

open HomComplex HomologicalComplex

variable (K L : CochainComplex C ℤ)

noncomputable def cylinder : CochainComplex C ℤ := mappingCone (biprod.lift (𝟙 K) (-𝟙 K))

namespace cylinder

variable {K L}

noncomputable def inl : K ⟶ cylinder K := biprod.inl ≫ MappingCone.inr _
noncomputable def inr : K ⟶ cylinder K := biprod.inr ≫ MappingCone.inr _

attribute [local simp] sub_eq_add_neg

noncomputable def desc (f₁ f₂ : K ⟶ L) (h : Homotopy f₁ f₂) : cylinder K ⟶ L :=
  MappingCone.desc _ (Cochain.ofHomotopy h) (biprod.desc f₁ f₂) (by simp)

@[reassoc (attr := simp)]
lemma inl_desc (f₁ f₂ : K ⟶ L) (h : Homotopy f₁ f₂) : inl ≫ desc f₁ f₂ h = f₁ := by
  simp only [inl, desc, assoc, MappingCone.inr_desc, biprod.inl_desc]

@[reassoc (attr := simp)]
lemma inr_desc (f₁ f₂ : K ⟶ L) (h : Homotopy f₁ f₂) : inr ≫ desc f₁ f₂ h = f₂ := by
  simp only [inr, desc, assoc, MappingCone.inr_desc, biprod.inr_desc]

@[simp]
noncomputable def π : cylinder K ⟶ K := desc _ _ (Homotopy.refl (𝟙 K))

variable (K)

noncomputable def homotopyEquiv : HomotopyEquiv (cylinder K) K where
  hom := π
  inv := inl
  homotopyHomInvId := MappingCone.descHomotopy _ _ _ 0
    ((Cochain.ofHom biprod.snd).comp (MappingCone.inl _) (zero_add (-1)))
    (by
      dsimp only [π, inl, desc]
      rw [MappingCone.cochain_to_ext_iff _ _ _ _ (neg_add_self 1)]
      simp only [Cochain.ofHom_comp, Cochain.comp_assoc_of_second_is_zero_cochain,
        Cochain.comp_assoc_of_first_is_zero_cochain, MappingCone.inr_fst, Cochain.comp_zero,
        δ_zero, zero_add, Cochain.add_comp, MappingCone.inl_fst, Cochain.comp_id,
        MappingCone.inr_snd, MappingCone.inl_snd]
      erw [Cochain.id_comp, Cochain.id_comp]
      constructor
      . erw [MappingCone.inl_fst, ← Cochain.ofHom_comp, biprod.lift_snd,
          Cochain.ofHom_neg, add_left_neg]
      . erw [MappingCone.inl_snd, MappingCone.ofHom_desc,
          ← Cochain.comp_assoc_of_third_is_zero_cochain,
          MappingCone.inl_descCochain, Cochain.ofHomotopy_refl, Cochain.zero_comp])
    (by
      dsimp only [π, inl, desc]
      rw [MappingCone.cochain_to_ext_iff _ _ _ _ (zero_add 1)]
      simp only [Cochain.ofHomotopy_refl, MappingCone.inr_desc_assoc, Cochain.ofHom_comp,
        Cochain.comp_assoc_of_first_is_zero_cochain, MappingCone.inr_fst, Cochain.comp_zero,
        δ_ofHom_comp, MappingCone.δ_inl, Cochain.add_comp, zero_add,
        MappingCone.inr_snd, Cochain.comp_id]
      erw [Cochain.id_comp, Cochain.id_comp]
      constructor
      . simp only [MappingCone.inr_fst]
      . simp only [MappingCone.inr_snd, ← Cochain.ofHom_comp, ← Cochain.ofHom_add]
        apply congr_arg
        ext1 <;> ext1 <;> simp)
  homotopyInvHomId := Homotopy.ofEq (by simp)

end cylinder

lemma homotopyEquivalences_isInvertedBy_iff {D : Type _} [Category D]
    (F : CochainComplex C ℤ ⥤ D) :
    (homotopyEquivalences C (ComplexShape.up ℤ)).IsInvertedBy F ↔
      ∀ ⦃K L : CochainComplex C ℤ⦄ (f₁ f₂ : K ⟶ L) (_ : Homotopy f₁ f₂), F.map f₁ = F.map f₂ := by
  constructor
  . intros hF K L f₁ f₂ h
    have : IsIso (F.map (cylinder.π : _ ⟶ K)) := hF _ ⟨cylinder.homotopyEquiv K, rfl⟩
    have eq : F.map (cylinder.inl : K ⟶ _) = F.map cylinder.inr := by
      simp only [← cancel_mono (F.map (cylinder.π : _ ⟶ K)), ← F.map_comp, cylinder.π,
        cylinder.inl_desc, cylinder.inr_desc]
    simpa only [← F.map_comp, cylinder.inl_desc, cylinder.inr_desc]
      using eq =≫ F.map (cylinder.desc _ _ h)
  . rintro hF K L _ ⟨e, rfl⟩
    refine' ⟨⟨F.map e.inv, _, _⟩⟩
    . rw [← F.map_comp, hF  _ _ e.homotopyHomInvId, F.map_id]
    . rw [← F.map_comp, hF  _ _ e.homotopyInvHomId, F.map_id]

end CochainComplex

namespace HomotopyCategory

variable (C)

def localization_strict_universal_property (D : Type _) [Category D] :
    Localization.StrictUniversalPropertyFixedTarget (quotient C (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences _ _) D where
  inverts := by
    rw [CochainComplex.homotopyEquivalences_isInvertedBy_iff]
    intro K L f₁ f₂ h
    exact eq_of_homotopy _ _ h
  lift F hF := CategoryTheory.Quotient.lift _ F (fun K L f₁ f₂ ⟨h⟩ => by
    rw [CochainComplex.homotopyEquivalences_isInvertedBy_iff] at hF
    exact hF _ _ h)
  fac F hF := Quotient.lift_spec _ _ _
  uniq F₁ F₂ h := by
    rw [Quotient.lift_unique _ _ _ F₁ rfl, Quotient.lift_unique _ _ _ F₂ h.symm]
    . rfl
    . intro K L f₁ f₂ ⟨h⟩
      dsimp
      rw [eq_of_homotopy _ _ h]

instance IsLocalization :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).IsLocalization
      (HomologicalComplex.homotopyEquivalences _ _) :=
  Functor.IsLocalization.mk' _ _ (localization_strict_universal_property _ _)
  (localization_strict_universal_property _ _)

end HomotopyCategory
