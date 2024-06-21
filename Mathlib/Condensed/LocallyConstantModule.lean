import Mathlib.CategoryTheory.Sites.Discrete
import Mathlib.CategoryTheory.Sites.Coherent.Equivalence
import Mathlib.Condensed.LocallyConstant
import Mathlib.Condensed.Module
import Mathlib.Condensed.Light.Module
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.CategoryTheory.Monad.EquivMon

universe w u

open CategoryTheory LocallyConstant CompHausLike Functor Category Functor Opposite

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

namespace Sheaf

variable {A B : Type*} [Category A] [Category B] (e : C ≌ D) (F : A ⥤ B)
  (J : GrothendieckTopology C) [HasSheafify J A]
  (K : GrothendieckTopology D) [HasSheafify K A]
  [K.PreservesSheafification F] [e.TransportsGrothendieckTopology J K]

lemma transportPreservesSheafification : J.PreservesSheafification F where
  le := by
    sorry
    -- rw [← J.W_inverseImage_whiskeringLeft (G := e.inverse)]

end Sheaf

open Iso

namespace Monad

def transport {F : C ⥤ C} (T : Monad C) (i : (T : C ⥤ C) ≅ F) : Monad C where
  toFunctor := F
  η' := T.η ≫ i.hom
  μ' := (i.inv ◫ i.inv) ≫ T.μ ≫ i.hom
  left_unit' X := by
    simp only [Functor.id_obj, NatTrans.comp_app, comp_obj, NatTrans.hcomp_app, Category.assoc,
      hom_inv_id_app_assoc]
    slice_lhs 1 2 => rw [← T.η.naturality (i.inv.app X), ]
    simp
  right_unit' X := by
    simp only [id_obj, NatTrans.comp_app, Functor.map_comp, comp_obj, NatTrans.hcomp_app,
      Category.assoc, NatTrans.naturality_assoc]
    slice_lhs 2 4 =>
      simp only [← T.map_comp]
    simp
  assoc' X := by
    simp only [comp_obj, NatTrans.comp_app, NatTrans.hcomp_app, Category.assoc, Functor.map_comp,
      NatTrans.naturality_assoc, hom_inv_id_app_assoc, NatIso.cancel_natIso_inv_left]
    slice_lhs 4 5 => rw [← T.map_comp]
    simp only [hom_inv_id_app, Functor.map_id, id_comp]
    slice_lhs 1 2 => rw [← T.map_comp]
    simp only [Functor.map_comp, Category.assoc]
    congr 1
    simp only [← Category.assoc, NatIso.cancel_natIso_hom_right]
    rw [← T.μ.naturality]
    simp [T.assoc X]

end Monad

namespace Comonad

def transport {F : C ⥤ C} (T : Comonad C) (i : (T : C ⥤ C) ≅ F) : Comonad C where
  toFunctor := F
  ε' := i.inv ≫ T.ε
  δ' := i.inv ≫ T.δ ≫ (i.hom ◫ i.hom)
  right_counit' X := by
    simp only [id_obj, comp_obj, NatTrans.comp_app, NatTrans.hcomp_app, Functor.map_comp, assoc]
    slice_lhs 4 5 => rw [← F.map_comp]
    simp only [hom_inv_id_app, Functor.map_id, id_comp, ← i.hom.naturality]
    slice_lhs 2 3 => rw [T.right_counit]
    simp
  coassoc' X := by
    simp only [comp_obj, NatTrans.comp_app, NatTrans.hcomp_app, Functor.map_comp, assoc,
      NatTrans.naturality_assoc, Functor.comp_map, hom_inv_id_app_assoc,
      NatIso.cancel_natIso_inv_left]
    slice_lhs 3 4 => rw [← F.map_comp]
    simp only [hom_inv_id_app, Functor.map_id, id_comp, assoc]
    rw [← i.hom.naturality_assoc, ← T.coassoc_assoc]
    simp only [NatTrans.naturality_assoc]
    congr 3
    simp only [← Functor.map_comp, i.hom.naturality]

end Comonad

lemma NatTrans.id_comm (α β : 𝟭 C ⟶ 𝟭 C) : α ≫ β = β ≫ α := by
  ext X
  exact (α.naturality (β.app X)).symm

namespace Adjunction

variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C)

lemma isIso_unit_of_abstract_iso : IsIso adj.unit := by
  suffices IsIso (adj.unit ≫ i.hom) from IsIso.of_isIso_comp_right adj.unit i.hom
  refine ⟨(adj.toMonad.transport i).μ, ?_, ?_⟩
  · ext X; exact (adj.toMonad.transport i).right_unit X
  · rw [NatTrans.id_comm]; ext X; exact (adj.toMonad.transport i).right_unit X

noncomputable def fullyFaithfulLOfCompIsoId : L.FullyFaithful :=
  haveI := adj.isIso_unit_of_abstract_iso i
  adj.fullyFaithfulLOfIsIsoUnit

variable (j : R ⋙ L ≅ 𝟭 D)

lemma isIso_counit_of_abstract_iso : IsIso adj.counit := by
  suffices IsIso (j.inv ≫ adj.counit) from IsIso.of_isIso_comp_left j.inv adj.counit
  refine ⟨(adj.toComonad.transport j).δ, ?_, ?_⟩
  · rw [NatTrans.id_comm]; ext X; exact (adj.toComonad.transport j).right_counit X
  · ext X; exact (adj.toComonad.transport j).right_counit X

noncomputable def fullyFaithfulROfCompIsoId : R.FullyFaithful :=
  haveI := adj.isIso_counit_of_abstract_iso j
  adj.fullyFaithfulROfIsIsoCounit

end CategoryTheory.Adjunction

attribute [local instance] ConcreteCategory.instFunLike

variable {P : TopCat.{u} → Prop}

namespace Condensed.LocallyConstantModule

variable (R : Type (max u w)) [Ring R]

/--
The functor from the category of `R`-modules to presheaves on `CompHaus` given by locally constant
maps.
-/
@[simps]
def functorToPresheaves : ModuleCat.{max u w} R ⥤ ((CompHausLike.{u} P)ᵒᵖ ⥤ ModuleCat R) where
  obj X := {
    obj := fun ⟨S⟩ ↦ ModuleCat.of R (LocallyConstant S X)
    map := fun f ↦ comapₗ R f.unop }
  map f := { app := fun S ↦ mapₗ R f }

variable [HasExplicitFiniteCoproducts.{0} P] [HasExplicitPullbacks.{u} P]
  (hs : ∀ ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f → Function.Surjective f)

/-- `Condensed.LocallyConstantModule.functorToPresheaves` lands in condensed modules. -/
@[simps]
def functor :
    have := CompHausLike.preregular hs
    ModuleCat R ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (ModuleCat R) where
  obj X := {
    val := (functorToPresheaves.{w, u} R).obj X
    cond := by
      have := CompHausLike.preregular hs
      apply Presheaf.isSheaf_coherent_of_hasPullbacks_of_comp (s :=
        CategoryTheory.forget (ModuleCat R))
      exact ((Condensed.LocallyConstant.functor P hs).obj _).cond }
  map f := ⟨(functorToPresheaves.{w, u} R).map f⟩

end Condensed.LocallyConstantModule

namespace CondensedMod.LocallyConstant

variable (R : Type (u+1)) [Ring R]

abbrev functorToPresheaves : ModuleCat.{u+1} R ⥤ (CompHaus.{u}ᵒᵖ ⥤ ModuleCat R) :=
  Condensed.LocallyConstantModule.functorToPresheaves.{u+1, u} R

abbrev functor : ModuleCat R ⥤ CondensedMod.{u} R :=
  Condensed.LocallyConstantModule.functor.{u+1, u} R
    (fun _ _ _ ↦ ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

noncomputable def functorIsoDiscreteAux' (M : ModuleCat.{u+1} R) :
    M ≅ (ModuleCat.of R (LocallyConstant (CompHaus.of PUnit.{u+1}) M)) where
  hom := constₗ R
  inv := evalₗ R PUnit.unit

noncomputable def functorIsoDiscreteAux (M : ModuleCat R) :
    (Condensed.discrete _).obj M ≅ (Condensed.discrete _).obj
      (ModuleCat.of R (LocallyConstant (CompHaus.of PUnit.{u+1}) M)) :=
  (Condensed.discrete _).mapIso (functorIsoDiscreteAux' R M)

instance (M : ModuleCat R) : IsIso ((Condensed.forget R).map
    ((Condensed.discreteUnderlyingAdj (ModuleCat R)).counit.app
      ((functor R).obj M))) := by
  erw [Sheaf.constantCommuteComposeApp_counit_comp]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ?_
  change Sheaf.IsDiscrete _ _ _
  have : (constantSheaf (coherentTopology CompHaus) (Type (u + 1))).Faithful :=
    inferInstanceAs (Condensed.discrete _).Faithful
  have : (constantSheaf (coherentTopology CompHaus) (Type (u + 1))).Full :=
    inferInstanceAs (Condensed.discrete _).Full
  rw [Sheaf.isDiscrete_iff_mem_essImage]
  change _ ∈ (Condensed.discrete _).essImage
  rw [essImage_eq_of_natIso CondensedSet.LocallyConstant.iso.symm]
  exact obj_mem_essImage CondensedSet.LocallyConstant.functor M

noncomputable def functorIsoDiscrete_components (M : ModuleCat R) :
    (Condensed.discrete _).obj M ≅ (functor R).obj M := by
  have : (Condensed.forget R).ReflectsIsomorphisms :=
    inferInstanceAs (sheafCompose _ _).ReflectsIsomorphisms
  refine (functorIsoDiscreteAux R M) ≪≫ (@asIso _ _ _ _ ?_ ?_)
  · exact (Condensed.discreteUnderlyingAdj (ModuleCat R)).counit.app ((functor R).obj M)
  · apply this.reflects

open Condensed.LocallyConstantModule in
noncomputable def functorIsoDiscrete : functor R ≅ Condensed.discrete _ := by
  refine NatIso.ofComponents (fun M ↦ (functorIsoDiscrete_components R M).symm) ?_
  intro M N f
  dsimp
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  dsimp [functorIsoDiscrete_components]
  rw [Category.assoc, ← Iso.eq_inv_comp]
  erw [← (Condensed.discreteUnderlyingAdj (ModuleCat R)).counit.naturality]
  change _ ≫ ((Condensed.discreteUnderlyingAdj (ModuleCat R)).counit.app (((functor R).obj N))) = _
  simp only [← assoc]
  congr 1
  rw [← Iso.comp_inv_eq]
  apply Sheaf.hom_ext
  simp only [comp_obj, Condensed.underlying_obj, functor_obj_val, functorToPresheaves_obj_obj,
    coe_of, Condensed.discrete_obj, Functor.comp_map, Condensed.underlying_map,
    functorToPresheaves_map_app, Condensed.discrete_map, functorIsoDiscreteAux, mapIso_inv,
    ← Functor.map_comp]
  rfl

noncomputable def compIsoId :
    (functor R) ⋙ (Condensed.underlying (ModuleCat R)) ≅ 𝟭 _ :=
  NatIso.ofComponents fun M ↦ (functorIsoDiscreteAux' R _).symm

noncomputable def adjunction : functor R ⊣ Condensed.underlying (ModuleCat R) :=
  Adjunction.ofNatIsoLeft (Condensed.discreteUnderlyingAdj _) (functorIsoDiscrete R).symm

noncomputable def fullyFaithfulFunctor :
    (functor R).FullyFaithful := (adjunction R).fullyFaithfulLOfCompIsoId (compIsoId R)

end CondensedMod.LocallyConstant

namespace LightCondMod

variable (R : Type u) [Ring R]

abbrev LocallyConstant.functor : ModuleCat R ⥤ LightCondMod.{u} R :=
  Condensed.LocallyConstantModule.functor.{u, u} R
    (fun _ _ _ ↦ (LightProfinite.effectiveEpi_iff_surjective _).mp)

abbrev functorToPresheaves : ModuleCat.{u} R ⥤ (LightProfinite.{u}ᵒᵖ ⥤ ModuleCat R) :=
  Condensed.LocallyConstantModule.functorToPresheaves.{u, u} R

abbrev functor : ModuleCat R ⥤ LightCondMod.{u} R :=
  Condensed.LocallyConstantModule.functor.{u, u} R
    (fun _ _ _ ↦ (LightProfinite.effectiveEpi_iff_surjective _).mp)

noncomputable def functorIsoDiscreteAux' (M : ModuleCat.{u} R) :
    M ≅ (ModuleCat.of R (LocallyConstant (LightProfinite.of PUnit.{u+1}) M)) where
  hom := constₗ R
  inv := evalₗ R PUnit.unit

noncomputable def functorIsoDiscreteAux (M : ModuleCat R) :
    (LightCondensed.discrete _).obj M ≅ (LightCondensed.discrete _).obj
      (ModuleCat.of R (LocallyConstant (LightProfinite.of PUnit.{u+1}) M)) :=
  (LightCondensed.discrete _).mapIso (functorIsoDiscreteAux' R M)

instance (J : GrothendieckTopology (SmallModel LightProfinite.{u})) : HasSheafify J (ModuleCat R) :=
  inferInstance

instance : HasSheafify (coherentTopology LightProfinite) (ModuleCat R) :=
  inferInstance

instance : (coherentTopology LightProfinite).PreservesSheafification
    (CategoryTheory.forget (ModuleCat R)) := sorry

instance (M : ModuleCat R) : IsIso ((LightCondensed.forget R).map
    ((LightCondensed.discreteUnderlyingAdj (ModuleCat R)).counit.app
      ((functor R).obj M))) := by
  erw [Sheaf.constantCommuteComposeApp_counit_comp]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ?_
  change Sheaf.IsDiscrete _ _ _
  have : (constantSheaf (coherentTopology LightProfinite) (Type u)).Faithful :=
    inferInstanceAs (LightCondensed.discrete _).Faithful
  have : (constantSheaf (coherentTopology LightProfinite) (Type u)).Full :=
    inferInstanceAs (LightCondensed.discrete _).Full
  rw [Sheaf.isDiscrete_iff_mem_essImage]
  change _ ∈ (LightCondensed.discrete _).essImage
  rw [essImage_eq_of_natIso LightCondSet.LocallyConstant.iso.symm]
  exact obj_mem_essImage LightCondSet.LocallyConstant.functor M

noncomputable def functorIsoDiscrete_components (M : ModuleCat R) :
    (LightCondensed.discrete _).obj M ≅ (functor R).obj M := by
  have : (LightCondensed.forget R).ReflectsIsomorphisms :=
    inferInstanceAs (sheafCompose _ _).ReflectsIsomorphisms
  refine (functorIsoDiscreteAux R M) ≪≫ (@asIso _ _ _ _ ?_ ?_)
  · exact (LightCondensed.discreteUnderlyingAdj (ModuleCat R)).counit.app ((functor R).obj M)
  · apply this.reflects

open Condensed.LocallyConstantModule in
noncomputable def functorIsoDiscrete : functor R ≅ LightCondensed.discrete _ := by
  refine NatIso.ofComponents (fun M ↦ (functorIsoDiscrete_components R M).symm) ?_
  intro M N f
  dsimp
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  dsimp [functorIsoDiscrete_components]
  rw [Category.assoc, ← Iso.eq_inv_comp]
  erw [← (LightCondensed.discreteUnderlyingAdj (ModuleCat R)).counit.naturality]
  change _ ≫ ((LightCondensed.discreteUnderlyingAdj (ModuleCat R)).counit.app
    (((functor R).obj N))) = _
  simp only [← assoc]
  congr 1
  rw [← Iso.comp_inv_eq]
  apply Sheaf.hom_ext
  simp only [comp_obj, LightCondensed.underlying_obj, functor_obj_val, functorToPresheaves_obj_obj,
    coe_of, LightCondensed.discrete_obj, Functor.comp_map, LightCondensed.underlying_map,
    functorToPresheaves_map_app, LightCondensed.discrete_map, functorIsoDiscreteAux, mapIso_inv,
    ← Functor.map_comp]
  rfl

noncomputable def compIsoId :
    (functor R) ⋙ (LightCondensed.underlying (ModuleCat R)) ≅ 𝟭 _ :=
  NatIso.ofComponents fun M ↦ (functorIsoDiscreteAux' R _).symm

noncomputable def adjunction : functor R ⊣ LightCondensed.underlying (ModuleCat R) :=
  Adjunction.ofNatIsoLeft (LightCondensed.discreteUnderlyingAdj _) (functorIsoDiscrete R).symm

noncomputable def fullyFaithfulFunctor :
    (functor R).FullyFaithful := (adjunction R).fullyFaithfulLOfCompIsoId (compIsoId R)

end LightCondMod
