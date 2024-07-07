/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.TopComparison
/-!

# The adjunction between condensed sets and topological spaces

This file defines the functor `condensedSetToTopCat : CondensedSet.{u} ⥤ TopCat.{u+1}` which is
right adjoint to `topCatToCondensedSet : TopCat.{u+1} ⥤ CondensedSet.{u}`. We prove that the counit
is bijective (but not in general an isomorphism) and conclude that the left adjoint is faithful.
-/

universe u

open Condensed CondensedSet CategoryTheory

attribute [local instance] ConcreteCategory.instFunLike

variable (X : CondensedSet.{u})

/-- Auxiliary defiinition to define the topology on `X(*)` for a condensed set `X`. -/
private def _root_.CompHaus.const (S : CompHaus.{u}) (s : S) : CompHaus.of PUnit.{u+1} ⟶ S :=
  ContinuousMap.const _ s

/-- Auxiliary defiinition to define the topology on `X(*)` for a condensed set `X`. -/
private def CondensedSet.coinducingCoprod :
    (Σ (i : (S : CompHaus.{u}) × X.val.obj ⟨S⟩), i.fst) → X.val.obj ⟨CompHaus.of PUnit⟩ :=
  fun ⟨⟨S, i⟩, s⟩ ↦ X.val.map (S.const s).op i

/-- Let `X` be a condensed set. We define a topology on `X(*)` as the quotient topology of
all the maps from compact Hausdorff `S` spaces to `X(*)`, corresponding to elements of `X(S)`.
In other words, the topology coinduced by the map `CondensedSet.coinducingCoprod` above. -/
local instance : TopologicalSpace (X.val.obj ⟨CompHaus.of PUnit⟩) :=
  TopologicalSpace.coinduced (coinducingCoprod X) inferInstance

/-- The object part of the functor `CondensedSet ⥤ TopCat`  -/
def CondensedSet.toTopCat : TopCat.{u+1} := TopCat.of (X.val.obj ⟨CompHaus.of PUnit⟩)

namespace CondensedSet

variable {X} {Y : CondensedSet} (f : X ⟶ Y)

/-- The map part of the functor `CondensedSet ⥤ TopCat`  -/
@[simps]
def toTopCatMap : X.toTopCat ⟶ Y.toTopCat where
  toFun := f.val.app ⟨CompHaus.of PUnit⟩
  continuous_toFun := by
    rw [continuous_coinduced_dom]
    apply continuous_sigma
    intro ⟨S, x⟩
    simp only [Function.comp_apply, coinducingCoprod]
    have : (fun (a : S) ↦ f.val.app ⟨CompHaus.of PUnit⟩ (X.val.map (S.const a).op x)) =
        (fun (a : S) ↦ Y.val.map (S.const a).op (f.val.app ⟨S⟩ x)) :=
      funext fun a ↦ NatTrans.naturality_apply f.val (S.const a).op x
    rw [this]
    suffices ∀ (i : (T : CompHaus.{u}) × Y.val.obj ⟨T⟩),
        Continuous (fun (a : i.fst) ↦ Y.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
    rw [← continuous_sigma_iff]
    apply continuous_coinduced_rng

end CondensedSet

/-- The functor `CondensedSet ⥤ TopCat`  -/
@[simps]
def condensedSetToTopCat : CondensedSet.{u} ⥤ TopCat.{u+1} where
  obj X := X.toTopCat
  map f := toTopCatMap f

namespace CondensedSet

/-- The counit of the adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet` -/
def topCatAdjunctionCounit (X : TopCat.{u+1}) : X.toCondensedSet.toTopCat ⟶ X where
  toFun x := x.1 PUnit.unit
  continuous_toFun := by
    rw [continuous_coinduced_dom]
    continuity

/-- The counit of the adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet` is always bijective,
but not an isomorphism in general (the inverse isn't continuous unless `X` is compactly generated).
-/
def topCatAdjunctionCounitEquiv (X : TopCat.{u+1}) : X.toCondensedSet.toTopCat ≃ X where
  toFun := topCatAdjunctionCounit X
  invFun x := ContinuousMap.const _ x
  left_inv _ := rfl
  right_inv _ := rfl

lemma topCatAdjunctionCounit_bijective (X : TopCat.{u+1}) :
    Function.Bijective (topCatAdjunctionCounit X) :=
  (topCatAdjunctionCounitEquiv X).bijective

/-- The unit of the adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet` -/
def topCatAdjunctionUnit (X : CondensedSet.{u}) : X ⟶ X.toTopCat.toCondensedSet where
  val := {
    app := fun S x ↦ {
      toFun := fun s ↦ X.val.map (S.unop.const s).op x
      continuous_toFun := by
        suffices ∀ (i : (T : CompHaus.{u}) × X.val.obj ⟨T⟩),
          Continuous (fun (a : i.fst) ↦ X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
        rw [← continuous_sigma_iff]
        apply continuous_coinduced_rng }
    naturality := fun _ _ _ ↦ by
      ext
      simp only [types_comp_apply, ContinuousMap.coe_mk, TopCat.toCondensedSet_val_map,
        ContinuousMap.comp_apply, ← FunctorToTypes.map_comp_apply]
      rfl }

/-- The adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet` -/
noncomputable def topCatAdjunction : condensedSetToTopCat.{u} ⊣ topCatToCondensedSet :=
  Adjunction.mkOfUnitCounit {
    unit := {
      app := topCatAdjunctionUnit
      naturality := by
        intro X Y f
        -- shouldn't `ext` just do the following?
        apply Sheaf.hom_ext; ext S a; apply ContinuousMap.ext; intro x
        -- `simpa using (NatTrans.naturality_apply f.val _ _).symm` doesn't work, and neither
        -- does rewriting using `NatTrans.naturality_apply` (not even with `erw`). What's going on?
        simp? says
          simp only [condensedSetToTopCat_obj, compHausToTop_obj, Functor.id_obj, Functor.comp_obj,
            topCatToCondensedSet_obj, Functor.id_map, comp_val, FunctorToTypes.comp,
            Functor.comp_map, condensedSetToTopCat_map, topCatToCondensedSet_map_val_app,
            ContinuousMap.comp_apply, toTopCatMap_apply]
        exact (NatTrans.naturality_apply f.val _ _).symm }
    counit := { app := topCatAdjunctionCounit }
    left_triangle := by
      ext Y
      change Y.val.map (𝟙 _) _ = _
      simp }

instance (X : TopCat) : Epi (topCatAdjunction.counit.app X) := by
  rw [TopCat.epi_iff_surjective]
  exact (topCatAdjunctionCounit_bijective _).2

instance : topCatToCondensedSet.Faithful := topCatAdjunction.faithful_R_of_epi_counit_app

end CondensedSet
