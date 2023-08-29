/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion.Basic
import Mathlib.AlgebraicGeometry.LocallyRingedSpace.HasColimits

#align_import algebraic_geometry.presheafed_space.gluing from "leanprover-community/mathlib"@"533f62f4dd62a5aad24a04326e6e787c8f7e98b1"

/-!
# Gluing Structured spaces

Given a family of gluing data of structured spaces (presheafed spaces, sheafed spaces, or locally
ringed spaces), we may glue them together.

The construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `AlgebraicGeometry.PresheafedSpace.GlueData`: A structure containing the family of gluing data.
* `CategoryTheory.GlueData.glued`: The glued presheafed space.
    This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
    can be used.
* `CategoryTheory.GlueData.ι`: The immersion `ι i : U i ⟶ glued` for each `i : J`.

## Main results

* `AlgebraicGeometry.PresheafedSpace.GlueData.ιIsOpenImmersion`: The map `ι i : U i ⟶ glued`
  is an open immersion for each `i : J`.
* `AlgebraicGeometry.PresheafedSpace.GlueData.ι_jointly_surjective` : The underlying maps of
  `ι i : U i ⟶ glued` are jointly surjective.
* `AlgebraicGeometry.PresheafedSpace.GlueData.vPullbackConeIsLimit` : `V i j` is the pullback
  (intersection) of `U i` and `U j` over the glued space.

Analogous results are also provided for `SheafedSpace` and `LocallyRingedSpace`.

## Implementation details

Almost the whole file is dedicated to showing tht `ι i` is an open immersion. The fact that
this is an open embedding of topological spaces follows from `Mathlib/Topology/Gluing.lean`, and it
remains to construct `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_X, ι i '' U)` for each `U ⊆ U i`.
Since `Γ(𝒪_X, ι i '' U)` is the limit of `diagram_over_open`, the components of the structure
sheafs of the spaces in the gluing diagram, we need to construct a map
`ιInvApp_π_app : Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_V, U_V)` for each `V` in the gluing diagram.

We will refer to ![this diagram](https://i.imgur.com/P0phrwr.png) in the following doc strings.
The `X` is the glued space, and the dotted arrow is a partial inverse guaranteed by the fact
that it is an open immersion. The map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{U_j}, _)` is given by the composition
of the red arrows, and the map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{V_{jk}}, _)` is given by the composition of the
blue arrows. To lift this into a map from `Γ(𝒪_X, ι i '' U)`, we also need to show that these
commute with the maps in the diagram (the green arrows), which is just a lengthy diagram-chasing.

-/

set_option linter.uppercaseLean3 false

noncomputable section

open TopologicalSpace CategoryTheory Opposite

open CategoryTheory.Limits AlgebraicGeometry.PresheafedSpace

open CategoryTheory.GlueData

namespace AlgebraicGeometry

universe v u

variable (C : Type u) [Category.{v} C]

namespace PresheafedSpace

/-- A family of gluing data consists of
1. An index type `J`
2. A presheafed space `U i` for each `i : J`.
3. A presheafed space `V i j` for each `i j : J`.
  (Note that this is `J × J → PresheafedSpace C` rather than `J → J → PresheafedSpace C` to
  connect to the limits library easier.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the spaces `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subspaces of the glued space.
-/
-- Porting note : removed
-- @[nolint has_nonempty_instance]
structure GlueData extends GlueData (PresheafedSpace.{u, v, v} C) where
  f_open : ∀ i j, IsOpenImmersion (f i j)
#align algebraic_geometry.PresheafedSpace.glue_data AlgebraicGeometry.PresheafedSpace.GlueData

attribute [instance] GlueData.f_open

namespace GlueData

variable {C}
variable (D : GlueData.{v, u} C)

local notation "𝖣" => D.toGlueData

local notation "π₁ " i ", " j ", " k => @pullback.fst _ _ _ _ _ (D.f i j) (D.f i k) _

local notation "π₂ " i ", " j ", " k => @pullback.snd _ _ _ _ _ (D.f i j) (D.f i k) _

set_option quotPrecheck false
local notation "π₁⁻¹ " i ", " j ", " k =>
  (PresheafedSpace.IsOpenImmersion.pullbackFstOfRight (D.f i j) (D.f i k)).invApp

set_option quotPrecheck false
local notation "π₂⁻¹ " i ", " j ", " k =>
  (PresheafedSpace.IsOpenImmersion.pullbackSndOfLeft (D.f i j) (D.f i k)).invApp

/-- The glue data of topological spaces associated to a family of glue data of PresheafedSpaces. -/
abbrev toTopGlueData : TopCat.GlueData :=
  { f_open := fun i j => (D.f_open i j).base_open
    toGlueData := 𝖣.mapGlueData (forget C) }
#align algebraic_geometry.PresheafedSpace.glue_data.to_Top_glue_data AlgebraicGeometry.PresheafedSpace.GlueData.toTopGlueData

theorem ι_openEmbedding [HasLimits C] (i : D.J) : OpenEmbedding (𝖣.ι i).base := by
  rw [← show _ = (𝖣.ι i).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) _]
  -- ⊢ OpenEmbedding ↑(ι (mapGlueData D.toGlueData (forget C)) i ≫ (gluedIso D.toGl …
  -- Porting note : added this erewrite
  erw [coe_comp]
  -- ⊢ OpenEmbedding (↑(gluedIso D.toGlueData (forget C)).inv ∘ ↑(ι (mapGlueData D. …
  refine
    OpenEmbedding.comp
      (TopCat.homeoOfIso (𝖣.gluedIso (PresheafedSpace.forget _)).symm).openEmbedding
      (D.toTopGlueData.ι_openEmbedding i)
#align algebraic_geometry.PresheafedSpace.glue_data.ι_open_embedding AlgebraicGeometry.PresheafedSpace.GlueData.ι_openEmbedding

theorem pullback_base (i j k : D.J) (S : Set (D.V (i, j)).carrier) :
    (π₂ i, j, k) '' ((π₁ i, j, k) ⁻¹' S) = D.f i k ⁻¹' (D.f i j '' S) := by
  have eq₁ : _ = (π₁ i, j, k).base := PreservesPullback.iso_hom_fst (forget C) _ _
  -- ⊢ ↑pullback.snd.base '' (↑pullback.fst.base ⁻¹' S) = ↑(f D.toGlueData i k).bas …
  have eq₂ : _ = (π₂ i, j, k).base := PreservesPullback.iso_hom_snd (forget C) _ _
  -- ⊢ ↑pullback.snd.base '' (↑pullback.fst.base ⁻¹' S) = ↑(f D.toGlueData i k).bas …
  rw [← eq₁, ← eq₂]
  -- ⊢ ↑((PreservesPullback.iso (forget C) (f D.toGlueData i j) (f D.toGlueData i k …
  -- Porting note : `rw` to `erw` on `coe_comp`
  erw [coe_comp]
  -- ⊢ ↑pullback.snd ∘ ↑(PreservesPullback.iso (forget C) (f D.toGlueData i j) (f D …
  rw [Set.image_comp]
  -- ⊢ ↑pullback.snd '' (↑(PreservesPullback.iso (forget C) (f D.toGlueData i j) (f …
  -- Porting note : `rw` to `erw` on `coe_comp`
  erw [coe_comp]
  -- ⊢ ↑pullback.snd '' (↑(PreservesPullback.iso (forget C) (f D.toGlueData i j) (f …
  rw [Set.preimage_comp, Set.image_preimage_eq, TopCat.pullback_snd_image_fst_preimage]
  -- ⊢ ↑((forget C).map (f D.toGlueData i k)) ⁻¹' (↑((forget C).map (f D.toGlueData …
  rfl
  -- ⊢ Function.Surjective ↑(PreservesPullback.iso (forget C) (f D.toGlueData i j)  …
  rw [← TopCat.epi_iff_surjective]
  -- ⊢ Epi (PreservesPullback.iso (forget C) (f D.toGlueData i j) (f D.toGlueData i …
  infer_instance
  -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.glue_data.pullback_base AlgebraicGeometry.PresheafedSpace.GlueData.pullback_base

/-- The red and the blue arrows in ![this diagram](https://i.imgur.com/0GiBUh6.png) commute. -/
@[simp, reassoc]
theorem f_invApp_f_app (i j k : D.J) (U : Opens (D.V (i, j)).carrier) :
    (D.f_open i j).invApp U ≫ (D.f i k).c.app _ =
      (π₁ i, j, k).c.app (op U) ≫
        (π₂⁻¹ i, j, k) (unop _) ≫
          (D.V _).presheaf.map
            (eqToHom
              (by
                delta IsOpenImmersion.openFunctor
                -- ⊢ op ((IsOpenMap.functor (_ : IsOpenMap ↑pullback.snd.base)).obj { unop := { c …
                dsimp only [Functor.op, IsOpenMap.functor, Opens.map, unop_op]
                -- ⊢ op { carrier := ↑pullback.snd.base '' ↑{ carrier := ↑pullback.fst.base ⁻¹' ↑ …
                congr
                -- ⊢ ↑pullback.snd.base '' ↑{ carrier := ↑pullback.fst.base ⁻¹' ↑U, is_open' := ( …
                apply pullback_base)) := by
                -- 🎉 no goals
  have := PresheafedSpace.congr_app (@pullback.condition _ _ _ _ _ (D.f i j) (D.f i k) _)
  -- ⊢ IsOpenImmersion.invApp (_ : IsOpenImmersion (f D.toGlueData i j)) U ≫ NatTra …
  dsimp only [comp_c_app] at this
  -- ⊢ IsOpenImmersion.invApp (_ : IsOpenImmersion (f D.toGlueData i j)) U ≫ NatTra …
  rw [← cancel_epi (inv ((D.f_open i j).invApp U)), IsIso.inv_hom_id_assoc,
    IsOpenImmersion.inv_invApp]
  simp_rw [Category.assoc]
  -- ⊢ NatTrans.app (f D.toGlueData i k).c (op ((IsOpenImmersion.openFunctor (_ : I …
  erw [(π₁ i, j, k).c.naturality_assoc, reassoc_of% this, ← Functor.map_comp_assoc,
    IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.app_invApp_assoc, ←
    (D.V (i, k)).presheaf.map_comp, ← (D.V (i, k)).presheaf.map_comp]
  -- Porting note : need to provide an explicit argument, otherwise Lean does not know which
  -- category we are talking about
  convert (Category.comp_id ((f D.toGlueData i k).c.app _)).symm
  -- ⊢ (V D.toGlueData (i, k)).presheaf.map ((homOfLE (_ : ↑pullback.snd.base '' (↑ …
  erw [(D.V (i, k)).presheaf.map_id]
  -- ⊢ 𝟙 ((V D.toGlueData (i, k)).presheaf.obj (op ((Opens.map (f D.toGlueData i k) …
  rfl
  -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.glue_data.f_inv_app_f_app AlgebraicGeometry.PresheafedSpace.GlueData.f_invApp_f_app

/-- We can prove the `eq` along with the lemma. Thus this is bundled together here, and the
lemma itself is separated below.
-/
theorem snd_invApp_t_app' (i j k : D.J) (U : Opens (pullback (D.f i j) (D.f i k)).carrier) :
    ∃ eq,
      (π₂⁻¹ i, j, k) U ≫ (D.t k i).c.app _ ≫ (D.V (k, i)).presheaf.map (eqToHom eq) =
        (D.t' k i j).c.app _ ≫ (π₁⁻¹ k, j, i) (unop _) := by
  fconstructor
  -- ⊢ (Opens.map (t D.toGlueData k i).base).op.obj (op ((IsOpenImmersion.openFunct …
  -- Porting note: I don't know what the magic was in Lean3 proof, it just skipped the proof of `eq`
  · delta IsOpenImmersion.openFunctor
    -- ⊢ (Opens.map (t D.toGlueData k i).base).op.obj (op ((IsOpenMap.functor (_ : Is …
    dsimp only [Functor.op, Opens.map, IsOpenMap.functor, unop_op, Opens.coe_mk]
    -- ⊢ op { carrier := ↑(t D.toGlueData k i).base ⁻¹' (↑pullback.snd.base '' ↑U), i …
    congr
    -- ⊢ ↑(t D.toGlueData k i).base ⁻¹' (↑pullback.snd.base '' ↑U) = ↑pullback.fst.ba …
    have := (𝖣.t_fac k i j).symm
    -- ⊢ ↑(t D.toGlueData k i).base ⁻¹' (↑pullback.snd.base '' ↑U) = ↑pullback.fst.ba …
    rw [←IsIso.inv_comp_eq] at this
    -- ⊢ ↑(t D.toGlueData k i).base ⁻¹' (↑pullback.snd.base '' ↑U) = ↑pullback.fst.ba …
    replace this := (congr_arg ((PresheafedSpace.Hom.base ·)) this).symm
    -- ⊢ ↑(t D.toGlueData k i).base ⁻¹' (↑pullback.snd.base '' ↑U) = ↑pullback.fst.ba …
    replace this := congr_arg (ContinuousMap.toFun ·) this
    -- ⊢ ↑(t D.toGlueData k i).base ⁻¹' (↑pullback.snd.base '' ↑U) = ↑pullback.fst.ba …
    dsimp at this
    -- ⊢ ↑(t D.toGlueData k i).base ⁻¹' (↑pullback.snd.base '' ↑U) = ↑pullback.fst.ba …
    rw [coe_comp, coe_comp] at this
    -- ⊢ ↑(t D.toGlueData k i).base ⁻¹' (↑pullback.snd.base '' ↑U) = ↑pullback.fst.ba …
    rw [this, Set.image_comp, Set.image_comp, Set.preimage_image_eq]
    -- ⊢ ↑pullback.fst.base '' (↑(inv (t' D.toGlueData k i j)).base '' ↑U) = ↑pullbac …
    swap
    -- ⊢ Function.Injective ↑(t D.toGlueData k i).base
    · refine Function.HasLeftInverse.injective ⟨(D.t i k).base, fun x => ?_⟩
      -- ⊢ ↑(t D.toGlueData i k).base (↑(t D.toGlueData k i).base x) = x
      rw [←comp_apply, ←comp_base, D.t_inv, id_base, id_apply]
      -- 🎉 no goals
    refine congr_arg (_ '' ·) ?_
    -- ⊢ ↑(inv (t' D.toGlueData k i j)).base '' ↑U = ↑(t' D.toGlueData k i j).base ⁻¹ …
    refine congr_fun ?_ _
    -- ⊢ Set.image ↑(inv (t' D.toGlueData k i j)).base = Set.preimage ↑(t' D.toGlueDa …
    refine Set.image_eq_preimage_of_inverse ?_ ?_
    -- ⊢ Function.LeftInverse ↑(t' D.toGlueData k i j).base ↑(inv (t' D.toGlueData k  …
    · intro x
      -- ⊢ ↑(t' D.toGlueData k i j).base (↑(inv (t' D.toGlueData k i j)).base x) = x
      rw [←comp_apply, ←comp_base, IsIso.inv_hom_id, id_base, id_apply]
      -- 🎉 no goals
    · intro x
      -- ⊢ ↑(inv (t' D.toGlueData k i j)).base (↑(t' D.toGlueData k i j).base x) = x
      rw [←comp_apply, ←comp_base, IsIso.hom_inv_id, id_base, id_apply]
      -- 🎉 no goals
  · rw [← IsIso.eq_inv_comp, IsOpenImmersion.inv_invApp, Category.assoc,
      (D.t' k i j).c.naturality_assoc]
    simp_rw [← Category.assoc]
    -- ⊢ NatTrans.app (t D.toGlueData k i).c (op ((IsOpenImmersion.openFunctor (_ : I …
    erw [← comp_c_app]
    -- ⊢ NatTrans.app (t D.toGlueData k i).c (op ((IsOpenImmersion.openFunctor (_ : I …
    rw [congr_app (D.t_fac k i j), comp_c_app]
    -- ⊢ NatTrans.app (t D.toGlueData k i).c (op ((IsOpenImmersion.openFunctor (_ : I …
    simp_rw [Category.assoc]
    -- ⊢ NatTrans.app (t D.toGlueData k i).c (op ((IsOpenImmersion.openFunctor (_ : I …
    erw [IsOpenImmersion.inv_naturality, IsOpenImmersion.inv_naturality_assoc,
      IsOpenImmersion.app_inv_app'_assoc]
    simp_rw [← (𝖣.V (k, i)).presheaf.map_comp, eqToHom_map (Functor.op _), eqToHom_op,
      eqToHom_trans]
    rintro x ⟨y, -, eq⟩
    -- ⊢ x ∈ Set.range ↑pullback.fst.base
    replace eq := ConcreteCategory.congr_arg (𝖣.t i k).base eq
    -- ⊢ x ∈ Set.range ↑pullback.fst.base
    change ((π₂ i, j, k) ≫ D.t i k).base y = (D.t k i ≫ D.t i k).base x at eq
    -- ⊢ x ∈ Set.range ↑pullback.fst.base
    rw [𝖣.t_inv, id_base, TopCat.id_app] at eq
    -- ⊢ x ∈ Set.range ↑pullback.fst.base
    subst eq
    -- ⊢ ↑(pullback.snd ≫ t D.toGlueData i k).base y ∈ Set.range ↑pullback.fst.base
    use (inv (D.t' k i j)).base y
    -- ⊢ ↑pullback.fst.base (↑(inv (t' D.toGlueData k i j)).base y) = ↑(pullback.snd  …
    change (inv (D.t' k i j) ≫ π₁ k, i, j).base y = _
    -- ⊢ ↑(inv (t' D.toGlueData k i j) ≫ pullback.fst).base y = ↑(pullback.snd ≫ t D. …
    congr 2
    -- ⊢ inv (t' D.toGlueData k i j) ≫ pullback.fst = pullback.snd ≫ t D.toGlueData i k
    rw [IsIso.inv_comp_eq, 𝖣.t_fac_assoc, 𝖣.t_inv, Category.comp_id]
    -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.glue_data.snd_inv_app_t_app' AlgebraicGeometry.PresheafedSpace.GlueData.snd_invApp_t_app'

/-- The red and the blue arrows in ![this diagram](https://i.imgur.com/q6X1GJ9.png) commute. -/
@[simp, reassoc]
theorem snd_invApp_t_app (i j k : D.J) (U : Opens (pullback (D.f i j) (D.f i k)).carrier) :
    (π₂⁻¹ i, j, k) U ≫ (D.t k i).c.app _ =
      (D.t' k i j).c.app _ ≫
        (π₁⁻¹ k, j, i) (unop _) ≫
          (D.V (k, i)).presheaf.map (eqToHom (D.snd_invApp_t_app' i j k U).choose.symm) := by
  have e := (D.snd_invApp_t_app' i j k U).choose_spec
  -- ⊢ IsOpenImmersion.invApp (_ : IsOpenImmersion pullback.snd) U ≫ NatTrans.app ( …
  replace e := reassoc_of% e
  -- ⊢ IsOpenImmersion.invApp (_ : IsOpenImmersion pullback.snd) U ≫ NatTrans.app ( …
  rw [← e]
  -- ⊢ IsOpenImmersion.invApp (_ : IsOpenImmersion pullback.snd) U ≫ NatTrans.app ( …
  simp [eqToHom_map]
  -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.glue_data.snd_inv_app_t_app AlgebraicGeometry.PresheafedSpace.GlueData.snd_invApp_t_app

variable [HasLimits C]

theorem ι_image_preimage_eq (i j : D.J) (U : Opens (D.U i).carrier) :
    (Opens.map (𝖣.ι j).base).obj ((D.ι_openEmbedding i).isOpenMap.functor.obj U) =
      (D.f_open j i).openFunctor.obj
        ((Opens.map (𝖣.t j i).base).obj ((Opens.map (𝖣.f i j).base).obj U)) := by
  ext1
  -- ⊢ ↑((Opens.map (ι D.toGlueData j).base).obj ((IsOpenMap.functor (_ : IsOpenMap …
  dsimp only [Opens.map_coe, IsOpenMap.functor_obj_coe]
  -- ⊢ ↑(ι D.toGlueData j).base ⁻¹' (↑(ι D.toGlueData i).base '' ↑U) = ↑(f D.toGlue …
  rw [← show _ = (𝖣.ι i).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) i, ←
    show _ = (𝖣.ι j).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) j]
  -- Porting note : change `rw` to `erw` on `coe_comp`
  erw [coe_comp, coe_comp, coe_comp]
  -- ⊢ (↑(preservesColimitIso (forget C) (MultispanIndex.multispan (diagram D.toGlu …
  rw [Set.image_comp, Set.preimage_comp]
  -- ⊢ ↑(ι (mapGlueData D.toGlueData (forget C)) j) ⁻¹' (↑(preservesColimitIso (for …
  erw [Set.preimage_image_eq]
  -- ⊢ ↑(ι (mapGlueData D.toGlueData (forget C)) j) ⁻¹' (↑(ι (mapGlueData D.toGlueD …
  · refine' Eq.trans (D.toTopGlueData.preimage_image_eq_image' _ _ _) _
    -- ⊢ ↑(t (toTopGlueData D).toGlueData i j ≫ f (toTopGlueData D).toGlueData j i) ' …
    dsimp
    -- ⊢ ↑((t D.toGlueData i j).base ≫ (f D.toGlueData j i).base) '' (↑(f D.toGlueDat …
    rw [coe_comp, Set.image_comp]
    -- ⊢ ↑(f D.toGlueData j i).base '' (↑(t D.toGlueData i j).base '' (↑(f D.toGlueDa …
    refine congr_arg (_ '' ·) ?_
    -- ⊢ ↑(t D.toGlueData i j).base '' (↑(f D.toGlueData i j).base ⁻¹' ↑U) = ↑(t D.to …
    rw [Set.eq_preimage_iff_image_eq, ← Set.image_comp]
    -- ⊢ ↑(t D.toGlueData j i).base ∘ ↑(t D.toGlueData i j).base '' (↑(f D.toGlueData …
    swap
    -- ⊢ Function.Bijective ↑(t D.toGlueData j i).base
    · apply CategoryTheory.ConcreteCategory.bijective_of_isIso
      -- 🎉 no goals
    change (D.t i j ≫ D.t j i).base '' _ = _
    -- ⊢ ↑(t D.toGlueData i j ≫ t D.toGlueData j i).base '' (↑(f D.toGlueData i j).ba …
    rw [𝖣.t_inv]
    -- ⊢ ↑(𝟙 (V D.toGlueData (i, j))).base '' (↑(f D.toGlueData i j).base ⁻¹' ↑U) = ↑ …
    simp
    -- 🎉 no goals
  · rw [←coe_comp, ← TopCat.mono_iff_injective]
    -- ⊢ Mono ((HasColimit.isoOfNatIso (diagramIso D.toGlueData (forget C))).inv ≫ (p …
    infer_instance
    -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.glue_data.ι_image_preimage_eq AlgebraicGeometry.PresheafedSpace.GlueData.ι_image_preimage_eq

/-- (Implementation). The map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{U_j}, 𝖣.ι j ⁻¹' (𝖣.ι i '' U))` -/
def opensImagePreimageMap (i j : D.J) (U : Opens (D.U i).carrier) :
    (D.U i).presheaf.obj (op U) ⟶
    (D.U j).presheaf.obj (op <|
      (Opens.map (𝖣.ι j).base).obj ((D.ι_openEmbedding i).isOpenMap.functor.obj U)) :=
  (D.f i j).c.app (op U) ≫
    (D.t j i).c.app _ ≫
      (D.f_open j i).invApp (unop _) ≫
        (𝖣.U j).presheaf.map (eqToHom (D.ι_image_preimage_eq i j U)).op
#align algebraic_geometry.PresheafedSpace.glue_data.opens_image_preimage_map AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap

theorem opensImagePreimageMap_app' (i j k : D.J) (U : Opens (D.U i).carrier) :
    ∃ eq,
      D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ =
        ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫
          (π₂⁻¹ j, i, k) (unop _) ≫ (D.V (j, k)).presheaf.map (eqToHom eq) := by
  constructor
  -- ⊢ opensImagePreimageMap D i j U ≫ NatTrans.app (f D.toGlueData j k).c (op ((Op …
  delta opensImagePreimageMap
  -- ⊢ (NatTrans.app (f D.toGlueData i j).c (op U) ≫ NatTrans.app (t D.toGlueData j …
  simp_rw [Category.assoc]
  -- ⊢ NatTrans.app (f D.toGlueData i j).c (op U) ≫ NatTrans.app (t D.toGlueData j  …
  rw [(D.f j k).c.naturality, f_invApp_f_app_assoc]
  erw [← (D.V (j, k)).presheaf.map_comp]
  simp_rw [← Category.assoc]
  erw [← comp_c_app, ← comp_c_app]
  simp_rw [Category.assoc]
  dsimp only [Functor.op, unop_op, Quiver.Hom.unop_op]
  rw [eqToHom_map (Opens.map _), eqToHom_op, eqToHom_trans]
  congr
  -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.glue_data.opens_image_preimage_map_app' AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap_app'

/-- The red and the blue arrows in ![this diagram](https://i.imgur.com/mBzV1Rx.png) commute. -/
theorem opensImagePreimageMap_app (i j k : D.J) (U : Opens (D.U i).carrier) :
    D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ =
      ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫
        (π₂⁻¹ j, i, k) (unop _) ≫
          (D.V (j, k)).presheaf.map (eqToHom (opensImagePreimageMap_app' D i j k U).choose) :=
  (opensImagePreimageMap_app' D i j k U).choose_spec
#align algebraic_geometry.PresheafedSpace.glue_data.opens_image_preimage_map_app AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap_app

-- This is proved separately since `reassoc` somehow timeouts.
theorem opensImagePreimageMap_app_assoc (i j k : D.J) (U : Opens (D.U i).carrier) {X' : C}
    (f' : _ ⟶ X') :
    D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ ≫ f' =
      ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫
        (π₂⁻¹ j, i, k) (unop _) ≫
          (D.V (j, k)).presheaf.map
            (eqToHom (opensImagePreimageMap_app' D i j k U).choose) ≫ f' := by
  simpa only [Category.assoc] using congr_arg (· ≫ f') (opensImagePreimageMap_app D i j k U)
  -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.glue_data.opens_image_preimage_map_app_assoc AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap_app_assoc

/-- (Implementation) Given an open subset of one of the spaces `U ⊆ Uᵢ`, the sheaf component of
the image `ι '' U` in the glued space is the limit of this diagram. -/
abbrev diagramOverOpen {i : D.J} (U : Opens (D.U i).carrier) :
    -- Portinge note : ↓ these need to be explicit
    (WalkingMultispan D.diagram.fstFrom D.diagram.sndFrom)ᵒᵖ ⥤ C :=
  componentwiseDiagram 𝖣.diagram.multispan ((D.ι_openEmbedding i).isOpenMap.functor.obj U)
#align algebraic_geometry.PresheafedSpace.glue_data.diagram_over_open AlgebraicGeometry.PresheafedSpace.GlueData.diagramOverOpen

/-- (Implementation)
The projection from the limit of `diagram_over_open` to a component of `D.U j`. -/
abbrev diagramOverOpenπ {i : D.J} (U : Opens (D.U i).carrier) (j : D.J) :=
  limit.π (D.diagramOverOpen U) (op (WalkingMultispan.right j))
#align algebraic_geometry.PresheafedSpace.glue_data.diagram_over_open_π AlgebraicGeometry.PresheafedSpace.GlueData.diagramOverOpenπ

/-- (Implementation) We construct the map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_V, U_V)` for each `V` in the gluing
diagram. We will lift these maps into `ιInvApp`. -/
def ιInvAppπApp {i : D.J} (U : Opens (D.U i).carrier) (j) :
    (𝖣.U i).presheaf.obj (op U) ⟶ (D.diagramOverOpen U).obj (op j) := by
  rcases j with (⟨j, k⟩ | j)
  -- ⊢ (CategoryTheory.GlueData.U D.toGlueData i).presheaf.obj (op U) ⟶ (diagramOve …
  · refine'
      D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ ≫ (D.V (j, k)).presheaf.map (eqToHom _)
    rw [Functor.op_obj]
    -- ⊢ op ((Opens.map (f D.toGlueData j k).base).obj (op ((Opens.map (ι D.toGlueDat …
    congr 1; ext1
    -- ⊢ (Opens.map (f D.toGlueData j k).base).obj (op ((Opens.map (ι D.toGlueData j) …
             -- ⊢ ↑((Opens.map (f D.toGlueData j k).base).obj (op ((Opens.map (ι D.toGlueData  …
    dsimp only [Functor.op_obj, Opens.map_coe, unop_op, IsOpenMap.functor_obj_coe]
    -- ⊢ ↑(f D.toGlueData j k).base ⁻¹' (↑(ι D.toGlueData j).base ⁻¹' (↑(ι D.toGlueDa …
    rw [Set.preimage_preimage]
    -- ⊢ (fun x => ↑(ι D.toGlueData j).base (↑(f D.toGlueData j k).base x)) ⁻¹' (↑(ι  …
    change (D.f j k ≫ 𝖣.ι j).base ⁻¹' _ = _
    -- ⊢ ↑(f D.toGlueData j k ≫ ι D.toGlueData j).base ⁻¹' (↑(ι D.toGlueData i).base  …
    -- Porting note : used to be `congr 3`
    refine congr_arg (· ⁻¹' _) ?_
    -- ⊢ ↑(f D.toGlueData j k ≫ ι D.toGlueData j).base = ↑(colimit.ι (MultispanIndex. …
    convert congr_arg (ContinuousMap.toFun (α := D.V ⟨j, k⟩) (β := D.glued) ·) ?_
    -- ⊢ (f D.toGlueData j k ≫ ι D.toGlueData j).base = (colimit.ι (MultispanIndex.mu …
    refine congr_arg (PresheafedSpace.Hom.base (C := C) ·) ?_
    -- ⊢ f D.toGlueData j k ≫ ι D.toGlueData j = colimit.ι (MultispanIndex.multispan  …
    exact colimit.w 𝖣.diagram.multispan (WalkingMultispan.Hom.fst (j, k))
    -- 🎉 no goals
  · exact D.opensImagePreimageMap i j U
    -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.glue_data.ι_inv_app_π_app AlgebraicGeometry.PresheafedSpace.GlueData.ιInvAppπApp

-- Porting note : time out started in `erw [... congr_app (pullbackSymmetry_hom_comp_snd _ _)]` and
-- the last congr has a very difficult `rfl : eqToHom _ ≫ eqToHom _ ≫ ... = eqToHom ... `
set_option maxHeartbeats 600000 in
/-- (Implementation) The natural map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_X, 𝖣.ι i '' U)`.
This forms the inverse of `(𝖣.ι i).c.app (op U)`. -/
def ιInvApp {i : D.J} (U : Opens (D.U i).carrier) :
    (D.U i).presheaf.obj (op U) ⟶ limit (D.diagramOverOpen U) :=
  limit.lift (D.diagramOverOpen U)
    { pt := (D.U i).presheaf.obj (op U)
      π :=
        { app := fun j => D.ιInvAppπApp U (unop j)
          naturality := fun {X Y} f' => by
            induction X using Opposite.rec' with | h X => ?_
            -- ⊢ ((Functor.const (WalkingMultispan (diagram D.toGlueData).fstFrom (diagram D. …
            -- ⊢ ((Functor.const (WalkingMultispan (diagram D.toGlueData).fstFrom (diagram D. …
            induction Y using Opposite.rec' with | h Y => ?_
            -- ⊢ ((Functor.const (WalkingMultispan (diagram D.toGlueData).fstFrom (diagram D. …
            -- ⊢ ((Functor.const (WalkingMultispan (diagram D.toGlueData).fstFrom (diagram D. …
            let f : Y ⟶ X := f'.unop; have : f' = f.op := rfl; clear_value f; subst this
            -- ⊢ ((Functor.const (WalkingMultispan (diagram D.toGlueData).fstFrom (diagram D. …
                                      -- ⊢ ((Functor.const (WalkingMultispan (diagram D.toGlueData).fstFrom (diagram D. …
                                                               -- ⊢ ((Functor.const (WalkingMultispan (diagram D.toGlueData).fstFrom (diagram D. …
                                                                              -- ⊢ ((Functor.const (WalkingMultispan (diagram D.toGlueData).fstFrom (diagram D. …
            rcases f with (_ | ⟨j, k⟩ | ⟨j, k⟩)
            · erw [Category.id_comp, CategoryTheory.Functor.map_id]
              -- ⊢ (fun j => ιInvAppπApp D U j.unop) (op X) = (fun j => ιInvAppπApp D U j.unop) …
              rw [Category.comp_id]
              -- 🎉 no goals
            · erw [Category.id_comp]; congr 1
              -- ⊢ (fun j => ιInvAppπApp D U j.unop) (op (WalkingMultispan.left (j, k))) = (fun …
                                      -- 🎉 no goals
            erw [Category.id_comp]
            -- ⊢ (fun j => ιInvAppπApp D U j.unop) (op (WalkingMultispan.left (j, k))) = (fun …
            -- It remains to show that the blue is equal to red + green in the original diagram.
            -- The proof strategy is illustrated in ![this diagram](https://i.imgur.com/mBzV1Rx.png)
            -- where we prove red = pink = light-blue = green = blue.
            change
              D.opensImagePreimageMap i j U ≫
                  (D.f j k).c.app _ ≫ (D.V (j, k)).presheaf.map (eqToHom _) =
                D.opensImagePreimageMap _ _ _ ≫
                  ((D.f k j).c.app _ ≫ (D.t j k).c.app _) ≫ (D.V (j, k)).presheaf.map (eqToHom _)
            erw [opensImagePreimageMap_app_assoc]
            -- ⊢ NatTrans.app (pullback.fst ≫ t D.toGlueData j i ≫ f D.toGlueData i j).c (op  …
            simp_rw [Category.assoc]
            -- ⊢ NatTrans.app (pullback.fst ≫ t D.toGlueData j i ≫ f D.toGlueData i j).c (op  …
            erw [opensImagePreimageMap_app_assoc, (D.t j k).c.naturality_assoc]
            -- ⊢ NatTrans.app (pullback.fst ≫ t D.toGlueData j i ≫ f D.toGlueData i j).c (op  …
            rw [snd_invApp_t_app_assoc]
            -- ⊢ NatTrans.app (pullback.fst ≫ t D.toGlueData j i ≫ f D.toGlueData i j).c (op  …
            erw [← PresheafedSpace.comp_c_app_assoc]
            -- ⊢ NatTrans.app (pullback.fst ≫ t D.toGlueData j i ≫ f D.toGlueData i j).c (op  …
            -- light-blue = green is relatively easy since the part that differs does not involve
            -- partial inverses.
            have :
              D.t' j k i ≫ (π₁ k, i, j) ≫ D.t k i ≫ 𝖣.f i k =
                (pullbackSymmetry _ _).hom ≫ (π₁ j, i, k) ≫ D.t j i ≫ D.f i j := by
              rw [← 𝖣.t_fac_assoc, 𝖣.t'_comp_eq_pullbackSymmetry_assoc,
                pullbackSymmetry_hom_comp_snd_assoc, pullback.condition, 𝖣.t_fac_assoc]
            rw [congr_app this]
            -- ⊢ NatTrans.app (pullback.fst ≫ t D.toGlueData j i ≫ f D.toGlueData i j).c (op  …
            erw [PresheafedSpace.comp_c_app_assoc (pullbackSymmetry _ _).hom]
            -- ⊢ NatTrans.app (pullback.fst ≫ t D.toGlueData j i ≫ f D.toGlueData i j).c (op  …
            simp_rw [Category.assoc]
            -- ⊢ NatTrans.app (pullback.fst ≫ t D.toGlueData j i ≫ f D.toGlueData i j).c (op  …
            congr 1
            -- ⊢ IsOpenImmersion.invApp (_ : IsOpenImmersion pullback.snd) { carrier := ↑(pul …
            rw [← IsIso.eq_inv_comp]
            -- ⊢ (V D.toGlueData (j, k)).presheaf.map (eqToHom (_ : op ((IsOpenImmersion.open …
            erw [IsOpenImmersion.inv_invApp]
            -- ⊢ (V D.toGlueData (j, k)).presheaf.map (eqToHom (_ : op ((IsOpenImmersion.open …
            simp_rw [Category.assoc]
            -- ⊢ (V D.toGlueData (j, k)).presheaf.map (eqToHom (_ : op ((IsOpenImmersion.open …
            erw [NatTrans.naturality_assoc, ← PresheafedSpace.comp_c_app_assoc,
              congr_app (pullbackSymmetry_hom_comp_snd _ _)]
            simp_rw [Category.assoc]
            -- ⊢ (V D.toGlueData (j, k)).presheaf.map (eqToHom (_ : op ((IsOpenImmersion.open …
            erw [IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.inv_naturality_assoc,
              IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.app_invApp_assoc]
            repeat' erw [← (D.V (j, k)).presheaf.map_comp]
            -- ⊢ (V D.toGlueData (j, k)).presheaf.map (eqToHom (_ : op ((IsOpenImmersion.open …
            -- Porting note : was just `congr`
            exact congr_arg ((D.V (j, k)).presheaf.map ·) rfl } }
            -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.glue_data.ι_inv_app AlgebraicGeometry.PresheafedSpace.GlueData.ιInvApp

/-- `ιInvApp` is the left inverse of `D.ι i` on `U`. -/
theorem ιInvApp_π {i : D.J} (U : Opens (D.U i).carrier) :
    ∃ eq, D.ιInvApp U ≫ D.diagramOverOpenπ U i = (D.U i).presheaf.map (eqToHom eq) := by
  fconstructor
  -- ⊢ op U = op ((Opens.map (colimit.ι (MultispanIndex.multispan (diagram D.toGlue …
  -- Porting note: I don't know what the magic was in Lean3 proof, it just skipped the proof of `eq`
  · congr; ext1; change _ = _ ⁻¹' (_ '' _); ext1 x
    -- ⊢ U = (Opens.map (colimit.ι (MultispanIndex.multispan (diagram D.toGlueData))  …
           -- ⊢ ↑U = ↑((Opens.map (colimit.ι (MultispanIndex.multispan (diagram D.toGlueData …
                 -- ⊢ ↑U = (fun x => ↑(colimit.ι (MultispanIndex.multispan (diagram D.toGlueData)) …
                                            -- ⊢ x ∈ ↑U ↔ x ∈ (fun x => ↑(colimit.ι (MultispanIndex.multispan (diagram D.toGl …
    simp only [SetLike.mem_coe, diagram_l, diagram_r, unop_op, Set.mem_preimage, Set.mem_image]
    -- ⊢ x ∈ U ↔ ∃ x_1, x_1 ∈ U ∧ ↑(ι D.toGlueData i).base x_1 = ↑(colimit.ι (Multisp …
    refine ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    -- ⊢ (∃ x_1, x_1 ∈ U ∧ ↑(ι D.toGlueData i).base x_1 = ↑(colimit.ι (MultispanIndex …
    rintro ⟨y, h1, h2⟩
    -- ⊢ x ∈ U
    convert h1 using 1
    -- ⊢ x = y
    delta ι Multicoequalizer.π at h2
    -- ⊢ x = y
    apply_fun (D.ι _).base
    -- ⊢ ↑(ι D.toGlueData i).base x = ↑(ι D.toGlueData i).base y
    · exact h2.symm
      -- 🎉 no goals
    · have := D.ι_gluedIso_inv (PresheafedSpace.forget _) i
      -- ⊢ Function.Injective ↑(ι D.toGlueData i).base
      dsimp at this
      -- ⊢ Function.Injective ↑(ι D.toGlueData i).base
      rw [←this, coe_comp]
      -- ⊢ Function.Injective (↑(gluedIso D.toGlueData (forget C)).inv ∘ ↑(ι (mapGlueDa …
      refine Function.Injective.comp ?_ (TopCat.GlueData.ι_injective D.toTopGlueData i)
      -- ⊢ Function.Injective ↑(gluedIso D.toGlueData (forget C)).inv
      rw [←TopCat.mono_iff_injective]
      -- ⊢ Mono (gluedIso D.toGlueData (forget C)).inv
      infer_instance
      -- 🎉 no goals
  delta ιInvApp
  -- ⊢ limit.lift (diagramOverOpen D U) { pt := (CategoryTheory.GlueData.U D.toGlue …
  rw [limit.lift_π]
  -- ⊢ NatTrans.app { pt := (CategoryTheory.GlueData.U D.toGlueData i).presheaf.obj …
  change D.opensImagePreimageMap i i U = _
  -- ⊢ opensImagePreimageMap D i i U = (CategoryTheory.GlueData.U D.toGlueData i).p …
  dsimp [opensImagePreimageMap]
  -- ⊢ NatTrans.app (f D.toGlueData i i).c (op U) ≫ NatTrans.app (t D.toGlueData i  …
  rw [congr_app (D.t_id _), id_c_app, ← Functor.map_comp]
  -- ⊢ NatTrans.app (f D.toGlueData i i).c (op U) ≫ (V D.toGlueData (i, i)).preshea …
  erw [IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.app_inv_app'_assoc]
  -- ⊢ (CategoryTheory.GlueData.U D.toGlueData i).presheaf.map (eqToHom (_ : (IsOpe …
  · simp only [eqToHom_op, eqToHom_trans, eqToHom_map (Functor.op _), ← Functor.map_comp]
    -- ⊢ (CategoryTheory.GlueData.U D.toGlueData i).presheaf.map (eqToHom (_ : op U = …
    rfl
    -- 🎉 no goals
  · rw [Set.range_iff_surjective.mpr _]
    -- ⊢ ↑U ⊆ Set.univ
    · simp
      -- 🎉 no goals
    · rw [← TopCat.epi_iff_surjective]
      -- ⊢ Epi (f D.toGlueData i i).base
      infer_instance
      -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.glue_data.ι_inv_app_π AlgebraicGeometry.PresheafedSpace.GlueData.ιInvApp_π

/-- The `eqToHom` given by `ιInvApp_π`. -/
abbrev ιInvAppπEqMap {i : D.J} (U : Opens (D.U i).carrier) :=
  (D.U i).presheaf.map (eqToIso (D.ιInvApp_π U).choose).inv
#align algebraic_geometry.PresheafedSpace.glue_data.ι_inv_app_π_eq_map AlgebraicGeometry.PresheafedSpace.GlueData.ιInvAppπEqMap

/-- `ιInvApp` is the right inverse of `D.ι i` on `U`. -/
theorem π_ιInvApp_π (i j : D.J) (U : Opens (D.U i).carrier) :
    D.diagramOverOpenπ U i ≫ D.ιInvAppπEqMap U ≫ D.ιInvApp U ≫ D.diagramOverOpenπ U j =
      D.diagramOverOpenπ U j := by
  -- Porting note : originally, the proof of monotonicity was left a blank and proved in the end
  -- but Lean 4 doesn't like this any more, so the proof is restructured
  rw [← @cancel_mono (f := (componentwiseDiagram 𝖣.diagram.multispan _).map
    (Quiver.Hom.op (WalkingMultispan.Hom.snd (i, j))) ≫ 𝟙 _) _ _ (by
    rw [Category.comp_id]
    apply (config := { allowSynthFailures := true }) mono_comp
    change Mono ((_ ≫ D.f j i).c.app _)
    rw [comp_c_app]
    apply (config := { allowSynthFailures := true }) mono_comp
    erw [D.ι_image_preimage_eq i j U]
    · infer_instance
    · have : IsIso (D.t i j).c := by apply c_isIso_of_iso
      infer_instance)]
  simp_rw [Category.assoc]
  -- ⊢ diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ ιInvApp D U ≫ diagramOverOpenπ  …
  rw [limit.w_assoc]
  -- ⊢ diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ ιInvApp D U ≫ limit.π (diagramO …
  erw [limit.lift_π_assoc]
  -- ⊢ diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ NatTrans.app { pt := (CategoryT …
  rw [Category.comp_id, Category.comp_id]
  -- ⊢ diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ NatTrans.app { pt := (CategoryT …
  change _ ≫ _ ≫ (_ ≫ _) ≫ _ = _
  -- ⊢ diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ (NatTrans.app (f D.toGlueData i …
  rw [congr_app (D.t_id _), id_c_app]
  -- ⊢ diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ (NatTrans.app (f D.toGlueData i …
  simp_rw [Category.assoc]
  -- ⊢ diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ NatTrans.app (f D.toGlueData i  …
  rw [← Functor.map_comp_assoc]
  -- ⊢ diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ NatTrans.app (f D.toGlueData i  …
  -- Porting note : change `rw` to `erw`
  erw [IsOpenImmersion.inv_naturality_assoc]
  -- ⊢ diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ NatTrans.app (f D.toGlueData i  …
  erw [IsOpenImmersion.app_invApp_assoc]
  -- ⊢ diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ (CategoryTheory.GlueData.U D.to …
  iterate 3 rw [← Functor.map_comp_assoc]
  -- ⊢ diagramOverOpenπ D U i ≫ (CategoryTheory.GlueData.U D.toGlueData i).presheaf …
  rw [NatTrans.naturality_assoc]
  -- ⊢ diagramOverOpenπ D U i ≫ NatTrans.app (f D.toGlueData i j).c (op ((Opens.map …
  erw [← (D.V (i, j)).presheaf.map_comp]
  -- ⊢ diagramOverOpenπ D U i ≫ NatTrans.app (f D.toGlueData i j).c (op ((Opens.map …
  convert
    limit.w (componentwiseDiagram 𝖣.diagram.multispan _)
      (Quiver.Hom.op (WalkingMultispan.Hom.fst (i, j)))
#align algebraic_geometry.PresheafedSpace.glue_data.π_ι_inv_app_π AlgebraicGeometry.PresheafedSpace.GlueData.π_ιInvApp_π

/-- `ιInvApp` is the inverse of `D.ι i` on `U`. -/
theorem π_ιInvApp_eq_id (i : D.J) (U : Opens (D.U i).carrier) :
    D.diagramOverOpenπ U i ≫ D.ιInvAppπEqMap U ≫ D.ιInvApp U = 𝟙 _ := by
  ext j
  -- ⊢ (diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ ιInvApp D U) ≫ limit.π (diagra …
  induction j using Opposite.rec' with | h j => ?_
  -- ⊢ (diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ ιInvApp D U) ≫ limit.π (diagra …
  -- ⊢ (diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ ιInvApp D U) ≫ limit.π (diagra …
  rcases j with (⟨j, k⟩ | ⟨j⟩)
  -- ⊢ (diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ ιInvApp D U) ≫ limit.π (diagra …
  · rw [← limit.w (componentwiseDiagram 𝖣.diagram.multispan _)
        (Quiver.Hom.op (WalkingMultispan.Hom.fst (j, k))),
      ← Category.assoc, Category.id_comp]
    congr 1
    -- ⊢ (diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ ιInvApp D U) ≫ limit.π (compon …
    simp_rw [Category.assoc]
    -- ⊢ diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ ιInvApp D U ≫ limit.π (componen …
    apply π_ιInvApp_π
    -- 🎉 no goals
  · simp_rw [Category.assoc]
    -- ⊢ diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ ιInvApp D U ≫ limit.π (diagramO …
    rw [Category.id_comp]
    -- ⊢ diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ ιInvApp D U ≫ limit.π (diagramO …
    apply π_ιInvApp_π
    -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.glue_data.π_ι_inv_app_eq_id AlgebraicGeometry.PresheafedSpace.GlueData.π_ιInvApp_eq_id

instance componentwise_diagram_π_isIso (i : D.J) (U : Opens (D.U i).carrier) :
    IsIso (D.diagramOverOpenπ U i) := by
  use D.ιInvAppπEqMap U ≫ D.ιInvApp U
  -- ⊢ diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ ιInvApp D U = 𝟙 (limit (diagram …
  constructor
  -- ⊢ diagramOverOpenπ D U i ≫ ιInvAppπEqMap D U ≫ ιInvApp D U = 𝟙 (limit (diagram …
  · apply π_ιInvApp_eq_id
    -- 🎉 no goals
  · rw [Category.assoc, (D.ιInvApp_π _).choose_spec]
    -- ⊢ ιInvAppπEqMap D U ≫ (CategoryTheory.GlueData.U D.toGlueData i).presheaf.map  …
    exact Iso.inv_hom_id ((D.U i).presheaf.mapIso (eqToIso _))
    -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.glue_data.componentwise_diagram_π_IsIso AlgebraicGeometry.PresheafedSpace.GlueData.componentwise_diagram_π_isIso

instance ιIsOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) where
  base_open := D.ι_openEmbedding i
  c_iso U := by erw [← colimitPresheafObjIsoComponentwiseLimit_hom_π]; infer_instance
                -- ⊢ IsIso ((colimitPresheafObjIsoComponentwiseLimit (MultispanIndex.multispan (d …
                                                                       -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.glue_data.ι_IsOpenImmersion AlgebraicGeometry.PresheafedSpace.GlueData.ιIsOpenImmersion

/-- The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.

Vᵢⱼ ⟶ Uᵢ
 |      |
 ↓      ↓
 Uⱼ ⟶ X
-/
def vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j) :=
  PullbackCone.isLimitAux' _ fun s => by
    refine' ⟨_, _, _, _⟩
    · refine' PresheafedSpace.IsOpenImmersion.lift (D.f i j) s.fst _
      -- ⊢ Set.range ↑(PullbackCone.fst s).base ⊆ Set.range ↑(f D.toGlueData i j).base
      erw [← D.toTopGlueData.preimage_range j i]
      -- ⊢ Set.range ↑(PullbackCone.fst s).base ⊆ ↑(ι (toTopGlueData D).toGlueData i) ⁻ …
      have :
        s.fst.base ≫ D.toTopGlueData.ι i =
          s.snd.base ≫ D.toTopGlueData.ι j := by
        rw [← 𝖣.ι_gluedIso_hom (PresheafedSpace.forget _) _, ←
          𝖣.ι_gluedIso_hom (PresheafedSpace.forget _) _]
        have := congr_arg PresheafedSpace.Hom.base s.condition
        rw [comp_base, comp_base] at this
        replace this := reassoc_of% this
        exact this _
      rw [← Set.image_subset_iff, ← Set.image_univ, ← Set.image_comp, Set.image_univ]
      -- ⊢ Set.range (↑(ι (toTopGlueData D).toGlueData i) ∘ ↑(PullbackCone.fst s).base) …
      -- Porting note : change `rw` to `erw`
      erw [← coe_comp]
      -- ⊢ Set.range ↑((PullbackCone.fst s).base ≫ ι (toTopGlueData D).toGlueData i) ⊆  …
      rw [this, coe_comp, ← Set.image_univ, Set.image_comp]
      -- ⊢ ↑(ι (toTopGlueData D).toGlueData j) '' (↑(PullbackCone.snd s).base '' Set.un …
      exact Set.image_subset_range _ _
      -- 🎉 no goals
    · apply IsOpenImmersion.lift_fac
      -- 🎉 no goals
    · rw [← cancel_mono (𝖣.ι j), Category.assoc, ← (𝖣.vPullbackCone i j).condition]
      -- ⊢ IsOpenImmersion.lift (f D.toGlueData i j) (PullbackCone.fst s) (_ : Set.rang …
      conv_rhs => rw [← s.condition]
      -- ⊢ IsOpenImmersion.lift (f D.toGlueData i j) (PullbackCone.fst s) (_ : Set.rang …
      erw [IsOpenImmersion.lift_fac_assoc]
      -- 🎉 no goals
    · intro m e₁ _; rw [← cancel_mono (D.f i j)]; erw [e₁]; rw [IsOpenImmersion.lift_fac]
      -- ⊢ m = IsOpenImmersion.lift (f D.toGlueData i j) (PullbackCone.fst s) (_ : Set. …
                    -- ⊢ m ≫ f D.toGlueData i j = IsOpenImmersion.lift (f D.toGlueData i j) (Pullback …
                                                  -- ⊢ PullbackCone.fst s = IsOpenImmersion.lift (f D.toGlueData i j) (PullbackCone …
                                                            -- 🎉 no goals
#align algebraic_geometry.PresheafedSpace.glue_data.V_pullback_cone_is_limit AlgebraicGeometry.PresheafedSpace.GlueData.vPullbackConeIsLimit

theorem ι_jointly_surjective (x : 𝖣.glued) : ∃ (i : D.J) (y : D.U i), (𝖣.ι i).base y = x :=
  𝖣.ι_jointly_surjective (PresheafedSpace.forget _ ⋙ CategoryTheory.forget TopCat) x
#align algebraic_geometry.PresheafedSpace.glue_data.ι_jointly_surjective AlgebraicGeometry.PresheafedSpace.GlueData.ι_jointly_surjective

end GlueData

end PresheafedSpace

namespace SheafedSpace

variable [HasProducts.{v} C]

/-- A family of gluing data consists of
1. An index type `J`
2. A sheafed space `U i` for each `i : J`.
3. A sheafed space `V i j` for each `i j : J`.
  (Note that this is `J × J → SheafedSpace C` rather than `J → J → SheafedSpace C` to
  connect to the limits library easier.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the spaces `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subspaces of the glued space.
-/
-- Porting note : removed
-- @[nolint has_nonempty_instance]
structure GlueData extends CategoryTheory.GlueData (SheafedSpace.{u, v, v} C) where
  f_open : ∀ i j, SheafedSpace.IsOpenImmersion (f i j)
#align algebraic_geometry.SheafedSpace.glue_data AlgebraicGeometry.SheafedSpaceₓ.GlueData

attribute [instance] GlueData.f_open

namespace GlueData

variable {C}
variable (D : GlueData C)

local notation "𝖣" => D.toGlueData

/-- The glue data of presheafed spaces associated to a family of glue data of sheafed spaces. -/
abbrev toPresheafedSpaceGlueData : PresheafedSpace.GlueData C :=
  { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToPresheafedSpace }
#align algebraic_geometry.SheafedSpace.glue_data.to_PresheafedSpace_glue_data AlgebraicGeometry.SheafedSpaceₓ.GlueData.toPresheafedSpaceGlueData

variable [HasLimits C]

/-- The gluing as sheafed spaces is isomorphic to the gluing as presheafed spaces. -/
abbrev isoPresheafedSpace :
    𝖣.glued.toPresheafedSpace ≅ D.toPresheafedSpaceGlueData.toGlueData.glued :=
  𝖣.gluedIso forgetToPresheafedSpace
#align algebraic_geometry.SheafedSpace.glue_data.iso_PresheafedSpace AlgebraicGeometry.SheafedSpaceₓ.GlueData.isoPresheafedSpace

theorem ι_isoPresheafedSpace_inv (i : D.J) :
    D.toPresheafedSpaceGlueData.toGlueData.ι i ≫ D.isoPresheafedSpace.inv = 𝖣.ι i :=
  𝖣.ι_gluedIso_inv _ _
#align algebraic_geometry.SheafedSpace.glue_data.ι_iso_PresheafedSpace_inv AlgebraicGeometry.SheafedSpaceₓ.GlueData.ι_isoPresheafedSpace_inv

instance ιIsOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) := by
  rw [← D.ι_isoPresheafedSpace_inv]
  -- ⊢ IsOpenImmersion (ι (toPresheafedSpaceGlueData D).toGlueData i ≫ (isoPresheaf …
  -- Porting note : was `inferInstance`
  refine PresheafedSpace.IsOpenImmersion.comp (hf := ?_) (hg := inferInstance)
  -- ⊢ PresheafedSpace.IsOpenImmersion (ι (toPresheafedSpaceGlueData D).toGlueData i)
  apply PresheafedSpace.GlueData.ιIsOpenImmersion
  -- 🎉 no goals
#align algebraic_geometry.SheafedSpace.glue_data.ι_IsOpenImmersion AlgebraicGeometry.SheafedSpaceₓ.GlueData.ιIsOpenImmersion

theorem ι_jointly_surjective (x : 𝖣.glued) : ∃ (i : D.J) (y : D.U i), (𝖣.ι i).base y = x :=
  𝖣.ι_jointly_surjective (SheafedSpace.forget _ ⋙ CategoryTheory.forget TopCat) x
#align algebraic_geometry.SheafedSpace.glue_data.ι_jointly_surjective AlgebraicGeometry.SheafedSpaceₓ.GlueData.ι_jointly_surjective

/-- The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.

Vᵢⱼ ⟶ Uᵢ
 |      |
 ↓      ↓
 Uⱼ ⟶ X
-/
def vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j) :=
  𝖣.vPullbackConeIsLimitOfMap forgetToPresheafedSpace i j
    (D.toPresheafedSpaceGlueData.vPullbackConeIsLimit _ _)
#align algebraic_geometry.SheafedSpace.glue_data.V_pullback_cone_is_limit AlgebraicGeometry.SheafedSpaceₓ.GlueData.vPullbackConeIsLimit

end GlueData

end SheafedSpace

namespace LocallyRingedSpace

/-- A family of gluing data consists of
1. An index type `J`
2. A locally ringed space `U i` for each `i : J`.
3. A locally ringed space `V i j` for each `i j : J`.
  (Note that this is `J × J → LocallyRingedSpace` rather than `J → J → LocallyRingedSpace` to
  connect to the limits library easier.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the spaces `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subspaces of the glued space.
-/
-- Porting note : removed
-- @[nolint has_nonempty_instance]
structure GlueData extends CategoryTheory.GlueData LocallyRingedSpace where
  f_open : ∀ i j, LocallyRingedSpace.IsOpenImmersion (f i j)
#align algebraic_geometry.LocallyRingedSpace.glue_data AlgebraicGeometry.LocallyRingedSpace.GlueData

attribute [instance] GlueData.f_open

namespace GlueData

variable (D : GlueData.{u})

local notation "𝖣" => D.toGlueData

/-- The glue data of ringed spaces associated to a family of glue data of locally ringed spaces. -/
abbrev toSheafedSpaceGlueData : SheafedSpace.GlueData CommRingCat :=
  { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToSheafedSpace }
#align algebraic_geometry.LocallyRingedSpace.glue_data.to_SheafedSpace_glue_data AlgebraicGeometry.LocallyRingedSpace.GlueData.toSheafedSpaceGlueData

/-- The gluing as locally ringed spaces is isomorphic to the gluing as ringed spaces. -/
abbrev isoSheafedSpace : 𝖣.glued.toSheafedSpace ≅ D.toSheafedSpaceGlueData.toGlueData.glued :=
  𝖣.gluedIso forgetToSheafedSpace
#align algebraic_geometry.LocallyRingedSpace.glue_data.iso_SheafedSpace AlgebraicGeometry.LocallyRingedSpace.GlueData.isoSheafedSpace

theorem ι_isoSheafedSpace_inv (i : D.J) :
    D.toSheafedSpaceGlueData.toGlueData.ι i ≫ D.isoSheafedSpace.inv = (𝖣.ι i).1 :=
  𝖣.ι_gluedIso_inv forgetToSheafedSpace i
#align algebraic_geometry.LocallyRingedSpace.glue_data.ι_iso_SheafedSpace_inv AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_isoSheafedSpace_inv

instance ι_isOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) := by
  delta IsOpenImmersion; rw [← D.ι_isoSheafedSpace_inv]
  -- ⊢ SheafedSpace.IsOpenImmersion (ι D.toGlueData i).val
                         -- ⊢ SheafedSpace.IsOpenImmersion (ι (toSheafedSpaceGlueData D).toGlueData i ≫ (i …
  apply (config := { allowSynthFailures := true }) PresheafedSpace.IsOpenImmersion.comp
  -- ⊢ PresheafedSpace.IsOpenImmersion (ι (toSheafedSpaceGlueData D).toGlueData i)
  -- Porting note : this was automatic
  exact (D.toSheafedSpaceGlueData).ιIsOpenImmersion i
  -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.glue_data.ι_IsOpenImmersion AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_isOpenImmersion

instance (i j k : D.J) : PreservesLimit (cospan (𝖣.f i j) (𝖣.f i k)) forgetToSheafedSpace :=
  inferInstance

theorem ι_jointly_surjective (x : 𝖣.glued) : ∃ (i : D.J) (y : D.U i), (𝖣.ι i).1.base y = x :=
  𝖣.ι_jointly_surjective
    ((LocallyRingedSpace.forgetToSheafedSpace.{u} ⋙ SheafedSpace.forget CommRingCatMax.{u, u}) ⋙
      forget TopCat.{u}) x
#align algebraic_geometry.LocallyRingedSpace.glue_data.ι_jointly_surjective AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective

/-- The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.

Vᵢⱼ ⟶ Uᵢ
 |      |
 ↓      ↓
 Uⱼ ⟶ X
-/
def vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j) :=
  𝖣.vPullbackConeIsLimitOfMap forgetToSheafedSpace i j
    (D.toSheafedSpaceGlueData.vPullbackConeIsLimit _ _)
#align algebraic_geometry.LocallyRingedSpace.glue_data.V_pullback_cone_is_limit AlgebraicGeometry.LocallyRingedSpace.GlueData.vPullbackConeIsLimit

end GlueData

end LocallyRingedSpace

end AlgebraicGeometry
