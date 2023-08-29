/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.AlgebraicGeometry.PresheafedSpace
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Sheaves.Limits

#align_import algebraic_geometry.presheafed_space.has_colimits from "leanprover-community/mathlib"@"178a32653e369dce2da68dc6b2694e385d484ef1"

/-!
# `PresheafedSpace C` has colimits.

If `C` has limits, then the category `PresheafedSpace C` has colimits,
and the forgetful functor to `TopCat` preserves these colimits.

When restricted to a diagram where the underlying continuous maps are open embeddings,
this says that we can glue presheaved spaces.

Given a diagram `F : J ⥤ PresheafedSpace C`,
we first build the colimit of the underlying topological spaces,
as `colimit (F ⋙ PresheafedSpace.forget C)`. Call that colimit space `X`.

Our strategy is to push each of the presheaves `F.obj j`
forward along the continuous map `colimit.ι (F ⋙ PresheafedSpace.forget C) j` to `X`.
Since pushforward is functorial, we obtain a diagram `J ⥤ (presheaf C X)ᵒᵖ`
of presheaves on a single space `X`.
(Note that the arrows now point the other direction,
because this is the way `PresheafedSpace C` is set up.)

The limit of this diagram then constitutes the colimit presheaf.
-/


noncomputable section

universe v' u' v u

open CategoryTheory Opposite CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Limits
  TopCat TopCat.Presheaf TopologicalSpace

variable {J : Type u'} [Category.{v'} J] {C : Type u} [Category.{v} C]

namespace AlgebraicGeometry

namespace PresheafedSpace

attribute [local simp] eqToHom_map

-- Porting note: we used to have:
-- local attribute [tidy] tactic.auto_cases_opens
-- We would replace this by:
-- attribute [local aesop safe cases (rule_sets [CategoryTheory])] Opens
-- although it doesn't appear to help in this file, in any case.

@[simp]
theorem map_id_c_app (F : J ⥤ PresheafedSpace.{_, _, v} C) (j) (U) :
    (F.map (𝟙 j)).c.app (op U) =
      (Pushforward.id (F.obj j).presheaf).inv.app (op U) ≫
        (pushforwardEq (by simp) (F.obj j).presheaf).hom.app
                           -- 🎉 no goals
          (op U) := by
  cases U
  -- ⊢ NatTrans.app (F.map (𝟙 j)).c (op { carrier := carrier✝, is_open' := is_open' …
  simp [PresheafedSpace.congr_app (F.map_id j)]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.map_id_c_app AlgebraicGeometry.PresheafedSpace.map_id_c_app

@[simp]
theorem map_comp_c_app (F : J ⥤ PresheafedSpace.{_, _, v} C) {j₁ j₂ j₃}
    (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃) (U) :
    (F.map (f ≫ g)).c.app (op U) =
      (F.map g).c.app (op U) ≫
        (pushforwardMap (F.map g).base (F.map f).c).app (op U) ≫
          (Pushforward.comp (F.obj j₁).presheaf (F.map f).base (F.map g).base).inv.app (op U) ≫
            (pushforwardEq (by rw [F.map_comp]; rfl) _).hom.app
                               -- ⊢ (F.map f).base ≫ (F.map g).base = (F.map f ≫ F.map g).base
                                                -- 🎉 no goals
              _ := by
  cases U
  -- ⊢ NatTrans.app (F.map (f ≫ g)).c (op { carrier := carrier✝, is_open' := is_ope …
  simp [PresheafedSpace.congr_app (F.map_comp f g)]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.map_comp_c_app AlgebraicGeometry.PresheafedSpace.map_comp_c_app

-- See note [dsimp, simp]
/-- Given a diagram of `PresheafedSpace C`s, its colimit is computed by pushing the sheaves onto
the colimit of the underlying spaces, and taking componentwise limit.
This is the componentwise diagram for an open set `U` of the colimit of the underlying spaces.
-/
@[simps]
def componentwiseDiagram (F : J ⥤ PresheafedSpace.{_, _, v} C) [HasColimit F]
    (U : Opens (Limits.colimit F).carrier) : Jᵒᵖ ⥤ C where
  obj j := (F.obj (unop j)).presheaf.obj (op ((Opens.map (colimit.ι F (unop j)).base).obj U))
  map {j k} f := (F.map f.unop).c.app _ ≫
    (F.obj (unop k)).presheaf.map (eqToHom (by rw [← colimit.w F f.unop, comp_base]; rfl))
                                               -- ⊢ (Opens.map (F.map f.unop).base).op.obj (op ((Opens.map (colimit.ι F j.unop). …
                                                                                     -- 🎉 no goals
  map_comp {i j k} f g := by
    dsimp
    -- ⊢ NatTrans.app (F.map (g.unop ≫ f.unop)).c (op ((Opens.map (colimit.ι F i.unop …
    simp_rw [map_comp_c_app]
    -- ⊢ (NatTrans.app (F.map f.unop).c (op ((Opens.map (colimit.ι F i.unop).base).ob …
    simp only [op_obj, unop_op, eqToHom_op, id_eq, id_comp, assoc, eqToHom_trans]
    -- ⊢ NatTrans.app (F.map f.unop).c (op ((Opens.map (colimit.ι F i.unop).base).obj …
    congr 1
    -- ⊢ NatTrans.app (pushforwardMap (F.map f.unop).base (F.map g.unop).c) (op ((Ope …
    rw [TopCat.Presheaf.Pushforward.comp_inv_app, TopCat.Presheaf.pushforwardEq_hom_app,
      CategoryTheory.NatTrans.naturality_assoc, TopCat.Presheaf.pushforwardMap_app]
    -- ⊢ NatTrans.app (F.map (𝟙 x.unop)).c (op ((Opens.map (colimit.ι F x.unop).base) …
    congr 1
    -- ⊢ 𝟙 (((F.map f.unop).base _* ((F.map g.unop).base _* (F.obj k.unop).presheaf)) …
    simp
    -- 🎉 no goals
    -- ⊢ (F.obj x.unop).presheaf.map (𝟙 (op { carrier := ((Opens.map (colimit.ι F x.u …
  map_id x := by
    -- 🎉 no goals
    dsimp
    simp [map_id_c_app, pushforwardObj_obj, op_obj, unop_op, pushforwardEq_hom_app, eqToHom_op,
      id_eq, eqToHom_map, assoc, eqToHom_trans, eqToHom_refl, comp_id,
      TopCat.Presheaf.Pushforward.id_inv_app']
    rw [TopCat.Presheaf.Pushforward.id_inv_app']
    simp only [Opens.carrier_eq_coe, Opens.mk_coe, map_id]
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.componentwise_diagram AlgebraicGeometry.PresheafedSpace.componentwiseDiagram

variable [HasColimitsOfShape J TopCat.{v}]

/-- Given a diagram of presheafed spaces,
we can push all the presheaves forward to the colimit `X` of the underlying topological spaces,
obtaining a diagram in `(Presheaf C X)ᵒᵖ`.
-/
@[simps]
def pushforwardDiagramToColimit (F : J ⥤ PresheafedSpace.{_, _, v} C) :
    J ⥤ (Presheaf C (colimit (F ⋙ PresheafedSpace.forget C)))ᵒᵖ where
  obj j := op (colimit.ι (F ⋙ PresheafedSpace.forget C) j _* (F.obj j).presheaf)
  map {j j'} f :=
    (pushforwardMap (colimit.ι (F ⋙ PresheafedSpace.forget C) j') (F.map f).c ≫
        (Pushforward.comp (F.obj j).presheaf ((F ⋙ PresheafedSpace.forget C).map f)
              (colimit.ι (F ⋙ PresheafedSpace.forget C) j')).inv ≫
          (pushforwardEq (colimit.w (F ⋙ PresheafedSpace.forget C) f) (F.obj j).presheaf).hom).op
  map_id j := by
    apply (opEquiv _ _).injective
    -- ⊢ ↑(opEquiv ({ obj := fun j => op (colimit.ι (F ⋙ forget C) j _* (F.obj j).pre …
    refine NatTrans.ext _ _ (funext fun U => ?_)
    -- ⊢ NatTrans.app (↑(opEquiv ({ obj := fun j => op (colimit.ι (F ⋙ forget C) j _* …
    induction U with
    | h U =>
      rcases U with ⟨U, hU⟩
      dsimp [comp_obj, forget_obj, Functor.comp_map, forget_map, op_comp, unop_op,
        pushforwardObj_obj, op_obj, Opens.map_obj, opEquiv, Equiv.coe_fn_mk, unop_comp,
        Quiver.Hom.unop_op, unop_id]
      -- Porting note : some `simp` lemmas are not picked up
      rw [NatTrans.comp_app, pushforwardMap_app, NatTrans.id_app]
      simp only [op_obj, unop_op, Opens.map_obj, map_id_c_app, Opens.map_id_obj',
        map_id, pushforwardEq_hom_app, eqToHom_op, id_eq, eqToHom_map, id_comp,
        TopCat.Presheaf.Pushforward.id_inv_app']
      rw [NatTrans.comp_app, Pushforward.comp_inv_app, id_comp]
      dsimp
      simp
  map_comp {j₁ j₂ j₃} f g := by
    apply (opEquiv _ _).injective
    -- ⊢ ↑(opEquiv ({ obj := fun j => op (colimit.ι (F ⋙ forget C) j _* (F.obj j).pre …
    refine NatTrans.ext _ _ (funext fun U => ?_)
    -- ⊢ NatTrans.app (↑(opEquiv ({ obj := fun j => op (colimit.ι (F ⋙ forget C) j _* …
    dsimp only [comp_obj, forget_obj, Functor.comp_map, forget_map, op_comp, unop_op,
      pushforwardObj_obj, op_obj, opEquiv, Equiv.coe_fn_mk, unop_comp, Quiver.Hom.unop_op]
    -- Porting note : some `simp` lemmas are not picked up
    rw [NatTrans.comp_app, pushforwardMap_app, NatTrans.comp_app, Pushforward.comp_inv_app,
      id_comp, pushforwardEq_hom_app, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
      pushforwardMap_app, Pushforward.comp_inv_app, id_comp, pushforwardEq_hom_app,
      NatTrans.comp_app, NatTrans.comp_app, pushforwardEq_hom_app, Pushforward.comp_inv_app,
      id_comp, pushforwardMap_app]
    simp only [pushforwardObj_obj, op_obj, unop_op, map_comp_c_app, pushforwardMap_app,
      Opens.map_comp_obj, Pushforward.comp_inv_app, pushforwardEq_hom_app, eqToHom_op, id_eq,
      eqToHom_map, id_comp, assoc, eqToHom_trans]
    dsimp
    -- ⊢ NatTrans.app (F.map g).c (op ((Opens.map (colimit.ι (F ⋙ forget C) j₃)).obj  …
    congr 1
    -- ⊢ NatTrans.app (F.map f).c (op ((Opens.map (F.map g).base).obj ((Opens.map (co …
    -- The key fact is `(F.map f).c.congr`,
    -- which allows us in rewrite in the argument of `(F.map f).c.app`.
    rw [@NatTrans.congr (α := (F.map f).c)
      (op ((Opens.map (F.map g).base).obj ((Opens.map (colimit.ι (F ⋙ forget C) j₃)).obj U.unop)))
      (op ((Opens.map (colimit.ι (F ⋙ PresheafedSpace.forget C) j₂)).obj (unop U)))
      _]
    swap
    -- ⊢ op ((Opens.map (F.map g).base).obj ((Opens.map (colimit.ι (F ⋙ forget C) j₃) …
    -- Now we show the open sets are equal.
    · apply unop_injective
      -- ⊢ (op ((Opens.map (F.map g).base).obj ((Opens.map (colimit.ι (F ⋙ forget C) j₃ …
      rw [← Opens.map_comp_obj]
      -- ⊢ (op ((Opens.map ((F.map g).base ≫ colimit.ι (F ⋙ forget C) j₃)).obj U.unop)) …
      congr
      -- ⊢ (F.map g).base ≫ colimit.ι (F ⋙ forget C) j₃ = colimit.ι (F ⋙ forget C) j₂
      exact colimit.w (F ⋙ PresheafedSpace.forget C) g
      -- 🎉 no goals
    -- Finally, the original goal is now easy:
    simp
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.pushforward_diagram_to_colimit AlgebraicGeometry.PresheafedSpace.pushforwardDiagramToColimit

variable [∀ X : TopCat.{v}, HasLimitsOfShape Jᵒᵖ (X.Presheaf C)]

/-- Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.instHasColimits`.
-/
def colimit (F : J ⥤ PresheafedSpace.{_, _, v} C) : PresheafedSpace C where
  carrier := Limits.colimit (F ⋙ PresheafedSpace.forget C)
  presheaf := limit (pushforwardDiagramToColimit F).leftOp
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.colimit AlgebraicGeometry.PresheafedSpace.colimit

@[simp]
theorem colimit_carrier (F : J ⥤ PresheafedSpace.{_, _, v} C) :
    (colimit F).carrier = Limits.colimit (F ⋙ PresheafedSpace.forget C) :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.colimit_carrier AlgebraicGeometry.PresheafedSpace.colimit_carrier

@[simp]
theorem colimit_presheaf (F : J ⥤ PresheafedSpace.{_, _, v} C) :
    (colimit F).presheaf = limit (pushforwardDiagramToColimit F).leftOp :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.colimit_presheaf AlgebraicGeometry.PresheafedSpace.colimit_presheaf

/-- Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.instHasColimits`.
-/
@[simps]
def colimitCocone (F : J ⥤ PresheafedSpace.{_, _, v} C) : Cocone F where
  pt := colimit F
  ι :=
    { app := fun j =>
        { base := colimit.ι (F ⋙ PresheafedSpace.forget C) j
          c := limit.π _ (op j) }
      naturality := fun {j j'} f => by
        ext1
        -- ⊢ (F.map f ≫ (fun j => { base := colimit.ι (F ⋙ forget C) j, c := limit.π (pus …
        · ext x
          -- ⊢ ↑(F.map f ≫ (fun j => { base := colimit.ι (F ⋙ forget C) j, c := limit.π (pu …
          exact colimit.w_apply (F ⋙ PresheafedSpace.forget C) f x
          -- 🎉 no goals
        · ext ⟨U, hU⟩
          -- ⊢ NatTrans.app ((F.map f ≫ (fun j => { base := colimit.ι (F ⋙ forget C) j, c : …
          dsimp
          -- ⊢ NatTrans.app ((F.map f ≫ { base := colimit.ι (F ⋙ forget C) j', c := limit.π …
          rw [PresheafedSpace.id_c_app, map_id]
          -- ⊢ NatTrans.app ((F.map f ≫ { base := colimit.ι (F ⋙ forget C) j', c := limit.π …
          erw [id_comp]
          -- ⊢ NatTrans.app ((F.map f ≫ { base := colimit.ι (F ⋙ forget C) j', c := limit.π …
          rw [NatTrans.comp_app, PresheafedSpace.comp_c_app, whiskerRight_app, eqToHom_app,
            ← congr_arg NatTrans.app (limit.w (pushforwardDiagramToColimit F).leftOp f.op),
            NatTrans.comp_app, Functor.leftOp_map, pushforwardDiagramToColimit_map]
          dsimp
          -- ⊢ (NatTrans.app (limit.π (pushforwardDiagramToColimit F).leftOp (op j')) (op { …
          rw [NatTrans.comp_app, NatTrans.comp_app, pushforwardEq_hom_app, id.def, eqToHom_op,
            Pushforward.comp_inv_app, id_comp, pushforwardMap_app, ←assoc]
          congr 1 }
          -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.colimit_cocone AlgebraicGeometry.PresheafedSpace.colimitCocone

variable [HasLimitsOfShape Jᵒᵖ C]

namespace ColimitCoconeIsColimit

/-- Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.colimitCoconeIsColimit`.
-/
def descCApp (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) (U : (Opens s.pt.carrier)ᵒᵖ) :
    s.pt.presheaf.obj U ⟶
      (colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s) _*
            limit (pushforwardDiagramToColimit F).leftOp).obj
        U := by
  refine'
    limit.lift _
        { pt := s.pt.presheaf.obj U
          π :=
            { app := fun j => _
              naturality := fun j j' f => _ } } ≫
      (limitObjIsoLimitCompEvaluation _ _).inv
  -- We still need to construct the `app` and `naturality'` fields omitted above.
  · refine' (s.ι.app (unop j)).c.app U ≫ (F.obj (unop j)).presheaf.map (eqToHom _)
    -- ⊢ (Opens.map (NatTrans.app s.ι j.unop).base).op.obj U = (Opens.map (colimit.ι  …
    dsimp
    -- ⊢ op ((Opens.map (NatTrans.app s.ι j.unop).base).obj U.unop) = op ((Opens.map  …
    rw [← Opens.map_comp_obj]
    -- ⊢ op ((Opens.map (NatTrans.app s.ι j.unop).base).obj U.unop) = op ((Opens.map  …
    simp
    -- 🎉 no goals
  · dsimp
    -- ⊢ 𝟙 (s.pt.presheaf.obj U) ≫ NatTrans.app (NatTrans.app s.ι j'.unop).c U ≫ (F.o …
    rw [PresheafedSpace.congr_app (s.w f.unop).symm U]
    -- ⊢ 𝟙 (s.pt.presheaf.obj U) ≫ (NatTrans.app (F.map f.unop ≫ NatTrans.app s.ι j.u …
    have w :=
      Functor.congr_obj
        (congr_arg Opens.map (colimit.ι_desc ((PresheafedSpace.forget C).mapCocone s) (unop j)))
        (unop U)
    simp only [Opens.map_comp_obj_unop] at w
    -- ⊢ 𝟙 (s.pt.presheaf.obj U) ≫ (NatTrans.app (F.map f.unop ≫ NatTrans.app s.ι j.u …
    replace w := congr_arg op w
    -- ⊢ 𝟙 (s.pt.presheaf.obj U) ≫ (NatTrans.app (F.map f.unop ≫ NatTrans.app s.ι j.u …
    have w' := NatTrans.congr (F.map f.unop).c w
    -- ⊢ 𝟙 (s.pt.presheaf.obj U) ≫ (NatTrans.app (F.map f.unop ≫ NatTrans.app s.ι j.u …
    rw [w']
    -- ⊢ 𝟙 (s.pt.presheaf.obj U) ≫ (NatTrans.app (F.map f.unop ≫ NatTrans.app s.ι j.u …
    simp
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc_c_app AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.descCApp

theorem desc_c_naturality (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F)
    {U V : (Opens s.pt.carrier)ᵒᵖ} (i : U ⟶ V) :
    s.pt.presheaf.map i ≫ descCApp F s V =
      descCApp F s U ≫
        (colimit.desc (F ⋙ forget C) ((forget C).mapCocone s) _* (colimitCocone F).pt.presheaf).map
          i := by
  dsimp [descCApp]
  -- ⊢ s.pt.presheaf.map i ≫ limit.lift ((pushforwardDiagramToColimit F).leftOp ⋙ ( …
  refine limit_obj_ext (fun j => ?_)
  -- ⊢ (s.pt.presheaf.map i ≫ limit.lift ((pushforwardDiagramToColimit F).leftOp ⋙  …
  simp only [limit.lift_π, NatTrans.naturality, limit.lift_π_assoc, eqToHom_map, assoc,
    pushforwardObj_map, NatTrans.naturality_assoc, op_map,
    limitObjIsoLimitCompEvaluation_inv_π_app_assoc,
    limitObjIsoLimitCompEvaluation_inv_π_app]
  dsimp
  -- ⊢ NatTrans.app (NatTrans.app s.ι j.unop).c U ≫ (F.obj j.unop).presheaf.map ((O …
  have w :=
    Functor.congr_hom
      (congr_arg Opens.map (colimit.ι_desc ((PresheafedSpace.forget C).mapCocone s) (unop j)))
      i.unop
  simp only [Opens.map_comp_map] at w
  -- ⊢ NatTrans.app (NatTrans.app s.ι j.unop).c U ≫ (F.obj j.unop).presheaf.map ((O …
  replace w := congr_arg Quiver.Hom.op w
  -- ⊢ NatTrans.app (NatTrans.app s.ι j.unop).c U ≫ (F.obj j.unop).presheaf.map ((O …
  rw [w]
  -- ⊢ NatTrans.app (NatTrans.app s.ι j.unop).c U ≫ (F.obj j.unop).presheaf.map ((O …
  simp
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc_c_naturality AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.desc_c_naturality

/-- Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.colimitCoconeIsColimit`.
-/
def desc (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) : colimit F ⟶ s.pt where
  base := colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s)
  c :=
    { app := fun U => descCApp F s U
      naturality := fun _ _ i => desc_c_naturality F s i }
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.desc

theorem desc_fac (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) (j : J) :
    (colimitCocone F).ι.app j ≫ desc F s = s.ι.app j := by
  ext U
  -- ⊢ ↑(NatTrans.app (colimitCocone F).ι j ≫ desc F s).base U = ↑(NatTrans.app s.ι …
  · simp [desc]
    -- 🎉 no goals
  · -- Porting note : the original proof is just `ext; dsimp [desc, descCApp]; simpa`,
    -- but this has to be expanded a bit
    rw [NatTrans.comp_app, PresheafedSpace.comp_c_app, whiskerRight_app]
    -- ⊢ (NatTrans.app (desc F s).c (op U) ≫ NatTrans.app (NatTrans.app (colimitCocon …
    dsimp [desc, descCApp]
    -- ⊢ ((limit.lift ((pushforwardDiagramToColimit F).leftOp ⋙ (evaluation (Opens ↑( …
    simp only [eqToHom_app, op_obj, Opens.map_comp_obj, eqToHom_map, Functor.leftOp, assoc]
    -- ⊢ limit.lift (CategoryTheory.Functor.mk { obj := fun X => ((pushforwardDiagram …
    rw [limitObjIsoLimitCompEvaluation_inv_π_app_assoc]
    -- ⊢ limit.lift (CategoryTheory.Functor.mk { obj := fun X => ((pushforwardDiagram …
    simp
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc_fac AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.desc_fac

end ColimitCoconeIsColimit

open ColimitCoconeIsColimit

/-- Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.instHasColimits`.
-/
def colimitCoconeIsColimit (F : J ⥤ PresheafedSpace.{_, _, v} C) :
    IsColimit (colimitCocone F) where
  desc s := desc F s
  fac s := desc_fac F s
  uniq s m w := by
    -- We need to use the identity on the continuous maps twice, so we prepare that first:
    have t :
      m.base =
        colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s) := by
      dsimp
      ext j
      rw [colimit.ι_desc, mapCocone_ι_app, ← w j]
      simp
    ext : 1
    -- ⊢ m.base = ((fun s => desc F s) s).base
    · exact t
      -- 🎉 no goals
    · refine NatTrans.ext _ _ (funext fun U => limit_obj_ext fun j => ?_)
      -- ⊢ NatTrans.app (m.c ≫ whiskerRight (eqToHom (_ : (Opens.map m.base).op = (Open …
      dsimp only [colimitCocone_pt, colimit_carrier, leftOp_obj, pushforwardDiagramToColimit_obj,
        comp_obj, forget_obj, unop_op, op_obj, desc, colimit_presheaf, descCApp, mapCocone_pt,
        pushforwardObj_obj, const_obj_obj, id_eq, evaluation_obj_obj, Eq.ndrec, eq_mpr_eq_cast]
      rw [NatTrans.comp_app, whiskerRight_app]
      -- ⊢ (NatTrans.app m.c U ≫ (limit (pushforwardDiagramToColimit F).leftOp).map (Na …
      simp only [pushforwardObj_obj, op_obj, comp_obj, eqToHom_app, eqToHom_map, assoc,
        limitObjIsoLimitCompEvaluation_inv_π_app, limit.lift_π]
      rw [PresheafedSpace.congr_app (w (unop j)).symm U]
      -- ⊢ NatTrans.app m.c U ≫ eqToHom (_ : (limit (pushforwardDiagramToColimit F).lef …
      dsimp
      -- ⊢ NatTrans.app m.c U ≫ eqToHom (_ : (limit (pushforwardDiagramToColimit F).lef …
      have w := congr_arg op (Functor.congr_obj (congr_arg Opens.map t) (unop U))
      -- ⊢ NatTrans.app m.c U ≫ eqToHom (_ : (limit (pushforwardDiagramToColimit F).lef …
      rw [NatTrans.congr (limit.π (pushforwardDiagramToColimit F).leftOp j) w]
      -- ⊢ NatTrans.app m.c U ≫ eqToHom (_ : (limit (pushforwardDiagramToColimit F).lef …
      simp
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit AlgebraicGeometry.PresheafedSpace.colimitCoconeIsColimit

instance : HasColimitsOfShape J (PresheafedSpace.{_, _, v} C) where
  has_colimit F := ⟨colimitCocone F, colimitCoconeIsColimit F⟩

instance : PreservesColimitsOfShape J (PresheafedSpace.forget.{u, v, v} C) :=
  ⟨fun {F} => preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit F) <| by
    apply IsColimit.ofIsoColimit (colimit.isColimit _)
    -- ⊢ colimit.cocone (F ⋙ forget C) ≅ (forget C).mapCocone (colimitCocone F)
    fapply Cocones.ext
    -- ⊢ (colimit.cocone (F ⋙ forget C)).pt ≅ ((forget C).mapCocone (colimitCocone F) …
    · rfl
      -- 🎉 no goals
    · intro j
      -- ⊢ NatTrans.app (colimit.cocone (F ⋙ forget C)).ι j ≫ (Iso.refl (colimit.cocone …
      simp⟩
      -- 🎉 no goals

/-- When `C` has limits, the category of presheaved spaces with values in `C` itself has colimits.
-/
instance instHasColimits [HasLimits C] : HasColimits (PresheafedSpace.{_, _, v} C) :=
  ⟨fun {_ _} => ⟨fun {F} => ⟨colimitCocone F, colimitCoconeIsColimit F⟩⟩⟩

/-- The underlying topological space of a colimit of presheaved spaces is
the colimit of the underlying topological spaces.
-/
instance forgetPreservesColimits [HasLimits C] : PreservesColimits (PresheafedSpace.forget C) where
  preservesColimitsOfShape {J 𝒥} :=
    { preservesColimit := fun {F} =>
        preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit F)
          (by apply IsColimit.ofIsoColimit (colimit.isColimit _)
              -- ⊢ colimit.cocone (F ⋙ forget C) ≅ (forget C).mapCocone (colimitCocone F)
              fapply Cocones.ext
              -- ⊢ (colimit.cocone (F ⋙ forget C)).pt ≅ ((forget C).mapCocone (colimitCocone F) …
              · rfl
                -- 🎉 no goals
              · intro j
                -- ⊢ NatTrans.app (colimit.cocone (F ⋙ forget C)).ι j ≫ (Iso.refl (colimit.cocone …
                simp) }
                -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.forget_preserves_colimits AlgebraicGeometry.PresheafedSpace.forgetPreservesColimits

/-- The components of the colimit of a diagram of `PresheafedSpace C` is obtained
via taking componentwise limits.
-/
def colimitPresheafObjIsoComponentwiseLimit (F : J ⥤ PresheafedSpace.{_, _, v} C) [HasColimit F]
    (U : Opens (Limits.colimit F).carrier) :
    (Limits.colimit F).presheaf.obj (op U) ≅ limit (componentwiseDiagram F U) := by
  refine'
    ((sheafIsoOfIso (colimit.isoColimitCocone ⟨_, colimitCoconeIsColimit F⟩).symm).app
          (op U)).trans
      _
  refine' (limitObjIsoLimitCompEvaluation _ _).trans (Limits.lim.mapIso _)
  -- ⊢ (pushforwardDiagramToColimit F).leftOp ⋙ (evaluation (Opens ↑↑{ cocone := co …
  fapply NatIso.ofComponents
  -- ⊢ (X : Jᵒᵖ) → ((pushforwardDiagramToColimit F).leftOp ⋙ (evaluation (Opens ↑↑{ …
  · intro X
    -- ⊢ ((pushforwardDiagramToColimit F).leftOp ⋙ (evaluation (Opens ↑↑{ cocone := c …
    refine' (F.obj (unop X)).presheaf.mapIso (eqToIso _)
    -- ⊢ (Opens.map (colimit.ι (F ⋙ forget C) X.unop)).op.obj ((Opens.map (colimit.is …
    simp only [Functor.op_obj, unop_op, op_inj_iff, Opens.map_coe, SetLike.ext'_iff,
      Set.preimage_preimage]
    refine congr_arg (Set.preimage . U.1) (funext fun x => ?_)
    -- ⊢ ↑(colimit.isoColimitCocone { cocone := colimitCocone F, isColimit := colimit …
    erw [←comp_app]
    -- ⊢ ↑(colimit.ι (F ⋙ forget C) X.unop ≫ (colimit.isoColimitCocone { cocone := co …
    congr
    -- ⊢ colimit.ι (F ⋙ forget C) X.unop ≫ (colimit.isoColimitCocone { cocone := coli …
    exact ι_preservesColimitsIso_inv (forget C) F (unop X)
    -- 🎉 no goals
  · intro X Y f
    -- ⊢ ((pushforwardDiagramToColimit F).leftOp ⋙ (evaluation (Opens ↑↑{ cocone := c …
    change ((F.map f.unop).c.app _ ≫ _ ≫ _) ≫ (F.obj (unop Y)).presheaf.map _ = _ ≫ _
    -- ⊢ (NatTrans.app (F.map f.unop).c ((Opens.map (colimit.ι (F ⋙ forget C) X.unop) …
    rw [TopCat.Presheaf.Pushforward.comp_inv_app]
    -- ⊢ (NatTrans.app (F.map f.unop).c ((Opens.map (colimit.ι (F ⋙ forget C) X.unop) …
    erw [Category.id_comp]
    -- ⊢ (NatTrans.app (F.map f.unop).c ((Opens.map (colimit.ι (F ⋙ forget C) X.unop) …
    rw [Category.assoc]
    -- ⊢ NatTrans.app (F.map f.unop).c ((Opens.map (colimit.ι (F ⋙ forget C) X.unop)) …
    erw [← (F.obj (unop Y)).presheaf.map_comp, (F.map f.unop).c.naturality_assoc,
      ←(F.obj (unop Y)).presheaf.map_comp]
    rfl
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit AlgebraicGeometry.PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit

@[simp]
theorem colimitPresheafObjIsoComponentwiseLimit_inv_ι_app (F : J ⥤ PresheafedSpace.{_, _, v} C)
    (U : Opens (Limits.colimit F).carrier) (j : J) :
    (colimitPresheafObjIsoComponentwiseLimit F U).inv ≫ (colimit.ι F j).c.app (op U) =
      limit.π _ (op j) := by
  delta colimitPresheafObjIsoComponentwiseLimit
  -- ⊢ ((sheafIsoOfIso (colimit.isoColimitCocone { cocone := colimitCocone F, isCol …
  rw [Iso.trans_inv, Iso.trans_inv, Iso.app_inv, sheafIsoOfIso_inv, pushforwardToOfIso_app,
    congr_app (Iso.symm_inv _)]
  dsimp
  -- ⊢ ((limMap (NatIso.ofComponents fun X => (F.obj X.unop).presheaf.mapIso (eqToI …
  rw [map_id, comp_id, assoc, assoc, assoc, NatTrans.naturality]
  -- ⊢ limMap (NatIso.ofComponents fun X => (F.obj X.unop).presheaf.mapIso (eqToIso …
  erw [← comp_c_app_assoc]
  -- ⊢ limMap (NatIso.ofComponents fun X => (F.obj X.unop).presheaf.mapIso (eqToIso …
  rw [congr_app (colimit.isoColimitCocone_ι_hom _ _), assoc]
  -- ⊢ limMap (NatIso.ofComponents fun X => (F.obj X.unop).presheaf.mapIso (eqToIso …
  erw [limitObjIsoLimitCompEvaluation_inv_π_app_assoc, limMap_π_assoc]
  -- ⊢ limit.π (componentwiseDiagram F U) (op j) ≫ NatTrans.app (NatIso.ofComponent …
  -- Porting note : `convert` doesn't work due to meta variable, so change to a `suffices` block
  set f := _
  -- ⊢ limit.π (componentwiseDiagram F U) (op j) ≫ NatTrans.app (NatIso.ofComponent …
  change _ ≫ f = _
  -- ⊢ limit.π (componentwiseDiagram F U) (op j) ≫ f = limit.π (componentwiseDiagra …
  suffices f_eq : f = 𝟙 _ by rw [f_eq, comp_id]
  -- ⊢ f = 𝟙 ((componentwiseDiagram F U).obj (op j))
  erw [← (F.obj j).presheaf.map_id]
  -- ⊢ f = (F.obj j).presheaf.map (𝟙 (op ((Opens.map (colimit.ι F (op j).unop).base …
  change (F.obj j).presheaf.map _ ≫ _ = _
  -- ⊢ (F.obj j).presheaf.map (eqToIso (_ : (Opens.map (colimit.ι (F ⋙ forget C) (o …
  erw [← (F.obj j).presheaf.map_comp, ← (F.obj j).presheaf.map_comp]
  -- ⊢ (F.obj j).presheaf.map ((eqToIso (_ : (Opens.map (colimit.ι (F ⋙ forget C) ( …
  congr 1
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit_inv_ι_app AlgebraicGeometry.PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_inv_ι_app

@[simp]
theorem colimitPresheafObjIsoComponentwiseLimit_hom_π (F : J ⥤ PresheafedSpace.{_, _, v} C)
    (U : Opens (Limits.colimit F).carrier) (j : J) :
    (colimitPresheafObjIsoComponentwiseLimit F U).hom ≫ limit.π _ (op j) =
      (colimit.ι F j).c.app (op U) :=
  by rw [← Iso.eq_inv_comp, colimitPresheafObjIsoComponentwiseLimit_inv_ι_app]
     -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit_hom_π AlgebraicGeometry.PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π

end PresheafedSpace

end AlgebraicGeometry
