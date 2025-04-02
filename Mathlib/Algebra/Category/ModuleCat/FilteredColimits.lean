/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# The forgetful functor from `R`-modules preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a ring `R`, a small filtered category `J` and a functor
`F : J ⥤ ModuleCat R`. We show that the colimit of `F ⋙ forget₂ (ModuleCat R) AddCommGrp`
(in `AddCommGrp`) carries the structure of an `R`-module, thereby showing that the forgetful
functor `forget₂ (ModuleCat R) AddCommGrp` preserves filtered colimits. In particular, this
implies that `forget (ModuleCat R)` preserves filtered colimits.

-/


universe v u

noncomputable section

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.IsFiltered renaming max → max' -- avoid name collision with `_root_.max`.

namespace ModuleCat.FilteredColimits

section

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ ModuleCat.{max v u, u} R)

/-- The colimit of `F ⋙ forget₂ (ModuleCat R) AddCommGrp` in the category `AddCommGrp`.
In the following, we will show that this has the structure of an `R`-module.
-/
abbrev M : AddCommGrp :=
  AddCommGrp.FilteredColimits.colimit.{v, u}
    (F ⋙ forget₂ (ModuleCat R) AddCommGrp.{max v u})

/-- The canonical projection into the colimit, as a quotient type. -/
abbrev M.mk : (Σ j, F.obj j) → M F :=
  fun x ↦ (F ⋙ forget (ModuleCat R)).ιColimitType  x.1 x.2

theorem M.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) : M.mk F x = M.mk F y :=
  Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel
    (F ⋙ forget (ModuleCat R)) x y h)

/-- The "unlifted" version of scalar multiplication in the colimit. -/
def colimitSMulAux (r : R) (x : Σ j, F.obj j) : M F :=
  M.mk F ⟨x.1, r • x.2⟩

theorem colimitSMulAux_eq_of_rel (r : R) (x y : Σ j, F.obj j)
    (h : Types.FilteredColimit.Rel (F ⋙ forget (ModuleCat R)) x y) :
    colimitSMulAux F r x = colimitSMulAux F r y := by
  apply M.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  simp only [Functor.comp_obj, Functor.comp_map, forget_map] at hfg
  simp [hfg]

/-- Scalar multiplication in the colimit. See also `colimitSMulAux`. -/
instance colimitHasSMul : SMul R (M F) where
  smul r x := by
    refine Quot.lift (colimitSMulAux F r) ?_ x
    intro x y h
    apply colimitSMulAux_eq_of_rel
    apply Types.FilteredColimit.rel_of_colimitTypeRel
    exact h

lemma colimit_zero_eq (j : J) :
    0 = M.mk F ⟨j, 0⟩ := by
  apply AddMonCat.FilteredColimits.colimit_zero_eq

lemma colimit_add_mk_eq (x y : Σ j, F.obj j) (k : J)
    (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    M.mk _ x + M.mk _ y = M.mk _ ⟨k, F.map f x.2 + F.map g y.2⟩ := by
  apply AddMonCat.FilteredColimits.colimit_add_mk_eq

@[simp]
theorem colimit_smul_mk_eq (r : R) (x : Σ j, F.obj j) : r • M.mk F x = M.mk F ⟨x.1, r • x.2⟩ :=
  rfl

private theorem colimitModule.one_smul (x : (M F)) : (1 : R) • x = x := by
  refine Quot.inductionOn x ?_; clear x; intro x; obtain ⟨j, x⟩ := x
  erw [colimit_smul_mk_eq F 1 ⟨j, x⟩]
  simp
  rfl

-- Porting note (https://github.com/leanprover-community/mathlib4/pull/11083): writing directly the `Module` instance makes things very slow.
instance colimitMulAction : MulAction R (M F) where
  one_smul x := by
    refine Quot.inductionOn x ?_; clear x; intro x; obtain ⟨j, x⟩ := x
    erw [colimit_smul_mk_eq F 1 ⟨j, x⟩, one_smul]
    rfl
  mul_smul r s x := by
    refine Quot.inductionOn x ?_; clear x; intro x; obtain ⟨j, x⟩ := x
    erw [colimit_smul_mk_eq F (r * s) ⟨j, x⟩, colimit_smul_mk_eq F s ⟨j, x⟩,
      colimit_smul_mk_eq F r ⟨j, _⟩, mul_smul]

instance colimitSMulWithZero : SMulWithZero R (M F) :=
{ colimitMulAction F with
  smul_zero := fun r => by
    rw [colimit_zero_eq _ (IsFiltered.nonempty.some : J), colimit_smul_mk_eq, smul_zero]
  zero_smul := fun x => by
    refine Quot.inductionOn x ?_; clear x; intro x; obtain ⟨j, x⟩ := x
    change _ • M.mk F ⟨j, x⟩ = 0
    rw [colimit_smul_mk_eq, zero_smul, colimit_zero_eq _ j] }

private theorem colimitModule.add_smul (r s : R) (x : (M F)) : (r + s) • x = r • x + s • x := by
  refine Quot.inductionOn x ?_; clear x; intro x; obtain ⟨j, x⟩ := x
  change (r + s) • M.mk F ⟨j, x⟩ = r • M.mk F ⟨j, x⟩ + s • M.mk F ⟨j, x⟩
  simp [colimit_smul_mk_eq, _root_.add_smul, colimit_smul_mk_eq,
    colimit_smul_mk_eq, colimit_add_mk_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j)]

instance colimitModule : Module R (M F) :=
{ colimitMulAction F,
  colimitSMulWithZero F with
  smul_add := fun r x y => by
    refine Quot.induction_on₂ x y ?_; clear x y; intro x y; obtain ⟨i, x⟩ := x; obtain ⟨j, y⟩ := y
    change r • (M.mk _ ⟨i, x⟩ + M.mk _ ⟨j, y⟩) = r • M.mk _ ⟨i, x⟩ + r • M.mk _ ⟨j, y⟩
    rw [colimit_add_mk_eq _ ⟨i, _⟩ ⟨j, _⟩ (max' i j) (IsFiltered.leftToMax i j)
      (IsFiltered.rightToMax i j), colimit_smul_mk_eq, smul_add, colimit_smul_mk_eq,
      colimit_smul_mk_eq, colimit_add_mk_eq _ ⟨i, _⟩ ⟨j, _⟩ (max' i j) (IsFiltered.leftToMax i j)
      (IsFiltered.rightToMax i j), LinearMap.map_smul, LinearMap.map_smul]
  add_smul := colimitModule.add_smul F }

/-- The bundled `R`-module giving the filtered colimit of a diagram. -/
def colimit : ModuleCat.{max v u, u} R :=
  ModuleCat.of R (M F)

/-- The linear map from a given `R`-module in the diagram to the colimit module. -/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F :=
  ofHom
    { ((AddCommGrp.FilteredColimits.colimitCocone
      (F ⋙ forget₂ (ModuleCat R) AddCommGrp.{max v u})).ι.app j).hom with
    map_smul' := fun r x => by erw [colimit_smul_mk_eq F r ⟨j, x⟩]; rfl }

/-- The cocone over the proposed colimit module. -/
def colimitCocone : Cocone F where
  pt := colimit F
  ι :=
    { app := coconeMorphism F
      naturality := fun _ _' f =>
        hom_ext <| LinearMap.coe_injective
          ((Types.TypeMax.colimitCocone (F ⋙ forget (ModuleCat R))).ι.naturality f) }

/-- Given a cocone `t` of `F`, the induced monoid linear map from the colimit to the cocone point.
We already know that this is a morphism between additive groups. The only thing left to see is that
it is a linear map, i.e. preserves scalar multiplication.
-/
def colimitDesc (t : Cocone F) : colimit F ⟶ t.pt :=
  let h := (AddCommGrp.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ _ _))
  let f : colimit F →+ t.pt := (h.desc ((forget₂ _ _).mapCocone t)).hom
  have hf {j : J} (x : F.obj j) : f (M.mk _ ⟨j, x⟩) = t.ι.app j x :=
    congr_fun ((forget _).congr_map (h.fac ((forget₂ _ _).mapCocone t) j)) x
  ofHom
    { f with
    map_smul' := fun r x => by
      refine Quot.inductionOn x ?_; clear x; intro x; obtain ⟨j, x⟩ := x
      change f (r • M.mk _ ⟨j, x⟩) = r • f (M.mk _ ⟨j, x⟩)
      rw [colimit_smul_mk_eq, hf, hf, map_smul] }

@[reassoc (attr := simp)]
lemma ι_colimitDesc (t : Cocone F) (j : J) :
    (colimitCocone F).ι.app j ≫ colimitDesc F t = t.ι.app j :=
  (forget₂ _ AddCommGrp).map_injective
    ((AddCommGrp.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ _ _)).fac _ _)

/-- The proposed colimit cocone is a colimit in `ModuleCat R`. -/
def colimitCoconeIsColimit : IsColimit (colimitCocone F) where
  desc := colimitDesc F
  fac t j := by
    simp
  uniq t _ h := by
    ext ⟨j, x⟩
    exact (congr_fun ((forget _).congr_map (h j)) x).trans
      (congr_fun ((forget _).congr_map (ι_colimitDesc F t j)) x).symm

instance forget₂AddCommGroup_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ (ModuleCat.{u} R) AddCommGrp.{u}) where
  preserves_filtered_colimits _ _ _ :=
  { preservesColimit := fun {F} =>
      preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit F)
        (AddCommGrp.FilteredColimits.colimitCoconeIsColimit
          (F ⋙ forget₂ (ModuleCat.{u} R) AddCommGrp.{u})) }

instance forget_preservesFilteredColimits : PreservesFilteredColimits (forget (ModuleCat.{u} R)) :=
  Limits.comp_preservesFilteredColimits (forget₂ (ModuleCat R) AddCommGrp)
    (forget AddCommGrp)

instance forget_reflectsFilteredColimits : ReflectsFilteredColimits (forget (ModuleCat.{u} R)) where
  reflects_filtered_colimits _ := { reflectsColimit := reflectsColimit_of_reflectsIsomorphisms _ _ }

end

end ModuleCat.FilteredColimits
