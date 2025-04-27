/-
<<<<<<< HEAD
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Adjunction.Unique
=======
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Joël Riou
-/
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Adjunction.Mates
>>>>>>> origin/jriou_localization_bump_deps

/-!
# Adjoints commute with shifts

<<<<<<< HEAD
=======
Given categories `C` and `D` that have shifts by an additive group `A`, functors `F : C ⥤ D`
and `G : C ⥤ D`, an adjunction `F ⊣ G` and a `CommShift` structure on `F`, this file constructs
a `CommShift` structure on `G`. We also do the construction in the other direction: given a
`CommShift` structure on `G`, we construct a `CommShift` structure on `G`; we could do this
using opposite categories, but the construction is simple enough that it is not really worth it.
As an easy application, if `E : C ≌ D` is an equivalence and `E.functor` has a `CommShift`
structure, we get a `CommShift` structure on `E.inverse`.

We now explain the construction of a `CommShift` structure on `G` given a `CommShift` structure
on `F`; the other direction is similar. The `CommShift` structure on `G` must be compatible with
the one on `F` in the following sense (cf. `Adjunction.CommShift`):
for every `a` in `A`, the natural transformation `adj.unit : 𝟭 C ⟶ G ⋙ F` commutes with
the isomorphism `shiftFunctor C A ⋙ G ⋙ F ≅ G ⋙ F ⋙ shiftFunctor C A` induces by
`F.commShiftIso a` and `G.commShiftIso a`. We actually require a similar condition for
`adj.counit`, but it follows from the one for `adj.unit`.

In order to simplify the construction of the `CommShift` structure on `G`, we first introduce
the compatibility condition on `adj.unit` for a fixed `a` in `A` and for isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`. We then prove that:
- If `e₁` and `e₂` satusfy this condition, then `e₁` uniquely determines `e₂` and vice versa.
- If `a = 0`, the isomorphisms `Functor.CommShift.isoZero F` and `Functor.CommShift.isoZero G`
satisfy the condition.
- The condition is stable by addition on `A`, if we use `Functor.CommShift.isoAdd` to deduce
commutation isomorphism for `a + b` from such isomorphism from `a` and `b`.
- Given commutation isomorphisms for `F`, our candidate commutation isomorphisms for `G`,
constructed in `Adjunction.RightAdjointCommShift.iso`, satisfy the compatibility condition.

Once we have established all this, the compatibility of the commutation isomorphism for
`F` expressed in `CommShift.zero` and `CommShift.add` immediately implies the similar
statements for the commutation isomorphisms for `G`.

>>>>>>> origin/jriou_localization_bump_deps
-/

namespace CategoryTheory

open Category

<<<<<<< HEAD
/-- Variant of `Iso.ext`. -/
lemma Iso.ext' {C : Type*} [Category C] {X Y : C} {e₁ e₂ : X ≅ Y}
    (h : e₁.inv = e₂.inv) : e₁ = e₂ := by
  change e₁.symm.symm = e₂.symm.symm
  congr 1
  ext
  exact h

namespace Adjunction

variable {C D : Type*} [Category C] [Category D]
  {G₁ G₂ G₃ : C ⥤ D} {F₁ F₂ F₃ : D ⥤ C} (adj₁ : G₁ ⊣ F₁) (adj₂ : G₂ ⊣ F₂) (adj₃ : G₃ ⊣ F₃)

/-- natTransEquiv' -/
@[simps! apply_app symm_apply_app]
def natTransEquiv' : (G₁ ⟶ G₂) ≃ (F₂ ⟶ F₁) where
  toFun α := F₂.rightUnitor.inv ≫ whiskerLeft F₂ adj₁.unit ≫ whiskerLeft _ (whiskerRight α _) ≫
    (Functor.associator _ _ _).inv ≫ whiskerRight adj₂.counit F₁ ≫ F₁.leftUnitor.hom
  invFun β := G₁.leftUnitor.inv ≫ whiskerRight adj₂.unit G₁ ≫ whiskerRight (whiskerLeft _ β ) _ ≫
    (Functor.associator _ _ _ ).hom ≫ whiskerLeft G₂ adj₁.counit ≫ G₂.rightUnitor.hom
  left_inv α := by aesop_cat
  right_inv α := by
    ext X
    dsimp
    simp only [Category.comp_id, Category.id_comp, Functor.map_comp, Category.assoc,
      unit_naturality_assoc, right_triangle_components_assoc, ← α.naturality]

@[simp]
lemma natTransEquiv_id : natTransEquiv' adj₁ adj₁ (𝟙 _) = 𝟙 _ := by aesop_cat

@[simp]
lemma natTransEquiv_symm_id : (natTransEquiv' adj₁ adj₁).symm (𝟙 _) = 𝟙 _ := by aesop_cat

@[reassoc (attr := simp)]
lemma natTransEquiv_comp (α : G₁ ⟶ G₂) (β : G₂ ⟶ G₃) :
    natTransEquiv' adj₂ adj₃ β ≫ natTransEquiv' adj₁ adj₂ α =
      natTransEquiv' adj₁ adj₃ (α ≫ β) := by
  ext X
  apply (adj₁.homEquiv _ _).symm.injective
  dsimp
  simp [homEquiv_counit]

@[reassoc (attr := simp)]
lemma natTransEquiv_symm_comp (α : F₃ ⟶ F₂) (β : F₂ ⟶ F₁) :
    (natTransEquiv' adj₁ adj₂).symm β ≫ (natTransEquiv' adj₂ adj₃).symm α =
      (natTransEquiv' adj₁ adj₃).symm (α ≫ β) := by
  obtain ⟨α', rfl⟩ := (natTransEquiv' adj₂ adj₃).surjective α
  obtain ⟨β', rfl⟩ := (natTransEquiv' adj₁ adj₂).surjective β
  simp

/-- natIsoEquiv' -/
@[simps]
def natIsoEquiv' : (G₁ ≅ G₂) ≃ (F₁ ≅ F₂) where
  toFun e :=
    { hom := natTransEquiv' adj₂ adj₁ e.inv
      inv := natTransEquiv' adj₁ adj₂ e.hom }
  invFun e :=
    { hom := (natTransEquiv' adj₁ adj₂).symm e.inv
      inv := (natTransEquiv' adj₂ adj₁).symm e.hom }
  left_inv e := by dsimp; ext1; simp only [Equiv.symm_apply_apply]
  right_inv e := by dsimp; ext1; simp only [Equiv.apply_symm_apply]

end Adjunction

namespace Adjunction

variable {C D : Type*} [Category C] [Category D]
  {G : C ⥤ D} {F : D ⥤ C} (adj : G ⊣ F) (A Z : Type*) [AddMonoid A] [AddGroup Z]
  [HasShift C A] [HasShift D A] [F.CommShift A] [G.CommShift A]
  [HasShift C Z] [HasShift D Z]

=======
namespace Adjunction

variable {C D : Type*} [Category C] [Category D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A]

namespace CommShift

variable {a b : A} (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₁' : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (f₁ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b)
    (e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a)
    (e₂' : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a)
    (f₂ : shiftFunctor D b ⋙ G ≅ G ⋙ shiftFunctor C b)

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, this expresses the compatibility of
`e₁` and `e₂` with the unit of the adjunction `adj`.
-/
abbrev CompatibilityUnit :=
  ∀ (X : C), (adj.unit.app X)⟦a⟧' = adj.unit.app (X⟦a⟧) ≫ G.map (e₁.hom.app X) ≫ e₂.hom.app _

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, this expresses the compatibility of
`e₁` and `e₂` with the counit of the adjunction `adj`.
-/
abbrev CompatibilityCounit :=
  ∀ (Y : D), adj.counit.app (Y⟦a⟧) = F.map (e₂.hom.app Y) ≫ e₁.hom.app _ ≫ (adj.counit.app Y)⟦a⟧'

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, compatibility of `e₁` and `e₂` with the
unit of the adjunction `adj` implies compatibility with the counit of `adj`.
-/
lemma compatibilityCounit_of_compatibilityUnit (h : CompatibilityUnit adj e₁ e₂) :
    CompatibilityCounit adj e₁ e₂ := by
  intro Y
  have eq := h (G.obj Y)
  simp only [← cancel_mono (e₂.inv.app _ ≫ G.map (e₁.inv.app _)),
    assoc, Iso.hom_inv_id_app_assoc, comp_id, ← Functor.map_comp,
    Iso.hom_inv_id_app, Functor.comp_obj, Functor.map_id] at eq
  apply (adj.homEquiv _ _).injective
  dsimp
  rw [adj.homEquiv_unit, adj.homEquiv_unit, G.map_comp, adj.unit_naturality_assoc, ← eq]
  simp only [assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  erw [← e₂.inv.naturality]
  dsimp
  simp only [right_triangle_components, ← Functor.map_comp_assoc, Functor.map_id, id_comp,
    Iso.hom_inv_id_app, Functor.comp_obj]

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compatible with the
unit of the adjunction `adj`, then we get a formula for `e₂.inv` in terms of `e₁`.
-/
lemma compatibilityUnit_right (h : CompatibilityUnit adj e₁ e₂) (Y : D) :
    e₂.inv.app Y = adj.unit.app _ ≫ G.map (e₁.hom.app _) ≫ G.map ((adj.counit.app _)⟦a⟧') := by
  have := h (G.obj Y)
  rw [← cancel_mono (e₂.inv.app _), assoc, assoc, Iso.hom_inv_id_app] at this
  erw [comp_id] at this
  rw [← assoc, ← this, assoc]; erw [← e₂.inv.naturality]
  rw [← cancel_mono (e₂.hom.app _)]
  simp only [Functor.comp_obj, Iso.inv_hom_id_app, Functor.id_obj, Functor.comp_map, assoc, comp_id,
    ← (shiftFunctor C a).map_comp, right_triangle_components, Functor.map_id]

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compatible with the
counit of the adjunction `adj`, then we get a formula for `e₁.hom` in terms of `e₂`.
-/
lemma compatibilityCounit_left (h : CompatibilityCounit adj e₁ e₂) (X : C) :
    e₁.hom.app X = F.map ((adj.unit.app X)⟦a⟧') ≫ F.map (e₂.inv.app _) ≫ adj.counit.app _ := by
  have := h (F.obj X)
  rw [← cancel_epi (F.map (e₂.inv.app _)), ← assoc, ← F.map_comp, Iso.inv_hom_id_app, F.map_id,
    id_comp] at this
  rw [this]
  erw [e₁.hom.naturality_assoc]
  rw [Functor.comp_map, ← Functor.map_comp, left_triangle_components]
  simp only [Functor.comp_obj, Functor.id_obj, Functor.map_id, comp_id]

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compatible with the
unit of the adjunction `adj`, then `e₁` uniquely determines `e₂`.
-/
lemma compatibilityUnit_unique_right (h : CompatibilityUnit adj e₁ e₂)
    (h' : CompatibilityUnit adj e₁ e₂') : e₂ = e₂' := by
  rw [← Iso.symm_eq_iff]
  ext
  rw [Iso.symm_hom, Iso.symm_hom, compatibilityUnit_right adj e₁ e₂ h,
    compatibilityUnit_right adj e₁ e₂' h']

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compatible with the
unit of the adjunction `adj`, then `e₂` uniquely determines `e₁`.
-/
lemma compatibilityUnit_unique_left (h : CompatibilityUnit adj e₁ e₂)
    (h' : CompatibilityUnit adj e₁' e₂) : e₁ = e₁' := by
  ext
  rw [compatibilityCounit_left adj e₁ e₂ (compatibilityCounit_of_compatibilityUnit adj _ _ h),
    compatibilityCounit_left adj e₁' e₂ (compatibilityCounit_of_compatibilityUnit adj _ _ h')]

/--
The isomorphisms `Functor.CommShift.isoZero F` and `Functor.CommShift.isoZero G` are
compatible with the unit of an adjunction `F ⊣ G`.
-/
lemma compatibilityUnit_isoZero : CompatibilityUnit adj (Functor.CommShift.isoZero F A)
    (Functor.CommShift.isoZero G A) := by
  intro
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoZero_hom_app,
    Functor.map_comp, assoc, unit_naturality_assoc,
    ← cancel_mono ((shiftFunctorZero C A).hom.app _), ← G.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.id_obj, Functor.map_id, id_comp, NatTrans.naturality, Functor.id_map, assoc, comp_id]

/-- Given an adjunction `adj : F ⊣ G`, `a, b` in `A` and commutation isomorphisms
between shifts by `a` (resp. `b`) and `F` and `G`, if these commutation isomorphisms are
compatible with the unit of `adj`, then so are the commutation isomorphisms between shifts
by `a + b` and `F` and `G` constructed by `Functor.CommShift.isoAdd`.
-/
lemma compatibilityUnit_isoAdd (h : CompatibilityUnit adj e₁ e₂)
    (h' : CompatibilityUnit adj f₁ f₂) :
    CompatibilityUnit adj (Functor.CommShift.isoAdd e₁ f₁) (Functor.CommShift.isoAdd e₂ f₂) := by
  intro X
  have := h' (X⟦a⟧)
  simp only [← cancel_mono (f₂.inv.app _), assoc, Iso.hom_inv_id_app,
    Functor.id_obj, Functor.comp_obj, comp_id] at this
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoAdd_hom_app,
    Functor.map_comp, assoc, unit_naturality_assoc]
  slice_rhs 5 6 => rw [← G.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.map_id, id_comp, assoc]
  erw [f₂.hom.naturality_assoc]
  rw [← reassoc_of% this, ← cancel_mono ((shiftFunctorAdd C a b).hom.app _),
    assoc, assoc, assoc, assoc, assoc, assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  dsimp
  rw [← (shiftFunctor C b).map_comp_assoc, ← (shiftFunctor C b).map_comp_assoc,
    assoc, ← h X, NatTrans.naturality]
  dsimp
  rw [comp_id]

end CommShift

variable (A) [F.CommShift A] [G.CommShift A]

/--
The property for `CommShift` structures on `F` and `G` to be compatible with an
adjunction `F ⊣ G`.
-/
>>>>>>> origin/jriou_localization_bump_deps
class CommShift : Prop where
  commShift_unit : NatTrans.CommShift adj.unit A := by infer_instance
  commShift_counit : NatTrans.CommShift adj.counit A := by infer_instance

<<<<<<< HEAD
namespace CommShift

attribute [instance] commShift_unit commShift_counit
=======
open CommShift in
attribute [instance] commShift_unit commShift_counit

@[reassoc (attr := simp)]
lemma unit_app_commShiftIso_hom_app [adj.CommShift A] (a : A) (X : C) :
    adj.unit.app (X⟦a⟧) ≫ ((F ⋙ G).commShiftIso a).hom.app X = (adj.unit.app X)⟦a⟧' := by
  simpa using (NatTrans.shift_app_comm adj.unit a X).symm

@[reassoc (attr := simp)]
lemma unit_app_shift_commShiftIso_inv_app [adj.CommShift A] (a : A) (X : C) :
    (adj.unit.app X)⟦a⟧' ≫ ((F ⋙ G).commShiftIso a).inv.app X = adj.unit.app (X⟦a⟧) := by
  simp [← cancel_mono (((F ⋙ G).commShiftIso _).hom.app _)]

@[reassoc (attr := simp)]
lemma commShiftIso_hom_app_counit_app_shift [adj.CommShift A] (a : A) (Y : D) :
    ((G ⋙ F).commShiftIso a).hom.app Y ≫ (adj.counit.app Y)⟦a⟧' = adj.counit.app (Y⟦a⟧) := by
  simpa using (NatTrans.shift_app_comm adj.counit a Y)

@[reassoc (attr := simp)]
lemma commShiftIso_inv_app_counit_app [adj.CommShift A] (a : A) (Y : D) :
    ((G ⋙ F).commShiftIso a).inv.app Y ≫ adj.counit.app (Y⟦a⟧) = (adj.counit.app Y)⟦a⟧' := by
  simp [← cancel_epi (((G ⋙ F).commShiftIso _).hom.app _)]

namespace CommShift

>>>>>>> origin/jriou_localization_bump_deps

/-- Constructor for `Adjunction.CommShift`. -/
lemma mk' (h : NatTrans.CommShift adj.unit A) :
    adj.CommShift A where
<<<<<<< HEAD
  commShift_counit := ⟨by
    intro a
    ext X
    have eq := NatTrans.CommShift.app_shift adj.unit a (F.obj X)
    dsimp at eq ⊢
    simp only [Functor.CommShift.commShiftIso_id_hom_app, Functor.comp_obj,
      Functor.id_obj, Functor.commShiftIso_comp_inv_app, id_comp,
      Functor.commShiftIso_comp_hom_app, assoc, comp_id] at eq ⊢
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_unit, adj.homEquiv_unit, F.map_comp]
    dsimp
    rw [adj.unit_naturality_assoc]
    simp only [eq, assoc, ← F.map_comp, Iso.inv_hom_id_app_assoc, right_triangle_components,
      ← F.commShiftIso_inv_naturality, ← Functor.map_comp_assoc, Functor.map_id, id_comp,
      Iso.hom_inv_id_app, Functor.comp_obj]⟩
=======
  commShift_counit := ⟨fun a ↦ by
    ext
    simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app,
      Functor.commShiftIso_comp_hom_app, whiskerRight_app, assoc, whiskerLeft_app,
      Functor.commShiftIso_id_hom_app, comp_id]
    refine (compatibilityCounit_of_compatibilityUnit adj _ _ (fun X ↦ ?_) _).symm
    simpa only [NatTrans.comp_app,
      Functor.commShiftIso_id_hom_app, whiskerRight_app, id_comp,
      Functor.commShiftIso_comp_hom_app] using congr_app (h.shift_comm a) X⟩

variable [adj.CommShift A]

/-- The identity adjunction is compatible with the trivial `CommShift` structure on the
identity functor.
-/
instance instId : (Adjunction.id (C := C)).CommShift A where
  commShift_counit :=
    inferInstanceAs (NatTrans.CommShift (𝟭 C).leftUnitor.hom A)
  commShift_unit :=
    inferInstanceAs (NatTrans.CommShift (𝟭 C).leftUnitor.inv A)

variable {E : Type*} [Category E] {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G')
  [HasShift E A] [F'.CommShift A] [G'.CommShift A] [adj.CommShift A] [adj'.CommShift A]

/-- Compatibility of `Adjunction.Commshift` with the composition of adjunctions.
-/
instance instComp : (adj.comp adj').CommShift A where
  commShift_counit := by
    rw [comp_counit]
    infer_instance
  commShift_unit := by
    rw [comp_unit]
    infer_instance
>>>>>>> origin/jriou_localization_bump_deps

end CommShift

variable {A}

@[reassoc]
lemma shift_unit_app [adj.CommShift A] (a : A) (X : C) :
    (adj.unit.app X)⟦a⟧' =
      adj.unit.app (X⟦a⟧) ≫
<<<<<<< HEAD
        F.map ((G.commShiftIso a).hom.app X) ≫
          (F.commShiftIso a).hom.app (G.obj X) := by
  simpa [Functor.commShiftIso_comp_hom_app] using NatTrans.CommShift.comm_app adj.unit a X

@[reassoc]
lemma shift_counit_app [adj.CommShift A] (a : A) (X : D) :
    (adj.counit.app X)⟦a⟧' =
      (G.commShiftIso a).inv.app (F.obj X) ≫ G.map ((F.commShiftIso a).inv.app X)
        ≫ adj.counit.app (X⟦a⟧) := by
  have eq := NatTrans.CommShift.comm_app adj.counit a X
  simp only [Functor.comp_obj, Functor.id_obj, Functor.commShiftIso_comp_hom_app, assoc,
    Functor.CommShift.commShiftIso_id_hom_app, comp_id] at eq
  simp only [← eq, Functor.comp_obj, ← G.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.map_id, id_comp, Iso.inv_hom_id_app_assoc]

namespace RightAdjointCommShift

variable {Z}
variable (a b : Z) (h : b + a = 0)

noncomputable def adj₁ : G ⋙ shiftFunctor D b ⊣ shiftFunctor D a ⋙ F :=
  adj.comp (shiftEquiv' D b a h).toAdjunction

noncomputable def adj₂ : shiftFunctor C b ⋙ G ⊣ F ⋙ shiftFunctor C a :=
  (shiftEquiv' C b a h).toAdjunction.comp adj

variable [G.CommShift Z]

noncomputable def adj₃ : G ⋙ shiftFunctor D b ⊣ F ⋙ shiftFunctor C a :=
  (adj₂ adj a b h).ofNatIsoLeft (G.commShiftIso b)

/-- Auxiliary definition for `iso`. -/
noncomputable def iso' : shiftFunctor D a ⋙ F ≅ F ⋙ shiftFunctor C a :=
  Adjunction.natIsoEquiv' (adj₁ adj a b h) (adj₃ adj a b h) (Iso.refl _)

noncomputable def iso : shiftFunctor D a ⋙ F ≅ F ⋙ shiftFunctor C a :=
  iso' adj _ _ (neg_add_cancel a)

lemma iso_hom_app (X : D) :
    (iso adj a).hom.app X =
      (shiftFunctorCompIsoId C b a h).inv.app (F.obj ((shiftFunctor D a).obj X)) ≫
        (adj.unit.app ((shiftFunctor C b).obj (F.obj ((shiftFunctor D a).obj X))))⟦a⟧' ≫
          (F.map ((G.commShiftIso b).hom.app (F.obj ((shiftFunctor D a).obj X))))⟦a⟧' ≫
            (F.map ((shiftFunctor D b).map (adj.counit.app ((shiftFunctor D a).obj X))))⟦a⟧' ≫
              (F.map ((shiftFunctorCompIsoId D a b
                (by rw [← add_left_inj a, add_assoc, h, zero_add, add_zero])).hom.app X))⟦a⟧' := by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_cancel]
  simp [iso, iso', adj₃, ofNatIsoLeft, adj₂, comp, Equivalence.toAdjunction, shiftEquiv',
    equivHomsetLeftOfNatIso, adj₁, mk'_homEquiv, homEquiv_unit]

lemma iso_inv_app (X : D) :
    (iso adj a).inv.app X =
      adj.unit.app ((shiftFunctor C a).obj (F.obj X)) ≫
          F.map ((shiftFunctorCompIsoId D b a h).inv.app
              (G.obj ((shiftFunctor C a).obj (F.obj X)))) ≫
            F.map ((shiftFunctor D a).map ((shiftFunctor D b).map
                ((G.commShiftIso a).hom.app (F.obj X)))) ≫
              F.map ((shiftFunctor D a).map ((shiftFunctorCompIsoId D a b
                  (by rw [← add_left_inj a, add_assoc, h, zero_add, add_zero])).hom.app
                    (G.obj (F.obj X)))) ≫
                F.map ((shiftFunctor D a).map (adj.counit.app X)) := by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_cancel]
  simp [iso, iso', adj₃, ofNatIsoLeft, adj₂, comp, Equivalence.toAdjunction, shiftEquiv',
    equivHomsetLeftOfNatIso, adj₁, mk'_homEquiv, homEquiv_counit]

end RightAdjointCommShift

@[simps]
noncomputable def rightAdjointCommShift [G.CommShift Z] : F.CommShift Z where
  iso a := RightAdjointCommShift.iso adj a
  zero := by
    apply Iso.ext'
    ext X
    apply (adj.homEquiv _ _).symm.injective
    dsimp
    simp [RightAdjointCommShift.iso_inv_app adj _ _ (add_zero (0 : Z)) X, homEquiv_counit]
    erw [← NatTrans.naturality_assoc]
    dsimp
    rw [shift_shiftFunctorCompIsoId_hom_app, Iso.inv_hom_id_app_assoc, Functor.commShiftIso_zero,
      Functor.CommShift.isoZero_hom_app, assoc]
    erw [← NatTrans.naturality]
    rfl
  add a b := by
    apply Iso.ext'
    ext X
    apply (adj.homEquiv _ _).symm.injective
    dsimp
    simp [RightAdjointCommShift.iso_inv_app adj _ _ (neg_add_cancel (a + b)) X,
      RightAdjointCommShift.iso_inv_app adj _ _ (neg_add_cancel a) X,
      RightAdjointCommShift.iso_inv_app adj _ _ (neg_add_cancel b), homEquiv_counit]
    erw [← NatTrans.naturality_assoc]
    dsimp
    rw [shift_shiftFunctorCompIsoId_hom_app, Iso.inv_hom_id_app_assoc]
    rw [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app]
    simp
    simp only [← Functor.map_comp_assoc, assoc]
    erw [← (shiftFunctorCompIsoId D _ _ (neg_add_cancel a)).inv.naturality]
    dsimp
    rw [← NatTrans.naturality]
    rw [← F.map_comp, assoc, shift_shiftFunctorCompIsoId_hom_app, Iso.inv_hom_id_app]
    dsimp
    rw [comp_id]
    simp only [Functor.map_comp, assoc]; congr 1; simp only [← assoc]; congr 1; simp only [assoc]
    erw [← NatTrans.naturality_assoc]
    dsimp
    rw [shift_shiftFunctorCompIsoId_hom_app, Iso.inv_hom_id_app_assoc]
    simp only [← Functor.map_comp, ← Functor.map_comp_assoc, assoc]
    apply (adj.homEquiv _ _).injective
    dsimp
    simp only [Functor.map_comp, homEquiv_unit, Functor.id_obj, Functor.comp_obj, assoc,
      Functor.commShiftIso_hom_naturality_assoc]
    congr 1
    simp only [← F.map_comp, assoc]
    congr 2
    simp only [← Functor.map_comp, assoc]
    congr 1
    dsimp
    simp

lemma commShift_of_leftAdjoint [G.CommShift Z] :
    letI := adj.rightAdjointCommShift Z
    adj.CommShift Z := by
  suffices h : ∀ X (a : Z), (adj.unit.app X)⟦a⟧' =
      adj.unit.app (X⟦a⟧) ≫ F.map ((G.commShiftIso a).hom.app X) ≫
        (RightAdjointCommShift.iso adj a).hom.app (G.obj X) by
    letI := adj.rightAdjointCommShift Z
    apply CommShift.mk'
    refine ⟨fun a => ?_⟩
    ext X
    dsimp
    simp only [Functor.CommShift.commShiftIso_id_hom_app, Functor.comp_obj,
      Functor.id_obj, id_comp, Functor.commShiftIso_comp_hom_app]
    exact h X a
  intro X a
  rw [← cancel_mono ((RightAdjointCommShift.iso adj a).inv.app (G.obj X)), assoc, assoc,
    Iso.hom_inv_id_app]
  dsimp
  rw [comp_id]
  simp [RightAdjointCommShift.iso_inv_app adj _ _ (neg_add_cancel a)]
  apply (adj.homEquiv _ _).symm.injective
  dsimp
  simp [homEquiv_counit]
=======
        G.map ((F.commShiftIso a).hom.app X) ≫
          (G.commShiftIso a).hom.app (F.obj X) := by
  simpa [Functor.commShiftIso_comp_hom_app] using NatTrans.shift_app_comm adj.unit a X

@[reassoc]
lemma shift_counit_app [adj.CommShift A] (a : A) (Y : D) :
    (adj.counit.app Y)⟦a⟧' =
      (F.commShiftIso a).inv.app (G.obj Y) ≫ F.map ((G.commShiftIso a).inv.app Y) ≫
        adj.counit.app (Y⟦a⟧) := by
  have eq := NatTrans.shift_app_comm adj.counit a Y
  simp only [Functor.comp_obj, Functor.id_obj, Functor.commShiftIso_comp_hom_app, assoc,
    Functor.commShiftIso_id_hom_app, comp_id] at eq
  simp only [← eq, Functor.comp_obj, Functor.id_obj, ← F.map_comp_assoc, Iso.inv_hom_id_app,
    F.map_id, id_comp, Iso.inv_hom_id_app_assoc]

end Adjunction

namespace Adjunction

variable {C D : Type*} [Category C] [Category D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : Type*} [AddGroup A] [HasShift C A] [HasShift D A]

namespace RightAdjointCommShift

variable (a b : A) (h : b + a = 0) [F.CommShift A]

/-- Auxiliary definition for `iso`. -/
noncomputable def iso' : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a :=
  (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv' D b a h).toAdjunction)
    (Adjunction.comp (shiftEquiv' C b a h).toAdjunction adj)).toFun (F.commShiftIso b)

/--
Given an adjunction `F ⊣ G` and a `CommShift` structure on `F`, these are the candidate
`CommShift.iso a` isomorphisms for a compatible `CommShift` structure on `G`.
-/
noncomputable def iso : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a :=
  iso' adj _ _ (neg_add_cancel a)

@[reassoc]
lemma iso_hom_app (X : D) :
    (iso adj a).hom.app X =
      (shiftFunctorCompIsoId C b a h).inv.app (G.obj ((shiftFunctor D a).obj X)) ≫
        (adj.unit.app ((shiftFunctor C b).obj (G.obj ((shiftFunctor D a).obj X))))⟦a⟧' ≫
          (G.map ((F.commShiftIso b).hom.app (G.obj ((shiftFunctor D a).obj X))))⟦a⟧' ≫
            (G.map ((shiftFunctor D b).map (adj.counit.app ((shiftFunctor D a).obj X))))⟦a⟧' ≫
              (G.map ((shiftFunctorCompIsoId D a b
                (by rw [← add_left_inj a, add_assoc, h, zero_add, add_zero])).hom.app X))⟦a⟧' := by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_cancel]
  simp [iso, iso', shiftEquiv']

@[reassoc]
lemma iso_inv_app (Y : D) :
    (iso adj a).inv.app Y =
      adj.unit.app ((shiftFunctor C a).obj (G.obj Y)) ≫
          G.map ((shiftFunctorCompIsoId D b a h).inv.app
              (F.obj ((shiftFunctor C a).obj (G.obj Y)))) ≫
            G.map ((shiftFunctor D a).map ((shiftFunctor D b).map
                ((F.commShiftIso a).hom.app (G.obj Y)))) ≫
              G.map ((shiftFunctor D a).map ((shiftFunctorCompIsoId D a b
                  (by rw [eq_neg_of_add_eq_zero_left h, add_neg_cancel])).hom.app
                    (F.obj (G.obj Y)))) ≫
                G.map ((shiftFunctor D a).map (adj.counit.app Y)) := by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_cancel]
  simp only [iso, iso', shiftEquiv', Equiv.toFun_as_coe, conjugateIsoEquiv_apply_inv,
    conjugateEquiv_apply_app, Functor.comp_obj, comp_unit_app, Functor.id_obj,
    Equivalence.toAdjunction_unit, Equivalence.Equivalence_mk'_unit, Iso.symm_hom, Functor.comp_map,
    comp_counit_app, Equivalence.toAdjunction_counit, Equivalence.Equivalence_mk'_counit,
    Functor.map_shiftFunctorCompIsoId_hom_app, assoc, Functor.map_comp]
  slice_lhs 3 4 => rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.map_id, id_comp, assoc]

/--
The commutation isomorphisms of `Adjunction.RightAdjointCommShift.iso` are compatible with
the unit of the adjunction.
-/
lemma compatibilityUnit_iso (a : A) :
    CommShift.CompatibilityUnit adj (F.commShiftIso a) (iso adj a) := by
  intro
  rw [← cancel_mono ((RightAdjointCommShift.iso adj a).inv.app _), assoc, assoc,
    Iso.hom_inv_id_app, RightAdjointCommShift.iso_inv_app adj _ _ (neg_add_cancel a)]
  apply (adj.homEquiv _ _).symm.injective
  dsimp
  simp only [comp_id, homEquiv_counit, Functor.map_comp, assoc, counit_naturality,
    counit_naturality_assoc, left_triangle_components_assoc]
>>>>>>> origin/jriou_localization_bump_deps
  erw [← NatTrans.naturality_assoc]
  dsimp
  rw [shift_shiftFunctorCompIsoId_hom_app, Iso.inv_hom_id_app_assoc,
    Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp,
    left_triangle_components, Functor.map_id, comp_id]

<<<<<<< HEAD
=======
end RightAdjointCommShift

variable (A)

open RightAdjointCommShift in
/--
Given an adjunction `F ⊣ G` and a `CommShift` structure on `F`, this constructs
the unique compatible `CommShift` structure on `G`.
-/
@[simps]
noncomputable def rightAdjointCommShift [F.CommShift A] : G.CommShift A where
  iso a := iso adj a
  zero := by
    refine CommShift.compatibilityUnit_unique_right adj (F.commShiftIso 0) _ _
      (compatibilityUnit_iso adj 0) ?_
    rw [F.commShiftIso_zero]
    exact CommShift.compatibilityUnit_isoZero adj
  add a b := by
    refine CommShift.compatibilityUnit_unique_right adj (F.commShiftIso (a + b)) _ _
      (compatibilityUnit_iso adj (a + b)) ?_
    rw [F.commShiftIso_add]
    exact CommShift.compatibilityUnit_isoAdd adj _ _ _ _
      (compatibilityUnit_iso adj a) (compatibilityUnit_iso adj b)

lemma commShift_of_leftAdjoint [F.CommShift A] :
    letI := adj.rightAdjointCommShift A
    adj.CommShift A := by
  letI := adj.rightAdjointCommShift A
  refine CommShift.mk' _ _ ⟨fun a ↦ ?_⟩
  ext X
  dsimp
  simpa only [Functor.commShiftIso_id_hom_app, Functor.comp_obj, Functor.id_obj, id_comp,
    Functor.commShiftIso_comp_hom_app] using RightAdjointCommShift.compatibilityUnit_iso adj a X

namespace LeftAdjointCommShift

variable {A} (a b : A) (h : a + b = 0) [G.CommShift A]

/-- Auxiliary definition for `iso`. -/
noncomputable def iso' : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv' D a b h).toAdjunction)
    (Adjunction.comp (shiftEquiv' C a b h).toAdjunction adj)).invFun (G.commShiftIso b)

/--
Given an adjunction `F ⊣ G` and a `CommShift` structure on `G`, these are the candidate
`CommShift.iso a` isomorphisms for a compatible `CommShift` structure on `F`.
-/
noncomputable def iso : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  iso' adj _ _ (add_neg_cancel a)

@[reassoc]
lemma iso_hom_app (X : C) :
    (iso adj a).hom.app X = F.map ((adj.unit.app X)⟦a⟧') ≫
      F.map (G.map (((shiftFunctorCompIsoId D a b h).inv.app (F.obj X)))⟦a⟧') ≫
        F.map (((G.commShiftIso b).hom.app ((F.obj X)⟦a⟧))⟦a⟧') ≫
          F.map ((shiftFunctorCompIsoId C b a (by simp [eq_neg_of_add_eq_zero_left h])).hom.app
            (G.obj ((F.obj X)⟦a⟧))) ≫ adj.counit.app ((F.obj X)⟦a⟧) := by
  obtain rfl : b = -a := eq_neg_of_add_eq_zero_right h
  simp [iso, iso', shiftEquiv']

@[reassoc]
lemma iso_inv_app (Y : C) :
    (iso adj a).inv.app Y = (F.map ((shiftFunctorCompIsoId C a b h).inv.app Y))⟦a⟧' ≫
      (F.map ((adj.unit.app (Y⟦a⟧))⟦b⟧'))⟦a⟧' ≫ (F.map ((G.commShiftIso b).inv.app
        (F.obj (Y⟦a⟧))))⟦a⟧' ≫ (adj.counit.app ((F.obj (Y⟦a⟧))⟦b⟧))⟦a⟧' ≫
          (shiftFunctorCompIsoId D b a (by simp [eq_neg_of_add_eq_zero_left h])).hom.app
            (F.obj (Y⟦a⟧)) := by
  obtain rfl : b = -a := eq_neg_of_add_eq_zero_right h
  simp [iso, iso', shiftEquiv']

/--
The commutation isomorphisms of `Adjunction.LeftAdjointCommShift.iso` are compatible with
the unit of the adjunction.
-/
lemma compatibilityUnit_iso (a : A) :
    CommShift.CompatibilityUnit adj (iso adj a) (G.commShiftIso a) := by
  intro
  rw [LeftAdjointCommShift.iso_hom_app adj _ _ (add_neg_cancel a)]
  simp only [Functor.id_obj, Functor.comp_obj, Functor.map_shiftFunctorCompIsoId_inv_app,
    Functor.map_comp, assoc, unit_naturality_assoc, right_triangle_components_assoc]
  slice_rhs 4 5 => rw [← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.map_id, id_comp]
  rw [shift_shiftFunctorCompIsoId_inv_app, ← Functor.comp_map,
    (shiftFunctorCompIsoId C _ _ (neg_add_cancel a)).hom.naturality_assoc]
  simp

end LeftAdjointCommShift

open LeftAdjointCommShift in
/--
Given an adjunction `F ⊣ G` and a `CommShift` structure on `G`, this constructs
the unique compatible `CommShift` structure on `F`.
-/
@[simps]
noncomputable def leftAdjointCommShift [G.CommShift A] : F.CommShift A where
  iso a := iso adj a
  zero := by
    refine CommShift.compatibilityUnit_unique_left adj _ _ (G.commShiftIso 0)
      (compatibilityUnit_iso adj 0) ?_
    rw [G.commShiftIso_zero]
    exact CommShift.compatibilityUnit_isoZero adj
  add a b := by
    refine CommShift.compatibilityUnit_unique_left adj _ _ (G.commShiftIso (a + b))
      (compatibilityUnit_iso adj (a + b)) ?_
    rw [G.commShiftIso_add]
    exact CommShift.compatibilityUnit_isoAdd adj _ _ _ _
      (compatibilityUnit_iso adj a) (compatibilityUnit_iso adj b)

lemma commShift_of_rightAdjoint [G.CommShift A] :
    letI := adj.leftAdjointCommShift A
    adj.CommShift A := by
  letI := adj.leftAdjointCommShift A
  refine CommShift.mk' _ _ ⟨fun a ↦ ?_⟩
  ext X
  dsimp
  simpa only [Functor.commShiftIso_id_hom_app, Functor.comp_obj, Functor.id_obj, id_comp,
    Functor.commShiftIso_comp_hom_app] using LeftAdjointCommShift.compatibilityUnit_iso adj a X

>>>>>>> origin/jriou_localization_bump_deps
end Adjunction

namespace Equivalence

variable {C D : Type*} [Category C] [Category D] (E : C ≌ D)
<<<<<<< HEAD
  (A Z : Type*) [AddMonoid A] [AddGroup Z]
  [HasShift C A] [HasShift D A] [HasShift C Z] [HasShift D Z]

class CommShift [E.functor.CommShift A] [E.inverse.CommShift A] : Prop where
  commShift_unitIso_hom : NatTrans.CommShift E.unitIso.hom A := by infer_instance
  commShift_counitIso_hom : NatTrans.CommShift E.counitIso.hom A := by infer_instance

namespace CommShift

attribute [instance] commShift_unitIso_hom commShift_counitIso_hom
=======

section

variable (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A]

/--
If `E : C ≌ D` is an equivalence, this expresses the compatibility of `CommShift`
structures on `E.functor` and `E.inverse`.
-/
abbrev CommShift [E.functor.CommShift A] [E.inverse.CommShift A] : Prop :=
  E.toAdjunction.CommShift A

namespace CommShift

variable [E.functor.CommShift A] [E.inverse.CommShift A]

instance [E.CommShift A] : NatTrans.CommShift E.unitIso.hom A :=
  inferInstanceAs (NatTrans.CommShift E.toAdjunction.unit A)

instance [E.CommShift A] : NatTrans.CommShift E.counitIso.hom A :=
  inferInstanceAs (NatTrans.CommShift E.toAdjunction.counit A)
>>>>>>> origin/jriou_localization_bump_deps

instance [h : E.functor.CommShift A] : E.symm.inverse.CommShift A := h
instance [h : E.inverse.CommShift A] : E.symm.functor.CommShift A := h

/-- Constructor for `Equivalence.CommShift`. -/
<<<<<<< HEAD
lemma mk' [E.functor.CommShift A] [E.inverse.CommShift A]
    (h : NatTrans.CommShift E.unitIso.hom A) :
    E.CommShift A where
  commShift_counitIso_hom :=
    (Adjunction.CommShift.mk' E.toAdjunction A h).commShift_counit

/-- Constructor for `Equivalence.CommShift`. -/
lemma mk'' [E.functor.CommShift A] [E.inverse.CommShift A]
    (h : NatTrans.CommShift E.counitIso.hom A) :
    E.CommShift A where
  commShift_unitIso_hom := by
    have h' := NatTrans.CommShift.of_iso_inv E.counitIso A
    have : NatTrans.CommShift E.unitIso.symm.hom A :=
      (Adjunction.CommShift.mk' E.symm.toAdjunction A h').commShift_counit
    exact NatTrans.CommShift.of_iso_inv E.unitIso.symm A

instance [E.functor.CommShift A] [E.inverse.CommShift A] [E.CommShift A] :
    E.toAdjunction.CommShift A where
  commShift_unit := commShift_unitIso_hom
  commShift_counit := commShift_counitIso_hom


instance [E.functor.CommShift A] [E.inverse.CommShift A] [E.CommShift A] :
    E.symm.CommShift A := mk' _ _ (by
  dsimp only [Equivalence.symm, Iso.symm]
  infer_instance)

end CommShift

noncomputable def commShiftInverse [E.functor.CommShift Z] : E.inverse.CommShift Z :=
  E.toAdjunction.rightAdjointCommShift Z

lemma commShift_of_functor [E.functor.CommShift Z] :
    letI := E.commShiftInverse Z
    E.CommShift Z := by
  letI := E.commShiftInverse Z
  exact CommShift.mk' _ _ (E.toAdjunction.commShift_of_leftAdjoint Z).commShift_unit

noncomputable def commShiftFunctor [E.inverse.CommShift Z] : E.functor.CommShift Z :=
  E.symm.toAdjunction.rightAdjointCommShift Z

lemma commShift_of_inverse [E.inverse.CommShift Z] :
    letI := E.commShiftFunctor Z
    E.CommShift Z := by
  letI := E.commShiftFunctor Z
  apply CommShift.mk''
  have : NatTrans.CommShift E.counitIso.symm.hom Z :=
    (E.symm.toAdjunction.commShift_of_leftAdjoint Z).commShift_unit
  exact NatTrans.CommShift.of_iso_inv E.counitIso.symm Z
=======
lemma mk' (h : NatTrans.CommShift E.unitIso.hom A) :
    E.CommShift A where
  commShift_unit := h
  commShift_counit := (Adjunction.CommShift.mk' E.toAdjunction A h).commShift_counit

/--
The forward functor of the identity equivalence is compatible with shifts.
-/
instance : (Equivalence.refl (C := C)).functor.CommShift A := by
  dsimp
  infer_instance

/--
The inverse functor of the identity equivalence is compatible with shifts.
-/
instance : (Equivalence.refl (C := C)).inverse.CommShift A := by
  dsimp
  infer_instance

/--
The identity equivalence is compatible with shifts.
-/
instance : (Equivalence.refl (C := C)).CommShift A := by
  dsimp [Equivalence.CommShift, refl_toAdjunction]
  infer_instance

/--
If an equivalence `E : C ≌ D` is compatible with shifts, so is `E.symm`.
-/
instance [E.CommShift A] : E.symm.CommShift A :=
  mk' E.symm A (inferInstanceAs (NatTrans.CommShift E.counitIso.inv A))

/-- Constructor for `Equivalence.CommShift`. -/
lemma mk'' (h : NatTrans.CommShift E.counitIso.hom A) :
    E.CommShift A :=
  have := mk' E.symm A (inferInstanceAs (NatTrans.CommShift E.counitIso.inv A))
  inferInstanceAs (E.symm.symm.CommShift A)

variable {F : Type*} [Category F] [HasShift F A] {E' : D ≌ F} [E.CommShift A]
    [E'.functor.CommShift A] [E'.inverse.CommShift A] [E'.CommShift A]

/--
If `E : C ≌ D` and `E' : D ≌ F` are equivalence whose forward functors are compatible with shifts,
so is `(E.trans E').functor`.
-/
instance : (E.trans E').functor.CommShift A := by
  dsimp
  infer_instance

/--
If `E : C ≌ D` and `E' : D ≌ F` are equivalence whose inverse functors are compatible with shifts,
so is `(E.trans E').inverse`.
-/
instance : (E.trans E').inverse.CommShift A := by
  dsimp
  infer_instance

/--
If equivalences `E : C ≌ D` and `E' : D ≌ F` are compatible with shifts, so is `E.trans E'`.
-/
instance : (E.trans E').CommShift A :=
  inferInstanceAs ((E.toAdjunction.comp E'.toAdjunction).CommShift A)

end CommShift

end

variable (A : Type*) [AddGroup A] [HasShift C A] [HasShift D A]

/--
If `E : C ≌ D` is an equivalence and we have a `CommShift` structure on `E.functor`,
this constructs the unique compatible `CommShift` structure on `E.inverse`.
-/
noncomputable def commShiftInverse [E.functor.CommShift A] : E.inverse.CommShift A :=
  E.toAdjunction.rightAdjointCommShift A

lemma commShift_of_functor [E.functor.CommShift A] :
    letI := E.commShiftInverse A
    E.CommShift A := by
  letI := E.commShiftInverse A
  exact CommShift.mk' _ _ (E.toAdjunction.commShift_of_leftAdjoint A).commShift_unit

/--
If `E : C ≌ D` is an equivalence and we have a `CommShift` structure on `E.inverse`,
this constructs the unique compatible `CommShift` structure on `E.functor`.
-/
noncomputable def commShiftFunctor [E.inverse.CommShift A] : E.functor.CommShift A :=
  E.symm.toAdjunction.rightAdjointCommShift A

lemma commShift_of_inverse [E.inverse.CommShift A] :
    letI := E.commShiftFunctor A
    E.CommShift A := by
  letI := E.commShiftFunctor A
  have := E.symm.commShift_of_functor A
  exact inferInstanceAs (E.symm.symm.CommShift A)
>>>>>>> origin/jriou_localization_bump_deps

end Equivalence

end CategoryTheory
