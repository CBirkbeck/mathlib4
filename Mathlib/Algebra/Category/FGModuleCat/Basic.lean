/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.LinearAlgebra.Coevaluation
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-!
# The category of finitely generated modules over a ring

This introduces `FGModuleCat R`, the category of finitely generated modules over a ring `R`.
It is implemented as a full subcategory on a subtype of `ModuleCat R`.

When `K` is a field,
`FGModuleCatCat K` is the category of finite dimensional vector spaces over `K`.

We first create the instance as a preadditive category.
When `R` is commutative we then give the structure as an `R`-linear monoidal category.
When `R` is a field we give it the structure of a closed monoidal category
and then as a right-rigid monoidal category.

## Future work

* Show that `FGModuleCat R` is abelian when `R` is (left)-noetherian.

-/


noncomputable section

open CategoryTheory ModuleCat.monoidalCategory

universe u

section Ring

variable (R : Type u) [Ring R]

/-- Define `FGModuleCat` as the subtype of `ModuleCat.{u} R` of finitely generated modules. -/
def FGModuleCat :=
  FullSubcategory fun V : ModuleCat.{u} R => Module.Finite R V
-- Porting note: still no derive handler via `dsimp`.
-- see https://github.com/leanprover-community/mathlib4/issues/5020
-- deriving LargeCategory, ConcreteCategory,Preadditive

variable {R}

/-- A synonym for `M.obj.carrier`, which we can mark with `@[coe]`. -/
def FGModuleCat.carrier (M : FGModuleCat R) : Type u := M.obj.carrier

instance : CoeSort (FGModuleCat R) (Type u) :=
  ⟨FGModuleCat.carrier⟩

attribute [coe] FGModuleCat.carrier

@[simp] lemma obj_carrier (M : FGModuleCat R) : M.obj.carrier = M.carrier := rfl

instance (M : FGModuleCat R) : AddCommGroup M := by
  change AddCommGroup M.obj
  infer_instance

instance (M : FGModuleCat R) : Module R M := by
  change Module R M.obj
  infer_instance

instance : LargeCategory (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

instance {M N : FGModuleCat R} : FunLike (M ⟶ N) M N :=
  LinearMap.instFunLike

instance {M N : FGModuleCat R} : LinearMapClass (M ⟶ N) R M N :=
  LinearMap.semilinearMapClass

instance : ConcreteCategory (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

instance : Preadditive (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

end Ring

namespace FGModuleCat

section Ring

variable (R : Type u) [Ring R]

instance finite (V : FGModuleCat R) : Module.Finite R V :=
  V.property

instance : Inhabited (FGModuleCat R) :=
  ⟨⟨ModuleCat.of R R, Module.Finite.self R⟩⟩

/-- Lift an unbundled finitely generated module to `FGModuleCat R`. -/
def of (V : Type u) [AddCommGroup V] [Module R V] [Module.Finite R V] : FGModuleCat R :=
  ⟨ModuleCat.of R V, by change Module.Finite R V; infer_instance⟩

instance (V : FGModuleCat R) : Module.Finite R V :=
  V.property

instance : HasForget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) := by
  dsimp [FGModuleCat]
  infer_instance

instance : (forget₂ (FGModuleCat R) (ModuleCat.{u} R)).Full where
  map_surjective f := ⟨f, rfl⟩

variable {R}

/-- Converts and isomorphism in the category `FGModuleCat R` to
a `LinearEquiv` between the underlying modules. -/
def isoToLinearEquiv {V W : FGModuleCat R} (i : V ≅ W) : V ≃ₗ[R] W :=
  ((forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).mapIso i).toLinearEquiv

/-- Converts a `LinearEquiv` to an isomorphism in the category `FGModuleCat R`. -/
@[simps]
def _root_.LinearEquiv.toFGModuleCatIso
    {V W : Type u} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W] (e : V ≃ₗ[R] W) :
    FGModuleCat.of R V ≅ FGModuleCat.of R W where
  hom := e.toLinearMap
  inv := e.symm.toLinearMap
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x

end Ring

section CommRing

variable (R : Type u) [CommRing R]

instance : Linear R (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

open scoped MonoidalCategory in
@[simps]
instance : MonoidalCategoryStruct (FGModuleCat R) where
  tensorObj X Y := ⟨X.1 ⊗ Y.1, Module.Finite.tensorProduct R X Y⟩
  whiskerLeft X _ _ f := X.1 ◁ f
  whiskerRight {X₁ X₂} (f : X₁.1 ⟶ X₂.1) Y := (f ▷ Y.1 :)
  tensorHom {X Y W Z} (f : X.1 ⟶ Y.1) (g : W.1 ⟶ Z.1) := (f ⊗ g :)
  tensorUnit := ⟨ModuleCat.of R R, Module.Finite.self R⟩
  associator X Y Z := ⟨(α_ X.1 Y.1 Z.1).hom, (α_ X.1 Y.1 Z.1).inv,
      (α_ X.1 Y.1 Z.1).hom_inv_id, (α_ X.1 Y.1 Z.1).inv_hom_id⟩
  leftUnitor X :=
    let lid := (TensorProduct.lid R X.1).toModuleIso
    ⟨lid.hom, lid.inv, lid.hom_inv_id, lid.inv_hom_id⟩
  rightUnitor X :=
    let rid := (TensorProduct.rid R X.1).toModuleIso
    ⟨rid.hom, rid.inv, rid.hom_inv_id, rid.inv_hom_id⟩

@[simps]
def moduleCatInducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (FGModuleCat R) (ModuleCat R)) where
  μIso X Y := Iso.refl _
  εIso := ModuleCat.tensorUnitIso R
  associator_eq X Y Z := TensorProduct.ext_threefold fun x y z => rfl
  leftUnitor_eq X := TensorProduct.ext rfl
  rightUnitor_eq X := TensorProduct.ext rfl

instance : MonoidalCategory (FGModuleCat R) :=
  Monoidal.induced (forget₂ (FGModuleCat R) (ModuleCat R)) <| moduleCatInducingFunctorData R

/-- `forget₂ (FGModuleCat R) (ModuleCat R)` as a monoidal functor. -/
def forget₂Monoidal : MonoidalFunctor (FGModuleCat R) (ModuleCat R) := by
  unfold instMonoidalCategory
  exact Monoidal.fromInduced (forget₂ (FGModuleCat R) (ModuleCat R)) _

instance : (forget₂Monoidal R).Faithful :=
  forget₂_faithful _ _

instance forget₂Monoidal_additive : (forget₂Monoidal R).Additive := by
  dsimp [forget₂Monoidal]
  -- Porting note (#11187): was `infer_instance`
  exact Functor.fullSubcategoryInclusion_additive _

instance forget₂Monoidal_linear : (forget₂Monoidal R).Linear R := by
  dsimp [forget₂Monoidal]
  -- Porting note (#11187): was `infer_instance`
  exact Functor.fullSubcategoryInclusionLinear _ _

open MonoidalCategory

@[simp] lemma tensorUnit_obj : (𝟙_ (FGModuleCat R)).obj = ModuleCat.of R R := rfl
@[simp] lemma tensorObj_obj (M N : FGModuleCat.{u} R) : (M ⊗ N).obj = (M.obj ⊗ N.obj) := rfl

instance : BraidedCategory (FGModuleCat.{u} R) :=
  braidedCategoryOfFaithful (forget₂Monoidal R)
    (fun X Y =>  ⟨(β_ X.1 Y.1).hom, (β_ X.1 Y.1).inv,
      (β_ X.1 Y.1).hom_inv_id, (β_ X.1 Y.1).inv_hom_id⟩)
    (by aesop_cat)

/-- `forget₂ (FGModuleCat R) (ModuleCat R)` as a braided functor. -/
@[simps toMonoidalFunctor]
def forget₂Braided : BraidedFunctor (FGModuleCat.{u} R) (ModuleCat.{u} R) where
  toMonoidalFunctor := forget₂Monoidal R

instance : (forget₂Braided R).Faithful :=
  forget₂_faithful _ _

instance instSymmetricCategory : SymmetricCategory (FGModuleCat.{u} R) :=
  symmetricCategoryOfFaithful (forget₂Braided R)

instance : MonoidalPreadditive (FGModuleCat R) where

instance : MonoidalLinear R (FGModuleCat R) where

theorem Iso.conj_eq_conj {V W : FGModuleCat R} (i : V ≅ W) (f : End V) :
    Iso.conj i f = LinearEquiv.conj (isoToLinearEquiv i) f :=
  rfl

end CommRing

section Field

variable (K : Type u) [Field K]

instance (V W : FGModuleCat K) : Module.Finite K (V ⟶ W) :=
  (by infer_instance : Module.Finite K (V →ₗ[K] W))

instance closedPredicateModuleFinite :
    MonoidalCategory.ClosedPredicate fun V : ModuleCat.{u} K ↦ Module.Finite K V where
  prop_ihom {X Y} _ _ := Module.Finite.linearMap K K X Y

instance : MonoidalClosed (FGModuleCat K) where
  closed X :=
    { rightAdj := FullSubcategory.lift _ (fullSubcategoryInclusion _ ⋙ ihom X.1)
        fun Y => Module.Finite.linearMap K K X Y
      adj :=
        { unit :=
          { app := fun Y => (ihom.coev X.1).app Y.1
            naturality := fun _ _ f => ihom.coev_naturality X.1 f }
          counit :=
          { app := fun Y => (ihom.ev X.1).app Y.1
            naturality := fun _ _ f => ihom.ev_naturality X.1 f }
          left_triangle_components := fun _ ↦ TensorProduct.ext' fun _ _ => rfl
          right_triangle_components := fun _ ↦ rfl } }

variable (V W : FGModuleCat K)

@[simp]
theorem ihom_obj : (ihom V).obj W = FGModuleCat.of K (V →ₗ[K] W) :=
  rfl

/-- The dual module is the dual in the rigid monoidal category `FGModuleCat K`. -/
def FGModuleCatDual : FGModuleCat K :=
  ⟨ModuleCat.of K (Module.Dual K V), Subspace.instModuleDualFiniteDimensional⟩

@[simp] lemma FGModuleCatDual_obj : (FGModuleCatDual K V).obj = ModuleCat.of K (Module.Dual K V) :=
  rfl
@[simp] lemma FGModuleCatDual_coe : (FGModuleCatDual K V : Type u) = Module.Dual K V := rfl

open CategoryTheory.MonoidalCategory

/-- The coevaluation map is defined in `LinearAlgebra.coevaluation`. -/
def FGModuleCatCoevaluation : 𝟙_ (FGModuleCat K) ⟶ V ⊗ FGModuleCatDual K V :=
  coevaluation K V

theorem FGModuleCatCoevaluation_apply_one :
    FGModuleCatCoevaluation K V (1 : K) =
      ∑ i : Basis.ofVectorSpaceIndex K V,
        (Basis.ofVectorSpace K V) i ⊗ₜ[K] (Basis.ofVectorSpace K V).coord i :=
  coevaluation_apply_one K V

/-- The evaluation morphism is given by the contraction map. -/
def FGModuleCatEvaluation : FGModuleCatDual K V ⊗ V ⟶ 𝟙_ (FGModuleCat K) :=
  contractLeft K V

@[simp]
theorem FGModuleCatEvaluation_apply (f : FGModuleCatDual K V) (x : V) :
    (FGModuleCatEvaluation K V) (f ⊗ₜ x) = f.toFun x :=
  contractLeft_apply f x

private theorem coevaluation_evaluation :
    letI V' : FGModuleCat K := FGModuleCatDual K V
    V' ◁ FGModuleCatCoevaluation K V ≫ (α_ V' V V').inv ≫ FGModuleCatEvaluation K V ▷ V' =
      (ρ_ V').hom ≫ (λ_ V').inv := by
  apply contractLeft_assoc_coevaluation K V

private theorem evaluation_coevaluation :
    FGModuleCatCoevaluation K V ▷ V ≫
        (α_ V (FGModuleCatDual K V) V).hom ≫ V ◁ FGModuleCatEvaluation K V =
      (λ_ V).hom ≫ (ρ_ V).inv := by
  apply contractLeft_assoc_coevaluation' K V

instance exactPairing : ExactPairing V (FGModuleCatDual K V) where
  coevaluation' := FGModuleCatCoevaluation K V
  evaluation' := FGModuleCatEvaluation K V
  coevaluation_evaluation' := coevaluation_evaluation K V
  evaluation_coevaluation' := evaluation_coevaluation K V

instance rightDual : HasRightDual V :=
  ⟨FGModuleCatDual K V⟩

instance rightRigidCategory : RightRigidCategory (FGModuleCat K) where

end Field

end FGModuleCat

/-!
`@[simp]` lemmas for `LinearMap.comp` and categorical identities.
-/

@[simp] theorem LinearMap.comp_id_fgModuleCat
    {R} [Ring R] {G : FGModuleCat.{u} R} {H : Type u} [AddCommGroup H] [Module R H]
    (f : G →ₗ[R] H) : f.comp (𝟙 G) = f :=
  Category.id_comp (ModuleCat.ofHom f)
@[simp] theorem LinearMap.id_fgModuleCat_comp
    {R} [Ring R] {G : Type u} [AddCommGroup G] [Module R G] {H : FGModuleCat.{u} R}
    (f : G →ₗ[R] H) : LinearMap.comp (𝟙 H) f = f :=
  Category.comp_id (ModuleCat.ofHom f)
