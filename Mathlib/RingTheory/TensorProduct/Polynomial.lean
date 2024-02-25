/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

-- import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.TensorProduct
import Mathlib.Data.MvPolynomial.Equiv
import Mathlib.Data.Polynomial.Eval

/-! # Tensor products of a polynomial ring

Adaptations of `TensorProduct.finsuppLeft` when the `Finsupp` is a `Polynomial`.

It is messy because `Polynomial` is not a `Finsupp`…
I believe most of this file should go elsewhere,
and maybe the small stuff that remains could be deleted.

TODO : use what has been done for monoid algebras to get alg hom equiv
(or do it directly)

-/
open TensorProduct LinearMap

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}
  [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {S : Type*} [CommSemiring S] [Algebra R S]

section Module

open Polynomial

variable [AddCommMonoid N] [Module R N]

-- keep ?
noncomputable def LinearEquiv.rTensor
    (P : Type*) (e : M ≃ₗ[R] N)  [AddCommMonoid P] [Module R P] :
    M ⊗[R] P ≃ₗ[R] N ⊗[R] P := TensorProduct.congr e (refl R P)

-- TODO : lTensor ?


lemma TensorProduct.map_isLinearMap'
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    {P : Type*} [AddCommMonoid P] [Module R P]
    {Q : Type*} [AddCommMonoid Q] [Module R Q]
    (e : M →ₗ[S] N) (f : P →ₗ[R] Q) :
    IsLinearMap S (TensorProduct.map (e.restrictScalars R) f) where
  map_add := LinearMap.map_add _
  map_smul := fun s t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [smul_add, map_add] at hx hy ⊢
      simp only [hx, hy]
    | tmul m p =>
      rw [smul_tmul']
      simp only [map_tmul, coe_restrictScalars, map_smul]
      rfl

lemma TensorProduct.congr_isLinearMap'
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    {P : Type*} [AddCommMonoid P] [Module R P]
    {Q : Type*} [AddCommMonoid Q] [Module R Q]
    (e : M ≃ₗ[S] N) (f : P ≃ₗ[R] Q) :
    IsLinearMap S (TensorProduct.congr (e.restrictScalars R) f) :=
  TensorProduct.map_isLinearMap' e.toLinearMap f.toLinearMap

lemma LinearEquiv.rTensor_isLinearMap'
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    (P : Type*) [AddCommMonoid P] [Module R P] (e : M ≃ₗ[S] N) :
    IsLinearMap S (LinearEquiv.rTensor P (e.restrictScalars R)) :=
  TensorProduct.map_isLinearMap' e.toLinearMap _

noncomputable def LinearEquiv.rTensor'
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    (P : Type*) [AddCommMonoid P] [Module R P] (e : M ≃ₗ[S] N) :
    M ⊗[R] P ≃ₗ[S] N ⊗[R] P := {
  (LinearEquiv.rTensor P (e.restrictScalars R)) with
  map_smul' := (LinearEquiv.rTensor_isLinearMap' P e).map_smul }

lemma LinearEquiv.rTensor'_apply
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    (P : Type*) [AddCommMonoid P] [Module R P] (e : M ≃ₗ[S] N)
    (mp : M ⊗[R] P) :
    LinearEquiv.rTensor' P e mp = LinearEquiv.rTensor P (e.restrictScalars R) mp := rfl

namespace Polynomial

def toFinsuppLinearEquiv : S[X] ≃ₗ[S] (ℕ →₀ S) := {
  toFinsuppIso S  with
  map_smul' := fun r p => by simp }

noncomputable def rTensor :
    Polynomial R ⊗[R] N ≃ₗ[R] ℕ →₀ N :=
  (LinearEquiv.rTensor N toFinsuppLinearEquiv).trans TensorProduct.finsuppScalarLeft

lemma rTensor_apply_tmul_apply (p : Polynomial R) (n : N) (i : ℕ) :
    rTensor (p ⊗ₜ[R] n) i = (coeff p i) • n := by
  simp only [rTensor, LinearEquiv.trans_apply]
  simp only [LinearEquiv.rTensor, congr_tmul, LinearEquiv.refl_apply]
  rw [finsuppScalarLeft_apply_tmul_apply _ n i]
  rfl

lemma rTensor_apply_tmul (p : Polynomial R) (n : N) :
    Polynomial.rTensor (p ⊗ₜ[R] n) = p.sum (fun i r => Finsupp.single i (r • n)) := by
  ext i
  rw [rTensor_apply_tmul_apply]
  rw [sum_def]
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single i]
  · simp only [Finsupp.single_eq_same]
  · exact fun _ _ => Finsupp.single_eq_of_ne
  · intro h
    simp only [mem_support_iff, ne_eq, not_not] at h
    rw [h, zero_smul, Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply]

noncomputable def rTensor' :
    Polynomial S ⊗[R] N ≃ₗ[S] ℕ →₀ (S ⊗[R] N) :=
  (LinearEquiv.rTensor' N toFinsuppLinearEquiv).trans TensorProduct.finsuppLeft'

lemma rTensor'_apply_tmul_apply (p : Polynomial S) (n : N) (i : ℕ) :
    rTensor' (p ⊗ₜ[R] n) i = (coeff p i) ⊗ₜ[R] n := by
  simp only [rTensor', LinearEquiv.trans_apply, finsuppLeft'_apply]
  simp only [LinearEquiv.rTensor'_apply, LinearEquiv.rTensor, congr_tmul,
    LinearEquiv.restrictScalars_apply, LinearEquiv.refl_apply]
  simp only [toFinsuppLinearEquiv, RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
    Equiv.invFun_as_coe, LinearEquiv.coe_mk, toFinsuppIso_apply]
  rw [finsuppLeft_apply_tmul_apply]
  rfl

end Polynomial

end Module

section Algebra

namespace Polynomial

variable [CommSemiring N] [Algebra R N]

section

variable {R A B : Type*} [CommSemiring R]
    [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra R B]

noncomputable def mapAlgHom (f : A →ₐ[R] B) :
    A[X] →ₐ[R] B[X] := {
  mapRingHom (f : A →+* B) with
  commutes' := fun r => by
    have hA : (algebraMap R A[X]) r = C ((algebraMap R A) r) := rfl
    have hB : (algebraMap R B[X]) r = C ((algebraMap R B) r) := rfl
    rw [hA, hB]
    simp
  toFun := map (f : A →+* B) }

/-- If `e : A ≃ₐ[R] B` is an isomorphism of `R`-algebras, then so is `map e`. -/
@[simps apply]
noncomputable def mapAlgEquiv (e : A ≃ₐ[R] B) :
    Polynomial A ≃ₐ[R] Polynomial B :=
  { mapAlgHom (e : A →ₐ[R] B), mapEquiv (e : A ≃+* B) with
    toFun := map (e : A →+* B) }

end

noncomputable def rTensorAlgHom :
    (Polynomial S) ⊗[R] N →ₐ[S] Polynomial (S ⊗[R] N) :=
  Algebra.TensorProduct.lift
    (mapAlgHom Algebra.TensorProduct.includeLeft)
    ((IsScalarTower.toAlgHom R (S ⊗[R] N) _).comp Algebra.TensorProduct.includeRight)
    (fun p n => by simp only [commute_iff_eq, mul_comm])

lemma rTensorAlgHom_coeff_apply_tmul
    (p : Polynomial S) (n : N) (d : ℕ) :
    coeff (rTensorAlgHom (p ⊗ₜ[R] n)) d = (coeff p d) ⊗ₜ[R] n := by
  rw [rTensorAlgHom, Algebra.TensorProduct.lift_tmul]
  rw [AlgHom.coe_comp, IsScalarTower.coe_toAlgHom', Function.comp_apply, Algebra.TensorProduct.includeRight_apply]
  rw [← C_eq_algebraMap, mul_comm, coeff_C_mul]
  simp [mapAlgHom, coeff_map]

noncomputable def rTensorLinearEquiv :
    (Polynomial S) ⊗[R] N ≃ₗ[S] Polynomial (S ⊗[R] N) :=
  ((LinearEquiv.rTensor' N toFinsuppLinearEquiv).trans finsuppLeft').trans (toFinsuppLinearEquiv.symm.restrictScalars S)

lemma rTensorLinearEquiv_coeff_tmul (p : Polynomial S) (n : N) (e : ℕ) :
    coeff (rTensorLinearEquiv (S := S) (p ⊗ₜ[R] n)) e = (coeff p e) ⊗ₜ[R] n := by
  dsimp [coeff]
  have h : (rTensorLinearEquiv (S := S) (p ⊗ₜ[R] n)).toFinsupp
    = TensorProduct.finsuppLeft' (S := S) (p.toFinsupp ⊗ₜ[R] n) := by
    rfl
  rw [h, finsuppLeft'_apply, finsuppLeft_apply_tmul_apply]

lemma rTensorAlgHom_toLinearMap :
    (rTensorAlgHom.toLinearMap : (Polynomial S) ⊗[R] N →ₗ[S] Polynomial (S ⊗[R] N))
      = rTensorLinearEquiv.toLinearMap:= by
  ext d n e
  dsimp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply]
  simp only [coe_comp, Function.comp_apply, AlgebraTensorModule.curry_apply, curry_apply,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe]
  rw [rTensorAlgHom_coeff_apply_tmul, rTensorLinearEquiv_coeff_tmul]

lemma rTensorAlgHom_apply_eq (p : Polynomial S ⊗[R] N) :
    rTensorAlgHom (S := S) p = rTensorLinearEquiv (S := S) p := by
  rw [← AlgHom.toLinearMap_apply, rTensorAlgHom_toLinearMap]
  rfl

noncomputable def rTensorAlgEquiv :
    (Polynomial S) ⊗[R] N ≃ₐ[S] Polynomial (S ⊗[R] N) := by
  apply AlgEquiv.ofLinearEquiv
    (rTensorLinearEquiv : Polynomial S ⊗[R] N ≃ₗ[S] Polynomial (S ⊗[R] N))
  · simp only [Algebra.TensorProduct.one_def]
    apply symm
    ext e
    simp only [rTensorLinearEquiv_coeff_tmul, coeff_one]
    split_ifs ; rfl ; simp only [zero_tmul]
  · intro x y
    erw [← rTensorAlgHom_apply_eq (S := S)]
    simp only [_root_.map_mul, rTensorAlgHom_apply_eq]

/-- The tensor product of a polynomial ring  with an algebra is a polynomial ring -/
noncomputable def Polynomial.scalarRTensorAlgEquiv :
    Polynomial R ⊗[R] N ≃ₐ[R] Polynomial N :=
  rTensorAlgEquiv.trans (mapAlgEquiv (Algebra.TensorProduct.lid R N))

end Polynomial

end Algebra

#lint
