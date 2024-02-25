/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct
import Mathlib.Data.MvPolynomial.Equiv
/-!

# Tensor Product of polynomial rings

TODO : use what has been done for monoid algebras to get alg hom equiv
(or do it directly)

-/


universe u v w

noncomputable section

namespace MvPolynomial

open DirectSum TensorProduct

open Set LinearMap Submodule

variable {R : Type u} {M : Type v} {N : Type w}
  [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {σ : Type u} [DecidableEq σ]

variable {S : Type*} [CommSemiring S] [Algebra R S]

section Module

variable   [AddCommMonoid N] [Module R N]

noncomputable def rTensor' :
    MvPolynomial σ S ⊗[R] N ≃ₗ[S] (σ →₀ ℕ) →₀ (S ⊗[R] N) :=
  TensorProduct.finsuppLeft'

lemma rTensor'_apply_tmul (p : MvPolynomial σ S) (n : N) :
    rTensor' (p ⊗ₜ[R] n) = p.sum (fun i m ↦ Finsupp.single i (m ⊗ₜ[R] n)) :=
  TensorProduct.finsuppLeft_apply_tmul p n

lemma rTensor'_apply_tmul_apply (p : MvPolynomial σ S) (n : N) (d : σ →₀ ℕ) :
    rTensor' (p ⊗ₜ[R] n) d = (coeff d p) ⊗ₜ[R] n :=
  TensorProduct.finsuppLeft_apply_tmul_apply p n d

lemma rTensor'_symm_apply_single (d : σ →₀ ℕ) (s : S) (n : N) :
    rTensor'.symm (Finsupp.single d (s ⊗ₜ n)) =
      (monomial d s) ⊗ₜ[R] n :=
  TensorProduct.finsuppLeft_symm_apply_single d s n

noncomputable def rTensor :
    MvPolynomial σ R ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ N :=
  TensorProduct.finsuppScalarLeft

lemma rTensor_apply_tmul (p : MvPolynomial σ R) (n : N) :
    rTensor (p ⊗ₜ[R] n) = p.sum (fun i m ↦ Finsupp.single i (m • n)) :=
  TensorProduct.finsuppScalarLeft_apply_tmul p n

lemma rTensor_apply_tmul_apply (p : MvPolynomial σ R) (n : N) (d : σ →₀ ℕ):
    rTensor (p ⊗ₜ[R] n) d = (coeff d p) • n :=
  TensorProduct.finsuppScalarLeft_apply_tmul_apply p n d

lemma rTensor_symm_apply_single (d : σ →₀ ℕ) (n : N) :
    rTensor.symm (Finsupp.single d n) = (monomial d 1) ⊗ₜ[R] n :=
  TensorProduct.finsuppScalarLeft_symm_apply_single d n

end Module

section Algebra

variable [CommSemiring N] [Algebra R N]

noncomputable def rTensorAlgHom :
    (MvPolynomial σ S) ⊗[R] N →ₐ[S] MvPolynomial σ (S ⊗[R] N) :=
  Algebra.TensorProduct.lift
    (mapAlgHom Algebra.TensorProduct.includeLeft)
    ((IsScalarTower.toAlgHom R (S ⊗[R] N) _).comp Algebra.TensorProduct.includeRight)
    (fun p n => by simp [commute_iff_eq, algebraMap_eq, mul_comm])

lemma rTensorAlgHom_coeff_tmul
    (p : MvPolynomial σ S) (n : N) (d : σ →₀ ℕ) :
    coeff d (rTensorAlgHom (p ⊗ₜ[R] n)) = (coeff d p) ⊗ₜ[R] n := by
  rw [rTensorAlgHom, Algebra.TensorProduct.lift_tmul]
  rw [AlgHom.coe_comp, IsScalarTower.coe_toAlgHom', Function.comp_apply, Algebra.TensorProduct.includeRight_apply]
  rw [algebraMap_eq, mul_comm, coeff_C_mul]
  simp [mapAlgHom, coeff_map]

lemma rTensorAlgHom_toLinearMap :
    (rTensorAlgHom :
      MvPolynomial σ S ⊗[R] N →ₐ[S] MvPolynomial σ (S ⊗[R] N)).toLinearMap =
      finsuppLeft'.toLinearMap := by
  ext d n e
  dsimp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply]
  simp only [coe_comp, Function.comp_apply, AlgebraTensorModule.curry_apply, curry_apply,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply]
  rw [rTensorAlgHom_coeff_tmul]
  simp only [coeff]
  erw [finsuppLeft_apply_tmul_apply]

lemma rTensorAlgHom_toLinearMap' :
    (rTensorAlgHom :
      MvPolynomial σ S ⊗[R] N →ₐ[S] MvPolynomial σ (S ⊗[R] N)).toLinearMap.restrictScalars R =
      finsuppLeft.toLinearMap := by
  rw [rTensorAlgHom_toLinearMap]
  rfl

lemma rTensorAlgHom_apply_eq (p : MvPolynomial σ S ⊗[R] N) :
    rTensorAlgHom (S := S) p = finsuppLeft' (S := S) p := by
  rw [← AlgHom.toLinearMap_apply, rTensorAlgHom_toLinearMap]
  rfl

noncomputable def rTensorAlgEquiv :
    (MvPolynomial σ S) ⊗[R] N ≃ₐ[S] MvPolynomial σ (S ⊗[R] N) := by
  apply AlgEquiv.ofLinearEquiv
    (finsuppLeft' : MvPolynomial σ S ⊗[R] N ≃ₗ[S] MvPolynomial σ (S ⊗[R] N))
  · simp only [Algebra.TensorProduct.one_def]
    apply symm
    rw [← LinearEquiv.symm_apply_eq]
    exact finsuppLeft_symm_apply_single (0 : σ →₀ ℕ) (1 : S) (1 : N)
  · intro x y
    erw [← rTensorAlgHom_apply_eq (S := S)]
    simp only [_root_.map_mul, rTensorAlgHom_apply_eq]
    rfl

noncomputable def scalarRTensorAlgEquiv :
    MvPolynomial σ R ⊗[R] N ≃ₐ[R] MvPolynomial σ N :=
  rTensorAlgEquiv.trans (mapAlgEquiv σ (Algebra.TensorProduct.lid R N))

end Algebra

end MvPolynomial

end
