/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Antoine Chambert-Loir
-/
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Tower

#align_import linear_algebra.direct_sum.finsupp from "leanprover-community/mathlib"@"9b9d125b7be0930f564a68f1d73ace10cf46064d"

/-!
# Results on finitely supported functions.

* `TensorProduct.finsuppLeft`, the tensor product of `i →₀ M` and `N`
  is linearly equivalent to `i →₀ M ⊗[R] N`

* `TensorProduct.finsuppScalarLeft`, the tensor product of `i →₀ R` and `N`
  is linearly equivalent to `i →₀ N`

* `TensorProduct.finsuppRight`, the tensor product of `M` and `i →₀ N`
  is linearly equivalent to `i →₀ M ⊗[R] N`

* `TensorProduct.finsuppLeft'`, if `M` is an `S`-module,
  then the tensor product of `i →₀ M` and `N` is `S`-linearly equivalent
  to `i →₀ M ⊗[R] N`

* `finsuppTensorFinsupp`, the tensor product of `ι →₀ M` and `κ →₀ N`
  is linearly equivalent to `(ι × κ) →₀ (M ⊗ N)`.

## Case of MvPolynomial

These functions apply to `MvPolynomial`, one can define
```
noncomputable def MvPolynomial.rTensor' :
    MvPolynomial σ S ⊗[R] N ≃ₗ[S] (σ →₀ ℕ) →₀ (S ⊗[R] N) :=
  TensorProduct.finsuppLeft'

noncomputable def MvPolynomial.rTensor :
    MvPolynomial σ R ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ N :=
  TensorProduct.finsuppScalarLeft
 ```

## Case of `Polynomial`

`Polynomial` is a structure containing a `Finsupp`, so these functions
can't be applied directly to `Polynomial`.

Some linear equivs need to be added to mathlib for that.

## TODO

* generalize to `MonoidAlgebra`, `AlgHom `

* reprove `TensorProduct.finsuppLeft'` using existing heterobasic version of `TensorProduct.congr`
-/


universe u v w

noncomputable section

open DirectSum TensorProduct

open Set LinearMap Submodule

variable {R : Type u} {M : Type v} {N : Type w}
  [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

section TensorProduct

namespace TensorProduct

variable {ι : Type*} [DecidableEq ι]

/-- The tensor product of `i →₀ M` and `N` is linearly equivalent to `i →₀ M ⊗[R] N` -/
noncomputable def finsuppLeft :
    (ι →₀ M) ⊗[R] N ≃ₗ[R] ι →₀ (M ⊗[R] N) :=
  (congr (finsuppLEquivDirectSum R M ι) (LinearEquiv.refl R N)).trans
    ((directSumLeft R (fun _ : ι => M) N).trans
      (finsuppLEquivDirectSum R (M ⊗[R] N) ι).symm)

lemma finsuppLeft_apply_tmul (p : ι →₀ M) (n : N) :
    finsuppLeft (p ⊗ₜ[R] n) = p.sum (fun i m ↦ Finsupp.single i (m ⊗ₜ[R] n)) := by
  simp only [finsuppLeft, LinearEquiv.trans_apply, congr_tmul, LinearEquiv.refl_apply]
  conv_lhs => rw [← Finsupp.sum_single p]
  rw [LinearEquiv.symm_apply_eq]
  simp only [map_finsupp_sum]
  simp only [finsuppLEquivDirectSum_single]
  rw [← LinearEquiv.eq_symm_apply]
  simp only [map_finsupp_sum]
  simp only [directSumLeft_symm_lof_tmul]
  simp only [Finsupp.sum, sum_tmul]

lemma finsuppLeft_apply_tmul_apply (p : ι →₀ M) (n : N) (i : ι) :
    finsuppLeft (p ⊗ₜ[R] n) i = p i ⊗ₜ[R] n := by
  rw [finsuppLeft_apply_tmul]
  simp only [Finsupp.sum_apply]
  conv_rhs => rw [← Finsupp.single_eq_same (a := i) (b := p i ⊗ₜ[R] n)]
  apply Finsupp.sum_eq_single i
  · exact fun _ _ ↦ Finsupp.single_eq_of_ne
  · intro _
    simp

lemma finsuppLeft_symm_apply_single (i : ι) (m : M) (n : N) :
    finsuppLeft.symm (Finsupp.single i (m ⊗ₜ[R] n)) =
      Finsupp.single i m ⊗ₜ[R] n := by
  simp [finsuppLeft, Finsupp.lsum]

/-- The tensor product of `M` and `i →₀ N` is linearly equivalent to `i →₀ M ⊗[R] N` -/
noncomputable def finsuppRight :
    M ⊗[R] (ι →₀ N) ≃ₗ[R] ι →₀ (M ⊗[R] N) :=
  (congr (LinearEquiv.refl R M) (finsuppLEquivDirectSum R N ι)).trans
    ((directSumRight R M (fun _ : ι => N)).trans
      (finsuppLEquivDirectSum R (M ⊗[R] N) ι).symm)

lemma finsuppRight_apply_tmul (m : M) (p : ι →₀ N) :
    finsuppRight (m ⊗ₜ[R] p) = p.sum (fun i n ↦ Finsupp.single i (m ⊗ₜ[R] n)) := by
  simp [finsuppRight]
  conv_lhs => rw [← Finsupp.sum_single p]
  rw [LinearEquiv.symm_apply_eq]
  simp only [map_finsupp_sum]
  simp only [finsuppLEquivDirectSum_single]
  rw [← LinearEquiv.eq_symm_apply]
  simp only [map_finsupp_sum]
  simp only [directSumRight_symm_lof_tmul]
  simp only [Finsupp.sum, tmul_sum]

lemma finsuppRight_symm_apply_single (i : ι) (m : M) (n : N) :
    finsuppLeft.symm (Finsupp.single i (m ⊗ₜ[R] n)) =
      Finsupp.single i m ⊗ₜ[R] n := by
  simp [finsuppLeft, Finsupp.lsum]

variable {S : Type*} [CommSemiring S] [Algebra R S]
  [Module S M] [IsScalarTower R S M]

lemma finsuppLeft_smul' (s : S) (t : (ι →₀ M) ⊗[R] N) :
    finsuppLeft (s • t) = s • finsuppLeft t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [AddHom.toFun_eq_coe, coe_toAddHom, LinearEquiv.coe_coe, RingHom.id_apply] at hx hy ⊢
    simp only [smul_add, map_add, hx, hy]
  | tmul p n =>
    simp only [smul_tmul', finsuppLeft_apply_tmul]
    rw [Finsupp.smul_sum]
    simp only [Finsupp.smul_single]
    apply Finsupp.sum_smul_index'
    simp

/-- When `M` is also an `S`-module, then `TensorProduct.finsuppLeft R M N``
  is an `S`-linear equiv -/
noncomputable def finsuppLeft' :
    (ι →₀ M) ⊗[R] N ≃ₗ[S] ι →₀ (M ⊗[R] N) := {
  finsuppLeft with
  map_smul' := finsuppLeft_smul' }

lemma finsuppLeft'_apply (x : (ι →₀ M) ⊗[R] N) :
    finsuppLeft' (S := S) x = finsuppLeft x :=
  rfl

/- -- TODO : reprove using the existing heterobasic lemmas
noncomputable example :
    (ι →₀ M) ⊗[R] N ≃ₗ[S] ι →₀ (M ⊗[R] N) := by
  have f : (⨁ (i₁ : ι), M) ⊗[R] N ≃ₗ[S] ⨁ (i : ι), M ⊗[R] N := sorry
  exact (AlgebraTensorModule.congr
    (finsuppLEquivDirectSum S M ι) (LinearEquiv.refl R N)).trans
    (f.trans (finsuppLEquivDirectSum S (M ⊗[R] N) ι).symm) -/

/-- The tensor product of `i →₀ R` and `N` is linearly equivalent to `i →₀ N` -/
noncomputable def finsuppScalarLeft :
    (ι →₀ R) ⊗[R] N ≃ₗ[R] ι →₀ N :=
  finsuppLeft.trans (Finsupp.mapRange.linearEquiv (TensorProduct.lid R N))

lemma finsuppScalarLeft_apply_tmul_apply (p : ι →₀ R) (n : N) (i : ι) :
    finsuppScalarLeft (p ⊗ₜ[R] n) i = (p i) • n := by
  simp only [finsuppScalarLeft, LinearEquiv.trans_apply, finsuppLeft_apply_tmul,
    Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange.linearMap_apply, LinearEquiv.coe_coe,
    Finsupp.mapRange_apply, Finsupp.sum_apply]
  apply symm
  rw [← LinearEquiv.symm_apply_eq, lid_symm_apply]
  rw [Finsupp.sum_eq_single i (fun _ _ => Finsupp.single_eq_of_ne) (fun _ => by simp)]
  simp only [Finsupp.single_eq_same]
  rw [tmul_smul, smul_tmul', smul_eq_mul, mul_one]

lemma finsuppScalarLeft_apply_tmul (p : ι →₀ R) (n : N) :
    finsuppScalarLeft (p ⊗ₜ[R] n) = p.sum (fun i m ↦ Finsupp.single i (m • n)) := by
  ext i
  rw [finsuppScalarLeft_apply_tmul_apply]
  simp only [Finsupp.sum_apply]
  rw [Finsupp.sum_eq_single i (fun _ _ => Finsupp.single_eq_of_ne) (fun _ => by simp)]
  simp only [Finsupp.single_eq_same]

lemma finsuppScalarLeft_symm_apply_single (i : ι) (n : N) :
    finsuppScalarLeft.symm (Finsupp.single i n) =
      (Finsupp.single i 1) ⊗ₜ[R] n := by
  simp [finsuppScalarLeft, finsuppLeft_symm_apply_single]

end TensorProduct

open scoped Classical in
-- `noncomputable` is a performance workaround for mathlib4#7103
/-- The tensor product of `ι →₀ M` and `κ →₀ N` is linearly equivalent to `(ι × κ) →₀ (M ⊗ N)`. -/
noncomputable def finsuppTensorFinsupp (R M N ι κ : Sort _) [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] : (ι →₀ M) ⊗[R] (κ →₀ N) ≃ₗ[R] ι × κ →₀ M ⊗[R] N :=
  TensorProduct.congr (finsuppLEquivDirectSum R M ι) (finsuppLEquivDirectSum R N κ) ≪≫ₗ
    ((TensorProduct.directSum R (fun _ : ι => M) fun _ : κ => N) ≪≫ₗ
      (finsuppLEquivDirectSum R (M ⊗[R] N) (ι × κ)).symm)
#align finsupp_tensor_finsupp finsuppTensorFinsupp

@[simp]
theorem finsuppTensorFinsupp_single (R M N ι κ : Sort _)
    [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (i : ι) (m : M) (k : κ) (n : N) :
    finsuppTensorFinsupp R M N ι κ (Finsupp.single i m ⊗ₜ Finsupp.single k n) =
      Finsupp.single (i, k) (m ⊗ₜ n) :=
  by classical simp [finsuppTensorFinsupp]
#align finsupp_tensor_finsupp_single finsuppTensorFinsupp_single

@[simp]
theorem finsuppTensorFinsupp_apply (R M N ι κ : Sort _)
    [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : ι →₀ M) (g : κ →₀ N) (i : ι) (k : κ) :
    finsuppTensorFinsupp R M N ι κ (f ⊗ₜ g) (i, k) = f i ⊗ₜ g k := by
  apply Finsupp.induction_linear f
  · simp
  · intro f₁ f₂ hf₁ hf₂
    simp [add_tmul, hf₁, hf₂]
  · intro i' m
    apply Finsupp.induction_linear g
    · simp
    · intro g₁ g₂ hg₁ hg₂
      simp [tmul_add, hg₁, hg₂]
    · intro k' n
      simp only [finsuppTensorFinsupp_single]
      -- split_ifs; finish can close the goal from here
      by_cases h1 : (i', k') = (i, k)
      · simp only [Prod.mk.inj_iff] at h1
        simp [h1]
      · simp only [Prod.mk.inj_iff, not_and_or] at h1
        cases' h1 with h1 h1 <;> simp [h1]
#align finsupp_tensor_finsupp_apply finsuppTensorFinsupp_apply

@[simp]
theorem finsuppTensorFinsupp_symm_single (R M N ι κ : Sort _) [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (i : ι × κ) (m : M) (n : N) :
    (finsuppTensorFinsupp R M N ι κ).symm (Finsupp.single i (m ⊗ₜ n)) =
      Finsupp.single i.1 m ⊗ₜ Finsupp.single i.2 n :=
  Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsupp_single _ _ _ _ _ _ _ _ _).symm
#align finsupp_tensor_finsupp_symm_single finsuppTensorFinsupp_symm_single

variable (S : Type*) [CommRing S] (α β : Type*)

/-- A variant of `finsuppTensorFinsupp` where both modules are the ground ring. -/
def finsuppTensorFinsupp' : (α →₀ S) ⊗[S] (β →₀ S) ≃ₗ[S] α × β →₀ S :=
  (finsuppTensorFinsupp S S S α β).trans (Finsupp.lcongr (Equiv.refl _) (TensorProduct.lid S S))
#align finsupp_tensor_finsupp' finsuppTensorFinsupp'

@[simp]
theorem finsuppTensorFinsupp'_apply_apply (f : α →₀ S) (g : β →₀ S) (a : α) (b : β) :
    finsuppTensorFinsupp' S α β (f ⊗ₜ[S] g) (a, b) = f a * g b := by simp [finsuppTensorFinsupp']
#align finsupp_tensor_finsupp'_apply_apply finsuppTensorFinsupp'_apply_apply

@[simp]
theorem finsuppTensorFinsupp'_single_tmul_single (a : α) (b : β) (r₁ r₂ : S) :
    finsuppTensorFinsupp' S α β (Finsupp.single a r₁ ⊗ₜ[S] Finsupp.single b r₂) =
      Finsupp.single (a, b) (r₁ * r₂) := by
  ext ⟨a', b'⟩
  classical
  aesop (add norm [Finsupp.single_apply])
#align finsupp_tensor_finsupp'_single_tmul_single finsuppTensorFinsupp'_single_tmul_single

end TensorProduct
