/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.RingTheory.HahnSeries.Binomial

/-!
# Vertex operators
In this file we introduce heterogeneous vertex operators using Hahn series.  When `R = ℂ`, `V = W`,
and `Γ = ℤ`, then this is the usual notion of "meromorphic left-moving 2D field".  The notion we use
here allows us to consider composites and scalar-multiply by multivariable Laurent series.
## Definitions
* `HVertexOperator` : An `R`-linear map from an `R`-module `V` to `HahnModule Γ W`.
* The coefficient function as an `R`-linear map.
* Composition of heterogeneous vertex operators - values are Hahn series on lex order product.
* Composition of heterogeneous vertex operators - values are Hahn series on lex order product.
## Main results
* `HahnSeries Γ R`-module structure on `HVertexOperator Γ R V W`.  This means we can consider
  products of the form `(X-Y)^n A(X)B(Y)` for all integers `n`, where `(X-Y)^n` is expanded as
  `X^n(1-Y/X)^n` in `R((X))((Y))`
## TODO
* curry for tensor product inputs
* more API to make ext comparisons easier.
* formal variable API, e.g., like the `T` function for Laurent polynomials.
## References

* [R. Borcherds, *Vertex Algebras, Kac-Moody Algebras, and the Monster*][borcherds1986vertex]
* G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328
* A. Matsuo, K. Nagatomo `On axioms for a vertex algebra and locality of quantum fields`
  arXiv:hep-th/9706118
* H. Li's paper on local systems?
-/

assert_not_exists Cardinal

noncomputable section

variable {Γ : Type*} [PartialOrder Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- A heterogeneous `Γ`-vertex operator over a commutator ring `R` is an `R`-linear map from an
`R`-module `V` to `Γ`-Hahn series with coefficients in an `R`-module `W`. -/
abbrev HVertexOperator (Γ : Type*) [PartialOrder Γ] (R : Type*) [CommRing R]
    (V : Type*) (W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] :=
  V →ₗ[R] (HahnModule Γ R W)

namespace HVertexOperator

section Coeff

variable {Γ : Type*} [PartialOrder Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

open HahnModule

@[ext]
theorem ext (A B : HVertexOperator Γ R V W) (h : ∀ v : V, A v = B v) :
    A = B := LinearMap.ext h

@[deprecated (since := "2024-06-18")] alias _root_.VertexAlg.HetVertexOperator.ext := ext

/-- The coefficient of a heterogeneous vertex operator, viewed as a formal power series with
coefficients in linear maps. -/
@[simps]
def coeff (A : HVertexOperator Γ R V W) (n : Γ) : V →ₗ[R] W where
  toFun v := ((of R).symm (A v)).coeff n
  map_add' _ _ := by simp
  map_smul' _ _ := by
    simp only [map_smul, RingHom.id_apply, of_symm_smul, HahnSeries.smul_coeff]

@[deprecated (since := "2024-06-18")] alias _root_.VertexAlg.coeff := coeff

theorem coeff_isPWOsupport (A : HVertexOperator Γ R V W) (v : V) :
    ((of R).symm (A v)).coeff.support.IsPWO :=
  ((of R).symm (A v)).isPWO_support'

@[deprecated (since := "2024-06-18")]
alias _root_.VertexAlg.coeff_isPWOsupport := coeff_isPWOsupport

@[ext]
theorem coeff_inj : Function.Injective (coeff : HVertexOperator Γ R V W → Γ → (V →ₗ[R] W)) := by
  intro _ _ h
  ext v n
  exact congrFun (congrArg DFunLike.coe (congrFun h n)) v

@[deprecated (since := "2024-06-18")] alias _root_.VertexAlg.coeff_inj := coeff_inj

/-- Given a coefficient function valued in linear maps satisfying a partially well-ordered support
condition, we produce a heterogeneous vertex operator. -/
@[simps]
def of_coeff (f : Γ → V →ₗ[R] W)
    (hf : ∀ x : V , (Function.support (f · x)).IsPWO) : HVertexOperator Γ R V W where
  toFun x := (of R) { coeff := fun g => f g x, isPWO_support' := hf x }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[deprecated (since := "2024-06-18")] alias _root_.VertexAlg.HetVertexOperator.of_coeff := of_coeff

@[simp]
theorem coeff_of_coeff (f : Γ → V →ₗ[R] W)
    (hf : ∀(x : V), (Function.support (fun g => f g x)).IsPWO) : (of_coeff f hf).coeff = f :=
  rfl

@[simp]
theorem zero_coeff : (0 : HVertexOperator Γ R V W).coeff = 0 :=
  rfl

@[simp]
theorem add_coeff_apply (A B : HVertexOperator Γ R V W) (n : Γ) :
    (A + B).coeff n = A.coeff n + B.coeff n := by
  ext v
  simp [coeff_apply, LinearMap.add_apply, of_symm_add, HahnSeries.add_coeff', Pi.add_apply]

@[simp]
theorem add_coeff (A B : HVertexOperator Γ R V W) : (A + B).coeff = A.coeff + B.coeff := by
  ext1 n
  exact add_coeff_apply A B n

@[simp]
theorem smul_coeff_apply (A : HVertexOperator Γ R V W) (r : R) (n : Γ) :
    (r • A).coeff n = r • (A.coeff) n := by
  ext v
  simp only [coeff_apply, LinearMap.smul_apply, of_symm_smul, HahnSeries.smul_coeff]

@[simp]
theorem smul_coeff (A : HVertexOperator Γ R V W) (r : R) : (r • A).coeff = r • (A.coeff) := by
  ext1 n
  exact smul_coeff_apply A r n

@[simp]
theorem nsmul_coeff (A : HVertexOperator Γ R V W) {n : ℕ} : (n • A).coeff = n • (A.coeff) := by
  induction n with
  | zero => ext; simp
  | succ n ih => ext; simp [add_nsmul, add_coeff, ih]

end Coeff


section Module

variable {Γ Γ' : Type*} [OrderedCancelAddCommMonoid Γ] [PartialOrder Γ'] [AddAction Γ Γ']
  [IsOrderedCancelVAdd Γ Γ'] {R : Type*} [CommRing R] {V W : Type*} [AddCommGroup V]
  [Module R V] [AddCommGroup W] [Module R W]

/-- The scalar multiplication of Hahn series on heterogeneous vertex operators. -/
def HahnSMul (x : HahnSeries Γ R) (A : HVertexOperator Γ' R V W) :
    HVertexOperator Γ' R V W where
  toFun v := x • (A v)
  map_add' u v := by simp only [map_add, smul_add]
  map_smul' r v := by
    simp only [map_smul, RingHom.id_apply]
    exact (HahnModule.smul_comm r x (A v)).symm

instance instHahnModule : Module (HahnSeries Γ R) (HVertexOperator Γ' R V W) where
  smul x A := HahnSMul x A
  one_smul _ := by
    ext _ _
    simp only [one_smul]
  mul_smul _ _ _ := by
    ext _ _
    simp only [LinearMap.smul_apply, mul_smul]
  smul_zero _ := by
    ext _ _
    simp only [smul_zero, LinearMap.zero_apply, HahnModule.of_symm_zero, HahnSeries.zero_coeff]
  smul_add _ _ _ := by
    ext _ _
    simp only [smul_add, LinearMap.add_apply, LinearMap.smul_apply, HahnModule.of_symm_add,
      HahnSeries.add_coeff', Pi.add_apply]
  add_smul _ _ _ := by
    ext _ _
    simp only [coeff_apply, LinearMap.smul_apply, LinearMap.add_apply, HahnSeries.add_coeff']
    rw [HahnModule.add_smul Module.add_smul]
  zero_smul _ := by
    ext _ _
    simp only [zero_smul, LinearMap.zero_apply, HahnModule.of_symm_zero, HahnSeries.zero_coeff]

@[simp]
theorem smul_eq {x : HahnSeries Γ R} {A : HVertexOperator Γ' R V W} {v : V} :
    (x • A) v = x • (A v) :=
  rfl

end  Module

section Products

variable {Γ Γ' : Type*} [OrderedCancelAddCommMonoid Γ] [OrderedCancelAddCommMonoid Γ'] {R : Type*}
  [CommRing R] {U V W : Type*} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ' R U V)

open HahnModule

/-- The composite of two heterogeneous vertex operators acting on a vector, as an iterated Hahn
  series.-/
@[simps]
def compHahnSeries (u : U) : HahnSeries Γ' (HahnSeries Γ W) where
  coeff g' := A (coeff B g' u)
  isPWO_support' := by
    refine Set.IsPWO.mono (((of R).symm (B u)).isPWO_support') ?_
    simp_all only [coeff_apply, Function.support_subset_iff, ne_eq, Function.mem_support]
    exact fun g' hg' hAB => hg' (by simp [hAB])

@[simp]
theorem compHahnSeries.add (u v : U) :
    compHahnSeries A B (u + v) = compHahnSeries A B u + compHahnSeries A B v := by
  ext
  simp only [compHahnSeries_coeff, map_add, coeff_apply, HahnSeries.add_coeff', Pi.add_apply]
  rw [← @HahnSeries.add_coeff]

@[simp]
theorem compHahnSeries.smul {U : Type*} [AddCommGroup U] [Module R U]
    (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ' R U V) (r : R) (u : U) :
    compHahnSeries A B (r • u) = r • compHahnSeries A B u := by
  ext
  rw [HahnSeries.smul_coeff]
  simp only [compHahnSeries_coeff, LinearMapClass.map_smul, coeff_apply]

/-- The composite of two heterogeneous vertex operators, as a heterogeneous vertex operator. -/
@[simps]
def comp : HVertexOperator (Γ' ×ₗ Γ) R U W where
  toFun u := HahnModule.of R (HahnSeries.ofIterate (compHahnSeries A B u))
  map_add' u v := by
    ext g
    simp only [HahnSeries.ofIterate, compHahnSeries.add, Equiv.symm_apply_apply,
      HahnModule.of_symm_add, HahnSeries.add_coeff', Pi.add_apply]
  map_smul' r x := by
    ext g
    simp only [HahnSeries.ofIterate, compHahnSeries.smul, Equiv.symm_apply_apply, RingHom.id_apply,
      HahnSeries.smul_coeff, compHahnSeries_coeff, coeff_apply]
    exact rfl

@[simp]
theorem comp_coeff (g : Γ' ×ₗ Γ) :
    (comp A B).coeff g = A.coeff (ofLex g).2 ∘ₗ B.coeff (ofLex g).1 := by
  rfl

-- TODO: comp_assoc

/-- The restriction of a heterogeneous vertex operator on a lex product to an element of the left
factor. -/
def ResLeft (A : HVertexOperator (Γ' ×ₗ Γ) R V W) (g' : Γ'):  HVertexOperator Γ R V W :=
  HVertexOperator.of_coeff (fun g => coeff A (toLex (g', g)))
    (fun v => Set.PartiallyWellOrderedOn.fiberProdLex (A v).isPWO_support' _)

theorem coeff_ResLeft (A : HVertexOperator (Γ' ×ₗ Γ) R V W) (g' : Γ') (g : Γ) :
    coeff (ResLeft A g') g = coeff A (toLex (g', g)) :=
  rfl

/-- The left residue as a linear map. -/
@[simps]
def ResLeft.linearMap (g' : Γ'):
    HVertexOperator (Γ' ×ₗ Γ) R V W →ₗ[R] HVertexOperator Γ R V W where
  toFun A := ResLeft A g'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coeff_left_lex_supp.isPWO (A : HVertexOperator (Γ ×ₗ Γ') R V W) (g' : Γ') (v : V) :
    (Function.support (fun (g : Γ) => (coeff A (toLex (g, g'))) v)).IsPWO := by
  refine Set.IsPWO.mono (Set.PartiallyWellOrderedOn.imageProdLex (A v).isPWO_support') ?_
  simp_all only [coeff_apply, Function.support_subset_iff, ne_eq, Set.mem_image,
    Function.mem_support]
  exact fun x a ↦ Exists.intro (toLex (x, g')) { left := a, right := rfl }

/-- The restriction of a heterogeneous vertex operator on a lex product to an element of the right
factor. -/
def ResRight (A : HVertexOperator (Γ ×ₗ Γ') R V W) (g' : Γ') : HVertexOperator Γ R V W :=
  HVertexOperator.of_coeff (fun g => coeff A (toLex (g, g')))
    (fun v => coeff_left_lex_supp.isPWO A g' v)

theorem coeff_ResRight (A : HVertexOperator (Γ ×ₗ Γ') R V W) (g' : Γ') (g : Γ) :
    coeff (ResRight A g') g = coeff A (toLex (g, g')) := rfl

/-- The right residue as a linear map. -/
@[simps]
def ResRight.linearMap (g' : Γ') :
    HVertexOperator (Γ ×ₗ Γ') R V W →ₗ[R] HVertexOperator Γ R V W where
  toFun A := ResRight A g'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Products

section Binomial

variable {Γ : Type*} [OrderedCancelAddCommMonoid Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem lex_basis_lt : (toLex (0,1) : ℤ ×ₗ ℤ) < (toLex (1,0) : ℤ ×ₗ ℤ) := by decide
--#find_home! lex_basis_lt --[Mathlib.Data.Prod.Lex]

theorem toLex_vAdd_of_sub (k l m n : ℤ) :
    toLex ((m : ℤ) , (n : ℤ)) +ᵥ toLex (k - m, l - n) = toLex (k, l) := by
  rw [vadd_eq_add, ← toLex_add, Prod.mk_add_mk, Int.add_comm, Int.sub_add_cancel, Int.add_comm,
    Int.sub_add_cancel]
--#find_home! toLex_vAdd_of_sub --[Mathlib.RingTheory.HahnSeries.Multiplication]

/-- `-Y + X` as a unit of `R((X))((Y))` -/
def subLeft (R : Type*) [CommRing R] : (HahnSeries (ℤ ×ₗ ℤ) R)ˣ :=
  HahnSeries.UnitBinomial (AddGroup.isAddUnit (toLex (0,1))) lex_basis_lt (isUnit_neg_one (α := R))
    (1 : R)

theorem subLeft_eq : (subLeft R).val = HahnSeries.single (toLex (1,0)) 1 +
    HahnSeries.single (toLex (0,1)) (-1 : R) := by
  rw [subLeft, HahnSeries.unitBinomial_eq_single_add_single, add_comm]

@[simp]
theorem subLeft_smul_eq {A : HVertexOperator (ℤ ×ₗ ℤ) R V W} :
    subLeft R • A = (subLeft R).val • A :=
  rfl

@[simp]
theorem subLeft_leadingCoeff [Nontrivial R] : (subLeft R).val.leadingCoeff = (-1 : R) := by
  rw [subLeft_eq, add_comm, HahnSeries.leadingCoeff_single_add_single lex_basis_lt (by simp)]

theorem subLeft_order [Nontrivial R] : (subLeft R).val.order = toLex (0,1) := by
  rw [subLeft_eq, add_comm, HahnSeries.order_single_add_single lex_basis_lt (by simp)]

@[simp]
theorem subLeft_smul_coeff (A : HVertexOperator (ℤ ×ₗ ℤ) R V W) (k l : ℤ) :
    ((subLeft R).val • A).coeff (toLex (k, l)) =
      A.coeff (toLex (k - 1, l)) - A.coeff (toLex (k, l - 1)) := by
  rw [subLeft_eq, add_smul, add_coeff_apply]
  ext v
  simp only [LinearMap.add_apply, coeff_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq]
  nth_rw 1 [← toLex_vAdd_of_sub k l 1 0]
  rw [sub_zero, HahnModule.single_smul_coeff_add, one_smul, ← toLex_vAdd_of_sub k l 0 1,
    sub_zero, HahnModule.single_smul_coeff_add, neg_one_smul, ← sub_eq_add_neg]

--describe coefficients of powers
--describe coefficients of `subLeft R • A` for `A : HetVO`.

/-- `X - Y` as a unit of `R((Y))((X))`.  This is `-1` times subLeft, so it may be superfluous. -/
def subRight (R : Type*) [CommRing R] : (HahnSeries (ℤ ×ₗ ℤ) R)ˣ :=
    HahnSeries.UnitBinomial (AddGroup.isAddUnit (toLex (0,1))) lex_basis_lt (isUnit_one (M := R))
    (-1 : R)

theorem subRight_eq : (subRight R).val = HahnSeries.single (toLex (1,0)) (-1 : R) +
    HahnSeries.single (toLex (0,1)) (1 : R) := by
  rw [subRight, HahnSeries.unitBinomial_eq_single_add_single, add_comm]

theorem subRight_leadingCoeff [Nontrivial R] : (subRight R).val.leadingCoeff = (1 : R) := by
  rw [subRight_eq, add_comm, HahnSeries.leadingCoeff_single_add_single lex_basis_lt one_ne_zero]

theorem subRight_order [Nontrivial R] : (subRight R).val.order = toLex (0,1) := by
  rw [subRight_eq, add_comm, HahnSeries.order_single_add_single lex_basis_lt one_ne_zero]

theorem subRight_smul_eq (A : HVertexOperator (ℤ ×ₗ ℤ) R V W) :
    (subRight R) • A = (subRight R).val • A :=
  rfl

theorem subRight_smul_coeff (A : HVertexOperator (ℤ ×ₗ ℤ) R V W) (k l : ℤ) :
    ((subRight R) • A).coeff (toLex (k, l)) =
      A.coeff (toLex (k, l - 1)) - A.coeff (toLex (k - 1, l)) := by
  rw [subRight_smul_eq, subRight_eq, add_smul, add_coeff_apply]
  ext v
  simp only [LinearMap.add_apply, coeff_apply, LinearMap.sub_apply, smul_eq]
  nth_rw 1 [← toLex_vAdd_of_sub k l 1 0]
  rw [sub_zero, HahnModule.single_smul_coeff_add, neg_one_smul, ← toLex_vAdd_of_sub k l 0 1,
    sub_zero, HahnModule.single_smul_coeff_add, one_smul, neg_add_eq_sub]

--describe coefficients of powers

theorem subLeft_smul_eq_subRight_smul (A B : HVertexOperator (ℤ ×ₗ ℤ) R V W)
    (h : ∀ (k l : ℤ), A.coeff (toLex (k, l)) = B.coeff (toLex (l, k))) (k l : ℤ) :
    ((subLeft R).val • A).coeff (toLex (k, l)) = ((subRight R) • B).coeff (toLex (l, k)) := by
  rw [subLeft_smul_coeff, subRight_smul_coeff, h k (l-1), h (k-1) l]

end Binomial

section StateFieldMap

/-- A heterogeneous state-field map is a linear map from a vector space `U` to the space of
heterogeneous fields (or vertex operators) from `V` to `W`.  Equivalently, it is a bilinear map
`U →ₗ[R] V →ₗ[R] HahnModule Γ R W`.  When `Γ = ℤ` and `U = V = W`, then the multiplication map in a
vertex algebra has this form, but in other cases, we use this for module structures and intertwining
operators. -/
abbrev HStateFieldMap (Γ R U V W : Type*) [PartialOrder Γ] [CommRing R] [AddCommGroup U]
    [Module R U] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] :=
  U →ₗ[R] HVertexOperator Γ R V W

-- Can I just use `curry` to say this is a HVertexOperator Γ R (U ⊗ V) W?
-- Then composition is easier.

namespace VertexAlg

variable {U} (R) {X Y : Type*} [CommRing R] [AddCommGroup U] [Module R U] [AddCommGroup V]
  [Module R V] [AddCommGroup W] [Module R W] [AddCommGroup X] [Module R X] [AddCommGroup Y]
  [Module R Y]

/-- The coefficient function of a heterogeneous state-field map. -/
@[simps]
def coeff (A : HStateFieldMap Γ R U V W) (g : Γ) : U →ₗ[R] V →ₗ[R] W where
  toFun u := (A u).coeff g
  map_add' a b := by simp
  map_smul' r a := by simp

open TensorProduct

/-- The standard equivalence between heterogeneous state field maps and heterogeneous vertex
operators on the tensor product. -/
def uncurry : HStateFieldMap Γ R U V W ≃ₗ[R] HVertexOperator Γ R (U ⊗[R] V) W :=
  lift.equiv R U V (HahnModule Γ R W)

@[simp]
theorem uncurry_apply (A : HStateFieldMap Γ R U V W) (u : U) (v : V) :
    uncurry R A (u ⊗ₜ v) = A u v :=
  rfl

@[simp]
theorem uncurry_symm_apply (A : HVertexOperator Γ R (U ⊗[R] V) W) (u : U) (v : V) :
    (uncurry R).symm A u v = A (u ⊗ₜ v) :=
  rfl

/-! Iterate starting with `Y_{UV}^W : U ⊗ V → W((z))` and `Y_{WX}^Y : W ⊗ X → Y((w))`, make
`Y_{UVX}^Y (t_1, t_2) : U ⊗ V ⊗ X → W((z)) ⊗ X → Y((w))((z))`.
I need an operator on tensor products giving Lex Hahn series from Hahn Series inputs.
So, define `W((z)) ⊗ X → (W ⊗ X)((z))` by coefficient-wise maps, then extend the `HVertexOperator`
`Y_{WX}^Y` to `(W ⊗ X)((z)) → Y((w))((z))` coefficient-wise.
-/
-- Right composition: `Y_{XW}^Y (x, t_0) Y_{UV}^W (u, t_1) v`

-- Define things like order of a pair, creativity?

end VertexAlg

end StateFieldMap

end HVertexOperator
