/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.CStarAlgebra.Module

/-!
# Vectors with entries in a C⋆-algebra

This file creates a type copy of `n → A` meant for vectors with entries in a C⋆-algebra `A`. It is
endowed with a Hilbert C⋆-module structure, which in particular comes with an `A`-valued
"inner product" `⟪w, v⟫ = ∑ i, star (w i) * v i` and a norm `‖v‖ = √‖⟪v, v⟫‖`.

## Main declarations

+ `CStarVec n A`: the type copy
+ `instCStarModule`: the Hilbert C⋆-module instance

## Implementation notes

The norm on this type induces the product uniformity and bornology, but these are not defeq to
`Pi.uniformSpace` and `Pi.instBornology`. Hence, we prove the equality to the Pi instances and
replace the uniformity and bornology by the Pi ones when registering the
`NormedAddCommGroup (CStarVec n A)` instance. See the docstring of the `TopologyAux` section below
for more details.

-/

open scoped ComplexOrder RightActions Topology Uniformity Bornology

/-- A vector with entries in a C⋆-algebra and a Hilbert C⋆-module structure. -/
def CStarVec (n : Type*) (A : Type*) := n → A

namespace CStarVec

section basic

variable {n R A : Type*} (v w : CStarVec n A)

instance [Inhabited A] : Inhabited (CStarVec n A) :=
  ⟨fun _ => default⟩

/-- The equivalence between `n → A` and `CStarVec n A`. -/
def ofFun : (n → A) ≃ CStarVec n A := Equiv.refl _

@[simp] lemma ofFun_symm_apply {i : n} : ofFun.symm v i = v i := rfl

@[simp] lemma ofFun_apply {i : n} : ofFun v i = v i := rfl

/-The following should not be a `FunLike` instance because then the coercion `⇑` would get
unfolded to `FunLike.coe` instead of `ofFun.symm`. -/
instance instCoeFun : CoeFun (CStarVec n A) (fun _ => (_ : n) → A) where
  coe := ofFun.symm

@[ext] protected theorem ext (h : ∀ i, v i = w i) : v = w := funext h

instance instZero [Zero A] : Zero (CStarVec n A) :=
  Pi.instZero

instance instNeg [Neg A] : Neg (CStarVec n A) :=
  Pi.instNeg

instance instAdd [Add A] : Add (CStarVec n A) :=
  Pi.instAdd

instance instSub [Sub A] : Sub (CStarVec n A) :=
  Pi.instSub

instance instAddSemigroup [AddSemigroup A] : AddSemigroup (CStarVec n A) :=
  { instAdd, Pi.addSemigroup with }

instance instAddMonoid [AddMonoid A] : AddMonoid (CStarVec n A) :=
  { instAdd, instAddSemigroup, instZero, Pi.addMonoid with }

instance instSubNegMonoid [SubNegMonoid A] : SubNegMonoid (CStarVec n A) :=
  { instAddMonoid, instNeg, instSub, Pi.subNegMonoid with }

instance instAddGroup [AddGroup A] : AddGroup (CStarVec n A) :=
  { instSubNegMonoid, Pi.addGroup with }

instance instAddCommMonoid [AddCommMonoid A] : AddCommMonoid (CStarVec n A) :=
  { instAddMonoid, Pi.addCommMonoid with }

instance instAddCommGroup [AddCommGroup A] : AddCommGroup (CStarVec n A) :=
  { instAddGroup, Pi.addCommGroup with }

variable (R) in
instance instSMul [SMul R A] : SMul R (CStarVec n A) :=
  Pi.instSMul

instance instModule [Semiring R] [AddCommMonoid A] [Module R A] : Module R (CStarVec n A) :=
  { instSMul R, Pi.module n (fun _ => A) R with }

@[simp] theorem zero_apply [Zero A] {i : n} : (0 : CStarVec n A) i = 0 := rfl

@[simp] theorem add_apply [Add A] {i : n} : (v + w) i = v i + w i := rfl

@[simp] theorem sub_apply [Sub A] {i : n} : (v - w) i = v i - w i := rfl

@[simp] theorem smul_apply (c : R) [SMul R A] {i : n} : (c • v) i = c • v i := rfl

@[simp] theorem neg_apply [Neg A] {i : n} : (-v) i = -v i := rfl

theorem finset_sum_fn {ι : Type*} {s : Finset ι} [AddCommMonoid A] {f : ι → CStarVec n A} :
    ∑ i ∈ s, ofFun (f i) = (fun j => ∑ i ∈ s, f i j) := by
  rw [Finset.sum_fn]
  rfl

end basic

section inner

variable {n R A : Type*} [Fintype n] [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℂ A]
  [PartialOrder A] [StarOrderedRing A] [CStarRing A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [StarModule ℂ A]

instance instInner : Inner A (CStarVec n A) where
  inner v w := ∑ i : n, star (v i) * w i

noncomputable instance instNorm : Norm (CStarVec n A) where
  norm v := √‖⟪v, v⟫_A‖

lemma inner_eq_sum {v w : CStarVec n A} : ⟪v, w⟫_A = ∑ i : n, star (v i) * w i := rfl

lemma norm_eq_sqrt_sum {v : CStarVec n A} : ‖v‖ = √‖∑ i : n, star (v i) * v i‖ := rfl

lemma inner_single_left [DecidableEq n] {v : CStarVec n A} {i : n} {a : A} :
    ⟪ofFun (Pi.single i a), v⟫_A = star a * v i := by
  simp [inner_eq_sum, ofFun_apply, Pi.single_apply]
  have hmain :
      (fun x => star (if x = i then a else 0) * v x)
        = fun x => if x = i then star a * v x else 0 := by
    ext
    split_ifs with h <;> simp [h, mul_assoc]
  simp [hmain, Finset.sum_ite]

@[simp] lemma norm_single {i : n} {a : A} [DecidableEq n] : ‖ofFun (Pi.single i a)‖ = ‖a‖ := by
  simp [norm_eq_sqrt_sum, Pi.single_apply, CStarRing.norm_star_mul_self]

instance instCStarModule : CStarModule A (CStarVec n A) where
  inner_add_right {v} {w₁} {w₂} := by
    simp only [inner_eq_sum, add_apply, mul_add, Finset.sum_add_distrib]
  inner_self_nonneg {x} := by
    simp only [inner]
    exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg (x i)
  inner_self {x} := by
    refine ⟨fun h => ?_, ?_⟩
    · simp only [inner] at h
      have : ∀ i ∈ Finset.univ, 0 ≤ star (x i) * x i := fun i _ => star_mul_self_nonneg (x i)
      rw [Finset.sum_eq_zero_iff_of_nonneg this] at h
      ext i
      simp only [zero_apply]
      exact (CStarRing.star_mul_self_eq_zero_iff (x i)).mp <| h i (Finset.mem_univ i)
    · rintro rfl; simp only [inner, CStarVec.zero_apply, star_zero, mul_zero, Finset.sum_const_zero]
  inner_op_smul_right {a} {x} {y} := by
    simp only [inner, smul_apply, smul_eq_mul, mul_assoc]
    apply Eq.symm
    simp [Finset.sum_mul, mul_assoc]
  inner_smul_right_complex {z} {x} {y} := by
    simp only [inner_eq_sum, smul_apply, smul_mul_assoc]
    apply Eq.symm
    simp only [Finset.smul_sum, mul_smul_comm]
  star_inner x y := by simp only [inner, star_sum, star_mul, star_star]
  norm_eq_sqrt_norm_inner_self v := rfl

lemma norm_apply_le_norm [DecidableEq n] [CompleteSpace A] {v : CStarVec n A} {i : n} :
    ‖v i‖ ≤ ‖v‖ := by
  by_cases htriv : 0 < ‖v i‖
  · have hmain := calc ‖v i‖ * ‖v i‖ = ‖star (v i) * v i‖  := CStarRing.norm_star_mul_self.symm
      _ = ‖⟪ofFun (Pi.single i (v i)), v⟫_A‖ := by rw [inner_single_left]
      _ ≤ ‖ofFun (Pi.single i (v i))‖ * ‖v‖ :=
            CStarModule.norm_inner_le (E := CStarVec n A)
      _ = ‖v i‖ * ‖v‖ := by rw [norm_single]
    rwa [mul_le_mul_left htriv] at hmain
  · push_neg at htriv
    simp only [norm_le_zero_iff] at htriv
    simp only [htriv, _root_.norm_zero]
    exact CStarModule.norm_nonneg

end inner

section TopologyAux
/-
## Replacing the uniformity and bornology

Note that while the norm that we have defined on `CStarVec n A` induces the product uniformity,
it is not defeq to `Pi.uniformSpace`. In this section, we show that the norm indeed does induce
the product topology and use this fact to properly set up the `NormedAddCommGroup (CStarVec n A)`
instance such that the uniformity is still `Pi.uniformSpace` and the bornology is
`Pi.instBornology`.

To do this, we first temporarily register the "bad" `NormedAddCommGroup (CStarVec n A)` instance
and show that the map from `ofFun.symm : CStarVec n A → (n → A)` is both Lipschitz and
Antilipschitz.  We then finally register the `NormedAddCommGroup (CStarVec n A)` instance via
`NormedAddCommGroup.ofCoreReplaceAll`.
-/

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [PartialOrder A]
  [CompleteSpace A] [StarOrderedRing A] [NormedSpace ℂ A] [StarModule ℂ A] [IsScalarTower ℂ A A]
  [SMulCommClass ℂ A A]

variable {n : Type*} [Fintype n]

/-- A temporary "bad" instance of `NormedAddCommGroup` that induces a uniformity that is not
defeq with the product uniformity.

This is not intended for use outside of this file. -/
private noncomputable abbrev normedAddCommGroupAux : NormedAddCommGroup (CStarVec n A) :=
  NormedAddCommGroup.ofCore CStarModule.normedSpaceCore

attribute [local instance] normedAddCommGroupAux

/-- A temporary "bad" instance of `NormedSpace`.

This is not intended for use outside of this file.  -/
private noncomputable abbrev normedSpaceAux : NormedSpace ℂ (CStarVec n A) :=
  .ofCore CStarModule.normedSpaceCore

attribute [local instance] normedSpaceAux

open Finset Classical in
private lemma lipschitzWith_ofFun_symm_aux :
    LipschitzWith 1 (ofFun.symm : CStarVec n A → n → A) := by
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  simp only [dist_eq_norm, NNReal.coe_one, one_mul]
  let d := f - g
  change ‖CStarVec.ofFun.symm d‖ ≤ ‖d‖
  by_cases hn : Nonempty n
  · obtain ⟨i, ⟨hi_univ, hi⟩⟩ := exists_mem_eq_sup univ univ_nonempty fun i => ‖d i‖₊
    simp only [dist_eq_norm, Pi.norm_def, Pi.sub_apply, ofFun_symm_apply, hi, coe_nnnorm,
      NNReal.coe_one, CStarModule.norm_eq_sqrt_norm_inner_self, inner, sub_apply, star_sub,
      one_mul]
    rw [Finset.sum_eq_add_sum_diff_singleton hi_univ]
    have h₁ : ‖d i‖ = Real.sqrt ‖star (d i) * d i‖ := by
      simp only [← star_sub, CStarRing.norm_star_mul_self, norm_nonneg, Real.sqrt_mul_self]
    rw [h₁]
    gcongr
    refine CStarRing.norm_le_norm_of_nonneg_of_le (star_mul_self_nonneg (d i)) ?_
    calc _ = star (d i) * d i + ∑ _ ∈ univ \ {i}, 0 := by simp
      _ ≤ _ := by gcongr with j; exact star_mul_self_nonneg (d j)
  · simp only [not_nonempty_iff] at hn
    simp [dist_eq_norm, Pi.norm_def, Pi.sub_apply, ofFun_symm_apply, coe_nnnorm, NNReal.coe_one,
      CStarModule.norm_eq_sqrt_norm_inner_self, inner, sub_apply, star_sub, one_mul]

open Finset Classical in
private lemma antilipschitzWith_ofFun_symm_aux :
    AntilipschitzWith (NNReal.sqrt (Fintype.card n)) (ofFun.symm : CStarVec n A → n → A) := by
  refine AntilipschitzWith.of_le_mul_dist fun f g => ?_
  let d := f - g
  let D := Fintype.card n
  simp only [dist_eq_norm]
  change ‖d‖ ≤ (NNReal.sqrt D) * ‖ofFun.symm d‖
  by_cases hn : Nonempty n
  · obtain ⟨i, ⟨_, hi⟩⟩ := exists_mem_eq_sup univ univ_nonempty fun i => ‖d i‖₊
    simp only [dist_eq_norm, Pi.norm_def, Pi.sub_apply, ofFun_symm_apply, hi, coe_nnnorm,
      NNReal.coe_one, CStarModule.norm_eq_sqrt_norm_inner_self, inner, sub_apply, star_sub,
      one_mul]
    have h₀ : ∀ j, ‖star (d j) * d j‖ ≤ ‖star (d i) * d i‖ := fun j => by
      simp only [CStarRing.norm_star_mul_self]
      have : ‖d j‖ ≤ ‖d i‖ := by
        convert_to (‖d j‖₊ : ℝ) ≤ (‖d i‖₊ : ℝ)
        rw [← hi]
        gcongr
        exact Finset.le_sup (f := fun j => ‖d j‖₊) (mem_univ j)
      gcongr
    have h₁ : Real.sqrt ‖∑ j, star (d j) * d j‖ ≤ Real.sqrt ‖∑ (_ : n), star (d i) * d i‖ := by
      gcongr
      calc _ ≤ ∑ j : n, ‖star (d j) * d j‖ := norm_sum_le univ fun i => star (d i) * d i
        _ ≤ ∑ _ : n, ‖star (d i) * d i‖ := by gcongr with j; exact h₀ j
        _ = ‖∑ _ : n, star (d i) * d i‖ := by
                simp only [sum_const]
                exact Eq.symm (RCLike.norm_nsmul ℂ univ.card (star (d i) * d i))
    refine h₁.trans ?_
    simp only [sum_const, card_univ, Real.coe_sqrt]
    have h₂ : Real.sqrt ‖D • (star (d i) * d i)‖ ≤ Real.sqrt (D * ‖star (d i) * d i‖) := by
      gcongr
      exact norm_nsmul_le _ _
    refine h₂.trans ?_
    simp only [Nat.cast_nonneg, Real.sqrt_mul, NNReal.coe_natCast, CStarRing.norm_self_mul_star]
    gcongr
    simp only [CStarRing.norm_star_mul_self, norm_nonneg, Real.sqrt_mul_self, le_refl]
  · simp only [not_nonempty_iff] at hn
    simp [dist_eq_norm, Pi.norm_def, Pi.sub_apply, ofFun_symm_apply, coe_nnnorm, NNReal.coe_one,
      CStarModule.norm_eq_sqrt_norm_inner_self, inner, sub_apply, star_sub, one_mul]

private lemma uniformInducing_ofFun_symm_aux :
    UniformInducing (CStarVec.ofFun.symm : CStarVec n A → n → A) :=
  AntilipschitzWith.uniformInducing antilipschitzWith_ofFun_symm_aux
    lipschitzWith_ofFun_symm_aux.uniformContinuous

private lemma uniformity_eq_aux : 𝓤 (CStarVec n A) = 𝓤[Pi.uniformSpace _] := by
  have : (fun x : CStarVec n A × CStarVec n A => ⟨ofFun.symm x.1, ofFun.symm x.2⟩) = id := by
    ext i <;> rfl
  rw [← uniformInducing_ofFun_symm_aux.comap_uniformity, this, Filter.comap_id]

open Bornology in
private lemma cobounded_eq_aux : cobounded (CStarVec n A) = @cobounded _ Pi.instBornology := by
  have : cobounded (CStarVec n A) = Filter.comap ofFun.symm (cobounded _) := by
    refine le_antisymm ?_ ?_
    · exact antilipschitzWith_ofFun_symm_aux.tendsto_cobounded.le_comap
    · exact lipschitzWith_ofFun_symm_aux.comap_cobounded_le
  exact this.trans Filter.comap_id

end TopologyAux

section NormedSpace

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [PartialOrder A]
  [CompleteSpace A] [StarOrderedRing A] [NormedSpace ℂ A] [StarModule ℂ A] [IsScalarTower ℂ A A]
  [SMulCommClass ℂ A A]

variable {n : Type*} [Fintype n]

instance : TopologicalSpace (CStarVec n A) := Pi.topologicalSpace

instance : UniformSpace (CStarVec n A) := Pi.uniformSpace _

instance : Bornology (CStarVec n A) := Pi.instBornology

instance : CompleteSpace (CStarVec n A) := Pi.complete _

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (CStarVec n A) :=
  NormedAddCommGroup.ofCoreReplaceAll CStarModule.normedSpaceCore
    uniformity_eq_aux.symm fun _ => Filter.ext_iff.1 cobounded_eq_aux.symm _

instance instNormedSpace : NormedSpace ℂ (CStarVec n A) :=
  NormedSpace.ofCore CStarModule.normedSpaceCore

end NormedSpace

end CStarVec
