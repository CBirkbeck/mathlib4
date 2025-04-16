/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.LinearAlgebra.RootSystem.Basic
import Mathlib.LinearAlgebra.RootSystem.Irreducible
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import Mathlib.Algebra.Algebra.Rat

/-!
# The root system associated with a Lie algebra

We show that the roots of a finite dimensional splitting semisimple Lie algebra over a field of
characteristic 0 form a root system. We achieve this by studying root chains.

## Main results

- `LieAlgebra.IsKilling.apply_coroot_eq_cast`:
  If `β - qα ... β ... β + rα` is the `α`-chain through `β`, then
  `β (coroot α) = q - r`. In particular, it is an integer.

- `LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff`:
  The `α`-chain through `β` (`β - qα ... β ... β + rα`) are the only roots of the form `β + kα`.

- `LieAlgebra.IsKilling.eq_neg_or_eq_of_eq_smul`:
  `±α` are the only `K`-multiples of a root `α` that are also (non-zero) roots.

- `LieAlgebra.IsKilling.rootSystem`: The root system of a finite-dimensional Lie algebra with
  non-degenerate Killing form over a field of characteristic zero,
  relative to a splitting Cartan subalgebra.

-/

noncomputable section

namespace LieAlgebra.IsKilling

open LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

variable (α β : Weight K H L)

private lemma chainLength_aux (hα : α.IsNonZero) {x} (hx : x ∈ rootSpace H (chainTop α β)) :
    ∃ n : ℕ, n • x = ⁅coroot α, x⁆ := by
  by_cases hx' : x = 0
  · exact ⟨0, by simp [hx']⟩
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have : isSl2.HasPrimitiveVectorWith x (chainTop α β (coroot α)) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨hx', by rw [← lie_eq_smul_of_mem_rootSpace hx]; rfl,
      by rwa [genWeightSpace_add_chainTop α β hα] at this⟩
  obtain ⟨μ, hμ⟩ := this.exists_nat
  exact ⟨μ, by rw [← Nat.cast_smul_eq_nsmul K, ← hμ, lie_eq_smul_of_mem_rootSpace hx]⟩

/-- The length of the `α`-chain through `β`. See `chainBotCoeff_add_chainTopCoeff`. -/
def chainLength (α β : Weight K H L) : ℕ :=
  letI := Classical.propDecidable
  if hα : α.IsZero then 0 else
    (chainLength_aux α β hα (chainTop α β).exists_ne_zero.choose_spec.1).choose

lemma chainLength_of_isZero (hα : α.IsZero) : chainLength α β = 0 := dif_pos hα

lemma chainLength_nsmul {x} (hx : x ∈ rootSpace H (chainTop α β)) :
    chainLength α β • x = ⁅coroot α, x⁆ := by
  by_cases hα : α.IsZero
  · rw [coroot_eq_zero_iff.mpr hα, chainLength_of_isZero _ _ hα, zero_smul, zero_lie]
  let x' := (chainTop α β).exists_ne_zero.choose
  have h : x' ∈ rootSpace H (chainTop α β) ∧ x' ≠ 0 :=
    (chainTop α β).exists_ne_zero.choose_spec
  obtain ⟨k, rfl⟩ : ∃ k : K, k • x' = x := by
    simpa using (finrank_eq_one_iff_of_nonzero' ⟨x', h.1⟩ (by simpa using h.2)).mp
      (finrank_rootSpace_eq_one _ (chainTop_isNonZero α β hα)) ⟨_, hx⟩
  rw [lie_smul, smul_comm, chainLength, dif_neg hα, (chainLength_aux α β hα h.1).choose_spec]

lemma chainLength_smul {x} (hx : x ∈ rootSpace H (chainTop α β)) :
    (chainLength α β : K) • x = ⁅coroot α, x⁆ := by
  rw [Nat.cast_smul_eq_nsmul, chainLength_nsmul _ _ hx]

lemma apply_coroot_eq_cast' :
    β (coroot α) = ↑(chainLength α β - 2 * chainTopCoeff α β : ℤ) := by
  by_cases hα : α.IsZero
  · rw [coroot_eq_zero_iff.mpr hα, chainLength, dif_pos hα, hα.eq, chainTopCoeff_zero, map_zero,
      CharP.cast_eq_zero, mul_zero, sub_self, Int.cast_zero]
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α β).exists_ne_zero
  have := chainLength_smul _ _ hx
  rw [lie_eq_smul_of_mem_rootSpace hx, ← sub_eq_zero, ← sub_smul,
    smul_eq_zero_iff_left x_ne0, sub_eq_zero, coe_chainTop', nsmul_eq_mul, Pi.natCast_def,
    Pi.add_apply, Pi.mul_apply, root_apply_coroot hα] at this
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat, eq_sub_iff_add_eq',
    this, mul_comm (2 : K)]

lemma rootSpace_neg_nsmul_add_chainTop_of_le {n : ℕ} (hn : n ≤ chainLength α β) :
    rootSpace H (- (n • α) + chainTop α β) ≠ ⊥ := by
  by_cases hα : α.IsZero
  · simpa only [hα.eq, smul_zero, neg_zero, chainTop_zero, zero_add, ne_eq] using β.2
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α β).exists_ne_zero
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have prim : isSl2.HasPrimitiveVectorWith x (chainLength α β : K) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨x_ne0, (chainLength_smul _ _ hx).symm, by rwa [genWeightSpace_add_chainTop _ _ hα] at this⟩
  simp only [← smul_neg, ne_eq, LieSubmodule.eq_bot_iff, not_forall]
  exact ⟨_, toEnd_pow_apply_mem hf hx n, prim.pow_toEnd_f_ne_zero_of_eq_nat rfl hn⟩

lemma rootSpace_neg_nsmul_add_chainTop_of_lt (hα : α.IsNonZero) {n : ℕ} (hn : chainLength α β < n) :
    rootSpace H (- (n • α) + chainTop α β) = ⊥ := by
  by_contra e
  let W : Weight K H L := ⟨_, e⟩
  have hW : (W : H → K) = - (n • α) + chainTop α β := rfl
  have H₁ : 1 + n + chainTopCoeff (-α) W ≤ chainLength (-α) W := by
    have := apply_coroot_eq_cast' (-α) W
    simp only [coroot_neg, map_neg, hW, nsmul_eq_mul, Pi.natCast_def, coe_chainTop, zsmul_eq_mul,
      Int.cast_natCast, Pi.add_apply, Pi.neg_apply, Pi.mul_apply, root_apply_coroot hα, mul_two,
      neg_add_rev, apply_coroot_eq_cast' α β, Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
      mul_comm (2 : K), add_sub_cancel, neg_neg, add_sub, Nat.cast_inj,
      eq_sub_iff_add_eq, ← Nat.cast_add, ← sub_eq_neg_add, sub_eq_iff_eq_add] at this
    omega
  have H₂ : ((1 + n + chainTopCoeff (-α) W) • α + chainTop (-α) W : H → K) =
      (chainTopCoeff α β + 1) • α + β := by
    simp only [Weight.coe_neg, ← Nat.cast_smul_eq_nsmul ℤ, Nat.cast_add, Nat.cast_one, coe_chainTop,
      smul_neg, ← neg_smul, hW, ← add_assoc, ← add_smul, ← sub_eq_add_neg]
    congr 2
    ring
  have := rootSpace_neg_nsmul_add_chainTop_of_le (-α) W H₁
  rw [Weight.coe_neg, ← smul_neg, neg_neg, ← Weight.coe_neg, H₂] at this
  exact this (genWeightSpace_chainTopCoeff_add_one_nsmul_add α β hα)

lemma chainTopCoeff_le_chainLength : chainTopCoeff α β ≤ chainLength α β := by
  by_cases hα : α.IsZero
  · simp only [hα.eq, chainTopCoeff_zero, zero_le]
  rw [← not_lt, ← Nat.succ_le]
  intro e
  apply genWeightSpace_nsmul_add_ne_bot_of_le α β
    (Nat.sub_le (chainTopCoeff α β) (chainLength α β).succ)
  rw [← Nat.cast_smul_eq_nsmul ℤ, Nat.cast_sub e, sub_smul, sub_eq_neg_add,
    add_assoc, ← coe_chainTop, Nat.cast_smul_eq_nsmul]
  exact rootSpace_neg_nsmul_add_chainTop_of_lt α β hα (Nat.lt_succ_self _)

lemma chainBotCoeff_add_chainTopCoeff :
    chainBotCoeff α β + chainTopCoeff α β = chainLength α β := by
  by_cases hα : α.IsZero
  · rw [hα.eq, chainTopCoeff_zero, chainBotCoeff_zero, zero_add, chainLength_of_isZero α β hα]
  apply le_antisymm
  · rw [← Nat.le_sub_iff_add_le (chainTopCoeff_le_chainLength α β),
      ← not_lt, ← Nat.succ_le, chainBotCoeff, ← Weight.coe_neg]
    intro e
    apply genWeightSpace_nsmul_add_ne_bot_of_le _ _ e
    rw [← Nat.cast_smul_eq_nsmul ℤ, Nat.cast_succ, Nat.cast_sub (chainTopCoeff_le_chainLength α β),
      LieModule.Weight.coe_neg, smul_neg, ← neg_smul, neg_add_rev, neg_sub, sub_eq_neg_add,
      ← add_assoc, ← neg_add_rev, add_smul, add_assoc, ← coe_chainTop, neg_smul,
      ← @Nat.cast_one ℤ, ← Nat.cast_add, Nat.cast_smul_eq_nsmul]
    exact rootSpace_neg_nsmul_add_chainTop_of_lt α β hα (Nat.lt_succ_self _)
  · rw [← not_lt]
    intro e
    apply rootSpace_neg_nsmul_add_chainTop_of_le α β e
    rw [← Nat.succ_add, ← Nat.cast_smul_eq_nsmul ℤ, ← neg_smul, coe_chainTop, ← add_assoc,
      ← add_smul, Nat.cast_add, neg_add, add_assoc, neg_add_cancel, add_zero, neg_smul, ← smul_neg,
      Nat.cast_smul_eq_nsmul]
    exact genWeightSpace_chainTopCoeff_add_one_nsmul_add (-α) β (Weight.IsNonZero.neg hα)

lemma chainTopCoeff_add_chainBotCoeff :
    chainTopCoeff α β + chainBotCoeff α β = chainLength α β := by
  rw [add_comm, chainBotCoeff_add_chainTopCoeff]

lemma chainBotCoeff_le_chainLength : chainBotCoeff α β ≤ chainLength α β :=
  (Nat.le_add_left _ _).trans_eq (chainTopCoeff_add_chainBotCoeff α β)

@[simp]
lemma chainLength_neg :
    chainLength (-α) β = chainLength α β := by
  rw [← chainBotCoeff_add_chainTopCoeff, ← chainBotCoeff_add_chainTopCoeff, add_comm,
    Weight.coe_neg, chainTopCoeff_neg, chainBotCoeff_neg]

@[simp]
lemma chainLength_zero [Nontrivial L] : chainLength 0 β = 0 := by
  simp [← chainBotCoeff_add_chainTopCoeff]

/-- If `β - qα ... β ... β + rα` is the `α`-chain through `β`, then
  `β (coroot α) = q - r`. In particular, it is an integer. -/
lemma apply_coroot_eq_cast :
    β (coroot α) = (chainBotCoeff α β - chainTopCoeff α β : ℤ) := by
  rw [apply_coroot_eq_cast', ← chainTopCoeff_add_chainBotCoeff]; congr 1; omega

lemma le_chainBotCoeff_of_rootSpace_ne_top
    (hα : α.IsNonZero) (n : ℤ) (hn : rootSpace H (-n • α + β) ≠ ⊥) :
    n ≤ chainBotCoeff α β := by
  contrapose! hn
  lift n to ℕ using (Nat.cast_nonneg _).trans hn.le
  rw [Nat.cast_lt, ← @Nat.add_lt_add_iff_right (chainTopCoeff α β),
    chainBotCoeff_add_chainTopCoeff] at hn
  have := rootSpace_neg_nsmul_add_chainTop_of_lt α β hα hn
  rwa [← Nat.cast_smul_eq_nsmul ℤ, ← neg_smul, coe_chainTop, ← add_assoc,
    ← add_smul, Nat.cast_add, neg_add, add_assoc, neg_add_cancel, add_zero] at this

/-- Members of the `α`-chain through `β` are the only roots of the form `β - kα`. -/
lemma rootSpace_zsmul_add_ne_bot_iff (hα : α.IsNonZero) (n : ℤ) :
    rootSpace H (n • α + β) ≠ ⊥ ↔ n ≤ chainTopCoeff α β ∧ -n ≤ chainBotCoeff α β := by
  constructor
  · refine (fun hn ↦ ⟨?_, le_chainBotCoeff_of_rootSpace_ne_top α β hα _ (by rwa [neg_neg])⟩)
    rw [← chainBotCoeff_neg, ← Weight.coe_neg]
    apply le_chainBotCoeff_of_rootSpace_ne_top _ _ hα.neg
    rwa [neg_smul, Weight.coe_neg, smul_neg, neg_neg]
  · rintro ⟨h₁, h₂⟩
    set k := chainTopCoeff α β - n with hk; clear_value k
    lift k to ℕ using (by rw [hk, le_sub_iff_add_le, zero_add]; exact h₁)
    rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq'] at hk
    subst hk
    simp only [neg_sub, tsub_le_iff_right, ← Nat.cast_add, Nat.cast_le,
      chainBotCoeff_add_chainTopCoeff] at h₂
    have := rootSpace_neg_nsmul_add_chainTop_of_le α β h₂
    rwa [coe_chainTop, ← Nat.cast_smul_eq_nsmul ℤ, ← neg_smul,
      ← add_assoc, ← add_smul, ← sub_eq_neg_add] at this

lemma rootSpace_zsmul_add_ne_bot_iff_mem (hα : α.IsNonZero) (n : ℤ) :
    rootSpace H (n • α + β) ≠ ⊥ ↔ n ∈ Finset.Icc (-chainBotCoeff α β : ℤ) (chainTopCoeff α β) := by
  rw [rootSpace_zsmul_add_ne_bot_iff α β hα n, Finset.mem_Icc, and_comm, neg_le]

lemma chainTopCoeff_of_eq_zsmul_add
    (hα : α.IsNonZero) (β' : Weight K H L) (n : ℤ) (hβ' : (β' : H → K) = n • α + β) :
    chainTopCoeff α β' = chainTopCoeff α β - n := by
  apply le_antisymm
  · refine le_sub_iff_add_le.mpr ((rootSpace_zsmul_add_ne_bot_iff α β hα _).mp ?_).1
    rw [add_smul, add_assoc, ← hβ', ← coe_chainTop]
    exact (chainTop α β').2
  · refine ((rootSpace_zsmul_add_ne_bot_iff α β' hα _).mp ?_).1
    rw [hβ', ← add_assoc, ← add_smul, sub_add_cancel, ← coe_chainTop]
    exact (chainTop α β).2

lemma chainBotCoeff_of_eq_zsmul_add
    (hα : α.IsNonZero) (β' : Weight K H L) (n : ℤ) (hβ' : (β' : H → K) = n • α + β) :
    chainBotCoeff α β' = chainBotCoeff α β + n := by
  have : (β' : H → K) = -n • (-α) + β := by rwa [neg_smul, smul_neg, neg_neg]
  rw [chainBotCoeff, chainBotCoeff, ← Weight.coe_neg,
    chainTopCoeff_of_eq_zsmul_add (-α) β hα.neg β' (-n) this, sub_neg_eq_add]

lemma chainLength_of_eq_zsmul_add (β' : Weight K H L) (n : ℤ) (hβ' : (β' : H → K) = n • α + β) :
    chainLength α β' = chainLength α β := by
  by_cases hα : α.IsZero
  · rw [chainLength_of_isZero _ _ hα, chainLength_of_isZero _ _ hα]
  · apply Nat.cast_injective (R := ℤ)
    rw [← chainTopCoeff_add_chainBotCoeff, ← chainTopCoeff_add_chainBotCoeff,
      Nat.cast_add, Nat.cast_add, chainTopCoeff_of_eq_zsmul_add α β hα β' n hβ',
      chainBotCoeff_of_eq_zsmul_add α β hα β' n hβ', sub_eq_add_neg, add_add_add_comm,
      neg_add_cancel, add_zero]

lemma chainTopCoeff_zero_right [Nontrivial L] (hα : α.IsNonZero) :
    chainTopCoeff α (0 : Weight K H L) = 1 := by
  symm
  apply eq_of_le_of_not_lt
  · rw [Nat.one_le_iff_ne_zero]
    intro e
    exact α.2 (by simpa [e, Weight.coe_zero] using
      genWeightSpace_chainTopCoeff_add_one_nsmul_add α (0 : Weight K H L) hα)
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α (0 : Weight K H L)).exists_ne_zero
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have prim : isSl2.HasPrimitiveVectorWith x (chainLength α (0 : Weight K H L) : K) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨x_ne0, (chainLength_smul _ _ hx).symm, by rwa [genWeightSpace_add_chainTop _ _ hα] at this⟩
  obtain ⟨k, hk⟩ : ∃ k : K, k • f =
      (toEnd K L L f ^ (chainTopCoeff α (0 : Weight K H L) + 1)) x := by
    have : (toEnd K L L f ^ (chainTopCoeff α (0 : Weight K H L) + 1)) x ∈ rootSpace H (-α) := by
      convert toEnd_pow_apply_mem hf hx (chainTopCoeff α (0 : Weight K H L) + 1) using 2
      rw [coe_chainTop', Weight.coe_zero, add_zero, succ_nsmul',
        add_assoc, smul_neg, neg_add_cancel, add_zero]
    simpa using (finrank_eq_one_iff_of_nonzero' ⟨f, hf⟩ (by simpa using isSl2.f_ne_zero)).mp
      (finrank_rootSpace_eq_one _ hα.neg) ⟨_, this⟩
  apply_fun (⁅f, ·⁆) at hk
  simp only [lie_smul, lie_self, smul_zero, prim.lie_f_pow_toEnd_f] at hk
  intro e
  refine prim.pow_toEnd_f_ne_zero_of_eq_nat rfl ?_ hk.symm
  have := (apply_coroot_eq_cast' α 0).symm
  simp only [← @Nat.cast_two ℤ, ← Nat.cast_mul, Weight.zero_apply, Int.cast_eq_zero, sub_eq_zero,
    Nat.cast_inj] at this
  rwa [this, Nat.succ_le, two_mul, add_lt_add_iff_left]

lemma chainBotCoeff_zero_right [Nontrivial L] (hα : α.IsNonZero) :
    chainBotCoeff α (0 : Weight K H L) = 1 :=
  chainTopCoeff_zero_right (-α) hα.neg

lemma chainLength_zero_right [Nontrivial L] (hα : α.IsNonZero) : chainLength α 0 = 2 := by
  rw [← chainBotCoeff_add_chainTopCoeff, chainTopCoeff_zero_right α hα,
    chainBotCoeff_zero_right α hα]

lemma rootSpace_two_smul (hα : α.IsNonZero) : rootSpace H (2 • α) = ⊥ := by
  cases subsingleton_or_nontrivial L
  · exact IsEmpty.elim inferInstance α
  simpa [chainTopCoeff_zero_right α hα] using
    genWeightSpace_chainTopCoeff_add_one_nsmul_add α (0 : Weight K H L) hα

lemma rootSpace_one_div_two_smul (hα : α.IsNonZero) : rootSpace H ((2⁻¹ : K) • α) = ⊥ := by
  by_contra h
  let W : Weight K H L := ⟨_, h⟩
  have hW : 2 • (W : H → K) = α := by
    show 2 • (2⁻¹ : K) • (α : H → K) = α
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul]; simp
  apply α.genWeightSpace_ne_bot
  have := rootSpace_two_smul W (fun (e : (W : H → K) = 0) ↦ hα <| by
    apply_fun (2 • ·) at e; simpa [hW] using e)
  rwa [hW] at this

lemma eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul
    (hα : α.IsNonZero) (k : K) (h : (β : H → K) = k • α) :
    k = -1 ∨ k = 0 ∨ k = 1 := by
  cases subsingleton_or_nontrivial L
  · exact IsEmpty.elim inferInstance α
  have H := apply_coroot_eq_cast' α β
  rw [h] at H
  simp only [Pi.smul_apply, root_apply_coroot hα] at H
  rcases (chainLength α β).even_or_odd with (⟨n, hn⟩|⟨n, hn⟩)
  · rw [hn, ← two_mul] at H
    simp only [smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, ← mul_sub, ← mul_comm (2 : K),
      Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at H
    rw [← Int.cast_natCast, ← Int.cast_natCast (chainTopCoeff α β), ← Int.cast_sub] at H
    have := (rootSpace_zsmul_add_ne_bot_iff_mem α 0 hα (n - chainTopCoeff α β)).mp
      (by rw [← Int.cast_smul_eq_zsmul K, ← H, ← h, Weight.coe_zero, add_zero]; exact β.2)
    rw [chainTopCoeff_zero_right α hα, chainBotCoeff_zero_right α hα, Nat.cast_one] at this
    set k' : ℤ := n - chainTopCoeff α β
    subst H
    have : k' ∈ ({-1, 0, 1} : Finset ℤ) := by
      show k' ∈ Finset.Icc (-1 : ℤ) (1 : ℤ)
      exact this
    simpa only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton, ← @Int.cast_inj K,
      Int.cast_zero, Int.cast_neg, Int.cast_one] using this
  · apply_fun (· / 2) at H
    rw [hn, smul_eq_mul] at H
    have hk : k = n + 2⁻¹ - chainTopCoeff α β := by simpa [sub_div, add_div] using H
    have := (rootSpace_zsmul_add_ne_bot_iff α β hα (chainTopCoeff α β - n)).mpr ?_
    swap
    · simp only [tsub_le_iff_right, le_add_iff_nonneg_right, Nat.cast_nonneg, neg_sub, true_and]
      rw [← Nat.cast_add, chainBotCoeff_add_chainTopCoeff, hn]
      omega
    rw [h, hk, ← Int.cast_smul_eq_zsmul K, ← add_smul] at this
    simp only [Int.cast_sub, Int.cast_natCast,
      sub_add_sub_cancel', add_sub_cancel_left, ne_eq] at this
    cases this (rootSpace_one_div_two_smul α hα)

/-- `±α` are the only `K`-multiples of a root `α` that are also (non-zero) roots. -/
lemma eq_neg_or_eq_of_eq_smul (hβ : β.IsNonZero) (k : K) (h : (β : H → K) = k • α) :
    β = -α ∨ β = α := by
  by_cases hα : α.IsZero
  · rw [hα, smul_zero] at h; cases hβ h
  rcases eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul α β hα k h with (rfl | rfl | rfl)
  · exact .inl (by ext; rw [h, neg_one_smul]; rfl)
  · cases hβ (by rwa [zero_smul] at h)
  · exact .inr (by ext; rw [h, one_smul])

/-- The reflection of a root along another. -/
def reflectRoot (α β : Weight K H L) : Weight K H L where
  toFun := β - β (coroot α) • α
  genWeightSpace_ne_bot' := by
    by_cases hα : α.IsZero
    · simpa [hα.eq] using β.genWeightSpace_ne_bot
    rw [sub_eq_neg_add, apply_coroot_eq_cast α β, ← neg_smul, ← Int.cast_neg,
      Int.cast_smul_eq_zsmul, rootSpace_zsmul_add_ne_bot_iff α β hα]
    omega

lemma reflectRoot_isNonZero (α β : Weight K H L) (hβ : β.IsNonZero) :
    (reflectRoot α β).IsNonZero := by
  intro e
  have : β (coroot α) = 0 := by
    by_cases hα : α.IsZero
    · simp [coroot_eq_zero_iff.mpr hα]
    apply add_left_injective (β (coroot α))
    simpa [root_apply_coroot hα, mul_two] using congr_fun (sub_eq_zero.mp e) (coroot α)
  have : reflectRoot α β = β := by ext; simp [reflectRoot, this]
  exact hβ (this ▸ e)

variable (H)

/-- The root system of a finite-dimensional Lie algebra with non-degenerate Killing form over a
field of characteristic zero, relative to a splitting Cartan subalgebra. -/
def rootSystem :
    RootSystem H.root K (Dual K H) H :=
  RootSystem.mk'
    IsReflexive.toPerfectPairingDual
    { toFun := (↑)
      inj' := by
        intro α β h; ext x; simpa using LinearMap.congr_fun h x  }
    { toFun := coroot ∘ (↑)
      inj' := by rintro ⟨α, hα⟩ ⟨β, hβ⟩ h; simpa using h }
    (fun ⟨α, hα⟩ ↦ by simpa using root_apply_coroot <| by simpa using hα)
    (by
      rintro ⟨α, hα⟩ - ⟨⟨β, hβ⟩, rfl⟩
      simp only [Function.Embedding.coeFn_mk, IsReflexive.toPerfectPairingDual_toLin,
        Function.comp_apply, Set.mem_range, Subtype.exists, exists_prop]
      exact ⟨reflectRoot α β, (by simpa using reflectRoot_isNonZero α β <| by simpa using hβ), rfl⟩)
    (by convert span_weight_isNonZero_eq_top K L H; ext; simp)
    (fun α β ↦
      ⟨chainBotCoeff β.1 α.1 - chainTopCoeff β.1 α.1, by simp [apply_coroot_eq_cast β.1 α.1]⟩)

@[simp]
lemma corootForm_rootSystem_eq_killing :
    (rootSystem H).CorootForm = (killingForm K L).restrict H := by
  rw [restrict_killingForm_eq_sum, RootPairing.CorootForm, ← Finset.sum_coe_sort (s := H.root)]
  rfl

@[simp] lemma rootSystem_toPerfectPairing_apply (f x) : (rootSystem H).toPerfectPairing f x = f x :=
  rfl
@[simp] lemma rootSystem_pairing_apply (α β) : (rootSystem H).pairing β α = β.1 (coroot α.1) := rfl
@[simp] lemma rootSystem_root_apply (α) : (rootSystem H).root α = α := rfl
@[simp] lemma rootSystem_coroot_apply (α) : (rootSystem H).coroot α = coroot α := rfl

instance : (rootSystem H).IsCrystallographic where
  exists_value α β :=
    ⟨chainBotCoeff β.1 α.1 - chainTopCoeff β.1 α.1, by simp [apply_coroot_eq_cast β.1 α.1]⟩

instance : (rootSystem H).IsReduced where
  eq_or_eq_neg := by
    intro ⟨α, hα⟩ ⟨β, hβ⟩ e
    rw [LinearIndependent.pair_iff' ((rootSystem H).ne_zero _), not_forall] at e
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, rootSystem_root_apply, ne_eq, not_not] at e
    obtain ⟨u, hu⟩ := e
    obtain (h | h) := eq_neg_or_eq_of_eq_smul α β (by simpa using hβ) u
      (by ext x; exact DFunLike.congr_fun hu.symm x)
    · right; ext x; simpa [neg_eq_iff_eq_neg] using DFunLike.congr_fun h.symm x
    · left; ext x; simpa using DFunLike.congr_fun h.symm x

end LieAlgebra.IsKilling

section jjj

variable (K L : Type*) [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [LieAlgebra.IsSimple K L] [FiniteDimensional K L]
  [LieAlgebra.IsKilling K L] -- Follows from simplicity; will be redundant after #10068 done
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

set_option maxHeartbeats 2000000

lemma invtSubmodule_reflection:
   ∀ (q : Submodule K (Module.Dual K H)), (∀ (i : H.root), q ∈ Module.End.invtSubmodule
      ((LieAlgebra.IsKilling.rootSystem H).reflection i)) → q ≠ ⊥ → q = ⊤ := by
  have _i := LieModule.nontrivial_of_isIrreducible K L L
  let S := (LieAlgebra.IsKilling.rootSystem H)
  by_contra!
  obtain ⟨q, h₀, h₁, h₃⟩ := this
  suffices h₂ : ∀ Φ, Φ.Nonempty → S.root '' Φ ⊆ q → (∀ i ∉ Φ, q ≤ LinearMap.ker (S.coroot' i)) →
      Φ = Set.univ by
    have := (S.invtsubmodule_to_root_subset q h₁ h₀) h₂
    apply False.elim (h₃ this)
  intro Φ hΦ₁ hΦ₂ hΦ₃
  by_contra hc
  have hΦ₂' : ∀ i ∈ Φ, (S.root i) ∈ q := by
    intro i hi
    apply hΦ₂
    exact Set.mem_image_of_mem S.root hi
  have s₁ (i j : H.root) (h₁ : i ∈ Φ) (h₂ : j ∉ Φ) : S.root i (S.coroot j) = 0 :=
    (hΦ₃ j h₂) (hΦ₂' i h₁)
  have s₁' (i j : H.root) (h₁ : i ∈ Φ) (h₂ : j ∉ Φ) : S.root j (S.coroot i) = 0 :=
    (S.pairing_zero_iff (i := i) (j := j)).1 (s₁ i j h₁ h₂)
  have s₂ (i j : H.root) (h₁ : i ∈ Φ) (h₂ : j ∉ Φ) : i.1 (LieAlgebra.IsKilling.coroot j) = 0 :=
    s₁ i j h₁ h₂
  have s₂' (i j : H.root) (h₁ : i ∈ Φ) (h₂ : j ∉ Φ) : j.1 (LieAlgebra.IsKilling.coroot i) = 0 :=
    s₁' i j h₁ h₂
  have s₃ (i j : H.root) (h₁ : i ∈ Φ) (h₂ : j ∉ Φ) :
      LieModule.genWeightSpace L (i.1.1 + j.1.1) = ⊥ := by
    by_contra!
    have inz : i.1.IsNonZero := by
      obtain ⟨val_1, property_1⟩ := i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at property_1
      exact property_1
    have jnz : j.1.IsNonZero := by
      obtain ⟨val_1, property_1⟩ := j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at property_1
      exact property_1
    let r := LieModule.Weight.mk (R := K) (L := H) (M := L) (i.1.1 + j.1.1) this
    have r₁ : r ≠ 0 := by
      intro a
      have h : i.1 = -j.1 := LieModule.Weight.ext <| congrFun (eq_neg_of_add_eq_zero_left <| by
        have := congr_arg LieModule.Weight.toFun a
        simp at this; exact this)
      have := s₂ i j h₁ h₂
      rw [h, LieModule.Weight.coe_neg, Pi.neg_apply,
      LieAlgebra.IsKilling.root_apply_coroot (K := K) (H := H) (L := L) jnz] at this
      field_simp at this
    have r₂ : r ∈ H.root := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact LieModule.Weight.isNonZero_iff_ne_zero.mpr r₁
    rcases Classical.em (⟨r, r₂⟩ ∈ Φ) with h | h
    have abs : (0 : K) = 2 := by
      calc
        0 = (i.1.1 + j.1.1) (LieAlgebra.IsKilling.coroot j) := by apply (s₂ ⟨r, r₂⟩ j h h₂).symm
        _ = i.1.1 (LieAlgebra.IsKilling.coroot j) + j.1.1 (LieAlgebra.IsKilling.coroot j) := by
          exact rfl
        _ = 0 + 2 := by
          have e₁ : i.1.1 (LieAlgebra.IsKilling.coroot j) = 0 := s₂ i j h₁ h₂
          have e₂ : j.1.1 (LieAlgebra.IsKilling.coroot j) = 2 :=
            LieAlgebra.IsKilling.root_apply_coroot jnz
          rw [e₁, e₂]
        _ = 2 := by rw [zero_add]
    field_simp at abs
    have abs : (0 : K) = 2 := by
      calc
        0 = (i.1.1 + j.1.1) (LieAlgebra.IsKilling.coroot i) := by apply (s₂' i ⟨r, r₂⟩ h₁ h).symm
        _ = i.1.1 (LieAlgebra.IsKilling.coroot i) + j.1.1 (LieAlgebra.IsKilling.coroot i) := by
          exact rfl
        _ = 2 + 0 := by
          have e₁ : j.1.1 (LieAlgebra.IsKilling.coroot i) = 0 := s₂' i j h₁ h₂
          have e₂ : i.1.1 (LieAlgebra.IsKilling.coroot i) = 2 :=
            LieAlgebra.IsKilling.root_apply_coroot inz
          rw [e₁, e₂]
        _ = 2 := by rw [add_zero]
    field_simp at abs
  have rr4 (i j : H.root) (h1 : i ∈ Φ) (h2 : j ∉ Φ) (li : LieAlgebra.rootSpace H i.1.1)
      (lj : LieAlgebra.rootSpace H j.1.1) : ⁅li.1, lj.1⁆ = 0 := by
    have ttt := LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace li.2 lj.2
    have := s₃ i j h1 h2
    rw [this] at ttt
    exact ttt
  have help : ⨆ χ : LieModule.Weight K H L, LieModule.genWeightSpace L χ = ⊤ := by
    exact LieModule.iSup_genWeightSpace_eq_top' K H L
  let gg := ⋃ i ∈ Φ, (LieAlgebra.rootSpace H i : Set L)
  let I := LieSubalgebra.lieSpan K L gg
  have rr5 : I ≠ ⊤ := by
    have : ∃ (j : H.root), j ∉ Φ := by
      exact (Set.ne_univ_iff_exists_not_mem Φ).mp hc
    obtain ⟨j, hj⟩ := this
    --rrrr : { x // x ∈ LieSubalgebra.root }
    obtain ⟨z, hz1, hz2⟩ := LieModule.Weight.exists_ne_zero (R := K) (L := H) (M := L) j
    by_contra!
    have lll : z ∈ LieAlgebra.center K L := by
      have rrr (x : L) : ⁅x, z⁆ = 0 := by
        have qq : x ∈ I := by
          rw [this]
          exact trivial
        simp [I] at qq
        refine LieSubalgebra.lieSpan_induction (R := K) (L := L) ?_ ?_ ?_ ?_ ?_ qq
        intro x hx
        obtain ⟨i, hi, hx1_mem⟩ := Set.mem_iUnion₂.mp hx
        have := rr4 i j hi hj
        simp at this
        have ssss2 := this x hx1_mem
        have ssss3 := ssss2 z hz1
        exact ssss3
        exact zero_lie z
        intro a b c d e f
        simp only [add_lie]
        rw [e, f, add_zero]
        intro a b c d
        simp only [smul_lie, smul_eq_zero]
        right
        exact d
        intro a b c d e f
        simp only [lie_lie]
        rw [e, f, lie_zero, lie_zero, sub_self]
      exact rrr
    have cent := LieAlgebra.center_eq_bot (R := K) (L := L)
    rw [cent] at lll
    exact hz2 lll
  have rr6 : I ≠ ⊥ := by
    have : ∃ (rrrr : H.root), rrrr ∈ Φ := by
      refine Set.nonempty_def.mp ?_
      exact hΦ₁
    obtain ⟨rrrr, rrrr1⟩ := this
    obtain ⟨x, hx1, hx2⟩ := LieModule.Weight.exists_ne_zero (R := K) (L := H) (M := L) rrrr
    have : x ∈ gg := by
      apply Set.mem_iUnion_of_mem rrrr
      simp only [LieModule.Weight.coe_coe, Set.mem_iUnion, SetLike.mem_coe, exists_prop]
      constructor
      exact rrrr1
      exact hx1
    have cc : x ∈ I := by
      exact LieSubalgebra.mem_lieSpan.mpr fun K_1 a ↦ a this
    by_contra!
    have dddd := LieSubalgebra.eq_bot_iff I
    have dddd2 := dddd.1 this
    have dddd3 := dddd2 x cc
    exact hx2 dddd3
  have rr7 : ∀ x y : L, y ∈ I → ⁅x, y⁆ ∈ I := by
    have help : ⨆ χ : LieModule.Weight K H L, (LieModule.genWeightSpace L χ).toSubmodule = ⊤ := by
      exact LieModule.iSup_genWeightSpace_as_module_eq_top' K H L
    intro x y
    intro hy
    have hx : x ∈ ⨆ χ : LieModule.Weight K H L, (LieModule.genWeightSpace L χ).toSubmodule := by
      rw [help]
      simp only [Submodule.mem_top]
    induction hx using Submodule.iSup_induction' with
    | mem j x hx =>
      --simp_all
      --(p := (y : L) → y ∈ LieSubalgebra.lieSpan K L gg → ⁅x, y⁆ ∈ LieSubalgebra.lieSpan K L gg)
      simp [I] at hy
      refine LieSubalgebra.lieSpan_induction (R := K) (L := L) ?_ ?_ ?_ ?_ ?_ hy
      --intro a x_1
      intro x1 hx1
      obtain ⟨i, hi, hx1_mem⟩ := Set.mem_iUnion₂.mp hx1
      have rr79 (j : LieModule.Weight K H L) : j = 0 ∨ j ∈ H.root := by
        have : j = 0 ∨ j ≠ 0 := by
          exact eq_or_ne j 0
        rcases this with h | h
        · left
          exact h
        right
        refine Finset.mem_filter.mpr ?_
        constructor
        · exact Finset.mem_univ j
        exact LieModule.Weight.isNonZero_iff_ne_zero.mpr h
      have step1 := rr79 j
      rcases step1 with h | h
      have ttt := LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace hx hx1_mem
      simp at ttt
      rw [h] at ttt
      simp at ttt
      have rrrr : ⁅x, x1⁆ ∈ gg := by
        exact Set.mem_biUnion hi ttt
      exact LieSubalgebra.mem_lieSpan.mpr fun K_1 a ↦ a rrrr
      --obtain ⟨j1, j2⟩ := j
      let jj : H.root := ⟨j, h⟩
      --simp only [Finset.mem_filter, Finset.mem_univ, true_and, I] at jj
      rcases (Classical.em (jj ∈ Φ)) with h | h
      --simp at jj
      have hx2 : x ∈ LieModule.genWeightSpace L jj.1 := hx
      have rrrr : x ∈ gg := by
        exact Set.mem_biUnion h hx2
      have rrrr2 : x ∈ I := by
        exact LieSubalgebra.mem_lieSpan.mpr fun K_1 a ↦ a rrrr
      have rrrr3 : x1 ∈ I := by
         exact LieSubalgebra.mem_lieSpan.mpr fun K_1 a ↦ a hx1
      exact LieSubalgebra.lie_mem I rrrr2 rrrr3
      have key : ⁅x1, x⁆ = 0 := by
        have := rr4 i jj hi h
        simp at this
        have ssss2 := this x1 hx1_mem
        have ssss3 := ssss2 x hx
        exact ssss3
      have : ⁅x, x1⁆ = 0 := by
        rw [← neg_eq_zero, lie_skew x1 x, key]
      rw [this]
      exact LieSubalgebra.zero_mem I
      · simp only [lie_zero, LieSubalgebra.zero_mem, I]
      · intro a b c d e f
        simp only [lie_add, I]
        exact LieSubalgebra.add_mem I e f
      · intro a b c d
        simp only [lie_smul, I]
        exact LieSubalgebra.smul_mem I a d
      · intro x_1
        intro zzz
        intro x_2
        intro zzz_2
        intro hx_1
        intro hxzzz
        have x1n : x_1 ∈ I := x_2
        have z1n : zzz ∈ I := zzz_2
        have : ⁅x, ⁅x_1, zzz⁆⁆ = ⁅⁅x, x_1⁆, zzz⁆ + ⁅x_1, ⁅x, zzz⁆⁆ := by
          simp
        rw [this]
        have p1 : ⁅⁅x, x_1⁆, zzz⁆ ∈ I := by
          exact LieSubalgebra.lie_mem I hx_1 z1n
        have p2 : ⁅x_1, ⁅x, zzz⁆⁆ ∈ I := by
          exact LieSubalgebra.lie_mem I x1n hxzzz
        exact LieSubalgebra.add_mem I p1 p2
    | zero =>
      simp only [zero_lie, LieSubalgebra.zero_mem]
    | add x1 y1 _ _ hx hy =>
      simp only [add_lie]
      exact LieSubalgebra.add_mem I hx hy
  have rr8 := (LieSubalgebra.exists_lieIdeal_coe_eq_iff (R := K) (L := L) (K := I)).2 rr7
  obtain ⟨I', hhh⟩ := rr8
  have rr9 : LieAlgebra.IsSimple K L := inferInstance
  have := rr9.eq_bot_or_eq_top I'
  have rr52 : I' ≠ ⊤ := by
    rw [← hhh] at rr5
    exact ne_of_apply_ne (LieIdeal.toLieSubalgebra K L) rr5
  have rr62 : I' ≠ ⊥ := by
    rw [← hhh] at rr6
    exact ne_of_apply_ne (LieIdeal.toLieSubalgebra K L) rr6
  rcases this with h_bot | h_top
  · contradiction
  contradiction

instance : (LieAlgebra.IsKilling.rootSystem H).IsIrreducible := by
  have _i := LieModule.nontrivial_of_isIrreducible K L L
  exact RootPairing.IsIrreducible.mk' (LieAlgebra.IsKilling.rootSystem H).toRootPairing
    (invtSubmodule_reflection K L H)

end jjj
