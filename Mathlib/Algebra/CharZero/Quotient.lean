/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Module.NatInt
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Lemmas about quotients in characteristic zero
-/


variable {R : Type*} [DivisionRing R] [CharZero R] {p : R}

namespace AddSubgroup

/-- `z • r` is a multiple of `p` iff `r` is `k * (p / z)` above a multiple of `p`, where
`0 ≤ k < |z|`. -/
theorem zsmul_mem_zmultiples_iff_exists_sub_div {r : R} {z : ℤ} (hz : z ≠ 0) :
    z • r ∈ AddSubgroup.zmultiples p ↔
      ∃ k : Fin z.natAbs, r - (k : ℕ) • (p / z : R) ∈ AddSubgroup.zmultiples p := by
  rw [AddSubgroup.mem_zmultiples_iff]
  simp_rw [AddSubgroup.mem_zmultiples_iff, div_eq_mul_inv, ← smul_mul_assoc, eq_sub_iff_add_eq]
  have hz' : (z : R) ≠ 0 := Int.cast_ne_zero.mpr hz
  conv_rhs => simp +singlePass only [← (mul_right_injective₀ hz').eq_iff]
  simp_rw [← zsmul_eq_mul, smul_add, ← mul_smul_comm, zsmul_eq_mul (z : R)⁻¹, mul_inv_cancel₀ hz',
    mul_one, ← natCast_zsmul, smul_smul, ← add_smul]
  constructor
  · rintro ⟨k, h⟩
    simp_rw [← h]
    refine ⟨⟨(k % z).toNat, ?_⟩, k / z, ?_⟩
    · rw [← Int.ofNat_lt, Int.toNat_of_nonneg (Int.emod_nonneg _ hz)]
      exact (Int.emod_lt_abs _ hz).trans_eq (Int.abs_eq_natAbs _)
    rw [Fin.val_mk, Int.toNat_of_nonneg (Int.emod_nonneg _ hz)]
    nth_rewrite 3 [← Int.ediv_add_emod k z]
    rfl
  · rintro ⟨k, n, h⟩
    exact ⟨_, h⟩

theorem nsmul_mem_zmultiples_iff_exists_sub_div {r : R} {n : ℕ} (hn : n ≠ 0) :
    n • r ∈ AddSubgroup.zmultiples p ↔
      ∃ k : Fin n, r - (k : ℕ) • (p / n : R) ∈ AddSubgroup.zmultiples p := by
  rw [← natCast_zsmul r, zsmul_mem_zmultiples_iff_exists_sub_div (Int.natCast_ne_zero.mpr hn),
    Int.cast_natCast]
  rfl

end AddSubgroup

namespace QuotientAddGroup

theorem zmultiples_zsmul_eq_zsmul_iff {ψ θ : R ⧸ AddSubgroup.zmultiples p} {z : ℤ} (hz : z ≠ 0) :
    z • ψ = z • θ ↔ ∃ k : Fin z.natAbs, ψ = θ + ((k : ℕ) • (p / z) : R) := by
  induction ψ using Quotient.inductionOn
  induction θ using Quotient.inductionOn
  -- Porting note: Introduced Zp notation to shorten lines
  let Zp := AddSubgroup.zmultiples p
  have : (Quotient.mk _ : R → R ⧸ Zp) = ((↑) : R → R ⧸ Zp) := rfl
  simp only [Zp, this]
  simp_rw [← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_add,
    QuotientAddGroup.eq_iff_sub_mem, ← smul_sub, ← sub_sub]
  exact AddSubgroup.zsmul_mem_zmultiples_iff_exists_sub_div hz

theorem zmultiples_nsmul_eq_nsmul_iff {ψ θ : R ⧸ AddSubgroup.zmultiples p} {n : ℕ} (hz : n ≠ 0) :
    n • ψ = n • θ ↔ ∃ k : Fin n, ψ = θ + (k : ℕ) • (p / n : R) := by
  rw [← natCast_zsmul ψ, ← natCast_zsmul θ,
    zmultiples_zsmul_eq_zsmul_iff (Int.natCast_ne_zero.mpr hz), Int.cast_natCast]
  rfl

end QuotientAddGroup
