/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Data.IsROrC.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Analysis.NormedSpace.Pointwise

#align_import analysis.normed_space.is_R_or_C from "leanprover-community/mathlib"@"3f655f5297b030a87d641ad4e825af8d9679eb0b"

/-!
# Normed spaces over R or C

This file is about results on normed spaces over the fields `ℝ` and `ℂ`.

## Main definitions

None.

## Main theorems

* `ContinuousLinearMap.op_norm_bound_of_ball_bound`: A bound on the norms of values of a linear
  map in a ball yields a bound on the operator norm.

## Notes

This file exists mainly to avoid importing `IsROrC` in the main normed space theory files.
-/


open Metric

variable {𝕜 : Type*} [IsROrC 𝕜] {E : Type*} [NormedAddCommGroup E]

theorem IsROrC.norm_coe_norm {z : E} : ‖(‖z‖ : 𝕜)‖ = ‖z‖ := by simp
                                                               -- 🎉 no goals
#align is_R_or_C.norm_coe_norm IsROrC.norm_coe_norm

variable [NormedSpace 𝕜 E]

/-- Lemma to normalize a vector in a normed space `E` over either `ℂ` or `ℝ` to unit length. -/
@[simp]
theorem norm_smul_inv_norm {x : E} (hx : x ≠ 0) : ‖(‖x‖⁻¹ : 𝕜) • x‖ = 1 := by
  have : ‖x‖ ≠ 0 := by simp [hx]
  -- ⊢ ‖(↑‖x‖)⁻¹ • x‖ = 1
  field_simp [norm_smul]
  -- 🎉 no goals
#align norm_smul_inv_norm norm_smul_inv_norm

/-- Lemma to normalize a vector in a normed space `E` over either `ℂ` or `ℝ` to length `r`. -/
theorem norm_smul_inv_norm' {r : ℝ} (r_nonneg : 0 ≤ r) {x : E} (hx : x ≠ 0) :
    ‖((r : 𝕜) * (‖x‖ : 𝕜)⁻¹) • x‖ = r := by
  have : ‖x‖ ≠ 0 := by simp [hx]
  -- ⊢ ‖(↑r * (↑‖x‖)⁻¹) • x‖ = r
  field_simp [norm_smul, r_nonneg, isROrC_simps]
  -- 🎉 no goals
#align norm_smul_inv_norm' norm_smul_inv_norm'

theorem LinearMap.bound_of_sphere_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] 𝕜)
    (h : ∀ z ∈ sphere (0 : E) r, ‖f z‖ ≤ c) (z : E) : ‖f z‖ ≤ c / r * ‖z‖ := by
  by_cases z_zero : z = 0
  -- ⊢ ‖↑f z‖ ≤ c / r * ‖z‖
  · rw [z_zero]
    -- ⊢ ‖↑f 0‖ ≤ c / r * ‖0‖
    simp only [LinearMap.map_zero, norm_zero, mul_zero]
    -- ⊢ 0 ≤ 0
    exact le_rfl
    -- 🎉 no goals
  set z₁ := ((r : 𝕜) * (‖z‖ : 𝕜)⁻¹) • z with hz₁
  -- ⊢ ‖↑f z‖ ≤ c / r * ‖z‖
  have norm_f_z₁ : ‖f z₁‖ ≤ c := by
    apply h
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm' r_pos.le z_zero
  have r_ne_zero : (r : 𝕜) ≠ 0 := IsROrC.ofReal_ne_zero.mpr r_pos.ne'
  -- ⊢ ‖↑f z‖ ≤ c / r * ‖z‖
  have eq : f z = ‖z‖ / r * f z₁ := by
    rw [hz₁, LinearMap.map_smul, smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc, div_mul_cancel _ r_ne_zero, mul_inv_cancel, one_mul]
    simp only [z_zero, IsROrC.ofReal_eq_zero, norm_eq_zero, Ne.def, not_false_iff]
  rw [eq, norm_mul, norm_div, IsROrC.norm_coe_norm, IsROrC.norm_of_nonneg r_pos.le,
    div_mul_eq_mul_div, div_mul_eq_mul_div, mul_comm]
  apply div_le_div _ _ r_pos rfl.ge
  -- ⊢ 0 ≤ c * ‖z‖
  · exact mul_nonneg ((norm_nonneg _).trans norm_f_z₁) (norm_nonneg z)
    -- 🎉 no goals
  apply mul_le_mul norm_f_z₁ rfl.le (norm_nonneg z) ((norm_nonneg _).trans norm_f_z₁)
  -- 🎉 no goals
#align linear_map.bound_of_sphere_bound LinearMap.bound_of_sphere_bound

/-- `LinearMap.bound_of_ball_bound` is a version of this over arbitrary nontrivially normed fields.
It produces a less precise bound so we keep both versions. -/
theorem LinearMap.bound_of_ball_bound' {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] 𝕜)
    (h : ∀ z ∈ closedBall (0 : E) r, ‖f z‖ ≤ c) (z : E) : ‖f z‖ ≤ c / r * ‖z‖ :=
  f.bound_of_sphere_bound r_pos c (fun z hz => h z hz.le) z
#align linear_map.bound_of_ball_bound' LinearMap.bound_of_ball_bound'

theorem ContinuousLinearMap.op_norm_bound_of_ball_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ)
    (f : E →L[𝕜] 𝕜) (h : ∀ z ∈ closedBall (0 : E) r, ‖f z‖ ≤ c) : ‖f‖ ≤ c / r := by
  apply ContinuousLinearMap.op_norm_le_bound
  -- ⊢ 0 ≤ c / r
  · apply div_nonneg _ r_pos.le
    -- ⊢ 0 ≤ c
    exact
      (norm_nonneg _).trans
        (h 0 (by simp only [norm_zero, mem_closedBall, dist_zero_left, r_pos.le]))
  apply LinearMap.bound_of_ball_bound' r_pos
  -- ⊢ ∀ (z : E), z ∈ closedBall 0 r → ‖↑↑f z‖ ≤ c
  exact fun z hz => h z hz
  -- 🎉 no goals
#align continuous_linear_map.op_norm_bound_of_ball_bound ContinuousLinearMap.op_norm_bound_of_ball_bound

variable (𝕜)

theorem NormedSpace.sphere_nonempty_isROrC [Nontrivial E] {r : ℝ} (hr : 0 ≤ r) :
    Nonempty (sphere (0 : E) r) :=
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  (NormedSpace.sphere_nonempty.mpr hr).coe_sort
#align normed_space.sphere_nonempty_is_R_or_C NormedSpace.sphere_nonempty_isROrC
