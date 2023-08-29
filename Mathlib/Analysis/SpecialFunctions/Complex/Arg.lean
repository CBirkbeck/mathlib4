/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

#align_import analysis.special_functions.complex.arg from "leanprover-community/mathlib"@"2c1d8ca2812b64f88992a5294ea3dba144755cd1"

/-!
# The argument of a complex number.

We define `arg : ℂ → ℝ`, returning a real number in the range (-π, π],
such that for `x ≠ 0`, `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
while `arg 0` defaults to `0`
-/


noncomputable section

namespace Complex

open ComplexConjugate Real Topology

open Filter Set

/-- `arg` returns values in the range (-π, π], such that for `x ≠ 0`,
  `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
  `arg 0` defaults to `0` -/
noncomputable def arg (x : ℂ) : ℝ :=
  if 0 ≤ x.re then Real.arcsin (x.im / abs x)
  else if 0 ≤ x.im then Real.arcsin ((-x).im / abs x) + π else Real.arcsin ((-x).im / abs x) - π
#align complex.arg Complex.arg

theorem sin_arg (x : ℂ) : Real.sin (arg x) = x.im / abs x := by
  unfold arg; split_ifs <;>
  -- ⊢ Real.sin (if 0 ≤ x.re then arcsin (x.im / ↑abs x) else if 0 ≤ x.im then arcs …
    simp [sub_eq_add_neg, arg,
      Real.sin_arcsin (abs_le.1 (abs_im_div_abs_le_one x)).1 (abs_le.1 (abs_im_div_abs_le_one x)).2,
      Real.sin_add, neg_div, Real.arcsin_neg, Real.sin_neg]
#align complex.sin_arg Complex.sin_arg

theorem cos_arg {x : ℂ} (hx : x ≠ 0) : Real.cos (arg x) = x.re / abs x := by
  rw [arg]
  -- ⊢ Real.cos (if 0 ≤ x.re then arcsin (x.im / ↑abs x) else if 0 ≤ x.im then arcs …
  split_ifs with h₁ h₂
  · rw [Real.cos_arcsin]
    -- ⊢ sqrt (1 - (x.im / ↑abs x) ^ 2) = x.re / ↑abs x
    field_simp [Real.sqrt_sq, (abs.pos hx).le, *]
    -- 🎉 no goals
  · rw [Real.cos_add_pi, Real.cos_arcsin]
    -- ⊢ -sqrt (1 - ((-x).im / ↑abs x) ^ 2) = x.re / ↑abs x
    field_simp [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs,
      _root_.abs_of_neg (not_le.1 h₁), *]
  · rw [Real.cos_sub_pi, Real.cos_arcsin]
    -- ⊢ -sqrt (1 - ((-x).im / ↑abs x) ^ 2) = x.re / ↑abs x
    field_simp [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs,
      _root_.abs_of_neg (not_le.1 h₁), *]
#align complex.cos_arg Complex.cos_arg

@[simp]
theorem abs_mul_exp_arg_mul_I (x : ℂ) : ↑(abs x) * exp (arg x * I) = x := by
  rcases eq_or_ne x 0 with (rfl | hx)
  -- ⊢ ↑(↑abs 0) * exp (↑(arg 0) * I) = 0
  · simp
    -- 🎉 no goals
  · have : abs x ≠ 0 := abs.ne_zero hx
    -- ⊢ ↑(↑abs x) * exp (↑(arg x) * I) = x
    ext <;> field_simp [sin_arg, cos_arg hx, this, mul_comm (abs x)]
    -- ⊢ (↑(↑abs x) * exp (↑(arg x) * I)).re = x.re
            -- 🎉 no goals
            -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.abs_mul_exp_arg_mul_I Complex.abs_mul_exp_arg_mul_I

@[simp]
theorem abs_mul_cos_add_sin_mul_I (x : ℂ) : (abs x * (cos (arg x) + sin (arg x) * I) : ℂ) = x := by
  rw [← exp_mul_I, abs_mul_exp_arg_mul_I]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.abs_mul_cos_add_sin_mul_I Complex.abs_mul_cos_add_sin_mul_I

theorem abs_eq_one_iff (z : ℂ) : abs z = 1 ↔ ∃ θ : ℝ, exp (θ * I) = z := by
  refine' ⟨fun hz => ⟨arg z, _⟩, _⟩
  -- ⊢ exp (↑(arg z) * I) = z
  · calc
      exp (arg z * I) = abs z * exp (arg z * I) := by rw [hz, ofReal_one, one_mul]
      _ = z := abs_mul_exp_arg_mul_I z

  · rintro ⟨θ, rfl⟩
    -- ⊢ ↑abs (exp (↑θ * I)) = 1
    exact Complex.abs_exp_ofReal_mul_I θ
    -- 🎉 no goals
#align complex.abs_eq_one_iff Complex.abs_eq_one_iff

@[simp]
theorem range_exp_mul_I : (Set.range fun x : ℝ => exp (x * I)) = Metric.sphere 0 1 := by
  ext x
  -- ⊢ (x ∈ Set.range fun x => exp (↑x * I)) ↔ x ∈ Metric.sphere 0 1
  simp only [mem_sphere_zero_iff_norm, norm_eq_abs, abs_eq_one_iff, Set.mem_range]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.range_exp_mul_I Complex.range_exp_mul_I

theorem arg_mul_cos_add_sin_mul_I {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : θ ∈ Set.Ioc (-π) π) :
    arg (r * (cos θ + sin θ * I)) = θ := by
  simp only [arg, map_mul, abs_cos_add_sin_mul_I, abs_of_nonneg hr.le, mul_one]
  -- ⊢ (if 0 ≤ (↑r * (cos ↑θ + sin ↑θ * I)).re then arcsin ((↑r * (cos ↑θ + sin ↑θ  …
  simp only [ofReal_mul_re, ofReal_mul_im, neg_im, ← ofReal_cos, ← ofReal_sin, ←
    mk_eq_add_mul_I, neg_div, mul_div_cancel_left _ hr.ne', mul_nonneg_iff_right_nonneg_of_pos hr]
  by_cases h₁ : θ ∈ Set.Icc (-(π / 2)) (π / 2)
  -- ⊢ (if 0 ≤ Real.cos θ then arcsin (Real.sin θ) else if 0 ≤ Real.sin θ then arcs …
  · rw [if_pos]
    -- ⊢ arcsin (Real.sin θ) = θ
    exacts [Real.arcsin_sin' h₁, Real.cos_nonneg_of_mem_Icc h₁]
    -- 🎉 no goals
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at h₁
    -- ⊢ (if 0 ≤ Real.cos θ then arcsin (Real.sin θ) else if 0 ≤ Real.sin θ then arcs …
    cases' h₁ with h₁ h₁
    -- ⊢ (if 0 ≤ Real.cos θ then arcsin (Real.sin θ) else if 0 ≤ Real.sin θ then arcs …
    · replace hθ := hθ.1
      -- ⊢ (if 0 ≤ Real.cos θ then arcsin (Real.sin θ) else if 0 ≤ Real.sin θ then arcs …
      have hcos : Real.cos θ < 0 := by
        rw [← neg_pos, ← Real.cos_add_pi]
        refine' Real.cos_pos_of_mem_Ioo ⟨_, _⟩ <;> linarith
      have hsin : Real.sin θ < 0 := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) hθ
      -- ⊢ (if 0 ≤ Real.cos θ then arcsin (Real.sin θ) else if 0 ≤ Real.sin θ then arcs …
      rw [if_neg, if_neg, ← Real.sin_add_pi, Real.arcsin_sin, add_sub_cancel] <;> [linarith;
        linarith; exact hsin.not_le; exact hcos.not_le]
    · replace hθ := hθ.2
      -- ⊢ (if 0 ≤ Real.cos θ then arcsin (Real.sin θ) else if 0 ≤ Real.sin θ then arcs …
      have hcos : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt h₁ (by linarith)
      -- ⊢ (if 0 ≤ Real.cos θ then arcsin (Real.sin θ) else if 0 ≤ Real.sin θ then arcs …
      have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨by linarith, hθ⟩
      -- ⊢ (if 0 ≤ Real.cos θ then arcsin (Real.sin θ) else if 0 ≤ Real.sin θ then arcs …
      rw [if_neg, if_pos, ← Real.sin_sub_pi, Real.arcsin_sin, sub_add_cancel] <;> [linarith;
        linarith; exact hsin; exact hcos.not_le]
set_option linter.uppercaseLean3 false in
#align complex.arg_mul_cos_add_sin_mul_I Complex.arg_mul_cos_add_sin_mul_I

theorem arg_cos_add_sin_mul_I {θ : ℝ} (hθ : θ ∈ Set.Ioc (-π) π) : arg (cos θ + sin θ * I) = θ := by
  rw [← one_mul (_ + _), ← ofReal_one, arg_mul_cos_add_sin_mul_I zero_lt_one hθ]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.arg_cos_add_sin_mul_I Complex.arg_cos_add_sin_mul_I

@[simp]
theorem arg_zero : arg 0 = 0 := by simp [arg, le_refl]
                                   -- 🎉 no goals
#align complex.arg_zero Complex.arg_zero

theorem ext_abs_arg {x y : ℂ} (h₁ : abs x = abs y) (h₂ : x.arg = y.arg) : x = y := by
  rw [← abs_mul_exp_arg_mul_I x, ← abs_mul_exp_arg_mul_I y, h₁, h₂]
  -- 🎉 no goals
#align complex.ext_abs_arg Complex.ext_abs_arg

theorem ext_abs_arg_iff {x y : ℂ} : x = y ↔ abs x = abs y ∧ arg x = arg y :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, and_imp.2 ext_abs_arg⟩
#align complex.ext_abs_arg_iff Complex.ext_abs_arg_iff

theorem arg_mem_Ioc (z : ℂ) : arg z ∈ Set.Ioc (-π) π := by
  have hπ : 0 < π := Real.pi_pos
  -- ⊢ arg z ∈ Set.Ioc (-π) π
  rcases eq_or_ne z 0 with (rfl | hz); simp [hπ, hπ.le]
  -- ⊢ arg 0 ∈ Set.Ioc (-π) π
                                       -- ⊢ arg z ∈ Set.Ioc (-π) π
  rcases existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos (arg z) (-π) with ⟨N, hN, -⟩
  -- ⊢ arg z ∈ Set.Ioc (-π) π
  rw [two_mul, neg_add_cancel_left, ← two_mul, zsmul_eq_mul] at hN
  -- ⊢ arg z ∈ Set.Ioc (-π) π
  rw [← abs_mul_cos_add_sin_mul_I z, ← cos_add_int_mul_two_pi _ N, ← sin_add_int_mul_two_pi _ N]
  -- ⊢ arg (↑(↑abs z) * (cos (↑(arg z) + ↑N * (2 * ↑π)) + sin (↑(arg z) + ↑N * (2 * …
  simp only [← ofReal_one, ← ofReal_bit0, ← ofReal_mul, ← ofReal_add, ofReal_int_cast]
  -- ⊢ arg (↑(↑abs z) * (cos (↑(arg z) + ↑N * (2 * ↑π)) + sin (↑(arg z) + ↑N * (2 * …
  have := arg_mul_cos_add_sin_mul_I (abs.pos hz) hN
  -- ⊢ arg (↑(↑abs z) * (cos (↑(arg z) + ↑N * (2 * ↑π)) + sin (↑(arg z) + ↑N * (2 * …
  push_cast at this
  -- ⊢ arg (↑(↑abs z) * (cos (↑(arg z) + ↑N * (2 * ↑π)) + sin (↑(arg z) + ↑N * (2 * …
  rwa [this]
  -- 🎉 no goals
#align complex.arg_mem_Ioc Complex.arg_mem_Ioc

@[simp]
theorem range_arg : Set.range arg = Set.Ioc (-π) π :=
  (Set.range_subset_iff.2 arg_mem_Ioc).antisymm fun _ hx => ⟨_, arg_cos_add_sin_mul_I hx⟩
#align complex.range_arg Complex.range_arg

theorem arg_le_pi (x : ℂ) : arg x ≤ π :=
  (arg_mem_Ioc x).2
#align complex.arg_le_pi Complex.arg_le_pi

theorem neg_pi_lt_arg (x : ℂ) : -π < arg x :=
  (arg_mem_Ioc x).1
#align complex.neg_pi_lt_arg Complex.neg_pi_lt_arg

theorem abs_arg_le_pi (z : ℂ) : |arg z| ≤ π :=
  abs_le.2 ⟨(neg_pi_lt_arg z).le, arg_le_pi z⟩
#align complex.abs_arg_le_pi Complex.abs_arg_le_pi

@[simp]
theorem arg_nonneg_iff {z : ℂ} : 0 ≤ arg z ↔ 0 ≤ z.im := by
  rcases eq_or_ne z 0 with (rfl | h₀); · simp
  -- ⊢ 0 ≤ arg 0 ↔ 0 ≤ 0.im
                                         -- 🎉 no goals
  calc
    0 ≤ arg z ↔ 0 ≤ Real.sin (arg z) :=
      ⟨fun h => Real.sin_nonneg_of_mem_Icc ⟨h, arg_le_pi z⟩, by
        contrapose!
        intro h
        exact Real.sin_neg_of_neg_of_neg_pi_lt h (neg_pi_lt_arg _)⟩
    _ ↔ _ := by rw [sin_arg, le_div_iff (abs.pos h₀), zero_mul]

#align complex.arg_nonneg_iff Complex.arg_nonneg_iff

@[simp]
theorem arg_neg_iff {z : ℂ} : arg z < 0 ↔ z.im < 0 :=
  lt_iff_lt_of_le_iff_le arg_nonneg_iff
#align complex.arg_neg_iff Complex.arg_neg_iff

theorem arg_real_mul (x : ℂ) {r : ℝ} (hr : 0 < r) : arg (r * x) = arg x := by
  rcases eq_or_ne x 0 with (rfl | hx); · rw [mul_zero]
  -- ⊢ arg (↑r * 0) = arg 0
                                         -- 🎉 no goals
  conv_lhs =>
    rw [← abs_mul_cos_add_sin_mul_I x, ← mul_assoc, ← ofReal_mul,
      arg_mul_cos_add_sin_mul_I (mul_pos hr (abs.pos hx)) x.arg_mem_Ioc]
#align complex.arg_real_mul Complex.arg_real_mul

theorem arg_eq_arg_iff {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    arg x = arg y ↔ (abs y / abs x : ℂ) * x = y := by
  simp only [ext_abs_arg_iff, map_mul, map_div₀, abs_ofReal, abs_abs,
    div_mul_cancel _ (abs.ne_zero hx), eq_self_iff_true, true_and_iff]
  rw [← ofReal_div, arg_real_mul]
  -- ⊢ 0 < ↑abs y / ↑abs x
  exact div_pos (abs.pos hy) (abs.pos hx)
  -- 🎉 no goals
#align complex.arg_eq_arg_iff Complex.arg_eq_arg_iff

@[simp]
theorem arg_one : arg 1 = 0 := by simp [arg, zero_le_one]
                                  -- 🎉 no goals
#align complex.arg_one Complex.arg_one

@[simp]
theorem arg_neg_one : arg (-1) = π := by simp [arg, le_refl, not_le.2 (zero_lt_one' ℝ)]
                                         -- 🎉 no goals
#align complex.arg_neg_one Complex.arg_neg_one

@[simp]
theorem arg_I : arg I = π / 2 := by simp [arg, le_refl]
                                    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.arg_I Complex.arg_I

@[simp]
theorem arg_neg_I : arg (-I) = -(π / 2) := by simp [arg, le_refl]
                                              -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.arg_neg_I Complex.arg_neg_I

@[simp]
theorem tan_arg (x : ℂ) : Real.tan (arg x) = x.im / x.re := by
  by_cases h : x = 0
  -- ⊢ Real.tan (arg x) = x.im / x.re
  · simp only [h, zero_div, Complex.zero_im, Complex.arg_zero, Real.tan_zero, Complex.zero_re]
    -- 🎉 no goals
  rw [Real.tan_eq_sin_div_cos, sin_arg, cos_arg h, div_div_div_cancel_right _ (abs.ne_zero h)]
  -- 🎉 no goals
#align complex.tan_arg Complex.tan_arg

theorem arg_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) : arg x = 0 := by simp [arg, hx]
                                                                    -- 🎉 no goals
#align complex.arg_of_real_of_nonneg Complex.arg_ofReal_of_nonneg

theorem arg_eq_zero_iff {z : ℂ} : arg z = 0 ↔ 0 ≤ z.re ∧ z.im = 0 := by
  refine' ⟨fun h => _, _⟩
  -- ⊢ 0 ≤ z.re ∧ z.im = 0
  · rw [← abs_mul_cos_add_sin_mul_I z, h]
    -- ⊢ 0 ≤ (↑(↑abs z) * (cos ↑0 + sin ↑0 * I)).re ∧ (↑(↑abs z) * (cos ↑0 + sin ↑0 * …
    simp [abs.nonneg]
    -- 🎉 no goals
  · cases' z with x y
    -- ⊢ 0 ≤ { re := x, im := y }.re ∧ { re := x, im := y }.im = 0 → arg { re := x, i …
    rintro ⟨h, rfl : y = 0⟩
    -- ⊢ arg { re := x, im := 0 } = 0
    exact arg_ofReal_of_nonneg h
    -- 🎉 no goals
#align complex.arg_eq_zero_iff Complex.arg_eq_zero_iff

theorem arg_eq_pi_iff {z : ℂ} : arg z = π ↔ z.re < 0 ∧ z.im = 0 := by
  by_cases h₀ : z = 0; simp [h₀, lt_irrefl, Real.pi_ne_zero.symm]
  -- ⊢ arg z = π ↔ z.re < 0 ∧ z.im = 0
                       -- ⊢ arg z = π ↔ z.re < 0 ∧ z.im = 0
  constructor
  -- ⊢ arg z = π → z.re < 0 ∧ z.im = 0
  · intro h
    -- ⊢ z.re < 0 ∧ z.im = 0
    rw [← abs_mul_cos_add_sin_mul_I z, h]
    -- ⊢ (↑(↑abs z) * (cos ↑π + sin ↑π * I)).re < 0 ∧ (↑(↑abs z) * (cos ↑π + sin ↑π * …
    simp [h₀]
    -- 🎉 no goals
  · cases' z with x y
    -- ⊢ { re := x, im := y }.re < 0 ∧ { re := x, im := y }.im = 0 → arg { re := x, i …
    rintro ⟨h : x < 0, rfl : y = 0⟩
    -- ⊢ arg { re := x, im := 0 } = π
    rw [← arg_neg_one, ← arg_real_mul (-1) (neg_pos.2 h)]
    -- ⊢ arg { re := x, im := 0 } = arg (↑(-x) * -1)
    simp [← ofReal_def]
    -- 🎉 no goals
#align complex.arg_eq_pi_iff Complex.arg_eq_pi_iff

theorem arg_lt_pi_iff {z : ℂ} : arg z < π ↔ 0 ≤ z.re ∨ z.im ≠ 0 := by
  rw [(arg_le_pi z).lt_iff_ne, not_iff_comm, not_or, not_le, Classical.not_not, arg_eq_pi_iff]
  -- 🎉 no goals
#align complex.arg_lt_pi_iff Complex.arg_lt_pi_iff

theorem arg_ofReal_of_neg {x : ℝ} (hx : x < 0) : arg x = π :=
  arg_eq_pi_iff.2 ⟨hx, rfl⟩
#align complex.arg_of_real_of_neg Complex.arg_ofReal_of_neg

theorem arg_eq_pi_div_two_iff {z : ℂ} : arg z = π / 2 ↔ z.re = 0 ∧ 0 < z.im := by
  by_cases h₀ : z = 0; · simp [h₀, lt_irrefl, Real.pi_div_two_pos.ne]
  -- ⊢ arg z = π / 2 ↔ z.re = 0 ∧ 0 < z.im
                         -- 🎉 no goals
  constructor
  -- ⊢ arg z = π / 2 → z.re = 0 ∧ 0 < z.im
  · intro h
    -- ⊢ z.re = 0 ∧ 0 < z.im
    rw [← abs_mul_cos_add_sin_mul_I z, h]
    -- ⊢ (↑(↑abs z) * (cos ↑(π / 2) + sin ↑(π / 2) * I)).re = 0 ∧ 0 < (↑(↑abs z) * (c …
    simp [h₀]
    -- 🎉 no goals
  · cases' z with x y
    -- ⊢ { re := x, im := y }.re = 0 ∧ 0 < { re := x, im := y }.im → arg { re := x, i …
    rintro ⟨rfl : x = 0, hy : 0 < y⟩
    -- ⊢ arg { re := 0, im := y } = π / 2
    rw [← arg_I, ← arg_real_mul I hy, ofReal_mul', I_re, I_im, mul_zero, mul_one]
    -- 🎉 no goals
#align complex.arg_eq_pi_div_two_iff Complex.arg_eq_pi_div_two_iff

theorem arg_eq_neg_pi_div_two_iff {z : ℂ} : arg z = -(π / 2) ↔ z.re = 0 ∧ z.im < 0 := by
  by_cases h₀ : z = 0; · simp [h₀, lt_irrefl, Real.pi_ne_zero]
  -- ⊢ arg z = -(π / 2) ↔ z.re = 0 ∧ z.im < 0
                         -- 🎉 no goals
  constructor
  -- ⊢ arg z = -(π / 2) → z.re = 0 ∧ z.im < 0
  · intro h
    -- ⊢ z.re = 0 ∧ z.im < 0
    rw [← abs_mul_cos_add_sin_mul_I z, h]
    -- ⊢ (↑(↑abs z) * (cos ↑(-(π / 2)) + sin ↑(-(π / 2)) * I)).re = 0 ∧ (↑(↑abs z) *  …
    simp [h₀]
    -- 🎉 no goals
  · cases' z with x y
    -- ⊢ { re := x, im := y }.re = 0 ∧ { re := x, im := y }.im < 0 → arg { re := x, i …
    rintro ⟨rfl : x = 0, hy : y < 0⟩
    -- ⊢ arg { re := 0, im := y } = -(π / 2)
    rw [← arg_neg_I, ← arg_real_mul (-I) (neg_pos.2 hy), mk_eq_add_mul_I]
    -- ⊢ arg (↑0 + ↑y * I) = arg (↑(-y) * -I)
    simp
    -- 🎉 no goals
#align complex.arg_eq_neg_pi_div_two_iff Complex.arg_eq_neg_pi_div_two_iff

theorem arg_of_re_nonneg {x : ℂ} (hx : 0 ≤ x.re) : arg x = Real.arcsin (x.im / abs x) :=
  if_pos hx
#align complex.arg_of_re_nonneg Complex.arg_of_re_nonneg

theorem arg_of_re_neg_of_im_nonneg {x : ℂ} (hx_re : x.re < 0) (hx_im : 0 ≤ x.im) :
    arg x = Real.arcsin ((-x).im / abs x) + π := by
  simp only [arg, hx_re.not_le, hx_im, if_true, if_false]
  -- 🎉 no goals
#align complex.arg_of_re_neg_of_im_nonneg Complex.arg_of_re_neg_of_im_nonneg

theorem arg_of_re_neg_of_im_neg {x : ℂ} (hx_re : x.re < 0) (hx_im : x.im < 0) :
    arg x = Real.arcsin ((-x).im / abs x) - π := by
  simp only [arg, hx_re.not_le, hx_im.not_le, if_false]
  -- 🎉 no goals
#align complex.arg_of_re_neg_of_im_neg Complex.arg_of_re_neg_of_im_neg

theorem arg_of_im_nonneg_of_ne_zero {z : ℂ} (h₁ : 0 ≤ z.im) (h₂ : z ≠ 0) :
    arg z = Real.arccos (z.re / abs z) := by
  rw [← cos_arg h₂, Real.arccos_cos (arg_nonneg_iff.2 h₁) (arg_le_pi _)]
  -- 🎉 no goals
#align complex.arg_of_im_nonneg_of_ne_zero Complex.arg_of_im_nonneg_of_ne_zero

theorem arg_of_im_pos {z : ℂ} (hz : 0 < z.im) : arg z = Real.arccos (z.re / abs z) :=
  arg_of_im_nonneg_of_ne_zero hz.le fun h => hz.ne' <| h.symm ▸ rfl
#align complex.arg_of_im_pos Complex.arg_of_im_pos

theorem arg_of_im_neg {z : ℂ} (hz : z.im < 0) : arg z = -Real.arccos (z.re / abs z) := by
  have h₀ : z ≠ 0 := mt (congr_arg im) hz.ne
  -- ⊢ arg z = -arccos (z.re / ↑abs z)
  rw [← cos_arg h₀, ← Real.cos_neg, Real.arccos_cos, neg_neg]
  -- ⊢ 0 ≤ -arg z
  exacts [neg_nonneg.2 (arg_neg_iff.2 hz).le, neg_le.2 (neg_pi_lt_arg z).le]
  -- 🎉 no goals
#align complex.arg_of_im_neg Complex.arg_of_im_neg

theorem arg_conj (x : ℂ) : arg (conj x) = if arg x = π then π else -arg x := by
  simp_rw [arg_eq_pi_iff, arg, neg_im, conj_im, conj_re, abs_conj, neg_div, neg_neg,
    Real.arcsin_neg]
  rcases lt_trichotomy x.re 0 with (hr | hr | hr) <;>
    rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hr, hr.not_le, hi.le, hi.ne, not_le.2 hi, add_comm]
    -- 🎉 no goals
  · simp [hr, hr.not_le, hi]
    -- 🎉 no goals
  · simp [hr, hr.not_le, hi.ne.symm, hi.le, not_le.2 hi, sub_eq_neg_add]
    -- 🎉 no goals
  · simp [hr]
    -- 🎉 no goals
  · simp [hr]
    -- 🎉 no goals
  · simp [hr]
    -- 🎉 no goals
  · simp [hr, hr.le, hi.ne]
    -- 🎉 no goals
  · simp [hr, hr.le, hr.le.not_lt]
    -- 🎉 no goals
  · simp [hr, hr.le, hr.le.not_lt]
    -- 🎉 no goals
#align complex.arg_conj Complex.arg_conj

theorem arg_inv (x : ℂ) : arg x⁻¹ = if arg x = π then π else -arg x := by
  rw [← arg_conj, inv_def, mul_comm]
  -- ⊢ arg (↑(↑normSq x)⁻¹ * ↑(starRingEnd ℂ) x) = arg (↑(starRingEnd ℂ) x)
  by_cases hx : x = 0
  -- ⊢ arg (↑(↑normSq x)⁻¹ * ↑(starRingEnd ℂ) x) = arg (↑(starRingEnd ℂ) x)
  · simp [hx]
    -- 🎉 no goals
  · exact arg_real_mul (conj x) (by simp [hx])
    -- 🎉 no goals
#align complex.arg_inv Complex.arg_inv

theorem arg_le_pi_div_two_iff {z : ℂ} : arg z ≤ π / 2 ↔ 0 ≤ re z ∨ im z < 0 := by
  cases' le_or_lt 0 (re z) with hre hre
  -- ⊢ arg z ≤ π / 2 ↔ 0 ≤ z.re ∨ z.im < 0
  · simp only [hre, arg_of_re_nonneg hre, Real.arcsin_le_pi_div_two, true_or_iff]
    -- 🎉 no goals
  simp only [hre.not_le, false_or_iff]
  -- ⊢ arg z ≤ π / 2 ↔ z.im < 0
  cases' le_or_lt 0 (im z) with him him
  -- ⊢ arg z ≤ π / 2 ↔ z.im < 0
  · simp only [him.not_lt]
    -- ⊢ arg z ≤ π / 2 ↔ False
    rw [iff_false_iff, not_le, arg_of_re_neg_of_im_nonneg hre him, ← sub_lt_iff_lt_add, half_sub,
      Real.neg_pi_div_two_lt_arcsin, neg_im, neg_div, neg_lt_neg_iff, div_lt_one, ←
      _root_.abs_of_nonneg him, abs_im_lt_abs]
    exacts [hre.ne, abs.pos <| ne_of_apply_ne re hre.ne]
    -- 🎉 no goals
  · simp only [him]
    -- ⊢ arg z ≤ π / 2 ↔ True
    rw [iff_true_iff, arg_of_re_neg_of_im_neg hre him]
    -- ⊢ arcsin ((-z).im / ↑abs z) - π ≤ π / 2
    exact (sub_le_self _ Real.pi_pos.le).trans (Real.arcsin_le_pi_div_two _)
    -- 🎉 no goals
#align complex.arg_le_pi_div_two_iff Complex.arg_le_pi_div_two_iff

theorem neg_pi_div_two_le_arg_iff {z : ℂ} : -(π / 2) ≤ arg z ↔ 0 ≤ re z ∨ 0 ≤ im z := by
  cases' le_or_lt 0 (re z) with hre hre
  -- ⊢ -(π / 2) ≤ arg z ↔ 0 ≤ z.re ∨ 0 ≤ z.im
  · simp only [hre, arg_of_re_nonneg hre, Real.neg_pi_div_two_le_arcsin, true_or_iff]
    -- 🎉 no goals
  simp only [hre.not_le, false_or_iff]
  -- ⊢ -(π / 2) ≤ arg z ↔ 0 ≤ z.im
  cases' le_or_lt 0 (im z) with him him
  -- ⊢ -(π / 2) ≤ arg z ↔ 0 ≤ z.im
  · simp only [him]
    -- ⊢ -(π / 2) ≤ arg z ↔ True
    rw [iff_true_iff, arg_of_re_neg_of_im_nonneg hre him]
    -- ⊢ -(π / 2) ≤ arcsin ((-z).im / ↑abs z) + π
    exact (Real.neg_pi_div_two_le_arcsin _).trans (le_add_of_nonneg_right Real.pi_pos.le)
    -- 🎉 no goals
  · simp only [him.not_le]
    -- ⊢ -(π / 2) ≤ arg z ↔ False
    rw [iff_false_iff, not_le, arg_of_re_neg_of_im_neg hre him, sub_lt_iff_lt_add', ←
      sub_eq_add_neg, sub_half, Real.arcsin_lt_pi_div_two, div_lt_one, neg_im, ← abs_of_neg him,
      abs_im_lt_abs]
    exacts [hre.ne, abs.pos <| ne_of_apply_ne re hre.ne]
    -- 🎉 no goals
#align complex.neg_pi_div_two_le_arg_iff Complex.neg_pi_div_two_le_arg_iff

@[simp]
theorem abs_arg_le_pi_div_two_iff {z : ℂ} : |arg z| ≤ π / 2 ↔ 0 ≤ re z := by
  rw [abs_le, arg_le_pi_div_two_iff, neg_pi_div_two_le_arg_iff, ← or_and_left, ← not_le,
    and_not_self_iff, or_false_iff]
#align complex.abs_arg_le_pi_div_two_iff Complex.abs_arg_le_pi_div_two_iff

@[simp]
theorem arg_conj_coe_angle (x : ℂ) : (arg (conj x) : Real.Angle) = -arg x := by
  by_cases h : arg x = π <;> simp [arg_conj, h]
  -- ⊢ ↑(arg (↑(starRingEnd ℂ) x)) = -↑(arg x)
                             -- 🎉 no goals
                             -- 🎉 no goals
#align complex.arg_conj_coe_angle Complex.arg_conj_coe_angle

@[simp]
theorem arg_inv_coe_angle (x : ℂ) : (arg x⁻¹ : Real.Angle) = -arg x := by
  by_cases h : arg x = π <;> simp [arg_inv, h]
  -- ⊢ ↑(arg x⁻¹) = -↑(arg x)
                             -- 🎉 no goals
                             -- 🎉 no goals
#align complex.arg_inv_coe_angle Complex.arg_inv_coe_angle

theorem arg_neg_eq_arg_sub_pi_of_im_pos {x : ℂ} (hi : 0 < x.im) : arg (-x) = arg x - π := by
  rw [arg_of_im_pos hi, arg_of_im_neg (show (-x).im < 0 from Left.neg_neg_iff.2 hi)]
  -- ⊢ -arccos ((-x).re / ↑abs (-x)) = arccos (x.re / ↑abs x) - π
  simp [neg_div, Real.arccos_neg]
  -- 🎉 no goals
#align complex.arg_neg_eq_arg_sub_pi_of_im_pos Complex.arg_neg_eq_arg_sub_pi_of_im_pos

theorem arg_neg_eq_arg_add_pi_of_im_neg {x : ℂ} (hi : x.im < 0) : arg (-x) = arg x + π := by
  rw [arg_of_im_neg hi, arg_of_im_pos (show 0 < (-x).im from Left.neg_pos_iff.2 hi)]
  -- ⊢ arccos ((-x).re / ↑abs (-x)) = -arccos (x.re / ↑abs x) + π
  simp [neg_div, Real.arccos_neg, add_comm, ← sub_eq_add_neg]
  -- 🎉 no goals
#align complex.arg_neg_eq_arg_add_pi_of_im_neg Complex.arg_neg_eq_arg_add_pi_of_im_neg

theorem arg_neg_eq_arg_sub_pi_iff {x : ℂ} :
    arg (-x) = arg x - π ↔ 0 < x.im ∨ x.im = 0 ∧ x.re < 0 := by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hi, hi.ne, hi.not_lt, arg_neg_eq_arg_add_pi_of_im_neg, sub_eq_add_neg, ←
      add_eq_zero_iff_eq_neg, Real.pi_ne_zero]
  · rw [(ext rfl hi : x = x.re)]
    -- ⊢ arg (-↑x.re) = arg ↑x.re - π ↔ 0 < (↑x.re).im ∨ (↑x.re).im = 0 ∧ (↑x.re).re  …
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_ofReal_of_neg hr, ← ofReal_neg, arg_ofReal_of_nonneg (Left.neg_pos_iff.2 hr).le]
      -- ⊢ 0 = π - π ↔ 0 < (↑x.re).im ∨ (↑x.re).im = 0 ∧ (↑x.re).re < 0
      simp [hr]
      -- 🎉 no goals
    · simp [hr, hi, Real.pi_ne_zero]
      -- 🎉 no goals
    · rw [arg_ofReal_of_nonneg hr.le, ← ofReal_neg, arg_ofReal_of_neg (Left.neg_neg_iff.2 hr)]
      -- ⊢ π = 0 - π ↔ 0 < (↑x.re).im ∨ (↑x.re).im = 0 ∧ (↑x.re).re < 0
      simp [hr.not_lt, ← add_eq_zero_iff_eq_neg, Real.pi_ne_zero]
      -- 🎉 no goals
  · simp [hi, arg_neg_eq_arg_sub_pi_of_im_pos]
    -- 🎉 no goals
#align complex.arg_neg_eq_arg_sub_pi_iff Complex.arg_neg_eq_arg_sub_pi_iff

theorem arg_neg_eq_arg_add_pi_iff {x : ℂ} :
    arg (-x) = arg x + π ↔ x.im < 0 ∨ x.im = 0 ∧ 0 < x.re := by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hi, arg_neg_eq_arg_add_pi_of_im_neg]
    -- 🎉 no goals
  · rw [(ext rfl hi : x = x.re)]
    -- ⊢ arg (-↑x.re) = arg ↑x.re + π ↔ (↑x.re).im < 0 ∨ (↑x.re).im = 0 ∧ 0 < (↑x.re) …
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_ofReal_of_neg hr, ← ofReal_neg, arg_ofReal_of_nonneg (Left.neg_pos_iff.2 hr).le]
      -- ⊢ 0 = π + π ↔ (↑x.re).im < 0 ∨ (↑x.re).im = 0 ∧ 0 < (↑x.re).re
      simp [hr.not_lt, ← two_mul, Real.pi_ne_zero]
      -- 🎉 no goals
    · simp [hr, hi, Real.pi_ne_zero.symm]
      -- 🎉 no goals
    · rw [arg_ofReal_of_nonneg hr.le, ← ofReal_neg, arg_ofReal_of_neg (Left.neg_neg_iff.2 hr)]
      -- ⊢ π = 0 + π ↔ (↑x.re).im < 0 ∨ (↑x.re).im = 0 ∧ 0 < (↑x.re).re
      simp [hr]
      -- 🎉 no goals
  · simp [hi, hi.ne.symm, hi.not_lt, arg_neg_eq_arg_sub_pi_of_im_pos, sub_eq_add_neg, ←
      add_eq_zero_iff_neg_eq, Real.pi_ne_zero]
#align complex.arg_neg_eq_arg_add_pi_iff Complex.arg_neg_eq_arg_add_pi_iff

theorem arg_neg_coe_angle {x : ℂ} (hx : x ≠ 0) : (arg (-x) : Real.Angle) = arg x + π := by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · rw [arg_neg_eq_arg_add_pi_of_im_neg hi, Real.Angle.coe_add]
    -- 🎉 no goals
  · rw [(ext rfl hi : x = x.re)]
    -- ⊢ ↑(arg (-↑x.re)) = ↑(arg ↑x.re) + ↑π
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_ofReal_of_neg hr, ← ofReal_neg, arg_ofReal_of_nonneg (Left.neg_pos_iff.2 hr).le, ←
        Real.Angle.coe_add, ← two_mul, Real.Angle.coe_two_pi, Real.Angle.coe_zero]
    · exact False.elim (hx (ext hr hi))
      -- 🎉 no goals
    · rw [arg_ofReal_of_nonneg hr.le, ← ofReal_neg, arg_ofReal_of_neg (Left.neg_neg_iff.2 hr),
        Real.Angle.coe_zero, zero_add]
  · rw [arg_neg_eq_arg_sub_pi_of_im_pos hi, Real.Angle.coe_sub, Real.Angle.sub_coe_pi_eq_add_coe_pi]
    -- 🎉 no goals
#align complex.arg_neg_coe_angle Complex.arg_neg_coe_angle

theorem arg_mul_cos_add_sin_mul_I_eq_toIocMod {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    arg (r * (cos θ + sin θ * I)) = toIocMod Real.two_pi_pos (-π) θ := by
  have hi : toIocMod Real.two_pi_pos (-π) θ ∈ Set.Ioc (-π) π := by
    convert toIocMod_mem_Ioc _ _ θ
    ring
  convert arg_mul_cos_add_sin_mul_I hr hi using 3
  -- ⊢ cos ↑θ + sin ↑θ * I = cos ↑(toIocMod two_pi_pos (-π) θ) + sin ↑(toIocMod two …
  simp [toIocMod, cos_sub_int_mul_two_pi, sin_sub_int_mul_two_pi]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.arg_mul_cos_add_sin_mul_I_eq_to_Ioc_mod Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod

theorem arg_cos_add_sin_mul_I_eq_toIocMod (θ : ℝ) :
    arg (cos θ + sin θ * I) = toIocMod Real.two_pi_pos (-π) θ := by
  rw [← one_mul (_ + _), ← ofReal_one, arg_mul_cos_add_sin_mul_I_eq_toIocMod zero_lt_one]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.arg_cos_add_sin_mul_I_eq_to_Ioc_mod Complex.arg_cos_add_sin_mul_I_eq_toIocMod

theorem arg_mul_cos_add_sin_mul_I_sub {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    arg (r * (cos θ + sin θ * I)) - θ = 2 * π * ⌊(π - θ) / (2 * π)⌋ := by
  rw [arg_mul_cos_add_sin_mul_I_eq_toIocMod hr, toIocMod_sub_self, toIocDiv_eq_neg_floor,
    zsmul_eq_mul]
  ring_nf
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.arg_mul_cos_add_sin_mul_I_sub Complex.arg_mul_cos_add_sin_mul_I_sub

theorem arg_cos_add_sin_mul_I_sub (θ : ℝ) :
    arg (cos θ + sin θ * I) - θ = 2 * π * ⌊(π - θ) / (2 * π)⌋ := by
  rw [← one_mul (_ + _), ← ofReal_one, arg_mul_cos_add_sin_mul_I_sub zero_lt_one]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.arg_cos_add_sin_mul_I_sub Complex.arg_cos_add_sin_mul_I_sub

theorem arg_mul_cos_add_sin_mul_I_coe_angle {r : ℝ} (hr : 0 < r) (θ : Real.Angle) :
    (arg (r * (Real.Angle.cos θ + Real.Angle.sin θ * I)) : Real.Angle) = θ := by
  induction' θ using Real.Angle.induction_on with θ
  -- ⊢ ↑(arg (↑r * (↑(Angle.cos ↑θ) + ↑(Angle.sin ↑θ) * I))) = ↑θ
  rw [Real.Angle.cos_coe, Real.Angle.sin_coe, Real.Angle.angle_eq_iff_two_pi_dvd_sub]
  -- ⊢ ∃ k, arg (↑r * (↑(Real.cos θ) + ↑(Real.sin θ) * I)) - θ = 2 * π * ↑k
  use ⌊(π - θ) / (2 * π)⌋
  -- ⊢ arg (↑r * (↑(Real.cos θ) + ↑(Real.sin θ) * I)) - θ = 2 * π * ↑⌊(π - θ) / (2  …
  exact_mod_cast arg_mul_cos_add_sin_mul_I_sub hr θ
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.arg_mul_cos_add_sin_mul_I_coe_angle Complex.arg_mul_cos_add_sin_mul_I_coe_angle

theorem arg_cos_add_sin_mul_I_coe_angle (θ : Real.Angle) :
    (arg (Real.Angle.cos θ + Real.Angle.sin θ * I) : Real.Angle) = θ := by
  rw [← one_mul (_ + _), ← ofReal_one, arg_mul_cos_add_sin_mul_I_coe_angle zero_lt_one]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.arg_cos_add_sin_mul_I_coe_angle Complex.arg_cos_add_sin_mul_I_coe_angle

theorem arg_mul_coe_angle {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (arg (x * y) : Real.Angle) = arg x + arg y := by
  convert arg_mul_cos_add_sin_mul_I_coe_angle (mul_pos (abs.pos hx) (abs.pos hy))
      (arg x + arg y : Real.Angle) using
    3
  simp_rw [← Real.Angle.coe_add, Real.Angle.sin_coe, Real.Angle.cos_coe, ofReal_cos, ofReal_sin,
    cos_add_sin_I, ofReal_add, add_mul, exp_add, ofReal_mul]
  rw [mul_assoc, mul_comm (exp _), ← mul_assoc (abs y : ℂ), abs_mul_exp_arg_mul_I, mul_comm y, ←
    mul_assoc, abs_mul_exp_arg_mul_I]
#align complex.arg_mul_coe_angle Complex.arg_mul_coe_angle

theorem arg_div_coe_angle {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (arg (x / y) : Real.Angle) = arg x - arg y := by
  rw [div_eq_mul_inv, arg_mul_coe_angle hx (inv_ne_zero hy), arg_inv_coe_angle, sub_eq_add_neg]
  -- 🎉 no goals
#align complex.arg_div_coe_angle Complex.arg_div_coe_angle

@[simp]
theorem arg_coe_angle_toReal_eq_arg (z : ℂ) : (arg z : Real.Angle).toReal = arg z := by
  rw [Real.Angle.toReal_coe_eq_self_iff_mem_Ioc]
  -- ⊢ arg z ∈ Set.Ioc (-π) π
  exact arg_mem_Ioc _
  -- 🎉 no goals
#align complex.arg_coe_angle_to_real_eq_arg Complex.arg_coe_angle_toReal_eq_arg

theorem arg_coe_angle_eq_iff_eq_toReal {z : ℂ} {θ : Real.Angle} :
    (arg z : Real.Angle) = θ ↔ arg z = θ.toReal := by
  rw [← Real.Angle.toReal_inj, arg_coe_angle_toReal_eq_arg]
  -- 🎉 no goals
#align complex.arg_coe_angle_eq_iff_eq_to_real Complex.arg_coe_angle_eq_iff_eq_toReal

@[simp]
theorem arg_coe_angle_eq_iff {x y : ℂ} : (arg x : Real.Angle) = arg y ↔ arg x = arg y := by
  simp_rw [← Real.Angle.toReal_inj, arg_coe_angle_toReal_eq_arg]
  -- 🎉 no goals
#align complex.arg_coe_angle_eq_iff Complex.arg_coe_angle_eq_iff

section Continuity

variable {x z : ℂ}

theorem arg_eq_nhds_of_re_pos (hx : 0 < x.re) : arg =ᶠ[𝓝 x] fun x => Real.arcsin (x.im / abs x) :=
  ((continuous_re.tendsto _).eventually (lt_mem_nhds hx)).mono fun _ hy => arg_of_re_nonneg hy.le
#align complex.arg_eq_nhds_of_re_pos Complex.arg_eq_nhds_of_re_pos

theorem arg_eq_nhds_of_re_neg_of_im_pos (hx_re : x.re < 0) (hx_im : 0 < x.im) :
    arg =ᶠ[𝓝 x] fun x => Real.arcsin ((-x).im / abs x) + π := by
  suffices h_forall_nhds : ∀ᶠ y : ℂ in 𝓝 x, y.re < 0 ∧ 0 < y.im
  -- ⊢ arg =ᶠ[𝓝 x] fun x => arcsin ((-x).im / ↑abs x) + π
  exact h_forall_nhds.mono fun y hy => arg_of_re_neg_of_im_nonneg hy.1 hy.2.le
  -- ⊢ ∀ᶠ (y : ℂ) in 𝓝 x, y.re < 0 ∧ 0 < y.im
  refine' IsOpen.eventually_mem _ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ 0 < x.im)
  -- ⊢ IsOpen fun y => y.re < 0 ∧ 0 < y.im
  exact
    IsOpen.and (isOpen_lt continuous_re continuous_zero) (isOpen_lt continuous_zero continuous_im)
#align complex.arg_eq_nhds_of_re_neg_of_im_pos Complex.arg_eq_nhds_of_re_neg_of_im_pos

theorem arg_eq_nhds_of_re_neg_of_im_neg (hx_re : x.re < 0) (hx_im : x.im < 0) :
    arg =ᶠ[𝓝 x] fun x => Real.arcsin ((-x).im / abs x) - π := by
  suffices h_forall_nhds : ∀ᶠ y : ℂ in 𝓝 x, y.re < 0 ∧ y.im < 0
  -- ⊢ arg =ᶠ[𝓝 x] fun x => arcsin ((-x).im / ↑abs x) - π
  exact h_forall_nhds.mono fun y hy => arg_of_re_neg_of_im_neg hy.1 hy.2
  -- ⊢ ∀ᶠ (y : ℂ) in 𝓝 x, y.re < 0 ∧ y.im < 0
  refine' IsOpen.eventually_mem _ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ x.im < 0)
  -- ⊢ IsOpen fun y => y.re < 0 ∧ y.im < 0
  exact
    IsOpen.and (isOpen_lt continuous_re continuous_zero) (isOpen_lt continuous_im continuous_zero)
#align complex.arg_eq_nhds_of_re_neg_of_im_neg Complex.arg_eq_nhds_of_re_neg_of_im_neg

theorem arg_eq_nhds_of_im_pos (hz : 0 < im z) : arg =ᶠ[𝓝 z] fun x => Real.arccos (x.re / abs x) :=
  ((continuous_im.tendsto _).eventually (lt_mem_nhds hz)).mono fun _ => arg_of_im_pos
#align complex.arg_eq_nhds_of_im_pos Complex.arg_eq_nhds_of_im_pos

theorem arg_eq_nhds_of_im_neg (hz : im z < 0) : arg =ᶠ[𝓝 z] fun x => -Real.arccos (x.re / abs x) :=
  ((continuous_im.tendsto _).eventually (gt_mem_nhds hz)).mono fun _ => arg_of_im_neg
#align complex.arg_eq_nhds_of_im_neg Complex.arg_eq_nhds_of_im_neg

theorem continuousAt_arg (h : 0 < x.re ∨ x.im ≠ 0) : ContinuousAt arg x := by
  have h₀ : abs x ≠ 0 := by
    rw [abs.ne_zero_iff]
    rintro rfl
    simp at h
  rw [← lt_or_lt_iff_ne] at h
  -- ⊢ ContinuousAt arg x
  rcases h with (hx_re | hx_im | hx_im)
  exacts [(Real.continuousAt_arcsin.comp
          (continuous_im.continuousAt.div continuous_abs.continuousAt h₀)).congr
      (arg_eq_nhds_of_re_pos hx_re).symm,
    (Real.continuous_arccos.continuousAt.comp
            (continuous_re.continuousAt.div continuous_abs.continuousAt h₀)).neg.congr
      (arg_eq_nhds_of_im_neg hx_im).symm,
    (Real.continuous_arccos.continuousAt.comp
          (continuous_re.continuousAt.div continuous_abs.continuousAt h₀)).congr
      (arg_eq_nhds_of_im_pos hx_im).symm]
#align complex.continuous_at_arg Complex.continuousAt_arg

theorem tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto arg (𝓝[{ z : ℂ | z.im < 0 }] z) (𝓝 (-π)) := by
  suffices H :
    Tendsto (fun x : ℂ => Real.arcsin ((-x).im / abs x) - π) (𝓝[{ z : ℂ | z.im < 0 }] z) (𝓝 (-π))
  · refine' H.congr' _
    -- ⊢ (fun x => arcsin ((-x).im / ↑abs x) - π) =ᶠ[𝓝[{z | z.im < 0}] z] arg
    have : ∀ᶠ x : ℂ in 𝓝 z, x.re < 0 := continuous_re.tendsto z (gt_mem_nhds hre)
    -- ⊢ (fun x => arcsin ((-x).im / ↑abs x) - π) =ᶠ[𝓝[{z | z.im < 0}] z] arg
    -- Porting note: need to specify the `nhdsWithin` set
    filter_upwards [self_mem_nhdsWithin (s := { z : ℂ | z.im < 0 }),
      mem_nhdsWithin_of_mem_nhds this] with _ him hre
    rw [arg, if_neg hre.not_le, if_neg him.not_le]
    -- 🎉 no goals
  convert (Real.continuousAt_arcsin.comp_continuousWithinAt
          ((continuous_im.continuousAt.comp_continuousWithinAt continuousWithinAt_neg).div
            -- Porting note: added type hint to assist in goal state below
            continuous_abs.continuousWithinAt (s := { z : ℂ | z.im < 0 }) (_ : abs z ≠ 0))
          -- Porting note: specify constant precisely to assist in goal below
          ).sub_const π using 1
  · simp [him]
    -- 🎉 no goals
  · lift z to ℝ using him
    -- ⊢ ↑abs ↑z ≠ 0
    simpa using hre.ne
    -- 🎉 no goals
#align complex.tendsto_arg_nhds_within_im_neg_of_re_neg_of_im_zero
Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero

theorem continuousWithinAt_arg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
    ContinuousWithinAt arg { z : ℂ | 0 ≤ z.im } z := by
  have : arg =ᶠ[𝓝[{ z : ℂ | 0 ≤ z.im }] z] fun x => Real.arcsin ((-x).im / abs x) + π := by
    have : ∀ᶠ x : ℂ in 𝓝 z, x.re < 0 := continuous_re.tendsto z (gt_mem_nhds hre)
    filter_upwards [self_mem_nhdsWithin (s := { z : ℂ | 0 ≤ z.im }),
      mem_nhdsWithin_of_mem_nhds this] with _ him hre
    rw [arg, if_neg hre.not_le, if_pos him]
  refine' ContinuousWithinAt.congr_of_eventuallyEq _ this _
  -- ⊢ ContinuousWithinAt (fun x => arcsin ((-x).im / ↑abs x) + π) {z | 0 ≤ z.im} z
  · refine'
      (Real.continuousAt_arcsin.comp_continuousWithinAt
            ((continuous_im.continuousAt.comp_continuousWithinAt continuousWithinAt_neg).div
              continuous_abs.continuousWithinAt _)).add
        tendsto_const_nhds
    lift z to ℝ using him
    -- ⊢ ↑abs ↑z ≠ 0
    simpa using hre.ne
    -- 🎉 no goals
  · rw [arg, if_neg hre.not_le, if_pos him.ge]
    -- 🎉 no goals
#align complex.continuous_within_at_arg_of_re_neg_of_im_zero Complex.continuousWithinAt_arg_of_re_neg_of_im_zero

theorem tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto arg (𝓝[{ z : ℂ | 0 ≤ z.im }] z) (𝓝 π) := by
  simpa only [arg_eq_pi_iff.2 ⟨hre, him⟩] using
    (continuousWithinAt_arg_of_re_neg_of_im_zero hre him).tendsto
#align complex.tendsto_arg_nhds_within_im_nonneg_of_re_neg_of_im_zero
Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero

theorem continuousAt_arg_coe_angle (h : x ≠ 0) : ContinuousAt ((↑) ∘ arg : ℂ → Real.Angle) x := by
  by_cases hs : 0 < x.re ∨ x.im ≠ 0
  -- ⊢ ContinuousAt (Angle.coe ∘ arg) x
  · exact Real.Angle.continuous_coe.continuousAt.comp (continuousAt_arg hs)
    -- 🎉 no goals
  · rw [← Function.comp.right_id (((↑) : ℝ → Real.Angle) ∘ arg),
      (Function.funext_iff.2 fun _ => (neg_neg _).symm : (id : ℂ → ℂ) = Neg.neg ∘ Neg.neg), ←
      Function.comp.assoc]
    refine' ContinuousAt.comp _ continuous_neg.continuousAt
    -- ⊢ ContinuousAt ((Angle.coe ∘ arg) ∘ Neg.neg) (-x)
    suffices ContinuousAt (Function.update (((↑) ∘ arg) ∘ Neg.neg : ℂ → Real.Angle) 0 π) (-x) by
      rwa [continuousAt_update_of_ne (neg_ne_zero.2 h)] at this
    have ha :
      Function.update (((↑) ∘ arg) ∘ Neg.neg : ℂ → Real.Angle) 0 π = fun z =>
        (arg z : Real.Angle) + π := by
      rw [Function.update_eq_iff]
      exact ⟨by simp, fun z hz => arg_neg_coe_angle hz⟩
    rw [ha]
    -- ⊢ ContinuousAt (fun z => ↑(arg z) + ↑π) (-x)
    push_neg at hs
    -- ⊢ ContinuousAt (fun z => ↑(arg z) + ↑π) (-x)
    refine'
      (Real.Angle.continuous_coe.continuousAt.comp (continuousAt_arg (Or.inl _))).add
        continuousAt_const
    rw [neg_re, neg_pos]
    -- ⊢ x.re < 0
    exact hs.1.lt_of_ne fun h0 => h (ext_iff.2 ⟨h0, hs.2⟩)
    -- 🎉 no goals
#align complex.continuous_at_arg_coe_angle Complex.continuousAt_arg_coe_angle

end Continuity

end Complex
