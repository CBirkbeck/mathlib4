/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Analysis.InnerProductSpace.Basic

#align_import analysis.inner_product_space.of_norm from "leanprover-community/mathlib"@"baa88307f3e699fa7054ef04ec79fa4f056169cb"

/-!
# Inner product space derived from a norm

This file defines an `InnerProductSpace` instance from a norm that respects the
parallellogram identity. The parallelogram identity is a way to express the inner product of `x` and
`y` in terms of the norms of `x`, `y`, `x + y`, `x - y`.

## Main results

- `InnerProductSpace.ofNorm`: a normed space whose norm respects the parallellogram identity,
  can be seen as an inner product space.

## Implementation notes

We define `inner_`

$$\langle x, y \rangle := \frac{1}{4} (‖x + y‖^2 - ‖x - y‖^2 + i ‖ix + y‖ ^ 2 - i ‖ix - y‖^2)$$

and use the parallelogram identity

$$‖x + y‖^2 + ‖x - y‖^2 = 2 (‖x‖^2 + ‖y‖^2)$$

to prove it is an inner product, i.e., that it is conjugate-symmetric (`inner_.conj_symm`) and
linear in the first argument. `add_left` is proved by judicious application of the parallelogram
identity followed by tedious arithmetic. `smul_left` is proved step by step, first noting that
$\langle λ x, y \rangle = λ \langle x, y \rangle$ for $λ ∈ ℕ$, $λ = -1$, hence $λ ∈ ℤ$ and $λ ∈ ℚ$
by arithmetic. Then by continuity and the fact that ℚ is dense in ℝ, the same is true for ℝ.
The case of ℂ then follows by applying the result for ℝ and more arithmetic.

## TODO

Move upstream to `Analysis.InnerProductSpace.Basic`.

## References

- [Jordan, P. and von Neumann, J., *On inner products in linear, metric spaces*][Jordan1935]
- https://math.stackexchange.com/questions/21792/norms-induced-by-inner-products-and-the-parallelogram-law
- https://math.dartmouth.edu/archive/m113w10/public_html/jordan-vneumann-thm.pdf

## Tags

inner product space, Hilbert space, norm
-/


open IsROrC

open scoped ComplexConjugate

variable {𝕜 : Type*} [IsROrC 𝕜] (E : Type*) [NormedAddCommGroup E]

/-- Predicate for the parallelogram identity to hold in a normed group. This is a scalar-less
version of `InnerProductSpace`. If you have an `InnerProductSpaceable` assumption, you can
locally upgrade that to `InnerProductSpace 𝕜 E` using `casesI nonempty_innerProductSpace 𝕜 E`.
-/
class InnerProductSpaceable : Prop where
  parallelogram_identity :
    ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)
#align inner_product_spaceable InnerProductSpaceable

variable (𝕜) {E}

theorem InnerProductSpace.toInnerProductSpaceable [InnerProductSpace 𝕜 E] :
    InnerProductSpaceable E :=
  ⟨parallelogram_law_with_norm 𝕜⟩
#align inner_product_space.to_inner_product_spaceable InnerProductSpace.toInnerProductSpaceable

-- See note [lower instance priority]
instance (priority := 100) InnerProductSpace.toInnerProductSpaceable_ofReal
    [InnerProductSpace ℝ E] : InnerProductSpaceable E :=
  ⟨parallelogram_law_with_norm ℝ⟩
#align inner_product_space.to_inner_product_spaceable_of_real InnerProductSpace.toInnerProductSpaceable_ofReal

variable [NormedSpace 𝕜 E]

local notation "𝓚" => algebraMap ℝ 𝕜

/-- Auxiliary definition of the inner product derived from the norm. -/
private noncomputable def inner_ (x y : E) : 𝕜 :=
  4⁻¹ * (𝓚 ‖x + y‖ * 𝓚 ‖x + y‖ - 𝓚 ‖x - y‖ * 𝓚 ‖x - y‖ +
    (I : 𝕜) * 𝓚 ‖(I : 𝕜) • x + y‖ * 𝓚 ‖(I : 𝕜) • x + y‖ -
    (I : 𝕜) * 𝓚 ‖(I : 𝕜) • x - y‖ * 𝓚 ‖(I : 𝕜) • x - y‖)

namespace InnerProductSpaceable

variable {𝕜} (E)

-- Porting note: prime added to avoid clashing with public `innerProp`
/-- Auxiliary definition for the `add_left` property. -/
private def innerProp' (r : 𝕜) : Prop :=
  ∀ x y : E, inner_ 𝕜 (r • x) y = conj r * inner_ 𝕜 x y

variable {E}

theorem innerProp_neg_one : innerProp' E ((-1 : ℤ) : 𝕜) := by
  intro x y
  -- ⊢ inner_ 𝕜 (↑(-1) • x) y = ↑(starRingEnd 𝕜) ↑(-1) * inner_ 𝕜 x y
  simp only [inner_, neg_mul_eq_neg_mul, one_mul, Int.cast_one, one_smul, RingHom.map_one, map_neg,
    Int.cast_neg, neg_smul, neg_one_mul]
  rw [neg_mul_comm]
  -- ⊢ 4⁻¹ * (↑𝓚 ‖-x + y‖ * ↑𝓚 ‖-x + y‖ - ↑𝓚 ‖-x - y‖ * ↑𝓚 ‖-x - y‖ + I * ↑𝓚 ‖I • - …
  congr 1
  -- ⊢ ↑𝓚 ‖-x + y‖ * ↑𝓚 ‖-x + y‖ - ↑𝓚 ‖-x - y‖ * ↑𝓚 ‖-x - y‖ + I * ↑𝓚 ‖I • -x + y‖  …
  have h₁ : ‖-x - y‖ = ‖x + y‖ := by rw [← neg_add', norm_neg]
  -- ⊢ ↑𝓚 ‖-x + y‖ * ↑𝓚 ‖-x + y‖ - ↑𝓚 ‖-x - y‖ * ↑𝓚 ‖-x - y‖ + I * ↑𝓚 ‖I • -x + y‖  …
  have h₂ : ‖-x + y‖ = ‖x - y‖ := by rw [← neg_sub, norm_neg, sub_eq_neg_add]
  -- ⊢ ↑𝓚 ‖-x + y‖ * ↑𝓚 ‖-x + y‖ - ↑𝓚 ‖-x - y‖ * ↑𝓚 ‖-x - y‖ + I * ↑𝓚 ‖I • -x + y‖  …
  have h₃ : ‖(I : 𝕜) • -x + y‖ = ‖(I : 𝕜) • x - y‖ := by
    rw [← neg_sub, norm_neg, sub_eq_neg_add, ← smul_neg]
  have h₄ : ‖(I : 𝕜) • -x - y‖ = ‖(I : 𝕜) • x + y‖ := by rw [smul_neg, ← neg_add', norm_neg]
  -- ⊢ ↑𝓚 ‖-x + y‖ * ↑𝓚 ‖-x + y‖ - ↑𝓚 ‖-x - y‖ * ↑𝓚 ‖-x - y‖ + I * ↑𝓚 ‖I • -x + y‖  …
  rw [h₁, h₂, h₃, h₄]
  -- ⊢ ↑𝓚 ‖x - y‖ * ↑𝓚 ‖x - y‖ - ↑𝓚 ‖x + y‖ * ↑𝓚 ‖x + y‖ + I * ↑𝓚 ‖I • x - y‖ * ↑𝓚  …
  ring
  -- 🎉 no goals
#align inner_product_spaceable.inner_prop_neg_one InnerProductSpaceable.innerProp_neg_one

theorem _root_.Continuous.inner_ {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => inner_ 𝕜 (f x) (g x) := by
  unfold inner_
  -- ⊢ Continuous fun x => 4⁻¹ * (↑𝓚 ‖f x + g x‖ * ↑𝓚 ‖f x + g x‖ - ↑𝓚 ‖f x - g x‖  …
  have := Continuous.const_smul (M := 𝕜) hf I
  -- ⊢ Continuous fun x => 4⁻¹ * (↑𝓚 ‖f x + g x‖ * ↑𝓚 ‖f x + g x‖ - ↑𝓚 ‖f x - g x‖  …
  continuity
  -- 🎉 no goals
#align inner_product_spaceable.continuous.inner_ Continuous.inner_

theorem inner_.norm_sq (x : E) : ‖x‖ ^ 2 = re (inner_ 𝕜 x x) := by
  simp only [inner_]
  -- ⊢ ‖x‖ ^ 2 = ↑re (4⁻¹ * (↑𝓚 ‖x + x‖ * ↑𝓚 ‖x + x‖ - ↑𝓚 ‖x - x‖ * ↑𝓚 ‖x - x‖ + I  …
  have h₁ : IsROrC.normSq (4 : 𝕜) = 16 := by
    have : ((4 : ℝ) : 𝕜) = (4 : 𝕜) := by norm_cast
    rw [← this, normSq_eq_def', IsROrC.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have h₂ : ‖x + x‖ = 2 * ‖x‖ := by rw [← two_smul 𝕜, norm_smul, IsROrC.norm_two]
  -- ⊢ ‖x‖ ^ 2 = ↑re (4⁻¹ * (↑𝓚 ‖x + x‖ * ↑𝓚 ‖x + x‖ - ↑𝓚 ‖x - x‖ * ↑𝓚 ‖x - x‖ + I  …
  simp only [h₁, h₂, algebraMap_eq_ofReal, sub_self, norm_zero, mul_re, inv_re, ofNat_re, map_sub,
    map_add, ofReal_re, ofNat_im, ofReal_im, mul_im, I_re, inv_im]
  ring
  -- 🎉 no goals
#align inner_product_spaceable.inner_.norm_sq InnerProductSpaceable.inner_.norm_sq

theorem inner_.conj_symm (x y : E) : conj (inner_ 𝕜 y x) = inner_ 𝕜 x y := by
  simp only [inner_]
  -- ⊢ ↑(starRingEnd 𝕜) (4⁻¹ * (↑𝓚 ‖y + x‖ * ↑𝓚 ‖y + x‖ - ↑𝓚 ‖y - x‖ * ↑𝓚 ‖y - x‖ + …
  have h4 : conj (4⁻¹ : 𝕜) = 4⁻¹ := by norm_num
  -- ⊢ ↑(starRingEnd 𝕜) (4⁻¹ * (↑𝓚 ‖y + x‖ * ↑𝓚 ‖y + x‖ - ↑𝓚 ‖y - x‖ * ↑𝓚 ‖y - x‖ + …
  rw [map_mul, h4]
  -- ⊢ 4⁻¹ * ↑(starRingEnd 𝕜) (↑𝓚 ‖y + x‖ * ↑𝓚 ‖y + x‖ - ↑𝓚 ‖y - x‖ * ↑𝓚 ‖y - x‖ +  …
  congr 1
  -- ⊢ ↑(starRingEnd 𝕜) (↑𝓚 ‖y + x‖ * ↑𝓚 ‖y + x‖ - ↑𝓚 ‖y - x‖ * ↑𝓚 ‖y - x‖ + I * ↑𝓚 …
  simp only [map_sub, map_add, algebraMap_eq_ofReal, ← ofReal_mul, conj_ofReal, map_mul, conj_I]
  -- ⊢ ↑(‖y + x‖ * ‖y + x‖) - ↑(‖y - x‖ * ‖y - x‖) + -I * ↑‖I • y + x‖ * ↑‖I • y +  …
  rw [add_comm y x, norm_sub_rev]
  -- ⊢ ↑(‖x + y‖ * ‖x + y‖) - ↑(‖x - y‖ * ‖x - y‖) + -I * ↑‖I • y + x‖ * ↑‖I • y +  …
  by_cases hI : (I : 𝕜) = 0
  -- ⊢ ↑(‖x + y‖ * ‖x + y‖) - ↑(‖x - y‖ * ‖x - y‖) + -I * ↑‖I • y + x‖ * ↑‖I • y +  …
  · simp only [hI, neg_zero, zero_mul]
    -- 🎉 no goals
  -- Porting note: this replaces `norm_I_of_ne_zero` which does not exist in Lean 4
  have : ‖(I : 𝕜)‖ = 1 := by
    rw [← mul_self_inj_of_nonneg (norm_nonneg I) zero_le_one, one_mul, ← norm_mul,
      I_mul_I_of_nonzero hI, norm_neg, norm_one]
  have h₁ : ‖(I : 𝕜) • y - x‖ = ‖(I : 𝕜) • x + y‖ := by
    trans ‖(I : 𝕜) • ((I : 𝕜) • y - x)‖
    · rw [norm_smul, this, one_mul]
    · rw [smul_sub, smul_smul, I_mul_I_of_nonzero hI, neg_one_smul, ← neg_add', add_comm, norm_neg]
  have h₂ : ‖(I : 𝕜) • y + x‖ = ‖(I : 𝕜) • x - y‖ := by
    trans ‖(I : 𝕜) • ((I : 𝕜) • y + x)‖
    · rw [norm_smul, this, one_mul]
    · rw [smul_add, smul_smul, I_mul_I_of_nonzero hI, neg_one_smul, ← neg_add_eq_sub]
  rw [h₁, h₂, ← sub_add_eq_add_sub]
  -- ⊢ ↑(‖x + y‖ * ‖x + y‖) - ↑(‖x - y‖ * ‖x - y‖) - -I * ↑‖I • x + y‖ * ↑‖I • x +  …
  simp only [neg_mul, sub_eq_add_neg, neg_neg]
  -- 🎉 no goals
#align inner_product_spaceable.inner_.conj_symm InnerProductSpaceable.inner_.conj_symm

variable [InnerProductSpaceable E]

private theorem add_left_aux1 (x y z : E) : ‖x + y + z‖ * ‖x + y + z‖ =
    (‖2 • x + y‖ * ‖2 • x + y‖ + ‖2 • z + y‖ * ‖2 • z + y‖) / 2 - ‖x - z‖ * ‖x - z‖ := by
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm]
  -- ⊢ ‖2 • x + y‖ * ‖2 • x + y‖ + ‖2 • z + y‖ * ‖2 • z + y‖ = 2 * (‖x + y + z‖ * ‖ …
  convert parallelogram_identity (x + y + z) (x - z) using 4 <;> · rw [two_smul]; abel
                                                                   -- ⊢ x + x + y = x + y + z + (x - z)
                                                                                  -- 🎉 no goals
                                                                                  -- 🎉 no goals
                                                                   -- ⊢ x + x + y = x + y + z + (x - z)
                                                                                  -- 🎉 no goals
                                                                                  -- 🎉 no goals
                                                                   -- ⊢ z + z + y = x + y + z - (x - z)
                                                                                  -- 🎉 no goals
                                                                                  -- 🎉 no goals
                                                                   -- ⊢ z + z + y = x + y + z - (x - z)
                                                                                  -- 🎉 no goals
                                                                                  -- 🎉 no goals

private theorem add_left_aux2 (x y z : E) : ‖x + y - z‖ * ‖x + y - z‖ =
    (‖2 • x + y‖ * ‖2 • x + y‖ + ‖y - 2 • z‖ * ‖y - 2 • z‖) / 2 - ‖x + z‖ * ‖x + z‖ := by
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm]
  -- ⊢ ‖2 • x + y‖ * ‖2 • x + y‖ + ‖y - 2 • z‖ * ‖y - 2 • z‖ = 2 * (‖x + y - z‖ * ‖ …
  have h₀ := parallelogram_identity (x + y - z) (x + z)
  -- ⊢ ‖2 • x + y‖ * ‖2 • x + y‖ + ‖y - 2 • z‖ * ‖y - 2 • z‖ = 2 * (‖x + y - z‖ * ‖ …
  convert h₀ using 4 <;> · rw [two_smul]; abel
                           -- ⊢ x + x + y = x + y - z + (x + z)
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                           -- ⊢ x + x + y = x + y - z + (x + z)
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                           -- ⊢ y - (z + z) = x + y - z - (x + z)
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                           -- ⊢ y - (z + z) = x + y - z - (x + z)
                                          -- 🎉 no goals
                                          -- 🎉 no goals

private theorem add_left_aux2' (x y z : E) :
    ‖x + y + z‖ * ‖x + y + z‖ - ‖x + y - z‖ * ‖x + y - z‖ =
    ‖x + z‖ * ‖x + z‖ - ‖x - z‖ * ‖x - z‖ +
    (‖2 • z + y‖ * ‖2 • z + y‖ - ‖y - 2 • z‖ * ‖y - 2 • z‖) / 2 := by
  rw [add_left_aux1, add_left_aux2]; ring
  -- ⊢ (‖2 • x + y‖ * ‖2 • x + y‖ + ‖2 • z + y‖ * ‖2 • z + y‖) / 2 - ‖x - z‖ * ‖x - …
                                     -- 🎉 no goals

private theorem add_left_aux3 (y z : E) :
    ‖2 • z + y‖ * ‖2 • z + y‖ = 2 * (‖y + z‖ * ‖y + z‖ + ‖z‖ * ‖z‖) - ‖y‖ * ‖y‖ := by
  apply eq_sub_of_add_eq
  -- ⊢ ‖2 • z + y‖ * ‖2 • z + y‖ + ‖y‖ * ‖y‖ = 2 * (‖y + z‖ * ‖y + z‖ + ‖z‖ * ‖z‖)
  convert parallelogram_identity (y + z) z using 4 <;> (try rw [two_smul]) <;> abel
                                                        -- ⊢ z + z + y = y + z + z
                                                        -- ⊢ z + z + y = y + z + z
                                                        -- ⊢ y = y + z - z
                                                        -- ⊢ y = y + z - z
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals

private theorem add_left_aux4 (y z : E) :
    ‖y - 2 • z‖ * ‖y - 2 • z‖ = 2 * (‖y - z‖ * ‖y - z‖ + ‖z‖ * ‖z‖) - ‖y‖ * ‖y‖ := by
  apply eq_sub_of_add_eq'
  -- ⊢ ‖y‖ * ‖y‖ + ‖y - 2 • z‖ * ‖y - 2 • z‖ = 2 * (‖y - z‖ * ‖y - z‖ + ‖z‖ * ‖z‖)
  have h₀ := parallelogram_identity (y - z) z
  -- ⊢ ‖y‖ * ‖y‖ + ‖y - 2 • z‖ * ‖y - 2 • z‖ = 2 * (‖y - z‖ * ‖y - z‖ + ‖z‖ * ‖z‖)
  convert h₀ using 4 <;> (try rw [two_smul]) <;> abel
                          -- ⊢ y = y - z + z
                          -- ⊢ y = y - z + z
                          -- ⊢ y - (z + z) = y - z - z
                          -- ⊢ y - (z + z) = y - z - z
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals

private theorem add_left_aux4' (y z : E) :
    (‖2 • z + y‖ * ‖2 • z + y‖ - ‖y - 2 • z‖ * ‖y - 2 • z‖) / 2 =
    ‖y + z‖ * ‖y + z‖ - ‖y - z‖ * ‖y - z‖ := by
  rw [add_left_aux3, add_left_aux4]; ring
  -- ⊢ (2 * (‖y + z‖ * ‖y + z‖ + ‖z‖ * ‖z‖) - ‖y‖ * ‖y‖ - (2 * (‖y - z‖ * ‖y - z‖ + …
                                     -- 🎉 no goals

private theorem add_left_aux5 (x y z : E) :
    ‖(I : 𝕜) • (x + y) + z‖ * ‖(I : 𝕜) • (x + y) + z‖ =
    (‖(I : 𝕜) • (2 • x + y)‖ * ‖(I : 𝕜) • (2 • x + y)‖ +
    ‖(I : 𝕜) • y + 2 • z‖ * ‖(I : 𝕜) • y + 2 • z‖) / 2 -
    ‖(I : 𝕜) • x - z‖ * ‖(I : 𝕜) • x - z‖ := by
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm]
  -- ⊢ ‖I • (2 • x + y)‖ * ‖I • (2 • x + y)‖ + ‖I • y + 2 • z‖ * ‖I • y + 2 • z‖ =  …
  have h₀ := parallelogram_identity ((I : 𝕜) • (x + y) + z) ((I : 𝕜) • x - z)
  -- ⊢ ‖I • (2 • x + y)‖ * ‖I • (2 • x + y)‖ + ‖I • y + 2 • z‖ * ‖I • y + 2 • z‖ =  …
  convert h₀ using 4 <;> · try simp only [two_smul, smul_add]; abel
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals

private theorem add_left_aux6 (x y z : E) :
    ‖(I : 𝕜) • (x + y) - z‖ * ‖(I : 𝕜) • (x + y) - z‖ =
    (‖(I : 𝕜) • (2 • x + y)‖ * ‖(I : 𝕜) • (2 • x + y)‖ +
    ‖(I : 𝕜) • y - 2 • z‖ * ‖(I : 𝕜) • y - 2 • z‖) / 2 -
    ‖(I : 𝕜) • x + z‖ * ‖(I : 𝕜) • x + z‖ := by
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm]
  -- ⊢ ‖I • (2 • x + y)‖ * ‖I • (2 • x + y)‖ + ‖I • y - 2 • z‖ * ‖I • y - 2 • z‖ =  …
  have h₀ := parallelogram_identity ((I : 𝕜) • (x + y) - z) ((I : 𝕜) • x + z)
  -- ⊢ ‖I • (2 • x + y)‖ * ‖I • (2 • x + y)‖ + ‖I • y - 2 • z‖ * ‖I • y - 2 • z‖ =  …
  convert h₀ using 4 <;> · try simp only [two_smul, smul_add]; abel
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals

private theorem add_left_aux7 (y z : E) :
    ‖(I : 𝕜) • y + 2 • z‖ * ‖(I : 𝕜) • y + 2 • z‖ =
    2 * (‖(I : 𝕜) • y + z‖ * ‖(I : 𝕜) • y + z‖ + ‖z‖ * ‖z‖) - ‖(I : 𝕜) • y‖ * ‖(I : 𝕜) • y‖ := by
  apply eq_sub_of_add_eq
  -- ⊢ ‖I • y + 2 • z‖ * ‖I • y + 2 • z‖ + ‖I • y‖ * ‖I • y‖ = 2 * (‖I • y + z‖ * ‖ …
  have h₀ := parallelogram_identity ((I : 𝕜) • y + z) z
  -- ⊢ ‖I • y + 2 • z‖ * ‖I • y + 2 • z‖ + ‖I • y‖ * ‖I • y‖ = 2 * (‖I • y + z‖ * ‖ …
  convert h₀ using 4 <;> · (try simp only [two_smul, smul_add]); abel
                            -- ⊢ I • y + (z + z) = I • y + z + z
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                            -- ⊢ I • y + (z + z) = I • y + z + z
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                            -- ⊢ I • y = I • y + z - z
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                            -- ⊢ I • y = I • y + z - z
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals

private theorem add_left_aux8 (y z : E) :
    ‖(I : 𝕜) • y - 2 • z‖ * ‖(I : 𝕜) • y - 2 • z‖ =
    2 * (‖(I : 𝕜) • y - z‖ * ‖(I : 𝕜) • y - z‖ + ‖z‖ * ‖z‖) - ‖(I : 𝕜) • y‖ * ‖(I : 𝕜) • y‖ := by
  apply eq_sub_of_add_eq'
  -- ⊢ ‖I • y‖ * ‖I • y‖ + ‖I • y - 2 • z‖ * ‖I • y - 2 • z‖ = 2 * (‖I • y - z‖ * ‖ …
  have h₀ := parallelogram_identity ((I : 𝕜) • y - z) z
  -- ⊢ ‖I • y‖ * ‖I • y‖ + ‖I • y - 2 • z‖ * ‖I • y - 2 • z‖ = 2 * (‖I • y - z‖ * ‖ …
  convert h₀ using 4 <;> · (try simp only [two_smul, smul_add]); abel
                            -- ⊢ I • y = I • y - z + z
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                            -- ⊢ I • y = I • y - z + z
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                            -- ⊢ I • y - (z + z) = I • y - z - z
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                            -- ⊢ I • y - (z + z) = I • y - z - z
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals

theorem add_left (x y z : E) : inner_ 𝕜 (x + y) z = inner_ 𝕜 x z + inner_ 𝕜 y z := by
  simp only [inner_, ← mul_add]
  -- ⊢ 4⁻¹ * (↑𝓚 ‖x + y + z‖ * ↑𝓚 ‖x + y + z‖ - ↑𝓚 ‖x + y - z‖ * ↑𝓚 ‖x + y - z‖ + I …
  congr
  -- ⊢ ↑𝓚 ‖x + y + z‖ * ↑𝓚 ‖x + y + z‖ - ↑𝓚 ‖x + y - z‖ * ↑𝓚 ‖x + y - z‖ + I * ↑𝓚 ‖ …
  simp only [mul_assoc, ← map_mul, add_sub_assoc, ← mul_sub, ← map_sub]
  -- ⊢ ↑𝓚 (‖x + y + z‖ * ‖x + y + z‖ - ‖x + (y - z)‖ * ‖x + (y - z)‖) + I * ↑𝓚 (‖I  …
  rw [add_add_add_comm]
  -- ⊢ ↑𝓚 (‖x + y + z‖ * ‖x + y + z‖ - ‖x + (y - z)‖ * ‖x + (y - z)‖) + I * ↑𝓚 (‖I  …
  simp only [← map_add, ← mul_add]
  -- ⊢ ↑𝓚 (‖x + y + z‖ * ‖x + y + z‖ - ‖x + (y - z)‖ * ‖x + (y - z)‖) + I * ↑𝓚 (‖I  …
  congr
  -- ⊢ ‖x + y + z‖ * ‖x + y + z‖ - ‖x + (y - z)‖ * ‖x + (y - z)‖ = ‖x + z‖ * ‖x + z …
  · rw [← add_sub_assoc, add_left_aux2', add_left_aux4']
    -- 🎉 no goals
  · rw [add_left_aux5, add_left_aux6, add_left_aux7, add_left_aux8]
    -- ⊢ (‖I • (2 • x + y)‖ * ‖I • (2 • x + y)‖ + (2 * (‖I • y + z‖ * ‖I • y + z‖ + ‖ …
    simp only [map_sub, map_mul, map_add, div_eq_mul_inv]
    -- ⊢ (‖I • (2 • x + y)‖ * ‖I • (2 • x + y)‖ + (2 * (‖I • y + z‖ * ‖I • y + z‖ + ‖ …
    ring
    -- 🎉 no goals
#align inner_product_spaceable.add_left InnerProductSpaceable.add_left

theorem nat (n : ℕ) (x y : E) : inner_ 𝕜 ((n : 𝕜) • x) y = (n : 𝕜) * inner_ 𝕜 x y := by
  induction' n with n ih
  -- ⊢ inner_ 𝕜 (↑Nat.zero • x) y = ↑Nat.zero * inner_ 𝕜 x y
  · simp only [inner_, Nat.zero_eq, zero_sub, Nat.cast_zero, zero_mul,
      eq_self_iff_true, zero_smul, zero_add, mul_zero, sub_self, norm_neg, smul_zero]
  · simp only [Nat.cast_succ, add_smul, one_smul]
    -- ⊢ inner_ 𝕜 (↑n • x + x) y = (↑n + 1) * inner_ 𝕜 x y
    rw [add_left, ih, add_mul, one_mul]
    -- 🎉 no goals
#align inner_product_spaceable.nat InnerProductSpaceable.nat

private theorem nat_prop (r : ℕ) : innerProp' E (r : 𝕜) := fun x y => by
  simp only [map_natCast]; exact nat r x y
  -- ⊢ inner_ 𝕜 (↑r • x) y = ↑r * inner_ 𝕜 x y
                           -- 🎉 no goals

private theorem int_prop (n : ℤ) : innerProp' E (n : 𝕜) := by
  intro x y
  -- ⊢ inner_ 𝕜 (↑n • x) y = ↑(starRingEnd 𝕜) ↑n * inner_ 𝕜 x y
  rw [← n.sign_mul_natAbs]
  -- ⊢ inner_ 𝕜 (↑(Int.sign n * ↑(Int.natAbs n)) • x) y = ↑(starRingEnd 𝕜) ↑(Int.si …
  simp only [Int.cast_ofNat, map_natCast, map_intCast, Int.cast_mul, map_mul, mul_smul]
  -- ⊢ inner_ 𝕜 (↑(Int.sign n) • ↑(Int.natAbs n) • x) y = ↑(Int.sign n) * ↑(Int.nat …
  obtain hn | rfl | hn := lt_trichotomy n 0
  · rw [Int.sign_eq_neg_one_of_neg hn, innerProp_neg_one ((n.natAbs : 𝕜) • x), nat]
    -- ⊢ ↑(starRingEnd 𝕜) ↑(-1) * (↑(Int.natAbs n) * inner_ 𝕜 x y) = ↑(-1) * ↑(Int.na …
    simp only [map_neg, neg_mul, one_mul, mul_eq_mul_left_iff, true_or_iff, Int.natAbs_eq_zero,
      eq_self_iff_true, Int.cast_one, map_one, neg_inj, Nat.cast_eq_zero, Int.cast_neg]
  · simp only [inner_, Int.cast_zero, zero_sub, Nat.cast_zero, zero_mul,
      eq_self_iff_true, Int.sign_zero, zero_smul, zero_add, mul_zero, smul_zero,
      sub_self, norm_neg, Int.natAbs_zero]
  · rw [Int.sign_eq_one_of_pos hn]
    -- ⊢ inner_ 𝕜 (↑1 • ↑(Int.natAbs n) • x) y = ↑1 * ↑(Int.natAbs n) * inner_ 𝕜 x y
    simp only [one_mul, mul_eq_mul_left_iff, true_or_iff, Int.natAbs_eq_zero, eq_self_iff_true,
      Int.cast_one, one_smul, Nat.cast_eq_zero, nat]

private theorem rat_prop (r : ℚ) : innerProp' E (r : 𝕜) := by
  intro x y
  -- ⊢ inner_ 𝕜 (↑r • x) y = ↑(starRingEnd 𝕜) ↑r * inner_ 𝕜 x y
  have : (r.den : 𝕜) ≠ 0 := by
    haveI : CharZero 𝕜 := IsROrC.charZero_isROrC
    exact_mod_cast r.pos.ne'
  rw [← r.num_div_den, ← mul_right_inj' this, ← nat r.den _ y, smul_smul, Rat.cast_div]
  -- ⊢ inner_ 𝕜 ((↑r.den * (↑↑r.num / ↑↑r.den)) • x) y = ↑r.den * (↑(starRingEnd 𝕜) …
  simp only [map_natCast, Rat.cast_coe_nat, map_intCast, Rat.cast_coe_int, map_div₀]
  -- ⊢ inner_ 𝕜 ((↑r.den * (↑r.num / ↑r.den)) • x) y = ↑r.den * (↑r.num / ↑r.den *  …
  rw [← mul_assoc, mul_div_cancel' _ this, int_prop _ x, map_intCast]
  -- 🎉 no goals

private theorem real_prop (r : ℝ) : innerProp' E (r : 𝕜) := by
  intro x y
  -- ⊢ inner_ 𝕜 (↑r • x) y = ↑(starRingEnd 𝕜) ↑r * inner_ 𝕜 x y
  revert r
  -- ⊢ ∀ (r : ℝ), inner_ 𝕜 (↑r • x) y = ↑(starRingEnd 𝕜) ↑r * inner_ 𝕜 x y
  rw [← Function.funext_iff]
  -- ⊢ (fun r => inner_ 𝕜 (↑r • x) y) = fun r => ↑(starRingEnd 𝕜) ↑r * inner_ 𝕜 x y
  refine' Rat.denseEmbedding_coe_real.dense.equalizer _ _ (funext fun X => _)
  · exact (continuous_ofReal.smul continuous_const).inner_ continuous_const
    -- 🎉 no goals
  · exact (continuous_conj.comp continuous_ofReal).mul continuous_const
    -- 🎉 no goals
  · simp only [Function.comp_apply, IsROrC.ofReal_ratCast, rat_prop _ _]
    -- 🎉 no goals

private theorem I_prop : innerProp' E (I : 𝕜) := by
  by_cases hI : (I : 𝕜) = 0
  -- ⊢ InnerProductSpaceable.innerProp' E I
  · rw [hI, ← Nat.cast_zero]; exact nat_prop _
    -- ⊢ InnerProductSpaceable.innerProp' E ↑0
                              -- 🎉 no goals
  intro x y
  -- ⊢ inner_ 𝕜 (I • x) y = ↑(starRingEnd 𝕜) I * inner_ 𝕜 x y
  have hI' : (-I : 𝕜) * I = 1 := by rw [← inv_I, inv_mul_cancel hI]
  -- ⊢ inner_ 𝕜 (I • x) y = ↑(starRingEnd 𝕜) I * inner_ 𝕜 x y
  rw [conj_I, inner_, inner_, mul_left_comm]
  -- ⊢ 4⁻¹ * (↑𝓚 ‖I • x + y‖ * ↑𝓚 ‖I • x + y‖ - ↑𝓚 ‖I • x - y‖ * ↑𝓚 ‖I • x - y‖ + I …
  congr 1
  -- ⊢ ↑𝓚 ‖I • x + y‖ * ↑𝓚 ‖I • x + y‖ - ↑𝓚 ‖I • x - y‖ * ↑𝓚 ‖I • x - y‖ + I * ↑𝓚 ‖ …
  rw [smul_smul, I_mul_I_of_nonzero hI, neg_one_smul]
  -- ⊢ ↑𝓚 ‖I • x + y‖ * ↑𝓚 ‖I • x + y‖ - ↑𝓚 ‖I • x - y‖ * ↑𝓚 ‖I • x - y‖ + I * ↑𝓚 ‖ …
  rw [mul_sub, mul_add, mul_sub, mul_assoc I (𝓚 ‖I • x - y‖), ← mul_assoc (-I) I, hI', one_mul,
    mul_assoc I (𝓚 ‖I • x + y‖), ← mul_assoc (-I) I, hI', one_mul]
  have h₁ : ‖-x - y‖ = ‖x + y‖ := by rw [← neg_add', norm_neg]
  -- ⊢ ↑𝓚 ‖I • x + y‖ * ↑𝓚 ‖I • x + y‖ - ↑𝓚 ‖I • x - y‖ * ↑𝓚 ‖I • x - y‖ + I * ↑𝓚 ‖ …
  have h₂ : ‖-x + y‖ = ‖x - y‖ := by rw [← neg_sub, norm_neg, sub_eq_neg_add]
  -- ⊢ ↑𝓚 ‖I • x + y‖ * ↑𝓚 ‖I • x + y‖ - ↑𝓚 ‖I • x - y‖ * ↑𝓚 ‖I • x - y‖ + I * ↑𝓚 ‖ …
  rw [h₁, h₂]
  -- ⊢ ↑𝓚 ‖I • x + y‖ * ↑𝓚 ‖I • x + y‖ - ↑𝓚 ‖I • x - y‖ * ↑𝓚 ‖I • x - y‖ + I * ↑𝓚 ‖ …
  simp only [sub_eq_add_neg, mul_assoc]
  -- ⊢ ↑𝓚 ‖I • x + y‖ * ↑𝓚 ‖I • x + y‖ + -(↑𝓚 ‖I • x + -y‖ * ↑𝓚 ‖I • x + -y‖) + I * …
  rw [← neg_mul_eq_neg_mul, ← neg_mul_eq_neg_mul]
  -- ⊢ ↑𝓚 ‖I • x + y‖ * ↑𝓚 ‖I • x + y‖ + -(↑𝓚 ‖I • x + -y‖ * ↑𝓚 ‖I • x + -y‖) + I * …
  abel
  -- 🎉 no goals
  -- 🎉 no goals

theorem innerProp (r : 𝕜) : innerProp' E r := by
  intro x y
  -- ⊢ inner_ 𝕜 (r • x) y = ↑(starRingEnd 𝕜) r * inner_ 𝕜 x y
  rw [← re_add_im r, add_smul, add_left, real_prop _ x, ← smul_smul, real_prop _ _ y, I_prop,
    map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
  ring
  -- 🎉 no goals
#align inner_product_spaceable.inner_prop InnerProductSpaceable.innerProp

end InnerProductSpaceable

open InnerProductSpaceable

/-- **Fréchet–von Neumann–Jordan Theorem**. A normed space `E` whose norm satisfies the
parallelogram identity can be given a compatible inner product. -/
noncomputable def InnerProductSpace.ofNorm
    (h : ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) :
    InnerProductSpace 𝕜 E :=
  haveI : InnerProductSpaceable E := ⟨h⟩
  { inner := inner_ 𝕜
    norm_sq_eq_inner := inner_.norm_sq
    conj_symm := inner_.conj_symm
    add_left := InnerProductSpaceable.add_left
    smul_left := fun _ _ _ => innerProp _ _ _ }
#align inner_product_space.of_norm InnerProductSpace.ofNorm

variable (E)

variable [InnerProductSpaceable E]

/-- **Fréchet–von Neumann–Jordan Theorem**. A normed space `E` whose norm satisfies the
parallelogram identity can be given a compatible inner product. Do
`casesI nonempty_innerProductSpace 𝕜 E` to locally upgrade `InnerProductSpaceable E` to
`InnerProductSpace 𝕜 E`. -/
theorem nonempty_innerProductSpace : Nonempty (InnerProductSpace 𝕜 E) :=
  ⟨{  inner := inner_ 𝕜
      norm_sq_eq_inner := inner_.norm_sq
      conj_symm := inner_.conj_symm
      add_left := add_left
      smul_left := fun _ _ _ => innerProp _ _ _ }⟩
#align nonempty_inner_product_space nonempty_innerProductSpace

variable {𝕜 E}

variable [NormedSpace ℝ E]

-- TODO: Replace `InnerProductSpace.toUniformConvexSpace`
-- See note [lower instance priority]
instance (priority := 100) InnerProductSpaceable.to_uniformConvexSpace : UniformConvexSpace E := by
  cases nonempty_innerProductSpace ℝ E; infer_instance
  -- ⊢ UniformConvexSpace E
                                        -- 🎉 no goals
#align inner_product_spaceable.to_uniform_convex_space InnerProductSpaceable.to_uniformConvexSpace
