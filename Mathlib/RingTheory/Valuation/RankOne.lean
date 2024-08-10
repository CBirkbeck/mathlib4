/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Data.NNReal.Basic
import Mathlib.RingTheory.Valuation.Basic

/-!
# Rank one valuations

We define rank one valuations.

## Main Definitions

* `RankLeOne` : A valuation `v` has rank at most one it its image is contained in `ℝ≥0`
  Note that this class contains the data of the inclusion of the codomain of `v` into `ℝ≥0`.

* `RankOne` : A valuation `v` has rank one if it is nontrivial and of rank at most one.

## Tags

valuation, rank one
-/

noncomputable section

open Function Multiplicative

open scoped NNReal

variable {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

/-- A valuation has rank at most one if its image is contained in `ℝ≥0`.
  Note that this class includes the data of an inclusion morphism `Γ₀ → ℝ≥0`. -/
class RankLeOne (v : Valuation R Γ₀) where
  /-- The inclusion morphism from `Γ₀` to `ℝ≥0`. -/
  hom : Γ₀ →*₀ ℝ≥0
  strictMono' : StrictMono hom

/-- A valuation has rank one if it is nontrivial and its image is contained in `ℝ≥0`.
  Note that this class includes the data of an inclusion morphism `Γ₀ → ℝ≥0`. -/
class RankOne (v : Valuation R Γ₀) extends RankLeOne v where
  nontrivial' : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1

namespace RankLeOne

variable (v : Valuation R Γ₀) [RankLeOne v]

lemma strictMono : StrictMono (hom v) := strictMono'

def hom_rangeGroup : v.rangeGroup →* ℝ≥0 where
  toFun := (hom v ·.val)
  map_one' := by simp
  map_mul' := by simp

theorem strictMono_rangeGroup : StrictMono (hom_rangeGroup v) := by
  intro x y h
  simpa only [Units.val_lt_val, Subtype.coe_lt_coe, h] using (strictMono v h)

/-- If `v` is a valuation of rank at most one,
and if `x : Γ₀` has image `0` under `RankLeOne.hom v`, then `x = 0`. -/
theorem zero_of_hom_zero {x : Γ₀} (hx : hom v x = 0) : x = 0 := by
  refine (eq_of_le_of_not_lt (zero_le' (a := x)) fun h_lt ↦ ?_).symm
  have hs := strictMono v h_lt
  rw [_root_.map_zero, hx] at hs
  exact hs.false

/-- If `v` is a valuation of rank at most one,
then`x : Γ₀` has image `0` under `RankLeOne.hom v` if and only if `x = 0`. -/
theorem hom_eq_zero_iff {x : Γ₀} : hom v x = 0 ↔ x = 0 :=
  ⟨fun h ↦ zero_of_hom_zero v h, fun h ↦ by rw [h, _root_.map_zero]⟩

end RankLeOne

namespace RankOne

variable (v : Valuation R Γ₀) [RankOne v]

lemma nontrivial : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1 := nontrivial'

/-- A nontrivial unit of `Γ₀`, given that there exists a rank one `v : Valuation R Γ₀`. -/
def unit : Γ₀ˣ :=
  Units.mk0 (v (nontrivial v).choose) ((nontrivial v).choose_spec).1

/-- A proof that `RankOne.unit v ≠ 1`. -/
theorem unit_ne_one : unit v ≠ 1 := by
  rw [Ne, ← Units.eq_iff, Units.val_one]
  exact ((nontrivial v).choose_spec ).2

theorem rangeGroup_ne_one : v.rangeGroup ≠ ⊥ := by
  simp only [Subgroup.ne_bot_iff_exists_ne_one, ne_eq, Subtype.exists, Submonoid.mk_eq_one,
    exists_prop]
  exact ⟨unit v, mem_rangeGroup v (by rfl), unit_ne_one v⟩

@[nontriviality]
theorem nontrivial_range : Nontrivial (v.rangeGroup) :=
  (Subgroup.nontrivial_iff_ne_bot v.rangeGroup).mpr (rangeGroup_ne_one v)

end RankOne

end Valuation
