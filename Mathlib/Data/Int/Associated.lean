/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Associated
import Mathlib.Data.Int.Units
import Mathlib.Data.Int.Basic

#align_import data.int.associated from "leanprover-community/mathlib"@"207cfac9fcd06138865b5d04f7091e46d9320432"
/-!
# Associated elements and the integers

This file contains some results on equality up to units in the integers.

## Main results

 * `Int.natAbs_eq_iff_associated`: the absolute value is equal iff integers are associated
-/


theorem Int.natAbs_eq_iff_associated {a b : ℤ} : a.natAbs = b.natAbs ↔ Associated a b := by
  refine' Int.natAbs_eq_natAbs_iff.trans _
  -- ⊢ a = b ∨ a = -b ↔ Associated a b
  constructor
  -- ⊢ a = b ∨ a = -b → Associated a b
  · rintro (rfl | rfl)
    -- ⊢ Associated a a
    · rfl
      -- 🎉 no goals
    · exact ⟨-1, by simp⟩
      -- 🎉 no goals
  · rintro ⟨u, rfl⟩
    -- ⊢ a = a * ↑u ∨ a = -(a * ↑u)
    obtain rfl | rfl := Int.units_eq_one_or u
    -- ⊢ a = a * ↑1 ∨ a = -(a * ↑1)
    · exact Or.inl (by simp)
      -- 🎉 no goals
    · exact Or.inr (by simp)
      -- 🎉 no goals
#align int.nat_abs_eq_iff_associated Int.natAbs_eq_iff_associated
