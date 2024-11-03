/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.ContinuedFractions.Computation.RatEquiv
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Denumerability of ℚ

This file proves that ℚ is infinite, denumerable, and deduces that it has cardinality `omega`.
-/

assert_not_exists Module

open Cardinal
#print Encodable

instance : Countable ℚ := @Encodable.countable _ _


theorem Cardinal.mkRat : #ℚ = ℵ₀ :=
  le_antisymm _ _

namespace Rat

open Denumerable List

instance : Infinite ℚ :=
  Infinite.of_injective ((↑) : ℕ → ℚ) Nat.cast_injective

instance : Denumerable FiniteContFract :=
  Denumerable.ofEquiv (ℤ × List ℕ+)
    { toFun := fun ⟨z, l, _⟩ =>
        ⟨z, l.reverse.modifyHead (· - 1)⟩
      invFun := fun ⟨z, l⟩ =>
        ⟨z, (l.modifyHead (· + 1)).reverse, by
          simp only [getLast?_reverse, Option.mem_def]
          cases l with
          | nil => simp
          | cons _ _ =>
            simp only [modifyHead_cons, head?_cons, Option.some.injEq]
            exact ne_of_gt (PNat.lt_add_left _ _)⟩
      left_inv := fun ⟨z, l, hl1⟩ => by
        cases h : l.reverse with
          | nil => simp_all
          | cons a _ =>
            rw [← l.reverse_reverse, h, getLast?_reverse, head?_cons,
              Option.mem_def, Option.some.injEq] at hl1
            simp only [h, List.modifyHead_cons, List.reverse_cons, FiniteContFract.mk.injEq,
              true_and]
            rw [← l.reverse_reverse, h, PNat.sub_add_of_lt (lt_of_le_of_ne a.one_le (Ne.symm hl1))]
            simp
      right_inv := fun ⟨z, l⟩ => by cases l <;> simp_all }

/-- **Denumerability of the Rational Numbers** -/
instance instDenumerable : Denumerable ℚ :=
  Denumerable.ofEquiv _ equivFiniteContFract

end Rat

#eval (Denumerable.eqv ℚ).symm 145903
#eval Denumerable.eqv ℚ (55/42)
