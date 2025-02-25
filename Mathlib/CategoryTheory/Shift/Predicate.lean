/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Shift.Basic

/-!
# Predicates on categories equipped with shift

Given a predicate `P : C → Prop` on objects of a category equipped with a shift
by `A`, we define shifted predicates `PredicateShift P a` for all `a : A`.

-/

open CategoryTheory Category

namespace CategoryTheory

variable {C : Type*} [Category C] (P : ObjectProperty C)
  {A : Type*} [AddMonoid A] [HasShift C A]

/-- Given a predicate `P : C → Prop` on objects of a category equipped with a shift by `A`,
this is the predicate which is satisfied by `X` if `P (X⟦a⟧)`. -/
def PredicateShift (a : A) : ObjectProperty C := fun X => P (X⟦a⟧)

lemma predicateShift_iff (a : A) (X : C) : PredicateShift P a X ↔ P (X⟦a⟧) := Iff.rfl

instance predicateShift_closedUnderIsomorphisms (a : A) [P.IsClosedUnderIsomorphisms] :
    (PredicateShift P a).IsClosedUnderIsomorphisms  where
  of_iso e hX := P.prop_of_iso ((shiftFunctor C a).mapIso e) hX

variable (A)

@[simp]
lemma predicateShift_zero [P.IsClosedUnderIsomorphisms] : PredicateShift P (0 : A) = P := by
  ext X
  exact P.prop_iff_of_iso ((shiftFunctorZero C A).app X)

variable {A}

lemma predicateShift_predicateShift (a b c : A) (h : a + b = c) [P.IsClosedUnderIsomorphisms] :
    PredicateShift (PredicateShift P b) a = PredicateShift P c := by
  ext X
  exact P.prop_iff_of_iso ((shiftFunctorAdd' C a b c h).symm.app X)

end CategoryTheory
