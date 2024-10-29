/-
Copyright (c) 2024 Pieter Cuijpers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pieter Cuijpers
-/
import Mathlib.Algebra.Group.Defs

/-!
# Mixing for Idempotent Semigroups

An idempotent semigroup is a semigroup that satisfies `x * x = x`.

## Main definitions

* `IsIdemSemigroup`: Typeclass mixin for a semigroup respecting `x * x = x`.
* `IsAddIdemSemigroup`: Typeclass mixin for a semigroup respecting `x + x = x`.

## Naming conventions

## Notation

## References

## TODO

-/

/-- An idempotent additive semigroup is a type with an associative idempotent `(+)`. -/
class IsIdemAddSemigroup (G : Type _) [AddSemigroup G] : Prop where
  /-- Idempotence: `x + x = x` -/
  protected add_idem : ∀ x : G, x + x = x

/-- An idempotent semigroup is a type with an associative idempotent `(*)`. -/
@[to_additive]
class IsIdemSemigroup (G : Type _) [Semigroup G] : Prop where
  /-- Idempotence: `x * x = x` -/
  protected mul_idem : ∀ x : G, x * x = x

section IsIdem

variable (G : Type _)
variable [Semigroup G] [IsIdemSemigroup G]

/-- Making mul_idem available globally -/
@[to_additive]
theorem mul_idem (x : G) : x * x = x := IsIdemSemigroup.mul_idem _

end IsIdem
