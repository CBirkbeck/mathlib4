/-
Copyright (c) 2025 Tomaz Mascarenhas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving, Tomaz Mascarenhas
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Set.Basic

/-!
# Definition of a model of computation based on oracles.

This module defines an abstraction of computation with oracles, enabling the analysis of upper
bounds on the query complexity of algorithms. It also provides a Monad instance for it.

Note that this is the deterministic version. In the future, the stochastic version will
also be ported, which enables the possibility of proving lower bounds on the query complexity
of algorithms. In order to facilitate this future integration, the design of the types
in this module is based on the original stochastic version. Source:
  https://github.com/girving/debate/blob/862fdb1cf55df0d541b802bdb1e672d724df6398/Comp/Oracle.lean

## Main Definitions

* Comp (ι : Type) {I : Type} (s : Set I) (α : Type) : Type
* Comp.run : Comp ι s α → (I → Oracle ι) → α × (I → ℕ)
-/

open Classical
open Set
noncomputable section

universe u

variable {ι I : Type*}
variable {s t : Set I}
variable {α β γ : Type*}
variable {ω : ι → Type*}

namespace QueryComplexity

/-- A deterministic oracle is a dependent map -/
def Oracle (α : Type*) (β : α → Type*) := (x : α) → (β x)

/-- An `Oracle` that always returns `Bool` -/
abbrev BOracle (α : Type*) := Oracle α fun _ ↦ Bool

/-- A deterministic computation that make decisions by querying oracles. A computation is either a
pure value or the identifier of an oracle (`o`) drawn from a predefined set (`s`), a value to
be queried by the oracle (`i`) and a dependent selection function that determines which oracle to
run, depending on the result of the query. -/
inductive Comp (ι : Type*) (ω : ι → Type*) (s : Set I) (α : Type*) : Type _ where
  | pure' : α → Comp ι ω s α
  | query' : (o : I) → o ∈ s → (y : ι) → ((ω y) → Comp ι ω s α) → Comp ι ω s α

/-- `Comp` where all oracles return `Bool` -/
abbrev BComp (ι : Type*) {I : Type*} (s : Set I) (α : Type*) := Comp ι (fun _ ↦ Bool) s α

namespace Comp

/-- The standard bind operation for `Comp` -/
def bind' (f : Comp ι ω s α) (g : α → Comp ι ω s β) : Comp ι ω s β := match f with
  | .pure' x => g x
  | .query' o m y f => .query' o m y fun b => (f b).bind' g

/-- `Comp` is a monad -/
instance : Monad (Comp ι ω s) where
  pure := Comp.pure'
  bind := Comp.bind'

/-- Produce a `Comp` given the identifier of an oracle and a value to be queried.
The `Comp` just returns `true` or `false` according to the answer of the oracle. -/
def query (o : I) (y : ι) : Comp ι ω {o} (ω y)  :=
  Comp.query' o (mem_singleton _) y pure

/-- Execute `f` with the oracles `os`. Returns the final value and the number of queries to
each one of the oracles. -/
def run (f : Comp ι ω s α) (os : I → Oracle ι ω) : α × (I → ℕ) := match f with
  | .pure' x => (x, fun _ => 0)
  | .query' i _ y f =>
    let x := os i y
    let (z,c) := (f x).run os
    (z, c + fun j => if j = i then 1 else 0)

/-- The value of a `Comp ι s` after execution -/
def value (f : Comp ι ω s α) (o : I → Oracle ι ω) : α :=
  (f.run o).1

/-- The value of a `Comp ι s` after execution with a single oracle -/
@[simp]
def value' (f : Comp ι ω s α) (o : Oracle ι ω) : α :=
  f.value fun _ ↦ o

/-- The query count for a specific oracle of a `Comp ι s` -/
def cost (f : Comp ι ω s α) (o : I → Oracle ι ω) (i : I) : ℕ :=
  (f.run o).2 i

/-- The cost of a `Comp ι s`, when run with a single oracle -/
def cost' (f : Comp ι ω s α) (o : Oracle ι ω) : I → ℕ :=
  f.cost fun _ ↦ o

/-- Extend the set of allowed oracles in a computation -/
def allow (f : Comp ι ω s α) (st : s ⊆ t) : Comp ι ω t α := match f with
  | .pure' x => pure x
  | .query' i m y f => .query' i (st m) y (fun b => (f b).allow st)

/-- Extend the set of allowed oracles in a computation to the universe set -/
def allow_all (f : Comp ι ω s α) : Comp ι ω (@univ I) α :=
  f.allow (subset_univ s)

end Comp

end QueryComplexity
