/-
Copyright (c) 2025 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib.Data.CombinatorialMap
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Planar Graphs

This file defines planar graphs using combinatorial maps.

-/

namespace SimpleGraph

variable {V D : Type*}

/-- A `CombinatorialMap` induces a `SimpleGraph`. -/
def fromCombinatorialMap (M : CombinatorialMap D) : SimpleGraph M.Vertex where
  Adj v₁ v₂ := ∃ d₁ d₂ : D, M.dartVertex d₁ = v₁ ∧ M.dartVertex d₂ = v₂ ∧ M.edgePerm d₁ = d₂ ∧
    v₁ ≠ v₂
  symm := by
    intro v₁ v₂ ⟨d₁, d₂, h₁, h₂, h₃, h₄⟩
    use d₂, d₁
    exact ⟨h₂, h₁, (M.edgePerm_involutive.eq_iff.mp h₃).symm, h₄.symm⟩
  loopless := by tauto

/-- A `SimpleGraph` is planar if it is induced by a planar `CombinatorialMap`. -/
def IsPlanar [Fintype D] (G : SimpleGraph V) : Prop :=
  ∃ M : CombinatorialMap D, Nonempty ((fromCombinatorialMap M) ≃g G) ∧ M.IsPlanar

end SimpleGraph
