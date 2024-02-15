import Mathlib.LinearAlgebra.LinearIndependent

set_option pp.unicode.fun true

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {s : Set V} {x : V}

-- FIXME temporarily removing this to get a build on nightly-testing
-- Mathlib tracking issue at https://github.com/leanprover-community/mathlib4/issues/10536

-- variable (h : LinearIndependent K (fun b => b : s → V)) in
-- /-- info: h : LinearIndependent K fun (b : ↑s) ↦ ↑b -/
-- #guard_msgs in #check h

variable (h : LinearIndependent K (Subtype.val : s → V)) in
/-- info: h : LinearIndependent (ι := { x // x ∈ s }) K Subtype.val -/
#guard_msgs in #check h

variable (h : LinearIndependent K (by exact Subtype.val : s → V)) in
/-- info: h : LinearIndependent (ι := ↑s) K Subtype.val -/
#guard_msgs in #check h

-- FIXME temporarily removing this to get a build on nightly-testing

-- variable (h : LinearIndependent K (fun b => (fun b => b : s → V) b)) in
-- /-- info: h : LinearIndependent K fun (b : ↑s) ↦ (fun b ↦ ↑b) b -/
-- #guard_msgs in #check h
