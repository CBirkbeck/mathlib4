/-
Copyright (c) 2024 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Topology.Algebra.Module.StrongTopology
import Mathlib.LinearAlgebra.SesquilinearForm

/-!
# Topological dual

## Main definitions

* `Dual`: abbreviation for `E →L[𝕜] 𝕜`.
* `dualPairing`: the canonical pairing `Dual 𝕜 E →ₗ[𝕜] E →ₗ[𝕜] 𝕜`.

## Main statements

* `dualPairing_separatingLeft`: the dual pairing is always left separating

-/

noncomputable section

open Filter Topology

variable {𝕜 E F ι : Type*}

section CommSemiring

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] [TopologicalSpace E] [ContinuousConstSMul 𝕜 𝕜]

variable (𝕜 E) in
/-- The topological dual of a topological vector space `E`. -/
abbrev Dual : Type _ := E →L[𝕜] 𝕜
#align normed_space.dual Dual

variable (𝕜 E) in
/-- The canonical pairing of a vector space and its topological dual. -/
def dualPairing : (Dual 𝕜 E) →ₗ[𝕜] E →ₗ[𝕜] 𝕜 :=
  ContinuousLinearMap.coeLM 𝕜
#align top_dual_pairing dualPairing
#align normed_space.dual_pairing dualPairing

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
variable [ContinuousConstSMul 𝕜 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

theorem dualPairing_apply (v : E →L[𝕜] 𝕜) (x : E) : dualPairing 𝕜 E v x = v x :=
  rfl
#align dual_pairing_apply dualPairing_apply
#align normed_space.dual_pairing_apply dualPairing_apply

end CommSemiring

section Ring

variable [CommRing 𝕜] [TopologicalSpace 𝕜] [TopologicalAddGroup 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousConstSMul 𝕜 𝕜]

variable (𝕜 E) in
theorem dualPairing_separatingLeft : (dualPairing 𝕜 E).SeparatingLeft := by
  rw [LinearMap.separatingLeft_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact ContinuousLinearMap.coe_injective
#align normed_space.dual_pairing_separating_left dualPairing_separatingLeft

end Ring
