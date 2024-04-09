/-
Copyright (c) 2024 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Topology.Algebra.Module.StrongTopology
import Mathlib.Topology.Algebra.Module.WeakDual

/-!
# Topology of pointwise convergence on continous linear maps

## Main definitions

* `PointwiseConvergenceCLM`: Type synonym of `E →SL[σ] F` equipped with the uniform convergence
topology on finite sets.
* `PointwiseConvergenceCLM.evalCLM`: The evaluation map `(f : E →SLₚₜ[σ] F) ↦ f a` for fixed `a : E`
as a continuous linear map.
* `ContinousLinearMap.toPointwiseConvergenceCLM`: The canonical map from `E →SL[σ] F` to
`E →SLₚₜ[σ] F` as a continuous linear map. This is the statement that bounded convergence is
stronger than pointwise convergence.
* `PointwiseConvergenceCLM.equivWeakDual`: The continuous equivalence between `E →Lₚₜ[𝕜] 𝕜` and
`WeakDual 𝕜 E`.

## Main statements

* `PointwiseConvergenceCLM.tendsto_iff_forall_tendsto`: In the topology of pointwise convergence,
`a` converges to `a₀` iff for every `x : E` the map `a · x` converges to `a₀ x`.
* `PointwiseConvergenceCLM.continuous_of_continuous_eval`: A map to `g : α → E →SLₚₜ[σ] F` is
continuous if for every `x : E` the evaluation `g · x` is continuous.

## Notation

* `E →SLₚₜ[σ] F` is space of continuous linear maps equipped with pointwise convergence topology.

-/

/-! ### Topology of pointwise convergence -/

variable {α ι : Type*} [TopologicalSpace α]
variable {𝕜 𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜] [NormedField 𝕜₁] [NormedField 𝕜₂]
variable {σ : 𝕜₁ →+* 𝕜₂}
variable {E F : Type*} [AddCommGroup E] [TopologicalSpace E]
  [AddCommGroup F] [TopologicalSpace F] [TopologicalAddGroup F]
  [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜₁ E] [Module 𝕜₂ F]

open Topology

variable (σ E F) in
/-- The space of continuous linear maps equipped with the topology of pointwise convergence,
sometimes also called the *strong operator topology*. We avoid this terminology since so many other
things share similar names, and using "pointwise convergence" in the name is more informative.

This topology is also known as the weak*-topology in the case that `σ = RingHom.id 𝕜` and `F = 𝕜` -/
@[reducible]
def PointwiseConvergenceCLM := UniformConvergenceCLM σ F {s : Set E | Finite s}

@[inherit_doc]
notation:25 E " →SLₚₜ[" σ "] " F => PointwiseConvergenceCLM σ E F

@[inherit_doc]
notation:25 E " →Lₚₜ[" R "] " F => PointwiseConvergenceCLM (RingHom.id R) E F

namespace PointwiseConvergenceCLM

protected theorem hasBasis_nhds_zero_of_basis
    {ι : Type*} {p : ι → Prop} {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    (𝓝 (0 : E →SLₚₜ[σ] F)).HasBasis (fun Si : Set E × ι => Finite Si.1 ∧ p Si.2)
      fun Si => { f : E →SLₚₜ[σ] F | ∀ x ∈ Si.1, f x ∈ b Si.2 } :=
  UniformConvergenceCLM.hasBasis_nhds_zero_of_basis σ F { S | Finite S }
    ⟨∅, Set.finite_empty⟩ (directedOn_of_sup_mem fun _ _ => Set.Finite.union) h

protected theorem hasBasis_nhds_zero [TopologicalSpace F] [TopologicalAddGroup F] :
    (𝓝 (0 : E →SLₚₜ[σ] F)).HasBasis
      (fun SV : Set E × Set F => Finite SV.1 ∧ SV.2 ∈ (𝓝 0 : Filter F))
      fun SV => { f : E →SLₚₜ[σ] F | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  PointwiseConvergenceCLM.hasBasis_nhds_zero_of_basis (𝓝 0).basis_sets

/-- In the topology of pointwise convergence, `a` converges to `a₀` iff for every `x : E` the map
`a · x` converges to `a₀ x`. -/
theorem tendsto_iff_forall_tendsto {p : Filter ι} {a : ι → E →SLₚₜ[σ] F} {a₀ : E →SLₚₜ[σ] F} :
    Filter.Tendsto a p (𝓝 a₀) ↔ ∀ x : E, Filter.Tendsto (a · x) p (𝓝 (a₀ x)) := by
  let _ := TopologicalAddGroup.toUniformSpace F
  have _ : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  suffices h : Filter.Tendsto a p (𝓝 a₀) ↔ ∀ x, TendstoUniformlyOn (a · ·) a₀ p {x} by
    rw [h, forall_congr]
    intro
    rw [tendstoUniformlyOn_singleton_iff_tendsto]
  rw [UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn]
  unfold TendstoUniformlyOn
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h x u hu
    simpa using h {x} (Set.finite_singleton _) u hu
  · intro h s hs u hu
    rw [Filter.eventually_all_finite hs]
    intro x _hx
    exact h x u hu

variable (σ E F) in
/-- Coercion from `E →SLₚₜ[σ] F` to `E →ₛₗ[σ] F` as a `𝕜₂`-linear map. -/
@[simps!]
def coeLMₛₗ [ContinuousConstSMul 𝕜₂ F] : (E →SLₚₜ[σ] F) →ₗ[𝕜₂] E →ₛₗ[σ] F :=
  ContinuousLinearMap.coeLMₛₗ σ

variable (𝕜 E F) in
/-- Coercion from `E →Lₚₜ[𝕜] F` to `E →ₗ[𝕜] F` as a `𝕜`-linear map. -/
@[simps!]
def coeLM [ContinuousConstSMul 𝕜 F] : (E →Lₚₜ[𝕜] F) →ₗ[𝕜] E →ₗ[𝕜] F := ContinuousLinearMap.coeLM 𝕜

variable (σ F) in
/-- The evaluation map `(f : E →SLₚₜ[σ] F) ↦ f a` for `a : E` as a continuous linear map. -/
@[simps!]
def evalCLM [ContinuousConstSMul 𝕜₂ F] (a : E) : (E →SLₚₜ[σ] F) →L[𝕜₂] F where
  toLinearMap := (coeLMₛₗ σ E F).flip a
  cont := by
    change Continuous ((coeLMₛₗ σ E F).flip a)
    apply continuous_of_continuousAt_zero
    unfold ContinuousAt
    simp only [map_zero]
    rw [PointwiseConvergenceCLM.hasBasis_nhds_zero.tendsto_left_iff]
    intro s hs
    use ({a}, s)
    simp only [hs, and_true, Set.mem_singleton_iff, forall_eq]
    exact ⟨Set.finite_singleton _, fun _ hy ↦ by rwa [Set.mem_setOf_eq] at hy⟩

/-- A map to `E →SLₚₜ[σ] F` is continuous if for every `x : E` the evaluation `g · x` is
continuous. -/
theorem continuous_of_continuous_eval {g : α → E →SLₚₜ[σ] F}
    (h : ∀ x, Continuous (g · x)) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro f
  unfold ContinuousAt
  rw [tendsto_iff_forall_tendsto]
  intro x
  exact (h x).continuousAt

/-- The topology of bounded convergence is stronger than the topology of pointwise convergence. -/
@[simps!]
def _root_.ContinousLinearMap.toPointwiseConvergenceCLM [ContinuousSMul 𝕜₁ E]
    [ContinuousConstSMul 𝕜₂ F] : (E →SL[σ] F) →L[𝕜₂] (E →SLₚₜ[σ] F) where
  toLinearMap := LinearMap.id
  cont := continuous_id_of_le
    (UniformConvergenceCLM.topologicalSpace_mono _ _ fun _ ↦ Set.Finite.isVonNBounded)

variable (𝕜 E) in
/-- The topology of pointwise convergence on `E →Lₚₜ[𝕜] 𝕜` coincides with the weak-* topology. -/
@[simps!]
def equivWeakDual : (E →Lₚₜ[𝕜] 𝕜) ≃L[𝕜] WeakDual 𝕜 E where
  toLinearEquiv := LinearEquiv.refl 𝕜 (E →L[𝕜] 𝕜)
  continuous_toFun :=
    WeakDual.continuous_of_continuous_eval (fun y ↦ (evalCLM _ 𝕜 y).continuous)
  continuous_invFun := continuous_of_continuous_eval (WeakBilin.eval_continuous _)

end PointwiseConvergenceCLM
