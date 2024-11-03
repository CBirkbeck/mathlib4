/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Topology.Order.Basic

/-!
# Instances related to the discrete topology

We prove that the discrete topology is
* first-countable,
* second-countable for an encodable type,
* equal to the order topology in linear orders which are also `PredOrder` and `SuccOrder`,
* metrizable.

When importing this file and `Data.Nat.SuccPred`, the instances `SecondCountableTopology ℕ`
and `OrderTopology ℕ` become available.

-/


open Order Set TopologicalSpace Filter

variable {α : Type*} [TopologicalSpace α]

instance (priority := 100) DiscreteTopology.firstCountableTopology [DiscreteTopology α] :
    FirstCountableTopology α where
  nhds_generated_countable := by rw [nhds_discrete]; exact isCountablyGenerated_pure

instance (priority := 100) DiscreteTopology.secondCountableTopology_of_countable
    [hd : DiscreteTopology α] [Countable α] : SecondCountableTopology α :=
  haveI : ∀ i : α, SecondCountableTopology (↥({i} : Set α)) := fun i =>
    { is_open_generated_countable :=
        ⟨{univ}, countable_singleton _, by simp only [eq_iff_true_of_subsingleton]⟩ }
  secondCountableTopology_of_countable_cover (singletons_open_iff_discrete.mpr hd)
    (iUnion_of_singleton α)

@[deprecated DiscreteTopology.secondCountableTopology_of_countable (since := "2024-03-11")]
theorem DiscreteTopology.secondCountableTopology_of_encodable {α : Type*}
    [TopologicalSpace α] [DiscreteTopology α] [Countable α] : SecondCountableTopology α :=
  DiscreteTopology.secondCountableTopology_of_countable

theorem LinearOrder.bot_topologicalSpace_eq_generateFrom {α} [LinearOrder α] [PredOrder α]
    [SuccOrder α] : (⊥ : TopologicalSpace α) = generateFrom { s | ∃ a, s = Ioi a ∨ s = Iio a } := by
  let _ := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  exact DiscreteTopology.eq_bot.symm

@[deprecated (since := "2024-11-02")]
alias bot_topologicalSpace_eq_generateFrom_of_pred_succOrder :=
  LinearOrder.bot_topologicalSpace_eq_generateFrom

theorem discreteTopology_iff_orderTopology_of_pred_succ [LinearOrder α] [PredOrder α]
    [SuccOrder α] : DiscreteTopology α ↔ OrderTopology α := by
  refine ⟨fun h => ⟨?_⟩, fun h => ⟨?_⟩⟩
  · rw [h.eq_bot]
    exact LinearOrder.bot_topologicalSpace_eq_generateFrom
  · rw [h.topology_eq_generate_intervals]
    exact LinearOrder.bot_topologicalSpace_eq_generateFrom.symm

@[deprecated (since := "2024-11-02")]
alias discreteTopology_iff_orderTopology_of_pred_succ' :=
  discreteTopology_iff_orderTopology_of_pred_succ
