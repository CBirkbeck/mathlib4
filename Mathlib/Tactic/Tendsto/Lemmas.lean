import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Field

universe u v

open Filter Topology

namespace TendstoTactic

theorem tendsto_bot_of_tendsto_top {α : Type v} {𝕜 : Type u} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    (f : 𝕜 → α) {l : Filter α} (h : Tendsto (fun x ↦ f (-x)) atTop l) :
    Tendsto f atBot l := by
  rw [show f = (f ∘ Neg.neg) ∘ Neg.neg by eta_expand; simp]
  exact Tendsto.comp h tendsto_neg_atBot_atTop

theorem tendsto_zero_right_of_tendsto_top {α : Type v} {𝕜 : Type u} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    (f : 𝕜 → α) {l : Filter α} (h : Tendsto (fun x ↦ f x⁻¹) atTop l) :
    Tendsto f (𝓝[>] 0) l := by
  rw [show f = (f ∘ Inv.inv) ∘ Inv.inv by eta_expand; simp]
  apply Tendsto.comp h tendsto_inv_zero_atTop

theorem tendsto_zero_left_of_tendsto_bot {α : Type v} {𝕜 : Type u} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    (f : 𝕜 → α) {l : Filter α} (h : Tendsto (fun x ↦ f x⁻¹) atBot l) :
    Tendsto f (𝓝[<] 0) l := by
  rw [show f = (f ∘ Inv.inv) ∘ Inv.inv by eta_expand; simp]
  apply Tendsto.comp h tendsto_inv_zero_atBot

theorem tendsto_zero_left_of_tendsto_top {α : Type v} {𝕜 : Type u} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    (f : 𝕜 → α) {l : Filter α} (h : Tendsto (fun x ↦ f (- x⁻¹)) atTop l) :
    Tendsto f (𝓝[<] 0) l := by
  conv at h => arg 1; ext x; arg 1; rw [show -x⁻¹ = (-x)⁻¹ by ring]
  exact tendsto_zero_left_of_tendsto_bot _ (tendsto_bot_of_tendsto_top _ h)

theorem tendsto_zero_punctured_of_tendsto_top {α : Type v} {𝕜 : Type u} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    (f : 𝕜 → α) {l : Filter α} (h_pos : Tendsto (fun x ↦ f x⁻¹) atTop l)
    (h_neg : Tendsto (fun x ↦ f (-x⁻¹)) atTop l) :
    Tendsto f (𝓝[≠] 0) l := by
  rw [← nhds_left'_sup_nhds_right']
  apply Tendsto.sup
  · exact tendsto_zero_left_of_tendsto_top _ h_neg
  · exact tendsto_zero_right_of_tendsto_top _ h_pos

theorem tendsto_nhds_right_of_tendsto_top {α : Type v} {𝕜 : Type u} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    (f : 𝕜 → α) {l : Filter α} {c : 𝕜} (h : Tendsto (fun x ↦ f (c + x⁻¹)) atTop l) :
    Tendsto f (𝓝[>] c) l := by
  sorry

theorem tendsto_nhds_left_of_tendsto_top {α : Type v} {𝕜 : Type u} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    (f : 𝕜 → α) {l : Filter α} {c : 𝕜} (h : Tendsto (fun x ↦ f (c - x⁻¹)) atTop l) :
    Tendsto f (𝓝[<] c) l := by
  sorry

theorem tendsto_nhds_punctured_of_tendsto_top {α : Type v} {𝕜 : Type u} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    (f : 𝕜 → α) {l : Filter α} {c : 𝕜}
    (h_neg : Tendsto (fun x ↦ f (c - x⁻¹)) atTop l)
    (h_pos : Tendsto (fun x ↦ f (c + x⁻¹)) atTop l) :
    Tendsto f (𝓝[≠] c) l := by
  sorry

end TendstoTactic
