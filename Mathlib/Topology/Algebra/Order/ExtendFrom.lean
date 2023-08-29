/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ExtendFrom

#align_import topology.algebra.order.extend_from from "leanprover-community/mathlib"@"0a0ec35061ed9960bf0e7ffb0335f44447b58977"

/-!
# Lemmas about `extendFrom` in an order topology.
-/

set_option autoImplicit true


open Filter Set TopologicalSpace

open Topology Classical

theorem continuousOn_Icc_extendFrom_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {la lb : β}
    (hab : a ≠ b) (hf : ContinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la))
    (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) : ContinuousOn (extendFrom (Ioo a b) f) (Icc a b) := by
  apply continuousOn_extendFrom
  -- ⊢ Icc a b ⊆ closure (Ioo a b)
  · rw [closure_Ioo hab]
    -- 🎉 no goals
  · intro x x_in
    -- ⊢ ∃ y, Tendsto f (𝓝[Ioo a b] x) (𝓝 y)
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc x_in with (rfl | rfl | h)
    · exact ⟨la, ha.mono_left <| nhdsWithin_mono _ Ioo_subset_Ioi_self⟩
      -- 🎉 no goals
    · exact ⟨lb, hb.mono_left <| nhdsWithin_mono _ Ioo_subset_Iio_self⟩
      -- 🎉 no goals
    · exact ⟨f x, hf x h⟩
      -- 🎉 no goals
#align continuous_on_Icc_extend_from_Ioo continuousOn_Icc_extendFrom_Ioo

theorem eq_lim_at_left_extendFrom_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [T2Space β] {f : α → β} {a b : α} {la : β} (hab : a < b)
    (ha : Tendsto f (𝓝[>] a) (𝓝 la)) : extendFrom (Ioo a b) f a = la := by
  apply extendFrom_eq
  -- ⊢ a ∈ closure (Ioo a b)
  · rw [closure_Ioo hab.ne]
    -- ⊢ a ∈ Icc a b
    simp only [le_of_lt hab, left_mem_Icc, right_mem_Icc]
    -- 🎉 no goals
  · simpa [hab]
    -- 🎉 no goals
#align eq_lim_at_left_extend_from_Ioo eq_lim_at_left_extendFrom_Ioo

theorem eq_lim_at_right_extendFrom_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [T2Space β] {f : α → β} {a b : α} {lb : β} (hab : a < b)
    (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) : extendFrom (Ioo a b) f b = lb := by
  apply extendFrom_eq
  -- ⊢ b ∈ closure (Ioo a b)
  · rw [closure_Ioo hab.ne]
    -- ⊢ b ∈ Icc a b
    simp only [le_of_lt hab, left_mem_Icc, right_mem_Icc]
    -- 🎉 no goals
  · simpa [hab]
    -- 🎉 no goals
#align eq_lim_at_right_extend_from_Ioo eq_lim_at_right_extendFrom_Ioo

theorem continuousOn_Ico_extendFrom_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {la : β}
    (hab : a < b) (hf : ContinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la)) :
    ContinuousOn (extendFrom (Ioo a b) f) (Ico a b) := by
  apply continuousOn_extendFrom
  -- ⊢ Ico a b ⊆ closure (Ioo a b)
  · rw [closure_Ioo hab.ne]
    -- ⊢ Ico a b ⊆ Icc a b
    exact Ico_subset_Icc_self
    -- 🎉 no goals
  · intro x x_in
    -- ⊢ ∃ y, Tendsto f (𝓝[Ioo a b] x) (𝓝 y)
    rcases eq_left_or_mem_Ioo_of_mem_Ico x_in with (rfl | h)
    -- ⊢ ∃ y, Tendsto f (𝓝[Ioo x b] x) (𝓝 y)
    · use la
      -- ⊢ Tendsto f (𝓝[Ioo x b] x) (𝓝 la)
      simpa [hab]
      -- 🎉 no goals
    · exact ⟨f x, hf x h⟩
      -- 🎉 no goals
#align continuous_on_Ico_extend_from_Ioo continuousOn_Ico_extendFrom_Ioo

theorem continuousOn_Ioc_extendFrom_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {lb : β}
    (hab : a < b) (hf : ContinuousOn f (Ioo a b)) (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) :
    ContinuousOn (extendFrom (Ioo a b) f) (Ioc a b) := by
  have := @continuousOn_Ico_extendFrom_Ioo αᵒᵈ _ _ _ _ _ _ _ f _ _ lb hab
  -- ⊢ ContinuousOn (extendFrom (Ioo a b) f) (Ioc a b)
  erw [dual_Ico, dual_Ioi, dual_Ioo] at this
  -- ⊢ ContinuousOn (extendFrom (Ioo a b) f) (Ioc a b)
  exact this hf hb
  -- 🎉 no goals
#align continuous_on_Ioc_extend_from_Ioo continuousOn_Ioc_extendFrom_Ioo
