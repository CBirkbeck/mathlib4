/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.NumberTheory.IccSums

/-!
# Infinite conditional sums and products over intervals of integers.

We define filters on `Finset ℤ` given by intervals `Icc (-N) N`, `Ico (-N) N`, `Ioc (-N) N` and
`Ioo (-N) N` as `N` tends to infinity. We then prove that the corresponding infinite sums and
products *are equal to the infinite sum or product over `ℤ

-/

open TopologicalSpace Filter Function Finset

open scoped Topology

variable {α β γ : Type*} [CommMonoid α] [TopologicalSpace α] [T2Space α]

/-- The filter in the integers of intevals of the form `[-N,N]`. -/
def Icc_filter : Filter (Finset ℤ) := atTop.map (fun N : ℕ ↦ Icc (-(N : ℤ)) N)

/-- The filter in the integers of intevals of the form `[N,N)`. -/
def Ico_filter : Filter (Finset ℤ) := atTop.map (fun N : ℕ ↦ Ico (-(N : ℤ)) N)

/-- The filter in the integers of intevals of the form `(N,N]`. -/
def Ioc_filter : Filter (Finset ℤ) := atTop.map (fun N : ℕ ↦ Ioc (-(N : ℤ)) N)

/-- The filter in the integers of intevals of the form `(N,N)`. -/
def Ioo_filter : Filter (Finset ℤ) := atTop.map (fun N : ℕ ↦ Ioo (-(N : ℤ)) N)

instance : NeBot (Icc_filter) := by
  simp [Icc_filter, Filter.NeBot.map]

instance : NeBot (Ico_filter) := by
  simp [Ico_filter, Filter.NeBot.map]

instance : NeBot (Ioc_filter) := by
  simp [Ioc_filter, Filter.NeBot.map]

instance : NeBot (Ioo_filter) := by
  simp [Ioo_filter, Filter.NeBot.map]

lemma tendsto_Icc_atTop_atTop : Tendsto (fun N : ℕ => Finset.Icc (-N : ℤ) N) atTop atTop :=
  tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Icc_subset_Icc (by gcongr) (by gcongr))
  (fun x ↦ ⟨x.natAbs, by simp [le_abs, neg_le]⟩)

lemma tendsto_Ico_atTop_atTop : Tendsto (fun N : ℕ => Finset.Ico (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Ico_subset_Ico (by omega) (by gcongr))
  exact fun x => ⟨x.natAbs + 1, by simpa using ⟨by apply le_trans _ (add_abs_nonneg x); omega,
    Int.lt_add_one_iff.mpr (le_abs_self x)⟩ ⟩

lemma tendsto_Ioc_atTop_atTop : Tendsto (fun N : ℕ => Finset.Ioc (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Ioc_subset_Ioc (by omega) (by gcongr))
  exact fun x => ⟨x.natAbs + 1, by simpa using ⟨by apply le_trans _ (add_abs_nonneg x); omega,
    (Int.lt_add_one_iff.mpr (le_abs_self x)).le⟩⟩

lemma tendsto_Ioo_atTop_atTop : Tendsto (fun N : ℕ => Finset.Ioo (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Ioo_subset_Ioo (by omega) (by gcongr))
  exact fun x => ⟨x.natAbs + 1, by simpa using ⟨by apply le_trans _ (add_abs_nonneg x); omega,
    (Int.lt_add_one_iff.mpr (le_abs_self x))⟩⟩

@[to_additive]
lemma prodFilter_int_atTop_eq_Icc_filter {f : ℤ → α} (hf : MultipliableFilter atTop f) :
    ∏'[atTop] b, f b = ∏'[Icc_filter] b, f b := by
  have := (hf.hasProdFilter).comp tendsto_Icc_atTop_atTop
  simp only [Icc_filter] at *
  apply symm
  apply HasProdFilter.tprodFilter_eq
  simp only [HasProdFilter, tendsto_map'_iff]
  apply this.congr
  simp

@[to_additive]
lemma prodFilter_int_atTop_eq_Ico_filter {f : ℤ → α} (hf : MultipliableFilter atTop f) :
    ∏'[atTop] b, f b = ∏'[Ico_filter] b, f b := by
  have := (hf.hasProdFilter).comp tendsto_Ico_atTop_atTop
  simp only [Ico_filter] at *
  apply symm
  apply HasProdFilter.tprodFilter_eq
  simp only [HasProdFilter, tendsto_map'_iff]
  apply this.congr
  simp

@[to_additive] --this needs a hyp, but lets see what the min it needs
lemma multipliableFilter_int_Icc_eq_Ico_filter {α : Type*} {f : ℤ → α} [CommGroup α]
    [TopologicalSpace α] [ContinuousMul α] [T2Space α] (hf : MultipliableFilter Icc_filter f)
    (hf2 : Tendsto (fun N : ℕ ↦ (f ↑N)⁻¹) atTop (𝓝 1)) : MultipliableFilter Ico_filter f := by
  have := (hf.hasProdFilter)
  apply HasProdFilter.multipliableFilter
  · simp only [Ico_filter] at *
    simp only [HasProdFilter, tendsto_map'_iff] at *
    apply Filter.Tendsto_of_div_tendsto_one _ (by apply this)
    conv =>
      enter [1, N]
      simp
      rw [prod_Icc_eq_prod_Ico_succ _ (by omega)]
      simp
    apply hf2

@[to_additive] --this needs a hyp, but lets see what the min it needs
lemma prodFilter_int_Icc_eq_Ico_filter {α : Type*} {f : ℤ → α} [CommGroup α] [TopologicalSpace α]
    [ContinuousMul α] [T2Space α] (hf : MultipliableFilter Icc_filter f)
    (hf2 : Tendsto (fun N : ℕ ↦ (f ↑N)⁻¹) atTop (𝓝 1)) :
    ∏'[Icc_filter] b, f b = ∏'[Ico_filter] b, f b := by
  have := (hf.hasProdFilter)
  simp only [Ico_filter] at *
  apply symm
  apply HasProdFilter.tprodFilter_eq
  simp only [HasProdFilter, tendsto_map'_iff] at *
  apply Filter.Tendsto_of_div_tendsto_one _ (by apply this)
  conv =>
    enter [1, N]
    simp
    rw [prod_Icc_eq_prod_Ico_succ _ (by omega)]
    simp
  apply hf2
