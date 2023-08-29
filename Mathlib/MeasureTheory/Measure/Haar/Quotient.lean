/-
Copyright (c) 2022 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Algebra.Group.Opposite

#align_import measure_theory.measure.haar.quotient from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

/-!
# Haar quotient measure

In this file, we consider properties of fundamental domains and measures for the action of a
subgroup of a group `G` on `G` itself.

## Main results

* `MeasureTheory.IsFundamentalDomain.smulInvariantMeasure_map `: given a subgroup `Γ` of a
  topological group `G`, the pushforward to the coset space `G ⧸ Γ` of the restriction of a both
  left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure
  on `G ⧸ Γ`.

* `MeasureTheory.IsFundamentalDomain.isMulLeftInvariant_map `: given a normal subgroup `Γ` of
  a topological group `G`, the pushforward to the quotient group `G ⧸ Γ` of the restriction of
  a both left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a left-invariant
  measure on `G ⧸ Γ`.

Note that a group `G` with Haar measure that is both left and right invariant is called
**unimodular**.
-/


open Set MeasureTheory TopologicalSpace MeasureTheory.Measure

open scoped Pointwise NNReal

variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] {μ : Measure G} {Γ : Subgroup G}

/-- Measurability of the action of the topological group `G` on the left-coset space `G/Γ`. -/
@[to_additive "Measurability of the action of the additive topological group `G` on the left-coset
  space `G/Γ`."]
instance QuotientGroup.measurableSMul [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)] :
    MeasurableSMul G (G ⧸ Γ) where
  measurable_const_smul g := (continuous_const_smul g).measurable
  measurable_smul_const x := (QuotientGroup.continuous_smul₁ x).measurable
#align quotient_group.has_measurable_smul QuotientGroup.measurableSMul
#align quotient_add_group.has_measurable_vadd QuotientAddGroup.measurableVAdd

variable {𝓕 : Set G} (h𝓕 : IsFundamentalDomain (Subgroup.opposite Γ) 𝓕 μ)

variable [Countable Γ] [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]

/-- The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and right-
  invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure on `G ⧸ Γ`. -/
@[to_additive "The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and
  right-invariant measure on an additive topological group `G` to a fundamental domain `𝓕` is a
  `G`-invariant measure on `G ⧸ Γ`."]
theorem MeasureTheory.IsFundamentalDomain.smulInvariantMeasure_map [μ.IsMulLeftInvariant]
    [μ.IsMulRightInvariant] :
    SMulInvariantMeasure G (G ⧸ Γ) (Measure.map QuotientGroup.mk (μ.restrict 𝓕)) where
  measure_preimage_smul g A hA := by
    let π : G → G ⧸ Γ := QuotientGroup.mk
    -- ⊢ ↑↑(map QuotientGroup.mk (Measure.restrict μ 𝓕)) ((fun x => g • x) ⁻¹' A) = ↑ …
    have meas_π : Measurable π := continuous_quotient_mk'.measurable
    -- ⊢ ↑↑(map QuotientGroup.mk (Measure.restrict μ 𝓕)) ((fun x => g • x) ⁻¹' A) = ↑ …
    have 𝓕meas : NullMeasurableSet 𝓕 μ := h𝓕.nullMeasurableSet
    -- ⊢ ↑↑(map QuotientGroup.mk (Measure.restrict μ 𝓕)) ((fun x => g • x) ⁻¹' A) = ↑ …
    have meas_πA : MeasurableSet (π ⁻¹' A) := measurableSet_preimage meas_π hA
    -- ⊢ ↑↑(map QuotientGroup.mk (Measure.restrict μ 𝓕)) ((fun x => g • x) ⁻¹' A) = ↑ …
    rw [Measure.map_apply meas_π hA,
      Measure.map_apply meas_π (measurableSet_preimage (measurable_const_smul g) hA),
      Measure.restrict_apply₀' 𝓕meas, Measure.restrict_apply₀' 𝓕meas]
    set π_preA := π ⁻¹' A
    -- ⊢ ↑↑μ (π ⁻¹' ((fun x x_1 => x • x_1) g ⁻¹' A) ∩ 𝓕) = ↑↑μ (π_preA ∩ 𝓕)
    have : π ⁻¹' ((fun x : G ⧸ Γ => g • x) ⁻¹' A) = (g * ·) ⁻¹' π_preA := by
      ext1; simp
    rw [this]
    -- ⊢ ↑↑μ ((fun x => g * x) ⁻¹' π_preA ∩ 𝓕) = ↑↑μ (π_preA ∩ 𝓕)
    have : μ ((g * ·) ⁻¹' π_preA ∩ 𝓕) = μ (π_preA ∩ (g⁻¹ * ·) ⁻¹' 𝓕) := by
      trans μ ((g * ·) ⁻¹' (π_preA ∩ (g⁻¹ * ·) ⁻¹' 𝓕))
      · rw [preimage_inter]
        congr 2
        simp [Set.preimage]
      rw [measure_preimage_mul]
    rw [this]
    -- ⊢ ↑↑μ (π_preA ∩ (fun x => g⁻¹ * x) ⁻¹' 𝓕) = ↑↑μ (π_preA ∩ 𝓕)
    have h𝓕_translate_fundom : IsFundamentalDomain (Subgroup.opposite Γ) (g • 𝓕) μ :=
      h𝓕.smul_of_comm g
    rw [h𝓕.measure_set_eq h𝓕_translate_fundom meas_πA, ← preimage_smul_inv]; rfl
    -- ⊢ ↑↑μ (π_preA ∩ (fun x => g⁻¹ * x) ⁻¹' 𝓕) = ↑↑μ (π_preA ∩ (fun x => g⁻¹ • x) ⁻ …
                                                                             -- ⊢ ∀ (g : { x // x ∈ ↑Subgroup.opposite Γ }), (fun x => g • x) ⁻¹' π_preA = π_p …
    rintro ⟨γ, γ_in_Γ⟩
    -- ⊢ (fun x => { val := γ, property := γ_in_Γ } • x) ⁻¹' π_preA = π_preA
    ext x
    -- ⊢ x ∈ (fun x => { val := γ, property := γ_in_Γ } • x) ⁻¹' π_preA ↔ x ∈ π_preA
    have : π (x * MulOpposite.unop γ) = π x := by simpa [QuotientGroup.eq'] using γ_in_Γ
    -- ⊢ x ∈ (fun x => { val := γ, property := γ_in_Γ } • x) ⁻¹' π_preA ↔ x ∈ π_preA
    simp only [(· • ·), ← this, mem_preimage]
    -- ⊢ ↑(SMul.smul { val := γ, property := γ_in_Γ } x) ∈ A ↔ ↑(x * MulOpposite.unop …
    rfl
    -- 🎉 no goals
#align measure_theory.is_fundamental_domain.smul_invariant_measure_map MeasureTheory.IsFundamentalDomain.smulInvariantMeasure_map
#align measure_theory.is_add_fundamental_domain.vadd_invariant_measure_map MeasureTheory.IsAddFundamentalDomain.vaddInvariantMeasure_map

/-- Assuming `Γ` is a normal subgroup of a topological group `G`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of a both left- and right-invariant measure on `G` to a
  fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`. -/
@[to_additive "Assuming `Γ` is a normal subgroup of an additive topological group `G`, the
  pushforward to the quotient group `G ⧸ Γ` of the restriction of a both left- and right-invariant
  measure on `G` to a fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`."]
theorem MeasureTheory.IsFundamentalDomain.isMulLeftInvariant_map [Subgroup.Normal Γ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] :
    (Measure.map (QuotientGroup.mk' Γ) (μ.restrict 𝓕)).IsMulLeftInvariant where
  map_mul_left_eq_self x := by
    apply Measure.ext
    -- ⊢ ∀ (s : Set (G ⧸ Γ)), MeasurableSet s → ↑↑(map (fun x_1 => x * x_1) (map (↑(Q …
    intro A hA
    -- ⊢ ↑↑(map (fun x_1 => x * x_1) (map (↑(QuotientGroup.mk' Γ)) (Measure.restrict  …
    obtain ⟨x₁, h⟩ := @Quotient.exists_rep _ (QuotientGroup.leftRel Γ) x
    -- ⊢ ↑↑(map (fun x_1 => x * x_1) (map (↑(QuotientGroup.mk' Γ)) (Measure.restrict  …
    haveI := h𝓕.smulInvariantMeasure_map
    -- ⊢ ↑↑(map (fun x_1 => x * x_1) (map (↑(QuotientGroup.mk' Γ)) (Measure.restrict  …
    convert measure_preimage_smul x₁ ((Measure.map QuotientGroup.mk) (μ.restrict 𝓕)) A using 1
    -- ⊢ ↑↑(map (fun x_1 => x * x_1) (map (↑(QuotientGroup.mk' Γ)) (Measure.restrict  …
    rw [← h, Measure.map_apply]
    · rfl
      -- 🎉 no goals
    · exact measurable_const_mul _
      -- 🎉 no goals
    · exact hA
      -- 🎉 no goals
#align measure_theory.is_fundamental_domain.is_mul_left_invariant_map MeasureTheory.IsFundamentalDomain.isMulLeftInvariant_map
#align measure_theory.is_add_fundamental_domain.is_add_left_invariant_map MeasureTheory.IsAddFundamentalDomain.isAddLeftInvariant_map

variable [T2Space (G ⧸ Γ)] [SecondCountableTopology (G ⧸ Γ)] (K : PositiveCompacts (G ⧸ Γ))

/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of `μ` to `𝓕` is a multiple of Haar measure on `G ⧸ Γ`. -/
@[to_additive "Given a normal subgroup `Γ` of an additive topological group `G` with Haar measure
  `μ`, which is also right-invariant, and a finite volume fundamental domain `𝓕`, the pushforward
  to the quotient group `G ⧸ Γ` of the restriction of `μ` to `𝓕` is a multiple of Haar measure on
  `G ⧸ Γ`."]
theorem MeasureTheory.IsFundamentalDomain.map_restrict_quotient [Subgroup.Normal Γ]
    [MeasureTheory.Measure.IsHaarMeasure μ] [μ.IsMulRightInvariant] (h𝓕_finite : μ 𝓕 < ⊤) :
    Measure.map (QuotientGroup.mk' Γ) (μ.restrict 𝓕) =
      μ (𝓕 ∩ QuotientGroup.mk' Γ ⁻¹' K) • MeasureTheory.Measure.haarMeasure K := by
  let π : G →* G ⧸ Γ := QuotientGroup.mk' Γ
  -- ⊢ map (↑(QuotientGroup.mk' Γ)) (Measure.restrict μ 𝓕) = ↑↑μ (𝓕 ∩ ↑(QuotientGro …
  have meas_π : Measurable π := continuous_quotient_mk'.measurable
  -- ⊢ map (↑(QuotientGroup.mk' Γ)) (Measure.restrict μ 𝓕) = ↑↑μ (𝓕 ∩ ↑(QuotientGro …
  have 𝓕meas : NullMeasurableSet 𝓕 μ := h𝓕.nullMeasurableSet
  -- ⊢ map (↑(QuotientGroup.mk' Γ)) (Measure.restrict μ 𝓕) = ↑↑μ (𝓕 ∩ ↑(QuotientGro …
  haveI := Fact.mk h𝓕_finite
  -- ⊢ map (↑(QuotientGroup.mk' Γ)) (Measure.restrict μ 𝓕) = ↑↑μ (𝓕 ∩ ↑(QuotientGro …
  -- the measure is left-invariant, so by the uniqueness of Haar measure it's enough to show that
  -- it has the stated size on the reference compact set `K`.
  haveI : (Measure.map (QuotientGroup.mk' Γ) (μ.restrict 𝓕)).IsMulLeftInvariant :=
    h𝓕.isMulLeftInvariant_map
  rw [Measure.haarMeasure_unique (Measure.map (QuotientGroup.mk' Γ) (μ.restrict 𝓕)) K,
    Measure.map_apply meas_π, Measure.restrict_apply₀' 𝓕meas, inter_comm]
  exact K.isCompact.measurableSet
  -- 🎉 no goals
#align measure_theory.is_fundamental_domain.map_restrict_quotient MeasureTheory.IsFundamentalDomain.map_restrict_quotient
#align measure_theory.is_add_fundamental_domain.map_restrict_quotient MeasureTheory.IsAddFundamentalDomain.map_restrict_quotient

/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ` is
  measure-preserving between appropriate multiples of Haar measure on `G` and `G ⧸ Γ`. -/
@[to_additive MeasurePreservingQuotientAddGroup.mk' "Given a normal subgroup `Γ` of an additive
  topological group `G` with Haar measure `μ`, which is also right-invariant, and a finite volume
  fundamental domain `𝓕`, the quotient map to `G ⧸ Γ` is measure-preserving between appropriate
  multiples of Haar measure on `G` and `G ⧸ Γ`."]
theorem MeasurePreservingQuotientGroup.mk' [Subgroup.Normal Γ]
    [MeasureTheory.Measure.IsHaarMeasure μ] [μ.IsMulRightInvariant] (h𝓕_finite : μ 𝓕 < ⊤) (c : ℝ≥0)
    (h : μ (𝓕 ∩ QuotientGroup.mk' Γ ⁻¹' K) = c) :
    MeasurePreserving (QuotientGroup.mk' Γ) (μ.restrict 𝓕)
      (c • MeasureTheory.Measure.haarMeasure K) where
  measurable := continuous_quotient_mk'.measurable
  map_eq := by rw [h𝓕.map_restrict_quotient K h𝓕_finite, h]; rfl
               -- ⊢ ↑c • haarMeasure K = c • haarMeasure K
                                                             -- 🎉 no goals
#align measure_preserving_quotient_group.mk' MeasurePreservingQuotientGroup.mk'
#align measure_preserving_quotient_add_group.mk' MeasurePreservingQuotientAddGroup.mk'
