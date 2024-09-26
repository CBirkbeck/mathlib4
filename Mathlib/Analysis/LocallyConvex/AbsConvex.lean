/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Convex.Gauge

/-!
# Absolutely convex sets

A set is called absolutely convex or disked if it is convex and balanced.
The importance of absolutely convex sets comes from the fact that every locally convex
topological vector space has a basis consisting of absolutely convex sets.

## Main definitions

* `gaugeSeminormFamily`: the seminorm family induced by all open absolutely convex neighborhoods
of zero.

## Main statements

* `with_gaugeSeminormFamily`: the topology of a locally convex space is induced by the family
`gaugeSeminormFamily`.

## TODO

* Define the disked hull

## Tags

disks, convex, balanced
-/


open NormedField Set

open NNReal Pointwise Topology

variable {𝕜 E F G ι : Type*}

section NontriviallyNormedField

variable (𝕜 E) {s : Set E}
variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [Module ℝ E] [SMulCommClass ℝ 𝕜 E]
variable [TopologicalSpace E] [LocallyConvexSpace ℝ E] [ContinuousSMul 𝕜 E]

theorem nhds_basis_abs_convex :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ 𝓝 (0 : E) ∧ Balanced 𝕜 s ∧ Convex ℝ s) id := by
  refine
    (LocallyConvexSpace.convex_basis_zero ℝ E).to_hasBasis (fun s hs => ?_) fun s hs =>
      ⟨s, ⟨hs.1, hs.2.2⟩, rfl.subset⟩
  refine ⟨convexHull ℝ (balancedCore 𝕜 s), ?_, convexHull_min (balancedCore_subset s) hs.2⟩
  refine ⟨Filter.mem_of_superset (balancedCore_mem_nhds_zero hs.1) (subset_convexHull ℝ _), ?_⟩
  refine ⟨(balancedCore_balanced s).convexHull, ?_⟩
  exact convex_convexHull ℝ (balancedCore 𝕜 s)

variable [ContinuousSMul ℝ E] [TopologicalAddGroup E]

theorem nhds_basis_abs_convex_open :
    (𝓝 (0 : E)).HasBasis (fun s => (0 : E) ∈ s ∧ IsOpen s ∧ Balanced 𝕜 s ∧ Convex ℝ s) id := by
  refine (nhds_basis_abs_convex 𝕜 E).to_hasBasis ?_ ?_
  · rintro s ⟨hs_nhds, hs_balanced, hs_convex⟩
    refine ⟨interior s, ?_, interior_subset⟩
    exact
      ⟨mem_interior_iff_mem_nhds.mpr hs_nhds, isOpen_interior,
        hs_balanced.interior (mem_interior_iff_mem_nhds.mpr hs_nhds), hs_convex.interior⟩
  rintro s ⟨hs_zero, hs_open, hs_balanced, hs_convex⟩
  exact ⟨s, ⟨hs_open.mem_nhds hs_zero, hs_balanced, hs_convex⟩, rfl.subset⟩

end NontriviallyNormedField

section AbsolutelyConvex

variable (𝕜) [SeminormedRing 𝕜] [SMul 𝕜 E] [SMul ℝ E] [AddCommMonoid E]
/-- The type of absolutely convex sets. -/
def AbsConvex (s : Set E) : Prop := Balanced 𝕜 s ∧ Convex ℝ s

variable {𝕜}

theorem absConvex_empty : AbsConvex 𝕜 (∅ : Set E) := ⟨balanced_empty, convex_empty⟩

theorem absConvex_univ : AbsConvex 𝕜 (Set.univ : Set E) := ⟨balanced_univ, convex_univ⟩

theorem AbsConvex.inter {s : Set E} {t : Set E} (hs : AbsConvex 𝕜 s) (ht : AbsConvex 𝕜 t) :
    AbsConvex 𝕜 (s ∩ t) := ⟨Balanced.inter hs.1 ht.1, Convex.inter hs.2 ht.2⟩

theorem absConvex_sInter {S : Set (Set E)} (h : ∀ s ∈ S, AbsConvex 𝕜 s) : AbsConvex 𝕜 (⋂₀ S) :=
  ⟨balanced_sInter (fun s hs => (h s hs).1), convex_sInter (fun s hs => (h s hs).2)⟩

variable (𝕜)

/-- The absolute convex hull of a set `s` is the minimal absolute convex set that includes `s`. -/
@[simps! isClosed]
def absConvexHull : ClosureOperator (Set E) :=
    .ofCompletePred (AbsConvex 𝕜) fun _ ↦ absConvex_sInter

variable (s : Set E)

theorem subset_absConvexHull : s ⊆ absConvexHull 𝕜 s :=
  (absConvexHull 𝕜).le_closure s

theorem absConvex_absConvexHull : AbsConvex 𝕜 (absConvexHull 𝕜 s) :=
    (absConvexHull 𝕜).isClosed_closure s

theorem balanced_absConvexHull : Balanced 𝕜 ((absConvexHull 𝕜) s) := (absConvex_absConvexHull 𝕜 s).1

theorem convex_absConvexHull : Convex ℝ ((absConvexHull 𝕜) s) := (absConvex_absConvexHull 𝕜 s).2

theorem absConvexHull_eq_iInter :
    absConvexHull 𝕜 s = ⋂ (t : Set E) (_ : s ⊆ t) (_ : AbsConvex 𝕜 t), t := by
  simp [absConvexHull, iInter_subtype, iInter_and]

variable {𝕜 s} {t : Set E} {x y : E}

theorem mem_absConvexHull_iff : x ∈ absConvexHull 𝕜 s ↔ ∀ t, s ⊆ t → AbsConvex 𝕜 t → x ∈ t := by
  simp_rw [absConvexHull_eq_iInter, mem_iInter]

theorem absConvexHull_min : s ⊆ t → AbsConvex 𝕜 t → absConvexHull 𝕜 s ⊆ t :=
  (absConvexHull 𝕜).closure_min

theorem AbsConvex.absConvexHull_subset_iff (ht : AbsConvex 𝕜 t) : absConvexHull 𝕜 s ⊆ t ↔ s ⊆ t :=
  (show (absConvexHull 𝕜).IsClosed t from ht).closure_le_iff

@[mono, gcongr]
theorem absConvexHull_mono (hst : s ⊆ t) : absConvexHull 𝕜 s ⊆ absConvexHull 𝕜 t :=
  (absConvexHull 𝕜).monotone hst

lemma absConvexHull_eq_self : absConvexHull 𝕜 s = s ↔ AbsConvex 𝕜 s :=
  (absConvexHull 𝕜).isClosed_iff.symm

alias ⟨_, AbsConvex.absConvexHull_eq⟩ := absConvexHull_eq_self

@[simp]
theorem absConvexHull_univ : absConvexHull 𝕜 (univ : Set E) = univ :=
  ClosureOperator.closure_top (absConvexHull 𝕜)

@[simp]
theorem absConvexHull_empty : absConvexHull 𝕜 (∅ : Set E) = ∅ :=
  absConvex_empty.absConvexHull_eq

@[simp]
theorem absConvexHull_empty_iff : absConvexHull 𝕜 s = ∅ ↔ s = ∅ := by
  constructor
  · intro h
    rw [← Set.subset_empty_iff, ← h]
    exact subset_absConvexHull 𝕜 _
  · rintro rfl
    exact absConvexHull_empty

@[simp]
theorem absConvexHull_nonempty_iff : (absConvexHull 𝕜 s).Nonempty ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty, nonempty_iff_ne_empty, Ne, Ne]
  exact not_congr absConvexHull_empty_iff

protected alias ⟨_, Set.Nonempty.absConvexHull⟩ := absConvexHull_nonempty_iff

end AbsolutelyConvex

section

variable (𝕜) [NontriviallyNormedField 𝕜] --[NormOneClass 𝕜]
variable [AddCommGroup E] [Module ℝ E] [Module 𝕜 E]

theorem absConvexHull_eq_convexHull_balancedHull  [SMulCommClass ℝ 𝕜 E] {s : Set E} :
    absConvexHull 𝕜 s = convexHull ℝ (balancedHull 𝕜 s) := by
  apply le_antisymm
  · exact absConvexHull_min
      (subset_trans (subset_convexHull ℝ s) (convexHull_mono (subset_balancedHull 𝕜)))
      ⟨Balanced.convexHull (balancedHull.balanced s), convex_convexHull _ _⟩
  · rw [← Convex.convexHull_eq (convex_absConvexHull 𝕜 s)]
    exact convexHull_mono
      (Balanced.balancedHull_subset_of_subset (balanced_absConvexHull 𝕜 s)
        (subset_absConvexHull 𝕜 s))

theorem AbsConvex.hullAdd {s t : Set E} :
    absConvexHull 𝕜 (s + t) ⊆ absConvexHull 𝕜 s + absConvexHull 𝕜 t :=
  absConvexHull_min (add_subset_add (subset_absConvexHull 𝕜 s) (subset_absConvexHull 𝕜 t))
    ⟨Balanced.add (balanced_absConvexHull 𝕜 s) (balanced_absConvexHull 𝕜 t),
      Convex.add (convex_absConvexHull 𝕜 s) (convex_absConvexHull 𝕜 t)⟩

end

section

variable [AddCommGroup E] [Module ℝ E]

lemma balancedHull_subseteq_convexHull {s : Set E} : balancedHull ℝ s ⊆ convexHull ℝ (s ∪ -s) := by
  intro a ha
  obtain ⟨r, hr, y, hy, rfl⟩ := mem_balancedHull_iff.1 ha
  apply segment_subset_convexHull (mem_union_left (-s) hy) (mem_union_right _ (neg_mem_neg.mpr hy))
  use (1+r)/2
  use (1-r)/2
  constructor
  · rw [← zero_div 2]
    exact (div_le_div_right zero_lt_two).mpr (neg_le_iff_add_nonneg'.mp (neg_le_of_abs_le hr))
  · constructor
    · rw [← zero_div 2]
      exact (div_le_div_right zero_lt_two).mpr (sub_nonneg_of_le (le_of_max_le_left hr))
    · constructor
      · ring_nf
      · rw [smul_neg, ← sub_eq_add_neg, ← sub_smul]
        apply congrFun (congrArg HSMul.hSMul _) y
        ring_nf

theorem absConvexHull_eq_convexHull_union_neg {s : Set E} :
    absConvexHull ℝ s = convexHull ℝ (s ∪ -s) := by
  rw [absConvexHull_eq_convexHull_balancedHull]
  exact le_antisymm (by
    rw [← Convex.convexHull_eq (convex_convexHull ℝ (s ∪ -s)) ]
    exact convexHull_mono balancedHull_subseteq_convexHull)
    (convexHull_mono (union_subset (subset_balancedHull ℝ)
      (fun _ _ => by rw [mem_balancedHull_iff]; use -1; aesop)))

theorem absConvexHull_inter_neg_eq {s : Set E} :
    absConvexHull ℝ (s ∩ -s) = convexHull ℝ (s ∩ -s) := by
  rw [absConvexHull_eq_convexHull_union_neg, inter_neg, neg_neg, inter_comm, union_self]

end

section

variable [AddCommGroup E] [Module ℝ E]

lemma half_add_half_of_convex {V : Set E} (h : Convex ℝ V) : (1/2 : ℝ) • V + (1/2 : ℝ) • V = V := by
  apply le_antisymm
  · apply convex_iff_pointwise_add_subset.mp h (le_of_lt (half_pos Real.zero_lt_one))
      (le_of_lt (half_pos Real.zero_lt_one))
      (add_halves 1)
  · intro x hx
    have e1 : x = (1/2 : ℝ) • x + (1/2 : ℝ) • x := by
      rw [← two_smul ℝ]
      simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, smul_inv_smul₀]
    rw [e1]
    apply add_mem_add
    exact smul_mem_smul_set hx
    exact smul_mem_smul_set hx

lemma add_self_eq_smul_two {V : Set E} (h : Convex ℝ V) : V + V = (2 : ℝ) • V := by
  have v1 : Convex ℝ ((2 : ℝ) • V) := Convex.smul h 2
  rw [← half_add_half_of_convex v1]
  simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_smul_smul₀]

lemma help' (a b :E) (h : a = b) : (1/2 : ℝ) • a = (1/2 : ℝ) •b := by
  exact congrArg (HSMul.hSMul (1 / 2)) h

lemma help (a b :E) (h : (2:ℝ)•a = (2:ℝ)•b) : a = b := by
  have e1 : (1/2 : ℝ) • ((2:ℝ)•a) = (1/2 : ℝ) •((2:ℝ)•b) := by
    apply help'
    exact h
  simp at e1
  exact e1

variable (E 𝕜) {s : Set E}
variable [NontriviallyNormedField 𝕜]  [Module 𝕜 E]
variable [SMulCommClass ℝ 𝕜 E]
variable [TopologicalSpace E] [TopologicalAddGroup E]  [lcs : LocallyConvexSpace ℝ E]
  [ContinuousSMul ℝ E]

-- TVS II.25 Prop3
theorem totallyBounded_absConvexHull
    (hs : TotallyBounded (uniformSpace := TopologicalAddGroup.toUniformSpace E) s) :
    TotallyBounded (uniformSpace := TopologicalAddGroup.toUniformSpace E) (absConvexHull ℝ s) := by
  intro d' hd'
  letI := TopologicalAddGroup.toUniformSpace E
  obtain ⟨d,⟨hd₁, hd₂⟩⟩ := comp_mem_uniformity_sets hd'
  obtain ⟨N,⟨hN₁,hN₂⟩⟩ := hd₁
  obtain ⟨S,⟨hS₁,hS₂,hS₃⟩⟩ := (locallyConvexSpace_iff_exists_convex_subset_zero ℝ E).mp lcs N hN₁
  let V := S ∩ -S
  let d₂ := {(x,y) | y-x ∈ S} ∩ {(x,y) | y-x ∈ -S}
  obtain ⟨t,⟨htf,hts⟩⟩ := hs d₂ (by
    rw [uniformity_eq_comap_nhds_zero' E]
    simp_all only [Filter.inter_mem_iff, Filter.mem_comap, d₂]
    apply And.intro
    · aesop
    · use -S
      constructor
      · exact neg_mem_nhds_zero E hS₁
      · exact fun ⦃a⦄ a ↦ a
    )
  have e1 (y : E) : {x | (x, y) ∈ d₂} = y +ᵥ V := by
    apply le_antisymm
    · intro x hx
      rw [Set.mem_vadd']
      aesop
    · intro x hx
      rw [Set.mem_vadd'] at hx
      aesop
  have e2 {t₁ : Set E} : ⋃ y ∈ t₁, {x | (x, y) ∈ d₂} = t₁ + V := by
    aesop
  rw [e2] at hts
  have e3 : (absConvexHull ℝ) s ⊆ (absConvexHull ℝ) (t + V) := by
    exact absConvexHull_mono hts
  have e4 : (absConvexHull ℝ) s ⊆ ((absConvexHull ℝ) t) + (absConvexHull ℝ) V :=
    le_trans e3 (AbsConvex.hullAdd _)
  have e5 : (absConvexHull ℝ) V = V := by
    rw [AbsConvex.absConvexHull_eq]
    rw [← absConvexHull_eq_self]
    rw [absConvexHull_inter_neg_eq]
    rw [Convex.convexHull_eq]
    exact Convex.inter hS₂ (Convex.neg hS₂)
  rw [e5] at e4
  rw [absConvexHull_eq_convexHull_union_neg (s := t)] at e4
  have e6 : TotallyBounded (uniformSpace := TopologicalAddGroup.toUniformSpace E)
      ((convexHull ℝ) (t ∪ -t)) := by
    apply IsCompact.totallyBounded
    apply Set.Finite.isCompact_convexHull
    apply finite_union.mpr ⟨htf,Finite.neg htf⟩
  have e0 : d₂ = symmetrizeRel {(x,y) | y-x ∈ S} := by
    simp_all only [mem_neg, neg_sub, d₂]
    rfl
  obtain ⟨t',⟨htf',hts'⟩⟩ := e6 d₂ (by
    rw [e0]
    apply symmetrize_mem_uniformity
    rw [uniformity_eq_comap_nhds_zero']
    aesop
  )
  rw [e2] at hts'
  have e7: (absConvexHull ℝ) s ⊆ t' + (V + V) := by
    apply le_trans
    apply e4
    rw [← add_assoc]
    apply Set.add_subset_add_right
    apply hts'
  rw [add_self_eq_smul_two] at e7
  have e8 (y : E): y +ᵥ ((2 : ℝ) • V) ⊆ {x | (x, y) ∈ d'} := by
    intro x hx
    rw [mem_setOf_eq]
    rw [Set.mem_vadd'] at hx
    obtain ⟨z,⟨hz₁,hz₂⟩⟩ := hx
    apply hd₂
    rw [vadd_eq_add] at hz₂
    rw [mem_compRel]
    obtain ⟨z',⟨hz'₁,hz'₂⟩⟩ := hz₁
    simp at hz'₂
    have e11 : (1 / 2 : ℝ) • (x + y) - x = -z' := by
      rw [smul_add]
      rw [add_sub_right_comm]
      apply help
      rw [smul_add]
      rw [smul_sub]
      rw [← smul_assoc]
      simp?
      rw [add_comm]
      rw [two_smul]
      simp
      rw [← hz₂]
      simp?
      exact id (Eq.symm hz'₂)
    have e12 : y - (1 / 2 : ℝ) • (x + y) = -z' := by
      apply help
      rw [smul_sub]
      simp
      rw [two_smul]
      simp
      rw [← hz₂]
      simp
      exact id (Eq.symm hz'₂)
    use (1/2:ℝ)•(x+y)
    constructor
    · apply hN₂
      simp only [mem_preimage]
      rw [e11]
      apply hS₃
      aesop
    · apply hN₂
      simp only [mem_preimage]
      rw [e12]
      apply hS₃
      aesop
  have e9 : ⋃ y ∈ t', y +ᵥ ((2 : ℝ) • V) ⊆ ⋃ y ∈ t', {x | (x, y) ∈ d'} := by
    apply biUnion_mono
    exact fun ⦃a⦄ a ↦ a
    intro y _
    exact e8 y
  use t'
  constructor
  · exact htf'
  · apply subset_trans e7
    aesop
  apply Convex.inter
  exact hS₂
  exact Convex.neg hS₂
end

section AbsolutelyConvexSets

variable [TopologicalSpace E] [AddCommMonoid E] [Zero E] [SeminormedRing 𝕜]
variable [SMul 𝕜 E] [SMul ℝ E]
variable (𝕜 E)

/-- The type of absolutely convex open sets. -/
def AbsConvexOpenSets :=
  { s : Set E // (0 : E) ∈ s ∧ IsOpen s ∧ AbsConvex 𝕜 s }

noncomputable instance AbsConvexOpenSets.instCoeTC : CoeTC (AbsConvexOpenSets 𝕜 E) (Set E) :=
  ⟨Subtype.val⟩

namespace AbsConvexOpenSets

variable {𝕜 E}

theorem coe_zero_mem (s : AbsConvexOpenSets 𝕜 E) : (0 : E) ∈ (s : Set E) :=
  s.2.1

theorem coe_isOpen (s : AbsConvexOpenSets 𝕜 E) : IsOpen (s : Set E) :=
  s.2.2.1

theorem coe_nhds (s : AbsConvexOpenSets 𝕜 E) : (s : Set E) ∈ 𝓝 (0 : E) :=
  s.coe_isOpen.mem_nhds s.coe_zero_mem

theorem coe_balanced (s : AbsConvexOpenSets 𝕜 E) : Balanced 𝕜 (s : Set E) :=
  s.2.2.2.1

theorem coe_convex (s : AbsConvexOpenSets 𝕜 E) : Convex ℝ (s : Set E) :=
  s.2.2.2.2

end AbsConvexOpenSets

instance AbsConvexOpenSets.instNonempty : Nonempty (AbsConvexOpenSets 𝕜 E) := by
  rw [← exists_true_iff_nonempty]
  dsimp only [AbsConvexOpenSets]
  rw [Subtype.exists]
  exact ⟨Set.univ, ⟨mem_univ 0, isOpen_univ, balanced_univ, convex_univ⟩, trivial⟩

end AbsolutelyConvexSets

variable [RCLike 𝕜]
variable [AddCommGroup E] [TopologicalSpace E]
variable [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
variable [ContinuousSMul ℝ E]
variable (𝕜 E)

/-- The family of seminorms defined by the gauges of absolute convex open sets. -/
noncomputable def gaugeSeminormFamily : SeminormFamily 𝕜 E (AbsConvexOpenSets 𝕜 E) := fun s =>
  gaugeSeminorm s.coe_balanced s.coe_convex (absorbent_nhds_zero s.coe_nhds)

variable {𝕜 E}

theorem gaugeSeminormFamily_ball (s : AbsConvexOpenSets 𝕜 E) :
    (gaugeSeminormFamily 𝕜 E s).ball 0 1 = (s : Set E) := by
  dsimp only [gaugeSeminormFamily]
  rw [Seminorm.ball_zero_eq]
  simp_rw [gaugeSeminorm_toFun]
  exact gauge_lt_one_eq_self_of_isOpen s.coe_convex s.coe_zero_mem s.coe_isOpen

variable [TopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable [SMulCommClass ℝ 𝕜 E] [LocallyConvexSpace ℝ E]

/-- The topology of a locally convex space is induced by the gauge seminorm family. -/
theorem with_gaugeSeminormFamily : WithSeminorms (gaugeSeminormFamily 𝕜 E) := by
  refine SeminormFamily.withSeminorms_of_hasBasis _ ?_
  refine (nhds_basis_abs_convex_open 𝕜 E).to_hasBasis (fun s hs => ?_) fun s hs => ?_
  · refine ⟨s, ⟨?_, rfl.subset⟩⟩
    convert (gaugeSeminormFamily _ _).basisSets_singleton_mem ⟨s, hs⟩ one_pos
    rw [gaugeSeminormFamily_ball, Subtype.coe_mk]
  refine ⟨s, ⟨?_, rfl.subset⟩⟩
  rw [SeminormFamily.basisSets_iff] at hs
  rcases hs with ⟨t, r, hr, rfl⟩
  rw [Seminorm.ball_finset_sup_eq_iInter _ _ _ hr]
  -- We have to show that the intersection contains zero, is open, balanced, and convex
  refine
    ⟨mem_iInter₂.mpr fun _ _ => by simp [Seminorm.mem_ball_zero, hr],
      isOpen_biInter_finset fun S _ => ?_,
      balanced_iInter₂ fun _ _ => Seminorm.balanced_ball_zero _ _,
      convex_iInter₂ fun _ _ => Seminorm.convex_ball _ _ _⟩
  -- The only nontrivial part is to show that the ball is open
  have hr' : r = ‖(r : 𝕜)‖ * 1 := by simp [abs_of_pos hr]
  have hr'' : (r : 𝕜) ≠ 0 := by simp [hr.ne']
  rw [hr', ← Seminorm.smul_ball_zero hr'', gaugeSeminormFamily_ball]
  exact S.coe_isOpen.smul₀ hr''
