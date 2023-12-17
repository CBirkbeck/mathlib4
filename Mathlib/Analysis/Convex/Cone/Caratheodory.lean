import Mathlib.Analysis.Convex.Cone.Pointed
import Mathlib.Analysis.Convex.Caratheodory

universe u

open Set Finset

open BigOperators

def toPointedCone (𝕜 : Type*) {E : Type u} [LinearOrderedField 𝕜] [AddCommGroup E]
    [Module 𝕜 E] (s : Set E) :=
  Submodule.span {c : 𝕜 // 0 ≤ c} s

variable {𝕜 : Type*} {E : Type u} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

local notation3 "𝕜≥0" => {c : 𝕜 // 0 ≤ c}

namespace Caratheodory

-- theorem toPointedCone_eq_union_toPointedCone_finite_subsets (s : Set E) :
--     toPointedCone 𝕜 s = ⋃ (t : Finset E) (w : ↑t ⊆ s), toPointedCone 𝕜 ↑t := by sorry

example (t : Finset E) (g : t → 𝕜) :
  ∑ i : t, g i = ∑ i in t, Function.extend Subtype.val g 0 i := by sorry

theorem mem_toPointedCone_erase [DecidableEq E] {t : Finset E}
    (h : ¬LinearIndependent 𝕜 ((↑) : t → E))
    {x : E} (hx : x ∈ toPointedCone 𝕜 t) :
    ∃ y : (↑t : Set E), x ∈ toPointedCone 𝕜 (↑(t.erase y) : Set E) := by
  replace ⟨f, combo⟩ := mem_span_finset.1 hx
  replace ⟨g, relation, c, hnzero⟩ := Fintype.not_linearIndependent_iff.1 h

  simp only [toPointedCone, mem_span_finset, mem_span_finset, coe_sort_coe, coe_mem,
    not_true_eq_false, Subtype.exists, exists_prop]

  by_cases hf : ∃ i₀, i₀ ∈ t ∧ f i₀ = 0
  · replace ⟨i₀, hi₀t, hf⟩ := hf
    use i₀, hi₀t, f
    rwa [sum_erase_eq_sub, hf, zero_smul, sub_zero, combo]
  · push_neg at hf
    have hf' : ∀ i ∈ t, 0 < f i := by
      intro i hi
      specialize hf i hi
      exact zero_lt_iff.mpr hf
    clear hf

    let g' := Function.extend Subtype.val g 0

    obtain (hneg | hpos) := Ne.lt_or_lt hnzero
    · let s := @Finset.filter _ (fun z => g' z < 0) (fun _ => LinearOrder.decidableLT _ _) t
      obtain ⟨d, hd₁, hd₂⟩ := s.exists_min_image (fun z => g' z / f z) $ ⟨c, by {
        simp only [filter_congr_decidable, Subtype.exists, exists_prop, exists_eq_right, not_lt,
          mem_filter, coe_mem, exists_apply_eq_apply, not_true_eq_false, true_and]
        rwa [Function.Injective.extend_apply Subtype.val_injective] }⟩
      rw [mem_filter] at hd₁
      use d
      constructor
      · aesop
      · let k : E → 𝕜≥0 := fun z => ⟨f z - f d / g' d * g' z, by {
        -- proof that the image consists of non-negative elements
        rw [sub_nonneg]
        by_cases hzt : z ∈ t
        · by_cases hzs : z ∈ s
          · specialize hd₂ z hzs
            rw [mem_filter] at hzs
            rwa [← div_le_iff_of_neg hzs.2, ← inv_le_inv_of_neg, inv_div, inv_div]
            · exact div_neg_of_pos_of_neg (hf' d hd₁.1) hd₁.2
            · exact div_neg_of_pos_of_neg (hf' z hzt) hzs.2
          · rw [mem_filter] at hzs
            push_neg at hzs
            specialize hzs hzt
            exact le_trans (mul_nonpos_of_nonpos_of_nonneg
              (div_nonpos_of_nonneg_of_nonpos (zero_le $ f d) $ le_of_lt hd₁.2) hzs) $ zero_le (f z)
        · have : g' z = 0 := by
            simp only [Subtype.exists, exists_prop, exists_eq_right, Function.extend_apply']
            aesop
          rw [this, mul_zero]
          exact zero_le (f z) }⟩
        use k
        rw [sum_erase]
        · simp
          simp_rw [sub_smul]
          simp only [Nonneg.coe_smul, Subtype.exists, exists_prop, exists_eq_right, sum_sub_distrib]
          rw [combo]
          simp only [Subtype.exists, exists_prop, exists_eq_right, sub_eq_self]
          simp_rw [mul_smul, ← Finset.smul_sum]
          convert smul_zero (f d / g' d)
          rw [← relation]
          conv_lhs => rw [←Finset.sum_coe_sort]
          apply Finset.sum_congr rfl ?_
          rintro _ -
          rw [Function.Injective.extend_apply]
          exact Subtype.val_injective
        · have : k d = 0 := by
            rw [Nonneg.mk_eq_zero, div_mul_cancel, sub_self]
            apply ne_of_lt hd₁.2
          rw [this, zero_smul]
    · sorry

variable {s : Set E} {x : E} (hx : x ∈ toPointedCone 𝕜 s)

/-- Given a point `x` in the convex hull of a set `s`, this is a finite subset of `s` of minimum
cardinality, whose convex hull contains `x`. -/
noncomputable def minCardFinsetOfMemtoPointedCone (hx : x ∈ toPointedCone 𝕜 s) : Finset E :=
  Function.argminOn Finset.card Nat.lt_wfRel.2 { t | ↑t ⊆ s ∧ x ∈ toPointedCone 𝕜 (t : Set E) } <| by exact Submodule.mem_span_finite_of_mem_span hx

theorem minCardFinsetOftoPointedCone_subseteq : ↑(minCardFinsetOfMemtoPointedCone hx) ⊆ s := (Function.argminOn_mem _ _ { t : Finset E | ↑t ⊆ s ∧ x ∈ toPointedCone 𝕜 (t : Set E) } _).1

theorem mem_minCardFinsetOfMemtoPointedCone :
    x ∈ toPointedCone 𝕜 (minCardFinsetOfMemtoPointedCone hx : Set E) := by sorry
  -- have := Function.argminOn_mem _ _ { t : Finset E | ↑t ⊆ s ∧ x ∈ toPointedCone 𝕜 (t : Set E) } _).2
  -- (Function.argminOn_mem _ _ { t : Finset E | ↑t ⊆ s ∧ x ∈ toPointedCone 𝕜 (t : Set E) } _).2
  -- simp_rw [Function.argminOn_mem]

#exit
theorem minCardFinsetOfMemtoPointedCone_nonempty : (minCardFinsetOfMemtoPointedCone hx).Nonempty := by
  simp_rw [← Finset.coe_nonempty]
  -- exact ⟨x, mem_minCardFinsetOfMemtoPointedCone hx⟩

theorem minCardFinsetOfMemtoPointedCone_card_le_card {t : Finset E} (ht₁ : ↑t ⊆ s)
    (ht₂ : x ∈ toPointedCone 𝕜 (t : Set E)) : (minCardFinsetOfMemtoPointedCone hx).card ≤ t.card :=
  Function.argminOn_le _ _ _ (by exact ⟨ht₁, ht₂⟩)

theorem affineIndependent_minCardFinsetOfMemtoPointedCone :
    AffineIndependent 𝕜 ((↑) : minCardFinsetOfMemtoPointedCone hx → E) := by
  let k := (minCardFinsetOfMemtoPointedCone hx).card - 1
  have hk : (minCardFinsetOfMemtoPointedCone hx).card = k + 1 :=
    (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr (minCardFinsetOfMemtoPointedCone_nonempty hx))).symm
  classical
  by_contra h
  obtain ⟨p, hp⟩ := mem_toPointedCone_erase h (mem_minCardFinsetOfMemtoPointedCone hx)
  have contra := minCardFinsetOfMemtoPointedCone_card_le_card hx (Set.Subset.trans
    (Finset.erase_subset (p : E) (minCardFinsetOfMemtoPointedCone hx))
    (minCardFinsetOfMemtoPointedCone_subseteq hx)) hp
  rw [← not_lt] at contra
  apply contra
  erw [card_erase_of_mem p.2, hk]
  exact lt_add_one _
#align caratheodory.affine_independent_min_card_finset_of_mem_convex_hull Caratheodory.affineIndependent_minCardFinsetOfMemtoPointedCone

end Caratheodory

variable {s : Set E}

/-- **Carathéodory's convexity theorem** -/
theorem toPointedCone_eq_union : toPointedCone 𝕜 s =
    ⋃ (t : Finset E) (hss : ↑t ⊆ s) (hai : AffineIndependent 𝕜 ((↑) : t → E)), toPointedCone 𝕜 ↑t := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [exists_prop, Set.mem_iUnion]
    exact ⟨Caratheodory.minCardFinsetOfMemtoPointedCone hx,
      Caratheodory.minCardFinsetOfMemtoPointedCone_subseteq hx,
      Caratheodory.affineIndependent_minCardFinsetOfMemtoPointedCone hx,
      Caratheodory.mem_minCardFinsetOfMemtoPointedCone hx⟩
  · iterate 3 convert Set.iUnion_subset _; intro
    exact toPointedCone_mono ‹_›
#align convex_hull_eq_union toPointedCone_eq_union

/-- A more explicit version of `toPointedCone_eq_union`. -/
theorem eq_pos_convex_span_of_mem_toPointedCone {x : E} (hx : x ∈ toPointedCone 𝕜 s) :
    ∃ (ι : Sort (u + 1)) (_ : Fintype ι),
      ∃ (z : ι → E) (w : ι → 𝕜) (_ : Set.range z ⊆ s) (_ : AffineIndependent 𝕜 z)
        (_ : ∀ i, 0 < w i), ∑ i, w i = 1 ∧ ∑ i, w i • z i = x := by
  rw [toPointedCone_eq_union] at hx
  simp only [exists_prop, Set.mem_iUnion] at hx
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := hx
  simp only [t.toPointedCone_eq, exists_prop, Set.mem_setOf_eq] at ht₃
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := ht₃
  let t' := t.filter fun i => w i ≠ 0
  refine' ⟨t', t'.fintypeCoeSort, ((↑) : t' → E), w ∘ ((↑) : t' → E), _, _, _, _, _⟩
  · rw [Subtype.range_coe_subtype]
    exact Subset.trans (Finset.filter_subset _ t) ht₁
  · exact ht₂.comp_embedding ⟨_, inclusion_injective (Finset.filter_subset (fun i => w i ≠ 0) t)⟩
  · exact fun i =>
      (hw₁ _ (Finset.mem_filter.mp i.2).1).lt_of_ne (Finset.mem_filter.mp i.property).2.symm
  · erw [Finset.sum_attach, Finset.sum_filter_ne_zero, hw₂]
  · change (∑ i : t' in t'.attach, (fun e => w e • e) ↑i) = x
    erw [Finset.sum_attach (f := fun e => w e • e), Finset.sum_filter_of_ne]
    · rw [t.centerMass_eq_of_sum_1 id hw₂] at hw₃
      exact hw₃
    · intro e _ hwe contra
      apply hwe
      rw [contra, zero_smul]
#align eq_pos_convex_span_of_mem_convex_hull eq_pos_convex_span_of_mem_toPointedCone
