/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.Order.LiminfLimsup

#align_import analysis.normed_space.lp_space from "leanprover-community/mathlib"@"de83b43717abe353f425855fcf0cedf9ea0fe8a4"

/-!
# ℓp space

This file describes properties of elements `f` of a pi-type `∀ i, E i` with finite "norm",
defined for `p:ℝ≥0∞` as the size of the support of `f` if `p=0`, `(∑' a, ‖f a‖^p) ^ (1/p)` for
`0 < p < ∞` and `⨆ a, ‖f a‖` for `p=∞`.

The Prop-valued `Memℓp f p` states that a function `f : ∀ i, E i` has finite norm according
to the above definition; that is, `f` has finite support if `p = 0`, `Summable (fun a ↦ ‖f a‖^p)` if
`0 < p < ∞`, and `BddAbove (norm '' (Set.range f))` if `p = ∞`.

The space `lp E p` is the subtype of elements of `∀ i : α, E i` which satisfy `Memℓp f p`. For
`1 ≤ p`, the "norm" is genuinely a norm and `lp` is a complete metric space.

## Main definitions

* `Memℓp f p` : property that the function `f` satisfies, as appropriate, `f` finitely supported
  if `p = 0`, `Summable (fun a ↦ ‖f a‖^p)` if `0 < p < ∞`, and `BddAbove (norm '' (Set.range f))` if
  `p = ∞`.
* `lp E p` : elements of `∀ i : α, E i` such that `Memℓp f p`. Defined as an `AddSubgroup` of
  a type synonym `PreLp` for `∀ i : α, E i`, and equipped with a `NormedAddCommGroup` structure.
  Under appropriate conditions, this is also equipped with the instances `lp.normedSpace`,
  `lp.completeSpace`. For `p=∞`, there is also `lp.inftyNormedRing`,
  `lp.inftyNormedAlgebra`, `lp.inftyStarRing` and `lp.inftyCstarRing`.

## Main results

* `Memℓp.of_exponent_ge`: For `q ≤ p`, a function which is `Memℓp` for `q` is also `Memℓp` for `p`.
* `lp.memℓp_of_tendsto`, `lp.norm_le_of_tendsto`: A pointwise limit of functions in `lp`, all with
  `lp` norm `≤ C`, is itself in `lp` and has `lp` norm `≤ C`.
* `lp.tsum_mul_le_mul_norm`: basic form of Hölder's inequality

## Implementation

Since `lp` is defined as an `AddSubgroup`, dot notation does not work. Use `lp.norm_neg f` to
say that `‖-f‖ = ‖f‖`, instead of the non-working `f.norm_neg`.

## TODO

* More versions of Hölder's inequality (for example: the case `p = 1`, `q = ∞`; a version for normed
  rings which has `‖∑' i, f i * g i‖` rather than `∑' i, ‖f i‖ * g i‖` on the RHS; a version for
  three exponents satisfying `1 / r = 1 / p + 1 / q`)

-/

set_option autoImplicit true


local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

noncomputable section

open scoped NNReal ENNReal BigOperators Function

variable {α : Type*} {E : α → Type*} {p q : ℝ≥0∞} [∀ i, NormedAddCommGroup (E i)]

/-!
### `Memℓp` predicate

-/


/-- The property that `f : ∀ i : α, E i`
* is finitely supported, if `p = 0`, or
* admits an upper bound for `Set.range (fun i ↦ ‖f i‖)`, if `p = ∞`, or
* has the series `∑' i, ‖f i‖ ^ p` be summable, if `0 < p < ∞`. -/
def Memℓp (f : ∀ i, E i) (p : ℝ≥0∞) : Prop :=
  if p = 0 then Set.Finite { i | f i ≠ 0 }
  else if p = ∞ then BddAbove (Set.range fun i => ‖f i‖)
  else Summable fun i => ‖f i‖ ^ p.toReal
#align mem_ℓp Memℓp

theorem memℓp_zero_iff {f : ∀ i, E i} : Memℓp f 0 ↔ Set.Finite { i | f i ≠ 0 } := by
  dsimp [Memℓp]
  -- ⊢ (if 0 = 0 then Set.Finite {i | ¬f i = 0} else if 0 = ⊤ then BddAbove (Set.ra …
  rw [if_pos rfl]
  -- 🎉 no goals
#align mem_ℓp_zero_iff memℓp_zero_iff

theorem memℓp_zero {f : ∀ i, E i} (hf : Set.Finite { i | f i ≠ 0 }) : Memℓp f 0 :=
  memℓp_zero_iff.2 hf
#align mem_ℓp_zero memℓp_zero

theorem memℓp_infty_iff {f : ∀ i, E i} : Memℓp f ∞ ↔ BddAbove (Set.range fun i => ‖f i‖) := by
  dsimp [Memℓp]
  -- ⊢ (if ⊤ = 0 then Set.Finite {i | ¬f i = 0} else if ⊤ = ⊤ then BddAbove (Set.ra …
  rw [if_neg ENNReal.top_ne_zero, if_pos rfl]
  -- 🎉 no goals
#align mem_ℓp_infty_iff memℓp_infty_iff

theorem memℓp_infty {f : ∀ i, E i} (hf : BddAbove (Set.range fun i => ‖f i‖)) : Memℓp f ∞ :=
  memℓp_infty_iff.2 hf
#align mem_ℓp_infty memℓp_infty

theorem memℓp_gen_iff (hp : 0 < p.toReal) {f : ∀ i, E i} :
    Memℓp f p ↔ Summable fun i => ‖f i‖ ^ p.toReal := by
  rw [ENNReal.toReal_pos_iff] at hp
  -- ⊢ Memℓp f p ↔ Summable fun i => ‖f i‖ ^ ENNReal.toReal p
  dsimp [Memℓp]
  -- ⊢ (if p = 0 then Set.Finite {i | ¬f i = 0} else if p = ⊤ then BddAbove (Set.ra …
  rw [if_neg hp.1.ne', if_neg hp.2.ne]
  -- 🎉 no goals
#align mem_ℓp_gen_iff memℓp_gen_iff

theorem memℓp_gen {f : ∀ i, E i} (hf : Summable fun i => ‖f i‖ ^ p.toReal) : Memℓp f p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    -- ⊢ Set.Finite {i | f i ≠ 0}
    have H : Summable fun _ : α => (1 : ℝ) := by simpa using hf
    -- ⊢ Set.Finite {i | f i ≠ 0}
    exact (Set.Finite.of_summable_const (by norm_num) H).subset (Set.subset_univ _)
    -- 🎉 no goals
  · apply memℓp_infty
    -- ⊢ BddAbove (Set.range fun i => ‖f i‖)
    have H : Summable fun _ : α => (1 : ℝ) := by simpa using hf
    -- ⊢ BddAbove (Set.range fun i => ‖f i‖)
    simpa using ((Set.Finite.of_summable_const (by norm_num) H).image fun i => ‖f i‖).bddAbove
    -- 🎉 no goals
  exact (memℓp_gen_iff hp).2 hf
  -- 🎉 no goals
#align mem_ℓp_gen memℓp_gen

theorem memℓp_gen' {C : ℝ} {f : ∀ i, E i} (hf : ∀ s : Finset α, ∑ i in s, ‖f i‖ ^ p.toReal ≤ C) :
    Memℓp f p := by
  apply memℓp_gen
  -- ⊢ Summable fun i => ‖f i‖ ^ ENNReal.toReal p
  use ⨆ s : Finset α, ∑ i in s, ‖f i‖ ^ p.toReal
  -- ⊢ HasSum (fun i => ‖f i‖ ^ ENNReal.toReal p) (⨆ (s : Finset α), ∑ i in s, ‖f i …
  apply hasSum_of_isLUB_of_nonneg
  -- ⊢ ∀ (i : α), 0 ≤ ‖f i‖ ^ ENNReal.toReal p
  · intro b
    -- ⊢ 0 ≤ ‖f b‖ ^ ENNReal.toReal p
    exact Real.rpow_nonneg_of_nonneg (norm_nonneg _) _
    -- 🎉 no goals
  apply isLUB_ciSup
  -- ⊢ BddAbove (Set.range fun s => ∑ i in s, ‖f i‖ ^ ENNReal.toReal p)
  use C
  -- ⊢ C ∈ upperBounds (Set.range fun s => ∑ i in s, ‖f i‖ ^ ENNReal.toReal p)
  rintro - ⟨s, rfl⟩
  -- ⊢ (fun s => ∑ i in s, ‖f i‖ ^ ENNReal.toReal p) s ≤ C
  exact hf s
  -- 🎉 no goals
#align mem_ℓp_gen' memℓp_gen'

theorem zero_memℓp : Memℓp (0 : ∀ i, E i) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    -- ⊢ Set.Finite {i | OfNat.ofNat 0 i ≠ 0}
    simp
    -- 🎉 no goals
  · apply memℓp_infty
    -- ⊢ BddAbove (Set.range fun i => ‖OfNat.ofNat 0 i‖)
    simp only [norm_zero, Pi.zero_apply]
    -- ⊢ BddAbove (Set.range fun i => 0)
    exact bddAbove_singleton.mono Set.range_const_subset
    -- 🎉 no goals
  · apply memℓp_gen
    -- ⊢ Summable fun i => ‖OfNat.ofNat 0 i‖ ^ ENNReal.toReal p
    simp [Real.zero_rpow hp.ne', summable_zero]
    -- 🎉 no goals
#align zero_mem_ℓp zero_memℓp

theorem zero_mem_ℓp' : Memℓp (fun i : α => (0 : E i)) p :=
  zero_memℓp
#align zero_mem_ℓp' zero_mem_ℓp'

namespace Memℓp

theorem finite_dsupport {f : ∀ i, E i} (hf : Memℓp f 0) : Set.Finite { i | f i ≠ 0 } :=
  memℓp_zero_iff.1 hf
#align mem_ℓp.finite_dsupport Memℓp.finite_dsupport

theorem bddAbove {f : ∀ i, E i} (hf : Memℓp f ∞) : BddAbove (Set.range fun i => ‖f i‖) :=
  memℓp_infty_iff.1 hf
#align mem_ℓp.bdd_above Memℓp.bddAbove

theorem summable (hp : 0 < p.toReal) {f : ∀ i, E i} (hf : Memℓp f p) :
    Summable fun i => ‖f i‖ ^ p.toReal :=
  (memℓp_gen_iff hp).1 hf
#align mem_ℓp.summable Memℓp.summable

theorem neg {f : ∀ i, E i} (hf : Memℓp f p) : Memℓp (-f) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    -- ⊢ Set.Finite {i | (-f) i ≠ 0}
    simp [hf.finite_dsupport]
    -- 🎉 no goals
  · apply memℓp_infty
    -- ⊢ BddAbove (Set.range fun i => ‖(-f) i‖)
    simpa using hf.bddAbove
    -- 🎉 no goals
  · apply memℓp_gen
    -- ⊢ Summable fun i => ‖(-f) i‖ ^ ENNReal.toReal p
    simpa using hf.summable hp
    -- 🎉 no goals
#align mem_ℓp.neg Memℓp.neg

@[simp]
theorem neg_iff {f : ∀ i, E i} : Memℓp (-f) p ↔ Memℓp f p :=
  ⟨fun h => neg_neg f ▸ h.neg, Memℓp.neg⟩
#align mem_ℓp.neg_iff Memℓp.neg_iff

theorem of_exponent_ge {p q : ℝ≥0∞} {f : ∀ i, E i} (hfq : Memℓp f q) (hpq : q ≤ p) : Memℓp f p := by
  rcases ENNReal.trichotomy₂ hpq with
    (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hp⟩ | ⟨rfl, rfl⟩ | ⟨hq, rfl⟩ | ⟨hq, _, hpq'⟩)
  · exact hfq
    -- 🎉 no goals
  · apply memℓp_infty
    -- ⊢ BddAbove (Set.range fun i => ‖f i‖)
    obtain ⟨C, hC⟩ := (hfq.finite_dsupport.image fun i => ‖f i‖).bddAbove
    -- ⊢ BddAbove (Set.range fun i => ‖f i‖)
    use max 0 C
    -- ⊢ max 0 C ∈ upperBounds (Set.range fun i => ‖f i‖)
    rintro x ⟨i, rfl⟩
    -- ⊢ (fun i => ‖f i‖) i ≤ max 0 C
    by_cases hi : f i = 0
    -- ⊢ (fun i => ‖f i‖) i ≤ max 0 C
    · simp [hi]
      -- 🎉 no goals
    · exact (hC ⟨i, hi, rfl⟩).trans (le_max_right _ _)
      -- 🎉 no goals
  · apply memℓp_gen
    -- ⊢ Summable fun i => ‖f i‖ ^ ENNReal.toReal p
    have : ∀ (i) (_ : i ∉ hfq.finite_dsupport.toFinset), ‖f i‖ ^ p.toReal = 0 := by
      intro i hi
      have : f i = 0 := by simpa using hi
      simp [this, Real.zero_rpow hp.ne']
    exact summable_of_ne_finset_zero this
    -- 🎉 no goals
  · exact hfq
    -- 🎉 no goals
  · apply memℓp_infty
    -- ⊢ BddAbove (Set.range fun i => ‖f i‖)
    obtain ⟨A, hA⟩ := (hfq.summable hq).tendsto_cofinite_zero.bddAbove_range_of_cofinite
    -- ⊢ BddAbove (Set.range fun i => ‖f i‖)
    use A ^ q.toReal⁻¹
    -- ⊢ A ^ (ENNReal.toReal q)⁻¹ ∈ upperBounds (Set.range fun i => ‖f i‖)
    rintro x ⟨i, rfl⟩
    -- ⊢ (fun i => ‖f i‖) i ≤ A ^ (ENNReal.toReal q)⁻¹
    have : 0 ≤ ‖f i‖ ^ q.toReal := Real.rpow_nonneg_of_nonneg (norm_nonneg _) _
    -- ⊢ (fun i => ‖f i‖) i ≤ A ^ (ENNReal.toReal q)⁻¹
    simpa [← Real.rpow_mul, mul_inv_cancel hq.ne'] using
      Real.rpow_le_rpow this (hA ⟨i, rfl⟩) (inv_nonneg.mpr hq.le)
  · apply memℓp_gen
    -- ⊢ Summable fun i => ‖f i‖ ^ ENNReal.toReal p
    have hf' := hfq.summable hq
    -- ⊢ Summable fun i => ‖f i‖ ^ ENNReal.toReal p
    refine' summable_of_norm_bounded_eventually _ hf' (@Set.Finite.subset _ { i | 1 ≤ ‖f i‖ } _ _ _)
    -- ⊢ Set.Finite {i | 1 ≤ ‖f i‖}
    · have H : { x : α | 1 ≤ ‖f x‖ ^ q.toReal }.Finite := by
        simpa using eventually_lt_of_tendsto_lt (by norm_num) hf'.tendsto_cofinite_zero
      exact H.subset fun i hi => Real.one_le_rpow hi hq.le
      -- 🎉 no goals
    · show ∀ i, ¬|‖f i‖ ^ p.toReal| ≤ ‖f i‖ ^ q.toReal → 1 ≤ ‖f i‖
      -- ⊢ ∀ (i : α), ¬|‖f i‖ ^ ENNReal.toReal p| ≤ ‖f i‖ ^ ENNReal.toReal q → 1 ≤ ‖f i‖
      intro i hi
      -- ⊢ 1 ≤ ‖f i‖
      have : 0 ≤ ‖f i‖ ^ p.toReal := Real.rpow_nonneg_of_nonneg (norm_nonneg _) p.toReal
      -- ⊢ 1 ≤ ‖f i‖
      simp only [abs_of_nonneg, this] at hi
      -- ⊢ 1 ≤ ‖f i‖
      contrapose! hi
      -- ⊢ ‖f i‖ ^ ENNReal.toReal p ≤ ‖f i‖ ^ ENNReal.toReal q
      exact Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hi.le hq.le hpq'
      -- 🎉 no goals
#align mem_ℓp.of_exponent_ge Memℓp.of_exponent_ge

theorem add {f g : ∀ i, E i} (hf : Memℓp f p) (hg : Memℓp g p) : Memℓp (f + g) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    -- ⊢ Set.Finite {i | (f + g) i ≠ 0}
    refine' (hf.finite_dsupport.union hg.finite_dsupport).subset fun i => _
    -- ⊢ i ∈ {i | (f + g) i ≠ 0} → i ∈ {i | f i ≠ 0} ∪ {i | g i ≠ 0}
    simp only [Pi.add_apply, Ne.def, Set.mem_union, Set.mem_setOf_eq]
    -- ⊢ ¬f i + g i = 0 → ¬f i = 0 ∨ ¬g i = 0
    contrapose!
    -- ⊢ f i = 0 ∧ g i = 0 → f i + g i = 0
    rintro ⟨hf', hg'⟩
    -- ⊢ f i + g i = 0
    simp [hf', hg']
    -- 🎉 no goals
  · apply memℓp_infty
    -- ⊢ BddAbove (Set.range fun i => ‖(f + g) i‖)
    obtain ⟨A, hA⟩ := hf.bddAbove
    -- ⊢ BddAbove (Set.range fun i => ‖(f + g) i‖)
    obtain ⟨B, hB⟩ := hg.bddAbove
    -- ⊢ BddAbove (Set.range fun i => ‖(f + g) i‖)
    refine' ⟨A + B, _⟩
    -- ⊢ A + B ∈ upperBounds (Set.range fun i => ‖(f + g) i‖)
    rintro a ⟨i, rfl⟩
    -- ⊢ (fun i => ‖(f + g) i‖) i ≤ A + B
    exact le_trans (norm_add_le _ _) (add_le_add (hA ⟨i, rfl⟩) (hB ⟨i, rfl⟩))
    -- 🎉 no goals
  apply memℓp_gen
  -- ⊢ Summable fun i => ‖(f + g) i‖ ^ ENNReal.toReal p
  let C : ℝ := if p.toReal < 1 then 1 else (2 : ℝ) ^ (p.toReal - 1)
  -- ⊢ Summable fun i => ‖(f + g) i‖ ^ ENNReal.toReal p
  refine'
    summable_of_nonneg_of_le _ (fun i => _) (((hf.summable hp).add (hg.summable hp)).mul_left C)
  · exact fun b => Real.rpow_nonneg_of_nonneg (norm_nonneg (f b + g b)) p.toReal
    -- 🎉 no goals
  · refine' (Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) hp.le).trans _
    -- ⊢ (‖f i‖ + ‖g i‖) ^ ENNReal.toReal p ≤ C * (‖f i‖ ^ ENNReal.toReal p + ‖g i‖ ^ …
    dsimp only
    -- ⊢ (‖f i‖ + ‖g i‖) ^ ENNReal.toReal p ≤ (if ENNReal.toReal p < 1 then 1 else 2  …
    split_ifs with h
    -- ⊢ (‖f i‖ + ‖g i‖) ^ ENNReal.toReal p ≤ 1 * (‖f i‖ ^ ENNReal.toReal p + ‖g i‖ ^ …
    · simpa using NNReal.coe_le_coe.2 (NNReal.rpow_add_le_add_rpow ‖f i‖₊ ‖g i‖₊ hp.le h.le)
      -- 🎉 no goals
    · let F : Fin 2 → ℝ≥0 := ![‖f i‖₊, ‖g i‖₊]
      -- ⊢ (‖f i‖ + ‖g i‖) ^ ENNReal.toReal p ≤ 2 ^ (ENNReal.toReal p - 1) * (‖f i‖ ^ E …
      simp only [not_lt] at h
      -- ⊢ (‖f i‖ + ‖g i‖) ^ ENNReal.toReal p ≤ 2 ^ (ENNReal.toReal p - 1) * (‖f i‖ ^ E …
      simpa [Fin.sum_univ_succ] using
        Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Finset.univ h fun i _ => (F i).coe_nonneg
#align mem_ℓp.add Memℓp.add

theorem sub {f g : ∀ i, E i} (hf : Memℓp f p) (hg : Memℓp g p) : Memℓp (f - g) p := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg
  -- ⊢ Memℓp (f + -g) p
                       -- 🎉 no goals
#align mem_ℓp.sub Memℓp.sub

theorem finset_sum {ι} (s : Finset ι) {f : ι → ∀ i, E i} (hf : ∀ i ∈ s, Memℓp (f i) p) :
    Memℓp (fun a => ∑ i in s, f i a) p := by
  haveI : DecidableEq ι := Classical.decEq _
  -- ⊢ Memℓp (fun a => ∑ i in s, f i a) p
  revert hf
  -- ⊢ (∀ (i : ι), i ∈ s → Memℓp (f i) p) → Memℓp (fun a => ∑ i in s, f i a) p
  refine' Finset.induction_on s _ _
  -- ⊢ (∀ (i : ι), i ∈ ∅ → Memℓp (f i) p) → Memℓp (fun a => ∑ i in ∅, f i a) p
  · simp only [zero_mem_ℓp', Finset.sum_empty, imp_true_iff]
    -- 🎉 no goals
  · intro i s his ih hf
    -- ⊢ Memℓp (fun a => ∑ i in insert i s, f i a) p
    simp only [his, Finset.sum_insert, not_false_iff]
    -- ⊢ Memℓp (fun a => f i a + ∑ i in s, f i a) p
    exact (hf i (s.mem_insert_self i)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
    -- 🎉 no goals
#align mem_ℓp.finset_sum Memℓp.finset_sum

section BoundedSMul

variable {𝕜 : Type*} [NormedRing 𝕜] [∀ i, Module 𝕜 (E i)] [∀ i, BoundedSMul 𝕜 (E i)]

theorem const_smul {f : ∀ i, E i} (hf : Memℓp f p) (c : 𝕜) : Memℓp (c • f) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    -- ⊢ Set.Finite {i | (c • f) i ≠ 0}
    refine' hf.finite_dsupport.subset fun i => (_ : ¬c • f i = 0 → ¬f i = 0)
    -- ⊢ ¬c • f i = 0 → ¬f i = 0
    exact not_imp_not.mpr fun hf' => hf'.symm ▸ smul_zero c
    -- 🎉 no goals
  · obtain ⟨A, hA⟩ := hf.bddAbove
    -- ⊢ Memℓp (c • f) ⊤
    refine' memℓp_infty ⟨‖c‖ * A, _⟩
    -- ⊢ ‖c‖ * A ∈ upperBounds (Set.range fun i => ‖(c • f) i‖)
    rintro a ⟨i, rfl⟩
    -- ⊢ (fun i => ‖(c • f) i‖) i ≤ ‖c‖ * A
    refine' (norm_smul_le _ _).trans _
    -- ⊢ ‖c‖ * ‖f i‖ ≤ ‖c‖ * A
    exact mul_le_mul_of_nonneg_left (hA ⟨i, rfl⟩) (norm_nonneg c)
    -- 🎉 no goals
  · apply memℓp_gen
    -- ⊢ Summable fun i => ‖(c • f) i‖ ^ ENNReal.toReal p
    have := (hf.summable hp).mul_left (↑(‖c‖₊ ^ p.toReal) : ℝ)
    -- ⊢ Summable fun i => ‖(c • f) i‖ ^ ENNReal.toReal p
    simp_rw [← coe_nnnorm, ← NNReal.coe_rpow, ← NNReal.coe_mul, NNReal.summable_coe,
      ← NNReal.mul_rpow] at this ⊢
    refine' NNReal.summable_of_le _ this
    -- ⊢ ∀ (b : α), ‖(c • f) b‖₊ ^ ENNReal.toReal p ≤ (‖c‖₊ * ‖f b‖₊) ^ ENNReal.toRea …
    intro i
    -- ⊢ ‖(c • f) i‖₊ ^ ENNReal.toReal p ≤ (‖c‖₊ * ‖f i‖₊) ^ ENNReal.toReal p
    exact NNReal.rpow_le_rpow (nnnorm_smul_le _ _) ENNReal.toReal_nonneg
    -- 🎉 no goals
#align mem_ℓp.const_smul Memℓp.const_smul

theorem const_mul {f : α → 𝕜} (hf : Memℓp f p) (c : 𝕜) : Memℓp (fun x => c * f x) p :=
  @Memℓp.const_smul α (fun _ => 𝕜) _ _ 𝕜 _ _ (fun i => by infer_instance) _ hf c
                                                          -- 🎉 no goals
#align mem_ℓp.const_mul Memℓp.const_mul

end BoundedSMul

end Memℓp

/-!
### lp space

The space of elements of `∀ i, E i` satisfying the predicate `Memℓp`.
-/


/-- We define `PreLp E` to be a type synonym for `∀ i, E i` which, importantly, does not inherit
the `pi` topology on `∀ i, E i` (otherwise this topology would descend to `lp E p` and conflict
with the normed group topology we will later equip it with.)

We choose to deal with this issue by making a type synonym for `∀ i, E i` rather than for the `lp`
subgroup itself, because this allows all the spaces `lp E p` (for varying `p`) to be subgroups of
the same ambient group, which permits lemma statements like `lp.monotone` (below). -/
@[nolint unusedArguments]
def PreLp (E : α → Type*) [∀ i, NormedAddCommGroup (E i)] : Type _ :=
  ∀ i, E i --deriving AddCommGroup
#align pre_lp PreLp

instance : AddCommGroup (PreLp E) := by unfold PreLp; infer_instance
                                        -- ⊢ AddCommGroup ((i : α) → E i)
                                                      -- 🎉 no goals

instance PreLp.unique [IsEmpty α] : Unique (PreLp E) :=
  Pi.uniqueOfIsEmpty E
#align pre_lp.unique PreLp.unique

/-- lp space -/
def lp (E : α → Type*) [∀ i, NormedAddCommGroup (E i)] (p : ℝ≥0∞) : AddSubgroup (PreLp E) where
  carrier := { f | Memℓp f p }
  zero_mem' := zero_memℓp
  add_mem' := Memℓp.add
  neg_mem' := Memℓp.neg
#align lp lp

scoped[lp] notation "ℓ^∞(" ι ", " E ")" => lp (fun i : ι => E) ∞
scoped[lp] notation "ℓ^∞(" ι ")" => lp (fun i : ι => ℝ) ∞

namespace lp

-- Porting note: was `Coe`
instance : CoeOut (lp E p) (∀ i, E i) :=
  ⟨Subtype.val (α := ∀ i, E i)⟩ -- Porting note: Originally `coeSubtype`

instance coeFun : CoeFun (lp E p) fun _ => ∀ i, E i :=
  ⟨fun f => (f : ∀ i, E i)⟩

@[ext]
theorem ext {f g : lp E p} (h : (f : ∀ i, E i) = g) : f = g :=
  Subtype.ext h
#align lp.ext lp.ext

protected theorem ext_iff {f g : lp E p} : f = g ↔ (f : ∀ i, E i) = g :=
  Subtype.ext_iff
#align lp.ext_iff lp.ext_iff

theorem eq_zero' [IsEmpty α] (f : lp E p) : f = 0 :=
  Subsingleton.elim f 0
#align lp.eq_zero' lp.eq_zero'

protected theorem monotone {p q : ℝ≥0∞} (hpq : q ≤ p) : lp E q ≤ lp E p :=
  fun _ hf => Memℓp.of_exponent_ge hf hpq
#align lp.monotone lp.monotone

protected theorem memℓp (f : lp E p) : Memℓp f p :=
  f.prop
#align lp.mem_ℓp lp.memℓp

variable (E p)

@[simp]
theorem coeFn_zero : ⇑(0 : lp E p) = 0 :=
  rfl
#align lp.coe_fn_zero lp.coeFn_zero

variable {E p}

@[simp]
theorem coeFn_neg (f : lp E p) : ⇑(-f) = -f :=
  rfl
#align lp.coe_fn_neg lp.coeFn_neg

@[simp]
theorem coeFn_add (f g : lp E p) : ⇑(f + g) = f + g :=
  rfl
#align lp.coe_fn_add lp.coeFn_add

-- porting note: removed `@[simp]` because `simp` can prove this
theorem coeFn_sum {ι : Type*} (f : ι → lp E p) (s : Finset ι) :
    ⇑(∑ i in s, f i) = ∑ i in s, ⇑(f i) := by
  simp
  -- 🎉 no goals
#align lp.coe_fn_sum lp.coeFn_sum

@[simp]
theorem coeFn_sub (f g : lp E p) : ⇑(f - g) = f - g :=
  rfl
#align lp.coe_fn_sub lp.coeFn_sub

instance : Norm (lp E p) where
  norm f :=
    if hp : p = 0 then by
      subst hp
      -- ⊢ ℝ
      exact ((lp.memℓp f).finite_dsupport.toFinset.card : ℝ)
      -- 🎉 no goals
    else if p = ∞ then ⨆ i, ‖f i‖ else (∑' i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)

theorem norm_eq_card_dsupport (f : lp E 0) : ‖f‖ = (lp.memℓp f).finite_dsupport.toFinset.card :=
  dif_pos rfl
#align lp.norm_eq_card_dsupport lp.norm_eq_card_dsupport

theorem norm_eq_ciSup (f : lp E ∞) : ‖f‖ = ⨆ i, ‖f i‖ := by
  dsimp [norm]
  -- ⊢ (if hp : ⊤ = 0 then Eq.rec (motive := fun x x_1 => { x_2 // x_2 ∈ lp E x } → …
  rw [dif_neg ENNReal.top_ne_zero, if_pos rfl]
  -- 🎉 no goals
#align lp.norm_eq_csupr lp.norm_eq_ciSup

theorem isLUB_norm [Nonempty α] (f : lp E ∞) : IsLUB (Set.range fun i => ‖f i‖) ‖f‖ := by
  rw [lp.norm_eq_ciSup]
  -- ⊢ IsLUB (Set.range fun i => ‖↑f i‖) (⨆ (i : α), ‖↑f i‖)
  exact isLUB_ciSup (lp.memℓp f)
  -- 🎉 no goals
#align lp.is_lub_norm lp.isLUB_norm

theorem norm_eq_tsum_rpow (hp : 0 < p.toReal) (f : lp E p) :
    ‖f‖ = (∑' i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal) := by
  dsimp [norm]
  -- ⊢ (if hp : p = 0 then Eq.rec (motive := fun x x_1 => { x_2 // x_2 ∈ lp E x } → …
  rw [ENNReal.toReal_pos_iff] at hp
  -- ⊢ (if hp : p = 0 then Eq.rec (motive := fun x x_1 => { x_2 // x_2 ∈ lp E x } → …
  rw [dif_neg hp.1.ne', if_neg hp.2.ne]
  -- 🎉 no goals
#align lp.norm_eq_tsum_rpow lp.norm_eq_tsum_rpow

theorem norm_rpow_eq_tsum (hp : 0 < p.toReal) (f : lp E p) :
    ‖f‖ ^ p.toReal = ∑' i, ‖f i‖ ^ p.toReal := by
  rw [norm_eq_tsum_rpow hp, ← Real.rpow_mul]
  -- ⊢ (∑' (i : α), ‖↑f i‖ ^ ENNReal.toReal p) ^ (1 / ENNReal.toReal p * ENNReal.to …
  · field_simp
    -- 🎉 no goals
  apply tsum_nonneg
  -- ⊢ ∀ (i : α), 0 ≤ ‖↑f i‖ ^ ENNReal.toReal p
  intro i
  -- ⊢ 0 ≤ ‖↑f i‖ ^ ENNReal.toReal p
  calc
    (0 : ℝ) = (0 : ℝ) ^ p.toReal := by rw [Real.zero_rpow hp.ne']
    _ ≤ _ := Real.rpow_le_rpow rfl.le (norm_nonneg (f i)) hp.le
#align lp.norm_rpow_eq_tsum lp.norm_rpow_eq_tsum

theorem hasSum_norm (hp : 0 < p.toReal) (f : lp E p) :
    HasSum (fun i => ‖f i‖ ^ p.toReal) (‖f‖ ^ p.toReal) := by
  rw [norm_rpow_eq_tsum hp]
  -- ⊢ HasSum (fun i => ‖↑f i‖ ^ ENNReal.toReal p) (∑' (i : α), ‖↑f i‖ ^ ENNReal.to …
  exact ((lp.memℓp f).summable hp).hasSum
  -- 🎉 no goals
#align lp.has_sum_norm lp.hasSum_norm

theorem norm_nonneg' (f : lp E p) : 0 ≤ ‖f‖ := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · simp [lp.norm_eq_card_dsupport f]
    -- 🎉 no goals
  · cases' isEmpty_or_nonempty α with _i _i
    -- ⊢ 0 ≤ ‖f‖
    · rw [lp.norm_eq_ciSup]
      -- ⊢ 0 ≤ ⨆ (i : α), ‖↑f i‖
      simp [Real.ciSup_empty]
      -- 🎉 no goals
    inhabit α
    -- ⊢ 0 ≤ ‖f‖
    exact (norm_nonneg (f default)).trans ((lp.isLUB_norm f).1 ⟨default, rfl⟩)
    -- 🎉 no goals
  · rw [lp.norm_eq_tsum_rpow hp f]
    -- ⊢ 0 ≤ (∑' (i : α), ‖↑f i‖ ^ ENNReal.toReal p) ^ (1 / ENNReal.toReal p)
    refine' Real.rpow_nonneg_of_nonneg (tsum_nonneg _) _
    -- ⊢ ∀ (i : α), 0 ≤ ‖↑f i‖ ^ ENNReal.toReal p
    exact fun i => Real.rpow_nonneg_of_nonneg (norm_nonneg _) _
    -- 🎉 no goals
#align lp.norm_nonneg' lp.norm_nonneg'

@[simp]
theorem norm_zero : ‖(0 : lp E p)‖ = 0 := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · simp [lp.norm_eq_card_dsupport]
    -- 🎉 no goals
  · simp [lp.norm_eq_ciSup]
    -- 🎉 no goals
  · rw [lp.norm_eq_tsum_rpow hp]
    -- ⊢ (∑' (i : α), ‖↑0 i‖ ^ ENNReal.toReal p) ^ (1 / ENNReal.toReal p) = 0
    have hp' : 1 / p.toReal ≠ 0 := one_div_ne_zero hp.ne'
    -- ⊢ (∑' (i : α), ‖↑0 i‖ ^ ENNReal.toReal p) ^ (1 / ENNReal.toReal p) = 0
    simpa [Real.zero_rpow hp.ne'] using Real.zero_rpow hp'
    -- 🎉 no goals
#align lp.norm_zero lp.norm_zero

theorem norm_eq_zero_iff {f : lp E p} : ‖f‖ = 0 ↔ f = 0 := by
  refine' ⟨fun h => _, by rintro rfl; exact norm_zero⟩
  -- ⊢ f = 0
  rcases p.trichotomy with (rfl | rfl | hp)
  · ext i
    -- ⊢ ↑f i = ↑0 i
    have : { i : α | ¬f i = 0 } = ∅ := by simpa [lp.norm_eq_card_dsupport f] using h
    -- ⊢ ↑f i = ↑0 i
    have : (¬f i = 0) = False := congr_fun this i
    -- ⊢ ↑f i = ↑0 i
    tauto
    -- 🎉 no goals
  · cases' isEmpty_or_nonempty α with _i _i
    -- ⊢ f = 0
    · simp
      -- 🎉 no goals
    have H : IsLUB (Set.range fun i => ‖f i‖) 0 := by simpa [h] using lp.isLUB_norm f
    -- ⊢ f = 0
    ext i
    -- ⊢ ↑f i = ↑0 i
    have : ‖f i‖ = 0 := le_antisymm (H.1 ⟨i, rfl⟩) (norm_nonneg _)
    -- ⊢ ↑f i = ↑0 i
    simpa using this
    -- 🎉 no goals
  · have hf : HasSum (fun i : α => ‖f i‖ ^ p.toReal) 0 := by
      have := lp.hasSum_norm hp f
      rwa [h, Real.zero_rpow hp.ne'] at this
    have : ∀ i, 0 ≤ ‖f i‖ ^ p.toReal := fun i => Real.rpow_nonneg_of_nonneg (norm_nonneg _) _
    -- ⊢ f = 0
    rw [hasSum_zero_iff_of_nonneg this] at hf
    -- ⊢ f = 0
    ext i
    -- ⊢ ↑f i = ↑0 i
    have : f i = 0 ∧ p.toReal ≠ 0 := by
      simpa [Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg (f i))] using congr_fun hf i
    exact this.1
    -- 🎉 no goals
#align lp.norm_eq_zero_iff lp.norm_eq_zero_iff

theorem eq_zero_iff_coeFn_eq_zero {f : lp E p} : f = 0 ↔ ⇑f = 0 := by
  rw [lp.ext_iff, coeFn_zero]
  -- 🎉 no goals
#align lp.eq_zero_iff_coe_fn_eq_zero lp.eq_zero_iff_coeFn_eq_zero

-- porting note: this was very slow, so I squeezed the `simp` calls
@[simp]
theorem norm_neg ⦃f : lp E p⦄ : ‖-f‖ = ‖f‖ := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · simp only [norm_eq_card_dsupport, coeFn_neg, Pi.neg_apply, ne_eq, neg_eq_zero]
    -- 🎉 no goals
  · cases isEmpty_or_nonempty α
    -- ⊢ ‖-f‖ = ‖f‖
    · simp only [lp.eq_zero' f, neg_zero, norm_zero]
      -- 🎉 no goals
    apply (lp.isLUB_norm (-f)).unique
    -- ⊢ IsLUB (Set.range fun i => ‖↑(-f) i‖) ‖f‖
    simpa only [coeFn_neg, Pi.neg_apply, norm_neg] using lp.isLUB_norm f
    -- 🎉 no goals
  · suffices ‖-f‖ ^ p.toReal = ‖f‖ ^ p.toReal by
      exact Real.rpow_left_injOn hp.ne' (norm_nonneg' _) (norm_nonneg' _) this
    apply (lp.hasSum_norm hp (-f)).unique
    -- ⊢ HasSum (fun i => ‖↑(-f) i‖ ^ ENNReal.toReal p) (‖f‖ ^ ENNReal.toReal p)
    simpa only [coeFn_neg, Pi.neg_apply, _root_.norm_neg] using lp.hasSum_norm hp f
    -- 🎉 no goals
#align lp.norm_neg lp.norm_neg

instance normedAddCommGroup [hp : Fact (1 ≤ p)] : NormedAddCommGroup (lp E p) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := norm
      map_zero' := norm_zero
      neg' := norm_neg
      add_le' := fun f g => by
        rcases p.dichotomy with (rfl | hp')
        -- ⊢ ‖f + g‖ ≤ ‖f‖ + ‖g‖
        · cases isEmpty_or_nonempty α
          -- ⊢ ‖f + g‖ ≤ ‖f‖ + ‖g‖
          · -- Porting note: was `simp [lp.eq_zero' f]`
            rw [lp.eq_zero' f]
            -- ⊢ ‖0 + g‖ ≤ ‖0‖ + ‖g‖
            simp only [zero_add, norm_zero, le_refl] -- porting note: just `simp` was slow
            -- 🎉 no goals
          refine' (lp.isLUB_norm (f + g)).2 _
          -- ⊢ ‖f‖ + ‖g‖ ∈ upperBounds (Set.range fun i => ‖↑(f + g) i‖)
          rintro x ⟨i, rfl⟩
          -- ⊢ (fun i => ‖↑(f + g) i‖) i ≤ ‖f‖ + ‖g‖
          refine' le_trans _ (add_mem_upperBounds_add
            (lp.isLUB_norm f).1 (lp.isLUB_norm g).1 ⟨_, _, ⟨i, rfl⟩, ⟨i, rfl⟩, rfl⟩)
          exact norm_add_le (f i) (g i)
          -- 🎉 no goals
        · have hp'' : 0 < p.toReal := zero_lt_one.trans_le hp'
          -- ⊢ ‖f + g‖ ≤ ‖f‖ + ‖g‖
          have hf₁ : ∀ i, 0 ≤ ‖f i‖ := fun i => norm_nonneg _
          -- ⊢ ‖f + g‖ ≤ ‖f‖ + ‖g‖
          have hg₁ : ∀ i, 0 ≤ ‖g i‖ := fun i => norm_nonneg _
          -- ⊢ ‖f + g‖ ≤ ‖f‖ + ‖g‖
          have hf₂ := lp.hasSum_norm hp'' f
          -- ⊢ ‖f + g‖ ≤ ‖f‖ + ‖g‖
          have hg₂ := lp.hasSum_norm hp'' g
          -- ⊢ ‖f + g‖ ≤ ‖f‖ + ‖g‖
          -- apply Minkowski's inequality
          obtain ⟨C, hC₁, hC₂, hCfg⟩ :=
            Real.Lp_add_le_hasSum_of_nonneg hp' hf₁ hg₁ (norm_nonneg' _) (norm_nonneg' _) hf₂ hg₂
          refine' le_trans _ hC₂
          -- ⊢ ‖f + g‖ ≤ C
          rw [← Real.rpow_le_rpow_iff (norm_nonneg' (f + g)) hC₁ hp'']
          -- ⊢ ‖f + g‖ ^ ENNReal.toReal p ≤ C ^ ENNReal.toReal p
          refine' hasSum_le _ (lp.hasSum_norm hp'' (f + g)) hCfg
          -- ⊢ ∀ (i : α), ‖↑(f + g) i‖ ^ ENNReal.toReal p ≤ (‖↑f i‖ + ‖↑g i‖) ^ ENNReal.toR …
          intro i
          -- ⊢ ‖↑(f + g) i‖ ^ ENNReal.toReal p ≤ (‖↑f i‖ + ‖↑g i‖) ^ ENNReal.toReal p
          exact Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) hp''.le
          -- 🎉 no goals
      eq_zero_of_map_eq_zero' := fun f => norm_eq_zero_iff.1 }

-- TODO: define an `ENNReal` version of `IsConjugateExponent`, and then express this inequality
-- in a better version which also covers the case `p = 1, q = ∞`.
/-- Hölder inequality -/
protected theorem tsum_mul_le_mul_norm {p q : ℝ≥0∞} (hpq : p.toReal.IsConjugateExponent q.toReal)
    (f : lp E p) (g : lp E q) :
    (Summable fun i => ‖f i‖ * ‖g i‖) ∧ ∑' i, ‖f i‖ * ‖g i‖ ≤ ‖f‖ * ‖g‖ := by
  have hf₁ : ∀ i, 0 ≤ ‖f i‖ := fun i => norm_nonneg _
  -- ⊢ (Summable fun i => ‖↑f i‖ * ‖↑g i‖) ∧ ∑' (i : α), ‖↑f i‖ * ‖↑g i‖ ≤ ‖f‖ * ‖g‖
  have hg₁ : ∀ i, 0 ≤ ‖g i‖ := fun i => norm_nonneg _
  -- ⊢ (Summable fun i => ‖↑f i‖ * ‖↑g i‖) ∧ ∑' (i : α), ‖↑f i‖ * ‖↑g i‖ ≤ ‖f‖ * ‖g‖
  have hf₂ := lp.hasSum_norm hpq.pos f
  -- ⊢ (Summable fun i => ‖↑f i‖ * ‖↑g i‖) ∧ ∑' (i : α), ‖↑f i‖ * ‖↑g i‖ ≤ ‖f‖ * ‖g‖
  have hg₂ := lp.hasSum_norm hpq.symm.pos g
  -- ⊢ (Summable fun i => ‖↑f i‖ * ‖↑g i‖) ∧ ∑' (i : α), ‖↑f i‖ * ‖↑g i‖ ≤ ‖f‖ * ‖g‖
  obtain ⟨C, -, hC', hC⟩ :=
    Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg hpq (norm_nonneg' _) (norm_nonneg' _) hf₁ hg₁ hf₂ hg₂
  rw [← hC.tsum_eq] at hC'
  -- ⊢ (Summable fun i => ‖↑f i‖ * ‖↑g i‖) ∧ ∑' (i : α), ‖↑f i‖ * ‖↑g i‖ ≤ ‖f‖ * ‖g‖
  exact ⟨hC.summable, hC'⟩
  -- 🎉 no goals
#align lp.tsum_mul_le_mul_norm lp.tsum_mul_le_mul_norm

protected theorem summable_mul {p q : ℝ≥0∞} (hpq : p.toReal.IsConjugateExponent q.toReal)
    (f : lp E p) (g : lp E q) : Summable fun i => ‖f i‖ * ‖g i‖ :=
  (lp.tsum_mul_le_mul_norm hpq f g).1
#align lp.summable_mul lp.summable_mul

protected theorem tsum_mul_le_mul_norm' {p q : ℝ≥0∞} (hpq : p.toReal.IsConjugateExponent q.toReal)
    (f : lp E p) (g : lp E q) : ∑' i, ‖f i‖ * ‖g i‖ ≤ ‖f‖ * ‖g‖ :=
  (lp.tsum_mul_le_mul_norm hpq f g).2
#align lp.tsum_mul_le_mul_norm' lp.tsum_mul_le_mul_norm'

section ComparePointwise

theorem norm_apply_le_norm (hp : p ≠ 0) (f : lp E p) (i : α) : ‖f i‖ ≤ ‖f‖ := by
  rcases eq_or_ne p ∞ with (rfl | hp')
  -- ⊢ ‖↑f i‖ ≤ ‖f‖
  · haveI : Nonempty α := ⟨i⟩
    -- ⊢ ‖↑f i‖ ≤ ‖f‖
    exact (isLUB_norm f).1 ⟨i, rfl⟩
    -- 🎉 no goals
  have hp'' : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  -- ⊢ ‖↑f i‖ ≤ ‖f‖
  have : ∀ i, 0 ≤ ‖f i‖ ^ p.toReal := fun i => Real.rpow_nonneg_of_nonneg (norm_nonneg _) _
  -- ⊢ ‖↑f i‖ ≤ ‖f‖
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg' _) hp'']
  -- ⊢ ‖↑f i‖ ^ ENNReal.toReal p ≤ ‖f‖ ^ ENNReal.toReal p
  convert le_hasSum (hasSum_norm hp'' f) i fun i _ => this i
  -- 🎉 no goals
#align lp.norm_apply_le_norm lp.norm_apply_le_norm

theorem sum_rpow_le_norm_rpow (hp : 0 < p.toReal) (f : lp E p) (s : Finset α) :
    ∑ i in s, ‖f i‖ ^ p.toReal ≤ ‖f‖ ^ p.toReal := by
  rw [lp.norm_rpow_eq_tsum hp f]
  -- ⊢ ∑ i in s, ‖↑f i‖ ^ ENNReal.toReal p ≤ ∑' (i : α), ‖↑f i‖ ^ ENNReal.toReal p
  have : ∀ i, 0 ≤ ‖f i‖ ^ p.toReal := fun i => Real.rpow_nonneg_of_nonneg (norm_nonneg _) _
  -- ⊢ ∑ i in s, ‖↑f i‖ ^ ENNReal.toReal p ≤ ∑' (i : α), ‖↑f i‖ ^ ENNReal.toReal p
  refine' sum_le_tsum _ (fun i _ => this i) _
  -- ⊢ Summable fun i => ‖↑f i‖ ^ ENNReal.toReal p
  exact (lp.memℓp f).summable hp
  -- 🎉 no goals
#align lp.sum_rpow_le_norm_rpow lp.sum_rpow_le_norm_rpow

theorem norm_le_of_forall_le' [Nonempty α] {f : lp E ∞} (C : ℝ) (hCf : ∀ i, ‖f i‖ ≤ C) :
    ‖f‖ ≤ C := by
  refine' (isLUB_norm f).2 _
  -- ⊢ C ∈ upperBounds (Set.range fun i => ‖↑f i‖)
  rintro - ⟨i, rfl⟩
  -- ⊢ (fun i => ‖↑f i‖) i ≤ C
  exact hCf i
  -- 🎉 no goals
#align lp.norm_le_of_forall_le' lp.norm_le_of_forall_le'

theorem norm_le_of_forall_le {f : lp E ∞} {C : ℝ} (hC : 0 ≤ C) (hCf : ∀ i, ‖f i‖ ≤ C) :
    ‖f‖ ≤ C := by
  cases isEmpty_or_nonempty α
  -- ⊢ ‖f‖ ≤ C
  · simpa [eq_zero' f] using hC
    -- 🎉 no goals
  · exact norm_le_of_forall_le' C hCf
    -- 🎉 no goals
#align lp.norm_le_of_forall_le lp.norm_le_of_forall_le

theorem norm_le_of_tsum_le (hp : 0 < p.toReal) {C : ℝ} (hC : 0 ≤ C) {f : lp E p}
    (hf : ∑' i, ‖f i‖ ^ p.toReal ≤ C ^ p.toReal) : ‖f‖ ≤ C := by
  rw [← Real.rpow_le_rpow_iff (norm_nonneg' _) hC hp, norm_rpow_eq_tsum hp]
  -- ⊢ ∑' (i : α), ‖↑f i‖ ^ ENNReal.toReal p ≤ C ^ ENNReal.toReal p
  exact hf
  -- 🎉 no goals
#align lp.norm_le_of_tsum_le lp.norm_le_of_tsum_le

theorem norm_le_of_forall_sum_le (hp : 0 < p.toReal) {C : ℝ} (hC : 0 ≤ C) {f : lp E p}
    (hf : ∀ s : Finset α, ∑ i in s, ‖f i‖ ^ p.toReal ≤ C ^ p.toReal) : ‖f‖ ≤ C :=
  norm_le_of_tsum_le hp hC (tsum_le_of_sum_le ((lp.memℓp f).summable hp) hf)
#align lp.norm_le_of_forall_sum_le lp.norm_le_of_forall_sum_le

end ComparePointwise

section BoundedSMul

variable {𝕜 : Type*} {𝕜' : Type*}

variable [NormedRing 𝕜] [NormedRing 𝕜']

variable [∀ i, Module 𝕜 (E i)] [∀ i, Module 𝕜' (E i)]

instance : Module 𝕜 (PreLp E) :=
  Pi.module α E 𝕜

instance [∀ i, SMulCommClass 𝕜' 𝕜 (E i)] : SMulCommClass 𝕜' 𝕜 (PreLp E) :=
  Pi.smulCommClass

instance [SMul 𝕜' 𝕜] [∀ i, IsScalarTower 𝕜' 𝕜 (E i)] : IsScalarTower 𝕜' 𝕜 (PreLp E) :=
  Pi.isScalarTower

instance [∀ i, Module 𝕜ᵐᵒᵖ (E i)] [∀ i, IsCentralScalar 𝕜 (E i)] : IsCentralScalar 𝕜 (PreLp E) :=
  Pi.isCentralScalar

variable [∀ i, BoundedSMul 𝕜 (E i)] [∀ i, BoundedSMul 𝕜' (E i)]

theorem mem_lp_const_smul (c : 𝕜) (f : lp E p) : c • (f : PreLp E) ∈ lp E p :=
  (lp.memℓp f).const_smul c
#align lp.mem_lp_const_smul lp.mem_lp_const_smul

variable (E p 𝕜)

/-- The `𝕜`-submodule of elements of `∀ i : α, E i` whose `lp` norm is finite. This is `lp E p`,
with extra structure. -/
def _root_.lpSubmodule : Submodule 𝕜 (PreLp E) :=
  { lp E p with smul_mem' := fun c f hf => by simpa using mem_lp_const_smul c ⟨f, hf⟩ }
                                              -- 🎉 no goals
#align lp_submodule lpSubmodule

variable {E p 𝕜}

theorem coe_lpSubmodule : (lpSubmodule E p 𝕜).toAddSubgroup = lp E p :=
  rfl
#align lp.coe_lp_submodule lp.coe_lpSubmodule

instance : Module 𝕜 (lp E p) :=
  { (lpSubmodule E p 𝕜).module with }

@[simp]
theorem coeFn_smul (c : 𝕜) (f : lp E p) : ⇑(c • f) = c • ⇑f :=
  rfl
#align lp.coe_fn_smul lp.coeFn_smul

instance [∀ i, SMulCommClass 𝕜' 𝕜 (E i)] : SMulCommClass 𝕜' 𝕜 (lp E p) :=
  ⟨fun _ _ _ => Subtype.ext <| smul_comm _ _ _⟩

instance [SMul 𝕜' 𝕜] [∀ i, IsScalarTower 𝕜' 𝕜 (E i)] : IsScalarTower 𝕜' 𝕜 (lp E p) :=
  ⟨fun _ _ _ => Subtype.ext <| smul_assoc _ _ _⟩

instance [∀ i, Module 𝕜ᵐᵒᵖ (E i)] [∀ i, IsCentralScalar 𝕜 (E i)] : IsCentralScalar 𝕜 (lp E p) :=
  ⟨fun _ _ => Subtype.ext <| op_smul_eq_smul _ _⟩

theorem norm_const_smul_le (hp : p ≠ 0) (c : 𝕜) (f : lp E p) : ‖c • f‖ ≤ ‖c‖ * ‖f‖ := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · exact absurd rfl hp
    -- 🎉 no goals
  · cases isEmpty_or_nonempty α
    -- ⊢ ‖c • f‖ ≤ ‖c‖ * ‖f‖
    · simp [lp.eq_zero' f]
      -- 🎉 no goals
    have hcf := lp.isLUB_norm (c • f)
    -- ⊢ ‖c • f‖ ≤ ‖c‖ * ‖f‖
    have hfc := (lp.isLUB_norm f).mul_left (norm_nonneg c)
    -- ⊢ ‖c • f‖ ≤ ‖c‖ * ‖f‖
    simp_rw [← Set.range_comp, Function.comp] at hfc
    -- ⊢ ‖c • f‖ ≤ ‖c‖ * ‖f‖
    -- TODO: some `IsLUB` API should make it a one-liner from here.
    refine' hcf.right _
    -- ⊢ ‖c‖ * ‖f‖ ∈ upperBounds (Set.range fun i => ‖↑(c • f) i‖)
    have := hfc.left
    -- ⊢ ‖c‖ * ‖f‖ ∈ upperBounds (Set.range fun i => ‖↑(c • f) i‖)
    simp_rw [mem_upperBounds, Set.mem_range,
      forall_exists_index, forall_apply_eq_imp_iff'] at this ⊢
    intro a
    -- ⊢ ‖↑(c • f) a‖ ≤ ‖c‖ * ‖f‖
    exact (norm_smul_le _ _).trans (this a)
    -- 🎉 no goals
  · letI inst : NNNorm (lp E p) := ⟨fun f => ⟨‖f‖, norm_nonneg' _⟩⟩
    -- ⊢ ‖c • f‖ ≤ ‖c‖ * ‖f‖
    have coe_nnnorm : ∀ f : lp E p, ↑‖f‖₊ = ‖f‖ := fun _ => rfl
    -- ⊢ ‖c • f‖ ≤ ‖c‖ * ‖f‖
    suffices ‖c • f‖₊ ^ p.toReal ≤ (‖c‖₊ * ‖f‖₊) ^ p.toReal by
      rwa [NNReal.rpow_le_rpow_iff hp] at this
    clear_value inst
    -- ⊢ ‖c • f‖₊ ^ ENNReal.toReal p ≤ (‖c‖₊ * ‖f‖₊) ^ ENNReal.toReal p
    rw [NNReal.mul_rpow]
    -- ⊢ ‖c • f‖₊ ^ ENNReal.toReal p ≤ ‖c‖₊ ^ ENNReal.toReal p * ‖f‖₊ ^ ENNReal.toRea …
    have hLHS := lp.hasSum_norm hp (c • f)
    -- ⊢ ‖c • f‖₊ ^ ENNReal.toReal p ≤ ‖c‖₊ ^ ENNReal.toReal p * ‖f‖₊ ^ ENNReal.toRea …
    have hRHS := (lp.hasSum_norm hp f).mul_left (‖c‖ ^ p.toReal)
    -- ⊢ ‖c • f‖₊ ^ ENNReal.toReal p ≤ ‖c‖₊ ^ ENNReal.toReal p * ‖f‖₊ ^ ENNReal.toRea …
    simp_rw [← coe_nnnorm, ← _root_.coe_nnnorm, ← NNReal.coe_rpow, ← NNReal.coe_mul,
      NNReal.hasSum_coe] at hRHS hLHS
    refine' hasSum_mono hLHS hRHS fun i => _
    -- ⊢ ‖↑(c • f) i‖₊ ^ ENNReal.toReal p ≤ ‖c‖₊ ^ ENNReal.toReal p * ‖↑f i‖₊ ^ ENNRe …
    dsimp only
    -- ⊢ ‖↑(c • f) i‖₊ ^ ENNReal.toReal p ≤ ‖c‖₊ ^ ENNReal.toReal p * ‖↑f i‖₊ ^ ENNRe …
    rw [← NNReal.mul_rpow]
    -- ⊢ ‖↑(c • f) i‖₊ ^ ENNReal.toReal p ≤ (‖c‖₊ * ‖↑f i‖₊) ^ ENNReal.toReal p
    -- Porting note: added
    rw [lp.coeFn_smul, Pi.smul_apply]
    -- ⊢ ‖c • ↑f i‖₊ ^ ENNReal.toReal p ≤ (‖c‖₊ * ‖↑f i‖₊) ^ ENNReal.toReal p
    exact NNReal.rpow_le_rpow (nnnorm_smul_le _ _) ENNReal.toReal_nonneg
    -- 🎉 no goals
#align lp.norm_const_smul_le lp.norm_const_smul_le

instance [Fact (1 ≤ p)] : BoundedSMul 𝕜 (lp E p) :=
  BoundedSMul.of_norm_smul_le <| norm_const_smul_le (zero_lt_one.trans_le <| Fact.out).ne'

end BoundedSMul

section DivisionRing

variable {𝕜 : Type*}

variable [NormedDivisionRing 𝕜] [∀ i, Module 𝕜 (E i)] [∀ i, BoundedSMul 𝕜 (E i)]

theorem norm_const_smul (hp : p ≠ 0) {c : 𝕜} (f : lp E p) : ‖c • f‖ = ‖c‖ * ‖f‖ := by
  obtain rfl | hc := eq_or_ne c 0
  -- ⊢ ‖0 • f‖ = ‖0‖ * ‖f‖
  · simp
    -- 🎉 no goals
  refine' le_antisymm (norm_const_smul_le hp c f) _
  -- ⊢ ‖c‖ * ‖f‖ ≤ ‖c • f‖
  have := mul_le_mul_of_nonneg_left (norm_const_smul_le hp c⁻¹ (c • f)) (norm_nonneg c)
  -- ⊢ ‖c‖ * ‖f‖ ≤ ‖c • f‖
  rwa [inv_smul_smul₀ hc, norm_inv, mul_inv_cancel_left₀ (norm_ne_zero_iff.mpr hc)] at this
  -- 🎉 no goals
#align lp.norm_const_smul lp.norm_const_smul

end DivisionRing

section NormedSpace

variable {𝕜 : Type*} [NormedField 𝕜] [∀ i, NormedSpace 𝕜 (E i)]

instance instNormedSpace [Fact (1 ≤ p)] : NormedSpace 𝕜 (lp E p) where
  norm_smul_le c f := norm_smul_le c f

end NormedSpace

section NormedStarGroup

variable [∀ i, StarAddMonoid (E i)] [∀ i, NormedStarGroup (E i)]

theorem _root_.Memℓp.star_mem {f : ∀ i, E i} (hf : Memℓp f p) : Memℓp (star f) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    -- ⊢ Set.Finite {i | star f i ≠ 0}
    simp [hf.finite_dsupport]
    -- 🎉 no goals
  · apply memℓp_infty
    -- ⊢ BddAbove (Set.range fun i => ‖star f i‖)
    simpa using hf.bddAbove
    -- 🎉 no goals
  · apply memℓp_gen
    -- ⊢ Summable fun i => ‖star f i‖ ^ ENNReal.toReal p
    simpa using hf.summable hp
    -- 🎉 no goals
#align mem_ℓp.star_mem Memℓp.star_mem

@[simp]
theorem _root_.Memℓp.star_iff {f : ∀ i, E i} : Memℓp (star f) p ↔ Memℓp f p :=
  ⟨fun h => star_star f ▸ Memℓp.star_mem h, Memℓp.star_mem⟩
#align mem_ℓp.star_iff Memℓp.star_iff

instance : Star (lp E p) where
  star f := ⟨(star f : ∀ i, E i), f.property.star_mem⟩

@[simp]
theorem coeFn_star (f : lp E p) : ⇑(star f) = star (⇑f) :=
  rfl
#align lp.coe_fn_star lp.coeFn_star

@[simp]
protected theorem star_apply (f : lp E p) (i : α) : star f i = star (f i) :=
  rfl
#align lp.star_apply lp.star_apply

instance instInvolutiveStar : InvolutiveStar (lp E p) where
  star_involutive x := by simp [star]
                          -- 🎉 no goals

instance instStarAddMonoid : StarAddMonoid (lp E p) where
  star_add _f _g := ext <| star_add (R := ∀ i, E i) _ _

instance [hp : Fact (1 ≤ p)] : NormedStarGroup (lp E p) where
  norm_star f := by
    rcases p.trichotomy with (rfl | rfl | h)
    · exfalso
      -- ⊢ False
      have := ENNReal.toReal_mono ENNReal.zero_ne_top hp.elim
      -- ⊢ False
      norm_num at this
      -- 🎉 no goals
    · simp only [lp.norm_eq_ciSup, lp.star_apply, norm_star]
      -- 🎉 no goals
    · simp only [lp.norm_eq_tsum_rpow h, lp.star_apply, norm_star]
      -- 🎉 no goals

variable {𝕜 : Type*} [Star 𝕜] [NormedRing 𝕜]

variable [∀ i, Module 𝕜 (E i)] [∀ i, BoundedSMul 𝕜 (E i)] [∀ i, StarModule 𝕜 (E i)]

instance : StarModule 𝕜 (lp E p) where
  star_smul _r _f := ext <| star_smul (A := ∀ i, E i) _ _

end NormedStarGroup

section NonUnitalNormedRing

variable {I : Type*} {B : I → Type*} [∀ i, NonUnitalNormedRing (B i)]

theorem _root_.Memℓp.infty_mul {f g : ∀ i, B i} (hf : Memℓp f ∞) (hg : Memℓp g ∞) :
    Memℓp (f * g) ∞ := by
  rw [memℓp_infty_iff]
  -- ⊢ BddAbove (Set.range fun i => ‖(f * g) i‖)
  obtain ⟨⟨Cf, hCf⟩, ⟨Cg, hCg⟩⟩ := hf.bddAbove, hg.bddAbove
  -- ⊢ BddAbove (Set.range fun i => ‖(f * g) i‖)
  refine' ⟨Cf * Cg, _⟩
  -- ⊢ Cf * Cg ∈ upperBounds (Set.range fun i => ‖(f * g) i‖)
  rintro _ ⟨i, rfl⟩
  -- ⊢ (fun i => ‖(f * g) i‖) i ≤ Cf * Cg
  calc
    ‖(f * g) i‖ ≤ ‖f i‖ * ‖g i‖ := norm_mul_le (f i) (g i)
    _ ≤ Cf * Cg :=
      mul_le_mul (hCf ⟨i, rfl⟩) (hCg ⟨i, rfl⟩) (norm_nonneg _)
        ((norm_nonneg _).trans (hCf ⟨i, rfl⟩))
#align mem_ℓp.infty_mul Memℓp.infty_mul

instance : Mul (lp B ∞) where
  mul f g := ⟨HMul.hMul (α := ∀ i, B i) _ _ , f.property.infty_mul g.property⟩

@[simp]
theorem infty_coeFn_mul (f g : lp B ∞) : ⇑(f * g) = ⇑f * ⇑g :=
  rfl
#align lp.infty_coe_fn_mul lp.infty_coeFn_mul

instance nonUnitalRing : NonUnitalRing (lp B ∞) :=
  Function.Injective.nonUnitalRing lp.coeFun.coe Subtype.coe_injective (lp.coeFn_zero B ∞)
    lp.coeFn_add infty_coeFn_mul lp.coeFn_neg lp.coeFn_sub (fun _ _ => rfl) fun _ _ => rfl

instance nonUnitalNormedRing : NonUnitalNormedRing (lp B ∞) :=
  { lp.normedAddCommGroup, lp.nonUnitalRing with
    norm_mul := fun f g =>
      lp.norm_le_of_forall_le (mul_nonneg (norm_nonneg f) (norm_nonneg g)) fun i =>
        calc
          ‖(f * g) i‖ ≤ ‖f i‖ * ‖g i‖ := norm_mul_le _ _
          _ ≤ ‖f‖ * ‖g‖ :=
            mul_le_mul (lp.norm_apply_le_norm ENNReal.top_ne_zero f i)
              (lp.norm_apply_le_norm ENNReal.top_ne_zero g i) (norm_nonneg _) (norm_nonneg _) }

-- we also want a `non_unital_normed_comm_ring` instance, but this has to wait for #13719
instance infty_isScalarTower {𝕜} [NormedRing 𝕜] [∀ i, Module 𝕜 (B i)] [∀ i, BoundedSMul 𝕜 (B i)]
    [∀ i, IsScalarTower 𝕜 (B i) (B i)] : IsScalarTower 𝕜 (lp B ∞) (lp B ∞) :=
  ⟨fun r f g => lp.ext <| smul_assoc (N := ∀ i, B i) (α := ∀ i, B i) r (⇑f) (⇑g)⟩
#align lp.infty_is_scalar_tower lp.infty_isScalarTower

instance infty_sMulCommClass {𝕜} [NormedRing 𝕜] [∀ i, Module 𝕜 (B i)] [∀ i, BoundedSMul 𝕜 (B i)]
    [∀ i, SMulCommClass 𝕜 (B i) (B i)] : SMulCommClass 𝕜 (lp B ∞) (lp B ∞) :=
  ⟨fun r f g => lp.ext <| smul_comm (N := ∀ i, B i) (α := ∀ i, B i) r (⇑f) (⇑g)⟩
#align lp.infty_smul_comm_class lp.infty_sMulCommClass

section StarRing

variable [∀ i, StarRing (B i)] [∀ i, NormedStarGroup (B i)]

instance inftyStarRing : StarRing (lp B ∞) :=
  { lp.instStarAddMonoid with
    star_mul := fun _f _g => ext <| star_mul (R := ∀ i, B i) _ _ }
#align lp.infty_star_ring lp.inftyStarRing

instance inftyCstarRing [∀ i, CstarRing (B i)] : CstarRing (lp B ∞) where
  norm_star_mul_self := by
    intro f
    -- ⊢ ‖star f * f‖ = ‖f‖ * ‖f‖
    apply le_antisymm
    -- ⊢ ‖star f * f‖ ≤ ‖f‖ * ‖f‖
    · rw [← sq]
      -- ⊢ ‖star f * f‖ ≤ ‖f‖ ^ 2
      refine' lp.norm_le_of_forall_le (sq_nonneg ‖f‖) fun i => _
      -- ⊢ ‖↑(star f * f) i‖ ≤ ‖f‖ ^ 2
      simp only [lp.star_apply, CstarRing.norm_star_mul_self, ← sq, infty_coeFn_mul, Pi.mul_apply]
      -- ⊢ ‖↑f i‖ ^ 2 ≤ ‖f‖ ^ 2
      refine' sq_le_sq' _ (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _)
      -- ⊢ -‖f‖ ≤ ‖↑f i‖
      linarith [norm_nonneg (f i), norm_nonneg f]
      -- 🎉 no goals
    · rw [← sq, ← Real.le_sqrt (norm_nonneg _) (norm_nonneg _)]
      -- ⊢ ‖f‖ ≤ Real.sqrt ‖star f * f‖
      refine' lp.norm_le_of_forall_le ‖star f * f‖.sqrt_nonneg fun i => _
      -- ⊢ ‖↑f i‖ ≤ Real.sqrt ‖star f * f‖
      rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _), sq, ← CstarRing.norm_star_mul_self]
      -- ⊢ ‖star (↑f i) * ↑f i‖ ≤ ‖star f * f‖
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero (star f * f) i
      -- 🎉 no goals
#align lp.infty_cstar_ring lp.inftyCstarRing

end StarRing

end NonUnitalNormedRing

section NormedRing

variable {I : Type*} {B : I → Type*} [∀ i, NormedRing (B i)]

instance _root_.PreLp.ring : Ring (PreLp B) :=
  Pi.ring
#align pre_lp.ring PreLp.ring

variable [∀ i, NormOneClass (B i)]

theorem _root_.one_memℓp_infty : Memℓp (1 : ∀ i, B i) ∞ :=
  ⟨1, by rintro i ⟨i, rfl⟩; exact norm_one.le⟩
         -- ⊢ (fun i => ‖OfNat.ofNat 1 i‖) i ≤ 1
                            -- 🎉 no goals
#align one_mem_ℓp_infty one_memℓp_infty

variable (B)

/-- The `𝕜`-subring of elements of `∀ i : α, B i` whose `lp` norm is finite. This is `lp E ∞`,
with extra structure. -/
def _root_.lpInftySubring : Subring (PreLp B) :=
  { lp B ∞ with
    carrier := { f | Memℓp f ∞ }
    one_mem' := one_memℓp_infty
    mul_mem' := Memℓp.infty_mul }
#align lp_infty_subring lpInftySubring

variable {B}

instance inftyRing : Ring (lp B ∞) :=
  (lpInftySubring B).toRing
#align lp.infty_ring lp.inftyRing

theorem _root_.Memℓp.infty_pow {f : ∀ i, B i} (hf : Memℓp f ∞) (n : ℕ) : Memℓp (f ^ n) ∞ :=
  (lpInftySubring B).pow_mem hf n
#align mem_ℓp.infty_pow Memℓp.infty_pow

theorem _root_.nat_cast_memℓp_infty (n : ℕ) : Memℓp (n : ∀ i, B i) ∞ :=
  natCast_mem (lpInftySubring B) n
#align nat_cast_mem_ℓp_infty nat_cast_memℓp_infty

theorem _root_.int_cast_memℓp_infty (z : ℤ) : Memℓp (z : ∀ i, B i) ∞ :=
  coe_int_mem (lpInftySubring B) z
#align int_cast_mem_ℓp_infty int_cast_memℓp_infty

@[simp]
theorem infty_coeFn_one : ⇑(1 : lp B ∞) = 1 :=
  rfl
#align lp.infty_coe_fn_one lp.infty_coeFn_one

@[simp]
theorem infty_coeFn_pow (f : lp B ∞) (n : ℕ) : ⇑(f ^ n) = (⇑f) ^ n :=
  rfl
#align lp.infty_coe_fn_pow lp.infty_coeFn_pow

@[simp]
theorem infty_coeFn_nat_cast (n : ℕ) : ⇑(n : lp B ∞) = n :=
  rfl
#align lp.infty_coe_fn_nat_cast lp.infty_coeFn_nat_cast

@[simp]
theorem infty_coeFn_int_cast (z : ℤ) : ⇑(z : lp B ∞) = z :=
  rfl
#align lp.infty_coe_fn_int_cast lp.infty_coeFn_int_cast

instance [Nonempty I] : NormOneClass (lp B ∞) where
  norm_one := by simp_rw [lp.norm_eq_ciSup, infty_coeFn_one, Pi.one_apply, norm_one, ciSup_const]
                 -- 🎉 no goals

instance inftyNormedRing : NormedRing (lp B ∞) :=
  { lp.inftyRing, lp.nonUnitalNormedRing with }
#align lp.infty_normed_ring lp.inftyNormedRing

end NormedRing

section NormedCommRing

variable {I : Type*} {B : I → Type*} [∀ i, NormedCommRing (B i)] [∀ i, NormOneClass (B i)]

instance inftyCommRing : CommRing (lp B ∞) :=
  { lp.inftyRing with
    mul_comm := fun f g => by ext; simp only [lp.infty_coeFn_mul, Pi.mul_apply, mul_comm] }
                              -- ⊢ ↑(f * g) x✝ = ↑(g * f) x✝
                                   -- 🎉 no goals
#align lp.infty_comm_ring lp.inftyCommRing

instance inftyNormedCommRing : NormedCommRing (lp B ∞) :=
  { lp.inftyCommRing, lp.inftyNormedRing with }
#align lp.infty_normed_comm_ring lp.inftyNormedCommRing

end NormedCommRing

section Algebra

variable {I : Type*} {𝕜 : Type*} {B : I → Type*}

variable [NormedField 𝕜] [∀ i, NormedRing (B i)] [∀ i, NormedAlgebra 𝕜 (B i)]

/-- A variant of `Pi.algebra` that lean can't find otherwise. -/
instance _root_.Pi.algebraOfNormedAlgebra : Algebra 𝕜 (∀ i, B i) :=
  @Pi.algebra I 𝕜 B _ _ fun _ => NormedAlgebra.toAlgebra
#align pi.algebra_of_normed_algebra Pi.algebraOfNormedAlgebra

instance _root_.PreLp.algebra : Algebra 𝕜 (PreLp B) :=
  Pi.algebraOfNormedAlgebra
#align pre_lp.algebra PreLp.algebra

variable [∀ i, NormOneClass (B i)]

theorem _root_.algebraMap_memℓp_infty (k : 𝕜) : Memℓp (algebraMap 𝕜 (∀ i, B i) k) ∞ := by
  rw [Algebra.algebraMap_eq_smul_one]
  -- ⊢ Memℓp (k • 1) ⊤
  exact (one_memℓp_infty.const_smul k : Memℓp (k • (1 : ∀ i, B i)) ∞)
  -- 🎉 no goals
#align algebra_map_mem_ℓp_infty algebraMap_memℓp_infty

variable (𝕜 B)

/-- The `𝕜`-subalgebra of elements of `∀ i : α, B i` whose `lp` norm is finite. This is `lp E ∞`,
with extra structure. -/
def _root_.lpInftySubalgebra : Subalgebra 𝕜 (PreLp B) :=
  { lpInftySubring B with
    carrier := { f | Memℓp f ∞ }
    algebraMap_mem' := algebraMap_memℓp_infty }
#align lp_infty_subalgebra lpInftySubalgebra

variable {𝕜 B}

instance inftyNormedAlgebra : NormedAlgebra 𝕜 (lp B ∞) :=
  { (lpInftySubalgebra 𝕜 B).algebra, (lp.instNormedSpace : NormedSpace 𝕜 (lp B ∞)) with }
#align lp.infty_normed_algebra lp.inftyNormedAlgebra

end Algebra

section Single

variable {𝕜 : Type*} [NormedRing 𝕜] [∀ i, Module 𝕜 (E i)] [∀ i, BoundedSMul 𝕜 (E i)]

variable [DecidableEq α]

/-- The element of `lp E p` which is `a : E i` at the index `i`, and zero elsewhere. -/
protected def single (p) (i : α) (a : E i) : lp E p :=
  ⟨fun j => if h : j = i then Eq.ndrec a h.symm else 0, by
    refine' (memℓp_zero _).of_exponent_ge (zero_le p)
    -- ⊢ Set.Finite {i_1 | (fun j => if h : j = i then (_ : i = j) ▸ a else 0) i_1 ≠ 0}
    refine' (Set.finite_singleton i).subset _
    -- ⊢ {i_1 | (fun j => if h : j = i then (_ : i = j) ▸ a else 0) i_1 ≠ 0} ⊆ {i}
    intro j
    -- ⊢ j ∈ {i_1 | (fun j => if h : j = i then (_ : i = j) ▸ a else 0) i_1 ≠ 0} → j  …
    simp only [forall_exists_index, Set.mem_singleton_iff, Ne.def, dite_eq_right_iff,
      Set.mem_setOf_eq, not_forall]
    rintro rfl
    -- ⊢ ¬(_ : j = j) ▸ a = 0 → j = j
    simp⟩
    -- 🎉 no goals
#align lp.single lp.single

protected theorem single_apply (p) (i : α) (a : E i) (j : α) :
    lp.single p i a j = if h : j = i then Eq.ndrec a h.symm else 0 :=
  rfl
#align lp.single_apply lp.single_apply

protected theorem single_apply_self (p) (i : α) (a : E i) : lp.single p i a i = a := by
  rw [lp.single_apply, dif_pos rfl]
  -- 🎉 no goals
#align lp.single_apply_self lp.single_apply_self

protected theorem single_apply_ne (p) (i : α) (a : E i) {j : α} (hij : j ≠ i) :
    lp.single p i a j = 0 := by
  rw [lp.single_apply, dif_neg hij]
  -- 🎉 no goals
#align lp.single_apply_ne lp.single_apply_ne

@[simp]
protected theorem single_neg (p) (i : α) (a : E i) : lp.single p i (-a) = -lp.single p i a := by
  refine' ext (funext (fun (j : α) => _))
  -- ⊢ ↑(lp.single p i (-a)) j = ↑(-lp.single p i a) j
  by_cases hi : j = i
  -- ⊢ ↑(lp.single p i (-a)) j = ↑(-lp.single p i a) j
  · subst hi
    -- ⊢ ↑(lp.single p j (-a)) j = ↑(-lp.single p j a) j
    simp [lp.single_apply_self]
    -- 🎉 no goals
  · simp [lp.single_apply_ne p i _ hi]
    -- 🎉 no goals
#align lp.single_neg lp.single_neg

@[simp]
protected theorem single_smul (p) (i : α) (a : E i) (c : 𝕜) :
    lp.single p i (c • a) = c • lp.single p i a := by
  refine' ext (funext (fun (j : α) => _))
  -- ⊢ ↑(lp.single p i (c • a)) j = ↑(c • lp.single p i a) j
  by_cases hi : j = i
  -- ⊢ ↑(lp.single p i (c • a)) j = ↑(c • lp.single p i a) j
  · subst hi
    -- ⊢ ↑(lp.single p j (c • a)) j = ↑(c • lp.single p j a) j
    dsimp
    -- ⊢ ↑(lp.single p j (c • a)) j = c • ↑(lp.single p j a) j
    simp [lp.single_apply_self]
    -- 🎉 no goals
  · dsimp
    -- ⊢ ↑(lp.single p i (c • a)) j = c • ↑(lp.single p i a) j
    simp [lp.single_apply_ne p i _ hi]
    -- 🎉 no goals
#align lp.single_smul lp.single_smul

protected theorem norm_sum_single (hp : 0 < p.toReal) (f : ∀ i, E i) (s : Finset α) :
    ‖∑ i in s, lp.single p i (f i)‖ ^ p.toReal = ∑ i in s, ‖f i‖ ^ p.toReal := by
  refine' (hasSum_norm hp (∑ i in s, lp.single p i (f i))).unique _
  -- ⊢ HasSum (fun i => ‖↑(∑ i in s, lp.single p i (f i)) i‖ ^ ENNReal.toReal p) (∑ …
  simp only [lp.single_apply, coeFn_sum, Finset.sum_apply, Finset.sum_dite_eq]
  -- ⊢ HasSum (fun i => ‖if i ∈ s then f i else 0‖ ^ ENNReal.toReal p) (∑ i in s, ‖ …
  have h : ∀ (i) (_ : i ∉ s), ‖ite (i ∈ s) (f i) 0‖ ^ p.toReal = 0 := by
    intro i hi
    simp [if_neg hi, Real.zero_rpow hp.ne']
  have h' : ∀ i ∈ s, ‖f i‖ ^ p.toReal = ‖ite (i ∈ s) (f i) 0‖ ^ p.toReal := by
    intro i hi
    rw [if_pos hi]
  simpa [Finset.sum_congr rfl h'] using hasSum_sum_of_ne_finset_zero h
  -- 🎉 no goals
#align lp.norm_sum_single lp.norm_sum_single

protected theorem norm_single (hp : 0 < p.toReal) (f : ∀ i, E i) (i : α) :
    ‖lp.single p i (f i)‖ = ‖f i‖ := by
  refine' Real.rpow_left_injOn hp.ne' (norm_nonneg' _) (norm_nonneg _) _
  -- ⊢ (fun y => y ^ ENNReal.toReal p) ‖lp.single p i (f i)‖ = (fun y => y ^ ENNRea …
  simpa using lp.norm_sum_single hp f {i}
  -- 🎉 no goals
#align lp.norm_single lp.norm_single

protected theorem norm_sub_norm_compl_sub_single (hp : 0 < p.toReal) (f : lp E p) (s : Finset α) :
    ‖f‖ ^ p.toReal - ‖f - ∑ i in s, lp.single p i (f i)‖ ^ p.toReal =
      ∑ i in s, ‖f i‖ ^ p.toReal := by
  refine' ((hasSum_norm hp f).sub (hasSum_norm hp (f - ∑ i in s, lp.single p i (f i)))).unique _
  -- ⊢ HasSum (fun b => ‖↑f b‖ ^ ENNReal.toReal p - ‖↑(f - ∑ i in s, lp.single p i  …
  let F : α → ℝ := fun i => ‖f i‖ ^ p.toReal - ‖(f - ∑ i in s, lp.single p i (f i)) i‖ ^ p.toReal
  -- ⊢ HasSum (fun b => ‖↑f b‖ ^ ENNReal.toReal p - ‖↑(f - ∑ i in s, lp.single p i  …
  have hF : ∀ (i) (_ : i ∉ s), F i = 0 := by
    intro i hi
    suffices ‖f i‖ ^ p.toReal - ‖f i - ite (i ∈ s) (f i) 0‖ ^ p.toReal = 0 by
      simpa only [coeFn_sum, lp.single_apply, coeFn_sub, Pi.sub_apply, Finset.sum_apply,
        Finset.sum_dite_eq] using this
    simp only [if_neg hi, sub_zero, sub_self]
  have hF' : ∀ i ∈ s, F i = ‖f i‖ ^ p.toReal := by
    intro i hi
    simp only [coeFn_sum, lp.single_apply, if_pos hi, sub_self, eq_self_iff_true, coeFn_sub,
      Pi.sub_apply, Finset.sum_apply, Finset.sum_dite_eq, sub_eq_self]
    simp [Real.zero_rpow hp.ne']
  have : HasSum F (∑ i in s, F i) := hasSum_sum_of_ne_finset_zero hF
  -- ⊢ HasSum (fun b => ‖↑f b‖ ^ ENNReal.toReal p - ‖↑(f - ∑ i in s, lp.single p i  …
  rwa [Finset.sum_congr rfl hF'] at this
  -- 🎉 no goals
#align lp.norm_sub_norm_compl_sub_single lp.norm_sub_norm_compl_sub_single

protected theorem norm_compl_sum_single (hp : 0 < p.toReal) (f : lp E p) (s : Finset α) :
    ‖f - ∑ i in s, lp.single p i (f i)‖ ^ p.toReal = ‖f‖ ^ p.toReal - ∑ i in s, ‖f i‖ ^ p.toReal :=
  by linarith [lp.norm_sub_norm_compl_sub_single hp f s]
     -- 🎉 no goals
#align lp.norm_compl_sum_single lp.norm_compl_sum_single

/-- The canonical finitely-supported approximations to an element `f` of `lp` converge to it, in the
`lp` topology. -/
protected theorem hasSum_single [Fact (1 ≤ p)] (hp : p ≠ ⊤) (f : lp E p) :
    HasSum (fun i : α => lp.single p i (f i : E i)) f := by
  have hp₀ : 0 < p := zero_lt_one.trans_le Fact.out
  -- ⊢ HasSum (fun i => lp.single p i (↑f i)) f
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp₀.ne' hp
  -- ⊢ HasSum (fun i => lp.single p i (↑f i)) f
  have := lp.hasSum_norm hp' f
  -- ⊢ HasSum (fun i => lp.single p i (↑f i)) f
  rw [HasSum, Metric.tendsto_nhds] at this ⊢
  -- ⊢ ∀ (ε : ℝ), ε > 0 → ∀ᶠ (x : Finset α) in Filter.atTop, dist (∑ b in x, lp.sin …
  intro ε hε
  -- ⊢ ∀ᶠ (x : Finset α) in Filter.atTop, dist (∑ b in x, lp.single p b (↑f b)) f < ε
  refine' (this _ (Real.rpow_pos_of_pos hε p.toReal)).mono _
  -- ⊢ ∀ (x : Finset α), dist (∑ b in x, ‖↑f b‖ ^ ENNReal.toReal p) (‖f‖ ^ ENNReal. …
  intro s hs
  -- ⊢ dist (∑ b in s, lp.single p b (↑f b)) f < ε
  rw [← Real.rpow_lt_rpow_iff dist_nonneg (le_of_lt hε) hp']
  -- ⊢ dist (∑ b in s, lp.single p b (↑f b)) f ^ ENNReal.toReal p < ε ^ ENNReal.toR …
  rw [dist_comm] at hs
  -- ⊢ dist (∑ b in s, lp.single p b (↑f b)) f ^ ENNReal.toReal p < ε ^ ENNReal.toR …
  simp only [dist_eq_norm, Real.norm_eq_abs] at hs ⊢
  -- ⊢ ‖∑ x in s, lp.single p x (↑f x) - f‖ ^ ENNReal.toReal p < ε ^ ENNReal.toReal p
  have H : ‖(∑ i in s, lp.single p i (f i : E i)) - f‖ ^ p.toReal =
      ‖f‖ ^ p.toReal - ∑ i in s, ‖f i‖ ^ p.toReal := by
    simpa only [coeFn_neg, Pi.neg_apply, lp.single_neg, Finset.sum_neg_distrib, neg_sub_neg,
      norm_neg, _root_.norm_neg] using lp.norm_compl_sum_single hp' (-f) s
  rw [← H] at hs
  -- ⊢ ‖∑ x in s, lp.single p x (↑f x) - f‖ ^ ENNReal.toReal p < ε ^ ENNReal.toReal p
  have : |‖(∑ i in s, lp.single p i (f i : E i)) - f‖ ^ p.toReal| =
      ‖(∑ i in s, lp.single p i (f i : E i)) - f‖ ^ p.toReal := by
    simp only [Real.abs_rpow_of_nonneg (norm_nonneg _), abs_norm]
  exact this ▸ hs
  -- 🎉 no goals
#align lp.has_sum_single lp.hasSum_single

end Single

section Topology

open Filter

open scoped Topology uniformity

/-- The coercion from `lp E p` to `∀ i, E i` is uniformly continuous. -/
theorem uniformContinuous_coe [_i : Fact (1 ≤ p)] :
    UniformContinuous (α := lp E p) ((↑) : lp E p → ∀ i, E i) := by
  have hp : p ≠ 0 := (zero_lt_one.trans_le _i.elim).ne'
  -- ⊢ UniformContinuous Subtype.val
  rw [uniformContinuous_pi]
  -- ⊢ ∀ (i : α), UniformContinuous fun x => ↑x i
  intro i
  -- ⊢ UniformContinuous fun x => ↑x i
  rw [NormedAddCommGroup.uniformity_basis_dist.uniformContinuous_iff
    NormedAddCommGroup.uniformity_basis_dist]
  intro ε hε
  -- ⊢ ∃ j, 0 < j ∧ ∀ (x y : { x // x ∈ lp E p }), (x, y) ∈ {p_1 | ‖p_1.fst - p_1.s …
  refine' ⟨ε, hε, _⟩
  -- ⊢ ∀ (x y : { x // x ∈ lp E p }), (x, y) ∈ {p_1 | ‖p_1.fst - p_1.snd‖ < ε} → (↑ …
  rintro f g (hfg : ‖f - g‖ < ε)
  -- ⊢ (↑f i, ↑g i) ∈ {p | ‖p.fst - p.snd‖ < ε}
  have : ‖f i - g i‖ ≤ ‖f - g‖ := norm_apply_le_norm hp (f - g) i
  -- ⊢ (↑f i, ↑g i) ∈ {p | ‖p.fst - p.snd‖ < ε}
  exact this.trans_lt hfg
  -- 🎉 no goals
#align lp.uniform_continuous_coe lp.uniformContinuous_coe

variable {ι : Type*} {l : Filter ι} [Filter.NeBot l]

theorem norm_apply_le_of_tendsto {C : ℝ} {F : ι → lp E ∞} (hCF : ∀ᶠ k in l, ‖F k‖ ≤ C)
    {f : ∀ a, E a} (hf : Tendsto (id fun i => F i : ι → ∀ a, E a) l (𝓝 f)) (a : α) : ‖f a‖ ≤ C := by
  have : Tendsto (fun k => ‖F k a‖) l (𝓝 ‖f a‖) :=
    (Tendsto.comp (continuous_apply a).continuousAt hf).norm
  refine' le_of_tendsto this (hCF.mono _)
  -- ⊢ ∀ (x : ι), ‖F x‖ ≤ C → ‖↑(F x) a‖ ≤ C
  intro k hCFk
  -- ⊢ ‖↑(F k) a‖ ≤ C
  exact (norm_apply_le_norm ENNReal.top_ne_zero (F k) a).trans hCFk
  -- 🎉 no goals
#align lp.norm_apply_le_of_tendsto lp.norm_apply_le_of_tendsto

variable [_i : Fact (1 ≤ p)]

theorem sum_rpow_le_of_tendsto (hp : p ≠ ∞) {C : ℝ} {F : ι → lp E p} (hCF : ∀ᶠ k in l, ‖F k‖ ≤ C)
    {f : ∀ a, E a} (hf : Tendsto (id fun i => F i : ι → ∀ a, E a) l (𝓝 f)) (s : Finset α) :
    ∑ i : α in s, ‖f i‖ ^ p.toReal ≤ C ^ p.toReal := by
  have hp' : p ≠ 0 := (zero_lt_one.trans_le _i.elim).ne'
  -- ⊢ ∑ i in s, ‖f i‖ ^ ENNReal.toReal p ≤ C ^ ENNReal.toReal p
  have hp'' : 0 < p.toReal := ENNReal.toReal_pos hp' hp
  -- ⊢ ∑ i in s, ‖f i‖ ^ ENNReal.toReal p ≤ C ^ ENNReal.toReal p
  let G : (∀ a, E a) → ℝ := fun f => ∑ a in s, ‖f a‖ ^ p.toReal
  -- ⊢ ∑ i in s, ‖f i‖ ^ ENNReal.toReal p ≤ C ^ ENNReal.toReal p
  have hG : Continuous G := by
    refine' continuous_finset_sum s _
    intro a _
    have : Continuous fun f : ∀ a, E a => f a := continuous_apply a
    exact this.norm.rpow_const fun _ => Or.inr hp''.le
  refine' le_of_tendsto (hG.continuousAt.tendsto.comp hf) _
  -- ⊢ ∀ᶠ (c : ι) in l, (G ∘ id fun i => ↑(F i)) c ≤ C ^ ENNReal.toReal p
  refine' hCF.mono _
  -- ⊢ ∀ (x : ι), ‖F x‖ ≤ C → (G ∘ id fun i => ↑(F i)) x ≤ C ^ ENNReal.toReal p
  intro k hCFk
  -- ⊢ (G ∘ id fun i => ↑(F i)) k ≤ C ^ ENNReal.toReal p
  refine' (lp.sum_rpow_le_norm_rpow hp'' (F k) s).trans _
  -- ⊢ ‖F k‖ ^ ENNReal.toReal p ≤ C ^ ENNReal.toReal p
  exact Real.rpow_le_rpow (norm_nonneg _) hCFk hp''.le
  -- 🎉 no goals
#align lp.sum_rpow_le_of_tendsto lp.sum_rpow_le_of_tendsto

/-- "Semicontinuity of the `lp` norm": If all sufficiently large elements of a sequence in `lp E p`
 have `lp` norm `≤ C`, then the pointwise limit, if it exists, also has `lp` norm `≤ C`. -/
theorem norm_le_of_tendsto {C : ℝ} {F : ι → lp E p} (hCF : ∀ᶠ k in l, ‖F k‖ ≤ C) {f : lp E p}
    (hf : Tendsto (id fun i => F i : ι → ∀ a, E a) l (𝓝 f)) : ‖f‖ ≤ C := by
  obtain ⟨i, hi⟩ := hCF.exists
  -- ⊢ ‖f‖ ≤ C
  have hC : 0 ≤ C := (norm_nonneg _).trans hi
  -- ⊢ ‖f‖ ≤ C
  rcases eq_top_or_lt_top p with (rfl | hp)
  -- ⊢ ‖f‖ ≤ C
  · apply norm_le_of_forall_le hC
    -- ⊢ ∀ (i : α), ‖↑f i‖ ≤ C
    exact norm_apply_le_of_tendsto hCF hf
    -- 🎉 no goals
  · have : 0 < p := zero_lt_one.trans_le _i.elim
    -- ⊢ ‖f‖ ≤ C
    have hp' : 0 < p.toReal := ENNReal.toReal_pos this.ne' hp.ne
    -- ⊢ ‖f‖ ≤ C
    apply norm_le_of_forall_sum_le hp' hC
    -- ⊢ ∀ (s : Finset α), ∑ i in s, ‖↑f i‖ ^ ENNReal.toReal p ≤ C ^ ENNReal.toReal p
    exact sum_rpow_le_of_tendsto hp.ne hCF hf
    -- 🎉 no goals
#align lp.norm_le_of_tendsto lp.norm_le_of_tendsto

/-- If `f` is the pointwise limit of a bounded sequence in `lp E p`, then `f` is in `lp E p`. -/
theorem memℓp_of_tendsto {F : ι → lp E p} (hF : Metric.Bounded (Set.range F)) {f : ∀ a, E a}
    (hf : Tendsto (id fun i => F i : ι → ∀ a, E a) l (𝓝 f)) : Memℓp f p := by
  obtain ⟨C, _, hCF'⟩ := hF.exists_pos_norm_le
  -- ⊢ Memℓp f p
  have hCF : ∀ k, ‖F k‖ ≤ C := fun k => hCF' _ ⟨k, rfl⟩
  -- ⊢ Memℓp f p
  rcases eq_top_or_lt_top p with (rfl | hp)
  -- ⊢ Memℓp f ⊤
  · apply memℓp_infty
    -- ⊢ BddAbove (Set.range fun i => ‖f i‖)
    use C
    -- ⊢ C ∈ upperBounds (Set.range fun i => ‖f i‖)
    rintro _ ⟨a, rfl⟩
    -- ⊢ (fun i => ‖f i‖) a ≤ C
    refine' norm_apply_le_of_tendsto (eventually_of_forall hCF) hf a
    -- 🎉 no goals
  · apply memℓp_gen'
    -- ⊢ ∀ (s : Finset α), ∑ i in s, ‖f i‖ ^ ENNReal.toReal p ≤ ?intro.intro.inr.C
    exact sum_rpow_le_of_tendsto hp.ne (eventually_of_forall hCF) hf
    -- 🎉 no goals
#align lp.mem_ℓp_of_tendsto lp.memℓp_of_tendsto

/-- If a sequence is Cauchy in the `lp E p` topology and pointwise convergent to an element `f` of
`lp E p`, then it converges to `f` in the `lp E p` topology. -/
theorem tendsto_lp_of_tendsto_pi {F : ℕ → lp E p} (hF : CauchySeq F) {f : lp E p}
    (hf : Tendsto (id fun i => F i : ℕ → ∀ a, E a) atTop (𝓝 f)) : Tendsto F atTop (𝓝 f) := by
  rw [Metric.nhds_basis_closedBall.tendsto_right_iff]
  -- ⊢ ∀ (i : ℝ), 0 < i → ∀ᶠ (x : ℕ) in atTop, F x ∈ Metric.closedBall f i
  intro ε hε
  -- ⊢ ∀ᶠ (x : ℕ) in atTop, F x ∈ Metric.closedBall f ε
  have hε' : { p : lp E p × lp E p | ‖p.1 - p.2‖ < ε } ∈ uniformity (lp E p) :=
    NormedAddCommGroup.uniformity_basis_dist.mem_of_mem hε
  refine' (hF.eventually_eventually hε').mono _
  -- ⊢ ∀ (x : ℕ), (∀ᶠ (l : ℕ) in atTop, (F x, F l) ∈ {p_1 | ‖p_1.fst - p_1.snd‖ < ε …
  rintro n (hn : ∀ᶠ l in atTop, ‖(fun f => F n - f) (F l)‖ < ε)
  -- ⊢ F n ∈ Metric.closedBall f ε
  refine' norm_le_of_tendsto (hn.mono fun k hk => hk.le) _
  -- ⊢ Tendsto (id fun i => ↑((fun f => F n - f) (F i))) atTop (𝓝 ↑(F n - f))
  rw [tendsto_pi_nhds]
  -- ⊢ ∀ (x : α), Tendsto (fun i => id (fun i => ↑((fun f => F n - f) (F i))) i x)  …
  intro a
  -- ⊢ Tendsto (fun i => id (fun i => ↑((fun f => F n - f) (F i))) i a) atTop (𝓝 (↑ …
  exact (hf.apply a).const_sub (F n a)
  -- 🎉 no goals
#align lp.tendsto_lp_of_tendsto_pi lp.tendsto_lp_of_tendsto_pi

variable [∀ a, CompleteSpace (E a)]

instance completeSpace : CompleteSpace (lp E p) :=
  Metric.complete_of_cauchySeq_tendsto (by
    intro F hF
    -- ⊢ ∃ a, Tendsto F atTop (𝓝 a)
    -- A Cauchy sequence in `lp E p` is pointwise convergent; let `f` be the pointwise limit.
    obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete
      ((uniformContinuous_coe (p := p)).comp_cauchySeq hF)
    -- Since the Cauchy sequence is bounded, its pointwise limit `f` is in `lp E p`.
    have hf' : Memℓp f p := memℓp_of_tendsto hF.bounded_range hf
    -- ⊢ ∃ a, Tendsto F atTop (𝓝 a)
    -- And therefore `f` is its limit in the `lp E p` topology as well as pointwise.
    exact ⟨⟨f, hf'⟩, tendsto_lp_of_tendsto_pi hF hf⟩)
    -- 🎉 no goals

end Topology

end lp

section Lipschitz

open ENNReal lp

lemma LipschitzWith.uniformly_bounded [PseudoMetricSpace α] (g : α → ι → ℝ) {K : ℝ≥0}
    (hg : ∀ i, LipschitzWith K (g · i)) (a₀ : α) (hga₀b : Memℓp (g a₀) ∞) (a : α) :
    Memℓp (g a) ∞ := by
  rcases hga₀b with ⟨M, hM⟩
  -- ⊢ Memℓp (g a) ⊤
  use ↑K * dist a a₀ + M
  -- ⊢ ↑K * dist a a₀ + M ∈ upperBounds (Set.range fun i => ‖g a i‖)
  rintro - ⟨i, rfl⟩
  -- ⊢ (fun i => ‖g a i‖) i ≤ ↑K * dist a a₀ + M
  calc
    |g a i| = |g a i - g a₀ i + g a₀ i| := by simp
    _ ≤ |g a i - g a₀ i| + |g a₀ i| := abs_add _ _
    _ ≤ ↑K * dist a a₀ + M := by
        gcongr
        · exact lipschitzWith_iff_dist_le_mul.1 (hg i) a a₀
        · exact hM ⟨i, rfl⟩

theorem LipschitzOnWith.coordinate [PseudoMetricSpace α] (f : α → ℓ^∞(ι)) (s : Set α) (K : ℝ≥0) :
    LipschitzOnWith K f s ↔ ∀ i : ι, LipschitzOnWith K (fun a : α ↦ f a i) s := by
  simp_rw [lipschitzOnWith_iff_dist_le_mul]
  -- ⊢ (∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → dist (f x) (f y) ≤ ↑K * dist x y) ↔ ∀ …
  constructor
  -- ⊢ (∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → dist (f x) (f y) ≤ ↑K * dist x y) → ∀ …
  · intro hfl i x hx y hy
    -- ⊢ dist (↑(f x) i) (↑(f y) i) ≤ ↑K * dist x y
    calc
      dist (f x i) (f y i) ≤ dist (f x) (f y) := lp.norm_apply_le_norm top_ne_zero (f x - f y) i
      _ ≤ K * dist x y := hfl x hx y hy
  · intro hgl x hx y hy
    -- ⊢ dist (f x) (f y) ≤ ↑K * dist x y
    apply lp.norm_le_of_forall_le; positivity
    -- ⊢ 0 ≤ ↑K * dist x y
                                   -- ⊢ ∀ (i : ι), ‖↑(f x - f y) i‖ ≤ ↑K * dist x y
    intro i
    -- ⊢ ‖↑(f x - f y) i‖ ≤ ↑K * dist x y
    apply hgl i x hx y hy
    -- 🎉 no goals

theorem LipschitzWith.coordinate [PseudoMetricSpace α] {f : α → ℓ^∞(ι)} (K : ℝ≥0) :
    LipschitzWith K f ↔ ∀ i : ι, LipschitzWith K (fun a : α ↦ f a i) := by
  simp_rw [← lipschitz_on_univ]
  -- ⊢ LipschitzOnWith K f Set.univ ↔ ∀ (i : ι), LipschitzOnWith K (fun a => ↑(f a) …
  apply LipschitzOnWith.coordinate
  -- 🎉 no goals

end Lipschitz
