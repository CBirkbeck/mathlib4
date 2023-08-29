/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.Card

#align_import combinatorics.set_family.compression.down from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Down-compressions

This file defines down-compression.

Down-compressing `𝒜 : Finset (Finset α)` along `a : α` means removing `a` from the elements of `𝒜`,
when the resulting set is not already in `𝒜`.

## Main declarations

* `Finset.nonMemberSubfamily`: `𝒜.nonMemberSubfamily a` is the subfamily of sets not containing
  `a`.
* `Finset.memberSubfamily`: `𝒜.memberSubfamily a` is the image of the subfamily of sets containing
  `a` under removing `a`.
* `Down.compression`: Down-compression.

## Notation

`𝓓 a 𝒜` is notation for `Down.compress a 𝒜` in locale `SetFamily`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

compression, down-compression
-/


variable {α : Type*} [DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s : Finset α} {a : α}

namespace Finset

/-- Elements of `𝒜` that do not contain `a`. -/
def nonMemberSubfamily (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.filter fun s => a ∉ s
#align finset.non_member_subfamily Finset.nonMemberSubfamily

/-- Image of the elements of `𝒜` which contain `a` under removing `a`. Finsets that do not contain
`a` such that `insert a s ∈ 𝒜`. -/
def memberSubfamily (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  (𝒜.filter fun s => a ∈ s).image fun s => erase s a
#align finset.member_subfamily Finset.memberSubfamily

@[simp]
theorem mem_nonMemberSubfamily : s ∈ 𝒜.nonMemberSubfamily a ↔ s ∈ 𝒜 ∧ a ∉ s := by
  simp [nonMemberSubfamily]
  -- 🎉 no goals
#align finset.mem_non_member_subfamily Finset.mem_nonMemberSubfamily

@[simp]
theorem mem_memberSubfamily : s ∈ 𝒜.memberSubfamily a ↔ insert a s ∈ 𝒜 ∧ a ∉ s := by
  simp_rw [memberSubfamily, mem_image, mem_filter]
  -- ⊢ (∃ a_1, (a_1 ∈ 𝒜 ∧ a ∈ a_1) ∧ erase a_1 a = s) ↔ insert a s ∈ 𝒜 ∧ ¬a ∈ s
  refine' ⟨_, fun h => ⟨insert a s, ⟨h.1, by simp⟩, erase_insert h.2⟩⟩
  -- ⊢ (∃ a_1, (a_1 ∈ 𝒜 ∧ a ∈ a_1) ∧ erase a_1 a = s) → insert a s ∈ 𝒜 ∧ ¬a ∈ s
  rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
  -- ⊢ insert a (erase s a) ∈ 𝒜 ∧ ¬a ∈ erase s a
  rw [insert_erase hs2]
  -- ⊢ s ∈ 𝒜 ∧ ¬a ∈ erase s a
  exact ⟨hs1, not_mem_erase _ _⟩
  -- 🎉 no goals
#align finset.mem_member_subfamily Finset.mem_memberSubfamily

theorem nonMemberSubfamily_inter (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 ∩ ℬ).nonMemberSubfamily a = 𝒜.nonMemberSubfamily a ∩ ℬ.nonMemberSubfamily a :=
  filter_inter_distrib _ _ _
#align finset.non_member_subfamily_inter Finset.nonMemberSubfamily_inter

theorem memberSubfamily_inter (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 ∩ ℬ).memberSubfamily a = 𝒜.memberSubfamily a ∩ ℬ.memberSubfamily a := by
  unfold memberSubfamily
  -- ⊢ image (fun s => erase s a) (filter (fun s => a ∈ s) (𝒜 ∩ ℬ)) = image (fun s  …
  rw [filter_inter_distrib, image_inter_of_injOn _ _ ((erase_injOn' _).mono _)]
  -- ⊢ ↑(filter (fun s => a ∈ s) 𝒜) ∪ ↑(filter (fun s => a ∈ s) ℬ) ⊆ {s | a ∈ s}
  simp
  -- 🎉 no goals
#align finset.member_subfamily_inter Finset.memberSubfamily_inter

theorem nonMemberSubfamily_union (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 ∪ ℬ).nonMemberSubfamily a = 𝒜.nonMemberSubfamily a ∪ ℬ.nonMemberSubfamily a :=
  filter_union _ _ _
#align finset.non_member_subfamily_union Finset.nonMemberSubfamily_union

theorem memberSubfamily_union (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 ∪ ℬ).memberSubfamily a = 𝒜.memberSubfamily a ∪ ℬ.memberSubfamily a := by
  simp_rw [memberSubfamily, filter_union, image_union]
  -- 🎉 no goals
#align finset.member_subfamily_union Finset.memberSubfamily_union

theorem card_memberSubfamily_add_card_nonMemberSubfamily (a : α) (𝒜 : Finset (Finset α)) :
    (𝒜.memberSubfamily a).card + (𝒜.nonMemberSubfamily a).card = 𝒜.card := by
  rw [memberSubfamily, nonMemberSubfamily, card_image_of_injOn]
  -- ⊢ card (filter (fun s => a ∈ s) 𝒜) + card (filter (fun s => ¬a ∈ s) 𝒜) = card 𝒜
  · conv_rhs => rw [← filter_card_add_filter_neg_card_eq_card (fun s => (a ∈ s))]
    -- 🎉 no goals
  · apply (erase_injOn' _).mono
    -- ⊢ ↑(filter (fun s => a ∈ s) 𝒜) ⊆ {s | a ∈ s}
    simp
    -- 🎉 no goals
#align finset.card_member_subfamily_add_card_non_member_subfamily Finset.card_memberSubfamily_add_card_nonMemberSubfamily

theorem memberSubfamily_union_nonMemberSubfamily (a : α) (𝒜 : Finset (Finset α)) :
    𝒜.memberSubfamily a ∪ 𝒜.nonMemberSubfamily a = 𝒜.image fun s => s.erase a := by
  ext s
  -- ⊢ s ∈ memberSubfamily a 𝒜 ∪ nonMemberSubfamily a 𝒜 ↔ s ∈ image (fun s => erase …
  simp only [mem_union, mem_memberSubfamily, mem_nonMemberSubfamily, mem_image, exists_prop]
  -- ⊢ insert a s ∈ 𝒜 ∧ ¬a ∈ s ∨ s ∈ 𝒜 ∧ ¬a ∈ s ↔ ∃ a_1, a_1 ∈ 𝒜 ∧ erase a_1 a = s
  constructor
  -- ⊢ insert a s ∈ 𝒜 ∧ ¬a ∈ s ∨ s ∈ 𝒜 ∧ ¬a ∈ s → ∃ a_2, a_2 ∈ 𝒜 ∧ erase a_2 a = s
  · rintro (h | h)
    -- ⊢ ∃ a_1, a_1 ∈ 𝒜 ∧ erase a_1 a = s
    · exact ⟨_, h.1, erase_insert h.2⟩
      -- 🎉 no goals
    · exact ⟨_, h.1, erase_eq_of_not_mem h.2⟩
      -- 🎉 no goals
  · rintro ⟨s, hs, rfl⟩
    -- ⊢ insert a (erase s a) ∈ 𝒜 ∧ ¬a ∈ erase s a ∨ erase s a ∈ 𝒜 ∧ ¬a ∈ erase s a
    by_cases ha : a ∈ s
    -- ⊢ insert a (erase s a) ∈ 𝒜 ∧ ¬a ∈ erase s a ∨ erase s a ∈ 𝒜 ∧ ¬a ∈ erase s a
    · exact Or.inl ⟨by rwa [insert_erase ha], not_mem_erase _ _⟩
      -- 🎉 no goals
    · exact Or.inr ⟨by rwa [erase_eq_of_not_mem ha], not_mem_erase _ _⟩
      -- 🎉 no goals
#align finset.member_subfamily_union_non_member_subfamily Finset.memberSubfamily_union_nonMemberSubfamily

@[simp]
theorem memberSubfamily_memberSubfamily : (𝒜.memberSubfamily a).memberSubfamily a = ∅ := by
  ext
  -- ⊢ a✝ ∈ memberSubfamily a (memberSubfamily a 𝒜) ↔ a✝ ∈ ∅
  simp
  -- 🎉 no goals
#align finset.member_subfamily_member_subfamily Finset.memberSubfamily_memberSubfamily

@[simp]
theorem memberSubfamily_nonMemberSubfamily : (𝒜.nonMemberSubfamily a).memberSubfamily a = ∅ := by
  ext
  -- ⊢ a✝ ∈ memberSubfamily a (nonMemberSubfamily a 𝒜) ↔ a✝ ∈ ∅
  simp
  -- 🎉 no goals
#align finset.member_subfamily_non_member_subfamily Finset.memberSubfamily_nonMemberSubfamily

@[simp]
theorem nonMemberSubfamily_memberSubfamily :
    (𝒜.memberSubfamily a).nonMemberSubfamily a = 𝒜.memberSubfamily a := by
  ext
  -- ⊢ a✝ ∈ nonMemberSubfamily a (memberSubfamily a 𝒜) ↔ a✝ ∈ memberSubfamily a 𝒜
  simp
  -- 🎉 no goals
#align finset.non_member_subfamily_member_subfamily Finset.nonMemberSubfamily_memberSubfamily

@[simp]
theorem nonMemberSubfamily_nonMemberSubfamily :
    (𝒜.nonMemberSubfamily a).nonMemberSubfamily a = 𝒜.nonMemberSubfamily a := by
  ext
  -- ⊢ a✝ ∈ nonMemberSubfamily a (nonMemberSubfamily a 𝒜) ↔ a✝ ∈ nonMemberSubfamily …
  simp
  -- 🎉 no goals
#align finset.non_member_subfamily_non_member_subfamily Finset.nonMemberSubfamily_nonMemberSubfamily

end Finset

open Finset

-- The namespace is here to distinguish from other compressions.
namespace Down

/-- `a`-down-compressing `𝒜` means removing `a` from the elements of `𝒜` that contain it, when the
resulting Finset is not already in `𝒜`. -/
def compression (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  (𝒜.filter fun s => erase s a ∈ 𝒜).disjUnion
      ((𝒜.image fun s => erase s a).filter fun s => s ∉ 𝒜) <|
    disjoint_left.2 fun s h₁ h₂ => by
      have := (mem_filter.1 h₂).2
      -- ⊢ False
      exact this (mem_filter.1 h₁).1
      -- 🎉 no goals
#align down.compression Down.compression

-- mathport name: down.compression
@[inherit_doc]
scoped[FinsetFamily] notation "𝓓 " => Down.compression
-- Porting note: had to open this
open FinsetFamily

/-- `a` is in the down-compressed family iff it's in the original and its compression is in the
original, or it's not in the original but it's the compression of something in the original. -/
theorem mem_compression : s ∈ 𝓓 a 𝒜 ↔ s ∈ 𝒜 ∧ s.erase a ∈ 𝒜 ∨ s ∉ 𝒜 ∧ insert a s ∈ 𝒜 := by
  simp_rw [compression, mem_disjUnion, mem_filter, mem_image, and_comm (a := (¬ s ∈ 𝒜))]
  -- ⊢ s ∈ 𝒜 ∧ erase s a ∈ 𝒜 ∨ (∃ a_1, a_1 ∈ 𝒜 ∧ erase a_1 a = s) ∧ ¬s ∈ 𝒜 ↔ s ∈ 𝒜  …
  refine'
    or_congr_right
      (and_congr_left fun hs =>
        ⟨_, fun h => ⟨_, h, erase_insert <| insert_ne_self.1 <| ne_of_mem_of_not_mem h hs⟩⟩)
  rintro ⟨t, ht, rfl⟩
  -- ⊢ insert a (erase t a) ∈ 𝒜
  rwa [insert_erase (erase_ne_self.1 (ne_of_mem_of_not_mem ht hs).symm)]
  -- 🎉 no goals
#align down.mem_compression Down.mem_compression

theorem erase_mem_compression (hs : s ∈ 𝒜) : s.erase a ∈ 𝓓 a 𝒜 := by
  simp_rw [mem_compression, erase_idem, and_self_iff]
  -- ⊢ erase s a ∈ 𝒜 ∨ ¬erase s a ∈ 𝒜 ∧ insert a (erase s a) ∈ 𝒜
  refine' (em _).imp_right fun h => ⟨h, _⟩
  -- ⊢ insert a (erase s a) ∈ 𝒜
  rwa [insert_erase (erase_ne_self.1 (ne_of_mem_of_not_mem hs h).symm)]
  -- 🎉 no goals
#align down.erase_mem_compression Down.erase_mem_compression

-- This is a special case of `erase_mem_compression` once we have `compression_idem`.
theorem erase_mem_compression_of_mem_compression : s ∈ 𝓓 a 𝒜 → s.erase a ∈ 𝓓 a 𝒜 := by
  simp_rw [mem_compression, erase_idem]
  -- ⊢ s ∈ 𝒜 ∧ erase s a ∈ 𝒜 ∨ ¬s ∈ 𝒜 ∧ insert a s ∈ 𝒜 → erase s a ∈ 𝒜 ∧ erase s a  …
  refine' Or.imp (fun h => ⟨h.2, h.2⟩) fun h => _
  -- ⊢ ¬erase s a ∈ 𝒜 ∧ insert a (erase s a) ∈ 𝒜
  rwa [erase_eq_of_not_mem (insert_ne_self.1 <| ne_of_mem_of_not_mem h.2 h.1)]
  -- 🎉 no goals
#align down.erase_mem_compression_of_mem_compression Down.erase_mem_compression_of_mem_compression

theorem mem_compression_of_insert_mem_compression (h : insert a s ∈ 𝓓 a 𝒜) : s ∈ 𝓓 a 𝒜 := by
  by_cases ha : a ∈ s
  -- ⊢ s ∈ 𝓓 a 𝒜
  · rwa [insert_eq_of_mem ha] at h
    -- 🎉 no goals
  · rw [← erase_insert ha]
    -- ⊢ erase (insert a s) a ∈ 𝓓 a 𝒜
    exact erase_mem_compression_of_mem_compression h
    -- 🎉 no goals
#align down.mem_compression_of_insert_mem_compression Down.mem_compression_of_insert_mem_compression

/-- Down-compressing a family is idempotent. -/
@[simp]
theorem compression_idem (a : α) (𝒜 : Finset (Finset α)) : 𝓓 a (𝓓 a 𝒜) = 𝓓 a 𝒜 := by
  ext s
  -- ⊢ s ∈ 𝓓 a (𝓓 a 𝒜) ↔ s ∈ 𝓓 a 𝒜
  refine' mem_compression.trans ⟨_, fun h => Or.inl ⟨h, erase_mem_compression_of_mem_compression h⟩⟩
  -- ⊢ s ∈ 𝓓 a 𝒜 ∧ erase s a ∈ 𝓓 a 𝒜 ∨ ¬s ∈ 𝓓 a 𝒜 ∧ insert a s ∈ 𝓓 a 𝒜 → s ∈ 𝓓 a 𝒜
  rintro (h | h)
  -- ⊢ s ∈ 𝓓 a 𝒜
  · exact h.1
    -- 🎉 no goals
  · cases h.1 (mem_compression_of_insert_mem_compression h.2)
    -- 🎉 no goals
#align down.compression_idem Down.compression_idem

/-- Down-compressing a family doesn't change its size. -/
@[simp]
theorem card_compression (a : α) (𝒜 : Finset (Finset α)) : (𝓓 a 𝒜).card = 𝒜.card := by
  rw [compression, card_disjUnion, image_filter,
    card_image_of_injOn ((erase_injOn' _).mono fun s hs => _), ← card_disjoint_union]
  · conv_rhs => rw [← filter_union_filter_neg_eq (fun s => (erase s a ∈ 𝒜)) 𝒜]
    -- 🎉 no goals
  · exact disjoint_filter_filter_neg 𝒜 𝒜 (fun s => (erase s a ∈ 𝒜))
    -- 🎉 no goals
  intro s hs
  -- ⊢ s ∈ {s | a ∈ s}
  rw [mem_coe, mem_filter, Function.comp_apply] at hs
  -- ⊢ s ∈ {s | a ∈ s}
  exact not_imp_comm.1 erase_eq_of_not_mem (ne_of_mem_of_not_mem hs.1 hs.2).symm
  -- 🎉 no goals
#align down.card_compression Down.card_compression

end Down
