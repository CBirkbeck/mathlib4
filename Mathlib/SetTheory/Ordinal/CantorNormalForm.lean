/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Violeta Hernández Palacios
-/
import Mathlib.Data.Finsupp.AList
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Cantor Normal Form

The Cantor normal form of an ordinal is generally defined as its base `ω` expansion, with its
non-zero exponents in decreasing order. Here, we more generally define a base `b` expansion
`Ordinal.CNF` in this manner, which is well-behaved for any `b ≥ 2`.

# Implementation notes

We implement `Ordinal.CNF` as an association list, where keys are exponents and values are
coefficients. This is because this structure intrinsically reflects two key properties of the Cantor
normal form:

- It is ordered.
- It has finitely many entries.

# Todo

- Prove the basic results relating the CNF to the arithmetic operations on ordinals.
-/


noncomputable section

universe u

open List

namespace Ordinal

/-- Inducts on the base `b` expansion of an ordinal. -/
@[elab_as_elim]
noncomputable def CNFRec (b : Ordinal) {C : Ordinal → Sort*} (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) (o : Ordinal) : C o :=
  if h : o = 0 then h ▸ H0 else H o h (CNFRec _ H0 H (o % b ^ log b o))
termination_by o
decreasing_by exact mod_opow_log_lt_self b h

@[simp]
theorem CNFRec_zero {C : Ordinal → Sort*} (b : Ordinal) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) : CNFRec b H0 H 0 = H0 := by
  rw [CNFRec, dif_pos rfl]

theorem CNFRec_pos (b : Ordinal) {o : Ordinal} {C : Ordinal → Sort*} (ho : o ≠ 0) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) :
    CNFRec b H0 H o = H o ho (@CNFRec b C H0 H _) := by
  rw [CNFRec, dif_neg ho]

/-- The Cantor normal form of an ordinal `o` is the list of coefficients and exponents in the
base-`b` expansion of `o`.

We special-case `CNF 0 o = CNF 1 o = [(0, o)]` for `o ≠ 0`.

`CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)]` -/
@[pp_nodot]
def CNF (b o : Ordinal) : List (Σ _ : Ordinal, Ordinal) :=
  CNFRec b [] (fun o _ho IH ↦ ⟨log b o, o / b ^ log b o⟩::IH) o

/-- The exponents of the Cantor normal form are stored in the first entries. -/
abbrev CNF.exponents (b o : Ordinal) := (CNF b o).keys
/-- The coefficients of the Cantor normal form are stored in the second entries. -/
abbrev CNF.coefficients (b o : Ordinal) := (CNF b o).map Sigma.snd

@[simp]
theorem CNF_zero (b : Ordinal) : CNF b 0 = [] :=
  CNFRec_zero b _ _

@[simp]
theorem CNF.exponents_zero (b : Ordinal) : CNF.exponents b 0 = [] := by
  rw [exponents, CNF_zero, keys_nil]

@[simp]
theorem CNF.coefficients_zero (b : Ordinal) : CNF.coefficients b 0 = [] := by
  rw [coefficients, CNF_zero, map_nil]

/-- Recursive definition for the Cantor normal form. -/
theorem CNF_ne_zero {b o : Ordinal} (ho : o ≠ 0) :
    CNF b o = ⟨log b o, o / b ^ log b o⟩::CNF b (o % b ^ log b o) :=
  CNFRec_pos b ho _ _

@[simp]
theorem CNF_eq_nil {b o : Ordinal} : CNF b o = [] ↔ o = 0 := by
  constructor
  · intro h
    by_contra ho
    rw [CNF_ne_zero ho] at h
    exact cons_ne_nil _ _ h
  · rintro rfl
    exact CNF_zero b

theorem zero_CNF {o : Ordinal} (ho : o ≠ 0) : CNF 0 o = [⟨0, o⟩] := by
  simp [CNF_ne_zero ho]

theorem one_CNF {o : Ordinal} (ho : o ≠ 0) : CNF 1 o = [⟨0, o⟩] := by
  simp [CNF_ne_zero ho]

theorem CNF_of_le_one {b o : Ordinal} (hb : b ≤ 1) (ho : o ≠ 0) : CNF b o = [⟨0, o⟩] := by
  rcases le_one_iff.1 hb with (rfl | rfl)
  · exact zero_CNF ho
  · exact one_CNF ho

theorem CNF_of_lt {b o : Ordinal} (ho : o ≠ 0) (hb : o < b) : CNF b o = [⟨0, o⟩] := by
  simp only [CNF_ne_zero ho, log_eq_zero hb, opow_zero, div_one, mod_one, CNF_zero]

theorem CNF_opow {b : Ordinal} (hb : 1 < b) (e : Ordinal) : CNF b (b^e) = [⟨e, 1⟩] := by
  have H := (opow_pos e (zero_le_one.trans_lt hb)).ne'
  rw [CNF_ne_zero H]
  simpa [log_opow hb e] using div_self H

theorem CNF_one {b : Ordinal} (hb : 1 < b) : CNF b 1 = [⟨0, 1⟩] := by
  convert CNF_opow hb 0
  exact (opow_zero b).symm

theorem CNF_self {b : Ordinal} (hb : 1 < b) : CNF b b = [⟨1, 1⟩] := by
  convert CNF_opow hb 1
  exact (opow_one b).symm

/-- Evaluating the Cantor normal form of an ordinal returns the ordinal. -/
theorem CNF_foldr (b o : Ordinal) : (CNF b o).foldr (fun p r ↦ b ^ p.1 * p.2 + r) 0 = o := by
  refine CNFRec b ?_ ?_ o
  · rw [CNF_zero]
    rfl
  · intro o ho IH
    rw [CNF_ne_zero ho, foldr_cons, IH, div_add_mod]

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `log b o`. -/
theorem le_log_of_mem_CNF_exponents {b o : Ordinal.{u}} {x : Ordinal} :
    x ∈ CNF.exponents b o → x ≤ log b o := by
  rw [CNF.exponents]
  refine CNFRec b ?_ ?_ o
  · rw [CNF_zero]
    rintro ⟨⟩
  · intro o ho H
    rw [CNF_ne_zero ho, keys_cons, mem_cons]
    rintro (rfl | h)
    · exact le_rfl
    · exact (H h).trans (log_mono_right _ (mod_opow_log_lt_self b ho).le)

/-- Every coefficient in a Cantor normal form is positive. -/
theorem pos_of_mem_CNF_coefficients {b o : Ordinal.{u}} {x : Ordinal} :
    x ∈ CNF.coefficients b o → 0 < x := by
  rw [CNF.coefficients]
  refine CNFRec b ?_ ?_ o
  · simp
  · intro o ho IH
    rw [CNF_ne_zero ho]
    rintro (h | ⟨_, h⟩)
    · exact div_opow_log_pos b ho
    · exact IH h

/-- Every coefficient in the Cantor normal form `CNF b o` is less than `b`. -/
theorem lt_of_mem_CNF_coefficients {b o : Ordinal.{u}} (hb : 1 < b) {x : Ordinal} :
    x ∈ CNF.coefficients b o → x < b := by
  rw [CNF.coefficients]
  refine CNFRec b ?_ ?_ o
  · rw [CNF_zero]
    rintro ⟨⟩
  · intro o ho IH h
    rw [CNF_ne_zero ho] at h
    cases' (mem_cons.mp h) with h h
    · rw [h]
      simpa only using div_opow_log_lt o hb
    · exact IH h

/-- The exponents of the `CNF` are a decreasing sequence. -/
theorem CNF_exponents_sorted (b o : Ordinal) : (CNF.exponents b o).Sorted (· > ·) := by
  rw [CNF.exponents]
  refine CNFRec b ?_ ?_ o
  · rw [CNF_zero]
    exact sorted_nil
  · intro o ho IH
    obtain hb | hb := le_or_gt b 1
    · rw [CNF_of_le_one hb ho]
      exact sorted_singleton _
    · obtain hob | hbo := lt_or_le o b
      · rw [CNF_of_lt ho hob]
        exact sorted_singleton _
      · rw [CNF_ne_zero ho, keys_cons, sorted_cons]
        refine ⟨?_, IH⟩
        intro a H
        exact (le_log_of_mem_CNF_exponents H).trans_lt <| log_mod_opow_log_lt_log_self hb hbo

open AList Finsupp

/-- Cantor normal form `CNF` as an `AList`. -/
@[pp_nodot]
def CNF_AList (b o : Ordinal) : AList (fun _ : Ordinal => Ordinal) where
  entries := CNF b o
  nodupKeys := (CNF_exponents_sorted b o).nodup

@[simp]
theorem CNF_AList_entries (b o : Ordinal) : (CNF_AList b o).entries = CNF b o :=
  rfl

@[simp]
theorem CNF_AList_keys (b o : Ordinal) : (CNF_AList b o).keys = CNF.exponents b o :=
  rfl

@[simp]
theorem CNF_AList_eq_empty {b o : Ordinal} : CNF_AList b o = ∅ ↔ o = 0 := by
  rw [AList.ext_iff]
  exact CNF_eq_nil

@[simp]
theorem mem_CNF_AList_iff {b o e : Ordinal} : e ∈ CNF_AList b o ↔ e ∈ CNF.exponents b o :=
  Iff.rfl

@[simp]
theorem mem_CNF_AList_lookup_iff {b o e c : Ordinal} :
    c ∈ (CNF_AList b o).lookup e ↔ ⟨e, c⟩ ∈ CNF b o :=
  mem_lookup_iff

/-- `CNF_coeff b o` is the finitely supported function, returning the coefficient of `b^e` in the
`CNF` of `o`, for each `e`. -/
@[pp_nodot]
def CNF_coeff (b o : Ordinal) : Ordinal →₀ Ordinal :=
  (CNF_AList b o).lookupFinsupp

theorem CNF_coeff_support (b o : Ordinal) :
    (CNF_coeff b o).support = (CNF.exponents b o).toFinset := by
  rw [CNF_coeff, lookupFinsupp_support]
  congr
  apply List.filter_eq_self.2
  intro a h
  exact decide_eq_true (pos_of_mem_CNF_coefficients (mem_map_of_mem _ h)).ne'

theorem CNF_coeff_of_mem_CNF {b o e c : Ordinal} (h : ⟨e, c⟩ ∈ CNF b o) :
    CNF_coeff b o e = c := by
  rw [← CNF_AList_entries] at h
  rw [CNF_coeff, lookupFinsupp_apply, mem_lookup_iff.2 h]
  rfl

theorem CNF_coeff_eq_pos_iff {b o e c : Ordinal} (hc : c ≠ 0) :
    CNF_coeff b o e = c ↔ ⟨e, c⟩ ∈ CNF b o := by
  rw [CNF_coeff, lookupFinsupp_eq_iff_of_ne_zero hc, mem_CNF_AList_lookup_iff]

theorem CNF_coeff_eq_zero_iff {b o e : Ordinal} : CNF_coeff b o e = 0 ↔ e ∉ CNF.exponents b o := by
  rw [CNF_coeff, lookupFinsupp_eq_zero_iff, mem_CNF_AList_lookup_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact (lt_irrefl 0 <| pos_of_mem_CNF_coefficients (mem_map_of_mem Sigma.snd h)).elim
  · exact Or.inl

alias ⟨_, CNF_coeff_of_not_mem_CNF⟩ := CNF_coeff_eq_zero_iff

theorem CNF_coeff_zero_apply (b e : Ordinal) : CNF_coeff b 0 e = 0 := by
  rw [CNF_coeff_eq_zero_iff, CNF.exponents_zero]
  exact not_mem_nil e

@[simp]
theorem CNF_coeff_zero (b : Ordinal) : CNF_coeff b 0 = 0 := by
  ext e
  exact CNF_coeff_zero_apply b e

theorem CNF_coeff_of_le_one {b : Ordinal} (hb : b ≤ 1) (o : Ordinal) :
    CNF_coeff b o = single 0 o := by
  ext a
  obtain rfl | ho := eq_or_ne o 0
  · simp
  · obtain rfl | ha := eq_or_ne a 0
    · apply CNF_coeff_of_mem_CNF
      rw [CNF_of_le_one hb ho]
      simp
    · rw [single_eq_of_ne ha.symm, CNF_coeff_eq_zero_iff, CNF.exponents, CNF_of_le_one hb ho]
      simpa using ha

@[simp]
theorem zero_CNF_coeff (o : Ordinal) : CNF_coeff 0 o = single 0 o :=
  CNF_coeff_of_le_one zero_le_one o

@[simp]
theorem one_CNF_coeff (o : Ordinal) : CNF_coeff 1 o = single 0 o :=
  CNF_coeff_of_le_one le_rfl o

theorem CNF_coeff_opow {b : Ordinal} (hb : 1 < b) (e : Ordinal) :
    CNF_coeff b (b^e) = single e 1 := by
  ext a
  obtain rfl | ha := eq_or_ne e a
  · rw [single_eq_same]
    apply CNF_coeff_of_mem_CNF
    rw [CNF_opow hb]
    exact mem_cons_self _ _
  · rw [single_eq_of_ne ha, CNF_coeff_eq_zero_iff, CNF.exponents, CNF_opow hb,
      List.keys_singleton, mem_singleton]
    exact ha.symm

theorem CNF_coeff_one {b : Ordinal} (hb : 1 < b) : CNF_coeff b 1 = single 0 1 := by
  convert CNF_coeff_opow hb 0
  exact (opow_zero b).symm

theorem CNF_coeff_self {b : Ordinal} (hb : 1 < b) : CNF_coeff b b = single 1 1 := by
  convert CNF_coeff_opow hb 1
  exact (opow_one b).symm

end Ordinal
