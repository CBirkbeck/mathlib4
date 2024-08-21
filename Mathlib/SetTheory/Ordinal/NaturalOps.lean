/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.SetTheory.Ordinal.CantorNormalForm
import Mathlib.Tactic.Abel

/-!
# Natural operations on ordinals

The goal of this file is to define natural addition and multiplication on ordinals, also known as
the Hessenberg sum and product, and provide a basic API. The natural addition of two ordinals
`a ♯ b` is recursively defined as the least ordinal greater than `a' ♯ b` and `a ♯ b'` for `a' < a`
and `b' < b`. The natural multiplication `a ⨳ b` is likewise recursively defined as the least
ordinal such that `a ⨳ b ♯ a' ⨳ b'` is greater than `a' ⨳ b ♯ a ⨳ b'` for any `a' < a` and
`b' < b`.

These operations form a rich algebraic structure: they're commutative, associative, preserve order,
have the usual `0` and `1` from ordinals, and distribute over one another.

Moreover, these operations are the addition and multiplication of ordinals when viewed as
combinatorial `Game`s. This makes them particularly useful for game theory.

Finally, both operations admit simple, intuitive descriptions in terms of the Cantor normal form.
The natural addition of two ordinals corresponds to adding their Cantor normal forms as if they were
polynomials in `ω`. Likewise, their natural multiplication corresponds to multiplying the Cantor
normal forms as polynomials. These results are proven as `CNF_coeff_nadd` and `CNF_coeff_nmul`.

# Implementation notes

Given the rich algebraic structure of these two operations, we choose to create a type synonym
`NatOrdinal`, where we provide the appropriate instances. However, to avoid casting back and forth
between both types, we attempt to prove and state most results on `Ordinal`.
-/

universe u v

open Function Order

noncomputable section

/-! ### Basic casts between `Ordinal` and `NatOrdinal` -/


/-- A type synonym for ordinals with natural addition and multiplication. -/
def NatOrdinal : Type _ :=
  -- Porting note: used to derive LinearOrder & SuccOrder but need to manually define
  Ordinal deriving Zero, Inhabited, One, WellFoundedRelation

instance NatOrdinal.linearOrder : LinearOrder NatOrdinal := {Ordinal.linearOrder with}

instance NatOrdinal.succOrder : SuccOrder NatOrdinal := {Ordinal.succOrder with}

/-- The identity function between `Ordinal` and `NatOrdinal`. -/
@[match_pattern]
def Ordinal.toNatOrdinal : Ordinal ≃o NatOrdinal :=
  OrderIso.refl _

/-- The identity function between `NatOrdinal` and `Ordinal`. -/
@[match_pattern]
def NatOrdinal.toOrdinal : NatOrdinal ≃o Ordinal :=
  OrderIso.refl _

namespace NatOrdinal

open Ordinal

@[simp]
theorem toOrdinal_symm_eq : NatOrdinal.toOrdinal.symm = Ordinal.toNatOrdinal :=
  rfl

-- Porting note: used to use dot notation, but doesn't work in Lean 4 with `OrderIso`
@[simp]
theorem toOrdinal_toNatOrdinal (a : NatOrdinal) :
    Ordinal.toNatOrdinal (NatOrdinal.toOrdinal a) = a := rfl

theorem lt_wf : @WellFounded NatOrdinal (· < ·) :=
  Ordinal.lt_wf

instance : WellFoundedLT NatOrdinal :=
  Ordinal.wellFoundedLT

instance : IsWellOrder NatOrdinal (· < ·) :=
  Ordinal.isWellOrder

@[simp]
theorem toOrdinal_zero : toOrdinal 0 = 0 :=
  rfl

@[simp]
theorem toOrdinal_one : toOrdinal 1 = 1 :=
  rfl

@[simp]
theorem toOrdinal_eq_zero (a) : toOrdinal a = 0 ↔ a = 0 :=
  Iff.rfl

@[simp]
theorem toOrdinal_eq_one (a) : toOrdinal a = 1 ↔ a = 1 :=
  Iff.rfl

@[simp]
theorem toOrdinal_max {a b : NatOrdinal} : toOrdinal (max a b) = max (toOrdinal a) (toOrdinal b) :=
  rfl

@[simp]
theorem toOrdinal_min {a b : NatOrdinal} : toOrdinal (min a b) = min (toOrdinal a) (toOrdinal b) :=
  rfl

theorem succ_def (a : NatOrdinal) : succ a = toNatOrdinal (toOrdinal a + 1) :=
  rfl

/-- A recursor for `NatOrdinal`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {β : NatOrdinal → Sort*} (h : ∀ a, β (toNatOrdinal a)) : ∀ a, β a := fun a =>
  h (toOrdinal a)

/-- `Ordinal.induction` but for `NatOrdinal`. -/
theorem induction {p : NatOrdinal → Prop} : ∀ (i) (_ : ∀ j, (∀ k, k < j → p k) → p j), p i :=
  Ordinal.induction

end NatOrdinal

namespace Ordinal

variable {a b c : Ordinal.{u}}

@[simp]
theorem toNatOrdinal_symm_eq : toNatOrdinal.symm = NatOrdinal.toOrdinal :=
  rfl

@[simp]
theorem toNatOrdinal_toOrdinal (a : Ordinal) :  NatOrdinal.toOrdinal (toNatOrdinal a) = a :=
  rfl

@[simp]
theorem toNatOrdinal_zero : toNatOrdinal 0 = 0 :=
  rfl

@[simp]
theorem toNatOrdinal_one : toNatOrdinal 1 = 1 :=
  rfl

@[simp]
theorem toNatOrdinal_eq_zero (a) : toNatOrdinal a = 0 ↔ a = 0 :=
  Iff.rfl

@[simp]
theorem toNatOrdinal_eq_one (a) : toNatOrdinal a = 1 ↔ a = 1 :=
  Iff.rfl

@[simp]
theorem toNatOrdinal_max (a b : Ordinal) :
    toNatOrdinal (max a b) = max (toNatOrdinal a) (toNatOrdinal b) :=
  rfl

@[simp]
theorem toNatOrdinal_min (a b : Ordinal) :
    toNatOrdinal (linearOrder.min a b) = linearOrder.min (toNatOrdinal a) (toNatOrdinal b) :=
  rfl

/-! We place the definitions of `nadd` and `nmul` before actually developing their API, as this
guarantees we only need to open the `NaturalOps` locale once. -/

/-- Natural addition on ordinals `a ♯ b`, also known as the Hessenberg sum, is recursively defined
as the least ordinal greater than `a' ♯ b` and `a ♯ b'` for all `a' < a` and `b' < b`. In contrast
to normal ordinal addition, it is commutative.

Natural addition can equivalently be characterized as the ordinal resulting from adding up
corresponding coefficients in the Cantor normal forms of `a` and `b`. -/
noncomputable def nadd (a b : Ordinal) : Ordinal :=
  max (blsub.{u, u} a fun a' _ => nadd a' b) (blsub.{u, u} b fun b' _ => nadd a b')
termination_by (a, b)

@[inherit_doc]
scoped[NaturalOps] infixl:65 " ♯ " => Ordinal.nadd

open NaturalOps

/-- Natural multiplication on ordinals `a ⨳ b`, also known as the Hessenberg product, is recursively
defined as the least ordinal such that `a ⨳ b + a' ⨳ b'` is greater than `a' ⨳ b + a ⨳ b'` for all
`a' < a` and `b < b'`. In contrast to normal ordinal multiplication, it is commutative and
distributive (over natural addition).

Natural multiplication can equivalently be characterized as the ordinal resulting from multiplying
the Cantor normal forms of `a` and `b` as if they were polynomials in `ω`. Addition of exponents is
done via natural addition. -/
noncomputable def nmul (a b : Ordinal.{u}) : Ordinal.{u} :=
  sInf {c | ∀ a' < a, ∀ b' < b, nmul a' b ♯ nmul a b' < c ♯ nmul a' b'}
termination_by (a, b)

@[inherit_doc]
scoped[NaturalOps] infixl:70 " ⨳ " => Ordinal.nmul

/-! ### Natural addition -/


theorem nadd_def (a b : Ordinal) :
    a ♯ b = max (blsub.{u, u} a fun a' _ => a' ♯ b) (blsub.{u, u} b fun b' _ => a ♯ b') := by
  rw [nadd]

theorem lt_nadd_iff : a < b ♯ c ↔ (∃ b' < b, a ≤ b' ♯ c) ∨ ∃ c' < c, a ≤ b ♯ c' := by
  rw [nadd_def]
  simp [lt_blsub_iff]

theorem nadd_le_iff : b ♯ c ≤ a ↔ (∀ b' < b, b' ♯ c < a) ∧ ∀ c' < c, b ♯ c' < a := by
  rw [nadd_def]
  simp [blsub_le_iff]

theorem nadd_lt_nadd_left (h : b < c) (a) : a ♯ b < a ♯ c :=
  lt_nadd_iff.2 (Or.inr ⟨b, h, le_rfl⟩)

theorem nadd_lt_nadd_right (h : b < c) (a) : b ♯ a < c ♯ a :=
  lt_nadd_iff.2 (Or.inl ⟨b, h, le_rfl⟩)

theorem nadd_le_nadd_left (h : b ≤ c) (a) : a ♯ b ≤ a ♯ c := by
  rcases lt_or_eq_of_le h with (h | rfl)
  · exact (nadd_lt_nadd_left h a).le
  · exact le_rfl

theorem nadd_le_nadd_right (h : b ≤ c) (a) : b ♯ a ≤ c ♯ a := by
  rcases lt_or_eq_of_le h with (h | rfl)
  · exact (nadd_lt_nadd_right h a).le
  · exact le_rfl

variable (a b)

theorem nadd_comm (a b) : a ♯ b = b ♯ a := by
  rw [nadd_def, nadd_def, max_comm]
  congr <;> ext <;> apply nadd_comm
termination_by (a, b)

theorem blsub_nadd_of_mono {f : ∀ c < a ♯ b, Ordinal.{max u v}}
    (hf : ∀ {i j} (hi hj), i ≤ j → f i hi ≤ f j hj) :
    -- Porting note: needed to add universe hint blsub.{u,v} in the line below
    blsub.{u,v} _ f =
      max (blsub.{u, v} a fun a' ha' => f (a' ♯ b) <| nadd_lt_nadd_right ha' b)
        (blsub.{u, v} b fun b' hb' => f (a ♯ b') <| nadd_lt_nadd_left hb' a) := by
  apply (blsub_le_iff.2 fun i h => _).antisymm (max_le _ _)
  · intro i h
    rcases lt_nadd_iff.1 h with (⟨a', ha', hi⟩ | ⟨b', hb', hi⟩)
    · exact lt_max_of_lt_left ((hf h (nadd_lt_nadd_right ha' b) hi).trans_lt (lt_blsub _ _ ha'))
    · exact lt_max_of_lt_right ((hf h (nadd_lt_nadd_left hb' a) hi).trans_lt (lt_blsub _ _ hb'))
  all_goals
    apply blsub_le_of_brange_subset.{u, u, v}
    rintro c ⟨d, hd, rfl⟩
    apply mem_brange_self

theorem nadd_assoc (a b c) : a ♯ b ♯ c = a ♯ (b ♯ c) := by
  rw [nadd_def a (b ♯ c), nadd_def, blsub_nadd_of_mono, blsub_nadd_of_mono, max_assoc]
  · congr <;> ext <;> apply nadd_assoc
  · exact fun _ _ h => nadd_le_nadd_left h a
  · exact fun _ _ h => nadd_le_nadd_right h c
termination_by (a, b, c)

@[simp]
theorem nadd_zero : a ♯ 0 = a := by
  induction' a using Ordinal.induction with a IH
  rw [nadd_def, blsub_zero, max_zero_right]
  convert blsub_id a
  rename_i hb
  exact IH _ hb

@[simp]
theorem zero_nadd : 0 ♯ a = a := by rw [nadd_comm, nadd_zero]

@[simp]
theorem nadd_one : a ♯ 1 = succ a := by
  induction' a using Ordinal.induction with a IH
  rw [nadd_def, blsub_one, nadd_zero, max_eq_right_iff, blsub_le_iff]
  intro i hi
  rwa [IH i hi, succ_lt_succ_iff]

@[simp]
theorem one_nadd : 1 ♯ a = succ a := by rw [nadd_comm, nadd_one]

theorem nadd_succ : a ♯ succ b = succ (a ♯ b) := by rw [← nadd_one (a ♯ b), nadd_assoc, nadd_one]

theorem succ_nadd : succ a ♯ b = succ (a ♯ b) := by rw [← one_nadd (a ♯ b), ← nadd_assoc, one_nadd]

@[simp]
theorem nadd_nat (n : ℕ) : a ♯ n = a + n := by
  induction' n with n hn
  · simp
  · rw [Nat.cast_succ, add_one_eq_succ, nadd_succ, add_succ, hn]

@[simp]
theorem nat_nadd (n : ℕ) : ↑n ♯ a = a + n := by rw [nadd_comm, nadd_nat]

theorem add_le_nadd : a + b ≤ a ♯ b := by
  induction b using limitRecOn with
  | H₁ => simp
  | H₂ c h =>
    rwa [add_succ, nadd_succ, succ_le_succ_iff]
  | H₃ c hc H =>
    simp_rw [← IsNormal.blsub_eq.{u, u} (add_isNormal a) hc, blsub_le_iff]
    exact fun i hi => (H i hi).trans_lt (nadd_lt_nadd_left hi a)

end Ordinal

namespace NatOrdinal

open Ordinal NaturalOps

instance : Add NatOrdinal :=
  ⟨nadd⟩

instance add_covariantClass_lt : CovariantClass NatOrdinal.{u} NatOrdinal.{u} (· + ·) (· < ·) :=
  ⟨fun a _ _ h => nadd_lt_nadd_left h a⟩

instance add_covariantClass_le : CovariantClass NatOrdinal.{u} NatOrdinal.{u} (· + ·) (· ≤ ·) :=
  ⟨fun a _ _ h => nadd_le_nadd_left h a⟩

instance add_contravariantClass_le :
    ContravariantClass NatOrdinal.{u} NatOrdinal.{u} (· + ·) (· ≤ ·) :=
  ⟨fun a b c h => by
    by_contra! h'
    exact h.not_lt (add_lt_add_left h' a)⟩

instance orderedCancelAddCommMonoid : OrderedCancelAddCommMonoid NatOrdinal :=
  { NatOrdinal.linearOrder with
    add := (· + ·)
    add_assoc := nadd_assoc
    add_le_add_left := fun a b => add_le_add_left
    le_of_add_le_add_left := fun a b c => le_of_add_le_add_left
    zero := 0
    zero_add := zero_nadd
    add_zero := nadd_zero
    add_comm := nadd_comm
    nsmul := nsmulRec }

instance addMonoidWithOne : AddMonoidWithOne NatOrdinal :=
  AddMonoidWithOne.unary

@[simp]
theorem add_one_eq_succ : ∀ a : NatOrdinal, a + 1 = succ a :=
  nadd_one

@[simp]
theorem toOrdinal_cast_nat (n : ℕ) : toOrdinal n = n := by
  induction' n with n hn
  · rfl
  · change (toOrdinal n) ♯ 1 = n + 1
    rw [hn]; exact nadd_one n

@[simp]
theorem _root_.Ordinal.toNatOrdinal_cast_nat (n : ℕ) : toNatOrdinal n = n := by
  rw [← toOrdinal_cast_nat n]
  rfl

instance : CharZero NatOrdinal where
  cast_injective := by
    intro a b h
    iterate 2 rw [← toNatOrdinal_cast_nat] at h
    rwa [toNatOrdinal.apply_eq_iff_eq, Nat.cast_inj] at h

end NatOrdinal

open NatOrdinal

open NaturalOps

namespace Ordinal

theorem nadd_eq_add (a b : Ordinal) : a ♯ b = toOrdinal (toNatOrdinal a + toNatOrdinal b) :=
  rfl

theorem lt_of_nadd_lt_nadd_left : ∀ {a b c}, a ♯ b < a ♯ c → b < c :=
  @lt_of_add_lt_add_left NatOrdinal _ _ _

theorem lt_of_nadd_lt_nadd_right : ∀ {a b c}, b ♯ a < c ♯ a → b < c :=
  @lt_of_add_lt_add_right NatOrdinal _ _ _

theorem le_of_nadd_le_nadd_left : ∀ {a b c}, a ♯ b ≤ a ♯ c → b ≤ c :=
  @le_of_add_le_add_left NatOrdinal _ _ _

theorem le_of_nadd_le_nadd_right : ∀ {a b c}, b ♯ a ≤ c ♯ a → b ≤ c :=
  @le_of_add_le_add_right NatOrdinal _ _ _

theorem nadd_lt_nadd_iff_left : ∀ (a) {b c}, a ♯ b < a ♯ c ↔ b < c :=
  @add_lt_add_iff_left NatOrdinal _ _ _ _

theorem nadd_lt_nadd_iff_right : ∀ (a) {b c}, b ♯ a < c ♯ a ↔ b < c :=
  @add_lt_add_iff_right NatOrdinal _ _ _ _

theorem nadd_le_nadd_iff_left : ∀ (a) {b c}, a ♯ b ≤ a ♯ c ↔ b ≤ c :=
  @add_le_add_iff_left NatOrdinal _ _ _ _

theorem nadd_le_nadd_iff_right : ∀ (a) {b c}, b ♯ a ≤ c ♯ a ↔ b ≤ c :=
  @_root_.add_le_add_iff_right NatOrdinal _ _ _ _

theorem nadd_le_nadd : ∀ {a b c d}, a ≤ b → c ≤ d → a ♯ c ≤ b ♯ d :=
  @add_le_add NatOrdinal _ _ _ _

theorem nadd_lt_nadd : ∀ {a b c d}, a < b → c < d → a ♯ c < b ♯ d :=
  @add_lt_add NatOrdinal _ _ _ _

theorem nadd_lt_nadd_of_lt_of_le : ∀ {a b c d}, a < b → c ≤ d → a ♯ c < b ♯ d :=
  @add_lt_add_of_lt_of_le NatOrdinal _ _ _ _

theorem nadd_lt_nadd_of_le_of_lt : ∀ {a b c d}, a ≤ b → c < d → a ♯ c < b ♯ d :=
  @add_lt_add_of_le_of_lt NatOrdinal _ _ _ _

theorem nadd_left_cancel : ∀ {a b c}, a ♯ b = a ♯ c → b = c :=
  @_root_.add_left_cancel NatOrdinal _ _

theorem nadd_right_cancel : ∀ {a b c}, a ♯ b = c ♯ b → a = c :=
  @_root_.add_right_cancel NatOrdinal _ _

theorem nadd_left_cancel_iff : ∀ {a b c}, a ♯ b = a ♯ c ↔ b = c :=
  @add_left_cancel_iff NatOrdinal _ _

theorem nadd_right_cancel_iff : ∀ {a b c}, b ♯ a = c ♯ a ↔ b = c :=
  @add_right_cancel_iff NatOrdinal _ _

theorem le_nadd_self (a b) : a ≤ b ♯ a := by
  simpa using nadd_le_nadd_right (Ordinal.zero_le b) a

theorem le_nadd_left {a c} (h : a ≤ c) (b) : a ≤ b ♯ c :=
  (le_nadd_self a b).trans (nadd_le_nadd_left h b)

theorem le_self_nadd (a b) : a ≤ a ♯ b := by
  simpa using nadd_le_nadd_left (Ordinal.zero_le b) a

theorem le_nadd_right {a b} (h : a ≤ b) (c) : a ≤ b ♯ c :=
  (le_self_nadd a c).trans (nadd_le_nadd_right h c)

theorem nadd_left_comm : ∀ a b c, a ♯ (b ♯ c) = b ♯ (a ♯ c) :=
  @add_left_comm NatOrdinal _

theorem nadd_right_comm : ∀ a b c, a ♯ b ♯ c = a ♯ c ♯ b :=
  @add_right_comm NatOrdinal _

theorem nadd_eq_zero_iff {a b} : a ♯ b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    rw [← Ordinal.le_zero, ← Ordinal.le_zero, ← h]
    exact ⟨le_self_nadd a b, le_nadd_self b a⟩
  · rintro ⟨rfl, rfl⟩
    exact nadd_zero 0

theorem nadd_ne_zero_iff {a b} : a ♯ b ≠ 0 ↔ a ≠ 0 ∨ b ≠ 0 := by
  rw [← not_iff_not]
  simpa using nadd_eq_zero_iff

theorem nadd_ne_zero_of_left {a} (h : a ≠ 0) (b) : a ♯ b ≠ 0 :=
  nadd_ne_zero_iff.2 <| Or.inl h

theorem nadd_ne_zero_of_right (a) {b} (h : b ≠ 0) : a ♯ b ≠ 0 :=
  nadd_ne_zero_iff.2 <| Or.inr h

/-! ### Natural multiplication -/


variable {a b c d : Ordinal.{u}}

theorem nmul_def (a b : Ordinal) :
    a ⨳ b = sInf {c | ∀ a' < a, ∀ b' < b, a' ⨳ b ♯ a ⨳ b' < c ♯ a' ⨳ b'} := by rw [nmul]

/-- The set in the definition of `nmul` is nonempty. -/
theorem nmul_nonempty (a b : Ordinal.{u}) :
    {c : Ordinal.{u} | ∀ a' < a, ∀ b' < b, a' ⨳ b ♯ a ⨳ b' < c ♯ a' ⨳ b'}.Nonempty :=
  ⟨_, fun _ ha _ hb => (lt_blsub₂.{u, u, u} _ ha hb).trans_le <| le_self_nadd _ _⟩

theorem nmul_nadd_lt {a' b' : Ordinal} (ha : a' < a) (hb : b' < b) :
    a' ⨳ b ♯ a ⨳ b' < a ⨳ b ♯ a' ⨳ b' := by
  rw [nmul_def a b]
  exact csInf_mem (nmul_nonempty a b) a' ha b' hb

theorem nmul_nadd_le {a' b' : Ordinal} (ha : a' ≤ a) (hb : b' ≤ b) :
    a' ⨳ b ♯ a ⨳ b' ≤ a ⨳ b ♯ a' ⨳ b' := by
  rcases lt_or_eq_of_le ha with (ha | rfl)
  · rcases lt_or_eq_of_le hb with (hb | rfl)
    · exact (nmul_nadd_lt ha hb).le
    · rw [nadd_comm]
  · exact le_rfl

theorem lt_nmul_iff : c < a ⨳ b ↔ ∃ a' < a, ∃ b' < b, c ♯ a' ⨳ b' ≤ a' ⨳ b ♯ a ⨳ b' := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [nmul] at h
    simpa using not_mem_of_lt_csInf h ⟨0, fun _ _ => bot_le⟩
  · rintro ⟨a', ha, b', hb, h⟩
    have := h.trans_lt (nmul_nadd_lt ha hb)
    rwa [nadd_lt_nadd_iff_right] at this

theorem nmul_le_iff : a ⨳ b ≤ c ↔ ∀ a' < a, ∀ b' < b, a' ⨳ b ♯ a ⨳ b' < c ♯ a' ⨳ b' := by
  rw [← not_iff_not]; simp [lt_nmul_iff]

theorem nmul_comm (a b) : a ⨳ b = b ⨳ a := by
  rw [nmul, nmul]
  congr; ext x; constructor <;> intro H c hc d hd
  -- Porting note: had to add additional arguments to `nmul_comm` here
  -- for the termination checker.
  · rw [nadd_comm, ← nmul_comm d b, ← nmul_comm a c, ← nmul_comm d]
    exact H _ hd _ hc
  · rw [nadd_comm, nmul_comm a d, nmul_comm c, nmul_comm c]
    exact H _ hd _ hc
termination_by (a, b)

@[simp]
theorem nmul_zero (a) : a ⨳ 0 = 0 := by
  rw [← Ordinal.le_zero, nmul_le_iff]
  exact fun _ _ a ha => (Ordinal.not_lt_zero a ha).elim

@[simp]
theorem zero_nmul (a) : 0 ⨳ a = 0 := by rw [nmul_comm, nmul_zero]

@[simp]
theorem nmul_one (a : Ordinal) : a ⨳ 1 = a := by
  rw [nmul]
  simp only [lt_one_iff_zero, forall_eq, nmul_zero, nadd_zero]
  convert csInf_Ici (α := Ordinal)
  ext b
  -- Porting note: added this `simp` line, as the result from `convert`
  -- is slightly different.
  simp only [Set.mem_setOf_eq, Set.mem_Ici]
  refine ⟨fun H => le_of_forall_lt fun c hc => ?_, fun ha c hc => ?_⟩
  -- Porting note: had to add arguments to `nmul_one` in the next two lines
  -- for the termination checker.
  · simpa only [nmul_one c] using H c hc
  · simpa only [nmul_one c] using hc.trans_le ha
termination_by a

@[simp]
theorem one_nmul (a) : 1 ⨳ a = a := by rw [nmul_comm, nmul_one]

theorem nmul_lt_nmul_of_pos_left (h₁ : a < b) (h₂ : 0 < c) : c ⨳ a < c ⨳ b :=
  lt_nmul_iff.2 ⟨0, h₂, a, h₁, by simp⟩

theorem nmul_lt_nmul_of_pos_right (h₁ : a < b) (h₂ : 0 < c) : a ⨳ c < b ⨳ c :=
  lt_nmul_iff.2 ⟨a, h₁, 0, h₂, by simp⟩

theorem nmul_le_nmul_left (h : a ≤ b) (c) : c ⨳ a ≤ c ⨳ b := by
  rcases lt_or_eq_of_le h with (h₁ | rfl) <;> rcases (eq_zero_or_pos c).symm with (h₂ | rfl)
  · exact (nmul_lt_nmul_of_pos_left h₁ h₂).le
  all_goals simp

theorem nmul_le_nmul_right (h : a ≤ b) (c) : a ⨳ c ≤ b ⨳ c := by
  rw [nmul_comm, nmul_comm b]
  exact nmul_le_nmul_left h c

theorem le_nmul_self_of_pos (a) {b} (h : 0 < b) : a ≤ b ⨳ a := by
  rw [← Ordinal.one_le_iff_pos] at h
  simpa using nmul_le_nmul_right h a

theorem le_self_nmul_of_pos (a) {b} (h : 0 < b) : a ≤ a ⨳ b := by
  rw [nmul_comm]
  exact le_nmul_self_of_pos a h

theorem nmul_ne_zero_iff {a b} : a ⨳ b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  constructor
  · rw [← not_or]
    rintro h (rfl | rfl)
    · rw [zero_nmul] at h
      contradiction
    · rw [nmul_zero] at h
      contradiction
  · iterate 3 rw [← Ordinal.pos_iff_ne_zero]
    rintro ⟨ha, hb⟩
    have := nmul_lt_nmul_of_pos_left hb ha
    rwa [nmul_zero] at this

theorem nmul_ne_zero {a b} (ha : a ≠ 0) (hb : b ≠ 0) : a ⨳ b ≠ 0 :=
  nmul_ne_zero_iff.2 ⟨ha, hb⟩

theorem nmul_eq_zero_iff {a b} : a ⨳ b = 0 ↔ a = 0 ∨ b = 0 := by
  rw [← not_iff_not]
  simpa using nmul_ne_zero_iff

theorem nmul_nadd (a b c : Ordinal) : a ⨳ (b ♯ c) = a ⨳ b ♯ a ⨳ c := by
  refine le_antisymm (nmul_le_iff.2 fun a' ha d hd => ?_)
    (nadd_le_iff.2 ⟨fun d hd => ?_, fun d hd => ?_⟩)
  · -- Porting note: adding arguments to `nmul_nadd` for the termination checker.
    rw [nmul_nadd a' b c]
    rcases lt_nadd_iff.1 hd with (⟨b', hb, hd⟩ | ⟨c', hc, hd⟩)
    · have := nadd_lt_nadd_of_lt_of_le (nmul_nadd_lt ha hb) (nmul_nadd_le ha.le hd)
      -- Porting note: adding arguments to `nmul_nadd` for the termination checker.
      rw [nmul_nadd a' b' c, nmul_nadd a b' c] at this
      simp only [nadd_assoc] at this
      rwa [nadd_left_comm, nadd_left_comm _ (a ⨳ b'), nadd_left_comm (a ⨳ b),
        nadd_lt_nadd_iff_left, nadd_left_comm (a' ⨳ b), nadd_left_comm (a ⨳ b),
        nadd_lt_nadd_iff_left, ← nadd_assoc, ← nadd_assoc] at this
    · have := nadd_lt_nadd_of_le_of_lt (nmul_nadd_le ha.le hd) (nmul_nadd_lt ha hc)
      -- Porting note: adding arguments to `nmul_nadd` for the termination checker.
      rw [nmul_nadd a' b c', nmul_nadd a b c'] at this
      simp only [nadd_assoc] at this
      rwa [nadd_left_comm, nadd_comm (a ⨳ c), nadd_left_comm (a' ⨳ d), nadd_left_comm (a ⨳ c'),
        nadd_left_comm (a ⨳ b), nadd_lt_nadd_iff_left, nadd_comm (a' ⨳ c), nadd_left_comm (a ⨳ d),
        nadd_left_comm (a' ⨳ b), nadd_left_comm (a ⨳ b), nadd_lt_nadd_iff_left, nadd_comm (a ⨳ d),
        nadd_comm (a' ⨳ d), ← nadd_assoc, ← nadd_assoc] at this
  · rcases lt_nmul_iff.1 hd with ⟨a', ha, b', hb, hd⟩
    have := nadd_lt_nadd_of_le_of_lt hd (nmul_nadd_lt ha (nadd_lt_nadd_right hb c))
    -- Porting note: adding arguments to `nmul_nadd` for the termination checker.
    rw [nmul_nadd a' b c, nmul_nadd a b' c, nmul_nadd a'] at this
    simp only [nadd_assoc] at this
    rwa [nadd_left_comm (a' ⨳ b'), nadd_left_comm, nadd_lt_nadd_iff_left, nadd_left_comm,
      nadd_left_comm _ (a' ⨳ b'), nadd_left_comm (a ⨳ b'), nadd_lt_nadd_iff_left,
      nadd_left_comm (a' ⨳ c), nadd_left_comm, nadd_lt_nadd_iff_left, nadd_left_comm,
      nadd_comm _ (a' ⨳ c), nadd_lt_nadd_iff_left] at this
  · rcases lt_nmul_iff.1 hd with ⟨a', ha, c', hc, hd⟩
    have := nadd_lt_nadd_of_lt_of_le (nmul_nadd_lt ha (nadd_lt_nadd_left hc b)) hd
    -- Porting note: adding arguments to `nmul_nadd` for the termination checker.
    rw [nmul_nadd a' b c, nmul_nadd a b c', nmul_nadd a'] at this
    simp only [nadd_assoc] at this
    rwa [nadd_left_comm _ (a' ⨳ b), nadd_lt_nadd_iff_left, nadd_left_comm (a' ⨳ c'),
      nadd_left_comm _ (a' ⨳ c), nadd_lt_nadd_iff_left, nadd_left_comm, nadd_comm (a' ⨳ c'),
      nadd_left_comm _ (a ⨳ c'), nadd_lt_nadd_iff_left, nadd_comm _ (a' ⨳ c'),
      nadd_comm _ (a' ⨳ c'), nadd_left_comm, nadd_lt_nadd_iff_left] at this
termination_by (a, b, c)

theorem nadd_nmul (a b c) : (a ♯ b) ⨳ c = a ⨳ c ♯ b ⨳ c := by
  rw [nmul_comm, nmul_nadd, nmul_comm, nmul_comm c]

theorem nmul_nadd_lt₃ {a' b' c' : Ordinal} (ha : a' < a) (hb : b' < b) (hc : c' < c) :
    a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' <
      a ⨳ b ⨳ c ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' := by
  simpa only [nadd_nmul, ← nadd_assoc] using nmul_nadd_lt (nmul_nadd_lt ha hb) hc

theorem nmul_nadd_le₃ {a' b' c' : Ordinal} (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
    a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' ≤
      a ⨳ b ⨳ c ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' := by
  simpa only [nadd_nmul, ← nadd_assoc] using nmul_nadd_le (nmul_nadd_le ha hb) hc

theorem nmul_nadd_lt₃' {a' b' c' : Ordinal} (ha : a' < a) (hb : b' < b) (hc : c' < c) :
    a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') <
      a ⨳ (b ⨳ c) ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') := by
  simp only [nmul_comm _ (_ ⨳ _)]
  convert nmul_nadd_lt₃ hb hc ha using 1 <;>
    · simp only [nadd_eq_add, NatOrdinal.toOrdinal_toNatOrdinal]; abel_nf

theorem nmul_nadd_le₃' {a' b' c' : Ordinal} (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
    a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') ≤
      a ⨳ (b ⨳ c) ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') := by
  simp only [nmul_comm _ (_ ⨳ _)]
  convert nmul_nadd_le₃ hb hc ha using 1 <;>
    · simp only [nadd_eq_add, NatOrdinal.toOrdinal_toNatOrdinal]; abel_nf

theorem lt_nmul_iff₃ :
    d < a ⨳ b ⨳ c ↔
      ∃ a' < a, ∃ b' < b, ∃ c' < c,
        d ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' ≤
          a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' := by
  refine ⟨fun h => ?_, ?_⟩
  · rcases lt_nmul_iff.1 h with ⟨e, he, c', hc, H₁⟩
    rcases lt_nmul_iff.1 he with ⟨a', ha, b', hb, H₂⟩
    refine ⟨a', ha, b', hb, c', hc, ?_⟩
    have := nadd_le_nadd H₁ (nmul_nadd_le H₂ hc.le)
    simp only [nadd_nmul, nadd_assoc] at this
    rw [nadd_left_comm, nadd_left_comm d, nadd_left_comm, nadd_le_nadd_iff_left,
      nadd_left_comm (a ⨳ b' ⨳ c), nadd_left_comm (a' ⨳ b ⨳ c), nadd_left_comm (a ⨳ b ⨳ c'),
      nadd_le_nadd_iff_left, nadd_left_comm (a ⨳ b ⨳ c'), nadd_left_comm (a ⨳ b ⨳ c')] at this
    simpa only [nadd_assoc]
  · rintro ⟨a', ha, b', hb, c', hc, h⟩
    have := h.trans_lt (nmul_nadd_lt₃ ha hb hc)
    repeat' rw [nadd_lt_nadd_iff_right] at this
    assumption

theorem nmul_le_iff₃ :
    a ⨳ b ⨳ c ≤ d ↔
      ∀ a' < a, ∀ b' < b, ∀ c' < c,
        a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' <
          d ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' := by
  rw [← not_iff_not]; simp [lt_nmul_iff₃]

theorem lt_nmul_iff₃' :
    d < a ⨳ (b ⨳ c) ↔
      ∃ a' < a, ∃ b' < b, ∃ c' < c,
        d ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') ≤
          a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') := by
  simp only [nmul_comm _ (_ ⨳ _), lt_nmul_iff₃, nadd_eq_add, NatOrdinal.toOrdinal_toNatOrdinal]
  constructor <;> rintro ⟨b', hb, c', hc, a', ha, h⟩
  · use a', ha, b', hb, c', hc; convert h using 1 <;> abel_nf
  · use c', hc, a', ha, b', hb; convert h using 1 <;> abel_nf

theorem nmul_le_iff₃' :
    a ⨳ (b ⨳ c) ≤ d ↔
      ∀ a' < a, ∀ b' < b, ∀ c' < c,
        a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') <
          d ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') := by
  rw [← not_iff_not]; simp [lt_nmul_iff₃']

theorem nmul_assoc (a b c : Ordinal) : a ⨳ b ⨳ c = a ⨳ (b ⨳ c) := by
  apply le_antisymm
  · rw [nmul_le_iff₃]
    intro a' ha b' hb c' hc
    -- Porting note: the next line was just
    -- repeat' rw [nmul_assoc]
    -- but we need to spell out the arguments for the termination checker.
    rw [nmul_assoc a' b c, nmul_assoc a b' c, nmul_assoc a b c', nmul_assoc a' b' c',
      nmul_assoc a' b' c, nmul_assoc a' b c', nmul_assoc a b' c']
    exact nmul_nadd_lt₃' ha hb hc
  · rw [nmul_le_iff₃']
    intro a' ha b' hb c' hc
    -- Porting note: the next line was just
    -- repeat' rw [← nmul_assoc]
    -- but we need to spell out the arguments for the termination checker.
    rw [← nmul_assoc a' b c, ← nmul_assoc a b' c, ← nmul_assoc a b c', ← nmul_assoc a' b' c',
      ← nmul_assoc a' b' c, ← nmul_assoc a' b c', ← nmul_assoc a b' c']
    exact nmul_nadd_lt₃ ha hb hc
termination_by (a, b, c)

end Ordinal

open Ordinal

instance : Mul NatOrdinal :=
  ⟨nmul⟩

-- Porting note: had to add universe annotations to ensure that the
-- two sources lived in the same universe.
instance : OrderedCommSemiring NatOrdinal.{u} :=
  { NatOrdinal.orderedCancelAddCommMonoid.{u},
    NatOrdinal.linearOrder.{u} with
    mul := (· * ·)
    left_distrib := nmul_nadd
    right_distrib := nadd_nmul
    zero_mul := zero_nmul
    mul_zero := nmul_zero
    mul_assoc := nmul_assoc
    one := 1
    one_mul := one_nmul
    mul_one := nmul_one
    mul_comm := nmul_comm
    zero_le_one := @zero_le_one Ordinal _ _ _ _
    mul_le_mul_of_nonneg_left := fun a b c h _ => nmul_le_nmul_left h c
    mul_le_mul_of_nonneg_right := fun a b c h _ => nmul_le_nmul_right h c }

instance : NoZeroDivisors NatOrdinal.{u} where
  eq_zero_or_eq_zero_of_mul_eq_zero := nmul_eq_zero_iff.1

namespace Ordinal

theorem nmul_eq_mul (a b) : a ⨳ b = toOrdinal (toNatOrdinal a * toNatOrdinal b) :=
  rfl

theorem nmul_nadd_one : ∀ a b, a ⨳ (b ♯ 1) = a ⨳ b ♯ a :=
  @mul_add_one NatOrdinal _ _ _

theorem nadd_one_nmul : ∀ a b, (a ♯ 1) ⨳ b = a ⨳ b ♯ b :=
  @add_one_mul NatOrdinal _ _ _

theorem nmul_succ (a b) : a ⨳ succ b = a ⨳ b ♯ a := by rw [← nadd_one, nmul_nadd_one]

theorem succ_nmul (a b) : succ a ⨳ b = a ⨳ b ♯ b := by rw [← nadd_one, nadd_one_nmul]

theorem nmul_add_one : ∀ a b, a ⨳ (b + 1) = a ⨳ b ♯ a :=
  nmul_succ

theorem add_one_nmul : ∀ a b, (a + 1) ⨳ b = a ⨳ b ♯ b :=
  succ_nmul

theorem mul_le_nmul (a b : Ordinal.{u}) : a * b ≤ a ⨳ b := by
  refine b.limitRecOn ?_ ?_ ?_
  · simp
  · intro c h
    rw [mul_succ, nmul_succ]
    exact (add_le_nadd _ a).trans (nadd_le_nadd_right h a)
  · intro c hc H
    rcases eq_zero_or_pos a with (rfl | ha)
    · simp
    · rw [← IsNormal.blsub_eq.{u, u} (mul_isNormal ha) hc, blsub_le_iff]
      exact fun i hi => (H i hi).trans_lt (nmul_lt_nmul_of_pos_left hi ha)

/-! ### Powers of omega -/

/-! The hard part of this proof is showing that `ω ^ c * n ♯ b < ω ^ a + b` for `c < a` and `n ∈ ℕ`.
To do this, we write `b = ω ^ d + x`. If `c < d`, we write `ω ^ c * n ♯ b = ω ^ d ♯ (ω ^ c * n ♯ x)`
and apply the inductive hypothesis. Otherwise, we write `ω ^ c * n ♯ b = ω ^ c ♯ ⋯ ♯ ω ^ c ♯ b` and
repeatedly apply the inductive hypothesis. -/

theorem omega_opow_nadd_of_lt {a b : Ordinal} (h : b < ω ^ succ a) : ω ^ a ♯ b = ω ^ a + b := by
  obtain rfl | hb := eq_or_ne b 0; simp
  obtain rfl | ha := eq_or_ne a 0
  · rw [succ_zero, opow_one] at h
    obtain ⟨n, rfl⟩ := lt_omega.1 h
    simp
  · apply (add_le_nadd _ _).antisymm'
    rw [nadd_le_iff]
    constructor <;> intro d hd
    · obtain ⟨c, hc, n, hn⟩ := lt_omega_opow hd ha
      apply (nadd_lt_nadd_right hn b).trans
      clear hd hn d
      have H₁ : log ω b ≤ a := by rwa [lt_opow_iff_log_lt one_lt_omega hb, lt_succ_iff] at h
      have H₂ := sub_opow_log_omega_lt hb
      have H : ∀ m : ℕ, ω ^ c * m = ω ^ c ⨳ m := by
        intro m
        induction' m with m IH
        · rw [Nat.cast_zero, mul_zero, nmul_zero]
        · conv_rhs => rw [Nat.cast_succ, nmul_add_one]
          rw [add_comm, Nat.cast_add, Nat.cast_one, mul_one_add, ← omega_opow_nadd_of_lt, nadd_comm,
            IH]
          apply (mul_lt_mul_of_pos_left (nat_lt_omega m) (opow_pos c omega_pos)).trans_le
          rw [opow_succ]
      cases lt_or_le b (ω ^ succ c)
      · suffices ω ^ c * n ♯ b < ω ^ succ c by
          apply this.trans_le <| (opow_le_opow_right omega_pos _).trans (le_add_right _ b)
          rwa [succ_le_iff]
        induction' n with n IH
        · rwa [Nat.cast_zero, mul_zero, zero_nadd]
        · rw [H, Nat.cast_succ, nmul_add_one, nadd_comm _ (ω ^ c), nadd_assoc, ← H,
            omega_opow_nadd_of_lt IH]
          apply principal_add_omega_opow _ _ IH
          rw [opow_lt_opow_iff_right one_lt_omega]
          exact lt_succ c
      · have H₃ := omega_opow_nadd_of_lt <| H₂.trans (lt_opow_succ_log_self one_lt_omega b)
        have H₄ : ω ^ c * ↑n ♯ (b - ω ^ log ω b) < b := by
          have : ω ^ c * ↑n < ω ^ log ω b := by
            apply (omega_opow_mul_nat_lt c n).trans_le
            rwa [opow_le_opow_iff_right one_lt_omega, ← opow_le_iff_le_log one_lt_omega hb]
          apply (nadd_lt_nadd_right this _).trans_le
          rw [H₃, Ordinal.add_sub_cancel_of_le]
          exact opow_log_le_self ω hb
        conv_lhs => rw [← Ordinal.add_sub_cancel_of_le (opow_log_le_self ω hb)]
        rw [← H₃, ← nadd_assoc, nadd_comm (ω ^ c * n), nadd_assoc,
          omega_opow_nadd_of_lt (H₄.trans <| lt_opow_succ_log_self one_lt_omega b)]
        exact add_lt_add_of_le_of_lt (opow_le_opow_right omega_pos H₁) H₄
    · rw [omega_opow_nadd_of_lt (hd.trans h)]
      exact add_lt_add_left hd _
termination_by (a, b)
decreasing_by
· exact Prod.Lex.left _ _ hc
· exact Prod.Lex.left _ _ hc
· exact Prod.Lex.toLex_strictMono <| Prod.mk_lt_mk_of_le_of_lt H₁ H₂
· exact Prod.Lex.toLex_strictMono <| Prod.mk_lt_mk_of_le_of_lt H₁ H₄
· exact Prod.Lex.right _ hd

theorem nadd_omega_opow_of_lt {a b : Ordinal} (h : a < ω ^ succ b) : a ♯ ω ^ b = ω ^ b + a := by
  rw [nadd_comm, omega_opow_nadd_of_lt h]

theorem omega_opow_nadd_self (a : Ordinal) : ω ^ a ♯ ω ^ a = ω ^ a + ω ^ a := by
  rw [omega_opow_nadd_of_lt]
  rw [opow_lt_opow_iff_right one_lt_omega, lt_succ_iff]

@[simp]
theorem omega_opow_nmul_nat (a : Ordinal) (n : ℕ) : ω ^ a ⨳ n = ω ^ a * n := by
  induction' n with n IH
  · rw [Nat.cast_zero, nmul_zero, mul_zero]
  · conv_lhs => rw [Nat.cast_succ, nmul_add_one, nadd_comm]
    rw [add_comm, Nat.cast_add, Nat.cast_one, mul_one_add, IH, omega_opow_nadd_of_lt]
    rw [opow_succ]
    exact mul_lt_mul_of_pos_left (nat_lt_omega _) (opow_pos a omega_pos)

@[simp]
theorem nat_nmul_omega_opow (a : Ordinal) (n : ℕ) : n ⨳ ω ^ a = ω ^ a * n := by
  rw [nmul_comm, omega_opow_nmul_nat]

theorem principal_nadd_omega_opow (a : Ordinal) : Principal (· ♯ ·) (ω ^ a) := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [opow_zero, principal_one_iff, zero_nadd]
  · rw [principal_mono_iff
      (fun b _ _ h => nadd_le_nadd_left h b) (fun b _ _ h => nadd_le_nadd_right h b)]
    intro b hb
    obtain ⟨x, hx, m, hm⟩ := lt_omega_opow hb ha
    apply (nadd_lt_nadd_of_le_of_lt hm.le hm).trans
    rw [← omega_opow_nmul_nat, ← nmul_nadd, nadd_nat, ← Nat.cast_add, omega_opow_nmul_nat]
    apply (omega_opow_mul_nat_lt _ _).trans_le
    rwa [opow_le_opow_iff_right one_lt_omega, succ_le_iff]

theorem omega_opow_add_nadd_assoc (a : Ordinal) {b c : Ordinal}
    (hb : b < ω ^ succ a) (hc : c < ω ^ succ a) : ω ^ a + b ♯ c = ω ^ a + (b ♯ c) := by
  rw [← omega_opow_nadd_of_lt hb, nadd_assoc,
    omega_opow_nadd_of_lt (principal_nadd_omega_opow _ hb hc)]

theorem omega_opow_mul_nadd_of_lt {a c : Ordinal} (h : c < ω ^ succ a) (b : Ordinal) :
    ω ^ a * b ♯ c = ω ^ a * b + c := by
  refine CNFRec_omega ?_ ?_ b
  · rw [mul_zero, zero_nadd, zero_add]
  · intro o ho IH
    conv_lhs => rw [← add_sub_cancel_omega_opow_log ho]
    rw [mul_add, ← opow_add, omega_opow_add_nadd_assoc, IH, opow_add, ← add_assoc, ← mul_add,
      add_sub_cancel_omega_opow_log ho]
    · rw [← add_succ, opow_add, mul_lt_mul_iff_left (opow_pos a omega_pos)]
      exact (sub_le_self o _).trans_lt <| lt_opow_succ_log_self one_lt_omega _
    · apply h.trans_le
      rw [opow_le_opow_iff_right one_lt_omega, succ_le_succ_iff]
      exact le_add_right a _

theorem nadd_omega_opow_mul {a b : Ordinal} (h : b < ω ^ succ a) (c : Ordinal) :
    b ♯ ω ^ a * c = ω ^ a * c + b := by
  rw [nadd_comm, omega_opow_mul_nadd_of_lt h]

theorem omega_opow_mul_add_nadd_assoc (a b : Ordinal) {c d : Ordinal}
    (hc : c < ω ^ succ a) (hd : d < ω ^ succ a) : ω ^ a * b + c ♯ d = ω ^ a * b + (c ♯ d) := by
  rw [← omega_opow_mul_nadd_of_lt hc, nadd_assoc,
    omega_opow_mul_nadd_of_lt (principal_nadd_omega_opow _ hc hd)]

theorem omega_opow_nadd {a b : Ordinal} : ω ^ (a ♯ b) = ω ^ a ⨳ ω ^ b := by
  obtain rfl | ha := eq_or_ne a 0; simp
  obtain rfl | hb := eq_or_ne b 0; simp
  apply le_antisymm
  · apply le_of_forall_lt
    intro c hc
    obtain ⟨d, hd, n, hn⟩ := lt_omega_opow hc (nadd_ne_zero_of_left ha _)
    apply hn.trans
    obtain ⟨e, he, he'⟩ | ⟨e, he, he'⟩ := lt_nadd_iff.1 hd <;>
    apply (mul_le_mul_right' (opow_le_opow_right omega_pos he') _).trans_lt
    · rw [← omega_opow_nmul_nat, omega_opow_nadd, nmul_comm, ← nmul_assoc, nat_nmul_omega_opow]
      apply nmul_lt_nmul_of_pos_right ((omega_opow_mul_nat_lt _ _).trans_le _)
        (opow_pos b omega_pos)
      rwa [opow_le_opow_iff_right one_lt_omega, succ_le_iff]
    · rw [← omega_opow_nmul_nat, omega_opow_nadd, nmul_assoc, omega_opow_nmul_nat]
      apply nmul_lt_nmul_of_pos_left ((omega_opow_mul_nat_lt _ _).trans_le _)
        (opow_pos a omega_pos)
      rwa [opow_le_opow_iff_right one_lt_omega, succ_le_iff]
  · rw [nmul_le_iff]
    intro c hc d hd
    obtain ⟨e, he, m, hm⟩ := lt_omega_opow hc ha
    obtain ⟨f, hf, n, hn⟩ := lt_omega_opow hd hb
    apply (principal_nadd_omega_opow _ _ _).trans_le (le_self_nadd _ _)
    · apply (nmul_lt_nmul_of_pos_right hm (opow_pos b omega_pos)).trans
      rw [← omega_opow_nmul_nat, nmul_assoc, nmul_comm m, ← nmul_assoc, ← omega_opow_nadd,
        omega_opow_nmul_nat]
      apply (omega_opow_mul_nat_lt _ _).trans_le
      rwa [opow_le_opow_iff_right one_lt_omega, succ_le_iff, nadd_lt_nadd_iff_right]
    · apply (nmul_lt_nmul_of_pos_left hn (opow_pos a omega_pos)).trans
      rw [← omega_opow_nmul_nat, ← nmul_assoc, ← omega_opow_nadd, omega_opow_nmul_nat]
      apply (omega_opow_mul_nat_lt _ _).trans_le
      rwa [opow_le_opow_iff_right one_lt_omega, succ_le_iff, nadd_lt_nadd_iff_left]
termination_by (a, b)

theorem omega_opow_nmul {a b : Ordinal} : b < ω ^ ω ^ succ a → ω ^ ω ^ a ⨳ b = ω ^ ω ^ a * b := by
  refine CNFRec_omega ?_ ?_ b
  · simp
  · intro o ho IH ho'
    have H₁ : log ω o < ω ^ succ a := by
      rwa [← lt_opow_iff_log_lt one_lt_omega ho]
    have H₂ := (sub_le_self o (ω ^ log ω o)).trans_lt (lt_opow_succ_log_self one_lt_omega o)
    have H₃ : o - ω ^ log ω o < ω ^ ω ^ succ a := by
      apply H₂.trans_le
      rwa [opow_le_opow_iff_right one_lt_omega, succ_le_iff]
    have H₄ : ω ^ ω ^ a * (o - ω ^ log ω o) < ω ^ succ (ω ^ a + log ω o) := by
      rwa [← add_succ, opow_add, mul_lt_mul_iff_left (opow_pos _ omega_pos)]
    conv_lhs => rw [← add_sub_cancel_omega_opow_log ho]
    rw [← omega_opow_nadd_of_lt H₂, nmul_nadd, IH H₃, ← omega_opow_nadd, omega_opow_nadd_of_lt H₁,
      omega_opow_nadd_of_lt H₄, opow_add, ← mul_add, add_sub_cancel_omega_opow_log ho]

/-! ### Cantor normal forms -/


open Classical in
/-- We create an alias for `CNF_coeff ω` in order to properly state our results. -/
@[pp_nodot]
def CNF_coeff_omega (o : Ordinal) : AddMonoidAlgebra ℕ NatOrdinal where
  toFun e := Classical.choose <| lt_omega.1 <| CNF_coeff_lt one_lt_omega o (NatOrdinal.toOrdinal e)
  support := (CNF_coeff ω o).support.map toNatOrdinal
  mem_support_toFun e := by
    generalize_proofs h
    dsimp
    rw [← @Nat.cast_inj Ordinal, ← Classical.choose_spec (h e)]
    simp
    rfl

theorem CNF_coeff_omega_apply' (o : Ordinal) (e : NatOrdinal) :
    toOrdinal (CNF_coeff_omega o e) = CNF_coeff ω o (toOrdinal e) := by
  rw [CNF_coeff_omega]
  generalize_proofs h
  simpa using (Classical.choose_spec (h e)).symm

@[simp]
theorem CNF_coeff_omega_apply (o : Ordinal) (e : NatOrdinal) :
    CNF_coeff_omega o e = toNatOrdinal (CNF_coeff ω o (toOrdinal e)) := by
  rw [← toOrdinal.apply_eq_iff_eq, CNF_coeff_omega_apply']
  rfl

@[simp]
theorem CNF_coeff_omega_zero : CNF_coeff_omega 0 = 0 := by
  apply Finsupp.ext
  intro a
  apply @Nat.cast_injective NatOrdinal
  rw [CNF_coeff_omega_apply, CNF_coeff_zero]
  rfl

@[simp]
theorem CNF_coeff_omega_add_apply (o₁ o₂ : Ordinal) (e : NatOrdinal) :
    (CNF_coeff_omega o₁ + CNF_coeff_omega o₂) e =
    toNatOrdinal (CNF_coeff ω o₁ (toOrdinal e) ♯ CNF_coeff ω o₂ (toOrdinal e)) := by
  change CNF_coeff_omega o₁ e + CNF_coeff_omega o₂ e = _
  rw [CNF_coeff_omega_apply, CNF_coeff_omega_apply]
  rfl

  #exit

theorem CNF_coeff_omega_opow_add_of_principal_add {x o : Ordinal} (ho₂ : o < ω ^ Order.succ x) :
    CNF_coeff_omega (ω ^ x + o) = CNF_coeff_omega (ω ^ x) + CNF_coeff_omega o := by
  apply Finsupp.ext
  intro e
  apply @Nat.cast_injective NatOrdinal
  simp
  iterate 3 rw [CNF_coeff_omega_apply]
  apply CNF_coeff_opow_add_of_principal_add

private theorem CNF_coeff_omega_comm (o₁ o₂ : Ordinal) :
    CNF_coeff ω o₁ + CNF_coeff ω o₂ = CNF_coeff ω o₂ + CNF_coeff ω o₁ := by
  ext e
  obtain ⟨m, hm⟩ := lt_omega.1 (CNF_coeff_lt one_lt_omega o₁ e)
  obtain ⟨n, hn⟩ := lt_omega.1 (CNF_coeff_lt one_lt_omega o₂ e)
  dsimp
  rw [hm, hn, ← Nat.cast_add, ← Nat.cast_add, add_comm]-/

theorem CNF_coeff_nadd (o₁ o₂ : NatOrdinal) :
    CNF_coeff ω (o₁ ♯ o₂) = CNF_coeff ω o₁ + CNF_coeff ω o₂ := by
  obtain rfl | ho₁ := eq_or_ne o₁ 0; simp
  obtain rfl | ho₂ := eq_or_ne o₂ 0; simp
  obtain ho | ho := le_or_lt o₂ o₁
  -- Both halves of the proof are completely analogous.
  · have H₀ := lt_opow_succ_log_self one_lt_omega o₁
    have H₁ := ho.trans_lt H₀
    have H₂ := (sub_le_self _ (ω ^ log ω o₁)).trans_lt H₀
    have := Ordinal.sub_opow_log_omega_lt ho₁
    conv_lhs => rw [← add_sub_cancel_omega_opow_log ho₁]
    rw [omega_opow_add_nadd_assoc _ H₂ H₁, CNF_coeff_opow_add_of_principal_add principal_add_omega
      (principal_nadd_omega_opow _ H₂ H₁), CNF_coeff_nadd, ← add_assoc]
    conv_rhs => rw [← add_sub_cancel_omega_opow_log ho₁]
    rw [CNF_coeff_opow_add_of_principal_add principal_add_omega H₂]
  · rw [nadd_comm, CNF_coeff_omega_comm]
    have H₀ := lt_opow_succ_log_self one_lt_omega o₂
    have H₁ := ho.le.trans_lt H₀
    have H₂ := (sub_le_self _ (ω ^ log ω o₂)).trans_lt H₀
    have := Ordinal.sub_opow_log_omega_lt ho₂
    conv_lhs => rw [← add_sub_cancel_omega_opow_log ho₂]
    rw [omega_opow_add_nadd_assoc _ H₂ H₁, CNF_coeff_opow_add_of_principal_add principal_add_omega
      (principal_nadd_omega_opow _ H₂ H₁)]
    dsimp
    rw [nadd_comm, CNF_coeff_nadd, CNF_coeff_omega_comm o₁, ← add_assoc]
    conv_rhs => rw [← add_sub_cancel_omega_opow_log ho₂]
    rw [CNF_coeff_opow_add_of_principal_add principal_add_omega H₂]
termination_by (o₁, o₂)

theorem CNF_coeff_nadd_apply (o₁ o₂ e : Ordinal) :
    CNF_coeff ω (o₁ ♯ o₂) e = CNF_coeff ω o₁ e + CNF_coeff ω o₂ e := by
  rw [CNF_coeff_nadd]
  rfl

/-- The product of Cantor normal forms as polynomials.

We use the axiom of choice to  -/
def CNF_mul (f g : Ordinal →₀ Ordinal) : Ordinal →₀ Ordinal :=
  (f.support.toList.map (fun e₁ =>
    (g.support.toList.map (fun e₂ => Finsupp.single (e₁ ♯ e₂) (f e₁ * f e₂))).sum)).sum

#exit

/-- The base `ω` Cantor normal form of `o₁ ⨳ o₂` is obtained by directly adding up the coefficients
of those for `o₁` and `o₂`.

This corresponds to the product on `AddMonoidAlgebra ℕ NatOrdinal`. However, it's very hard to state
the result in this way, as `CNF_coeff ω o` is nominally of type `Ordinal →₀ Ordinal`. We instead
implement this operation from scratch as `CNF_mul` and prove the result in terms of it. -/
theorem CNF_coeff_nmul (o₁ o₂ : Ordinal) : CNF_coeff ω (o₁ ⨳ o₂) =
    (@AddMonoidAlgebra.hasMul NatOrdinal Ordinal).mul (CNF_coeff ω o₁) (CNF_coeff ω o₂) := by
  obtain rfl | ho₁ := eq_or_ne o₁ 0
  · simp
    exact (zero_mul (M₀ := AddMonoidAlgebra NatOrdinal Ordinal) _).symm

end Ordinal
