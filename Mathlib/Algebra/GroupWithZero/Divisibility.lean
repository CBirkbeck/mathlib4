/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Divisibility.Units

#align_import algebra.group_with_zero.divisibility from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# Divisibility in groups with zero.

Lemmas about divisibility in groups and monoids with zero.

We also define `Ring.divide`, a globally defined function on any ring
(in fact any `MonoidWithZero`), which returns division whenever divisible and zero otherwise.
-/


variable {α : Type*}

section SemigroupWithZero

variable [SemigroupWithZero α] {a : α}

theorem eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0 :=
  Dvd.elim h fun c H' => H'.trans (zero_mul c)
#align eq_zero_of_zero_dvd eq_zero_of_zero_dvd

/-- Given an element `a` of a commutative semigroup with zero, there exists another element whose
    product with zero equals `a` iff `a` equals zero. -/
@[simp]
theorem zero_dvd_iff : 0 ∣ a ↔ a = 0 :=
  ⟨eq_zero_of_zero_dvd, fun h => by
    rw [h]
    exact ⟨0, by simp⟩⟩
#align zero_dvd_iff zero_dvd_iff

@[simp]
theorem dvd_zero (a : α) : a ∣ 0 :=
  Dvd.intro 0 (by simp)
#align dvd_zero dvd_zero

end SemigroupWithZero

/-- Given two elements `b`, `c` of a `CancelMonoidWithZero` and a nonzero element `a`,
 `a*b` divides `a*c` iff `b` divides `c`. -/
theorem mul_dvd_mul_iff_left [CancelMonoidWithZero α] {a b c : α} (ha : a ≠ 0) :
    a * b ∣ a * c ↔ b ∣ c :=
  exists_congr fun d => by rw [mul_assoc, mul_right_inj' ha]
#align mul_dvd_mul_iff_left mul_dvd_mul_iff_left

/-- Given two elements `a`, `b` of a commutative `CancelMonoidWithZero` and a nonzero
  element `c`, `a*c` divides `b*c` iff `a` divides `b`. -/
theorem mul_dvd_mul_iff_right [CancelCommMonoidWithZero α] {a b c : α} (hc : c ≠ 0) :
    a * c ∣ b * c ↔ a ∣ b :=
  exists_congr fun d => by rw [mul_right_comm, mul_left_inj' hc]
#align mul_dvd_mul_iff_right mul_dvd_mul_iff_right

section CommMonoidWithZero

variable [CommMonoidWithZero α]

/-- `DvdNotUnit a b` expresses that `a` divides `b` "strictly", i.e. that `b` divided by `a`
is not a unit. -/
def DvdNotUnit (a b : α) : Prop :=
  a ≠ 0 ∧ ∃ x, ¬IsUnit x ∧ b = a * x
#align dvd_not_unit DvdNotUnit

theorem dvdNotUnit_of_dvd_of_not_dvd {a b : α} (hd : a ∣ b) (hnd : ¬b ∣ a) : DvdNotUnit a b := by
  constructor
  · rintro rfl
    exact hnd (dvd_zero _)
  · rcases hd with ⟨c, rfl⟩
    refine' ⟨c, _, rfl⟩
    rintro ⟨u, rfl⟩
    simp at hnd
#align dvd_not_unit_of_dvd_of_not_dvd dvdNotUnit_of_dvd_of_not_dvd

end CommMonoidWithZero

theorem dvd_and_not_dvd_iff [CancelCommMonoidWithZero α] {x y : α} :
    x ∣ y ∧ ¬y ∣ x ↔ DvdNotUnit x y :=
  ⟨fun ⟨⟨d, hd⟩, hyx⟩ =>
    ⟨fun hx0 => by simp [hx0] at hyx,
      ⟨d, mt isUnit_iff_dvd_one.1 fun ⟨e, he⟩ => hyx ⟨e, by rw [hd, mul_assoc, ← he, mul_one]⟩,
        hd⟩⟩,
    fun ⟨hx0, d, hdu, hdx⟩ =>
    ⟨⟨d, hdx⟩, fun ⟨e, he⟩ =>
      hdu
        (isUnit_of_dvd_one
          ⟨e, mul_left_cancel₀ hx0 <| by conv =>
            lhs
            rw [he, hdx]
            simp [mul_assoc]⟩)⟩⟩
#align dvd_and_not_dvd_iff dvd_and_not_dvd_iff

section MonoidWithZero

variable [MonoidWithZero α]

theorem ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q ≠ 0) (h₂ : p ∣ q) : p ≠ 0 := by
  rcases h₂ with ⟨u, rfl⟩
  exact left_ne_zero_of_mul h₁
#align ne_zero_of_dvd_ne_zero ne_zero_of_dvd_ne_zero

end MonoidWithZero

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α] [Subsingleton αˣ] {a b : α}

theorem dvd_antisymm : a ∣ b → b ∣ a → a = b := by
  rintro ⟨c, rfl⟩ ⟨d, hcd⟩
  rw [mul_assoc, eq_comm, mul_right_eq_self₀, mul_eq_one] at hcd
  obtain ⟨rfl, -⟩ | rfl := hcd <;> simp
#align dvd_antisymm dvd_antisymm

-- porting note: `attribute [protected]` is currently unsupported
-- attribute [protected] Nat.dvd_antisymm --This lemma is in core, so we protect it here

theorem dvd_antisymm' : a ∣ b → b ∣ a → b = a :=
  flip dvd_antisymm
#align dvd_antisymm' dvd_antisymm'

alias dvd_antisymm ← Dvd.dvd.antisymm
#align has_dvd.dvd.antisymm Dvd.dvd.antisymm

alias dvd_antisymm' ← Dvd.dvd.antisymm'
#align has_dvd.dvd.antisymm' Dvd.dvd.antisymm'

theorem eq_of_forall_dvd (h : ∀ c, a ∣ c ↔ b ∣ c) : a = b :=
  ((h _).2 dvd_rfl).antisymm <| (h _).1 dvd_rfl
#align eq_of_forall_dvd eq_of_forall_dvd

theorem eq_of_forall_dvd' (h : ∀ c, c ∣ a ↔ c ∣ b) : a = b :=
  ((h _).1 dvd_rfl).antisymm <| (h _).2 dvd_rfl
#align eq_of_forall_dvd' eq_of_forall_dvd'

end CancelCommMonoidWithZero

noncomputable def Exists.chooseP {α} {p : α → Prop} (h : ∃ i, p i) (x : α) :=
  by classical exact if p x then x else h.choose

lemma Exists.chooseP_spec {α} {p : α → Prop} (h : ∃ i, p i) (x : α) : p (h.chooseP x) :=
  by rw [chooseP]; split_ifs; assumption; exact h.choose_spec

@[simp]
lemma Exists.chooseP_true {α} {p : α → Prop} (h : ∃ i, p i) {x : α} (hx : p x) : h.chooseP x = x :=
  by simp [chooseP, hx]

@[simp]
lemma Exists.chooseP_neg {α} {p : α → Prop} (h : ∃ i, p i) {x : α} (hx : ¬p x) :
    h.chooseP x = h.choose :=
  by simp [chooseP, hx]

namespace Ring

open Classical

variable {M₀ : Type _} [MonoidWithZero M₀]

/-- Introduce a binary function `divide` on monoids with zero `M₀`, which sends `x` and `y` to
`x / y` if `y` is non-zero and divides `x`, and to `0` otherwise. This definition is somewhat
ad hoc, but one needs a fully (rather than partially) defined division function for some purposes.

Note that while this is in the `Ring` namespace for brevity, it requires the weaker assumption
`MonoidWithZero M₀` instead of `Ring M₀`. -/
noncomputable def divide (x y : M₀) : M₀ :=
  if h : y ≠ 0 ∧ y ∣ x then h.right.chooseP 0 else 0

lemma divide_dvd {x y : M₀} (hy : y ≠ 0) (hx : y ∣ x) : divide x y = hx.chooseP 0 := by
  rw [divide, dif_pos ⟨hy, hx⟩]

lemma divide_not_dvd {x y : M₀} (hx : ¬y ∣ x) : divide x y = 0 := by
  simp only [divide, dif_neg, hx, and_false]

lemma divide_zero (x : M₀) : divide x 0 = 0 := by
  simp only [divide, dif_neg, ne_eq, false_and]

lemma divide_one (x : M₀) : divide x 1 = x := by
  nontriviality
  rw [divide_dvd one_ne_zero <| one_dvd x, ]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [Exists.chooseP_true]; simp
  rw [Exists.chooseP_neg, ← one_mul <| Exists.choose _]
  · exact (one_dvd x).choose_spec.symm
  · simpa

lemma zero_divide (y : M₀) : divide 0 y = 0 := by
  by_cases hy : y = 0
  · rw [hy, divide_zero]
  · rw [divide_dvd hy <| dvd_zero y, Exists.chooseP_true]
    rw [mul_zero]

lemma one_divide {M₀ : Type _} [CommMonoidWithZero M₀] (y : M₀) : divide 1 y = inverse y := by
  nontriviality
  by_cases hy : y = 0
  · rw [hy, divide_zero, inverse_zero]
  · by_cases hy' : y ∣ 1
    · have hy'' : IsUnit y := isUnit_of_dvd_one hy'
      rw [divide_dvd hy hy', Exists.chooseP_neg,
          ← (inverse_mul_eq_iff_eq_mul y 1 _ hy'').mpr hy'.choose_spec, mul_one]
      simp
    · rw [divide_not_dvd hy', inverse_non_unit]
      exact hy' ∘ isUnit_iff_dvd_one.mp

lemma mul_divide_cancel {x y : M₀} (hy : y ≠ 0) (hx : y ∣ x) : y * divide x y = x := by
  simp only [divide_dvd hy hx, (hx.chooseP_spec _).symm]

lemma mul_divide_cancel_left [IsLeftCancelMulZero M₀] {x y : M₀} (hx : x ≠ 0) :
    divide (x * y) x = y := by
  rw [divide_dvd hx <| dvd_mul_right x y]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [Exists.chooseP_neg]
  · exact mul_left_cancel₀ hx (dvd_mul_right x y).choose_spec.symm
  · contrapose! hy
    rw [mul_left_cancel₀ hx hy]

variable {M₀ : Type _} [CommMonoidWithZero M₀]

lemma divide_mul_cancel {x y : M₀} (hy : y ≠ 0) (hx : y ∣ x) : divide x y * y = x := by
  rw [mul_comm, mul_divide_cancel hy hx]

lemma mul_divide_cancel_right [IsRightCancelMulZero M₀] {x y : M₀} (hy : y ≠ 0) :
    divide (x * y) y = x := by
  rw [divide_dvd hy <| dvd_mul_left y x]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [Exists.chooseP_neg]
  exact mul_right_cancel₀ hy <| mul_comm _ y ▸ (dvd_mul_left y x).choose_spec.symm
  contrapose! hx
  rw [mul_zero, ←zero_mul y] at hx
  rw [mul_right_cancel₀ hy hx]

end Ring

lemma IsUnit.divide_eq_mul_inverse {M₀ : Type _} [Nontrivial M₀] [CommMonoidWithZero M₀]
  {x y : M₀} (hy : IsUnit y) : Ring.divide x y = x * Ring.inverse y := by
  rw [Ring.divide_dvd hy.ne_zero hy.dvd, ← hy.mul_right_inj, ← hy.dvd.chooseP_spec, mul_comm,
    Ring.inverse_mul_cancel_right _ _ hy]
