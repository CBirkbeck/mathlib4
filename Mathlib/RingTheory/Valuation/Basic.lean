/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Patrick Massot
-/
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.TFAE

/-!

# The basics of valuation theory.

The basic theory of valuations (non-archimedean norms) on a commutative ring,
following T. Wedhorn's unpublished notes “Adic Spaces” ([wedhorn_adic]).

The definition of a valuation we use here is Definition 1.22 of [wedhorn_adic].
A valuation on a ring `R` is a monoid homomorphism `v` to a linearly ordered
commutative monoid with zero, that in addition satisfies the following two axioms:
 * `v 0 = 0`
 * `∀ x y, v (x + y) ≤ max (v x) (v y)`

`Valuation R Γ₀`is the type of valuations `R → Γ₀`, with a coercion to the underlying
function. If `v` is a valuation from `R` to `Γ₀` then the induced group
homomorphism `Units(R) → Γ₀` is called `unit_map v`.

The equivalence "relation" `IsEquiv v₁ v₂ : Prop` defined in 1.27 of [wedhorn_adic] is not strictly
speaking a relation, because `v₁ : Valuation R Γ₁` and `v₂ : Valuation R Γ₂` might
not have the same type. This corresponds in ZFC to the set-theoretic difficulty
that the class of all valuations (as `Γ₀` varies) on a ring `R` is not a set.
The "relation" is however reflexive, symmetric and transitive in the obvious
sense. Note that we use 1.27(iii) of [wedhorn_adic] as the definition of equivalence.

## Main definitions

* `Valuation R Γ₀`, the type of valuations on `R` with values in `Γ₀`
* `Valuation.IsEquiv`, the heterogeneous equivalence relation on valuations
* `Valuation.supp`, the support of a valuation

* `AddValuation R Γ₀`, the type of additive valuations on `R` with values in a
  linearly ordered additive commutative group with a top element, `Γ₀`.

## Implementation Details

`AddValuation R Γ₀` is implemented as `Valuation R (Multiplicative Γ₀)ᵒᵈ`.

## Notation

In the `DiscreteValuation` locale:

 * `ℕₘ₀` is a shorthand for `WithZero (Multiplicative ℕ)`
 * `ℤₘ₀` is a shorthand for `WithZero (Multiplicative ℤ)`

## TODO

If ever someone extends `Valuation`, we should fully comply to the `DFunLike` by migrating the
boilerplate lemmas to `ValuationClass`.
-/

open scoped Classical
open Function Ideal

noncomputable section

variable {K F R : Type*} [DivisionRing K]

section

variable (F R) (Γ₀ : Type*) [LinearOrderedCommMonoidWithZero Γ₀] [Ring R]

--porting note (#5171): removed @[nolint has_nonempty_instance]
/-- The type of `Γ₀`-valued valuations on `R`.

When you extend this structure, make sure to extend `ValuationClass`. -/
structure Valuation extends R →*₀ Γ₀ where
  /-- The valuation of a a sum is less that the sum of the valuations -/
  map_add_le_max' : ∀ x y, toFun (x + y) ≤ max (toFun x) (toFun y)

/-- `ValuationClass F α β` states that `F` is a type of valuations.

You should also extend this typeclass when you extend `Valuation`. -/
class ValuationClass (F) (R Γ₀ : outParam Type*) [LinearOrderedCommMonoidWithZero Γ₀] [Ring R]
  [FunLike F R Γ₀]
  extends MonoidWithZeroHomClass F R Γ₀ : Prop where
  /-- The valuation of a a sum is less that the sum of the valuations -/
  map_add_le_max (f : F) (x y : R) : f (x + y) ≤ max (f x) (f y)

export ValuationClass (map_add_le_max)

instance [FunLike F R Γ₀] [ValuationClass F R Γ₀] : CoeTC F (Valuation R Γ₀) :=
  ⟨fun f =>
    { toFun := f
      map_one' := map_one f
      map_zero' := map_zero f
      map_mul' := map_mul f
      map_add_le_max' := map_add_le_max f }⟩

end

namespace Valuation

variable {Γ₀ : Type*}
variable {Γ'₀ : Type*}
variable {Γ''₀ : Type*} [LinearOrderedCommMonoidWithZero Γ''₀]

section Basic

variable [Ring R]

section Monoid

variable [LinearOrderedCommMonoidWithZero Γ₀] [LinearOrderedCommMonoidWithZero Γ'₀]

instance : FunLike (Valuation R Γ₀) R Γ₀ where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨_,_⟩, _⟩, _⟩ := f
    congr

instance : ValuationClass (Valuation R Γ₀) R Γ₀ where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_zero f := f.map_zero'
  map_add_le_max f := f.map_add_le_max'

@[simp]
theorem coe_mk (f : R →*₀ Γ₀) (h) : ⇑(Valuation.mk f h) = f := rfl

theorem toFun_eq_coe (v : Valuation R Γ₀) : v.toFun = v := rfl

@[simp] -- Porting note: requested by simpNF as toFun_eq_coe LHS simplifies
theorem toMonoidWithZeroHom_coe_eq_coe (v : Valuation R Γ₀) :
    (v.toMonoidWithZeroHom : R → Γ₀) = v := rfl

@[ext]
theorem ext {v₁ v₂ : Valuation R Γ₀} (h : ∀ r, v₁ r = v₂ r) : v₁ = v₂ :=
  DFunLike.ext _ _ h

variable (v : Valuation R Γ₀) {x y z : R}

@[simp, norm_cast]
theorem coe_coe : ⇑(v : R →*₀ Γ₀) = v := rfl

-- @[simp] Porting note (#10618): simp can prove this
theorem map_zero : v 0 = 0 :=
  v.map_zero'

-- @[simp] Porting note (#10618): simp can prove this
theorem map_one : v 1 = 1 :=
  v.map_one'

-- @[simp] Porting note (#10618): simp can prove this
theorem map_mul : ∀ x y, v (x * y) = v x * v y :=
  v.map_mul'

-- Porting note: LHS side simplified so created map_add'
theorem map_add : ∀ x y, v (x + y) ≤ max (v x) (v y) :=
  v.map_add_le_max'

@[simp]
theorem map_add' : ∀ x y, v (x + y) ≤ v x ∨ v (x + y) ≤ v y := by
  intro x y
  rw [← le_max_iff, ← ge_iff_le]
  apply map_add

theorem map_add_le {x y g} (hx : v x ≤ g) (hy : v y ≤ g) : v (x + y) ≤ g :=
  le_trans (v.map_add x y) <| max_le hx hy

theorem map_add_lt {x y g} (hx : v x < g) (hy : v y < g) : v (x + y) < g :=
  lt_of_le_of_lt (v.map_add x y) <| max_lt hx hy

theorem map_sum_le {ι : Type*} {s : Finset ι} {f : ι → R} {g : Γ₀} (hf : ∀ i ∈ s, v (f i) ≤ g) :
    v (∑ i ∈ s, f i) ≤ g := by
  refine
    Finset.induction_on s (fun _ => v.map_zero ▸ zero_le')
      (fun a s has ih hf => ?_) hf
  rw [Finset.forall_mem_insert] at hf; rw [Finset.sum_insert has]
  exact v.map_add_le hf.1 (ih hf.2)

theorem map_sum_lt {ι : Type*} {s : Finset ι} {f : ι → R} {g : Γ₀} (hg : g ≠ 0)
    (hf : ∀ i ∈ s, v (f i) < g) : v (∑ i ∈ s, f i) < g := by
  refine
    Finset.induction_on s (fun _ => v.map_zero ▸ (zero_lt_iff.2 hg))
      (fun a s has ih hf => ?_) hf
  rw [Finset.forall_mem_insert] at hf; rw [Finset.sum_insert has]
  exact v.map_add_lt hf.1 (ih hf.2)

theorem map_sum_lt' {ι : Type*} {s : Finset ι} {f : ι → R} {g : Γ₀} (hg : 0 < g)
    (hf : ∀ i ∈ s, v (f i) < g) : v (∑ i ∈ s, f i) < g :=
  v.map_sum_lt (ne_of_gt hg) hf

-- @[simp] Porting note (#10618): simp can prove this
theorem map_pow : ∀ (x) (n : ℕ), v (x ^ n) = v x ^ n :=
  v.toMonoidWithZeroHom.toMonoidHom.map_pow

-- The following definition is not an instance, because we have more than one `v` on a given `R`.
-- In addition, type class inference would not be able to infer `v`.
/-- A valuation gives a preorder on the underlying ring. -/
def toPreorder : Preorder R :=
  Preorder.lift v

/-- If `v` is a valuation on a division ring then `v(x) = 0` iff `x = 0`. -/
-- @[simp] Porting note (#10618): simp can prove this
theorem zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K} : v x = 0 ↔ x = 0 :=
  map_eq_zero v

theorem ne_zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K} : v x ≠ 0 ↔ x ≠ 0 :=
  map_ne_zero v

theorem unit_map_eq (u : Rˣ) : (Units.map (v : R →* Γ₀) u : Γ₀) = v u :=
  rfl

theorem ne_zero_of_unit [Nontrivial Γ₀] (v : Valuation K Γ₀) (x : Kˣ) : v x ≠ (0 : Γ₀) := by
  simp only [ne_eq, Valuation.zero_iff, Units.ne_zero x, not_false_iff]

theorem ne_zero_of_isUnit [Nontrivial Γ₀] (v : Valuation K Γ₀) (x : K) (hx : IsUnit x) :
    v x ≠ (0 : Γ₀) := by
  simpa [hx.choose_spec] using ne_zero_of_unit v hx.choose

/-- A ring homomorphism `S → R` induces a map `Valuation R Γ₀ → Valuation S Γ₀`. -/
def comap {S : Type*} [Ring S] (f : S →+* R) (v : Valuation R Γ₀) : Valuation S Γ₀ :=
  { v.toMonoidWithZeroHom.comp f.toMonoidWithZeroHom with
    toFun := v ∘ f
    map_add_le_max' := fun x y => by simp only [comp_apply, map_add, f.map_add] }

@[simp]
theorem comap_apply {S : Type*} [Ring S] (f : S →+* R) (v : Valuation R Γ₀) (s : S) :
    v.comap f s = v (f s) := rfl

@[simp]
theorem comap_id : v.comap (RingHom.id R) = v :=
  ext fun _r => rfl

theorem comap_comp {S₁ : Type*} {S₂ : Type*} [Ring S₁] [Ring S₂] (f : S₁ →+* S₂) (g : S₂ →+* R) :
    v.comap (g.comp f) = (v.comap g).comap f :=
  ext fun _r => rfl

/-- A `≤`-preserving group homomorphism `Γ₀ → Γ'₀` induces a map `Valuation R Γ₀ → Valuation R Γ'₀`.
-/
def map (f : Γ₀ →*₀ Γ'₀) (hf : Monotone f) (v : Valuation R Γ₀) : Valuation R Γ'₀ :=
  { MonoidWithZeroHom.comp f v.toMonoidWithZeroHom with
    toFun := f ∘ v
    map_add_le_max' := fun r s =>
      calc
        f (v (r + s)) ≤ f (max (v r) (v s)) := hf (v.map_add r s)
        _ = max (f (v r)) (f (v s)) := hf.map_max
         }

/-- Two valuations on `R` are defined to be equivalent if they induce the same preorder on `R`. -/
def IsEquiv (v₁ : Valuation R Γ₀) (v₂ : Valuation R Γ'₀) : Prop :=
  ∀ r s, v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s

end Monoid

section Group

variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) {x y z : R}

/-- The subgroup with zero generated by the image of the valuation -/
def rangeGroup : Subgroup Γ₀ˣ := Subgroup.closure (Units.val ⁻¹' Set.range v)

theorem mem_rangeGroup {x : R} {γ : Γ₀ˣ} (Hx : v x = γ) : γ ∈ v.rangeGroup :=
  Subgroup.subset_closure ⟨x, Hx⟩

variable {v} in
theorem mem_rangeGroup_iff {α : Γ₀ˣ} :
    α ∈ v.rangeGroup ↔ ∃ a b, v a ≠ 0 ∧ (v a) * α = v b := by
  constructor
  · intro h
    induction h using Subgroup.closure_induction' with
    | mem α h =>
      rcases h with ⟨a, h⟩
      use 1, a
      simp [h]
    | inv α _ hα =>
      rcases hα with ⟨a, b, hb, hα⟩
      use b, a
      simp [← hα]
      intro h
      exact hb h
    | mul α _ β _ hα hβ =>
      rcases hα with ⟨a, b, hb, hα⟩
      rcases hβ with ⟨c, d, hd, hβ⟩
      use a * c, b * d
      constructor
      · simp [hb, hd]
      · simp [← hα, ← hβ]
        simp only [← mul_assoc]; apply congr_arg₂ _ _ rfl
        simp only [mul_assoc]; apply congr_arg₂ _ rfl
        rw [mul_comm]
    | one => exact ⟨1, 1, by simp⟩
  · rintro ⟨a, b, ha, h⟩
    let y := Units.mk0 _ ha
    let x := Units.mk0 (v b) (by
      intro hb; apply ha
      simpa only [hb, mul_eq_zero, Units.ne_zero, or_false] using h)
    suffices α = x / y by
      rw [this]
      exact div_mem (mem_rangeGroup v rfl) (mem_rangeGroup v rfl)
    rw [eq_div_iff_mul_eq', mul_comm, ← Units.eq_iff, Units.val_mul]
    exact h

theorem nontrivial_rangeGroup_iff :
    Nontrivial (v.rangeGroup) ↔ ∃ r, v r ≠ 0 ∧ v r ≠ 1 := by
  rw [Subgroup.nontrivial_iff_ne_bot, not_iff_comm]
  push_neg
  constructor
  · simp only [rangeGroup, Subgroup.closure_eq_bot_iff,
      Set.subset_singleton_iff, Set.mem_preimage, Set.mem_range, forall_exists_index]
    intro H u r hr
    rw [← Units.eq_iff, ← hr, Units.val_one]
    exact H _ (hr ▸ u.ne_zero)
  · intro H r hr
    simpa only [H, Subgroup.mem_bot, ← Units.eq_iff] using
      mem_rangeGroup (x := r) (γ := Units.mk0 _ hr) v rfl

/-- `rangeGroup`  is a linear ordered comm group -/
instance : LinearOrderedCommGroup v.rangeGroup where
  one_mul := by simp
  mul_one := by simp
  inv_mul_cancel := by simp
  mul_comm := fun a b ↦ mul_comm _ _
  le_refl := _
  le_trans := fun _ _ _ h1 h2 ↦ le_trans h1 h2
  lt_iff_le_not_le := fun a b ↦ lt_iff_le_not_le
  le_antisymm := fun a b ↦ le_antisymm
  mul_le_mul_left := fun a b h c ↦ mul_le_mul_left' h _
  le_total := fun a b ↦ le_total _ _
  decidableLE := Classical.decRel (· ≤ ·)
  min := _
  max := _
  min_def := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ by
    rw [min_def]
    simp only [Subtype.mk_le_mk]
  max_def := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ by
    rw [max_def]
    simp only [Subtype.mk_le_mk]
  compare_eq_compareOfLessAndEq := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [compareOfLessAndEq, Subtype.mk_lt_mk, Subtype.mk.injEq]
    split_ifs with h1 h2
    · exact compare_lt_iff_lt.mpr h1
    · simp_rw [compare_eq_iff_eq, h2]
    · rw [compare_gt_iff_gt]
      apply lt_of_le_of_ne (le_of_not_gt h1)
      simpa only [Subtype.mk_lt_mk, ne_eq, ne_comm]

@[simp]
lemma rangeGroup_min (x y : v.rangeGroup) : ((min x y).1 : Γ₀) = min (x.1 : Γ₀) y.1 := by
  exact Monotone.map_min fun ⦃a b⦄ a ↦ a

-- example : LinearOrderedCommGroupWithZero v.rangeGroupWithZero := inferInstance

-- def withZero_inclusion : v.rangeGroupWithZero → Γ₀ := fun
--   | 0 => 0
--   | some x => x.val

-- @[simp]
-- theorem withZero_inclusion_some (x : v.rangeGroup): withZero_inclusion v (some x) = x.val := rfl

-- @[simp]
-- theorem withZero_inclusion_coe (x : v.rangeGroup): withZero_inclusion v x = x.val := rfl

-- @[simp]
-- theorem withZero_inclusion_zero : withZero_inclusion v 0 = 0 := rfl

-- theorem withZero_inclusion_ne_zero_of_some (x : v.rangeGroup) : withZero_inclusion v x ≠ 0 := by
--   apply Units.ne_zero

-- theorem withZero_inclusion_ne_zero {x : v.rangeGroupWithZero} (hx : x ≠ 0) :
--     withZero_inclusion v x ≠ 0 := by
--   rw [WithZero.ne_zero_iff_exists] at hx
--   obtain ⟨_, rfl⟩ := hx
--   apply Units.ne_zero

-- theorem withZero_inclusion_eq_zero_iff {z : v.rangeGroupWithZero} :
--     withZero_inclusion v z = 0 ↔ z = 0 := by
--   constructor
--   · by_contra h_abs
--     simp at h_abs
--     rcases h_abs with ⟨h1, h2⟩
--     simp only [WithZero.ne_zero_iff_exists] at h2
--     obtain ⟨a, rfl⟩ := h2
--     apply withZero_inclusion_ne_zero_of_some v a h1
--   · intro h
--     simp [h, withZero_inclusion_zero]

-- theorem injective_withZero_inclusion : Injective (withZero_inclusion v) := by
--   intro a b hab
--   by_cases h : a = 0
--   · rwa [h, Eq.comm, withZero_inclusion_zero, withZero_inclusion_eq_zero_iff,
--      ← h, Eq.comm] at hab
--   · have ha : withZero_inclusion v a ≠ 0 := withZero_inclusion_ne_zero v h
--     have hb : withZero_inclusion v b ≠ 0 := by
--       rwa [← hab]
--     replace hb : b ≠ 0 := by
--       intro ht
--       rw [ht, withZero_inclusion_zero] at hb
--       tauto
--     obtain ⟨y, rfl⟩ := WithZero.ne_zero_iff_exists.mp h
--     obtain ⟨z, rfl⟩ := WithZero.ne_zero_iff_exists.mp hb
--     simp [withZero_inclusion_some] at hab
--     norm_cast at hab
--     rw [hab]

section ACL
/- Here, I try to define directly the `range₀`, in the hope that it will simplify everything
On the other hand, there is no `SubmonoidWithZero` -/

namespace MonoidHomWithZero

variable {A B : Type*} [MonoidWithZero A] [CommGroupWithZero B]
  {F : Type*} [FunLike F A B] [MonoidHomClass F A B] [ZeroHomClass F A B] (f : F)

/-- The range of `f`, as a `CommGroupWithZero` -/
def range₀ : Submonoid B where
  carrier := { b | ∃ a c, f a ≠ 0 ∧  (f a * b = f c)}
  mul_mem' {b b'} hb hb' := by
    simp only [ne_eq, Set.mem_setOf_eq] at hb hb' ⊢
    obtain ⟨a, c, ha, h⟩ := hb
    obtain ⟨a', c', ha', h'⟩ := hb'
    use a * a', c * c'
    constructor
    · simp only [_root_.map_mul, mul_eq_zero, ha, ha', or_self, not_false_eq_true]
    · simp only [_root_.map_mul, ← h, ← h']
      simp only [mul_assoc]; apply congr_arg₂ _ rfl
      simp only [← mul_assoc]; apply congr_arg₂ _ _ rfl
      rw [mul_comm]
  one_mem' := by
    simp only [ne_eq, exists_and_left, Set.mem_setOf_eq, mul_one, exists_apply_eq_apply', and_true]
    use 1
    rw [_root_.map_one]
    exact one_ne_zero

variable {f} in
theorem mem_range₀_iff {b : B} : b ∈ range₀ f ↔ ∃ a c, (f a ≠ 0 ∧ f a * b = f c) := by
  simp only [range₀]; rfl

theorem mem_range₀ {a : A} : f a ∈ range₀ f := by
  rw [mem_range₀_iff]
  use 1, a
  simp only [_root_.map_one, ne_eq, one_ne_zero, not_false_eq_true, one_mul, and_self]

theorem zero_mem_range₀ : 0 ∈ range₀ f := by
  rw [mem_range₀_iff]
  use 1, 0
  constructor
  · rw [_root_.map_one]; exact one_ne_zero
  · rw [mul_zero, _root_.map_zero]

theorem inv_mem_range₀ {b : B} (hb : b ∈ range₀ f) : b⁻¹ ∈ range₀ f := by
  by_cases h : b = 0
  · simp only [h, inv_zero, zero_mem_range₀]
  simp only [mem_range₀_iff] at hb ⊢
  obtain ⟨a, c, ha, hc⟩ := hb
  use c, a
  rw [← hc]
  constructor
  · simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨ha, h⟩
  · rw [mul_assoc, mul_inv_cancel₀ h, mul_one]

theorem inv_mem_range₀_iff {b : B} : b⁻¹ ∈ range₀ f ↔ b ∈ range₀ f := by
  constructor
  · nth_rewrite 2 [← inv_inv b]
    exact inv_mem_range₀ f
  · exact inv_mem_range₀ f

instance : CommGroupWithZero (range₀ f) where
  toCommMonoid := inferInstance
  zero := ⟨0, zero_mem_range₀ f⟩
  zero_mul a := by
    rw [← Subtype.coe_inj, Submonoid.coe_mul]
    exact zero_mul _
  mul_zero a := by
    rw [← Subtype.coe_inj, Submonoid.coe_mul]
    exact mul_zero _
  inv b := ⟨b⁻¹, inv_mem_range₀ f b.prop⟩
  exists_pair_ne := by
    use 1, ⟨0, zero_mem_range₀ f⟩
    rw [ne_eq, ← Subtype.coe_inj]
    exact one_ne_zero
  inv_zero := by
    rw [← Subtype.coe_inj]
    exact inv_zero
  mul_inv_cancel b hb := by
    obtain ⟨a, c, ha, hc⟩ := mem_range₀_iff.mpr b.prop
    rw [← Subtype.coe_inj, Submonoid.coe_mul]
    apply mul_inv_cancel₀
    rwa [ne_eq, ← Subtype.coe_inj] at hb

theorem range₀_coe_zero : ((0 : range₀ f) : B) = 0 := rfl

theorem range₀_coe_one : ((1 : range₀ f) : B) = 1 := rfl

end MonoidHomWithZero

/-- The image of the valuation, as a `CommGroupWithZero` -/
def rangeGroup₀ := MonoidHomWithZero.range₀ v

theorem mem_rangeGroup₀_iff {x : Γ₀} :
    x ∈ v.rangeGroup₀ ↔ ∃ a b, v a ≠ 0 ∧ v a * x = v b :=
  MonoidHomWithZero.mem_range₀_iff

theorem mem_rangeGroup_iff_mem_rangeGroup₀ {x : Γ₀ˣ} :
    x ∈ v.rangeGroup ↔ (x : Γ₀) ∈ v.rangeGroup₀ := by
  simp only [mem_rangeGroup_iff, mem_rangeGroup₀_iff]

theorem mem_rangeGroup₀ {a : R} : v a ∈ v.rangeGroup₀ :=
  MonoidHomWithZero.mem_range₀ v

instance : CommGroupWithZero v.rangeGroup₀ := by
  unfold rangeGroup₀
  infer_instance

instance : PartialOrder v.rangeGroup₀ where
  le a b := (a : Γ₀) ≤ b
  lt a b := (a : Γ₀) < b
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  lt_iff_le_not_le _ _ := lt_iff_le_not_le
  le_antisymm _ _ := le_antisymm

instance: LinearOrderedCommMonoid v.rangeGroup₀ where
  toCommMonoid := inferInstance
  toPartialOrder := inferInstance
  mul_le_mul_left _ _ h _ := by
    apply OrderedCommMonoid.mul_le_mul_left
    exact h
  le_total a b := LinearOrder.le_total (a : Γ₀) b
  decidableLE := LinearOrder.decidableLE
  decidableEq := LinearOrder.decidableEq
  decidableLT := LinearOrder.decidableLT
  min a b := ⟨min (a : Γ₀) b, by
    rw [min_def]; split_ifs with h; exact a.prop; exact b.prop⟩
  max a b := ⟨max (a : Γ₀) b, by
    rw [max_def]; split_ifs with h; exact b.prop; exact a.prop⟩
  compare a b := compare (a : Γ₀) b
  min_def a b := by
    rw [← Subtype.coe_inj, min_def, apply_ite (f := fun (x : v.rangeGroup₀) ↦ (x : Γ₀))]
  max_def a b := by
    rw [← Subtype.coe_inj, max_def, apply_ite (f := fun (x : v.rangeGroup₀) ↦ (x : Γ₀))]
  compare_eq_compareOfLessAndEq a b := by
    change compare (a : Γ₀) b = _
    rw [LinearOrderedCommMonoid.compare_eq_compareOfLessAndEq (a : Γ₀) b]
    simp only [compareOfLessAndEq]
    by_cases h : a < b
    · rw [if_pos h, if_pos (show (a : Γ₀) < b by exact h)]
    · rw [if_neg h, if_neg (show ¬ (a : Γ₀) < b by exact h)]
      by_cases h : a = b
      · rw [if_pos h, if_pos (show (a : Γ₀) = b by rw [Subtype.coe_inj]; exact h)]
      · rw [if_neg h, if_neg (show ¬ (a : Γ₀) = b by rw [Subtype.coe_inj]; exact h)]

instance : LinearOrderedCommMonoidWithZero v.rangeGroup₀ where
  zero_mul := zero_mul
  mul_zero := mul_zero
  zero_le_one := by
    change (0 : Γ₀) ≤ 1
    apply zero_le_one'

instance : LinearOrderedCommGroupWithZero v.rangeGroup₀ where
  toLinearOrderedCommMonoidWithZero := inferInstance
  inv_zero := inv_zero
  mul_inv_cancel := GroupWithZero.mul_inv_cancel

/-- The same valuation, with codomain restricted to `v.rangeGroup₀` -/
def restriction_rangeGroup₀ : Valuation R v.rangeGroup₀ where
  toFun x := ⟨v x, by rw [mem_rangeGroup₀_iff]; use 1, x; simp⟩
  map_zero' := by simp only [_root_.map_zero]; rfl
  map_one' := by simp [← Subtype.coe_inj]
  map_mul' x y := by simp [← Subtype.coe_inj]
  map_add_le_max' x y := v.map_add x y

/-- The equiv between units of rangeGroup₀ and those of rangeGroup -/
def units_rangeGroup₀_equiv_rangeGroup : v.rangeGroup₀ˣ ≃* v.rangeGroup where
  toFun u := by
    let x := (u.val : Γ₀)
    have hx : x ≠ 0 := fun h ↦ u.ne_zero (by
      rw [← Subtype.coe_inj]
      exact h)
    let ξ : Γ₀ˣ := Units.mk0 x hx
    let hx' := u.val.prop
    exact ⟨ξ, (mem_rangeGroup_iff_mem_rangeGroup₀ v).mpr hx'⟩
  invFun u := by
    let x := (u : Γ₀ˣ)
    let ξ : v.rangeGroup₀ := ⟨x.val, (mem_rangeGroup_iff_mem_rangeGroup₀ v).mp u.prop⟩
    have hξ : ξ ≠ 0 := by
      rw [ne_eq, ← Subtype.coe_inj]
      exact x.ne_zero
    exact Units.mk0 ξ hξ
  left_inv u := by rw [← Units.eq_iff]; rfl
  right_inv x := by rw [← Subtype.coe_inj, ← Units.eq_iff]; rfl
  map_mul' u v := by rw [← Subtype.coe_inj, ← Units.eq_iff]; rfl

end ACL

/-- The subgroup with zero generated by the image of the valuation -/
abbrev rangeGroupWithZero := WithZero v.rangeGroup

-- This is a "new" valuation, taking values in `rangeGroupWithZero`
/-- The same valuation, with codomain restricted to `v.rangeGroupWithZero` -/
def restrictionRangeGroup : Valuation R v.rangeGroupWithZero where
  toFun := by
    intro r
    by_cases h : v r ≠ 0
    · use (⟨Units.mk0 (v r) h, v.mem_rangeGroup (by rfl)⟩ : v.rangeGroup)
    · use 0
  map_zero' := by simp
  map_one' := by
    simp only [_root_.map_one, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceDIte, Units.mk0_one]
    rfl
  map_mul' := by
    intro _ _
    simp only [_root_.map_mul, ne_eq, mul_eq_zero, not_or, Units.mk0_mul, dite_not]
    split_ifs with h hx _ hy <;>
    try simp_all only <;>
    try rfl
    · rfl
    · simp_all only [not_true_eq_false, not_false_eq_true, and_true, zero_mul]
  map_add_le_max' := by
    intro x y
    simp only [ne_eq, dite_not, le_max_iff]
    split_ifs with h _ _ _ hx hy hh
    · simp_all only [le_refl, or_self]
    · simp_all only [le_refl, zero_le', or_self]
    · simp_all only [zero_le', le_refl, or_self]
    · simp_all only [zero_le', or_self]
    · have := v.map_add x y
      simp_all only [le_zero_iff, WithZero.coe_ne_zero, or_self, max_self, le_zero_iff]
    · have := v.map_add' x y
      simp_all only [le_zero_iff, false_or, WithZero.coe_ne_zero, WithZero.coe_le_coe,
        Subtype.mk_le_mk, ge_iff_le]
      exact this
    · have := v.map_add' x y
      simp_all only [le_zero_iff, false_or, WithZero.coe_ne_zero, WithZero.coe_le_coe,
        Subtype.mk_le_mk, ge_iff_le]
      exact this
    · have := v.map_add' x y
      simp_all only [le_zero_iff, false_or, WithZero.coe_ne_zero, WithZero.coe_le_coe,
        Subtype.mk_le_mk, ge_iff_le]
      exact this

lemma restriction_ne_zero (h : v x ≠ 0) : v.restrictionRangeGroup x ≠ 0 := by
  simpa only [restrictionRangeGroup, ne_eq, dite_not, coe_mk, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, dite_eq_left_iff, WithZero.coe_ne_zero, imp_false, Decidable.not_not]

lemma restriction_zero : v.restrictionRangeGroup 0 = 0 := by
  simp only [restrictionRangeGroup, ne_eq, dite_not, _root_.map_zero]

example (a b c : Prop) (h : ¬ a) : if a then b else c = c := by
  simp only [h, ↓reduceIte]

lemma restriction_eq (h : v x ≠ 0) :
    WithZero.unzero (v.restriction_ne_zero h) =
      (⟨Units.mk0 (v x) h, v.mem_rangeGroup (by rfl)⟩ : v.rangeGroup) := by
  simp only [restrictionRangeGroup, ne_eq, dite_not, coe_mk, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, h, ↓reduceDIte, WithZero.unzero_coe]

lemma restriction_eq' (h : v x ≠ 0) :
    WithZero.unzero (v.restriction_ne_zero h) =
      Units.mk0 (v x) h := by
  rw [v.restriction_eq h]

--from here on the old stuff

@[simp]
theorem map_neg (x : R) : v (-x) = v x :=
  v.toMonoidWithZeroHom.toMonoidHom.map_neg x

theorem map_sub_swap (x y : R) : v (x - y) = v (y - x) :=
  v.toMonoidWithZeroHom.toMonoidHom.map_sub_swap x y

theorem map_inv {R : Type*} [DivisionRing R] (v : Valuation R Γ₀) : ∀ x, v x⁻¹ = (v x)⁻¹ :=
  map_inv₀ _

theorem map_div {R : Type*} [DivisionRing R] (v : Valuation R Γ₀) : ∀ x y, v (x / y) = v x / v y :=
  map_div₀ _

theorem map_sub (x y : R) : v (x - y) ≤ max (v x) (v y) :=
  calc
    v (x - y) = v (x + -y) := by rw [sub_eq_add_neg]
    _ ≤ max (v x) (v <| -y) := v.map_add _ _
    _ = max (v x) (v y) := by rw [map_neg]

theorem map_sub_le {x y g} (hx : v x ≤ g) (hy : v y ≤ g) : v (x - y) ≤ g := by
  rw [sub_eq_add_neg]
  exact v.map_add_le hx (le_trans (le_of_eq (v.map_neg y)) hy)

theorem map_add_of_distinct_val (h : v x ≠ v y) : v (x + y) = max (v x) (v y) := by
  suffices ¬v (x + y) < max (v x) (v y) from
    or_iff_not_imp_right.1 (le_iff_eq_or_lt.1 (v.map_add x y)) this
  intro h'
  wlog vyx : v y < v x generalizing x y
  · refine this h.symm ?_ (h.lt_or_lt.resolve_right vyx)
    rwa [add_comm, max_comm]
  rw [max_eq_left_of_lt vyx] at h'
  apply lt_irrefl (v x)
  calc
    v x = v (x + y - y) := by simp
    _ ≤ max (v <| x + y) (v y) := map_sub _ _ _
    _ < v x := max_lt h' vyx

theorem map_add_eq_of_lt_right (h : v x < v y) : v (x + y) = v y :=
  (v.map_add_of_distinct_val h.ne).trans (max_eq_right_iff.mpr h.le)

theorem map_add_eq_of_lt_left (h : v y < v x) : v (x + y) = v x := by
  rw [add_comm]; exact map_add_eq_of_lt_right _ h

theorem map_sub_eq_of_lt_right (h : v x < v y) : v (x - y) = v y := by
  rw [sub_eq_add_neg, map_add_eq_of_lt_right, map_neg]
  rwa [map_neg]

theorem map_sub_eq_of_lt_left (h : v y < v x) : v (x - y) = v x := by
  rw [sub_eq_add_neg, map_add_eq_of_lt_left]
  rwa [map_neg]

theorem map_eq_of_sub_lt (h : v (y - x) < v x) : v y = v x := by
  have := Valuation.map_add_of_distinct_val v (ne_of_gt h).symm
  rw [max_eq_right (le_of_lt h)] at this
  simpa using this

theorem map_one_add_of_lt (h : v x < 1) : v (1 + x) = 1 := by
  rw [← v.map_one] at h
  simpa only [v.map_one] using v.map_add_eq_of_lt_left h

theorem map_one_sub_of_lt (h : v x < 1) : v (1 - x) = 1 := by
  rw [← v.map_one, ← v.map_neg] at h
  rw [sub_eq_add_neg 1 x]
  simpa only [v.map_one, v.map_neg] using v.map_add_eq_of_lt_left h

theorem one_lt_val_iff (v : Valuation K Γ₀) {x : K} (h : x ≠ 0) : 1 < v x ↔ v x⁻¹ < 1 := by
  simpa using (inv_lt_inv₀ (v.ne_zero_iff.2 h) one_ne_zero).symm

theorem one_le_val_iff (v : Valuation K Γ₀) {x : K} (h : x ≠ 0) : 1 ≤ v x ↔ v x⁻¹ ≤ 1 := by
  convert (one_lt_val_iff v (inv_ne_zero h)).symm.not <;>
  push_neg <;> simp only [inv_inv]

theorem val_lt_one_iff (v : Valuation K Γ₀) {x : K} (h : x ≠ 0) : v x < 1 ↔ 1 < v x⁻¹ := by
  simpa only [inv_inv] using (one_lt_val_iff v (inv_ne_zero h)).symm

theorem val_le_one_iff (v : Valuation K Γ₀) {x : K} (h : x ≠ 0) : v x ≤ 1 ↔ 1 ≤ v x⁻¹ := by
  simpa [inv_inv] using (one_le_val_iff v (inv_ne_zero h)).symm

theorem val_eq_one_iff (v : Valuation K Γ₀) {x : K} : v x = 1 ↔ v x⁻¹ = 1 := by
  by_cases h : x = 0
  · simp only [map_inv₀, inv_eq_one]
  · simpa only [le_antisymm_iff, And.comm] using and_congr (one_le_val_iff v h) (val_le_one_iff v h)

theorem val_le_one_or_val_inv_lt_one (v : Valuation K Γ₀) (x : K) : v x ≤ 1 ∨ v x⁻¹ < 1 := by
  by_cases h : x = 0
  · simp only [h, _root_.map_zero, zero_le', inv_zero, zero_lt_one, or_self]
  · simp only [← one_lt_val_iff v h, le_or_lt]

/--
This theorem is a weaker version of `Valuation.val_le_one_or_val_inv_lt_one`, but more symmetric
in `x` and `x⁻¹`.
-/
theorem val_le_one_or_val_inv_le_one (v : Valuation K Γ₀) (x : K) : v x ≤ 1 ∨ v x⁻¹ ≤ 1 := by
  by_cases h : x = 0
  · simp only [h, _root_.map_zero, zero_le', inv_zero, or_self]
  · simp only [← one_le_val_iff v h, le_total]

/-- The subgroup of elements whose valuation is less than a certain unit. -/
def ltAddSubgroup (v : Valuation R Γ₀) (γ : Γ₀ˣ) : AddSubgroup R where
  carrier := { x | v x < γ }
  zero_mem' := by simp
  add_mem' {x y} x_in y_in := lt_of_le_of_lt (v.map_add x y) (max_lt x_in y_in)
  neg_mem' x_in := by rwa [Set.mem_setOf, map_neg]

theorem mem_ltAddSubgroup_iff {v : Valuation R Γ₀} {γ : Γ₀ˣ} {r : R} :
    r ∈ v.ltAddSubgroup γ ↔ v r < γ := rfl.to_iff

end Group

end Basic

-- end of section
namespace IsEquiv

variable [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] [LinearOrderedCommMonoidWithZero Γ'₀]
  {v : Valuation R Γ₀} {v₁ : Valuation R Γ₀} {v₂ : Valuation R Γ'₀} {v₃ : Valuation R Γ''₀}

@[refl]
theorem refl : v.IsEquiv v := fun _ _ => Iff.refl _

@[symm]
theorem symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁ := fun _ _ => Iff.symm (h _ _)

@[trans]
theorem trans (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v₃) : v₁.IsEquiv v₃ := fun _ _ =>
  Iff.trans (h₁₂ _ _) (h₂₃ _ _)

theorem of_eq {v' : Valuation R Γ₀} (h : v = v') : v.IsEquiv v' := by subst h; rfl

theorem map {v' : Valuation R Γ₀} (f : Γ₀ →*₀ Γ'₀) (hf : Monotone f) (inf : Injective f)
    (h : v.IsEquiv v') : (v.map f hf).IsEquiv (v'.map f hf) :=
  let H : StrictMono f := hf.strictMono_of_injective inf
  fun r s =>
  calc
    f (v r) ≤ f (v s) ↔ v r ≤ v s := by rw [H.le_iff_le]
    _ ↔ v' r ≤ v' s := h r s
    _ ↔ f (v' r) ≤ f (v' s) := by rw [H.le_iff_le]

/-- `comap` preserves equivalence. -/
theorem comap {S : Type*} [Ring S] (f : S →+* R) (h : v₁.IsEquiv v₂) :
    (v₁.comap f).IsEquiv (v₂.comap f) := fun r s => h (f r) (f s)

theorem val_eq (h : v₁.IsEquiv v₂) {r s : R} : v₁ r = v₁ s ↔ v₂ r = v₂ s := by
  simpa only [le_antisymm_iff] using and_congr (h r s) (h s r)

theorem ne_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r ≠ 0 ↔ v₂ r ≠ 0 := by
  have : v₁ r ≠ v₁ 0 ↔ v₂ r ≠ v₂ 0 := not_congr h.val_eq
  rwa [v₁.map_zero, v₂.map_zero] at this

end IsEquiv

-- end of namespace
section

theorem isEquiv_of_map_strictMono [LinearOrderedCommMonoidWithZero Γ₀]
    [LinearOrderedCommMonoidWithZero Γ'₀] [Ring R] {v : Valuation R Γ₀} (f : Γ₀ →*₀ Γ'₀)
    (H : StrictMono f) : IsEquiv (v.map f H.monotone) v := fun _x _y =>
  ⟨H.le_iff_le.mp, fun h => H.monotone h⟩

theorem isEquiv_of_val_le_one [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ'₀] (v : Valuation K Γ₀) (v' : Valuation K Γ'₀)
    (h : ∀ {x : K}, v x ≤ 1 ↔ v' x ≤ 1) : v.IsEquiv v' := by
  intro x y
  obtain rfl | hy := eq_or_ne y 0
  · simp
  · rw [← div_le_one₀, ← v.map_div, h, v'.map_div, div_le_one₀] <;>
      rwa [zero_lt_iff, ne_zero_iff]

theorem isEquiv_iff_val_le_one [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ'₀] (v : Valuation K Γ₀) (v' : Valuation K Γ'₀) :
    v.IsEquiv v' ↔ ∀ {x : K}, v x ≤ 1 ↔ v' x ≤ 1 :=
  ⟨fun h x => by simpa using h x 1, isEquiv_of_val_le_one _ _⟩

theorem isEquiv_iff_val_eq_one [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ'₀] (v : Valuation K Γ₀) (v' : Valuation K Γ'₀) :
    v.IsEquiv v' ↔ ∀ {x : K}, v x = 1 ↔ v' x = 1 := by
  constructor
  · intro h x
    simpa using @IsEquiv.val_eq _ _ _ _ _ _ v v' h x 1
  · intro h
    apply isEquiv_of_val_le_one
    intro x
    constructor
    · intro hx
      rcases lt_or_eq_of_le hx with hx' | hx'
      · have : v (1 + x) = 1 := by
          rw [← v.map_one]
          apply map_add_eq_of_lt_left
          simpa
        rw [h] at this
        rw [show x = -1 + (1 + x) by simp]
        refine le_trans (v'.map_add _ _) ?_
        simp [this]
      · rw [h] at hx'
        exact le_of_eq hx'
    · intro hx
      rcases lt_or_eq_of_le hx with hx' | hx'
      · have : v' (1 + x) = 1 := by
          rw [← v'.map_one]
          apply map_add_eq_of_lt_left
          simpa
        rw [← h] at this
        rw [show x = -1 + (1 + x) by simp]
        refine le_trans (v.map_add _ _) ?_
        simp [this]
      · rw [← h] at hx'
        exact le_of_eq hx'

theorem isEquiv_iff_val_lt_one [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ'₀] (v : Valuation K Γ₀) (v' : Valuation K Γ'₀) :
    v.IsEquiv v' ↔ ∀ {x : K}, v x < 1 ↔ v' x < 1 := by
  constructor
  · intro h x
    simp only [lt_iff_le_and_ne,
      and_congr ((isEquiv_iff_val_le_one _ _).1 h) ((isEquiv_iff_val_eq_one _ _).1 h).not]
  · rw [isEquiv_iff_val_eq_one]
    intro h x
    by_cases hx : x = 0
    · simp only [(zero_iff _).2 hx, zero_ne_one]
    constructor
    · intro hh
      by_contra h_1
      cases ne_iff_lt_or_gt.1 h_1 with
      | inl h_2 => simpa [hh, lt_self_iff_false] using h.2 h_2
      | inr h_2 =>
          rw [← inv_one, ← inv_eq_iff_eq_inv, ← map_inv₀] at hh
          exact hh.not_lt (h.2 ((one_lt_val_iff v' hx).1 h_2))
    · intro hh
      by_contra h_1
      cases ne_iff_lt_or_gt.1 h_1 with
      | inl h_2 => simpa [hh, lt_self_iff_false] using h.1 h_2
      | inr h_2 =>
        rw [← inv_one, ← inv_eq_iff_eq_inv, ← map_inv₀] at hh
        exact hh.not_lt (h.1 ((one_lt_val_iff v hx).1 h_2))

theorem isEquiv_iff_val_sub_one_lt_one [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ'₀] (v : Valuation K Γ₀) (v' : Valuation K Γ'₀) :
    v.IsEquiv v' ↔ ∀ {x : K}, v (x - 1) < 1 ↔ v' (x - 1) < 1 := by
  rw [isEquiv_iff_val_lt_one]
  exact (Equiv.subRight 1).surjective.forall

theorem isEquiv_tfae [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ'₀]
    (v : Valuation K Γ₀) (v' : Valuation K Γ'₀) :
    [v.IsEquiv v', ∀ {x}, v x ≤ 1 ↔ v' x ≤ 1, ∀ {x}, v x = 1 ↔ v' x = 1, ∀ {x}, v x < 1 ↔ v' x < 1,
        ∀ {x}, v (x - 1) < 1 ↔ v' (x - 1) < 1].TFAE := by
  tfae_have 1 ↔ 2; · apply isEquiv_iff_val_le_one
  tfae_have 1 ↔ 3; · apply isEquiv_iff_val_eq_one
  tfae_have 1 ↔ 4; · apply isEquiv_iff_val_lt_one
  tfae_have 1 ↔ 5; · apply isEquiv_iff_val_sub_one_lt_one
  tfae_finish

end

section Supp

variable [CommRing R]
variable [LinearOrderedCommMonoidWithZero Γ₀] [LinearOrderedCommMonoidWithZero Γ'₀]
variable (v : Valuation R Γ₀)

/-- The support of a valuation `v : R → Γ₀` is the ideal of `R` where `v` vanishes. -/
def supp : Ideal R where
  carrier := { x | v x = 0 }
  zero_mem' := map_zero v
  add_mem' {x y} hx hy := le_zero_iff.mp <|
    calc
      v (x + y) ≤ max (v x) (v y) := v.map_add x y
      _ ≤ 0 := max_le (le_zero_iff.mpr hx) (le_zero_iff.mpr hy)
  smul_mem' c x hx :=
    calc
      v (c * x) = v c * v x := map_mul v c x
      _ = v c * 0 := congr_arg _ hx
      _ = 0 := mul_zero _

@[simp]
theorem mem_supp_iff (x : R) : x ∈ supp v ↔ v x = 0 :=
  Iff.rfl

/-- The support of a valuation is a prime ideal. -/
instance [Nontrivial Γ₀] [NoZeroDivisors Γ₀] : Ideal.IsPrime (supp v) :=
  ⟨fun h =>
    one_ne_zero (α := Γ₀) <|
      calc
        1 = v 1 := v.map_one.symm
        _ = 0 := by rw [← mem_supp_iff, h]; exact Submodule.mem_top,
   fun {x y} hxy => by
    simp only [mem_supp_iff] at hxy ⊢
    rw [v.map_mul x y] at hxy
    exact eq_zero_or_eq_zero_of_mul_eq_zero hxy⟩

theorem map_add_supp (a : R) {s : R} (h : s ∈ supp v) : v (a + s) = v a := by
  have aux : ∀ a s, v s = 0 → v (a + s) ≤ v a := by
    intro a' s' h'
    refine le_trans (v.map_add a' s') (max_le le_rfl ?_)
    simp [h']
  apply le_antisymm (aux a s h)
  calc
    v a = v (a + s + -s) := by simp
    _ ≤ v (a + s) := aux (a + s) (-s) (by rwa [← Ideal.neg_mem_iff] at h)

theorem comap_supp {S : Type*} [CommRing S] (f : S →+* R) :
    supp (v.comap f) = Ideal.comap f v.supp :=
  Ideal.ext fun x => by rw [mem_supp_iff, Ideal.mem_comap, mem_supp_iff, comap_apply]

end Supp

-- end of section
end Valuation

section AddMonoid

variable (R) [Ring R] (Γ₀ : Type*) [LinearOrderedAddCommMonoidWithTop Γ₀]

/-- The type of `Γ₀`-valued additive valuations on `R`. -/
-- porting note (#5171): removed @[nolint has_nonempty_instance]
def AddValuation :=
  Valuation R (Multiplicative Γ₀ᵒᵈ)

end AddMonoid

namespace AddValuation

variable {Γ₀ : Type*} {Γ'₀ : Type*}

section Basic

section Monoid

/-- A valuation is coerced to the underlying function `R → Γ₀`. -/
instance (R) (Γ₀) [Ring R] [LinearOrderedAddCommMonoidWithTop Γ₀] :
    FunLike (AddValuation R Γ₀) R Γ₀ where
  coe v := v.toMonoidWithZeroHom.toFun
  coe_injective' f g := by cases f; cases g; simp (config := {contextual := true})

variable [Ring R] [LinearOrderedAddCommMonoidWithTop Γ₀] [LinearOrderedAddCommMonoidWithTop Γ'₀]
  (v : AddValuation R Γ₀) {x y z : R}

section

variable (f : R → Γ₀) (h0 : f 0 = ⊤) (h1 : f 1 = 0)
variable (hadd : ∀ x y, min (f x) (f y) ≤ f (x + y)) (hmul : ∀ x y, f (x * y) = f x + f y)

/-- An alternate constructor of `AddValuation`, that doesn't reference `Multiplicative Γ₀ᵒᵈ` -/
def of : AddValuation R Γ₀ where
  toFun := f
  map_one' := h1
  map_zero' := h0
  map_add_le_max' := hadd
  map_mul' := hmul

variable {h0} {h1} {hadd} {hmul} {r : R}

@[simp]
theorem of_apply : (of f h0 h1 hadd hmul) r = f r := rfl

/-- The `Valuation` associated to an `AddValuation` (useful if the latter is constructed using
`AddValuation.of`). -/
def valuation : Valuation R (Multiplicative Γ₀ᵒᵈ) :=
  v

@[simp]
theorem valuation_apply (r : R) : v.valuation r = Multiplicative.ofAdd (OrderDual.toDual (v r)) :=
  rfl

end

-- Porting note: Lean get confused about namespaces and instances below
@[simp]
theorem map_zero : v 0 = (⊤ : Γ₀) :=
  Valuation.map_zero v

@[simp]
theorem map_one : v 1 = (0 : Γ₀) :=
  Valuation.map_one v

/- Porting note: helper wrapper to coerce `v` to the correct function type -/
/-- A helper function for Lean to inferring types correctly -/
def asFun : R → Γ₀ := v

@[simp]
theorem map_mul : ∀ (x y : R), v (x * y) = v x + v y :=
  Valuation.map_mul v

-- Porting note: LHS simplified so created map_add' and removed simp tag
theorem map_add : ∀ (x y : R), min (v x) (v y) ≤ v (x + y) :=
  Valuation.map_add v

@[simp]
theorem map_add' : ∀ (x y : R), v x ≤ v (x + y) ∨ v y ≤ v (x + y) := by
  intro x y
  rw [← @min_le_iff _ _ (v x) (v y) (v (x+y)), ← ge_iff_le]
  apply map_add

theorem map_le_add {x y : R} {g : Γ₀} (hx : g ≤ v x) (hy : g ≤ v y) : g ≤ v (x + y) :=
  Valuation.map_add_le v hx hy

theorem map_lt_add {x y : R} {g : Γ₀} (hx : g < v x) (hy : g < v y) : g < v (x + y) :=
  Valuation.map_add_lt v hx hy

theorem map_le_sum {ι : Type*} {s : Finset ι} {f : ι → R} {g : Γ₀} (hf : ∀ i ∈ s, g ≤ v (f i)) :
    g ≤ v (∑ i ∈ s, f i) :=
  v.map_sum_le hf

theorem map_lt_sum {ι : Type*} {s : Finset ι} {f : ι → R} {g : Γ₀} (hg : g ≠ ⊤)
    (hf : ∀ i ∈ s, g < v (f i)) : g < v (∑ i ∈ s, f i) :=
  v.map_sum_lt hg hf

theorem map_lt_sum' {ι : Type*} {s : Finset ι} {f : ι → R} {g : Γ₀} (hg : g < ⊤)
    (hf : ∀ i ∈ s, g < v (f i)) : g < v (∑ i ∈ s, f i) :=
  v.map_sum_lt' hg hf

@[simp]
theorem map_pow : ∀ (x : R) (n : ℕ), v (x ^ n) = n • (v x) :=
  Valuation.map_pow v

@[ext]
theorem ext {v₁ v₂ : AddValuation R Γ₀} (h : ∀ r, v₁ r = v₂ r) : v₁ = v₂ :=
  Valuation.ext h

-- The following definition is not an instance, because we have more than one `v` on a given `R`.
-- In addition, type class inference would not be able to infer `v`.
/-- A valuation gives a preorder on the underlying ring. -/
def toPreorder : Preorder R :=
  Preorder.lift v

/-- If `v` is an additive valuation on a division ring then `v(x) = ⊤` iff `x = 0`. -/
@[simp]
theorem top_iff [Nontrivial Γ₀] (v : AddValuation K Γ₀) {x : K} : v x = (⊤ : Γ₀) ↔ x = 0 :=
  v.zero_iff

theorem ne_top_iff [Nontrivial Γ₀] (v : AddValuation K Γ₀) {x : K} : v x ≠ (⊤ : Γ₀) ↔ x ≠ 0 :=
  v.ne_zero_iff

/-- A ring homomorphism `S → R` induces a map `AddValuation R Γ₀ → AddValuation S Γ₀`. -/
def comap {S : Type*} [Ring S] (f : S →+* R) (v : AddValuation R Γ₀) : AddValuation S Γ₀ :=
  Valuation.comap f v

@[simp]
theorem comap_id : v.comap (RingHom.id R) = v :=
  Valuation.comap_id v

theorem comap_comp {S₁ : Type*} {S₂ : Type*} [Ring S₁] [Ring S₂] (f : S₁ →+* S₂) (g : S₂ →+* R) :
    v.comap (g.comp f) = (v.comap g).comap f :=
  Valuation.comap_comp v f g

/-- A `≤`-preserving, `⊤`-preserving group homomorphism `Γ₀ → Γ'₀` induces a map
  `AddValuation R Γ₀ → AddValuation R Γ'₀`.
-/
def map (f : Γ₀ →+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f) (v : AddValuation R Γ₀) :
    AddValuation R Γ'₀ :=
  @Valuation.map R (Multiplicative Γ₀ᵒᵈ) (Multiplicative Γ'₀ᵒᵈ) _ _ _
    { toFun := f
      map_mul' := f.map_add
      map_one' := f.map_zero
      map_zero' := ht } (fun _ _ h => hf h) v

/-- Two additive valuations on `R` are defined to be equivalent if they induce the same
  preorder on `R`. -/
def IsEquiv (v₁ : AddValuation R Γ₀) (v₂ : AddValuation R Γ'₀) : Prop :=
  Valuation.IsEquiv v₁ v₂

end Monoid

section Group

variable [LinearOrderedAddCommGroupWithTop Γ₀] [Ring R] (v : AddValuation R Γ₀) {x y z : R}

@[simp]
theorem map_inv (v : AddValuation K Γ₀) {x : K} : v x⁻¹ = - (v x) :=
  map_inv₀ v.valuation x

@[simp]
theorem map_div (v : AddValuation K Γ₀) {x y : K} : v (x / y) = v x - v y :=
  map_div₀ v.valuation x y

@[simp]
theorem map_neg (x : R) : v (-x) = v x :=
  Valuation.map_neg v x

theorem map_sub_swap (x y : R) : v (x - y) = v (y - x) :=
  Valuation.map_sub_swap v x y

theorem map_sub (x y : R) : min (v x) (v y) ≤ v (x - y) :=
  Valuation.map_sub v x y

theorem map_le_sub {x y : R} {g : Γ₀} (hx : g ≤ v x) (hy : g ≤ v y) : g ≤ v (x - y) :=
  Valuation.map_sub_le v hx hy

theorem map_add_of_distinct_val (h : v x ≠ v y) : v (x + y) = @Min.min Γ₀ _ (v x) (v y) :=
  Valuation.map_add_of_distinct_val v h

theorem map_add_eq_of_lt_left {x y : R} (h : v x < v y) :
    v (x + y) = v x := by
  rw [map_add_of_distinct_val _ h.ne, min_eq_left h.le]

theorem map_add_eq_of_lt_right {x y : R} (hx : v y < v x) :
    v (x + y) = v y := add_comm y x ▸ map_add_eq_of_lt_left v hx

theorem map_sub_eq_of_lt_left {x y : R} (hx : v x < v y) :
    v (x - y) = v x := by
  rw [sub_eq_add_neg]
  apply map_add_eq_of_lt_left
  rwa [map_neg]

theorem map_sub_eq_of_lt_right {x y : R} (hx : v y < v x) :
    v (x - y) = v y := map_sub_swap v x y ▸ map_sub_eq_of_lt_left v hx

theorem map_eq_of_lt_sub (h : v x < v (y - x)) : v y = v x :=
  Valuation.map_eq_of_sub_lt v h

end Group

end Basic

namespace IsEquiv

variable [LinearOrderedAddCommMonoidWithTop Γ₀] [LinearOrderedAddCommMonoidWithTop Γ'₀]
  [Ring R]
  {Γ''₀ : Type*} [LinearOrderedAddCommMonoidWithTop Γ''₀]
  {v : AddValuation R Γ₀}
   {v₁ : AddValuation R Γ₀} {v₂ : AddValuation R Γ'₀} {v₃ : AddValuation R Γ''₀}

@[refl]
theorem refl : v.IsEquiv v :=
  Valuation.IsEquiv.refl

@[symm]
theorem symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁ :=
  Valuation.IsEquiv.symm h

@[trans]
theorem trans (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v₃) : v₁.IsEquiv v₃ :=
  Valuation.IsEquiv.trans h₁₂ h₂₃

theorem of_eq {v' : AddValuation R Γ₀} (h : v = v') : v.IsEquiv v' :=
  Valuation.IsEquiv.of_eq h

theorem map {v' : AddValuation R Γ₀} (f : Γ₀ →+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f)
    (inf : Injective f) (h : v.IsEquiv v') : (v.map f ht hf).IsEquiv (v'.map f ht hf) :=
  @Valuation.IsEquiv.map R (Multiplicative Γ₀ᵒᵈ) (Multiplicative Γ'₀ᵒᵈ) _ _ _ _ _
    { toFun := f
      map_mul' := f.map_add
      map_one' := f.map_zero
      map_zero' := ht } (fun _x _y h => hf h) inf h

/-- `comap` preserves equivalence. -/
theorem comap {S : Type*} [Ring S] (f : S →+* R) (h : v₁.IsEquiv v₂) :
    (v₁.comap f).IsEquiv (v₂.comap f) :=
  Valuation.IsEquiv.comap f h

theorem val_eq (h : v₁.IsEquiv v₂) {r s : R} : v₁ r = v₁ s ↔ v₂ r = v₂ s :=
  Valuation.IsEquiv.val_eq h

theorem ne_top (h : v₁.IsEquiv v₂) {r : R} : v₁ r ≠ (⊤ : Γ₀) ↔ v₂ r ≠ (⊤ : Γ'₀) :=
  Valuation.IsEquiv.ne_zero h

end IsEquiv

section Supp

variable [LinearOrderedAddCommMonoidWithTop Γ₀] [LinearOrderedAddCommMonoidWithTop Γ'₀]
variable [CommRing R]
variable (v : AddValuation R Γ₀)

/-- The support of an additive valuation `v : R → Γ₀` is the ideal of `R` where `v x = ⊤` -/
def supp : Ideal R :=
  Valuation.supp v

@[simp]
theorem mem_supp_iff (x : R) : x ∈ supp v ↔ v x = (⊤ : Γ₀) :=
  Valuation.mem_supp_iff v x

theorem map_add_supp (a : R) {s : R} (h : s ∈ supp v) : v (a + s) = v a :=
  Valuation.map_add_supp v a h

end Supp

-- end of section
end AddValuation

section ValuationNotation

/-- Notation for `WithZero (Multiplicative ℕ)` -/
scoped[DiscreteValuation] notation "ℕₘ₀" => WithZero (Multiplicative ℕ)

/-- Notation for `WithZero (Multiplicative ℤ)` -/
scoped[DiscreteValuation] notation "ℤₘ₀" => WithZero (Multiplicative ℤ)

end ValuationNotation
