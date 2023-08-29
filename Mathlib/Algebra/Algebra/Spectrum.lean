/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Star.Pointwise
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Tactic.NoncommRing

#align_import algebra.algebra.spectrum from "leanprover-community/mathlib"@"58a272265b5e05f258161260dd2c5d247213cbd3"

/-!
# Spectrum of an element in an algebra
This file develops the basic theory of the spectrum of an element of an algebra.
This theory will serve as the foundation for spectral theory in Banach algebras.

## Main definitions

* `resolventSet a : Set R`: the resolvent set of an element `a : A` where
  `A` is an `R`-algebra.
* `spectrum a : Set R`: the spectrum of an element `a : A` where
  `A` is an `R`-algebra.
* `resolvent : R → A`: the resolvent function is `fun r ↦ Ring.inverse (↑ₐr - a)`, and hence
  when `r ∈ resolvent R A`, it is actually the inverse of the unit `(↑ₐr - a)`.

## Main statements

* `spectrum.unit_smul_eq_smul` and `spectrum.smul_eq_smul`: units in the scalar ring commute
  (multiplication) with the spectrum, and over a field even `0` commutes with the spectrum.
* `spectrum.left_add_coset_eq`: elements of the scalar ring commute (addition) with the spectrum.
* `spectrum.unit_mem_mul_iff_mem_swap_mul` and `spectrum.preimage_units_mul_eq_swap_mul`: the
  units (of `R`) in `σ (a*b)` coincide with those in `σ (b*a)`.
* `spectrum.scalar_eq`: in a nontrivial algebra over a field, the spectrum of a scalar is
  a singleton.

## Notations

* `σ a` : `spectrum R a` of `a : A`
-/


open Set

open scoped Pointwise

universe u v

section Defs

variable (R : Type u) {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

local notation "↑ₐ" => algebraMap R A

-- definition and basic properties
/-- Given a commutative ring `R` and an `R`-algebra `A`, the *resolvent set* of `a : A`
is the `Set R` consisting of those `r : R` for which `r•1 - a` is a unit of the
algebra `A`.  -/
def resolventSet (a : A) : Set R :=
  {r : R | IsUnit (↑ₐ r - a)}
#align resolvent_set resolventSet

/-- Given a commutative ring `R` and an `R`-algebra `A`, the *spectrum* of `a : A`
is the `Set R` consisting of those `r : R` for which `r•1 - a` is not a unit of the
algebra `A`.

The spectrum is simply the complement of the resolvent set.  -/
def spectrum (a : A) : Set R :=
  (resolventSet R a)ᶜ
#align spectrum spectrum

variable {R}

/-- Given an `a : A` where `A` is an `R`-algebra, the *resolvent* is
    a map `R → A` which sends `r : R` to `(algebraMap R A r - a)⁻¹` when
    `r ∈ resolvent R A` and `0` when `r ∈ spectrum R A`. -/
noncomputable def resolvent (a : A) (r : R) : A :=
  Ring.inverse (↑ₐ r - a)
#align resolvent resolvent

/-- The unit `1 - r⁻¹ • a` constructed from `r • 1 - a` when the latter is a unit. -/
@[simps]
noncomputable def IsUnit.subInvSMul {r : Rˣ} {s : R} {a : A} (h : IsUnit <| r • ↑ₐ s - a) : Aˣ where
  val := ↑ₐ s - r⁻¹ • a
  inv := r • ↑h.unit⁻¹
  val_inv := by rw [mul_smul_comm, ← smul_mul_assoc, smul_sub, smul_inv_smul, h.mul_val_inv]
                -- 🎉 no goals
  inv_val := by rw [smul_mul_assoc, ← mul_smul_comm, smul_sub, smul_inv_smul, h.val_inv_mul]
                -- 🎉 no goals
#align is_unit.sub_inv_smul IsUnit.subInvSMul
#align is_unit.coe_sub_inv_smul IsUnit.val_subInvSMul
#align is_unit.coe_inv_sub_inv_smul IsUnit.val_inv_subInvSMul

end Defs

namespace spectrum

section ScalarSemiring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

theorem mem_iff {r : R} {a : A} : r ∈ σ a ↔ ¬IsUnit (↑ₐ r - a) :=
  Iff.rfl
#align spectrum.mem_iff spectrum.mem_iff

theorem not_mem_iff {r : R} {a : A} : r ∉ σ a ↔ IsUnit (↑ₐ r - a) := by
  apply not_iff_not.mp
  -- ⊢ ¬¬r ∈ σ a ↔ ¬IsUnit (↑↑ₐ r - a)
  simp [Set.not_not_mem, mem_iff]
  -- 🎉 no goals
#align spectrum.not_mem_iff spectrum.not_mem_iff

variable (R)

theorem zero_mem_iff {a : A} : (0 : R) ∈ σ a ↔ ¬IsUnit a := by
  rw [mem_iff, map_zero, zero_sub, IsUnit.neg_iff]
  -- 🎉 no goals
#align spectrum.zero_mem_iff spectrum.zero_mem_iff

theorem zero_not_mem_iff {a : A} : (0 : R) ∉ σ a ↔ IsUnit a := by
  rw [zero_mem_iff, Classical.not_not]
  -- 🎉 no goals
#align spectrum.zero_not_mem_iff spectrum.zero_not_mem_iff

variable {R}

theorem mem_resolventSet_of_left_right_inverse {r : R} {a b c : A} (h₁ : (↑ₐ r - a) * b = 1)
    (h₂ : c * (↑ₐ r - a) = 1) : r ∈ resolventSet R a :=
  Units.isUnit ⟨↑ₐ r - a, b, h₁, by rwa [← left_inv_eq_right_inv h₂ h₁]⟩
                                    -- 🎉 no goals
#align spectrum.mem_resolvent_set_of_left_right_inverse spectrum.mem_resolventSet_of_left_right_inverse

theorem mem_resolventSet_iff {r : R} {a : A} : r ∈ resolventSet R a ↔ IsUnit (↑ₐ r - a) :=
  Iff.rfl
#align spectrum.mem_resolvent_set_iff spectrum.mem_resolventSet_iff

@[simp]
theorem resolventSet_of_subsingleton [Subsingleton A] (a : A) : resolventSet R a = Set.univ := by
  simp_rw [resolventSet, Subsingleton.elim (algebraMap R A _ - a) 1, isUnit_one, Set.setOf_true]
  -- 🎉 no goals
#align spectrum.resolvent_set_of_subsingleton spectrum.resolventSet_of_subsingleton

@[simp]
theorem of_subsingleton [Subsingleton A] (a : A) : spectrum R a = ∅ := by
  rw [spectrum, resolventSet_of_subsingleton, Set.compl_univ]
  -- 🎉 no goals
#align spectrum.of_subsingleton spectrum.of_subsingleton

theorem resolvent_eq {a : A} {r : R} (h : r ∈ resolventSet R a) : resolvent a r = ↑h.unit⁻¹ :=
  Ring.inverse_unit h.unit
#align spectrum.resolvent_eq spectrum.resolvent_eq

theorem units_smul_resolvent {r : Rˣ} {s : R} {a : A} :
    r • resolvent a (s : R) = resolvent (r⁻¹ • a) (r⁻¹ • s : R) := by
  by_cases h : s ∈ spectrum R a
  -- ⊢ r • resolvent a s = resolvent (r⁻¹ • a) (r⁻¹ • s)
  · rw [mem_iff] at h
    -- ⊢ r • resolvent a s = resolvent (r⁻¹ • a) (r⁻¹ • s)
    simp only [resolvent, Algebra.algebraMap_eq_smul_one] at *
    -- ⊢ r • Ring.inverse (s • 1 - a) = Ring.inverse ((r⁻¹ • s) • 1 - r⁻¹ • a)
    rw [smul_assoc, ← smul_sub]
    -- ⊢ r • Ring.inverse (s • 1 - a) = Ring.inverse (r⁻¹ • (s • 1 - a))
    have h' : ¬IsUnit (r⁻¹ • (s • (1 : A) - a)) := fun hu =>
      h (by simpa only [smul_inv_smul] using IsUnit.smul r hu)
    simp only [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', smul_zero]
    -- 🎉 no goals
  · simp only [resolvent]
    -- ⊢ r • Ring.inverse (↑↑ₐ s - a) = Ring.inverse (↑↑ₐ (r⁻¹ • s) - r⁻¹ • a)
    have h' : IsUnit (r • algebraMap R A (r⁻¹ • s) - a) := by
      simpa [Algebra.algebraMap_eq_smul_one, smul_assoc] using not_mem_iff.mp h
    rw [← h'.val_subInvSMul, ← (not_mem_iff.mp h).unit_spec, Ring.inverse_unit, Ring.inverse_unit,
      h'.val_inv_subInvSMul]
    simp only [Algebra.algebraMap_eq_smul_one, smul_assoc, smul_inv_smul]
    -- 🎉 no goals
#align spectrum.units_smul_resolvent spectrum.units_smul_resolvent

theorem units_smul_resolvent_self {r : Rˣ} {a : A} :
    r • resolvent a (r : R) = resolvent (r⁻¹ • a) (1 : R) := by
  simpa only [Units.smul_def, Algebra.id.smul_eq_mul, Units.inv_mul] using
    @units_smul_resolvent _ _ _ _ _ r r a
#align spectrum.units_smul_resolvent_self spectrum.units_smul_resolvent_self

/-- The resolvent is a unit when the argument is in the resolvent set. -/
theorem isUnit_resolvent {r : R} {a : A} : r ∈ resolventSet R a ↔ IsUnit (resolvent a r) :=
  isUnit_ring_inverse.symm
#align spectrum.is_unit_resolvent spectrum.isUnit_resolvent

theorem inv_mem_resolventSet {r : Rˣ} {a : Aˣ} (h : (r : R) ∈ resolventSet R (a : A)) :
    (↑r⁻¹ : R) ∈ resolventSet R (↑a⁻¹ : A) := by
  rw [mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, ← Units.smul_def] at h ⊢
  -- ⊢ IsUnit (r⁻¹ • 1 - ↑a⁻¹)
  rw [IsUnit.smul_sub_iff_sub_inv_smul, inv_inv, IsUnit.sub_iff]
  -- ⊢ IsUnit (r • ↑a⁻¹ - 1)
  have h₁ : (a : A) * (r • (↑a⁻¹ : A) - 1) = r • (1 : A) - a := by
    rw [mul_sub, mul_smul_comm, a.mul_inv, mul_one]
  have h₂ : (r • (↑a⁻¹ : A) - 1) * a = r • (1 : A) - a := by
    rw [sub_mul, smul_mul_assoc, a.inv_mul, one_mul]
  have hcomm : Commute (a : A) (r • (↑a⁻¹ : A) - 1) := by rwa [← h₂] at h₁
  -- ⊢ IsUnit (r • ↑a⁻¹ - 1)
  exact (hcomm.isUnit_mul_iff.mp (h₁.symm ▸ h)).2
  -- 🎉 no goals
#align spectrum.inv_mem_resolvent_set spectrum.inv_mem_resolventSet

theorem inv_mem_iff {r : Rˣ} {a : Aˣ} : (r : R) ∈ σ (a : A) ↔ (↑r⁻¹ : R) ∈ σ (↑a⁻¹ : A) :=
  not_iff_not.2 <| ⟨inv_mem_resolventSet, inv_mem_resolventSet⟩
#align spectrum.inv_mem_iff spectrum.inv_mem_iff

theorem zero_mem_resolventSet_of_unit (a : Aˣ) : 0 ∈ resolventSet R (a : A) := by
  simpa only [mem_resolventSet_iff, ← not_mem_iff, zero_not_mem_iff] using a.isUnit
  -- 🎉 no goals
#align spectrum.zero_mem_resolvent_set_of_unit spectrum.zero_mem_resolventSet_of_unit

theorem ne_zero_of_mem_of_unit {a : Aˣ} {r : R} (hr : r ∈ σ (a : A)) : r ≠ 0 := fun hn =>
  (hn ▸ hr) (zero_mem_resolventSet_of_unit a)
#align spectrum.ne_zero_of_mem_of_unit spectrum.ne_zero_of_mem_of_unit

theorem add_mem_iff {a : A} {r s : R} : r + s ∈ σ a ↔ r ∈ σ (-↑ₐ s + a) := by
  simp only [mem_iff, sub_neg_eq_add, ← sub_sub, map_add]
  -- 🎉 no goals
#align spectrum.add_mem_iff spectrum.add_mem_iff

theorem add_mem_add_iff {a : A} {r s : R} : r + s ∈ σ (↑ₐ s + a) ↔ r ∈ σ a := by
  rw [add_mem_iff, neg_add_cancel_left]
  -- 🎉 no goals
#align spectrum.add_mem_add_iff spectrum.add_mem_add_iff

theorem smul_mem_smul_iff {a : A} {s : R} {r : Rˣ} : r • s ∈ σ (r • a) ↔ s ∈ σ a := by
  simp only [mem_iff, not_iff_not, Algebra.algebraMap_eq_smul_one, smul_assoc, ← smul_sub,
    isUnit_smul_iff]
#align spectrum.smul_mem_smul_iff spectrum.smul_mem_smul_iff

theorem unit_smul_eq_smul (a : A) (r : Rˣ) : σ (r • a) = r • σ a := by
  ext x
  -- ⊢ x ∈ σ (r • a) ↔ x ∈ r • σ a
  have x_eq : x = r • r⁻¹ • x := by simp
  -- ⊢ x ∈ σ (r • a) ↔ x ∈ r • σ a
  nth_rw 1 [x_eq]
  -- ⊢ r • r⁻¹ • x ∈ σ (r • a) ↔ x ∈ r • σ a
  rw [smul_mem_smul_iff]
  -- ⊢ r⁻¹ • x ∈ σ a ↔ x ∈ r • σ a
  constructor
  -- ⊢ r⁻¹ • x ∈ σ a → x ∈ r • σ a
  · exact fun h => ⟨r⁻¹ • x, ⟨h, show r • r⁻¹ • x = x by simp⟩⟩
    -- 🎉 no goals
  · rintro ⟨w, _, (x'_eq : r • w = x)⟩
    -- ⊢ r⁻¹ • x ∈ σ a
    simpa [← x'_eq ]
    -- 🎉 no goals
#align spectrum.unit_smul_eq_smul spectrum.unit_smul_eq_smul

-- `r ∈ σ(a*b) ↔ r ∈ σ(b*a)` for any `r : Rˣ`
theorem unit_mem_mul_iff_mem_swap_mul {a b : A} {r : Rˣ} : ↑r ∈ σ (a * b) ↔ ↑r ∈ σ (b * a) := by
  have h₁ : ∀ x y : A, IsUnit (1 - x * y) → IsUnit (1 - y * x) := by
    refine' fun x y h => ⟨⟨1 - y * x, 1 + y * h.unit.inv * x, _, _⟩, rfl⟩
    calc
      (1 - y * x) * (1 + y * (IsUnit.unit h).inv * x) =
          1 - y * x + y * ((1 - x * y) * h.unit.inv) * x :=
        by noncomm_ring
      _ = 1 := by simp only [Units.inv_eq_val_inv, IsUnit.mul_val_inv, mul_one, sub_add_cancel]
    calc
      (1 + y * (IsUnit.unit h).inv * x) * (1 - y * x) =
          1 - y * x + y * (h.unit.inv * (1 - x * y)) * x :=
        by noncomm_ring
      _ = 1 := by simp only [Units.inv_eq_val_inv, IsUnit.val_inv_mul, mul_one, sub_add_cancel]
  have := Iff.intro (h₁ (r⁻¹ • a) b) (h₁ b (r⁻¹ • a))
  -- ⊢ ↑r ∈ σ (a * b) ↔ ↑r ∈ σ (b * a)
  rw [mul_smul_comm r⁻¹ b a] at this
  -- ⊢ ↑r ∈ σ (a * b) ↔ ↑r ∈ σ (b * a)
  simpa only [mem_iff, not_iff_not, Algebra.algebraMap_eq_smul_one, ← Units.smul_def,
    IsUnit.smul_sub_iff_sub_inv_smul, smul_mul_assoc]
#align spectrum.unit_mem_mul_iff_mem_swap_mul spectrum.unit_mem_mul_iff_mem_swap_mul

theorem preimage_units_mul_eq_swap_mul {a b : A} :
    ((↑) : Rˣ → R) ⁻¹' σ (a * b) = (↑) ⁻¹' σ (b * a) :=
  Set.ext fun _ => unit_mem_mul_iff_mem_swap_mul
#align spectrum.preimage_units_mul_eq_swap_mul spectrum.preimage_units_mul_eq_swap_mul

section Star

variable [InvolutiveStar R] [StarRing A] [StarModule R A]

theorem star_mem_resolventSet_iff {r : R} {a : A} :
    star r ∈ resolventSet R a ↔ r ∈ resolventSet R (star a) := by
  refine' ⟨fun h => _, fun h => _⟩ <;>
  -- ⊢ r ∈ resolventSet R (star a)
    simpa only [mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, star_sub, star_smul,
      star_star, star_one] using IsUnit.star h
#align spectrum.star_mem_resolvent_set_iff spectrum.star_mem_resolventSet_iff

protected theorem map_star (a : A) : σ (star a) = star (σ a) := by
  ext
  -- ⊢ x✝ ∈ σ (star a) ↔ x✝ ∈ star (σ a)
  simpa only [Set.mem_star, mem_iff, not_iff_not] using star_mem_resolventSet_iff.symm
  -- 🎉 no goals
#align spectrum.map_star spectrum.map_star

end Star

end ScalarSemiring

section ScalarRing

variable {R : Type u} {A : Type v}

variable [CommRing R] [Ring A] [Algebra R A]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

-- it would be nice to state this for `subalgebra_class`, but we don't have such a thing yet
theorem subset_subalgebra {S : Subalgebra R A} (a : S) : spectrum R (a : A) ⊆ spectrum R a :=
  compl_subset_compl.2 fun _ => IsUnit.map S.val
#align spectrum.subset_subalgebra spectrum.subset_subalgebra

-- this is why it would be nice if `subset_subalgebra` was registered for `subalgebra_class`.
theorem subset_starSubalgebra [StarRing R] [StarRing A] [StarModule R A] {S : StarSubalgebra R A}
    (a : S) : spectrum R (a : A) ⊆ spectrum R a :=
  compl_subset_compl.2 fun _ => IsUnit.map S.subtype
#align spectrum.subset_star_subalgebra spectrum.subset_starSubalgebra

theorem singleton_add_eq (a : A) (r : R) : {r} + σ a = σ (↑ₐ r + a) :=
  ext fun x => by
    rw [singleton_add, image_add_left, mem_preimage]
    -- ⊢ (fun x x_1 => x + x_1) (-r) x ∈ σ a ↔ x ∈ σ (↑↑ₐ r + a)
    simp only
    -- ⊢ -r + x ∈ σ a ↔ x ∈ σ (↑↑ₐ r + a)
    rw [add_comm, add_mem_iff, map_neg, neg_neg]
    -- 🎉 no goals
#align spectrum.singleton_add_eq spectrum.singleton_add_eq

theorem add_singleton_eq (a : A) (r : R) : σ a + {r} = σ (a + ↑ₐ r) :=
  add_comm {r} (σ a) ▸ add_comm (algebraMap R A r) a ▸ singleton_add_eq a r
#align spectrum.add_singleton_eq spectrum.add_singleton_eq

theorem vadd_eq (a : A) (r : R) : r +ᵥ σ a = σ (↑ₐ r + a) :=
  singleton_add.symm.trans <| singleton_add_eq a r
#align spectrum.vadd_eq spectrum.vadd_eq

theorem neg_eq (a : A) : -σ a = σ (-a) :=
  Set.ext fun x => by
    simp only [mem_neg, mem_iff, map_neg, ← neg_add', IsUnit.neg_iff, sub_neg_eq_add]
    -- 🎉 no goals
#align spectrum.neg_eq spectrum.neg_eq

theorem singleton_sub_eq (a : A) (r : R) : {r} - σ a = σ (↑ₐ r - a) := by
  rw [sub_eq_add_neg, neg_eq, singleton_add_eq, sub_eq_add_neg]
  -- 🎉 no goals
#align spectrum.singleton_sub_eq spectrum.singleton_sub_eq

theorem sub_singleton_eq (a : A) (r : R) : σ a - {r} = σ (a - ↑ₐ r) := by
  simpa only [neg_sub, neg_eq] using congr_arg Neg.neg (singleton_sub_eq a r)
  -- 🎉 no goals
#align spectrum.sub_singleton_eq spectrum.sub_singleton_eq

end ScalarRing

section ScalarField

variable {𝕜 : Type u} {A : Type v}

variable [Field 𝕜] [Ring A] [Algebra 𝕜 A]

local notation "σ" => spectrum 𝕜

local notation "↑ₐ" => algebraMap 𝕜 A

/-- Without the assumption `Nontrivial A`, then `0 : A` would be invertible. -/
@[simp]
theorem zero_eq [Nontrivial A] : σ (0 : A) = {0} := by
  refine' Set.Subset.antisymm _ (by simp [Algebra.algebraMap_eq_smul_one, mem_iff])
  -- ⊢ σ 0 ⊆ {0}
  rw [spectrum, Set.compl_subset_comm]
  -- ⊢ {0}ᶜ ⊆ resolventSet 𝕜 0
  intro k hk
  -- ⊢ k ∈ resolventSet 𝕜 0
  rw [Set.mem_compl_singleton_iff] at hk
  -- ⊢ k ∈ resolventSet 𝕜 0
  have : IsUnit (Units.mk0 k hk • (1 : A)) := IsUnit.smul (Units.mk0 k hk) isUnit_one
  -- ⊢ k ∈ resolventSet 𝕜 0
  simpa [mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one]
  -- 🎉 no goals
#align spectrum.zero_eq spectrum.zero_eq

@[simp]
theorem scalar_eq [Nontrivial A] (k : 𝕜) : σ (↑ₐ k) = {k} := by
  rw [← add_zero (↑ₐ k), ← singleton_add_eq, zero_eq, Set.singleton_add_singleton, add_zero]
  -- 🎉 no goals
#align spectrum.scalar_eq spectrum.scalar_eq

@[simp]
theorem one_eq [Nontrivial A] : σ (1 : A) = {1} :=
  calc
    σ (1 : A) = σ (↑ₐ 1) := by rw [Algebra.algebraMap_eq_smul_one, one_smul]
                               -- 🎉 no goals
    _ = {1} := scalar_eq 1

#align spectrum.one_eq spectrum.one_eq

/-- the assumption `(σ a).Nonempty` is necessary and cannot be removed without
further conditions on the algebra `A` and scalar field `𝕜`. -/
theorem smul_eq_smul [Nontrivial A] (k : 𝕜) (a : A) (ha : (σ a).Nonempty) :
    σ (k • a) = k • σ a := by
  rcases eq_or_ne k 0 with (rfl | h)
  -- ⊢ σ (0 • a) = 0 • σ a
  · simpa [ha, zero_smul_set] using (show {(0 : 𝕜)} = (0 : Set 𝕜) from rfl)
    -- 🎉 no goals
  · exact unit_smul_eq_smul a (Units.mk0 k h)
    -- 🎉 no goals
#align spectrum.smul_eq_smul spectrum.smul_eq_smul

theorem nonzero_mul_eq_swap_mul (a b : A) : σ (a * b) \ {0} = σ (b * a) \ {0} := by
  suffices h : ∀ x y : A, σ (x * y) \ {0} ⊆ σ (y * x) \ {0}
  -- ⊢ σ (a * b) \ {0} = σ (b * a) \ {0}
  · exact Set.eq_of_subset_of_subset (h a b) (h b a)
    -- 🎉 no goals
  · rintro _ _ k ⟨k_mem, k_neq⟩
    -- ⊢ k ∈ σ (y✝ * x✝) \ {0}
    change ((Units.mk0 k k_neq) : 𝕜) ∈ _ at k_mem
    -- ⊢ k ∈ σ (y✝ * x✝) \ {0}
    exact ⟨unit_mem_mul_iff_mem_swap_mul.mp k_mem, k_neq⟩
    -- 🎉 no goals
#align spectrum.nonzero_mul_eq_swap_mul spectrum.nonzero_mul_eq_swap_mul

protected theorem map_inv (a : Aˣ) : (σ (a : A))⁻¹ = σ (↑a⁻¹ : A) := by
  refine' Set.eq_of_subset_of_subset (fun k hk => _) fun k hk => _
  -- ⊢ k ∈ σ ↑a⁻¹
  · rw [Set.mem_inv] at hk
    -- ⊢ k ∈ σ ↑a⁻¹
    have : k ≠ 0 := by simpa only [inv_inv] using inv_ne_zero (ne_zero_of_mem_of_unit hk)
    -- ⊢ k ∈ σ ↑a⁻¹
    lift k to 𝕜ˣ using isUnit_iff_ne_zero.mpr this
    -- ⊢ ↑k ∈ σ ↑a⁻¹
    rw [← Units.val_inv_eq_inv_val k] at hk
    -- ⊢ ↑k ∈ σ ↑a⁻¹
    exact inv_mem_iff.mp hk
    -- 🎉 no goals
  · lift k to 𝕜ˣ using isUnit_iff_ne_zero.mpr (ne_zero_of_mem_of_unit hk)
    -- ⊢ ↑k ∈ (σ ↑a)⁻¹
    simpa only [Units.val_inv_eq_inv_val] using inv_mem_iff.mp hk
    -- 🎉 no goals
#align spectrum.map_inv spectrum.map_inv

end ScalarField

end spectrum

namespace AlgHom

section CommSemiring

variable {F R A B : Type*} [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

variable [AlgHomClass F R A B]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

theorem mem_resolventSet_apply (φ : F) {a : A} {r : R} (h : r ∈ resolventSet R a) :
    r ∈ resolventSet R ((φ : A → B) a) := by
  simpa only [map_sub, AlgHomClass.commutes] using h.map φ
  -- 🎉 no goals
#align alg_hom.mem_resolvent_set_apply AlgHom.mem_resolventSet_apply

theorem spectrum_apply_subset (φ : F) (a : A) : σ ((φ : A → B) a) ⊆ σ a := fun _ =>
  mt (mem_resolventSet_apply φ)
#align alg_hom.spectrum_apply_subset AlgHom.spectrum_apply_subset

end CommSemiring

section CommRing

variable {F R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

variable [AlgHomClass F R A R]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

theorem apply_mem_spectrum [Nontrivial R] (φ : F) (a : A) : φ a ∈ σ a := by
  have h : ↑ₐ (φ a) - a ∈ RingHom.ker (φ : A →+* R) := by
    simp only [RingHom.mem_ker, map_sub, RingHom.coe_coe, AlgHomClass.commutes,
      Algebra.id.map_eq_id, RingHom.id_apply, sub_self]
  simp only [spectrum.mem_iff, ← mem_nonunits_iff,
    coe_subset_nonunits (RingHom.ker_ne_top (φ : A →+* R)) h]
#align alg_hom.apply_mem_spectrum AlgHom.apply_mem_spectrum

end CommRing

end AlgHom

@[simp]
theorem AlgEquiv.spectrum_eq {F R A B : Type*} [CommSemiring R] [Ring A] [Ring B] [Algebra R A]
    [Algebra R B] [AlgEquivClass F R A B] (f : F) (a : A) :
    spectrum R (f a) = spectrum R a :=
  Set.Subset.antisymm (AlgHom.spectrum_apply_subset _ _) <| by
    simpa only [AlgEquiv.coe_algHom, AlgEquiv.coe_coe_symm_apply_coe_apply] using
      AlgHom.spectrum_apply_subset (f : A ≃ₐ[R] B).symm (f a)
