/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.Algebra.Module.LinearMap
import Mathlib.RingTheory.HahnSeries
import Mathlib.Algebra.Vertex.Defs

/-!
# Basic results on Vertex algebras

In this file we prove some basic results about vertex algebras.

## Main results

* Associativity is equivalent to a special case of the Borcherds identity.
* The commutator formula is equivalent to a special case of the Borcherds identity.

## To do

In the non-unital setting:
* Locality is equivalent to a special case of the Borcherds identity.
* Weak associativity is equivalent to a special case of the Borcherds identity.
* Borcherds identity from (commutator or locality) and (associativity or weak associativity)

In the unital setting:
* Skew-symmetry is equivalent to a special case of the Borcherds identity.
* Hasse-Schmidt differential
* creative fields?
* reconstruction?

## References

G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328
Matsuo-Nagatomo?
Borcherds's original paper?

-/
universe u v

variable {V : Type u} {R : Type v}

namespace VertexAlg

section NonUnital

variable [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]

lemma toNat_sub_eq_zero_leq {m n : ℤ} (h : Int.toNat (-m - n) = 0) : -n ≤ m := by
   rw [← @sub_nonpos, neg_sub_left, neg_add']
   exact Int.toNat_eq_zero.mp h

theorem associativity_left (a b c : V) (s t : ℤ) : Borcherds_sum_1 R a b c 0 s t =
    index (Y R (index (Y R a) t b)) s c := by
  unfold Borcherds_sum_1
  cases h : (Int.toNat (-t - order R a b)) with
    | zero =>
      rw [Finset.range_zero, Finset.sum_empty]
      rw [index_zero_if_neg_order_leq a b t (toNat_sub_eq_zero_leq h), LinearMap.map_zero,
        VertexAlg.zero_index, LinearMap.zero_apply]
    | succ n =>
      rw [Finset.eventually_constant_sum ?_ (Nat.one_le_iff_ne_zero.mpr
        (Nat.succ_ne_zero n)), Finset.sum_range_one, zero_add, Ring.choose_zero_right, one_smul,
        Nat.cast_zero, add_zero, sub_zero]
      intro i hi
      rw [Ring.choose_zero_pos i (Nat.ne_zero_iff_zero_lt.mp <| Nat.one_le_iff_ne_zero.mp <| hi),
          zero_smul]

theorem associativity_right (a b c : V) (s t : ℤ) : Borcherds_sum_2 R a b c 0 s t +
    Borcherds_sum_3 R a b c 0 s t = Finset.sum (Finset.range (Int.toNat (-s - order R b c)))
    (fun i ↦ (-1)^i • (Ring.choose (t : ℤ) i) • index (Y R a) (t-i) (index (Y R b) (s+i) c)) +
    Finset.sum (Finset.range (Int.toNat (- order R a c))) (fun i ↦ (-1: ℤˣ)^(t+i+1) •
    (Ring.choose t i) • index (Y R b) (s+t-i) (index (Y R a) i c)) := by
  unfold Borcherds_sum_2 Borcherds_sum_3
  simp only [neg_zero, zero_sub, zero_add]

theorem Borcherds_id_at_zero_iff_associativity (a b c : V) (s t : ℤ) :
    Borcherds_id R a b c 0 s t ↔ associativity R a b c s t := by
  unfold Borcherds_id
  rw [associativity_left, associativity_right]
  exact Eq.congr rfl rfl

theorem commutator_right_2 (a b c : V) (r s : ℤ) : Borcherds_sum_2 R a b c r s 0 =
    index (Y R a) r (index (Y R b) s c) := by
  unfold Borcherds_sum_2
  cases h : (Int.toNat (-s - order R b c)) with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty]
    rw [index_zero_if_neg_order_leq b c s (toNat_sub_eq_zero_leq h), LinearMap.map_zero]
  | succ n =>
    rw [Finset.eventually_constant_sum ?_ (Nat.one_le_iff_ne_zero.mpr
        (Nat.succ_ne_zero n)), Finset.sum_range_one, add_zero, Ring.choose_zero_right, one_smul,
        Nat.cast_zero, add_zero, sub_zero, pow_zero, one_smul]
    intro i hi
    rw [Ring.choose_zero_pos i (Nat.ne_zero_iff_zero_lt.mp <| Nat.one_le_iff_ne_zero.mp <| hi),
      zero_smul, smul_zero]

theorem commutator_right_3 (a b c : V) (r s : ℤ) : Borcherds_sum_3 R a b c r s 0 =
    -index (Y R b) s (index (Y R a) r c) := by
  unfold Borcherds_sum_3
  cases h : (Int.toNat (-r - order R a c)) with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty]
    rw [index_zero_if_neg_order_leq a c r (toNat_sub_eq_zero_leq h), LinearMap.map_zero, neg_zero]
  | succ n =>
    rw [Finset.eventually_constant_sum ?_ (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)),
        Finset.sum_range_one, add_zero, Ring.choose_zero_right, one_smul, Nat.cast_zero, add_zero,
        sub_zero, zero_add, add_zero, zpow_one, Units.neg_smul, one_smul]
    intro i hi
    rw [Ring.choose_zero_pos i (Nat.ne_zero_iff_zero_lt.mp <| Nat.one_le_iff_ne_zero.mp <| hi),
        zero_smul, smul_zero]

theorem Borcherds_id_at_zero_iff_commutator_formula (a b c : V) (r s : ℤ) :
    Borcherds_id R a b c r s 0 ↔ commutator_formula R a b c r s := by
  unfold Borcherds_id commutator_formula Borcherds_sum_1
  rw [commutator_right_2, commutator_right_3, ← sub_eq_add_neg, neg_zero, zero_sub]
  simp_rw [zero_add]
  exact eq_comm

theorem locality_left (a b c : V) (r s t : ℤ) (h : - order R a b ≤ t) :
    Borcherds_sum_1 R a b c r s t = 0 := by
  unfold Borcherds_sum_1
  have hrange : Int.toNat (-t - order R a b) = 0 := by
    rw [Int.toNat_eq_zero, tsub_le_iff_right, zero_add, neg_le]
    exact h
  rw [hrange, Finset.range_zero, Finset.sum_empty]

theorem Borcherds_id_at_large_t_iff_locality (a b c : V) (r s t : ℤ) (h : - order R a b ≤ t) :
    Borcherds_id R a b c r s t ↔ locality R a b c r s t := by
  unfold Borcherds_id locality
  rw [locality_left a b c r s t h]
  exact eq_comm

theorem weak_assoc_right (a b c : V) (r s t: ℤ) (h : r ≥ - order R a c) :
    Borcherds_sum_3 R a b c r s t = 0 := by
  unfold Borcherds_sum_3
  have hrange : Int.toNat (-r - order R a c) = 0 := by
    rw [Int.toNat_eq_zero, tsub_le_iff_right, zero_add, neg_le]
    exact h
  rw [hrange, Finset.range_zero, Finset.sum_empty]

theorem Borcherds_id_at_large_r_iff_weak_assoc (a b c : V) (r s t: ℤ) (h : r ≥ - order R a c) :
    Borcherds_id R a b c r s t ↔ weak_associativity R a b c r s t := by
  unfold Borcherds_id weak_associativity
  rw [weak_assoc_right a b c r s t h, add_zero]

theorem toNat_eq_sub_toNat_add (t : ℤ) (n : ℕ) (h : Int.toNat t = Nat.succ n) :
    Int.toNat t = Int.toNat (t - 1) + 1 := by
  rw [Int.pred_toNat, h, Nat.succ_sub_succ_eq_sub, tsub_zero]

theorem toNat_neg_sub_eq_zero (x y : ℤ) (h : Int.toNat (-x - y) = Nat.zero) :
    Int.toNat (-(x + 1) - y) = 0 := by
  rw [Int.toNat_eq_zero] at h
  rw [Int.toNat_eq_zero]
  linarith

theorem toNat_neg_succ_sub_eq_Nat (x y : ℤ) (n : ℕ) (h : Int.toNat (-x - y) = n.succ) :
    Int.toNat (-(x + 1) - y) = n := by
  rw [toNat_eq_sub_toNat_add _ n h, ← Nat.add_one, Nat.add_right_cancel_iff] at h
  rw [neg_add', sub_right_comm]
  exact h

theorem borcherds1Recursion [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]
    (a b c : V) (r s t : ℤ) : Borcherds_sum_1 R a b c (r + 1) s t =
    Borcherds_sum_1 R a b c r (s + 1) t + Borcherds_sum_1 R a b c r s (t + 1) := by
  unfold Borcherds_sum_1
  cases h : (Int.toNat (-t - order R a b)) with
  | zero =>
    simp only [toNat_neg_sub_eq_zero t _ h, Finset.range_zero, Finset.sum_empty, zero_add]
  | succ n =>
    simp_rw [Finset.sum_range_succ', Nat.add_one, Ring.choose_succ_succ, add_smul]
    rw [Finset.sum_add_distrib, add_assoc, add_comm]
    refine Mathlib.Tactic.LinearCombination.add_pf ?_ ?_
    refine Mathlib.Tactic.LinearCombination.add_pf ?_ ?_
    rw [add_comm s 1, add_assoc r 1 s] -- end first sum
    simp only [Ring.choose_zero_right, add_comm s 1, add_assoc r 1 s] -- end second sum
    rw [← toNat_neg_succ_sub_eq_Nat _ _ _ h]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [← Nat.add_one, Nat.cast_add, sub_add_eq_sub_sub_swap, add_assoc t, add_comm 1, Nat.cast_one,
      add_sub_right_comm, Int.add_sub_cancel] -- end third sum

theorem borcherds2Recursion [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]
    (a b c : V) (r s t : ℤ) : Borcherds_sum_2 R a b c (r + 1) s t =
    Borcherds_sum_2 R a b c r (s + 1) t + Borcherds_sum_2 R a b c r s (t + 1) := by
  unfold Borcherds_sum_2
  cases h : (Int.toNat (-s - order R b c)) with
    | zero =>
      simp only [toNat_neg_sub_eq_zero s _ h, Finset.range_zero, Finset.sum_empty, zero_add]
    | succ n =>
      simp_rw [Finset.sum_range_succ', Nat.add_one, Ring.choose_succ_succ, add_smul, smul_add]
      rw [Finset.sum_add_distrib, ← add_assoc]
      refine Mathlib.Tactic.LinearCombination.add_pf ?_ ?_
      refine eq_add_of_sub_eq' ?_
      rw [sub_eq_neg_add]
      refine Mathlib.Tactic.LinearCombination.add_pf ?_ ?_
      rw [← Finset.sum_neg_distrib]
      rw [← toNat_neg_succ_sub_eq_Nat _ _ _ h]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [Nat.cast_succ, smul_algebra_smul_comm, smul_algebra_smul_comm,
        ← neg_smul, ← Nat.add_one k, add_comm k 1, pow_add, pow_one, neg_one_mul]
      have h₂ : r + (t + 1) - (k + 1) = r + t - k := by linarith
      rw [h₂, add_assoc, add_comm 1 _] -- end first sum
      rw [add_assoc, add_comm 1 t] --end second sum
      rw [Ring.choose_zero_right, Ring.choose_zero_right, add_assoc, add_comm 1 t] -- end third sum

theorem borcherds3Recursion [CommRing R] [AddCommGroup V] [NonAssocNonUnitalVertexAlgebra R V]
    (a b c : V) (r s t : ℤ) : Borcherds_sum_3 R a b c (r + 1) s t =
    Borcherds_sum_3 R a b c r (s + 1) t + Borcherds_sum_3 R a b c r s (t + 1) := by
  unfold Borcherds_sum_3
  cases h : (Int.toNat (-r - order R a c)) with
    | zero =>
      simp only [toNat_neg_sub_eq_zero r _ h, Finset.range_zero, Finset.sum_empty, zero_add]
    | succ n =>
      rw [add_assoc]
      refine eq_add_of_sub_eq' ?_
      simp_rw [Finset.sum_range_succ', Nat.add_one, Ring.choose_succ_succ, add_smul, smul_add]
      rw [Finset.sum_add_distrib, sub_eq_add_neg, neg_add, neg_add, add_assoc, add_assoc]
      refine Mathlib.Tactic.LinearCombination.add_pf ?_ ?_
      rw [← neg_add, toNat_neg_succ_sub_eq_Nat _ _ _ h]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Nat.add_one, Nat.cast_add, Nat.cast_one, show (-1:ℤˣ)^(t + 1 + (i + 1) + 1) =
        (-1)^(t + i + 1) by simp only [zpow_add, zpow_one, mul_neg, mul_one, zpow_coe_nat, neg_mul,
        neg_neg], show r + 1 + i =r + (i + 1) by linarith,
        show s + (t + 1) - (i + 1) = s + t - i by linarith] -- end first sum
      refine Mathlib.Tactic.LinearCombination.add_pf ?_ ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Nat.add_one, Nat.cast_add, Nat.cast_one, ← Units.neg_smul, neg_eq_neg_one_mul,
        mul_self_zpow, add_comm 1 t, add_right_comm t 1 _] -- end second sum
      rw [← Units.neg_smul, neg_eq_neg_one_mul, mul_self_zpow, add_comm 1 t]
      simp only [Ring.choose_zero_right, Nat.cast_zero, add_zero, zero_add] -- end third sum

-- theorem Borcherds on r s+1 t, r s t+1 implies r+1 s t (and two other versions)

-- theorem Borcherds_on_hyperplane_implies_half_space (and two other versions)

-- theorem Borcherds_on_two_half_spaces_implies Borcherds_everywhere
  -- For fixed r s t, find propagation length to union of half-spaces?
  -- Or, use induction on ℕ × ℕ


--theorem te (t : ℤ) (i : ℕ) : -1 * (-1) ^ (t + (i + 1) + 1) = (-1:ℤˣ) ^ (t + 1 + (i + 1) + 1) := by


end NonUnital

section Unital

/-!

theorem vacuum_derivative_is_zero [AddCommGroup V] [UnboundedVertexMul V] [NonunitalVertexRing V] :
    T 1 1 = 0 := by

--  refine NonunitalVertexRing.borcherds_id vac vac vac -1 -1 -1
-- set u=v=w = vac, r=s=t=-1 to get
  vac_{-2}vac = vac_{-2}(vac_{-1}vac) + vac_{-2}(vac_{-1}vac) = 2vac_{-2}vac

-- theorem vacuum_products_vanish : Y n vac vac = 0 when n ≠-1: for n ≥ 0, this is from van_vac.
For n < -1, we use induction: u=v=w=vac, r=s = -1, t=n.

-- theorem left identity : Y n vac u = u if n = -1, and 0 if not := Borcherds with v = w = vac,
r = -1, t = 0.
-- theorem unit_left (R : Type v) [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra R V] (a : V) :

theorem skew_symmetry_iff_Borcherds_at_zero



-/
end Unital
