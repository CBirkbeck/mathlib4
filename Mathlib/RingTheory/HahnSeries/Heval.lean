/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Scott Carnahan
-/
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Evaluation of power series in Hahn Series
We describe a class of ring homomorphisms from formal power series to Hahn series, given by
substitution of the generating variables to elements of strictly positive order.

## Main Definitions
 * `heval` an `R`-algebra homomorphism from formal power series to Hahn series.

## Main results
  * If `R` is a commutative domain, and `Γ` is a linearly ordered additive commutative group, then
  a Hahn series is a unit if and only if its leading term is a unit in `R`.

## TODO
  * Multivariable version

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/


open Finset Function

open Pointwise

noncomputable section

variable {Γ Γ' R V α β : Type*}

namespace HahnSeries

theorem support_pow_subset_closure [OrderedCancelAddCommMonoid Γ] [Semiring R] (x : HahnSeries Γ R)
    (n : ℕ) : support (x ^ n) ⊆ AddSubmonoid.closure (support x) := by
  induction' n with n ih <;> intro g hn
  · simp only [pow_zero, mem_support, one_coeff, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
    simp only [hn, SetLike.mem_coe]
    exact AddSubmonoid.zero_mem _
  · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support hn
    exact SetLike.mem_coe.2 (AddSubmonoid.add_mem _ (ih hi) (AddSubmonoid.subset_closure hj))

theorem support_smul_pow_subset_closure [OrderedCancelAddCommMonoid Γ] [Semiring R]
    (f : ℕ → R) (x : HahnSeries Γ R) (n : ℕ) :
    (f n • x ^ n).support ⊆ AddSubmonoid.closure x.support :=
  (Function.support_const_smul_subset (f n) (x ^ n).coeff).trans (support_pow_subset_closure x n)

theorem support_prod_subset_add_support [OrderedCancelAddCommMonoid Γ] [CommSemiring R]
    (σ : Type*) (x : σ →₀ HahnSeries Γ R) (s : Finset σ):
    (∏ i ∈ s, (x i)).support ⊆ ∑ i ∈ s, (x i).support := by
  refine Finset.cons_induction ?_ ?_ s
  · rw [prod_empty, sum_empty, ← single_zero_one, ← Set.singleton_zero]
    exact support_single_subset
  · intros _ _ _ his _ hg
    simp_all only [prod_cons, mem_support, ne_eq, sum_cons]
    exact support_mul_subset_add_support.trans (Set.add_subset_add (fun ⦃a⦄ a ↦ a) his) hg

theorem support_MVpow_subset_closure [OrderedCancelAddCommMonoid Γ] [CommSemiring R]
    (σ : Type*) (x : σ →₀ HahnSeries Γ R) (n : σ →₀ ℕ) :
    (∏ i ∈ x.support, (x i) ^ (n i)).support ⊆ AddSubmonoid.closure (⋃ i : σ, (x i).support) := by
  refine Finset.cons_induction ?_ ?_ x.support
  · rw [prod_empty, ← single_zero_one]
    have h₂ : 0 ∈ AddSubmonoid.closure (⋃ i, (x i).support) := by
      exact AddSubmonoid.zero_mem (AddSubmonoid.closure (⋃ i, (x i).support))
    intro g hg
    simp_all
  · intro i _ _ hx
    rw [prod_cons]
    have hi : (x i ^ n i).support ⊆ AddSubmonoid.closure (⋃ i, (x i).support) :=
      (support_pow_subset_closure (x i) (n i)).trans <| AddSubmonoid.closure_mono <|
        Set.subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a
    exact (support_mul_subset_add_support (x := x i ^ n i)).trans (AddSubmonoid.add_subset hi hx)

theorem support_smul_MVpow_subset_closure [OrderedCancelAddCommMonoid Γ] [CommSemiring R]
    (σ : Type*) (f : (σ →₀ ℕ) → R) (x : σ →₀ HahnSeries Γ R) (n : σ →₀ ℕ) :
    support (f n • ∏ i ∈ x.support, (x i) ^ (n i)) ⊆
      AddSubmonoid.closure (⋃ i : σ, (x i).support) := by
  exact (Function.support_const_smul_subset (f n) (∏ i ∈ x.support, x i ^ n i).coeff).trans
    (support_MVpow_subset_closure σ x n)

theorem isPWO_iUnion_support_MVpow [LinearOrderedCancelAddCommMonoid Γ] [CommSemiring R]
    (σ : Type*) (f : (σ →₀ ℕ) → R) (x : σ →₀ HahnSeries Γ R) (hx : ∀ i : σ, 0 ≤ (x i).order) :
    (⋃ n : σ →₀ ℕ, (f n •  ∏ i ∈ x.support, (x i) ^ (n i)).support).IsPWO := by
  refine Set.IsPWO.mono ?_ (Set.iUnion_subset fun n => support_smul_MVpow_subset_closure σ f x n)
  refine Set.IsPWO.addSubmonoid_closure ?_ ?_
  · intro g hg
    simp only [Set.mem_iUnion, mem_support, ne_eq] at hg
    obtain ⟨i, hi⟩ := hg
    exact (hx i).trans (order_le_of_coeff_ne_zero hi)
  · have h : ⋃ i, (x i).support =
        (⋃ i ∈ x.support, (x i).support) ∪ (⋃ i ∉ x.support, (x i).support) := by
      classical
      simp_rw [← Set.iUnion_ite, ite_id (x _).support]
    rw [h, Set.isPWO_union]
    constructor
    · exact (isPWO_bUnion x.support).mpr fun i _ ↦ isPWO_support (x i)
    · rw [show (⋃ i, ⋃ (_ : i ∉ x.support), (x i).support) = ∅ by simp_all]
      exact Set.isPWO_empty

/-!
theorem isPWO_iUnion_support_MVpow' [LinearOrderedCancelAddCommMonoid Γ] [CommSemiring R]
    {σ : Type*} (s : Finset σ) (f : (σ →₀ ℕ) → R) (x : σ →₀ HahnSeries Γ R)
    (hx : ∀ i : σ, 0 ≤ (x i).order) :
    (⋃ n : σ →₀ ℕ, (f n •  ∏ i ∈ s, (x i) ^ (n i)).support).IsPWO := by
  sorry
-/

theorem isPWO_iUnion_support_smul_pow [LinearOrderedCancelAddCommMonoid Γ] [Semiring R] (f : ℕ → R)
    (x : HahnSeries Γ R) (hx : 0 ≤ x.order) :
    (⋃ n : ℕ, (f n • x ^ n).support).IsPWO :=
  (x.isPWO_support'.addSubmonoid_closure
    fun _ hg => le_trans hx (order_le_of_coeff_ne_zero (Function.mem_support.mp hg))).mono
    (Set.iUnion_subset fun n => support_smul_pow_subset_closure f x n)

theorem isPWO_iUnion_support_powers [LinearOrderedCancelAddCommMonoid Γ] [Semiring R]
    (x : HahnSeries Γ R) (hx : 0 ≤ x.order) : (⋃ n : ℕ, (x ^ n).support).IsPWO := by
  have _ := isPWO_iUnion_support_smul_pow (fun n => 1) x hx
  simp_all only [one_smul]

namespace SummableFamily

section PowerSeriesFamily

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R]

-- consider substitutions of power series in finitely many variables, using finitely many
-- positive-orderTop elements.

theorem co_support_zero (g : Γ) : {a | ¬((0 : HahnSeries Γ R) ^ a).coeff g = 0} ⊆ {0} := by
  simp_all only [Set.subset_singleton_iff, Set.mem_setOf_eq]
  intro n hn
  by_contra h'
  simp_all only [ne_eq, not_false_eq_true, zero_pow, zero_coeff, not_true_eq_false]

variable {x : HahnSeries Γ R}

theorem pow_finite_co_support (hx : 0 < x.orderTop) (g : Γ) :
    Set.Finite {a | ((fun n ↦ x ^ n) a).coeff g ≠ 0} := by
  have hpwo : Set.IsPWO (⋃ n, support (x ^ n)) :=
    isPWO_iUnion_support_powers x (zero_le_orderTop_iff.mp <| le_of_lt hx)
  by_cases hox : x = 0
  · rw [hox]
    exact Set.Finite.subset (Set.finite_singleton 0) (co_support_zero g)
  by_cases hg : g ∈ ⋃ n : ℕ, { g | (x ^ n).coeff g ≠ 0 }
  swap; · exact Set.finite_empty.subset fun n hn => hg (Set.mem_iUnion.2 ⟨n, hn⟩)
  apply hpwo.isWF.induction hg
  intro y ys hy
  refine
    ((((addAntidiagonal x.isPWO_support hpwo y).finite_toSet.biUnion fun ij hij =>
                  hy ij.snd ?_ ?_).image
              Nat.succ).union
          (Set.finite_singleton 0)).subset
      ?_
  · exact (mem_addAntidiagonal.1 (mem_coe.1 hij)).2.1
  · obtain ⟨hi, _, rfl⟩ := mem_addAntidiagonal.1 (mem_coe.1 hij)
    exact lt_add_of_pos_left ij.2 <| lt_of_lt_of_le ((zero_lt_orderTop_iff hox).mp hx) <|
      order_le_of_coeff_ne_zero <| Function.mem_support.mp hi
  · rintro (_ | n) hn
    · exact Set.mem_union_right _ (Set.mem_singleton 0)
    · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support hn
      refine Set.mem_union_left _ ⟨n, Set.mem_iUnion.2 ⟨⟨j, i⟩, Set.mem_iUnion.2 ⟨?_, hi⟩⟩, rfl⟩
      simp only [mem_coe, mem_addAntidiagonal, mem_support, ne_eq, Set.mem_iUnion]
      exact ⟨hj, ⟨n, hi⟩, add_comm j i⟩

theorem smul_pow_finite_co_support (hx : 0 < x.orderTop) (f : ℕ → R) (g : Γ) :
    Set.Finite {a | ((fun n ↦ f n • x ^ n) a).coeff g ≠ 0} :=
  Set.Finite.subset (pow_finite_co_support hx g) fun n hn hng => (by simp_all)

lemma supp_eq_univ_of_pos' (σ : Type*) (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i : σ, 0 < (y i).order) : y.support = Set.univ (α := σ) := by
  have hy₁ : ∀ i : σ, y i ≠ 0 := fun i => ne_zero_of_order_ne (ne_of_gt (hy i))
  exact Set.eq_univ_of_univ_subset fun i _ => by simp_all

/-- A finsupp whose every element has positive order has fintype source. -/
def Fintype_of_pos_order (σ : Type*) (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i : σ, 0 < (y i).order) : Fintype σ := by
  refine Set.fintypeOfFiniteUniv ?_
  rw [← supp_eq_univ_of_pos' σ y hy]
  exact finite_toSet y.support

lemma supp_eq_univ_of_pos (σ : Type*) [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i : σ, 0 < (y i).order) : y.support = Finset.univ (α := σ) :=
  eq_univ_of_forall fun i => Finsupp.mem_support_iff.mpr (ne_zero_of_order_ne (ne_of_gt (hy i)))

/-!
theorem mvpow_finite_co_support {σ : Type*} {s : Finset σ} (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i ∈ s, 0 < (y i).order) (g : Γ) :
    Set.Finite {a : (s →₀ ℕ) | --{a | ((fun n ↦ ∏ i ∈ s, y i ^ n ⟨i, ⋯⟩) a).coeff g ≠ 0}
      ((fun n : (s →₀ ℕ) ↦ ∏ i ∈ s, y i ^ n ⟨i, _⟩) a).coeff g ≠ 0} := by
  refine cons_induction ?_ ?_ s
  · simp_all only [prod_empty, one_coeff, ne_eq, ite_eq_right_iff, Classical.not_imp]
    exact Set.toFinite {a | g = 0 ∧ ¬1 = 0}
  · intro i s his hs
    simp_rw [prod_cons]

    sorry
  have hpwo : Set.IsPWO (⋃ n : (σ →₀ ℕ), (∏ i, (y i) ^ (n i)).support) := by
    have hpwo' := isPWO_iUnion_support_MVpow σ (fun n => 1) y (fun i => le_of_lt (hy i))
    simp only [one_smul, supp_eq_univ_of_pos σ y hy] at hpwo'
    exact hpwo'
  by_cases hg : g ∈ ⋃ n : (σ →₀ ℕ), { g | (∏ i, (y i) ^ (n i)).coeff g ≠ 0 }
  swap; · exact Set.finite_empty.subset fun n hn => hg (Set.mem_iUnion.2 ⟨n, hn⟩)
  simp_all only [one_smul]
  by_cases h0 : g = 0
  · refine Set.Finite.subset (Set.finite_singleton 0) ?_
    intro a
    contrapose
    simp only [Set.mem_singleton_iff, ne_eq, Set.mem_setOf_eq, Decidable.not_not]
    intro ha
    obtain ⟨i, hi⟩ : ∃(i : σ), a i ≠ 0 := not_forall.mp fun h ↦ ha (Finsupp.ext h)

    refine coeff_eq_zero_of_lt_order ?_

    sorry

  sorry

/-- A summable family of Hahn series given by substituting the multivariable power series generators
into positive order Hahn series.-/
def mvPowerSeriesFamily {σ : Type*} (s : Finset σ) (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i ∈ s, 0 < (y i).order) : SummableFamily Γ R (s →₀ ℕ) where
  toFun n := ∏ i ∈ s, y i ^ n ⟨i, _⟩
  isPWO_iUnion_support' := by
    refine cons_induction (Set.IsPWO.mono (Set.isPWO_singleton 0) (by simp)) ?_ s
    intro i s his hp
    simp_rw [prod_cons]
    sorry
--    isPWO_iUnion_support_MVpow σ f y (fun i => le_of_lt (hy i))
  finite_co_support' g := by
    refine Set.Finite.subset (mvpow_finite_co_support y hy g) ?_
    intro n hn hng
    simp_all only [smul_coeff, smul_eq_mul, ne_eq, Set.mem_setOf_eq]
    rw [supp_eq_univ_of_pos σ y hy] at hn
    exact (ne_zero_and_ne_zero_of_mul hn).2 hng
-/

/-- A summable family of Hahn series given by substituting the power series variable `X` into the
positive order Hahn series `x`.-/
@[simps]
def PowerSeriesFamily (hx : 0 < x.orderTop) (f : PowerSeries R) : SummableFamily Γ R ℕ where
  toFun n := (PowerSeries.coeff R n f) • x ^ n
  isPWO_iUnion_support' := isPWO_iUnion_support_smul_pow (fun n => PowerSeries.coeff R n f) x
    (zero_le_orderTop_iff.mp <| le_of_lt hx)
  finite_co_support' g := smul_pow_finite_co_support hx (fun n => PowerSeries.coeff R n f) g

theorem powerSeriesFamilyAdd (hx : 0 < x.orderTop) (f g : PowerSeries R) :
    PowerSeriesFamily hx (f + g) = PowerSeriesFamily hx f + PowerSeriesFamily hx g := by
  ext1 n
  simp [add_smul]

theorem powerSeriesFamilySMul (hx : 0 < x.orderTop) (r : R) (f : PowerSeries R) :
    PowerSeriesFamily hx (r • f) = (HahnSeries.single (0 : Γ) r) • (PowerSeriesFamily hx f) := by
  ext1 n
  rw [PowerSeriesFamily_toFun, LinearMapClass.map_smul, smul_apply, PowerSeriesFamily_toFun,
    HahnModule.single_zero_smul_eq_smul, smul_assoc, HahnModule.of_symm_smul,
    Equiv.symm_apply_apply]

/-- This is missing a suitable isomorphism. -/
def mvpowerseries_family_aux {σ : Type*} (hx : 0 < x.orderTop) (s : Finset σ) (f : PowerSeries R)
    (t : SummableFamily Γ R (s →₀ ℕ)) : SummableFamily Γ R ((s →₀ ℕ) × ℕ) :=
  FamilyMul t (PowerSeriesFamily hx f)

theorem sum_coeff {α} (s : Finset α) (f : α → HahnSeries Γ R) (g : Γ) :
    (Finset.sum s f).coeff g = Finset.sum s (fun i => (f i).coeff g) :=
  cons_induction_on s (by simp) fun i t hit hc => by rw [sum_cons, sum_cons, add_coeff, hc]

theorem finsum_prod {R} [AddCommMonoid R] (f : ℕ × ℕ →₀ R) :
    ∑ᶠ (i : ℕ), ∑ᶠ (j : ℕ),  f (i, j) = ∑ᶠ (i : ℕ × ℕ), f i :=
  Eq.symm (finsum_curry (fun ab ↦ f ab) (Finsupp.finite_support f))

theorem finsum_antidiagonal_prod [AddCommMonoid α] [HasAntidiagonal α] (f : α × α →₀ R) :
    ∑ᶠ (i : α), (∑ j ∈ antidiagonal i, f j) =
    ∑ᶠ (i : α × α), f i := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (s := f.support) (fun i _ => by simp_all),
    finsum_eq_sum_of_support_subset _ (s := (f.support.image fun i => i.1 + i.2)) ?_, sum_sigma']
  refine (Finset.sum_of_injOn (fun x => ⟨x.1 + x.2, x⟩) ?_ ?_ ?_ ?_).symm
  · exact fun x _ y _ hxy => by simp_all
  · intro x hx
    simp_all only [mem_coe, Finsupp.mem_support_iff, ne_eq, coe_sigma, coe_image, Set.mem_sigma_iff,
      Set.mem_image, Prod.exists, mem_antidiagonal, and_true]
    use x.1, x.2
  · intro x hx h
    simp_all only [mem_sigma, mem_image, Finsupp.mem_support_iff, ne_eq, Prod.exists,
      mem_antidiagonal, Set.mem_image, mem_coe, not_exists, not_and]
    have h0 : ∀ i j : α, ⟨i + j, (i, j)⟩ = x → f (i, j) = 0 := by
      intro i j
      contrapose!
      exact h i j
    refine h0 x.snd.1 x.snd.2 ?_
    simp_all only [Prod.mk.eta, Sigma.eta]
  · exact fun x _ => rfl
  · intro x hx
    simp_all only [Function.mem_support, ne_eq, coe_image, Set.mem_image, mem_coe,
      Finsupp.mem_support_iff, Prod.exists]
    have h1 := exists_ne_zero_of_sum_ne_zero hx
    use h1.choose.1, h1.choose.2
    refine ⟨h1.choose_spec.2, ?_⟩
    · rw [← @mem_antidiagonal]
      exact h1.choose_spec.1

--#find_home! finsum_antidiagonal_prod --[Mathlib.RingTheory.Adjoin.Basic]

theorem power_series_family_supp_subset (hx : 0 < x.orderTop) (a b : PowerSeries R) (g : Γ) :
    ((PowerSeriesFamily hx (a * b)).coeff g).support ⊆
    (((PowerSeriesFamily hx a).FamilyMul (PowerSeriesFamily hx b)).coeff g).support.image
      fun i => i.1 + i.2 := by
  simp_all only [coeff_support, PowerSeriesFamily_toFun, smul_coeff, smul_eq_mul, FamilyMul_toFun,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Set.Finite.toFinset_subset, coe_image,
    Set.Finite.coe_toFinset, support_subset_iff, ne_eq, Set.mem_image, Function.mem_support,
    Prod.exists]
  intro n hn
  rw [PowerSeries.coeff_mul, ← ne_eq, sum_mul] at hn
  have he : ∃p ∈ antidiagonal n, ¬((PowerSeries.coeff R p.1) a *
      (PowerSeries.coeff R p.2) b * (x ^ n).coeff g) = 0 :=
    exists_ne_zero_of_sum_ne_zero hn
  use he.choose.1, he.choose.2
  refine ⟨?_, mem_antidiagonal.mp he.choose_spec.1⟩
  rw [← pow_add, mem_antidiagonal.mp he.choose_spec.1, mul_left_comm, ← mul_assoc]
  exact he.choose_spec.2

/-!  have hf : (fun (i : ℕ × ℕ) => ((PowerSeries.coeff R i.1) a • x ^ i.1 *
      (PowerSeries.coeff R i.2) b • x ^ i.2).coeff g).support.Finite := by
    refine (((PowerSeriesFamily hx a).FamilyMul
      (PowerSeriesFamily hx b)).finite_co_support' g).subset ?_
    intro y hy
    simp_all [FamilyMul, PowerSeriesFamily_toFun]
  let f : ℕ × ℕ →₀ R := Finsupp.ofSupportFinite _ hf -/

theorem power_series_family_prod_eq_family_mul (hx : 0 < x.orderTop) (a b : PowerSeries R) :
    (PowerSeriesFamily hx (a * b)).hsum =
    ((PowerSeriesFamily hx a).FamilyMul (PowerSeriesFamily hx b)).hsum := by
  ext g
  simp only [PowerSeriesFamily_toFun, PowerSeries.coeff_mul, Finset.sum_smul, ← Finset.sum_product,
    hsum_coeff_sum, FamilyMul_toFun]
  rw [sum_subset (power_series_family_supp_subset hx a b g)]
  rw [← @HahnSeries.sum_coeff, sum_sigma', sum_coeff]
  refine (Finset.sum_of_injOn (fun x => ⟨x.1 + x.2, x⟩) ?_ ?_ ?_ ?_).symm
  · intro ij _ kl _
    simp_all
  · intro ij hij
    simp_all only [coeff_support, FamilyMul_toFun, PowerSeriesFamily_toFun, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, smul_coeff, smul_eq_mul, Set.Finite.coe_toFinset,
      Function.mem_support, ne_eq, coe_sigma, coe_image, Set.mem_sigma_iff, Set.mem_image,
      Prod.exists, mem_coe, mem_antidiagonal, and_true]
    use ij.1, ij.2
  · intro i hi his
    simp_all only [coeff_support, FamilyMul_toFun, PowerSeriesFamily_toFun, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, smul_coeff, smul_eq_mul, mem_sigma, mem_image,
      Set.Finite.mem_toFinset, Function.mem_support, ne_eq, Prod.exists, mem_antidiagonal,
      Set.Finite.coe_toFinset, Set.mem_image, not_exists, not_and]
    have hisc : ∀ j k : ℕ, ⟨j + k, (j, k)⟩ = i → (PowerSeries.coeff R k) b *
        ((PowerSeries.coeff R j) a * (x ^ j * x ^ k).coeff g) = 0 := by
      intro m n
      contrapose!
      exact his m n
    rw [mul_comm ((PowerSeries.coeff R i.snd.1) a), ← hi.2, mul_assoc, pow_add]
    exact hisc i.snd.1 i.snd.2 <| Sigma.eq hi.2 (by simp)
  · intro i _
    simp only
    rw [smul_mul_smul_comm, pow_add]
  · intro i hi his
    classical
    simp_all only [coeff_support, FamilyMul_toFun, PowerSeriesFamily_toFun, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, smul_coeff, smul_eq_mul, mem_image, Set.Finite.mem_toFinset,
      Function.mem_support, ne_eq, Prod.exists, Decidable.not_not, HahnSeries.sum_coeff]
    rw [@PowerSeries.coeff_mul, sum_mul] at his
    exact his

end PowerSeriesFamily

end SummableFamily

section PowerSeriesSubst

open SummableFamily

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R] {x : HahnSeries Γ R}
(hx : 0 < x.orderTop)

-- Should I call this PowerSeries.heval?

/-- The `R`-algebra homomorphism from `R[[X]]` to `HahnSeries Γ R` given by sending the power series
variable `X` to a positive order element `x`. -/
@[simps]
def PowerSeriesSubst : PowerSeries R →ₐ[R] HahnSeries Γ R where
  toFun f := (PowerSeriesFamily hx f).hsum
  map_one' := by
    simp only [hsum, PowerSeriesFamily_toFun, PowerSeries.coeff_one, ite_smul, one_smul, zero_smul]
    ext g
    simp only
    rw [finsum_eq_single (fun i => (if i = 0 then x ^ i else 0).coeff g) (0 : ℕ)
      (fun n hn => by simp_all), pow_zero, ← zero_pow_eq 0, pow_zero]
  map_mul' a b := by
    simp only [← hsum_family_mul, power_series_family_prod_eq_family_mul]
  map_zero' := by
    simp only [hsum, PowerSeriesFamily_toFun, map_zero, zero_smul, zero_coeff, finsum_zero]
    exact rfl
  map_add' a b := by
    simp only [powerSeriesFamilyAdd, hsum_add]
  commutes' r := by
    simp only [PowerSeries.algebraMap_apply, algebraMap_apply, Algebra.id.map_eq_id,
      RingHom.id_apply, C_apply]
    ext g
    simp only [hsum_coeff, PowerSeriesFamily_toFun, smul_coeff, smul_eq_mul, PowerSeries.coeff_C]
    rw [finsum_eq_single _ 0 fun n hn => by simp_all, single_coeff, pow_zero, one_coeff, mul_ite,
      mul_one, mul_zero]
    exact rfl

theorem subst_mul {a b : PowerSeries R} :
    PowerSeriesSubst hx (a * b) = (PowerSeriesSubst hx a) * PowerSeriesSubst hx b :=
  map_mul (PowerSeriesSubst hx) a b

theorem subst_power_series_unit (u : (PowerSeries R)ˣ) : IsUnit (PowerSeriesSubst hx u) := by
  refine isUnit_iff_exists_inv.mpr ?_
  use PowerSeriesSubst hx u.inv
  rw [← subst_mul, Units.val_inv, map_one]

theorem powerSeriesSubst_coeff (f : PowerSeries R) (g : Γ) :
    (PowerSeriesSubst hx f).coeff g = ∑ᶠ n, ((PowerSeriesFamily hx f).coeff g) n := by
  rw [PowerSeriesSubst_apply, hsum_coeff]
  exact rfl

theorem powerSeriesSubst_coeff_zero (f : PowerSeries R) :
    (PowerSeriesSubst hx f).coeff 0 = PowerSeries.constantCoeff R f := by
  rw [powerSeriesSubst_coeff, finsum_eq_single (fun n => ((PowerSeriesFamily hx f).coeff 0) n) 0,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · simp_all
  · intro n hn
    simp_all only [ne_eq, coeff_toFun, PowerSeriesFamily_toFun, smul_coeff, smul_eq_mul]
    exact mul_eq_zero_of_right ((PowerSeries.coeff R n) f) (coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le ((nsmul_pos_iff hn).mpr hx) orderTop_nsmul_le_orderTop_pow))

/-!
theorem isUnit_of_leadingCoeff_one_order_zero {x : HahnSeries Γ R}
    (hx : x.leadingCoeff = 1) (hxo : x.order = 0) :  IsUnit x := by
  have h₁ : x.leadingTerm = 1 := by
    rw [leadingTerm, ]
  have h : 0 < (x - 1).orderTop := by


theorem isUnit_of_isUnit_leadingCoeff_order_add_unit {x : HahnSeries Γ R}
    (hx : IsUnit x.leadingCoeff) (hxo : IsAddUnit x.order) : IsUnit x := by
  let ⟨⟨u, i, ui, iu⟩, h⟩ := hx
  rw [Units.val_mk] at h
  rw [h] at iu
  have h' : ((single (IsAddUnit.addUnit hxo).neg i) * x).leadingCoeff = 1 := by
    rw [leadingCoeff_mul_of_nonzero, leadingCoeff_of_single]
    exact iu
    rw [leadingCoeff_of_single]
    --by_cases hz : 0 = (1 : R)
    sorry
-/

end PowerSeriesSubst

namespace SummableFamily

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R] {x : HahnSeries Γ R}
(hx : 0 < x.orderTop)

/-- Powers of an element of positive order (or zero) form a summable family. -/
def powers : SummableFamily Γ R ℕ := PowerSeriesFamily hx (PowerSeries.mk 1)

@[simp]
theorem powers_toFun (n : ℕ) : (powers hx) n = x ^ n := by
  ext
  simp [powers]

@[simp]
theorem coe_powers : ⇑(powers hx) = HPow.hPow x := by
  ext
  simp

theorem embDomain_succ_smul_powers :
    (x • powers hx).embDomain ⟨Nat.succ, Nat.succ_injective⟩ =
      powers hx - ofFinsupp (Finsupp.single 0 1) := by
  apply SummableFamily.ext
  rintro (_ | n)
  · rw [embDomain_notin_range, sub_apply, powers_toFun, pow_zero, coe_ofFinsupp,
      Finsupp.single_eq_same, sub_self]
    rw [Set.mem_range, not_exists]
    exact Nat.succ_ne_zero
  · refine Eq.trans (embDomain_image _ ⟨Nat.succ, Nat.succ_injective⟩) ?_
    simp only [smul_apply, powers_toFun, smul_eq_mul, coe_sub, coe_powers, coe_ofFinsupp,
      Pi.sub_apply, pow_succ', ne_eq, self_eq_add_left, add_eq_zero, one_ne_zero, and_false,
      not_false_eq_true, Finsupp.single_eq_of_ne, sub_zero]
    exact rfl

theorem one_sub_self_mul_hsum_powers : (1 - x) * (powers hx).hsum = 1 := by
  rw [← hsum_smul, sub_smul 1 x (powers hx), one_smul, hsum_sub, ←
    hsum_embDomain (x • powers hx) ⟨Nat.succ, Nat.succ_injective⟩, embDomain_succ_smul_powers]
  simp only [hsum_sub, hsum_ofFinsupp, id_eq, Finsupp.sum_single_index, sub_sub_cancel]

end SummableFamily

section Inversion

section Monoid

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R]

theorem one_minus_single_mul' {x y : HahnSeries Γ R} (r : R) (hr : r * x.leadingCoeff = 1)
    (hxy : x = y + x.leadingTerm) (hxo : IsAddUnit x.order) :
    1 - single (IsAddUnit.addUnit hxo).neg r * x = -(single (IsAddUnit.addUnit hxo).neg r * y) := by
  nth_rw 2 [hxy]
  rw [mul_add, leadingTerm_eq, single_mul_single, ← leadingCoeff_eq, hr, AddUnits.neg_eq_val_neg,
    IsAddUnit.val_neg_add, sub_add_eq_sub_sub_swap, sub_eq_neg_self, sub_eq_zero_of_eq]
  exact rfl

theorem unit_aux' (x : HahnSeries Γ R) {r : R} (hr : r * x.leadingCoeff = 1)
    (hxo : IsAddUnit x.order) : 0 < (1 - single (IsAddUnit.addUnit hxo).neg r * x).orderTop := by
  let y := (x - x.leadingTerm)
  by_cases hy : y = 0
  · have hrx : (single (IsAddUnit.addUnit hxo).neg) r * x = 1 := by
      nth_rw 2 [eq_of_sub_eq_zero hy] -- get a bad loop without `nth_rw`
      simp only [AddUnits.neg_eq_val_neg, leadingTerm_eq, ← leadingCoeff_eq, single_mul_single,
        IsAddUnit.val_neg_add, hr, single_zero_one]
    simp only [hrx, sub_self, orderTop_zero, WithTop.zero_lt_top]
  have hr' : ∀ (s : R), r * s = 0 → s = 0 :=
    fun s hs => by rw [← one_mul s, ← hr, mul_right_comm, hs, zero_mul]
  have hy' : 0 < (single (IsAddUnit.addUnit hxo).neg r * y).order := by
    rw [(order_mul_single_of_nonzero_divisor hr' hy)]
    refine pos_of_lt_add_right (a := x.order) ?_
    rw [← add_assoc, add_comm x.order, AddUnits.neg_eq_val_neg, IsAddUnit.val_neg_add, zero_add]
    exact order_lt_add_single_support_order (sub_add_cancel x x.leadingTerm).symm hy
  simp only [one_minus_single_mul' r hr (sub_add_cancel x x.leadingTerm).symm, orderTop_neg]
  exact zero_lt_orderTop_of_order hy'

theorem isUnit_of_isUnit_leadingCoeff_AddUnitOrder {x : HahnSeries Γ R} (hx : IsUnit x.leadingCoeff)
    (hxo : IsAddUnit x.order) : IsUnit x := by
  let ⟨⟨u, i, ui, iu⟩, h⟩ := hx
  rw [Units.val_mk] at h
  rw [h] at iu
  have h' := SummableFamily.one_sub_self_mul_hsum_powers (unit_aux' x iu hxo)
  rw [sub_sub_cancel] at h'
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_eq_one _ _ h')

end Monoid

variable [LinearOrderedAddCommGroup Γ]

section CommRing

variable [CommRing R]

theorem neg_eq_addUnit_neg {G : Type*} [AddGroup G] (g : G) :
    -g = (IsAddUnit.addUnit (AddGroup.isAddUnit g)).neg := by
  simp only [AddUnits.neg_eq_val_neg, AddUnits.val_neg_eq_neg_val, IsAddUnit.addUnit_spec]
--#find_home! neg_eq_addUnit_neg --[Mathlib.Algebra.Group.Units]

theorem one_minus_single_mul (x y : HahnSeries Γ R) (r : R) (hr : r * x.leadingCoeff = 1)
    (hxy : x = y + x.leadingTerm) : 1 - single (-order x) r * x = -(single (-x.order) r * y) := by
  rw [neg_eq_addUnit_neg]
  exact one_minus_single_mul' r hr hxy (AddGroup.isAddUnit x.order)

theorem unit_aux (x : HahnSeries Γ R) {r : R} (hr : r * x.leadingCoeff = 1) :
    0 < (1 - single (-x.order) r * x).orderTop := by
  rw [neg_eq_addUnit_neg]
  exact unit_aux' x hr (AddGroup.isAddUnit x.order)

theorem isUnit_of_isUnit_leadingCoeff {x : HahnSeries Γ R} (hx : IsUnit x.leadingCoeff) :
    IsUnit x := by
  exact isUnit_of_isUnit_leadingCoeff_AddUnitOrder hx (AddGroup.isAddUnit x.order)

theorem isUnit_iff [IsDomain R] {x : HahnSeries Γ R} :
    IsUnit x ↔ IsUnit (x.leadingCoeff) := by
  refine { mp := ?mp, mpr := isUnit_of_isUnit_leadingCoeff }
  rintro ⟨⟨u, i, ui, iu⟩, rfl⟩
  refine
    isUnit_of_mul_eq_one (u.leadingCoeff) (i.leadingCoeff)
      ((mul_coeff_order_add_order u i).symm.trans ?_)
  rw [ui, one_coeff, if_pos]
  rw [← order_mul (left_ne_zero_of_mul_eq_one ui) (right_ne_zero_of_mul_eq_one ui), ui, order_one]

end CommRing

open Classical in
instance instField [Field R] : Field (HahnSeries Γ R) where
  __ : IsDomain (HahnSeries Γ R) := inferInstance
  inv x :=
    if x0 : x = 0 then 0
    else
      (single (-x.order)) (x.leadingCoeff)⁻¹ *
        (SummableFamily.powers (unit_aux x (inv_mul_cancel₀ (leadingCoeff_ne_iff.mpr x0)))).hsum
  inv_zero := dif_pos rfl
  mul_inv_cancel x x0 := (congr rfl (dif_neg x0)).trans <| by
    have h :=
      SummableFamily.one_sub_self_mul_hsum_powers
        (unit_aux x (inv_mul_cancel₀ (leadingCoeff_ne_iff.mpr x0)))
    rw [sub_sub_cancel] at h
    rw [← mul_assoc, mul_comm x, h]
  nnqsmul := _
  nnqsmul_def := fun q a => rfl
  qsmul := _
  qsmul_def := fun q a => rfl

end Inversion

end HahnSeries
