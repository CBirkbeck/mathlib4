/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yonele Hu
-/
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Regular.RegularSequence

/-!

# Krull Dimension of quotient regular sequence

-/

section orderIso

variable {R : Type*} [CommRing R]

#check ringKrullDim_quotient
/-- `Spec (R / I)` is isomorphic to `Z(I)`. -/
noncomputable def Ideal.primeSpectrumQuotientOrderIsoZeroLocus (I : Ideal R) :
    PrimeSpectrum (R ⧸ I) ≃o (PrimeSpectrum.zeroLocus (R := R) I) where
  toFun p := ⟨(Ideal.Quotient.mk I).specComap p,
    I.mk_ker.symm.trans_le (Ideal.ker_le_comap (Ideal.Quotient.mk I))⟩
  invFun := fun ⟨⟨p, _⟩, hp⟩ ↦ ⟨p.map (Ideal.Quotient.mk I),
    p.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (I.mk_ker.trans_le hp)⟩
  left_inv := by
    intro ⟨p, _⟩
    simp only [PrimeSpectrum.mk.injEq]
    exact p.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  right_inv := by
    intro ⟨⟨p, _⟩, hp⟩
    simp only [Subtype.mk.injEq, PrimeSpectrum.mk.injEq]
    exact (p.comap_map_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).trans <|
      sup_eq_left.mpr <| I.mk_ker.trans_le hp
  map_rel_iff' {a b} := by
    show a.asIdeal.comap _ ≤ b.asIdeal.comap _ ↔ a ≤ b
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
      PrimeSpectrum.asIdeal_le_asIdeal]

variable {R : Type*} [CommSemiring R]

noncomputable def Ideal.primeSpectrumLocalizationAtPrime (I : Ideal R) [I.IsPrime] :
    PrimeSpectrum (Localization.AtPrime I) ≃o ({ p : PrimeSpectrum R // p.1 ≤ I }) :=
  let e := IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime I) I
  {
  toFun p := ⟨⟨(e ⟨p.1, p.2⟩).1, (e ⟨p.1, p.2⟩).2.1⟩, (e ⟨p.1, p.2⟩).2.2⟩
  invFun p := ⟨(e.symm ⟨p.1.1, p.1.2, p.2⟩).1, (e.symm ⟨p.1.1, p.1.2, p.2⟩).2⟩
  left_inv p := by simp only [Subtype.coe_eta, OrderIso.symm_apply_apply]
  right_inv p := by simp only [Subtype.coe_eta, OrderIso.apply_symm_apply]
  map_rel_iff' := e.le_iff_le
}

end orderIso

section QuotSMulTop

instance {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Subsingleton M] (N : Submodule R M) :
    Subsingleton (M ⧸ N) := by
  apply subsingleton_of_forall_eq 0
  rintro ⟨x⟩
  exact congrArg (Quot.mk ⇑N.quotientRel) (Subsingleton.eq_zero x)

end QuotSMulTop

/- section FiniteDimensionalOrder

open RingTheory Sequence IsLocalRing Submodule Module

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (x : R)
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

instance [Nontrivial M] : FiniteDimensionalOrder (Module.support R M) := by
  rw [support_eq_zeroLocus]
  have := primeSpectrumQuotientOrderIsoZeroLocus (annihilator R M)
  have : IsLocalRing (R ⧸ annihilator R M) := by
    have : annihilator R M ≤ maximalIdeal R := by
      sorry
    sorry
  have : FiniteDimensionalOrder (PrimeSpectrum (R ⧸ annihilator R M)) := inferInstance
  sorry

end FiniteDimensionalOrder -/

section LTSeries

variable {α : Type*} [Preorder α] (p : LTSeries α) (n : Fin (p.length + 1))

theorem LTSeries.head_le : p.head ≤ p n := LTSeries.monotone p (Fin.zero_le n)

end LTSeries

theorem IsLocalRing.le_maximalIdeal_of_isPrime {R : Type*} [CommSemiring R] [IsLocalRing R]
    (p : Ideal R) [hp : p.IsPrime] : p ≤ maximalIdeal R :=
  le_maximalIdeal hp.ne_top

theorem Fin.natCast_eq_mk {m n : ℕ} (h : m < n) : have : NeZero n := NeZero.of_gt h ;
    (m : Fin n) = Fin.mk m h :=
  Fin.val_inj.mp (Nat.mod_eq_of_lt h)

theorem Fin.one_eq_mk_of_lt {n : ℕ} (h : 1 < n) : have : NeZero n := NeZero.of_gt h ;
    1 = Fin.mk 1 h :=
  Fin.val_inj.mp (Nat.mod_eq_of_lt h)

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

local notation "𝔪" => IsLocalRing.maximalIdeal R

section move

open Ideal

#check Ideal.mem_minimalPrimes_span_of_mem_minimalPrimes_span_insert
theorem Ideal.map_height_le_one_of_mem_minimalPrimes {I p : Ideal R} {x : R}
    (hp : p ∈ (I ⊔ span {x}).minimalPrimes) : (p.map (Ideal.Quotient.mk I)).height ≤ 1 :=
  let f := Ideal.Quotient.mk I
  have : p.IsPrime := hp.1.1
  height_le_one_of_isPrincipal_of_mem_minimalPrimes ((span {x}).map f) (p.map f) ⟨
    ⟨map_isPrime_of_surjective Quotient.mk_surjective <|
      I.mk_ker.trans_le (le_sup_left.trans hp.1.2), map_mono (le_sup_right.trans hp.1.2)⟩,
    fun _ ⟨hr, hxr⟩ hrp ↦ map_le_iff_le_comap.mpr <| hp.2 ⟨hr.comap f, sup_le_iff.mpr
      ⟨I.mk_ker.symm.trans_le <| ker_le_comap (Ideal.Quotient.mk I), le_comap_of_map_le hxr⟩⟩ <|
        (comap_mono hrp).trans <| Eq.le <|
          (p.comap_map_of_surjective _ Quotient.mk_surjective).trans <|
            sup_eq_left.mpr (I.mk_ker.trans_le (le_sup_left.trans hp.1.2))⟩

theorem PrimeSpectrum.exist_mem_one_of_mem_maximal_ideal [IsLocalRing R] {p₁ p₀ : (PrimeSpectrum R)}
    (h₀ : p₀ < p₁) (h₁ : p₁ < ⟨𝔪, inferInstance⟩) {x : R} (hx : x ∈ 𝔪) :
      ∃ q : PrimeSpectrum R, x ∈ q.1 ∧ p₀ < q ∧ q.1 < 𝔪 := by
  by_cases hn : x ∈ p₀.1
  · exact ⟨p₁, h₀.le hn, h₀, h₁⟩
  let e := p₀.1.primeSpectrumQuotientOrderIsoZeroLocus.symm
  obtain ⟨q, hq⟩ := (p₀.1 + span {x}).nonempty_minimalPrimes <|
    sup_le (IsLocalRing.le_maximalIdeal_of_isPrime p₀.1) ((span_singleton_le_iff_mem 𝔪).mpr hx)
      |>.trans_lt (IsMaximal.isPrime' 𝔪).1.lt_top |>.ne
  let q : PrimeSpectrum R := ⟨q, hq.1.1⟩
  have : q.1.IsPrime := q.2
  have hxq : x ∈ q.1 := le_sup_right.trans hq.1.2 (mem_span_singleton_self x)
  refine ⟨q, hxq, lt_of_le_not_le (le_sup_left.trans hq.1.2) fun h ↦ hn (h hxq), ?_⟩
  refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime q.1) fun hqm ↦ ?_
  have h : (e ⟨q, le_sup_left.trans hq.1.2⟩).1.height ≤ 1 :=
    map_height_le_one_of_mem_minimalPrimes hq
  simp_rw [show q = ⟨𝔪, inferInstance⟩ from PrimeSpectrum.ext_iff.mpr hqm] at h
  have hph : (e ⟨p₁, h₀.le⟩).1.height ≤ 0 := by
    refine Order.lt_one_iff_nonpos.mp (height_le_iff.mp h _ inferInstance ?_)
    simp only [asIdeal_lt_asIdeal, OrderIso.lt_iff_lt, Subtype.mk_lt_mk, h₁]
  refine ENat.not_lt_zero (e ⟨p₀, le_refl p₀⟩).1.height (height_le_iff.mp hph _ inferInstance ?_)
  simp only [asIdeal_lt_asIdeal, OrderIso.lt_iff_lt, Subtype.mk_lt_mk, h₀]

theorem PrimeSpectrum.exist_mem_one_of_mem_two {p₁ p₀ p₂ : (PrimeSpectrum R)}
    (h₀ : p₀ < p₁) (h₁ : p₁ < p₂) {x : R} (hx : x ∈ p₂.1) :
      ∃ q : (PrimeSpectrum R), x ∈ q.1 ∧ p₀ < q ∧ q < p₂ := by
  let e := p₂.1.primeSpectrumLocalizationAtPrime.symm
  sorry--have := exist_mem_one_of_mem_maximal_ideal

/-- Let $R$ be a Noetherian ring, $\mathfrak{p}_0 < \dots < \mathfrak{p}_n$ be a
  chain of primes, $x \in \mathfrak{p}_n$. Then we can find a chain of primes
  $\mathfrak{q}_0 < \dots < \mathfrak{q}_n$ such that $x \in \mathfrak{q}_1$,
  $\mathfrak{p}_0 = \mathfrak{q}_0$ and $\mathfrak{p}_n = \mathfrak{q}_n$. -/
theorem PrimeSpectrum.exist_lTSeries_mem_one_of_mem_last (p : LTSeries (PrimeSpectrum R))
    {x : R} (hx : x ∈ p.last.1) : ∃ q : LTSeries (PrimeSpectrum R),
      x ∈ (q 1).1 ∧ p.length = q.length ∧ p.head = q.head ∧ p.last = q.last := by
  generalize hp : p.length = n
  induction' n with n hn generalizing p
  · use RelSeries.singleton (· < ·) p.last
    simp only [RelSeries.singleton_toFun, hx, RelSeries.singleton_length, RelSeries.head,
      RelSeries.last_singleton, and_true, true_and]
    rw [show 0 = Fin.last p.length from Fin.zero_eq_mk.mpr hp, RelSeries.last]
  by_cases h0 : n = 0
  · use p
    have h1 : 1 = Fin.last p.length := by
      rw [Fin.last, hp, h0, zero_add]
      exact Fin.natCast_eq_mk (Nat.one_lt_succ_succ 0)
    simp only [h1, hp, Nat.add_left_cancel_iff, and_self, and_true]
    exact hx
  obtain ⟨q, hxq, hq2, hq⟩ : ∃ q : (PrimeSpectrum R), x ∈ q.1 ∧
      p ⟨p.length - 2, p.length.sub_lt_succ 2⟩ < q ∧ q < p.last := by
    refine (p ⟨p.length - 1, p.length.sub_lt_succ 1⟩).exist_mem_one_of_mem_two ?_ ?_ hx
    · refine p.strictMono (Fin.mk_lt_mk.mpr (Nat.pred_lt ?_))
      simp only [hp, Nat.sub_eq, add_tsub_cancel_right, ne_eq, h0, not_false_eq_true]
    · refine p.strictMono (Fin.mk_lt_mk.mpr (Nat.pred_lt ?_))
      simp only [Nat.sub_eq, tsub_zero, ne_eq, hp, n.add_one_ne_zero, not_false_eq_true]
  obtain ⟨Q, hxQ, hQ, hh, hl⟩ :=
    hn (p.eraseLast.eraseLast.snoc q hq2) (by simp only [RelSeries.last_snoc, hxq]) <| by
      simp only [RelSeries.snoc_length, RelSeries.eraseLast_length, hp]
      exact Nat.succ_pred_eq_of_ne_zero h0
  refine ⟨Q.snoc p.last ?_, ?_, ?_, ?_, ?_⟩
  · simp only [← hl, RelSeries.last_snoc, hq]
  · have h1 : 1 = (1 : Fin (Q.length + 1)).castSucc := by
      have h : 1 < Q.length + 1 := by
        rw [← hQ]
        exact Nat.sub_ne_zero_iff_lt.mp h0
      simp only [Fin.one_eq_mk_of_lt h, Fin.castSucc_mk, Fin.mk_one]
    simp only [h1, RelSeries.snoc_castSucc, hxQ]
  · simp only [hQ, RelSeries.snoc_length, Nat.add_left_cancel_iff]
  · simp only [RelSeries.head_snoc, ← hh, RelSeries.head_eraseLast]
  · simp only [RelSeries.last_snoc]

end move

namespace Module

section Semiring

variable {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]

theorem subsingleton_of_top_le_bot (h : (⊤ : Submodule R M) ≤ ⊥) : Subsingleton M :=
  subsingleton_of_forall_eq 0 fun _ ↦ h Submodule.mem_top

end Semiring

section QuotSMulTop

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [hm : Module.Finite R M]

open Pointwise PrimeSpectrum

theorem support_quotSMulTop (x : R) :
    Module.support R (QuotSMulTop x M) = Module.support R M ∩ zeroLocus {x} := by
  refine (x • (⊤ : Submodule R M)).quotEquivOfEq (Ideal.span {x} • ⊤)
    ((⊤ : Submodule R M).ideal_span_singleton_smul x).symm |>.support_eq.trans <|
      (Module.support_quotient _).trans ?_
  rw [zeroLocus_span]

theorem subsingleton_of_subsingleton_quotSMulTop {x : R} (hx : x ∈ (annihilator R M).jacobson)
    [h : Subsingleton (QuotSMulTop x M)] : Subsingleton M := by
  rw [← Submodule.annihilator_top] at hx
  exact subsingleton_of_top_le_bot <| le_of_eq <|
    Submodule.eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator hm.1
      (Submodule.subsingleton_quotient_iff_eq_top.mp h).symm hx

theorem nontrivial_quotSMulTop_of_mem_annihilator_jacobson [h : Nontrivial M] {x : R}
    (hx : x ∈ (annihilator R M).jacobson) : Nontrivial (QuotSMulTop x M) := by
  by_contra hq
  have : Subsingleton (QuotSMulTop x M) := not_nontrivial_iff_subsingleton.mp hq
  have : Subsingleton M := subsingleton_of_subsingleton_quotSMulTop hx
  exact not_nontrivial M h

end QuotSMulTop

variable [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

open RingTheory Sequence IsLocalRing Ideal PrimeSpectrum

open scoped Classical in
/-- If $M$ is a finite module ove a local Noetherian ring $R$, then $\dim M \le \dim (M/xM) + 1$
  for all $x$ in the maximal ideal of $R$. -/
theorem supportDim_le_supportDim_quotSMulTop_succ {x : R} (hx : x ∈ maximalIdeal R) :
    supportDim R M ≤ supportDim R (QuotSMulTop x M) + 1 := by
  rcases subsingleton_or_nontrivial M with h | h
  · rw [(supportDim_eq_bot_iff_subsingleton R M).mpr h]
    rw [(supportDim_eq_bot_iff_subsingleton R (QuotSMulTop x M)).mpr inferInstance, WithBot.bot_add]
  have hm : ⟨𝔪, IsMaximal.isPrime' 𝔪⟩ ∈ support R M := maximalIdeal_mem_support R M
  refine iSup_le_iff.mpr (fun q ↦ ?_)
  let p : LTSeries (support R M) :=
    if lt : (q.last).1.1 < 𝔪 then q.snoc ⟨⟨𝔪, IsMaximal.isPrime' 𝔪⟩, hm⟩ lt else q
  obtain ⟨hxp, le⟩ : x ∈ p.last.1.1 ∧ q.length ≤ p.length := by
    by_cases lt : (q.last).1.1 < 𝔪
    · rw [show p = q.snoc ⟨⟨𝔪, IsMaximal.isPrime' 𝔪⟩, hm⟩ lt from dif_pos lt]
      simp only [q.last_snoc, hx, RelSeries.snoc_length, le_add_iff_nonneg_right, zero_le, and_self]
    · have hq : q.last.1.1 = 𝔪 := by
        contrapose! lt
        exact lt_of_le_of_ne (le_maximalIdeal_of_isPrime q.last.1.1) lt
      simp only [show p = q from dif_neg lt, hq, hx, le_refl, and_self]
  obtain ⟨q, hxq, hq, h0, _⟩ := PrimeSpectrum.exist_lTSeries_mem_one_of_mem_last
    (p.map (fun a ↦ a.1) (fun ⦃_ _⦄ a ↦ a)) hxp
  refine (Nat.cast_le.mpr le).trans ?_
  by_cases h : p.length = 0
  · have hb : supportDim R (QuotSMulTop x M) ≠ ⊥ :=
      (supportDim_ne_bot_iff_nontrivial R (QuotSMulTop x M)).mpr <|
        nontrivial_quotSMulTop_of_mem_annihilator_jacobson (maximalIdeal_le_jacobson _ hx)
    rw [h, ← WithBot.coe_unbot (supportDim R (QuotSMulTop x M)) hb]
    exact WithBot.coe_le_coe.mpr (zero_le ((supportDim R (QuotSMulTop x M)).unbot hb + 1))
  let q' : LTSeries (support R (QuotSMulTop x M)) := {
    length := p.length - 1
    toFun := by
      intro ⟨i, hi⟩
      have hi : i + 1 < q.length + 1 :=
        Nat.succ_lt_succ (hi.trans_eq ((Nat.sub_add_cancel (Nat.pos_of_ne_zero h)).trans hq))
      refine ⟨q ⟨i + 1, hi⟩, ?_⟩
      simp only [support_quotSMulTop, Set.mem_inter_iff, mem_zeroLocus, Set.singleton_subset_iff]
      refine ⟨?_, q.monotone
        ((Fin.natCast_eq_mk (Nat.lt_of_add_left_lt hi)).trans_le (Nat.le_add_left 1 i)) hxq⟩
      have hp : p.head.1 ∈ support R M := p.head.2
      simp only [support_eq_zeroLocus, mem_zeroLocus, SetLike.coe_subset_coe] at hp ⊢
      exact hp.trans (h0.trans_le (q.head_le _))
    step := fun ⟨i, _⟩ ↦ q.strictMono (i + 1).lt_add_one
  }
  calc
    (p.length : WithBot ℕ∞) ≤ (p.length - 1 + 1 : ℕ) := Nat.cast_le.mpr le_tsub_add
    _ = (p.length - (1 : ℕ) : WithBot ℕ∞) + 1 := by simp only [Nat.cast_add, Nat.cast_one]
    _ ≤ _ := by
      refine add_le_add_right ?_ 1
      exact le_iSup_iff.mpr fun _ h ↦ h q'

theorem supportDim_quotSMulTop_succ_eq_supportDim (x : R) (reg : IsSMulRegular M x)
    (hx : x ∈ maximalIdeal R) : supportDim R (QuotSMulTop x M) + 1 = supportDim R M := sorry

theorem supportDim_regular_sequence_add_length_eq_supportDim (rs : List R)
    (reg : IsRegular M rs) :
    supportDim R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) + rs.length = supportDim R M := by
  generalize len : rs.length = n
  induction' n with n hn generalizing M rs
  · rw [List.length_eq_zero_iff.mp len, Ideal.ofList_nil, Submodule.bot_smul]
    simpa using supportDim_eq_of_equiv (Submodule.quotEquivOfEqBot ⊥ rfl)
  · match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      have : IsSMulRegular M x := ((isRegular_cons_iff M _ _).mp reg).1
      have mem : x ∈ maximalIdeal R := by
        simp only [mem_maximalIdeal, mem_nonunits_iff]
        by_contra isu
        absurd reg.2
        simp [Ideal.span_singleton_eq_top.mpr isu]
      rw [supportDim_eq_of_equiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x _),
        ← supportDim_quotSMulTop_succ_eq_supportDim x this mem,
        ← hn rs' ((isRegular_cons_iff M _ _).mp reg).2 len, add_assoc]

end Module
