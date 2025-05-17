/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yi Song
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Support

/-!

# Hom(N,M) is subsingleton iff exist smul regular element of M in ann(N)

In this section, we proved that for `R` modules `M N`, `Hom(N,M)` is subsingleton iff
there exist `r : R`, `IsSMulRegular M r` and `r ∈ ann(N)`.
This is the case for `Depth[I](M) = 0`.

-/

open IsLocalRing LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

lemma mem_associatePrimes_of_comap_mem_associatePrimes_localization (S : Submonoid R)
    (p : Ideal (Localization S)) [p.IsPrime]
    (ass : p.comap (algebraMap R (Localization S)) ∈ associatedPrimes R M) :
    p ∈ associatedPrimes (Localization S) (LocalizedModule S M) := by
  rcases ass with ⟨hp, x, hx⟩
  constructor
  · --may be able to remove `p.IsPrime`
    trivial
  · use LocalizedModule.mkLinearMap S M x
    ext t
    induction' t using Localization.induction_on with a
    simp only [LocalizedModule.mkLinearMap_apply, LinearMap.mem_ker,
      LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, mul_one]
    rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_eq_zero']
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · use 1
      simp only [← LinearMap.toSpanSingleton_apply, one_smul, ← LinearMap.mem_ker, ← hx,
        Ideal.mem_comap, ← Localization.mk_one_eq_algebraMap]
      have : Localization.mk a.1 1 = Localization.mk a.1 a.2 * Localization.mk a.2.1 (1 : S) := by
        simp only [Localization.mk_mul, mul_one, ← sub_eq_zero, Localization.sub_mk,
          one_mul, sub_zero]
        simp [mul_comm, Localization.mk_zero]
      rw [this]
      exact Ideal.IsTwoSided.mul_mem_of_left _ h
    · rcases h with ⟨s, hs⟩
      have : s • a.1 • x = (s.1 * a.1) • x := smul_smul s.1 a.1 x
      rw [this, ← LinearMap.toSpanSingleton_apply, ← LinearMap.mem_ker, ← hx, Ideal.mem_comap,
        ← Localization.mk_one_eq_algebraMap] at hs
      have : Localization.mk a.1 a.2 =
        Localization.mk (s.1 * a.1) 1 * Localization.mk 1 (s * a.2) := by
        simp only [Localization.mk_mul, mul_one, one_mul, ← sub_eq_zero, Localization.sub_mk,
          Submonoid.coe_mul, sub_zero]
        simp [← mul_assoc, mul_comm s.1 a.2.1, Localization.mk_zero]
      rw [this]
      exact Ideal.IsTwoSided.mul_mem_of_left _ hs

lemma mem_associatePrimes_localizedModule_atPrime_of_mem_associated_primes {p : Ideal R} [p.IsPrime]
    (ass : p ∈ associatedPrimes R M) :
    maximalIdeal (Localization.AtPrime p) ∈
    associatedPrimes (Localization.AtPrime p) (LocalizedModule p.primeCompl M) := by
  apply mem_associatePrimes_of_comap_mem_associatePrimes_localization
  simpa [Localization.AtPrime.comap_maximalIdeal] using ass

lemma hom_subsingleton_of_mem_ann_isSMulRegular {r : R} (reg : IsSMulRegular M r)
    (mem_ann : r ∈ Module.annihilator R N) : Subsingleton (N →ₗ[R] M) := by
  apply subsingleton_of_forall_eq 0 (fun f ↦ ext fun x ↦ ?_)
  have : r • (f x) = r • 0 := by
    rw [smul_zero, ← map_smul, Module.mem_annihilator.mp mem_ann x, map_zero]
  simpa using reg this

lemma exist_mem_ann_isSMulRegular_of_hom_subsingleton_nontrivial [IsNoetherianRing R]
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] (hom0 : Subsingleton (N →ₗ[R] M)) :
    ∃ r ∈ Module.annihilator R N, IsSMulRegular M r := by
  by_contra! h
  have hexist : ∃ p ∈ associatedPrimes R M, Module.annihilator R N ≤ p := by
    rcases associatedPrimes.nonempty R M with ⟨Ia, hIa⟩
    apply (Ideal.subset_union_prime_finite (associatedPrimes.finite R M) Ia Ia _).mp
    · rw [biUnion_associatedPrimes_eq_compl_regular R M]
      exact fun r hr ↦ h r hr
    · exact fun I hin _ _ ↦ IsAssociatedPrime.isPrime hin
  rcases hexist with ⟨p, pass, hp⟩
  let _ := pass.isPrime
  let p' : PrimeSpectrum R := ⟨p, pass.isPrime⟩
  have loc_ne_zero : p' ∈ Module.support R N := Module.mem_support_iff_of_finite.mpr hp
  rw [Module.mem_support_iff] at loc_ne_zero
  let Rₚ := Localization.AtPrime p
  let Nₚ := LocalizedModule p'.asIdeal.primeCompl N
  let Mₚ := LocalizedModule p'.asIdeal.primeCompl M
  let Nₚ' := Nₚ ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) • (⊤ : Submodule Rₚ Nₚ)
  have ntr : Nontrivial Nₚ' :=
    Submodule.Quotient.nontrivial_of_lt_top _ (Ne.lt_top'
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator Rₚ Nₚ))))
  let Mₚ' := Mₚ ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) • (⊤ : Submodule Rₚ Mₚ)
  let _ : Module p.ResidueField Nₚ' :=
    Module.instQuotientIdealSubmoduleHSMulTop Nₚ (maximalIdeal (Localization.AtPrime p))
  have := AssociatePrimes.mem_iff.mp
    (mem_associatePrimes_localizedModule_atPrime_of_mem_associated_primes pass)
  rcases this.2 with ⟨x, hx⟩
  have : Nontrivial (Module.Dual p.ResidueField Nₚ') := by simpa using ntr
  rcases exists_ne (α := Module.Dual p.ResidueField Nₚ') 0 with ⟨g, hg⟩
  let to_res' : Nₚ' →ₗ[Rₚ] p.ResidueField := {
    __ := g
    map_smul' r x := by
      simp only [AddHom.toFun_eq_coe, coe_toAddHom, RingHom.id_apply]
      convert g.map_smul (Ideal.Quotient.mk _ r) x }
  let to_res : Nₚ →ₗ[Rₚ] p.ResidueField :=
    to_res'.comp ((IsLocalRing.maximalIdeal (Localization.AtPrime p)) • (⊤ : Submodule Rₚ Nₚ)).mkQ
  let i : p.ResidueField →ₗ[Rₚ] Mₚ :=
    Submodule.liftQ _ (LinearMap.toSpanSingleton Rₚ Mₚ x) (le_of_eq hx)
  have inj1 : Function.Injective i :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq hx.symm))
  let f := i.comp to_res
  have f_ne0 : f ≠ 0 := by
    by_contra eq0
    absurd hg
    apply LinearMap.ext
    intro np'
    induction' np' using Submodule.Quotient.induction_on with np
    show to_res np = 0
    apply inj1
    show f np = _
    simp [eq0]
  absurd hom0
  let _ := Module.finitePresentation_of_finite R N
  contrapose! f_ne0
  exact (Module.FinitePresentation.linearEquivMapExtendScalars
    p'.asIdeal.primeCompl).symm.map_eq_zero_iff.mp (Subsingleton.eq_zero _)

lemma exist_mem_ann_isSMulRegular_of_hom_subsingleton [IsNoetherianRing R]
    [Module.Finite R M] [Module.Finite R N] (hom0 : Subsingleton (N →ₗ[R] M)) :
    ∃ r ∈ Module.annihilator R N, IsSMulRegular M r := by
  by_cases htrivial : Subsingleton M
  · use 0
    constructor
    · exact Submodule.zero_mem (Module.annihilator R N)
    · exact IsSMulRegular.zero
  · let _ : Nontrivial M := not_subsingleton_iff_nontrivial.mp htrivial
    exact exist_mem_ann_isSMulRegular_of_hom_subsingleton_nontrivial hom0
