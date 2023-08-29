/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Alex J. Best, Johan Commelin, Eric Rodriguez, Ruben Van de Velde
-/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.ZMod.Algebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois
import Mathlib.FieldTheory.SplittingField.IsSplittingField

#align_import field_theory.finite.galois_field from "leanprover-community/mathlib"@"0723536a0522d24fc2f159a096fb3304bef77472"

/-!
# Galois fields

If `p` is a prime number, and `n` a natural number,
then `GaloisField p n` is defined as the splitting field of `X^(p^n) - X` over `ZMod p`.
It is a finite field with `p ^ n` elements.

## Main definition

* `GaloisField p n` is a field with `p ^ n` elements

## Main Results

- `GaloisField.algEquivGaloisField`: Any finite field is isomorphic to some Galois field
- `FiniteField.algEquivOfCardEq`: Uniqueness of finite fields : algebra isomorphism
- `FiniteField.ringEquivOfCardEq`: Uniqueness of finite fields : ring isomorphism

-/


noncomputable section


open Polynomial Finset

open scoped Polynomial

instance FiniteField.isSplittingField_sub (K F : Type*) [Field K] [Fintype K]
    [Field F] [Algebra F K] : IsSplittingField F K (X ^ Fintype.card K - X) where
  splits' := by
    have h : (X ^ Fintype.card K - X : K[X]).natDegree = Fintype.card K :=
      FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card
    rw [← splits_id_iff_splits, splits_iff_card_roots, Polynomial.map_sub, Polynomial.map_pow,
      map_X, h, FiniteField.roots_X_pow_card_sub_X K, ← Finset.card_def, Finset.card_univ]
  adjoin_rootSet' := by
    classical
    trans Algebra.adjoin F ((roots (X ^ Fintype.card K - X : K[X])).toFinset : Set K)
    · simp only [rootSet, Polynomial.map_pow, map_X, Polynomial.map_sub]
    · rw [FiniteField.roots_X_pow_card_sub_X, val_toFinset, coe_univ, Algebra.adjoin_univ]
#align finite_field.has_sub.sub.polynomial.is_splitting_field FiniteField.isSplittingField_sub

theorem galois_poly_separable {K : Type*} [Field K] (p q : ℕ) [CharP K p] (h : p ∣ q) :
    Separable (X ^ q - X : K[X]) := by
  use 1, X ^ q - X - 1
  -- ⊢ 1 * (X ^ q - X) + (X ^ q - X - 1) * ↑derivative (X ^ q - X) = 1
  rw [← CharP.cast_eq_zero_iff K[X] p] at h
  -- ⊢ 1 * (X ^ q - X) + (X ^ q - X - 1) * ↑derivative (X ^ q - X) = 1
  rw [derivative_sub, derivative_X_pow, derivative_X, C_eq_nat_cast, h]
  -- ⊢ 1 * (X ^ q - X) + (X ^ q - X - 1) * (0 * X ^ (q - 1) - 1) = 1
  ring
  -- 🎉 no goals
#align galois_poly_separable galois_poly_separable

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- A finite field with `p ^ n` elements.
Every field with the same cardinality is (non-canonically)
isomorphic to this field. -/
def GaloisField  := SplittingField (X ^ p ^ n - X : (ZMod p)[X])
-- deriving Field -- Porting note: see https://github.com/leanprover-community/mathlib4/issues/5020
#align galois_field GaloisField

instance : Field (GaloisField p n) :=
  inferInstanceAs (Field (SplittingField _))

instance : Inhabited (@GaloisField 2 (Fact.mk Nat.prime_two) 1) := ⟨37⟩

namespace GaloisField

variable (p : ℕ) [h_prime : Fact p.Prime] (n : ℕ)

instance : Algebra (ZMod p) (GaloisField p n) := SplittingField.algebra _

instance : IsSplittingField (ZMod p) (GaloisField p n) (X ^ p ^ n - X) :=
  Polynomial.IsSplittingField.splittingField _

instance : CharP (GaloisField p n) p :=
  (Algebra.charP_iff (ZMod p) (GaloisField p n) p).mp (by infer_instance)
                                                          -- 🎉 no goals

instance : FiniteDimensional (ZMod p) (GaloisField p n) := by
  dsimp only [GaloisField]; infer_instance
  -- ⊢ FiniteDimensional (ZMod p) (SplittingField (X ^ p ^ n - X))
                            -- 🎉 no goals

instance : Fintype (GaloisField p n) := by
  dsimp only [GaloisField]
  -- ⊢ Fintype (SplittingField (X ^ p ^ n - X))
  exact FiniteDimensional.fintypeOfFintype (ZMod p) (GaloisField p n)
  -- 🎉 no goals

theorem finrank {n} (h : n ≠ 0) : FiniteDimensional.finrank (ZMod p) (GaloisField p n) = n := by
  set g_poly := (X ^ p ^ n - X : (ZMod p)[X])
  -- ⊢ FiniteDimensional.finrank (ZMod p) (GaloisField p n) = n
  have hp : 1 < p := h_prime.out.one_lt
  -- ⊢ FiniteDimensional.finrank (ZMod p) (GaloisField p n) = n
  have aux : g_poly ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero _ h hp
  -- ⊢ FiniteDimensional.finrank (ZMod p) (GaloisField p n) = n
  -- Porting note : in the statment of `key`, replaced `g_poly` by its value otherwise the
  -- proof fails
  have key : Fintype.card (g_poly.rootSet (GaloisField p n)) = g_poly.natDegree :=
    card_rootSet_eq_natDegree (galois_poly_separable p _ (dvd_pow (dvd_refl p) h))
      (SplittingField.splits (X ^ p ^ n - X : (ZMod p)[X]))
  have nat_degree_eq : g_poly.natDegree = p ^ n :=
    FiniteField.X_pow_card_pow_sub_X_natDegree_eq _ h hp
  rw [nat_degree_eq] at key
  -- ⊢ FiniteDimensional.finrank (ZMod p) (GaloisField p n) = n
  suffices g_poly.rootSet (GaloisField p n) = Set.univ by
    simp_rw [this, ← Fintype.ofEquiv_card (Equiv.Set.univ _)] at key
    -- Porting note: prevents `card_eq_pow_finrank` from using a wrong instance for `Fintype`
    rw [@card_eq_pow_finrank (ZMod p) _ _ _ _ _ (_), ZMod.card] at key
    exact Nat.pow_right_injective (Nat.Prime.one_lt' p).out key
  rw [Set.eq_univ_iff_forall]
  -- ⊢ ∀ (x : GaloisField p n), x ∈ rootSet g_poly (GaloisField p n)
  suffices ∀ (x) (hx : x ∈ (⊤ : Subalgebra (ZMod p) (GaloisField p n))),
      x ∈ (X ^ p ^ n - X : (ZMod p)[X]).rootSet (GaloisField p n)
    by simpa
  rw [← SplittingField.adjoin_rootSet]
  -- ⊢ ∀ (x : GaloisField p n), x ∈ Algebra.adjoin (ZMod p) (rootSet (X ^ p ^ n - X …
  simp_rw [Algebra.mem_adjoin_iff]
  -- ⊢ ∀ (x : GaloisField p n), x ∈ Subring.closure (Set.range ↑(algebraMap (ZMod p …
  intro x hx
  -- ⊢ x ∈ rootSet (X ^ p ^ n - X) (GaloisField p n)
  -- We discharge the `p = 0` separately, to avoid typeclass issues on `ZMod p`.
  cases p; cases hp
  -- ⊢ x ∈ rootSet (X ^ Nat.zero ^ n - X) (GaloisField Nat.zero n)
           -- ⊢ x ∈ rootSet (X ^ Nat.succ n✝ ^ n - X) (GaloisField (Nat.succ n✝) n)
  refine Subring.closure_induction hx ?_ ?_ ?_ ?_ ?_ ?_ <;> simp_rw [mem_rootSet_of_ne aux]
                                                            -- ⊢ ∀ (x : GaloisField (Nat.succ n✝) n), x ∈ Set.range ↑(algebraMap (ZMod (Nat.s …
                                                            -- ⊢ ↑(aeval 0) (X ^ Nat.succ n✝ ^ n - X) = 0
                                                            -- ⊢ ↑(aeval 1) (X ^ Nat.succ n✝ ^ n - X) = 0
                                                            -- ⊢ ∀ (x y : GaloisField (Nat.succ n✝) n), ↑(aeval x) (X ^ Nat.succ n✝ ^ n - X)  …
                                                            -- ⊢ ∀ (x : GaloisField (Nat.succ n✝) n), ↑(aeval x) (X ^ Nat.succ n✝ ^ n - X) =  …
                                                            -- ⊢ ∀ (x y : GaloisField (Nat.succ n✝) n), ↑(aeval x) (X ^ Nat.succ n✝ ^ n - X)  …
  · rintro x (⟨r, rfl⟩ | hx)
    -- ⊢ ↑(aeval (↑(algebraMap (ZMod (Nat.succ n✝)) (GaloisField (Nat.succ n✝) n)) r) …
    · simp only [map_sub, map_pow, aeval_X]
      -- ⊢ ↑(algebraMap (ZMod (Nat.succ n✝)) (GaloisField (Nat.succ n✝) n)) r ^ Nat.suc …
      rw [← map_pow, ZMod.pow_card_pow, sub_self]
      -- 🎉 no goals
    · dsimp only [GaloisField] at hx
      -- ⊢ ↑(aeval x) (X ^ Nat.succ n✝ ^ n - X) = 0
      rwa [mem_rootSet_of_ne aux] at hx
      -- 🎉 no goals
  · rw [← coeff_zero_eq_aeval_zero']
    -- ⊢ ↑(algebraMap (ZMod (Nat.succ n✝)) (GaloisField (Nat.succ n✝) n)) (coeff (X ^ …
    simp only [coeff_X_pow, coeff_X_zero, sub_zero, _root_.map_eq_zero, ite_eq_right_iff,
      one_ne_zero, coeff_sub]
    intro hn
    -- ⊢ False
    exact Nat.not_lt_zero 1 (pow_eq_zero hn.symm ▸ hp)
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
  · simp only [aeval_X_pow, aeval_X, AlgHom.map_sub, add_pow_char_pow, sub_eq_zero]
    -- ⊢ ∀ (x y : GaloisField (Nat.succ n✝) n), x ^ Nat.succ n✝ ^ n = x → y ^ Nat.suc …
    intro x y hx hy
    -- ⊢ x ^ Nat.succ n✝ ^ n + y ^ Nat.succ n✝ ^ n = x + y
    rw [hx, hy]
    -- 🎉 no goals
  · intro x hx
    -- ⊢ ↑(aeval (-x)) (X ^ Nat.succ n✝ ^ n - X) = 0
    simp only [sub_eq_zero, aeval_X_pow, aeval_X, AlgHom.map_sub, sub_neg_eq_add] at *
    -- ⊢ (-x) ^ Nat.succ n✝ ^ n + x = 0
    rw [neg_pow, hx, CharP.neg_one_pow_char_pow]
    -- ⊢ -1 * x + x = 0
    simp
    -- 🎉 no goals
  · simp only [aeval_X_pow, aeval_X, AlgHom.map_sub, mul_pow, sub_eq_zero]
    -- ⊢ ∀ (x y : GaloisField (Nat.succ n✝) n), x ^ Nat.succ n✝ ^ n = x → y ^ Nat.suc …
    intro x y hx hy
    -- ⊢ x ^ Nat.succ n✝ ^ n * y ^ Nat.succ n✝ ^ n = x * y
    rw [hx, hy]
    -- 🎉 no goals
#align galois_field.finrank GaloisField.finrank

theorem card (h : n ≠ 0) : Fintype.card (GaloisField p n) = p ^ n := by
  let b := IsNoetherian.finsetBasis (ZMod p) (GaloisField p n)
  -- ⊢ Fintype.card (GaloisField p n) = p ^ n
  rw [Module.card_fintype b, ← FiniteDimensional.finrank_eq_card_basis b, ZMod.card, finrank p h]
  -- 🎉 no goals
#align galois_field.card GaloisField.card

theorem splits_zmod_X_pow_sub_X : Splits (RingHom.id (ZMod p)) (X ^ p - X) := by
  have hp : 1 < p := h_prime.out.one_lt
  -- ⊢ Splits (RingHom.id (ZMod p)) (X ^ p - X)
  have h1 : roots (X ^ p - X : (ZMod p)[X]) = Finset.univ.val := by
    convert FiniteField.roots_X_pow_card_sub_X (ZMod p)
    exact (ZMod.card p).symm
  have h2 := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp
  -- ⊢ Splits (RingHom.id (ZMod p)) (X ^ p - X)
  -- We discharge the `p = 0` separately, to avoid typeclass issues on `ZMod p`.
  cases p; cases hp
  -- ⊢ Splits (RingHom.id (ZMod Nat.zero)) (X ^ Nat.zero - X)
           -- ⊢ Splits (RingHom.id (ZMod (Nat.succ n✝))) (X ^ Nat.succ n✝ - X)
  rw [splits_iff_card_roots, h1, ← Finset.card_def, Finset.card_univ, h2, ZMod.card]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align galois_field.splits_zmod_X_pow_sub_X GaloisField.splits_zmod_X_pow_sub_X

/-- A Galois field with exponent 1 is equivalent to `ZMod` -/
def equivZmodP : GaloisField p 1 ≃ₐ[ZMod p] ZMod p :=
  let h : (X ^ p ^ 1 : (ZMod p)[X]) = X ^ Fintype.card (ZMod p) := by rw [pow_one, ZMod.card p]
                                                                      -- 🎉 no goals
  let inst : IsSplittingField (ZMod p) (ZMod p) (X ^ p ^ 1 - X) := by rw [h]; infer_instance
                                                                      -- ⊢ IsSplittingField (ZMod p) (ZMod p) (X ^ Fintype.card (ZMod p) - X)
                                                                              -- 🎉 no goals
  (@IsSplittingField.algEquiv _ (ZMod p) _ _ _ (X ^ p ^ 1 - X : (ZMod p)[X]) inst).symm
#align galois_field.equiv_zmod_p GaloisField.equivZmodP

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod p) K]

theorem splits_X_pow_card_sub_X : Splits (algebraMap (ZMod p) K) (X ^ Fintype.card K - X) :=
  (FiniteField.isSplittingField_sub K (ZMod p)).splits
set_option linter.uppercaseLean3 false in
#align galois_field.splits_X_pow_card_sub_X GaloisField.splits_X_pow_card_sub_X

theorem isSplittingField_of_card_eq (h : Fintype.card K = p ^ n) :
    IsSplittingField (ZMod p) K (X ^ p ^ n - X) :=
  h ▸ FiniteField.isSplittingField_sub K (ZMod p)
#align galois_field.is_splitting_field_of_card_eq GaloisField.isSplittingField_of_card_eq

instance (priority := 100) {K K' : Type*} [Field K] [Field K'] [Finite K'] [Algebra K K'] :
    IsGalois K K' := by
  cases nonempty_fintype K'
  -- ⊢ IsGalois K K'
  obtain ⟨p, hp⟩ := CharP.exists K
  -- ⊢ IsGalois K K'
  haveI : CharP K p := hp
  -- ⊢ IsGalois K K'
  haveI : CharP K' p := charP_of_injective_algebraMap' K K' p
  -- ⊢ IsGalois K K'
  exact IsGalois.of_separable_splitting_field
    (galois_poly_separable p (Fintype.card K')
      (let ⟨n, _, hn⟩ := FiniteField.card K' p
      hn.symm ▸ dvd_pow_self p n.ne_zero))

/-- Any finite field is (possibly non canonically) isomorphic to some Galois field. -/
def algEquivGaloisField (h : Fintype.card K = p ^ n) : K ≃ₐ[ZMod p] GaloisField p n :=
  haveI := isSplittingField_of_card_eq _ _ h
  IsSplittingField.algEquiv _ _
#align galois_field.alg_equiv_galois_field GaloisField.algEquivGaloisField

end GaloisField

namespace FiniteField

variable {K : Type*} [Field K] [Fintype K] {K' : Type*} [Field K'] [Fintype K']

/-- Uniqueness of finite fields:
  Any two finite fields of the same cardinality are (possibly non canonically) isomorphic-/
def algEquivOfCardEq (p : ℕ) [h_prime : Fact p.Prime] [Algebra (ZMod p) K] [Algebra (ZMod p) K']
    (hKK' : Fintype.card K = Fintype.card K') : K ≃ₐ[ZMod p] K' := by
  have : CharP K p := by rw [← Algebra.charP_iff (ZMod p) K p]; exact ZMod.charP p
  -- ⊢ K ≃ₐ[ZMod p] K'
  have : CharP K' p := by rw [← Algebra.charP_iff (ZMod p) K' p]; exact ZMod.charP p
  -- ⊢ K ≃ₐ[ZMod p] K'
  choose n a hK using FiniteField.card K p
  -- ⊢ K ≃ₐ[ZMod p] K'
  choose n' a' hK' using FiniteField.card K' p
  -- ⊢ K ≃ₐ[ZMod p] K'
  rw [hK, hK'] at hKK'
  -- ⊢ K ≃ₐ[ZMod p] K'
  have hGalK := GaloisField.algEquivGaloisField p n hK
  -- ⊢ K ≃ₐ[ZMod p] K'
  have hK'Gal := (GaloisField.algEquivGaloisField p n' hK').symm
  -- ⊢ K ≃ₐ[ZMod p] K'
  rw [Nat.pow_right_injective h_prime.out.one_lt hKK'] at *
  -- ⊢ K ≃ₐ[ZMod p] K'
  exact AlgEquiv.trans hGalK hK'Gal
  -- 🎉 no goals
#align finite_field.alg_equiv_of_card_eq FiniteField.algEquivOfCardEq

/-- Uniqueness of finite fields:
  Any two finite fields of the same cardinality are (possibly non canonically) isomorphic-/
def ringEquivOfCardEq (hKK' : Fintype.card K = Fintype.card K') : K ≃+* K' := by
  choose p _char_p_K using CharP.exists K
  -- ⊢ K ≃+* K'
  choose p' _char_p'_K' using CharP.exists K'
  -- ⊢ K ≃+* K'
  choose n hp hK using FiniteField.card K p
  -- ⊢ K ≃+* K'
  choose n' hp' hK' using FiniteField.card K' p'
  -- ⊢ K ≃+* K'
  have hpp' : p = p' := by
    by_contra hne
    have h2 := Nat.coprime_pow_primes n n' hp hp' hne
    rw [(Eq.congr hK hK').mp hKK', Nat.coprime_self, pow_eq_one_iff (PNat.ne_zero n')] at h2
    exact Nat.Prime.ne_one hp' h2
  rw [← hpp'] at _char_p'_K'
  -- ⊢ K ≃+* K'
  haveI := fact_iff.2 hp
  -- ⊢ K ≃+* K'
  letI : Algebra (ZMod p) K := ZMod.algebra _ _
  -- ⊢ K ≃+* K'
  letI : Algebra (ZMod p) K' := ZMod.algebra _ _
  -- ⊢ K ≃+* K'
  exact ↑(algEquivOfCardEq p hKK')
  -- 🎉 no goals
#align finite_field.ring_equiv_of_card_eq FiniteField.ringEquivOfCardEq

end FiniteField
