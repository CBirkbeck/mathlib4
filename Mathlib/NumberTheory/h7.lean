/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.NumberField.House
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Analysis.Analytic.IteratedFDeriv

set_option autoImplicit true
set_option linter.style.multiGoal false
set_option linter.style.cases false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
    Matrix Set Polynomial Finset IntermediateField

noncomputable section

lemma ExistsAlgInt {K : Type*} [Field K] [NumberField K] (α : K) :
  ∃ k : ℤ, k ≠ 0 ∧ IsIntegral ℤ (k • α) := by
  obtain ⟨y, hy, hf⟩ := exists_integral_multiples ℤ ℚ (L := K) {α}
  refine ⟨y, hy, hf α (mem_singleton_self _)⟩

def c'_both {K : Type*} [Field K] [NumberField K] (α : K) :
   {c : ℤ | c ≠ 0 ∧ IsIntegral ℤ (c • α)} :=
  ⟨(ExistsAlgInt α).choose, (ExistsAlgInt α).choose_spec⟩

lemma adjoin_le_adjoin_more (α β : ℂ) (_ : IsAlgebraic ℚ α) (_ : IsAlgebraic ℚ β) :
  (adjoin _ {α} ≤ adjoin ℚ {α, β}) ∧ (adjoin _ {β} ≤ adjoin ℚ {α, β}) :=
  ⟨by apply adjoin.mono; intros x hx; left; exact hx,
   by apply adjoin.mono; intros x hx; right; exact hx⟩

lemma isNumberField_adjoin_alg_numbers (α β γ : ℂ)
  (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β) (hγ : IsAlgebraic ℚ γ) :
    NumberField (adjoin ℚ {α, β, γ}) :=  {
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  to_finiteDimensional := finiteDimensional_adjoin (fun x hx => by
    cases' hx with ha hb; · simp_rw [ha, isAlgebraic_iff_isIntegral.1 hα]
    cases' hb with hb hc; · simp_rw [hb, isAlgebraic_iff_isIntegral.1 hβ]
    simp_rw [mem_singleton_iff.1 hc, isAlgebraic_iff_isIntegral.1 hγ])}

lemma getElemsInNF (α β γ : ℂ) (hα : IsAlgebraic ℚ α)
    (hβ : IsAlgebraic ℚ β) (hγ : IsAlgebraic ℚ γ) :
      ∃ (K : Type) (_ : Field K) (_ : NumberField K)
      (σ : K →+* ℂ) (_ : DecidableEq (K →+* ℂ)),
    ∃ (α' β' γ' : K), α = σ α' ∧ β = σ β' ∧ γ = σ γ' := by
  have  hab := adjoin.mono ℚ {α, β} {α, β, γ}
    fun x hxab => by cases' hxab with hxa hxb; left; exact hxa; right; left; exact hxb
  have hac := adjoin.mono ℚ {α, γ} {α, β, γ}
    fun x hx => by cases' hx with hsf hff; left; exact hsf; right; right; exact hff
  use adjoin ℚ {α, β, γ}
  constructor
  use isNumberField_adjoin_alg_numbers α β γ hα hβ hγ
  use { toFun := fun x => x.1, map_one' := rfl, map_mul' := fun x y => rfl
        map_zero' := rfl, map_add' := fun x y => rfl}
  use Classical.typeDecidableEq (↥ℚ⟮α, β, γ⟯ →+* ℂ)
  simp only [exists_and_left, exists_and_right, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, Subtype.exists, exists_prop, exists_eq_right']
  exact ⟨adjoin_simple_le_iff.1 fun _ hx =>
     hab ((adjoin_le_adjoin_more α β hα hβ).1 hx),
    adjoin_simple_le_iff.1 fun _ hx =>  hab (by
    apply adjoin.mono; intros x hx;
    · right; exact hx;
    · exact hx),
    adjoin_simple_le_iff.1 fun _ hx =>
    hac ((adjoin_le_adjoin_more α γ hα hγ).2 hx)⟩

variable (K : Type) [Field K]

lemma IsIntegral_assoc {x y : ℤ} (z : ℤ) (α : K) (ha : IsIntegral ℤ (z • α)) :
  IsIntegral ℤ ((x * y * z : ℤ) • α) := by
  have : ((x * y * z : ℤ) • α) = (x * y) • (z • α) := by
    simp only [Int.cast_mul, zsmul_eq_mul, mul_assoc (↑x * ↑y : K) z α]
  conv => enter [2]; rw [this]
  apply IsIntegral.smul _ ha

lemma IsIntegral.Cast (a : ℤ) : IsIntegral ℤ (a : K) :=
  map_isIntegral_int (algebraMap ℤ K) (Algebra.IsIntegral.isIntegral _)

lemma IsIntegral.Nat (a : ℕ) : IsIntegral ℤ (a : K) := by
  have : (a : K) = ((a : ℤ) : K) := by simp only [Int.cast_natCast]
  rw [this]; apply IsIntegral.Cast

lemma triple_comm (a b c : ℤ) (x y z : K) : ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
  simp only [zsmul_eq_mul, Int.cast_mul]; ring

variable (α β : ℂ) (hirr : ∀ i j : ℤ, β ≠ i / j) (htriv : α ≠ 0 ∧ α ≠ 1)

include htriv in
lemma γneq0 : α ^ β ≠ 0 := fun H => by
  simp_all only [Complex.cpow_eq_zero_iff, ne_eq,false_and]

include hirr in
lemma βneq0 : β ≠ 0 := fun H => by apply hirr 0 1; simpa [div_one];

variable (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β)
  (σ : K →+* ℂ)
  (hdec : DecidableEq (K →+* ℂ))
  (α' β' γ' : K) (habc : α = σ α' ∧ β = σ β' ∧ α ^ β = σ γ')

include habc htriv hirr in
lemma hneq0 : α' ≠ 0 ∧ β' ≠ 0 ∧ γ' ≠ 0 := by
  constructor
  · intros H; apply htriv.1; rwa [habc.1, _root_.map_eq_zero]
  · constructor
    · intros H; apply βneq0 β hirr ; rwa [habc.2.1, _root_.map_eq_zero]
    · intros H; apply γneq0 α β htriv  (by rwa [habc.2.2, _root_.map_eq_zero])

variable [NumberField K]

def c' (α : K) : ℤ := c'_both α

lemma c'_IsIntegral (α : K) : IsIntegral ℤ (c' K α • α) := (c'_both α).2.2

def h := Module.finrank ℚ K

def m := 2 * h K + 2

def c₁ := (c' K α') * (c' K β') * (c' K γ')

lemma c₁_α : IsIntegral ℤ (c₁ K α' β' γ' • α') := by
  have h := IsIntegral_assoc (x := c' K γ') (y := c' K β') K (c' K α') α' (c'_IsIntegral K α')
  rwa [c₁, mul_comm, mul_comm (c' K α') (c' K β'), ← mul_assoc]

lemma c₁_β : IsIntegral ℤ (c₁ K α' β' γ' • β') := by
  have h := IsIntegral_assoc (x := c' K γ') (y := c' K α') K (c' K β') β' (c'_IsIntegral K β')
  rwa [c₁, mul_comm, ← mul_assoc]

lemma c₁_γ : IsIntegral ℤ (c₁ K α' β' γ' • γ') :=
  IsIntegral_assoc (x := c' K α') (y := c' K β') K (c' K γ') γ' (c'_IsIntegral K γ')

lemma c₁b  (n : ℕ) : 1 ≤ n → k ≤ n - 1 → 1 ≤ (a : ℕ) → 1 ≤ (b : ℕ) →
  IsIntegral ℤ ((c₁ K α' β' γ')^(n - 1) • (a + b • β') ^ k) := by  {
  intros hn hkn ha hb
  have : (c₁ K α' β' γ')^(n - 1) = (c₁ K α' β' γ')^(n - 1 - k) * (c₁ K α' β' γ')^k := by {
    simp_all only [← pow_add, Nat.sub_add_cancel]}
  rw [this]
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, nsmul_eq_mul, mul_assoc]
  apply IsIntegral.mul
  · apply IsIntegral.pow
    · apply IsIntegral.Cast
  rw [← mul_pow]
  apply IsIntegral.pow
  rw [mul_add]
  apply IsIntegral.add
  · apply IsIntegral.mul <| IsIntegral.Cast _ _
    · apply IsIntegral.Nat
  rw [mul_comm, mul_assoc]
  apply IsIntegral.mul <| IsIntegral.Nat _ _
  rw [mul_comm, ← zsmul_eq_mul]
  exact c₁_β K α' β' γ'}

lemma c₁ac (u : K) (n k a l : ℕ) (hnk : a*l ≤ n*k) (H : IsIntegral ℤ (↑(c₁ K α' β' γ') * u)) :
  IsIntegral ℤ ((c₁ K α' β' γ')^(n*k) • u ^ (a*l)) := by
  have : (c₁ K α' β' γ') ^ (n * k) = (c₁ K α' β' γ') ^ (n * k - a * l)*(c₁ K α' β' γ')^(a*l) := by
    rw [← pow_add]; simp_all only [Nat.sub_add_cancel]
  rw[this, zsmul_eq_mul]
  simp only [Int.cast_mul, Int.cast_pow, nsmul_eq_mul]; rw [mul_assoc]
  apply IsIntegral.mul; apply IsIntegral.pow; apply IsIntegral.Cast
  rw [← mul_pow]; exact IsIntegral.pow H _

variable (q : ℕ) (h2mq : 2 * m K ∣ q ^ 2)

def n := q^2 / (2 * m K)

variable (u : Fin (m  K) × Fin (n K q)) (t : Fin q × Fin q) (hq0 : 0 < q)

open Nat in include hq0 in
lemma c1a : IsIntegral ℤ ((c₁ K α' β' γ')^(m K*q) • (α'^( (t.1 + 1) * (u.1 + 1) : ℕ))) := by
  apply c₁ac K α' β' γ' α' (m K) q (t.1 + 1) (u.1 + 1) ?_ ?_
  · rw [mul_comm]
    exact Nat.mul_le_mul
      (add_le_of_le_sub (le_of_ble_eq_true rfl) (le_sub_one_of_lt u.1.isLt))
      (add_le_of_le_sub hq0 (le_sub_one_of_lt t.1.isLt))
  · rw [← zsmul_eq_mul]; exact c₁_α K α' β' γ'

open Nat in include hq0 in
lemma c1c : IsIntegral ℤ ((c₁ K α' β' γ') ^ (m K*q) • (γ'^((t.2 + 1) * (u.1 + 1) : ℕ))) := by
  apply c₁ac K α' β' γ' γ' (m K) q (t.2 + 1) (u.1 + 1) ?_ ?_
  · rw [mul_comm]
    exact Nat.mul_le_mul
      (add_le_of_le_sub (le_of_ble_eq_true rfl) (le_sub_one_of_lt u.1.isLt))
        (add_le_of_le_sub hq0 (le_sub_one_of_lt t.2.isLt))
  · rw [← zsmul_eq_mul]; exact c₁_γ K α' β' γ'

def sys_coeffs : (Fin q × Fin q) → (Fin (m  K) × Fin (n K q)) → K := fun (a,b) (l,k) =>
  ((a+1 : ℕ) + (b+1 : ℕ) • β')^(k : ℕ) * α' ^((a+1) * (l+1 : ℕ)) * γ' ^((b+1) * (l+1 : ℕ))

-- def η : (Fin q × Fin q) → (Fin (m  K) × Fin (n K q)) → K := fun (a,b) (l,k) =>
--   ((a+1) + (b+1) * β')^(k : ℤ) * α' ^((a+1) * (l+1 : ℤ)) * γ' ^((b+1) * (l+1 : ℤ))

include hq0 h2mq in
lemma one_le_n : 1 ≤ n K q := by {
  simp only [n]
  rw [Nat.one_le_div_iff]
  · apply Nat.le_of_dvd (Nat.pow_pos hq0) h2mq
  · exact Nat.zero_lt_succ (Nat.mul 2 (2 * h K + 1) + 1)}

abbrev c_coeffs := (c₁ K α' β' γ')^(n K q - 1) *
  (c₁ K α' β' γ')^(m K * q) * ((c₁ K α' β' γ')^(m K * q))

open Nat in include hq0 h2mq in
lemma c₁IsInt : IsIntegral ℤ (((c_coeffs K α' β' γ' q)) • sys_coeffs K α' β' γ' q t u) := by
  simp only [sys_coeffs]
  rw [triple_comm K
    ((c₁ K α' β' γ')^(n K q - 1) : ℤ)
    ((c₁ K α' β' γ')^(m K * q) : ℤ)
    ((c₁ K α' β' γ')^(m K * q) : ℤ)
    (((t.1 + 1 : ℕ) + (t.2 + 1 : ℕ) • β')^(u.2 : ℕ))
    (α' ^ (((t.1 : ℕ) + 1) * (u.1 + 1)))
    (γ' ^ (((t.2 : ℕ) + 1) * (u.1 + 1)))]
  rw [mul_assoc]
  apply IsIntegral.mul
  · exact c₁b K α' β' γ' (n K q) (one_le_n K q h2mq hq0)
      (le_sub_one_of_lt u.2.isLt) (le_add_left 1 ↑t.1) (le_add_left 1 ↑t.2)
  · exact IsIntegral.mul (c1a K α' β' γ' q u t hq0) (c1c K α' β' γ' q u t hq0)

lemma c₁neq0 : c₁ K α' β' γ' ≠ 0 := by
  unfold c₁
  have hcα := (c'_both α').2.1
  have hcβ := (c'_both β').2.1
  have hcγ := (c'_both γ').2.1
  unfold c'
  simp_all only [ne_eq, mem_setOf_eq, mul_eq_zero, or_self, not_false_eq_true]

lemma c_coeffs_neq_zero : c_coeffs K α' β' γ' q ≠ 0 :=
  mul_ne_zero (mul_ne_zero (pow_ne_zero _ (c₁neq0 K α' β' γ'))
    (pow_ne_zero _ (c₁neq0 K α' β' γ'))) (pow_ne_zero _ (c₁neq0 K α' β' γ'))

-- variable (k' : ℤ) (hkneq0 : k' ≠ 0)
-- (sys_coeffs_int : IsIntegral ℤ (k' • sys_coeffs K α' β' γ' q t u))

def A : Matrix (Fin (m K) × Fin (n K q)) (Fin q × Fin q) (𝓞 K) :=
  fun (l,k) (a,b) => RingOfIntegers.restrict _
   (fun _ => (c₁IsInt K α' β' γ' q h2mq (l,k) (a,b) hq0)) ℤ

include hirr htriv habc in
lemma β'ne_zero : β' ≠ 0 := by
  sorry


include hirr htriv habc  in
lemma eta_ne_zero : sys_coeffs K α' β' γ' q t u ≠ 0 := by
  unfold sys_coeffs
  simp only [mul_eq_zero, pow_eq_zero_iff', not_or, not_and, Decidable.not_not]
  have h1 : α' ^ ((↑↑t.1 + 1) * (↑↑u.1 + 1)) ≠ 0 := by
    intros H
    apply (hneq0 K α β hirr htriv σ α' β' γ' habc).1
    exact pow_eq_zero H
  have h3: γ' ^ ((↑↑t.2 + 1) * (↑↑u.1 + 1)) ≠ 0 := by
    intros H
    apply (hneq0 K α β hirr htriv σ α' β' γ' habc).2.2
    norm_cast at H
    exact pow_eq_zero H
  have h2 : (↑↑t.1 + 1 + (↑↑t.2 + 1) • (β')) ^ ↑↑u.2 ≠ 0 := by
    apply pow_ne_zero
    --have h1: ↑↑t.1 + (1 : K) ≠ 0 := Nat.cast_add_one_ne_zero ↑t.1
    have h2 : (↑↑t.2 + (1 : K)) ≠ 0 := Nat.cast_add_one_ne_zero ↑t.2
    have :(↑t.2 + 1 : ℕ) • β' ≠ 0 := by
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      exact mul_ne_zero (Nat.cast_add_one_ne_zero t.2)
        ((hneq0 K α β hirr htriv σ α' β' γ' habc).2.1)
    --intros H
    specialize hirr (↑t.1 + 1) (-↑t.2 + 1)
    intros H
    apply hirr
    rw [← eq_neg_iff_add_eq_zero] at H
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_neg]
    rw [habc.2.1]
    have := hneq0 K α β hirr htriv σ α' β' γ' habc
    sorry
  rw [mul_assoc]
  apply mul_ne_zero (mod_cast h2)
  apply mul_ne_zero (mod_cast h1)
  exact mod_cast h3

include hirr htriv habc u t in
lemma hM_neq0 : A K α' β' γ' q h2mq hq0 ≠ 0 := by
  simp (config := { unfoldPartialApp := true }) only [A]
  rw [Ne, funext_iff]
  simp only [zpow_natCast, zsmul_eq_mul]
  simp only [RingOfIntegers.restrict,
    zpow_natCast, zsmul_eq_mul, RingOfIntegers.map_mk]
  intros H
  specialize H u
  rw [funext_iff] at H
  specialize H t
  simp only [Int.cast_mul, Int.cast_pow, Prod.mk.eta, zero_apply] at H
  injection H with H
  simp only [mul_eq_zero, pow_eq_zero_iff', Int.cast_eq_zero, ne_eq, not_or, or_self_right] at H
  cases' H with H1 H2
  · cases' H1 with H1 H11
    rcases H1 with ⟨H1, H11⟩
    · apply c₁neq0 K α' β' γ'
      exact H1
    · apply c₁neq0 K α' β' γ'
      exact H11.1
  · unfold sys_coeffs at H2
    simp only [Nat.cast_add, Nat.cast_one, nsmul_eq_mul, mul_eq_zero, pow_eq_zero_iff', ne_eq,
      AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, or_self, not_false_eq_true,
      pow_eq_zero_iff] at H2
    cases' H2 with H2 H22
    · obtain ⟨H2, H22⟩ := H2
      have h1 : ↑↑t.1 + 1 > 0 := Nat.zero_lt_succ ↑t.1
      have h2 : (↑↑t.2 + 1) > 0 := Nat.zero_lt_succ ↑t.2
      have : β' ≠ 0 := by {
        apply (hneq0 K α β hirr htriv σ α' β' γ' habc).2.1
      }
      sorry
      apply (hneq0 K α β hirr htriv σ α' β' γ' habc).1
      simp_all only [ne_eq, map_zero, not_true_eq_false, zero_ne_one, not_false_eq_true, and_true]
    · obtain ⟨H2, H22⟩ := H22
      apply (hneq0 K α β hirr htriv σ α' β' γ' habc).2.2
      exact H2

  -- have : (c_coeffs K α' β' γ' q) * sys_coeffs K α' β' γ' q t u ≠ 0 := by
  --   apply mul_ne_zero_iff.2
  --   constructor
  --   simp only [ne_eq, Int.cast_eq_zero]
  --   exact c_coeffs_neq_zero K α' β' γ' q
  --   exact eta_ne_zero K α β hirr htriv σ α' β' γ' habc q u t
  --apply this H

lemma cardmn : Fintype.card (Fin (m K) × Fin (n K q)) = m K * n K q := by
  simp only [card_prod, Fintype.card_fin]

lemma cardqq : card (Fin q × Fin q) = q * q := by
  simp only [card_prod, Fintype.card_fin]

lemma hm : 0 < m K := Nat.zero_lt_succ (2 * h K + 1)

include hq0 h2mq in
lemma h0m : 0 < m K * n K q := mul_pos (hm K) (one_le_n K q h2mq hq0)

include hq0 h2mq in
lemma hmn : m K * n K q < q*q := by
  rw [← Nat.mul_div_eq_iff_dvd] at h2mq
  rw [← pow_two q, ← mul_lt_mul_left (Nat.zero_lt_two)]
  rw [← mul_assoc, n, h2mq, lt_mul_iff_one_lt_left]
  · exact one_lt_two
  · exact Nat.pow_pos hq0

def c₂ : ℝ := (c₁ K α' β' γ') ^ (1 + 2*(m K) * Nat.sqrt (2*(m K)))

-- def c₃ : ℝ := ((c₂ K α' β' γ') * (q + q* house β')*
--   (house α')^(Nat.sqrt (2*m K))*(house γ')^(Nat.sqrt (2*m K)))

abbrev c₃ := max 1 (|↑(c_coeffs K α' β' γ' q)| *
    house ((((t.1 : ℕ) + 1) + ((t.2 : ℕ) + 1) • β') ^ (u.2 : ℕ)) *
    house (α' ^ (((t.1 : ℕ)+1) * ((u.1 : ℕ) + 1))) *
    house (γ' ^ (((t.2 : ℕ) + 1) * ((u.1 : ℕ) + 1))))

include hq0 h2mq in
lemma hMkl : ∀ (k : Fin (m K) × Fin (n K q)) (l : Fin q × Fin q),
  house ((algebraMap ((𝓞 K)) K)
  (A K α' β' γ' q h2mq hq0 k l)) ≤
  (c₃ K α' β' γ' q u t) ^ (n K q : ℝ) * ↑(n K q : ℝ)^(((n K q - 1)/2) : ℝ) := by {
    simp (config := { unfoldPartialApp := true }) only [A, sys_coeffs]
    simp only [RingOfIntegers.restrict, zsmul_eq_mul, RingOfIntegers.map_mk]
    intros u t
    have f : (-1 / 2 + ↑(n K q : ℝ) * (1 / 2)) = (((n K q : ℝ) - 1)/2) := by ring
    calc _ ≤ house (c_coeffs K α' β' γ' q : K) *
       house ((((t.1 : ℕ) + 1) + ((t.2 : ℕ) + 1) • β') ^ (u.2 : ℕ)) *
           house (α' ^ (((t.1 : ℕ)+1) * ((u.1 : ℕ) + 1))) *
           house (γ' ^ (((t.2 : ℕ) + 1) * ((u.1 : ℕ) + 1))) := ?_

        _ ≤  (c₃ K α' β' γ' q u t) := ?_
        _ ≤ (c₃ K α' β' γ' q u t)^(n K q : ℝ) := ?_
        _ ≤ (c₃ K α' β' γ' q u t)^(n K q : ℝ) * ↑(n K q : ℝ)^(((n K q - 1)/2) : ℝ) := ?_

    ·   trans
        apply house_mul_le
        simp only [Int.cast_mul, Int.cast_pow, Nat.cast_add, Nat.cast_one, nsmul_eq_mul, le_refl]
        trans
        apply mul_le_mul_of_nonneg_left
        · rw [mul_assoc]
        apply house_nonneg
        trans
        apply mul_le_mul_of_nonneg_left
        apply house_mul_le
        apply house_nonneg
        trans
        · apply mul_le_mul_of_nonneg_left
          · apply mul_le_mul_of_nonneg_left
            · apply house_mul_le
            apply house_nonneg
          · apply house_nonneg
        rw [← mul_assoc]
        rw [← mul_assoc]
    ·     simp only [house_intCast, Int.cast_abs]
          unfold c₃
          apply le_max_right
    ·   nth_rw 1 [← Real.rpow_one ((c₃ K α' β' γ' q u t))]
        apply Real.rpow_le_rpow_of_exponent_le
        · apply le_max_left
        · simp only [Nat.one_le_cast]; exact one_le_n K q h2mq hq0
    ·     nth_rw  1 [← mul_one (c₃ K α' β' γ' q u t ^ (n K q : ℝ))]
          apply mul_le_mul_of_nonneg_left
          · apply Real.one_le_rpow
            · simp only [Nat.one_le_cast]; exact one_le_n K q h2mq hq0
            · apply div_nonneg
              · simp only [sub_nonneg, Nat.one_le_cast]; exact one_le_n K q h2mq hq0
              · exact zero_le_two
          · apply Real.rpow_nonneg
            · simp only [c₃, Nat.cast_add, Nat.cast_one, le_max_iff, zero_le_one, true_or]
    sorry
              }

-- def c₄ : ℝ := ((c₂ K α' β' γ') * ((q : ℝ) + (q : ℝ) * house β')*
--     (house α')^(Nat.sqrt (2*m K))*(house γ')^(Nat.sqrt (2*m K)))

def applylemma82 := NumberField.house.exists_ne_zero_int_vec_house_le K
  (A K α' β' γ' q h2mq hq0)
  (hM_neq0 K α β hirr htriv σ α' β' γ' habc q h2mq u t hq0)
  (h0m K q h2mq hq0)
  (hmn K q h2mq hq0)
  (cardqq q)
  (hMkl K α' β' γ' q h2mq u t hq0)
  (cardmn K q)

def η : Fin q × Fin q → 𝓞 K :=
  (applylemma82 K α β hirr htriv σ hdec α' β' γ' habc q h2mq u t hq0).choose

def applylemma82_props :=
  (applylemma82 K α β hirr htriv σ hdec α' β' γ' habc q h2mq u t hq0).choose_spec

def bound : η K α β hirr htriv σ hdec α' β' γ' habc q h2mq u t hq0 ≠ 0 :=
  (applylemma82_props K α β hirr htriv σ hdec α' β' γ' habc q h2mq u t hq0).1

def applylemma82_Matrix :
    (A K α' β' γ' q h2mq hq0) *ᵥ
 (η K α β hirr htriv σ hdec α' β' γ' habc q h2mq u t hq0) = 0 :=
  (applylemma82_props K α β hirr htriv σ hdec α' β' γ' habc q h2mq u t hq0).2.1

def applylemma82_bound :=
  ((applylemma82 K α β hirr htriv σ hdec α' β' γ' habc q h2mq u t hq0).choose_spec).2.2

def c₄ := max 1 (house.c₁ K *
  ((house.c₁ K) * ↑(q * q : ℝ) *
  (c₃ K α' β' γ' q u t ^ ↑(n K q : ℝ) * ↑(n K q : ℝ) ^ ((↑(n K q : ℝ) - 1) / 2))) ^
  (↑(m K * n K q : ℝ) / (↑(q * q : ℝ) - ↑(m K * n K q : ℝ))))

open NumberField.house in
include hq0 h2mq hdec hirr htriv habc in
lemma fromapplylemma82_bound : ∃ (η : Fin q × Fin q → 𝓞 K),
  house ((η l).1) ≤ (c₄ K hdec α' β' γ' q u t) ^
    (n K q : ℝ) * ((n K q)^((1/2)*((n K q)+1)) : ℝ) := by
  obtain ⟨η, ⟨htneq0, ⟨hMt0,hbound⟩⟩⟩ :=
  applylemma82 K α β hirr htriv σ hdec α' β' γ' habc q h2mq u t hq0
  use η
  specialize hbound l
  calc _ ≤ (c₄ K hdec α' β' γ' q u t) := by {
    unfold c₄
    simp only [Real.rpow_natCast, le_max_iff]
    right
    exact mod_cast hbound
    }
       _ ≤ (c₄ K hdec α' β' γ' q u t)^(n K q : ℝ) := by {
           nth_rw  1 [← Real.rpow_one (c₄ K hdec α' β' γ' q u t)]
           apply Real.rpow_le_rpow_of_exponent_le
           · apply le_max_left
           simp only [Nat.one_le_cast]
           exact one_le_n K q h2mq hq0}
       _ ≤ (c₄ K hdec α' β' γ' q u t)^(n K q : ℝ) *
            ((n K q)^((1/2)*((n K q) + 1)) : ℝ) := by {
           nth_rw  1 [← mul_one (c₄ K hdec α' β' γ' q u t ^ (n K q : ℝ))]
           apply mul_le_mul_of_nonneg_left
           · simp only [Nat.reduceDiv, zero_mul, pow_zero, le_refl]
           apply Real.rpow_nonneg
           unfold c₄
           simp only [Real.rpow_natCast, le_max_iff, zero_le_one, true_or]}

def ρ : (Fin q × Fin q) → ℂ := fun (a, b) => ((a+1) + (b+1 : ℕ) • β) * Complex.log α

--η

include htriv in
lemma log_zero_zero : Complex.log α ≠ 0 := by {
  rw [Complex.log]
  sorry
}

lemma decompose_ij (i j : Fin (q * q)) : i = j ↔
  ((finProdFinEquiv.symm.1 i).1) = ((finProdFinEquiv.symm.1 j).1) ∧
    ((finProdFinEquiv.symm.1 i).2 : Fin q) = ((finProdFinEquiv.symm.1 j).2) := by
  rcases i with ⟨i1, i2⟩
  rcases j with ⟨j1, j2⟩
  rw [Fin.ext_iff]
  apply Iff.intro
  · intros H
    constructor
    sorry
    sorry
  · sorry
  -- simp only [Fin.ext_iff, Prod.mk.injEq]
  -- constructor
  -- · intro H
  --   constructor
  --   · exact H.1
  --   · exact H.2
  -- · intro H
  --   constructor
  --   · exact H.1
  --   · exact H.2

-- lemma i ≠ j → ρ ... i ≠ ρ ... j
-- needs β irrat and α ≠ 1
include hirr htriv in
lemma hdistinc : ∀ (i j : Fin (q * q)), i ≠ j →
  (ρ α β q (finProdFinEquiv.symm i)) ≠ (ρ α β q (finProdFinEquiv.symm j)) := by
  intros i j hij
  unfold ρ
  simp only [not_or]
  simp only [ne_eq, mul_eq_mul_right_iff, not_or]
  constructor
  · by_cases H : ((finProdFinEquiv.symm.1 i).2) = ((finProdFinEquiv.symm.1 j).2 : ℂ)
    norm_cast at H
    rw [H]
    simp only [Equiv.toFun_as_coe]
    intros H1
    apply hij
    · sorry
    · sorry
  · sorry
    -- ·
def V := vandermonde (fun (t : Fin (q*q)) => ρ α β q (finProdFinEquiv.symm t))

include α β hirr htriv in
lemma vandermonde_det_ne_zero : det (V α β q) ≠ 0 := by
  unfold V
  by_contra H
  rw [Matrix.det_vandermonde_eq_zero_iff] at H
  rcases H with ⟨i, j, ⟨hij, hij'⟩⟩
  have := hdistinc α β hirr htriv q i j
  simp only [ne_eq, Prod.mk.injEq, not_and] at this
  apply this
  intros H'
  · apply hij' H'
  · exact hij

def η' : Fin (q * q) → 𝓞 K := fun t =>
  η K α β hirr htriv σ hdec α' β' γ' habc q h2mq u
    (finProdFinEquiv.symm t) hq0 (finProdFinEquiv.symm t)

def R : (Fin (q*q)) → ℂ → ℂ := fun t x =>
  ∑ t, σ ((η' K α β hirr htriv σ hdec α' β' γ' habc q h2mq u hq0) t)
     * Complex.exp ((ρ α β q (finProdFinEquiv.symm t)) * x)

--fix Fin q × Fin q
include α β hirr htriv in
lemma vecMul_of_R_zero (hR : R K α β hirr htriv σ hdec α' β' γ' habc q h2mq u hq0 = 0) :
  (V α β q).vecMul (fun t => σ ((η' K α β hirr htriv σ
    hdec α' β' γ' habc q h2mq u hq0) t )) = 0 := by
  unfold R at hR
  unfold vecMul
  unfold dotProduct
  simp only [Finset.sum_eq_zero_iff]
  unfold V
  simp only [vandermonde_apply, Pi.zero_apply]
  ext t
  sorry
  -- simp only [Pi.zero_apply]
  -- rw [funext_iff] at hR
  -- have := hR t
  -- rw [funext_iff] at this
  -- specialize this 0
  -- have := applylemma82_Matrix K α β hirr htriv σ
  --   hdec α' β' γ' habc q h2mq u (finProdFinEquiv.symm t) hq0
  -- rw [funext_iff] at this
  -- have := this u
  -- simp only [Pi.zero_apply] at this
  -- unfold mulVec at this
  -- unfold dotProduct at this
  -- simp only [finProdFinEquiv_symm_apply] at this
  -- rw [Finset.sum_eq_zero_iff] at this

lemma η_eq_zero (hR : R K α β hirr htriv σ hdec α' β' γ' habc q h2mq u hq0 = 0) :
    (fun t => σ ((η' K α β hirr htriv σ hdec α' β' γ' habc q h2mq u hq0) t )) = 0 := by
  apply eq_zero_of_vecMul_eq_zero
  apply vandermonde_det_ne_zero α β hirr htriv q
  apply vecMul_of_R_zero K α β hirr htriv σ hdec α' β' γ' habc q h2mq u hq0
  apply hR

-- lemma det V ≠ 0
-- from det_vandermonde_eq_zero_iff
-- but need to navigate Fin q * Fin q

-- R is zero function → lemma V * ηvec = 0
-- by series expansion of R(x) and exponential and sums

-- ηvec = 0
-- linear algebra

include α β hirr htriv in
lemma ηvec_eq_zero
  (hVecMulEq0 : (V α β q).vecMul
      (fun t => σ ((η' K α β hirr htriv σ hdec α' β' γ' habc q h2mq u hq0) t )) = 0) :
       (fun t => σ ((η' K α β hirr htriv σ hdec α' β' γ' habc q h2mq u hq0) t )) = 0 := by {
  have M := vandermonde_det_ne_zero α β hirr htriv q
  apply eq_zero_of_vecMul_eq_zero M hVecMulEq0}

lemma hbound_sigma : ∀ (i : Fin (q * q)),
  σ ((η' K α β hirr htriv σ hdec α' β' γ' habc q h2mq u hq0) i) ≠ 0 := by
  sorry

include α β hirr htriv K σ α' β' γ' habc q t in
lemma R_nonzero
  (hdistinct : ∀ (i j : Fin q × Fin q), i ≠ j → (ρ α β q i) ≠ (ρ α β q j)) :
  (R K α β hirr htriv σ hdec α' β' γ' habc q h2mq u hq0) ≠ 0 := by
  by_contra H
  have HC := (ηvec_eq_zero K α β hirr htriv σ hdec α' β' γ' habc q h2mq u hq0)
    (vecMul_of_R_zero K α β hirr htriv σ hdec α' β' γ' habc q h2mq u hq0 H)
  simp only [funext_iff, Pi.zero_apply, _root_.map_eq_zero] at HC
  apply hbound_sigma K α β hirr htriv σ hdec α' β' γ' habc q h2mq u hq0
  specialize HC (finProdFinEquiv t)
  simp only [map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
  --rw [Equiv.symm_apply_apply] at HC
  ext
  exact HC

open Differentiable Complex

lemma isHolomorphicRFunction (_ : ℂ) :
  Differentiable ℂ (R K α β hirr htriv σ hdec α' β' γ' habc q h2mq u
    hq0 (finProdFinEquiv t)) := sum fun _ _ =>
  (differentiable_const _).mul
    (differentiable_exp.comp ((differentiable_const _).mul differentiable_id'))

lemma RFunctionIsAnalyticAt : AnalyticAt ℂ (R K α β hirr htriv σ hdec α' β' γ' habc q h2mq u
    hq0 (finProdFinEquiv t)) u.1 := by
  apply Differentiable.analyticAt
  exact isHolomorphicRFunction K α β hirr htriv σ hdec α' β' γ' habc q h2mq u t hq0 α

-- ∑ x, σ (η K α' β' γ' q (finProdFinEquiv.symm x) u)
-- * ρ α β q (finProdFinEquiv.symm x) ^ ↑t = 0
--induction with k

lemma cexp_mul : deriv (fun x => cexp (c * x)) x = c * cexp (c * x) := by
  change deriv (fun x => exp ((fun x => c * x) x)) x = c * exp (c * x)
  rw [deriv_cexp]
  · sorry
  · sorry

lemma iteratedDeriv_of_R : iteratedDeriv k (fun x => (R K α β hirr htriv σ hdec α' β' γ' habc q h2mq u
    hq0 (finProdFinEquiv t)) x) =
 fun x => ∑ t : Fin q × Fin q, (σ ((η' K α β hirr htriv σ hdec α' β' γ' habc q h2mq u hq0) t)) *
  Complex.exp ((ρ α β  q t) * x) * (ρ α β q t)^k  := by {
  induction' k with k hk
  · simp only [iteratedDeriv_zero, pow_zero, mul_one]
    rfl
  · simp only [iteratedDeriv_succ]
    simp only at hk
    conv => enter [1]; rw [hk]
    ext x
    unfold deriv
    rw [fderiv_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, fderiv_eq_smul_deriv,
      deriv_mul_const_field', differentiableAt_const, deriv_const_mul_field', smul_eq_mul, one_mul]
    rw [Finset.sum_congr rfl]
    intros t ht
    rw [mul_assoc]
    rw [mul_assoc]
    simp only [mul_eq_mul_left_iff, map_eq_zero]
    left
    rw [deriv_cexp]
    rw [deriv_mul]
    simp only [deriv_const', zero_mul, deriv_id'', mul_one, zero_add]
    rw [mul_assoc]
    rw [Eq.symm (pow_succ' (ρ α β q t) k)]
    · exact differentiableAt_const (ρ α β q t)
    · exact differentiableAt_id'
    · sorry
    · intros i hi
      apply Differentiable.mul
      apply Differentiable.mul
      exact differentiable_const (σ (sys_coeffs K α' β' γ' q i u))
      apply Differentiable.cexp
      sorry
      simp only [differentiable_const]
  }

lemma itatedDeriv_of_R_is_zero : (∀ x, (R K α β σ α' β' γ' q u) x = 0) →
  iteratedDeriv k (fun x => R K α β σ α' β' γ' q u x) x = 0 := fun hR => by {
  rw [iteratedDeriv]
  simp_all only [iteratedFDeriv_zero_fun, Pi.zero_apply,
    ContinuousMultilinearMap.zero_apply]}

def min_value_over_finset {γ : Type _} (f : Π _ : Finset.range ((m K + 1)), γ)
  [Fintype s] [Nonempty s] [LinearOrder γ] : γ := by
  apply Finset.min' (f '' Set.univ).toFinset
  simp only [Set.image_univ, Set.toFinset_range, Finset.image_nonempty,
    univ_eq_attach, attach_nonempty_iff]
  exact nonempty_range_succ

instance nonemptyFinsetRangeOfm : Nonempty (Finset (Finset.range ((m K + 1)))) :=
  instNonemptyOfInhabited

open FormalMultilinearSeries

include α β σ K σ α' β' γ' u
def r : ℕ := by
  apply @min_value_over_finset K _ _ _ _ _ _ (nonemptyFinsetRangeOfm K) _
  exact fun x => order (RFunctionIsAnalyticAt K α β σ α' β' γ' q u).choose

-- where l is the index over which you minimize
-- l0 is the index where the minimum is attained
include α β σ hq0 h2mq hdec hirr htriv K σ α' β' γ' habc h2mq t in
lemma iteratedDeriv_vanishes (k' : Fin (q * q)) (l : Fin (m K)) : l < n K q →
  iteratedDeriv k' (R K α β σ α' β' γ' q u) (l) = 0 := by
  intros hl
  have := applylemma82 K α β hirr htriv σ hdec α' β' γ' habc q h2mq u t hq0
  obtain ⟨η, ⟨htneq0, ⟨hMt0, hbound⟩⟩⟩ := this
  rw [iteratedDeriv_of_R]
  simp only
  sorry
-- from lemma 8.2
-- lemma l : order R l ≥ n
-- from this you get r ≥ n

-- def Fderivp : iteratedFDerivSeries _ (R α β K σ α' β' γ' q h2mq u hq0) :=
--   iteratedFDeriv ℂ (R K α β σ α' β' γ' q u) (R K α β σ α' β' γ' q u)

lemma exists_nonzero_iteratedFDeriv (k : ℕ) : ∃ (l₀ : Fin (m K)),
  iteratedFDeriv ℂ k (R K α β σ α' β' γ' q u) l₀ ≠ 0 := sorry

def c₅ : ℝ := sorry

def c₁₄ : ℝ := sorry

def c₁₅ : ℝ := c₁₄*c₅

theorem main : ∃ r ≥ n K q, r ^ ((r - 3 * (h K)) / 2) ≥ c₁₅ ^ r := by
  use r K α β σ α' β' γ' q u
  sorry

-- -- have use_c₃ : (c₂^n)*(q + q * house β')^(n-1)*(house α')^(m*q)*
--   --   (house γ')^(m*q) ≤ (c₃^n)*n^(((n-1)/2)) := sorry

-- -----------------------------------------------------------------
-- -----------------------------------------------------------------
-- -----------------------------------------------------------------
-- ----------------------------------------------------------------

--   let R : (Fin m × Fin n) → ℂ → ℂ := fun (l,k) x =>
--     ∑ t, σ ((η t)) * Complex.exp ((ρ t) * x)

--   let Rpow : (Fin m × Fin n) → ℂ → ℂ := fun (l,k) x =>
--     iteratedDeriv k (R (l,k)) x

--   have hrpow : (Fin m × Fin n) → Prop := fun (l,k) =>
--     (Complex.log α)^(-l : ℤ) * iteratedDeriv k (R (l, k)) l = 0

--   have Rexpand (l : Fin m) (x : ℂ):
--     R = fun (l,k) x => ∑ k : Fin n,
--       (iteratedDeriv k (R (l, k)) x)*(1/n.factorial) * (x - l)^n := by
--       ext u x
--       simp only [one_div]
--       sorry

--   --have eta_original : η ≠ 0 := sorry

--   --have hA : 1 ≤ c₃ := le_max_left ..
--   --need to make the Rpows generic for any n in Fin n
--     /- use taylor series to expand e^x -/
--   have  R_expand (l : Fin m) (k : Fin n) (t : Fin q × Fin q) (x : ℂ) :
--     R (l,k) x = ∑ i : Fin n, (∑ j : Fin q, σ ((η  t (l,k)))*
--       Complex.exp (ρ  t * l)*(ρ   t)^n/(n.factorial))* (x - (l : ℂ))^n := by {

--     have : Complex.exp ((ρ  t) * x) =
--       Complex.exp ((ρ   t) * (x - l))* Complex.exp ((ρ t) * (l :ℂ)) := by {
--       rw [← Complex.exp_add, mul_sub, sub_add_cancel]}
--     simp only [Prod.mk.eta, sum_prod_type, sum_const, card_univ,
--       Fintype.card_fin, nsmul_eq_mul, R]
--     sorry}

--   have R_not_zero (l : Fin m) (k : Fin n) (x : ℂ) : R (l,k) x ≠ 0 := by sorry

--          -- apply htneq0
--     -- unfold mulVec at hMt0
--     -- unfold dotProduct at hMt0
--     -- rw [Function.funext_iff] at hMt0
--     -- specialize hMt0 (l,k)
--     -- simp only [sum_prod_type, Pi.zero_apply] at hMt0
--     -- rw [Finset.sum_eq_zero] at hMt0

-- --   #exit
-- --
--   have exists_r : ∃ (r : ℕ), (r ≥ q^2/(2*m)) ∧ (∀ (l l₀ : Fin m) (k : Fin n),
--      Rpow ⟨l, k⟩ l = 0 ∧ Rpow ⟨l₀, k⟩ (l₀) ≠ 0) := by  {
--     use n
--     constructor
--     · exact Nat.le_refl (q ^ 2 / (2 * m))
--     · intros l l₀ k
--       constructor
--       · simp only [Prod.mk.eta, Rpow, R]
--         simp only [sum_prod_type]
--         sorry
--       · sorry
--     -- intros l l₀ k
--     -- constructor
--     -- · exact Nat.le_refl n
--     -- constructor
--     -- · sorry
--     -- · sorry
--     }
--
--   rcases exists_r with ⟨r, hr , hRkl⟩

--   -- let ρ : (Fin q × Fin q) → (Fin m × Fin r) → K := fun (a,b) (l₀,k) =>
--   --   algebraMap (𝓞 K) K (η (a, b))

--   let ρ : (Fin q × Fin q)  → K := fun (a,b) =>
--      algebraMap (𝓞 K) K (η (a, b))

--     -- ((a+1) + (b+1) * β')^(r : ℤ)
--     -- * α'^((a+1) * (l₀+1 : ℤ))
--     -- * γ' ^((b+1) * (l₀+1 : ℤ))

--   let c₅ : ℝ := c₁^(h*r + h*2*m*q : ℤ)

--   --The norm of an algebraic integer is again an integer,
--   --because it is equal (up to sign)
--    --  to the constant term of the characteristic polynomial.
--   --fix this (N (c₁^(r+2mq) ρ)) = c₁^r+2mq*N(ρ)
--   have eq5 (t : Fin q × Fin q) (u : Fin m × Fin r) : (c₅)^((-r : ℤ)) <
--     Complex.abs (Algebra.norm ℚ (ρ t)) := by
--       calc (c₅)^((-r : ℤ)) < (c₁)^((- h : ℤ)*(r + 2*m*q)) := by {
--         simp only [zpow_neg, zpow_natCast, neg_mul]
--         rw [inv_lt_inv]
--         · rw [mul_add]
--           have : (h:ℤ) * r + ↑h * (2 * ↑m * ↑q) = (h :ℤ)* ↑r + ↑h * 2 * ↑m * ↑q := by
--             rw [mul_assoc, mul_assoc, mul_assoc]
--           rw [this]
--           refine lt_self_pow ?h ?hm
--           · rw [← one_zpow ((h : ℤ)* ↑r + ↑h * 2 * ↑m * ↑q )]
--             simp only [one_zpow]
--             simp only [c₁]
--             simp only [Int.cast_mul, Int.cast_max, Int.cast_one]
--             apply one_lt_pow
--             · sorry
--             · sorry
--           · sorry
--         · sorry
--         · sorry
--       }
--         _ < Complex.abs (Algebra.norm ℚ (ρ t)):= sorry

--   let c₄' : ℝ  := c₄ ^ n * (↑n ^ (1 / 2) * (↑n + 1))

--   let c₆ : ℝ := sorry

--   let c₇ : ℝ := sorry

--   let c₈ : ℝ := max (c₄^n * (n^(1/2)*(n+1))*q^2*(c₆*q)^n*(c₇)^(q : ℤ)) 1

--   let c₈' : ℝ := max (c₈^r) ((c₈)^r * r ^ (r+3/2))

--   have eq6 (t : Fin q × Fin q) (u : Fin m × Fin r) :
--     house (ρ t) ≤ c₈' := by
--     calc _ ≤ c₄' := by {
--         simp only [c₄']
--         exact fromapplylemma82_bound t
--         }
--          _ ≤c₄'*(q^2*(c₆*q)^n*(c₇)^(q : ℤ)) := by {
--           apply  le_mul_of_one_le_right
--           · calc 0 ≤ 1 := sorry
--                  _ ≤ c₄' := sorry
--           · sorry
--          }
--          _ ≤ (c₈^r) := by { sorry
--           --apply le_max_left
--           }
--          _ ≤ c₈' := by {
--           simp only [c₈']
--           apply le_max_left
--           }

--   let S : (Fin m × Fin n) → ℂ → ℂ := fun (l₀, k) z =>
--     (r.factorial) * (R (l₀, k) z) / ((z - l₀) ^ r) *
--       ∏ k in Finset.range ((r - 1)) \ {(l₀ : ℕ)}, ((l₀ - k) / (z - k)) ^ r

--   -- --have hR : 0 < (m*(1+ (r/q)) : ℝ) := sorry
--   have alt_cauchy (k : Fin n) (l₀ : Fin m) (t : Fin q × Fin q) :
--       (∮ z in C(0, m*(1+ (r/q))), (z - l₀)⁻¹ * (S (l₀,k) z)) =
--         (2 * ↑Real.pi * Complex.I) •  S (l₀,k) l₀ := by
--     apply _root_.DifferentiableOn.circleIntegral_sub_inv_smul
--     · sorry
--     · simp only [Metric.mem_ball, dist_zero_right, Complex.norm_nat]
--       have : (l₀ : ℝ) < ↑m := by simp only [Nat.cast_lt, Fin.is_lt]
--       trans
--       · exact this
--       · apply lt_mul_right
--         · exact mod_cast hm
--         · sorry

--   have hcauchy : ∀ (k : Fin n) (l₀ : Fin m) (t : Fin q × Fin q), (2 * ↑Real.pi * Complex.I)⁻¹ *
--     (∮ z in C(0, m*(1+ (r/q))), (z - l₀)⁻¹ * (S (l₀,k) z)) = S (l₀,k) l₀ := fun k l₀ t => by
--    apply Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
--     · have : Set.Countable {(l₀ : ℂ)} := countable_singleton (l₀ : ℂ)
--       exact this
--     · have : (l₀ : ℂ) ∈ Metric.ball 0 (↑m * (1 + ↑r / ↑q)) := by {
--       simp only [Metric.mem_ball, dist_zero_right, Complex.norm_nat]
--       have : (l₀ : ℝ) < ↑m := by simp only [Nat.cast_lt, Fin.is_lt]
--       trans
--       · exact this
--       · apply lt_mul_right
--         · exact mod_cast hm
--         · sorry}
--       exact this
--     · intros x hx
--       simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_eq_abs] at hx
--       simp only [Prod.mk.eta, div_pow, prod_div_distrib, S]
--       simp only [Prod.mk.eta, sum_prod_type, R]
--       sorry

--     · have : ∀ z ∈ Metric.ball 0 (m*(1+ (r/q))) \ {(l₀ : ℂ)},
--          DifferentiableAt ℂ (S (l₀, k)) z := by {
--       intros z hz
--       simp only [mem_diff, Metric.mem_ball, dist_zero_right, Complex.norm_eq_abs,
--         mem_singleton_iff] at hz
--       rcases hz with ⟨hzabs, hzneq⟩
--       --simp only [S,R]
--       -- have : DifferentiableAt ℂ (R (l₀, k)) z := by {
--       --   simp only [DifferentiableAt]
--       --   use fderiv ℂ (R (l₀, k)) z
--       --   --use ∑ t, σ (η t) *σ (ρ t) * Complex.exp (σ (ρ t) * l₀)
--       -- }
--       simp only [DifferentiableAt]
--       use fderiv ℂ (S (l₀, k)) z
--       sorry
--       }
--       exact this


--   have newρ (z : ℂ) (hz : z ∈ Metric.ball 0 (m*(1+ (r/q))))
--           (k : Fin n) (l₀ : Fin m) (t : Fin q × Fin q) :
--       σ (ρ t) = Complex.log (α) ^ (-r : ℤ) * ((2 * ↑Real.pi * Complex.I)⁻¹ *
--         (∮ z in C(0, m*(1+ (r/q))), (z - l₀)⁻¹ * (S (l₀,k) z))) := by
--         calc
--       _ = (Complex.log (α))^(- r : ℤ) * (S  (l₀,k) l₀) := sorry
--       _ = Complex.log (α) ^ (-r : ℤ) * ((2 * ↑Real.pi * Complex.I)⁻¹ *
--       (∮ z in C(0, m*(1+ (r/q))), (z - l₀)⁻¹ * (S (l₀,k) z))) := by
--     {rw [← hcauchy]
--      exact t}

--   let c₉ : ℝ := sorry

--   let c₁₀ : ℝ := sorry

--   have abs_R (z : ℂ) (hz : z ∈ Metric.ball 0 (m*(1+ (r/q)))) (k : Fin n)
--         (l₀ : Fin m) (t : Fin q × Fin q) :
--     Complex.abs (R (l₀, k) z) ≤ (c₁₀)^r * r^(1/2*(r+3)):= calc
--        _ ≤ q^2 * ‖σ (η t)‖*
--           Real.exp ((q+q*(Complex.abs (β)))*(Real.log (Complex.abs (α)))*m*(1+r/q)) := by {
--             simp only [Prod.mk.eta, sum_prod_type, Complex.norm_eq_abs, R]
--             sorry

--           }
--        _ ≤ q^2 * (c₄)^n *n ^((1/2)*(n+1))*(c₉)^(r+q) := sorry
--        _ ≤ (c₁₀)^r * r^(1/2*(r+3)) := sorry

--   have abs_hmrqzl₀ (z : ℂ) (hz : z ∈ Metric.sphere 0 (m*(1+ (r/q))))
--      (k : Fin n) (l₀ : Fin m) : m*r/q ≤ Complex.abs (z - l₀) := calc
--           _ = (m * (1 + r/q) - m : ℝ) := by {ring}
--           _ ≤ Complex.abs z - Complex.abs l₀ := by {
--           simp only [hz, Complex.abs_natCast]
--           have : (l₀ : ℝ) < ↑m := by {
--             simp only [Nat.cast_lt, Fin.is_lt]
--             }
--           sorry
--           --rwa [sub_lt_sub_iff_left]
--           }
--           _ ≤ Complex.abs (z - l₀) := by {apply AbsoluteValue.le_sub}

--   have abs_z_k (k : Fin n) (l₀ : Fin m) (z : ℂ) (hz : z ∈ Metric.sphere 0 (m*(1+ (r/q)))) :
--         m*r/q ≤ Complex.abs (z-k) := by
--     calc _ ≤ Complex.abs (z - l₀) := abs_hmrqzl₀ z hz k l₀
--          _ ≤ Complex.abs (z-k) := by { sorry
--           --aesop
--          }

--   let c₁₁ : ℝ := sorry

--   have abs_denom (z : ℂ)(hz : z ∈ Metric.sphere 0 (m*(1+ (r/q)))) (k : Fin n) (l₀ : Fin m) :
--     Complex.abs (((z - l₀)^(-r : ℤ))* ∏ k ∈ Finset.range (m + 1) \ {(l₀: ℕ)}, ((l₀ - k)/(z-k))^r)
--            ≤ (c₁₁)^r * (q/r)^(m*r) := sorry

--   let c₁₂ : ℝ := sorry

--   have (z : ℂ) (k : Fin n) (l₀ : Fin m) (t : Fin q × Fin q) :
--           Complex.abs (S (l₀, k) z) ≤ (c₁₂)^r*((3-m)/2 + 3 /2) := calc
--           _ = Complex.abs ((r.factorial) * (R (l₀, k) z) / ((z - l₀) ^ r) *
--               ∏ k in Finset.range ((r - 1)) \ {(l₀ : ℕ)}, ((l₀ - k) / (z - k)) ^ r) := rfl
--           _ = r.factorial * (Complex.abs ((R (l₀, k) z)) * Complex.abs ( (1/(z - l₀) ^ (r))) *
--             Complex.abs (∏ k in Finset.range ((r - 1)) \
--                 {(l₀ : ℕ)}, ((l₀ - k) / (z - k)) ^ r)) := by {
--             simp only [_root_.map_mul]
--             simp only [map_div₀, _root_.map_mul, Complex.abs_natCast, map_pow, div_pow,
--               prod_div_distrib, map_prod, one_div, map_inv₀]
--             have : Complex.abs (R (l₀, k) z) / Complex.abs (z - ↑↑l₀) ^ r=
--              Complex.abs (R (l₀, k) z) * (1/  Complex.abs (z - ↑↑l₀) ^ r) := by {
--               rw [mul_one_div]
--              }
--             norm_cast at this
--             sorry
--             }
--           _ ≤  r.factorial*((c₁₀)^r*r^((r+3)/2)*(c₁₁)^r*(q/r)^(m*r)) := by {
--             rw [mul_le_mul_left]
--             · sorry
--             · simp only [Nat.cast_pos]
--               exact Nat.factorial_pos r
--           }
--           _ ≤ (c₁₂)^r*((3-m)/2 + 3 /2) := sorry
--   let c₁₃ : ℝ := sorry

--   let hρ (k : Fin n) (l₀ : Fin m) (t : Fin q × Fin q) :
--     σ (ρ t) = ((2 * Real.pi)⁻¹ * ∮ (z : ℂ) in
--         C(0, ↑m * (1 + ↑r / ↑q)), (z - ↑l₀)⁻¹ * S  (l₀, k) z) := sorry

--   have eq8 (z : ℂ) (k : Fin n) (l₀ : Fin m) (t : Fin q × Fin q) :
--     Complex.abs (σ (ρ t))≤ (c₁₃)^r*r^(r*(3-m)/2 +3/2) := by
--       calc _ = Complex.abs ((2 * Real.pi)⁻¹ * ∮ (z : ℂ) in
--         C(0, ↑m * (1 + ↑r / ↑q)), (z - ↑l₀)⁻¹ * S  (l₀, k) z) := by {rw [hρ k l₀ t]}
--            _≤ Complex.abs ((2 * Real.pi)⁻¹) *  Complex.abs (∮ (z : ℂ) in
--         C(0, ↑m * (1 + ↑r / ↑q)),(z - ↑l₀)⁻¹ * S  (l₀, k) z) := by {
--           simp only [_root_.map_mul]
--           simp only [_root_.mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv,
--            Complex.ofReal_ofNat, _root_.map_mul, map_inv₀, Complex.abs_ofReal, Complex.abs_ofNat,
--             le_refl]}
--            _ ≤ Complex.abs ((Complex.log (α)))^((-r : ℤ))*m*(1+r/q)*
--         (c₁₂)^r*r^(r*(3-m)/2 +3/2)*q/(m*r) := by sorry
--            _ ≤ (c₁₃)^r*r^(r*(3-m)/2 +3/2)  := by sorry

--   let c₁₄ : ℝ := sorry

--   have use6and8 : (Algebra.norm ℚ ρ) ≤ (c₁₄)^(r)*r^((-r:ℤ)/2+3*h/2) := calc
--           _ ≤ (c₁₄)^(r)*r^((h-1)*(r+3/2)+(3-m)*r*1/2 +3/2) := sorry
--           _ = (c₁₄)^(r)*r^((-r : ℤ)/2+3*h/2) := sorry

--   have final_ineq : r^(r/2 - 3*h/2) ≥ c₁₅^r := sorry

--   exact ⟨r,  hr, final_ineq⟩
--   --sorry
-- include hα hβ
-- theorem hilbert7 : Transcendental ℚ (α ^ β) := fun hγ => by

--   obtain ⟨K, hK, hNK, σ, hdec, α', β', γ', ha,hb, hc⟩ := getElemsInNF α β (α^β) hα hβ hγ

--   --have hq0 : 0 < q := sorry

--   rcases (main K α β σ α' β' γ' q) with ⟨r, ⟨hr, hs⟩⟩
--     -- only now you define t
--   have use5 : r^(r/2 - 3*h K/2) < c₁₅^r := calc
--     _ <  c₁₄^r * c₅^r := by sorry
--     _ = c₁₅^r := by {
--       rw [← mul_pow]
--       simp only [c₁₅]}
--   linarith
