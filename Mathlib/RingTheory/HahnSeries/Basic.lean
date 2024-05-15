/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.Function.Support
import Mathlib.Order.WellFoundedSet

#align_import ring_theory.hahn_series from "leanprover-community/mathlib"@"a484a7d0eade4e1268f4fb402859b6686037f965"

/-!
# Hahn Series
If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `HahnSeries Γ R`, with the most studied case being when `Γ` is
a linearly ordered abelian group and `R` is a field, in which case `HahnSeries Γ R` is a
valued field, with value group `Γ`.
These generalize Laurent series (with value group `ℤ`), and Laurent series are implemented that way
in the file `RingTheory/LaurentSeries`.

## Main Definitions
  * If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are partially well-ordered.
  * Laurent series over `R` are implemented as `HahnSeries ℤ R` in the file
    `RingTheory/LaurentSeries`.

## TODO
  * Equivalence between `HahnSeries Γ (HahnSeries Γ' R)` and `HahnSeries (Γ × Γ') R`
## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]

-/

set_option linter.uppercaseLean3 false

open Finset Function
open scoped Classical

noncomputable section

/-- If `Γ` is linearly ordered and `R` has zero, then `HahnSeries Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are well-founded. -/
@[ext]
structure HahnSeries (Γ : Type*) (R : Type*) [PartialOrder Γ] [Zero R] where
  /-- The coefficient function of a Hahn series. -/
  coeff : Γ → R
  isPWO_support' : (Function.support coeff).IsPWO
#align hahn_series HahnSeries

variable {Γ : Type*} {R : Type*}

namespace HahnSeries

section Zero

variable [PartialOrder Γ] [Zero R]

theorem coeff_injective : Injective (coeff : HahnSeries Γ R → Γ → R) :=
  HahnSeries.ext
#align hahn_series.coeff_injective HahnSeries.coeff_injective

@[simp]
theorem coeff_inj {x y : HahnSeries Γ R} : x.coeff = y.coeff ↔ x = y :=
  coeff_injective.eq_iff
#align hahn_series.coeff_inj HahnSeries.coeff_inj

/-- The support of a Hahn series is just the set of indices whose coefficients are nonzero.
  Notably, it is well-founded. -/
nonrec def support (x : HahnSeries Γ R) : Set Γ :=
  support x.coeff
#align hahn_series.support HahnSeries.support

@[simp]
theorem isPWO_support (x : HahnSeries Γ R) : x.support.IsPWO :=
  x.isPWO_support'
#align hahn_series.is_pwo_support HahnSeries.isPWO_support

@[simp]
theorem isWF_support (x : HahnSeries Γ R) : x.support.IsWF :=
  x.isPWO_support.isWF
#align hahn_series.is_wf_support HahnSeries.isWF_support

@[simp]
theorem mem_support (x : HahnSeries Γ R) (a : Γ) : a ∈ x.support ↔ x.coeff a ≠ 0 :=
  Iff.refl _
#align hahn_series.mem_support HahnSeries.mem_support

instance : Zero (HahnSeries Γ R) :=
  ⟨{  coeff := 0
      isPWO_support' := by simp }⟩

instance : Inhabited (HahnSeries Γ R) :=
  ⟨0⟩

instance [Subsingleton R] : Subsingleton (HahnSeries Γ R) :=
  ⟨fun a b => a.ext b (Subsingleton.elim _ _)⟩

@[simp]
theorem zero_coeff {a : Γ} : (0 : HahnSeries Γ R).coeff a = 0 :=
  rfl
#align hahn_series.zero_coeff HahnSeries.zero_coeff

@[simp]
theorem coeff_fun_eq_zero_iff {x : HahnSeries Γ R} : x.coeff = 0 ↔ x = 0 :=
  coeff_injective.eq_iff' rfl
#align hahn_series.coeff_fun_eq_zero_iff HahnSeries.coeff_fun_eq_zero_iff

theorem ne_zero_of_coeff_ne_zero {x : HahnSeries Γ R} {g : Γ} (h : x.coeff g ≠ 0) : x ≠ 0 :=
  mt (fun x0 => (x0.symm ▸ zero_coeff : x.coeff g = 0)) h
#align hahn_series.ne_zero_of_coeff_ne_zero HahnSeries.ne_zero_of_coeff_ne_zero

@[simp]
theorem support_zero : support (0 : HahnSeries Γ R) = ∅ :=
  Function.support_zero
#align hahn_series.support_zero HahnSeries.support_zero

@[simp]
nonrec theorem support_nonempty_iff {x : HahnSeries Γ R} : x.support.Nonempty ↔ x ≠ 0 := by
  rw [support, support_nonempty_iff, Ne, coeff_fun_eq_zero_iff]
#align hahn_series.support_nonempty_iff HahnSeries.support_nonempty_iff

@[simp]
theorem support_eq_empty_iff {x : HahnSeries Γ R} : x.support = ∅ ↔ x = 0 :=
  support_eq_empty_iff.trans coeff_fun_eq_zero_iff
#align hahn_series.support_eq_empty_iff HahnSeries.support_eq_empty_iff

/-- `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise. -/
def single (a : Γ) : ZeroHom R (HahnSeries Γ R) where
  toFun r :=
    { coeff := Pi.single a r
      isPWO_support' := (Set.isPWO_singleton a).mono Pi.support_single_subset }
  map_zero' := HahnSeries.ext _ _ (Pi.single_zero _)
#align hahn_series.single HahnSeries.single

variable {a b : Γ} {r : R}

@[simp]
theorem single_coeff_same (a : Γ) (r : R) : (single a r).coeff a = r :=
  Pi.single_eq_same (f := fun _ => R) a r
#align hahn_series.single_coeff_same HahnSeries.single_coeff_same

@[simp]
theorem single_coeff_of_ne (h : b ≠ a) : (single a r).coeff b = 0 :=
  Pi.single_eq_of_ne (f := fun _ => R) h r
#align hahn_series.single_coeff_of_ne HahnSeries.single_coeff_of_ne

theorem single_coeff : (single a r).coeff b = if b = a then r else 0 := by
  split_ifs with h <;> simp [h]
#align hahn_series.single_coeff HahnSeries.single_coeff

@[simp]
theorem support_single_of_ne (h : r ≠ 0) : support (single a r) = {a} :=
  Pi.support_single_of_ne h
#align hahn_series.support_single_of_ne HahnSeries.support_single_of_ne

theorem support_single_subset : support (single a r) ⊆ {a} :=
  Pi.support_single_subset
#align hahn_series.support_single_subset HahnSeries.support_single_subset

theorem eq_of_mem_support_single {b : Γ} (h : b ∈ support (single a r)) : b = a :=
  support_single_subset h
#align hahn_series.eq_of_mem_support_single HahnSeries.eq_of_mem_support_single

--@[simp] Porting note (#10618): simp can prove it
theorem single_eq_zero : single a (0 : R) = 0 :=
  (single a).map_zero
#align hahn_series.single_eq_zero HahnSeries.single_eq_zero

theorem single_injective (a : Γ) : Function.Injective (single a : R → HahnSeries Γ R) :=
  fun r s rs => by rw [← single_coeff_same a r, ← single_coeff_same a s, rs]
#align hahn_series.single_injective HahnSeries.single_injective

theorem single_ne_zero (h : r ≠ 0) : single a r ≠ 0 := fun con =>
  h (single_injective a (con.trans single_eq_zero.symm))
#align hahn_series.single_ne_zero HahnSeries.single_ne_zero

@[simp]
theorem single_eq_zero_iff {a : Γ} {r : R} : single a r = 0 ↔ r = 0 :=
  map_eq_zero_iff _ <| single_injective a
#align hahn_series.single_eq_zero_iff HahnSeries.single_eq_zero_iff

/-- Change a HahnSeries with coefficients in HahnSeries to a HahnSeries on the Lex product. -/
def ofIterate {Γ' : Type*} [PartialOrder Γ'] (x : HahnSeries Γ (HahnSeries Γ' R)) :
    HahnSeries (Γ ×ₗ Γ') R where
  coeff := fun g => coeff (coeff x g.1) g.2
  isPWO_support' := by
    refine Set.PartiallyWellOrderedOn.subsetProdLex ?_ ?_
    · have h : ((fun (x : Γ ×ₗ Γ') ↦ x.1) '' Function.support fun g ↦ (x.coeff g.1).coeff g.2) ⊆
          Function.support x.coeff :=
        Set.image_subset_iff.mpr <| support_subset_iff.mpr fun g hg => Set.mem_preimage.mpr <|
        Function.mem_support.mpr <| ne_zero_of_coeff_ne_zero hg
      exact Set.IsPWO.mono x.isPWO_support' h
    · intro a
      have h : {y | (a, y) ∈ Function.support fun g ↦ (x.coeff g.1).coeff g.2} =
          Function.support fun b => (x.coeff a).coeff b := by
        exact rfl
      simp_all only [Function.mem_support, ne_eq]
      exact (x.coeff a).isPWO_support'

/-- Change a Hahn series on a lex product to a Hahn series with coefficients in a Hahn series. -/
def toIterate {Γ' : Type*} [PartialOrder Γ'] (x : HahnSeries (Γ ×ₗ Γ') R) :
    HahnSeries Γ (HahnSeries Γ' R) where
  coeff := fun g => {
    coeff := fun g' => coeff x (g, g')
    isPWO_support' := Set.PartiallyWellOrderedOn.fiberProdLex x.isPWO_support' g
  }
  isPWO_support' := by
    have h₁ : (Function.support fun g => HahnSeries.mk (fun g' => x.coeff (g, g'))
        (Set.PartiallyWellOrderedOn.fiberProdLex x.isPWO_support' g)) = Function.support
        fun g => fun g' => x.coeff (g, g') := by
      rw [@support_eq_iff]
      constructor
      · intro y hy
        simp_all only [Function.mem_support, ne_eq]
        refine Not.intro ?left.h
        rw [@HahnSeries.ext_iff]
        simp only [imp_false, ne_eq]
        exact hy
      · intro y hy
        simp_all only [Function.mem_support, ne_eq, not_not]
        exact rfl
    rw [h₁]
    have h : (Function.support fun g => fun g' => x.coeff (g, g')) =
        ((fun x ↦ x.1) '' Function.support x.coeff) := by
      exact Function.support_on_image (fun g => x.coeff g)
    rw [h]
    exact Set.PartiallyWellOrderedOn.imageProdLex x.isPWO_support'

/-- The equivalence between iterated Hahn series and Hahn series on the lex product. -/
def iterate_equiv {Γ' : Type*} [PartialOrder Γ'] :
    HahnSeries Γ (HahnSeries Γ' R) ≃ HahnSeries (Γ ×ₗ Γ') R where
  toFun := ofIterate
  invFun := toIterate
  left_inv := congrFun rfl
  right_inv := congrFun rfl

instance [Nonempty Γ] [Nontrivial R] : Nontrivial (HahnSeries Γ R) :=
  ⟨by
    obtain ⟨r, s, rs⟩ := exists_pair_ne R
    inhabit Γ
    refine' ⟨single default r, single default s, fun con => rs _⟩
    rw [← single_coeff_same (default : Γ) r, con, single_coeff_same]⟩

section Order

/-- An orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero
  coefficient if `x ≠ 0`, and is `⊤` when `x = 0`. -/
def orderTop (x : HahnSeries Γ R) : WithTop Γ :=
  if h : x = 0 then ⊤ else x.isWF_support.min (support_nonempty_iff.2 h)

@[simp]
theorem orderTop_zero : orderTop (0 : HahnSeries Γ R) = ⊤ :=
  dif_pos rfl

theorem orderTop_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) :
    orderTop x = x.isWF_support.min (support_nonempty_iff.2 hx) :=
  dif_neg hx

theorem ne_zero_iff_orderTop {x : HahnSeries Γ R} : x ≠ 0 ↔ orderTop x ≠ ⊤ := by
  constructor
  · exact fun hx => Eq.mpr (congrArg (fun h ↦ h ≠ ⊤) (orderTop_of_ne hx)) WithTop.coe_ne_top
  · contrapose!
    exact fun hx ↦ Eq.mpr (congrArg (fun y ↦ orderTop y = ⊤) hx) orderTop_zero

theorem untop_orderTop_of_ne_zero {x : HahnSeries Γ R} (hx : x ≠ 0) :
    WithTop.untop x.orderTop (ne_zero_iff_orderTop.mp hx) =
      x.isWF_support.min (support_nonempty_iff.2 hx) :=
  WithTop.coe_inj.mp ((WithTop.coe_untop (orderTop x) (ne_zero_iff_orderTop.mp hx)).trans
    (orderTop_of_ne hx))

theorem coeff_orderTop_ne_zero {x : HahnSeries Γ R} {g : Γ} (hg : x.orderTop = g) :
    x.coeff g ≠ 0 := by
  have h : orderTop x ≠ ⊤ := by simp_all only [ne_eq, WithTop.coe_ne_top, not_false_eq_true]
  have hx : x ≠ 0 := ne_zero_iff_orderTop.mpr h
  rw [orderTop_of_ne hx, WithTop.coe_eq_coe] at hg
  rw [← hg]
  exact x.isWF_support.min_mem (support_nonempty_iff.2 hx)

theorem orderTop_le_of_coeff_ne_zero {Γ} [LinearOrder Γ] {x : HahnSeries Γ R}
    {g : Γ} (h : x.coeff g ≠ 0) : x.orderTop ≤ g := by
  rw [orderTop_of_ne (ne_zero_of_coeff_ne_zero h), WithTop.coe_le_coe]
  exact Set.IsWF.min_le _ _ ((mem_support _ _).2 h)

@[simp]
theorem orderTop_single (h : r ≠ 0) : (single a r).orderTop = a :=
  (orderTop_of_ne (single_ne_zero h)).trans
    (WithTop.coe_inj.mpr (support_single_subset
      ((single a r).isWF_support.min_mem (support_nonempty_iff.2 (single_ne_zero h)))))

theorem orderTop_single_le : a ≤ (single a r).orderTop := by
  by_cases hr : r = 0
  · rw [hr, single_eq_zero, orderTop_zero]
    exact OrderTop.le_top (a : WithTop Γ)
  · rw [orderTop_single hr]

theorem lt_orderTop_single {g g' : Γ} (hgg' : g < g') : g < (single g' r).orderTop :=
  lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hgg') orderTop_single_le

theorem coeff_eq_zero_of_lt_orderTop {x : HahnSeries Γ R} {i : Γ} (hi : i < x.orderTop) :
    x.coeff i = 0 := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · exact zero_coeff
  contrapose! hi
  rw [← mem_support] at hi
  rw [orderTop_of_ne hx, WithTop.coe_lt_coe]
  exact Set.IsWF.not_lt_min _ _ hi

/-- A variant of the coefficient function that takes inputs in `WithTop Γ`. -/
def coeffTop (x : HahnSeries Γ R) (g : WithTop Γ) : R :=
  match g with
  | ⊤ => 0
  | (g : Γ) => x.coeff g

@[simp]
theorem coeffTop_eq (x : HahnSeries Γ R) (g : Γ) : x.coeffTop g = x.coeff g :=
  rfl

@[simp]
theorem coeffTop_Top (x : HahnSeries Γ R) : x.coeffTop ⊤ = 0 :=
  rfl

@[simp]
theorem coeff_untop_eq {x : HahnSeries Γ R} {g : WithTop Γ} (hg : g ≠ ⊤) :
    x.coeff (WithTop.untop g hg) = x.coeffTop g := by
  rw [← coeffTop_eq, WithTop.coe_untop]

theorem ne_zero_of_coeffTop_ne_zero {x : HahnSeries Γ R} {g : WithTop Γ} (h : x.coeffTop g ≠ 0) :
    x ≠ 0 := by
  match g with
  | ⊤ => exact fun _ ↦ h rfl
  | (g : Γ) => exact ne_zero_of_coeff_ne_zero h

theorem orderTop_le_of_coeffTop_ne_zero {Γ} [LinearOrder Γ] {x : HahnSeries Γ R}
    {g : WithTop Γ} (h : x.coeffTop g ≠ 0) : x.orderTop ≤ g := by
  match g with
  | ⊤ => exact (h rfl).elim
  | (g : Γ) =>
    rw [orderTop_of_ne (ne_zero_of_coeffTop_ne_zero h), WithTop.coe_le_coe]
    exact Set.IsWF.min_le _ _ ((mem_support _ _).2 h)

theorem coeffTop_eq_zero_of_lt_orderTop {x : HahnSeries Γ R} {i : WithTop Γ} (hi : i < x.orderTop) :
    x.coeffTop i = 0 := by
  match i with
  | ⊤ => exact rfl
  | (i : Γ) => rw [coeffTop_eq, coeff_eq_zero_of_lt_orderTop hi]

/-- A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or
zero if the series vanishes. -/
def leadingCoeff (x : HahnSeries Γ R) : R :=
  x.coeffTop x.orderTop

@[simp]
theorem leadingCoeff_zero : leadingCoeff (0 : HahnSeries Γ R) = 0 := by
  simp [leadingCoeff]

theorem leadingCoeff_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) :
    x.leadingCoeff = x.coeff (x.isWF_support.min (support_nonempty_iff.2 hx)) := by
  rw [leadingCoeff, orderTop_of_ne hx, coeffTop_eq]

theorem leadingCoeff_ne_iff {x : HahnSeries Γ R} : x ≠ 0 ↔ x.leadingCoeff ≠ 0 := by
  constructor
  · intro hx
    rw [leadingCoeff_of_ne hx]
    exact coeff_orderTop_ne_zero (orderTop_of_ne hx)
  · contrapose!
    intro hx
    rw [hx]
    exact leadingCoeff_zero

theorem leadingCoeff_of_single {a : Γ} {r : R} : leadingCoeff (single a r) = r := by
  simp only [leadingCoeff, single_eq_zero_iff]
  by_cases h : r = 0
  · simp_all only [map_zero, orderTop_zero, coeffTop_Top]
  · simp_all only [ne_eq, not_false_eq_true, orderTop_single, coeffTop_eq, single_coeff_same]

/-- A leading term of a Hahn series is a Hahn series with subsingleton support at minimal-order. -/
def leadingTerm (x : HahnSeries Γ R) : HahnSeries Γ R :=
  if h : x = 0 then 0
    else single (x.isWF_support.min (support_nonempty_iff.2 h)) x.leadingCoeff

@[simp]
theorem leadingTerm_zero : leadingTerm (0 : HahnSeries Γ R) = 0 :=
  dif_pos rfl

theorem leadingTerm_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) :
    leadingTerm x = single (x.isWF_support.min (support_nonempty_iff.2 hx)) x.leadingCoeff :=
  dif_neg hx

theorem leadingTerm_ne_iff {x : HahnSeries Γ R} : x ≠ 0 ↔ leadingTerm x ≠ 0 := by
  constructor
  · intro hx
    rw [leadingTerm_of_ne hx]
    simp_all only [ne_eq, single_eq_zero_iff]
    exact leadingCoeff_ne_iff.mp hx
  · contrapose!
    intro hx
    rw [hx]
    exact leadingTerm_zero

theorem leadingCoeff_leadingTerm {x : HahnSeries Γ R} :
    leadingCoeff (leadingTerm x) = leadingCoeff x := by
  by_cases h : x = 0
  · rw [h, leadingTerm_zero]
  · rw [leadingTerm_of_ne h, leadingCoeff_of_single]

variable [Zero Γ]

/-- The order of a nonzero Hahn series `x` is a minimal element of `Γ` where `x` has a
nonzero coefficient, and is defined so that the order of 0 is 0. -/
def order (x : HahnSeries Γ R) : Γ :=
  if h : x = 0 then 0 else x.isWF_support.min (support_nonempty_iff.2 h)
#align hahn_series.order HahnSeries.order

@[simp]
theorem order_zero : order (0 : HahnSeries Γ R) = 0 :=
  dif_pos rfl
#align hahn_series.order_zero HahnSeries.order_zero

theorem order_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) :
    order x = x.isWF_support.min (support_nonempty_iff.2 hx) :=
  dif_neg hx
#align hahn_series.order_of_ne HahnSeries.order_of_ne

theorem order_eq_orderTop_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) : order x = orderTop x := by
  rw [order_of_ne hx, orderTop_of_ne hx]

theorem coeff_order_ne_zero {x : HahnSeries Γ R} (hx : x ≠ 0) : x.coeff x.order ≠ 0 := by
  rw [order_of_ne hx]
  exact x.isWF_support.min_mem (support_nonempty_iff.2 hx)
#align hahn_series.coeff_order_ne_zero HahnSeries.coeff_order_ne_zero

theorem order_le_of_coeff_ne_zero {Γ} [Zero Γ] [LinearOrder Γ] {x : HahnSeries Γ R}
    {g : Γ} (h : x.coeff g ≠ 0) : x.order ≤ g :=
  le_trans (le_of_eq (order_of_ne (ne_zero_of_coeff_ne_zero h)))
    (Set.IsWF.min_le _ _ ((mem_support _ _).2 h))
#align hahn_series.order_le_of_coeff_ne_zero HahnSeries.order_le_of_coeff_ne_zero

@[simp]
theorem order_single (h : r ≠ 0) : (single a r).order = a :=
  (order_of_ne (single_ne_zero h)).trans
    (support_single_subset
      ((single a r).isWF_support.min_mem (support_nonempty_iff.2 (single_ne_zero h))))
#align hahn_series.order_single HahnSeries.order_single

theorem coeff_eq_zero_of_lt_order {x : HahnSeries Γ R} {i : Γ} (hi : i < x.order) :
    x.coeff i = 0 := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  contrapose! hi
  rw [← mem_support] at hi
  rw [order_of_ne hx]
  exact Set.IsWF.not_lt_min _ _ hi
#align hahn_series.coeff_eq_zero_of_lt_order HahnSeries.coeff_eq_zero_of_lt_order

theorem zero_lt_order_of_orderTop {x : HahnSeries Γ R} (hx : 0 < x.orderTop) (hxne : x ≠ 0) :
    0 < x.order := by
  simp_all only [orderTop_of_ne hxne, WithTop.coe_pos, ne_eq, order_of_ne hxne]

theorem zero_lt_orderTop_of_order {x : HahnSeries Γ R} (hx : 0 < x.order) : 0 < x.orderTop := by
  by_cases h : x = 0
  · simp_all only [order_zero, lt_self_iff_false]
  · simp_all only [order_of_ne h, orderTop_of_ne h, WithTop.coe_pos]

theorem zero_le_order_of_orderTop {x : HahnSeries Γ R} (hx : 0 ≤ x.orderTop) : 0 ≤ x.order := by
  by_cases h : x = 0
  · refine le_of_eq ?_
    simp_all only [orderTop_zero, order_zero]
  · rw [order_of_ne h, ← @WithTop.coe_le_coe]
    rw [orderTop_of_ne h] at hx
    exact hx

theorem zero_lt_orderTop_iff {x : HahnSeries Γ R} :
    0 < x.orderTop ↔ (0 ≤ x.order ∧ (x.order = 0 → x = 0)) := by
  refine { mp := fun hx => ?_, mpr := fun hx => ?_ }
  · refine { left := zero_le_order_of_orderTop <| le_of_lt hx, right := fun hzero => ?_ }
    by_contra hxne
    have hxlt : 0 < x.order := zero_lt_order_of_orderTop hx hxne
    rw [hzero, lt_self_iff_false] at hxlt
    exact hxlt
  · by_cases hzero : x = 0
    · simp_all only [order_zero, le_refl, forall_true_left, and_self, orderTop_zero]
      exact WithTop.coe_lt_top 0
    · simp_all only [orderTop_of_ne, WithTop.coe_pos, order, orderTop, dite_false]
      simp_all only [lt_iff_le_and_ne, dite_false, true_and]
      exact fun h => hx.right h.symm

theorem leadingCoeff_eq [Zero Γ] {x : HahnSeries Γ R} : x.leadingCoeff = x.coeff x.order := by
  by_cases h : x = 0
  · rw [h, leadingCoeff_zero, zero_coeff]
  · rw [leadingCoeff_of_ne h, order_of_ne h]

theorem leadingTerm_eq [Zero Γ] {x : HahnSeries Γ R} :
    x.leadingTerm = single x.order (x.coeff x.order) := by
  by_cases h : x = 0
  · rw [h, leadingTerm_zero, order_zero, zero_coeff, single_eq_zero]
  · rw [leadingTerm_of_ne h, leadingCoeff_eq, order_of_ne h]

end Order

section Domain

variable {Γ' : Type*} [PartialOrder Γ']

/-- Extends the domain of a `HahnSeries` by an `OrderEmbedding`. -/
def embDomain (f : Γ ↪o Γ') : HahnSeries Γ R → HahnSeries Γ' R := fun x =>
  { coeff := fun b : Γ' => if h : b ∈ f '' x.support then x.coeff (Classical.choose h) else 0
    isPWO_support' :=
      (x.isPWO_support.image_of_monotone f.monotone).mono fun b hb => by
        contrapose! hb
        rw [Function.mem_support, dif_neg hb, Classical.not_not] }
#align hahn_series.emb_domain HahnSeries.embDomain

@[simp]
theorem embDomain_coeff {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {a : Γ} :
    (embDomain f x).coeff (f a) = x.coeff a := by
  rw [embDomain]
  dsimp only
  by_cases ha : a ∈ x.support
  · rw [dif_pos (Set.mem_image_of_mem f ha)]
    exact congr rfl (f.injective (Classical.choose_spec (Set.mem_image_of_mem f ha)).2)
  · rw [dif_neg, Classical.not_not.1 fun c => ha ((mem_support _ _).2 c)]
    contrapose! ha
    obtain ⟨b, hb1, hb2⟩ := (Set.mem_image _ _ _).1 ha
    rwa [f.injective hb2] at hb1
#align hahn_series.emb_domain_coeff HahnSeries.embDomain_coeff

@[simp]
theorem embDomain_mk_coeff {f : Γ → Γ'} (hfi : Function.Injective f)
    (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') {x : HahnSeries Γ R} {a : Γ} :
    (embDomain ⟨⟨f, hfi⟩, hf _ _⟩ x).coeff (f a) = x.coeff a :=
  embDomain_coeff
#align hahn_series.emb_domain_mk_coeff HahnSeries.embDomain_mk_coeff

theorem embDomain_notin_image_support {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {b : Γ'}
    (hb : b ∉ f '' x.support) : (embDomain f x).coeff b = 0 :=
  dif_neg hb
#align hahn_series.emb_domain_notin_image_support HahnSeries.embDomain_notin_image_support

theorem support_embDomain_subset {f : Γ ↪o Γ'} {x : HahnSeries Γ R} :
    support (embDomain f x) ⊆ f '' x.support := by
  intro g hg
  contrapose! hg
  rw [mem_support, embDomain_notin_image_support hg, Classical.not_not]
#align hahn_series.support_emb_domain_subset HahnSeries.support_embDomain_subset

theorem embDomain_notin_range {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {b : Γ'} (hb : b ∉ Set.range f) :
    (embDomain f x).coeff b = 0 :=
  embDomain_notin_image_support fun con => hb (Set.image_subset_range _ _ con)
#align hahn_series.emb_domain_notin_range HahnSeries.embDomain_notin_range

@[simp]
theorem embDomain_zero {f : Γ ↪o Γ'} : embDomain f (0 : HahnSeries Γ R) = 0 := by
  ext
  simp [embDomain_notin_image_support]
#align hahn_series.emb_domain_zero HahnSeries.embDomain_zero

@[simp]
theorem embDomain_single {f : Γ ↪o Γ'} {g : Γ} {r : R} :
    embDomain f (single g r) = single (f g) r := by
  ext g'
  by_cases h : g' = f g
  · simp [h]
  rw [embDomain_notin_image_support, single_coeff_of_ne h]
  by_cases hr : r = 0
  · simp [hr]
  rwa [support_single_of_ne hr, Set.image_singleton, Set.mem_singleton_iff]
#align hahn_series.emb_domain_single HahnSeries.embDomain_single

theorem embDomain_injective {f : Γ ↪o Γ'} :
    Function.Injective (embDomain f : HahnSeries Γ R → HahnSeries Γ' R) := fun x y xy => by
  ext g
  rw [HahnSeries.ext_iff, Function.funext_iff] at xy
  have xyg := xy (f g)
  rwa [embDomain_coeff, embDomain_coeff] at xyg
#align hahn_series.emb_domain_injective HahnSeries.embDomain_injective

end Domain

end Zero

section LinearOrder

theorem le_orderTop_iff [LinearOrder Γ] [Zero R] {x : HahnSeries Γ R} {i : WithTop Γ} :
    i ≤ x.orderTop ↔ (∀ (j : Γ), j < i → x.coeff j = 0) := by
  refine { mp := fun hi j hj =>
    coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le hj hi), mpr := fun hj => ?_ }
  by_cases hx : x = 0
  · simp_all only [zero_coeff, implies_true, orderTop_zero, le_top]
  · by_contra h
    specialize hj (x.isWF_support.min (support_nonempty_iff.2 hx))
    simp_all [not_le, orderTop_of_ne hx, ← leadingCoeff_of_ne hx, leadingCoeff_ne_iff.mp hx]

section LocallyFiniteLinearOrder

variable [Zero R]

theorem suppBddBelow_supp_PWO [LinearOrder Γ] [LocallyFiniteOrder Γ] (f : Γ → R)
    (hf : BddBelow (Function.support f)) : (Function.support f).IsPWO :=
  Set.isWF_iff_isPWO.mp hf.wellFoundedOn_lt

theorem forallLTEqZero_supp_BddBelow [LinearOrder Γ] (f : Γ → R) (n : Γ)
    (hn : ∀(m : Γ), m < n → f m = 0) : BddBelow (Function.support f) := by
  simp only [BddBelow, Set.Nonempty, lowerBounds]
  use n
  intro m hm
  rw [Function.mem_support, ne_eq] at hm
  exact not_lt.mp (mt (hn m) hm)

/-- Construct a Hahn series from any function whose support is bounded below. -/
@[simps]
def ofSuppBddBelow [LinearOrder Γ] [LocallyFiniteOrder Γ] (f : Γ → R)
    (hf : BddBelow (Function.support f)) : HahnSeries Γ R where
  coeff := f
  isPWO_support' := suppBddBelow_supp_PWO f hf

theorem BddBelow_zero [Preorder Γ] [Nonempty Γ] : BddBelow (Function.support (0 : Γ → R)) := by
  simp only [support_zero', bddBelow_empty]

@[simp]
theorem zero_ofSuppBddBelow [LinearOrder Γ] [LocallyFiniteOrder Γ] [Nonempty Γ] :
    ofSuppBddBelow 0 BddBelow_zero = (0 : HahnSeries Γ R) :=
  rfl

theorem order_ofForallLtEqZero [LinearOrder Γ] [LocallyFiniteOrder Γ] [Zero Γ] (f : Γ → R)
    (hf : f ≠ 0) (n : Γ) (hn : ∀(m : Γ), m < n → f m = 0) :
    n ≤ order (ofSuppBddBelow f (forallLTEqZero_supp_BddBelow f n hn)) := by
  dsimp only [order]
  by_cases h : ofSuppBddBelow f (forallLTEqZero_supp_BddBelow f n hn) = 0
  cases h
  · exact (hf rfl).elim
  simp_all only [dite_false]
  rw [Set.IsWF.le_min_iff]
  intro m hm
  rw [HahnSeries.support, Function.mem_support, ne_eq] at hm
  exact not_lt.mp (mt (hn m) hm)

end LocallyFiniteLinearOrder

end LinearOrder

end HahnSeries
