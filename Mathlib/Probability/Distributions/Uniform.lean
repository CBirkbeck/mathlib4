/-
Copyright (c) 2023 Claus Clausen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claus Clausen
-/

import Mathlib.Probability.Density
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Cdf
import Mathlib.Probability.Distributions.Exponential

/-! # Uniform distributions over ℝ

Define the Uniform Measure over Intervals on the reals

## Main definitions
* `uniformPdfReal`: the function `a b x ↦ 1 / (abs (b-a))` for `x ∈ uIcc a b` or `0` else, which is
  the probability density function of a uniform distribution on the Interval `[(a ⊓ b), (a ⊔ b)]`).
* `uniformPdf`: `ℝ≥0∞`-valued pdf, `uniformPdf a b x = ENNReal.ofReal (uniformPdfReal a b x)`.
* `uniformMeasure`: The uniform measure on `ℝ` defined by `a` and `b`, in case of `a = b`,
  it is the DiracMeasure on `a`.
* `uniformCdfReal`: the Cdf given by the Definition of CDF in `ProbabilityTheory.Cdf`
   on the `uniformMeasure`.

## Main results
* `uniformCdf_eq'`: Proof that the `uniformCdfReal` given by the Definition of the CDF equals the
  known function given as `a b x ↦ (x - a ⊓ b) / (a ⊔ b - a ⊓ b)` for `a ⊓ b ≤ x ≤ a ⊔ b`,
  `0` before and `1` afterwards in the case of `a ≠ b`.
* `uniformCdf_eq`: General equality of the uniformCdf, including the Dirac-case.
-/

open scoped ENNReal NNReal Real

open MeasureTheory Measure Set Filter

namespace ProbabilityTheory

section UniformPdf

/-- Definition of the PDF of the uniform distribution on the reals -/
noncomputable
def uniformPdfReal (a b x : ℝ) : ℝ :=
  indicator (uIcc a b) (fun _ ↦ 1 / (abs (b - a))) x

/-- Definition of the PDF of the uniform distribution on the ENNReals, needed for
  Lebesgue-Integration -/
noncomputable
def uniformPdf (a b x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (uniformPdfReal a b x)

lemma uniformPdf_eq (a b x : ℝ) : uniformPdf a b x =
    ENNReal.ofReal (if x ∈ Icc (a ⊓ b) (a ⊔ b) then (fun x ↦ 1 / abs (b - a)) x else 0) := by
  unfold uniformPdf uniformPdfReal indicator uIcc; congr

@[simp]
lemma uniformPdf_eq_zero_lower {a b : ℝ} : ∫⁻ x in Iio (a ⊓ b) , uniformPdf a b x = 0 := by
  rw [set_lintegral_congr_fun measurableSet_Iio
    (ae_of_all _ fun _ (h : _ < _) ↦
      by rw [uniformPdf_eq, if_neg fun ⟨_, _⟩ ↦ by linarith, ENNReal.ofReal_zero]), lintegral_zero]

@[simp]
lemma uniformPdf_eq_zero_upper {a b : ℝ} : ∫⁻ x in Ioi (a ⊔ b) , uniformPdf a b x = 0 := by
  rw [set_lintegral_congr_fun measurableSet_Ioi
    (ae_of_all _ fun _ (h : _ < _) ↦
      by rw [uniformPdf_eq, if_neg fun ⟨_, _⟩ ↦ by linarith, ENNReal.ofReal_zero]), lintegral_zero]

lemma split_lintegral_of_uniformPdf {a b : ℝ} : (∫⁻ x, uniformPdf a b x) =
    (∫⁻ x in Iio (a ⊓ b) , uniformPdf a b x) + (∫⁻ x in uIcc a b, uniformPdf a b x) +
    ∫⁻ x in Ioi (a ⊔ b), uniformPdf a b x := by
  have union : Iio (a ⊓ b) ∪ uIcc a b ∪ Ioi (a ⊔ b) = univ := by
    ext x; simp [uIcc]
  rw [←set_lintegral_univ, ←lintegral_union measurableSet_uIcc,
      ←lintegral_union measurableSet_Ioi, union]
  · simp [uIcc]
  · rw [uIcc, Set.disjoint_iff]
    intro _
    simp only [mem_inter_iff, mem_Iio, lt_inf_iff, mem_Icc, inf_le_iff, le_sup_iff,
        mem_empty_iff_false, and_imp]
    intro _ _ habx _; rcases habx <;> linarith

/-- The uniform Pdf is measurable-/
lemma measurable_uniformPdfReal (a b : ℝ) : Measurable (uniformPdfReal a b) :=
  Measurable.ite measurableSet_uIcc measurable_const measurable_const

/-- The uniform Pdf is strongly measurable -/
lemma stronglyMeasurable_uniformPdfReal (a b : ℝ) :
    StronglyMeasurable (uniformPdfReal a b) :=
  (measurable_uniformPdfReal a b).stronglyMeasurable

/-- The integral of the uniform PDF is equal to integrating over `uIcc a b` -/
lemma carrier_lintegral_of_uniformPdf {a b : ℝ} : (∫⁻ x, uniformPdf a b x) =
    (∫⁻ x in uIcc a b, uniformPdf a b x) := by
  simp [split_lintegral_of_uniformPdf]

/-- the uniform PDF integrates to 1 -/
lemma lintegral_uniformPdf_eq_one (a b : ℝ) (hab : a ≠ b) :
    ∫⁻ x, uniformPdf a b x = 1 := by
  rw [carrier_lintegral_of_uniformPdf]
  simp only [uniformPdf_eq, uIcc]
  rw [set_lintegral_congr_fun measurableSet_Icc (ae_of_all _ (fun _ hx ↦ by rw [if_pos hx])),
      set_lintegral_const, Real.volume_Icc, one_div, LatticeOrderedGroup.sup_sub_inf_eq_abs_sub,
      ← ENNReal.ofReal_mul' (abs_nonneg (b - a)), inv_mul_cancel ?neq, ENNReal.ofReal_one]
  exact ne_iff_lt_or_gt.mpr (Or.inr (abs_pos.mpr (sub_ne_zero.mpr hab.symm)))

end UniformPdf

open MeasureTheory

/-- Measure defined by the uniform Distribution -/
noncomputable
def uniformMeasure (a b : ℝ) : Measure ℝ :=
  if a = b then Measure.dirac a else volume.withDensity (uniformPdf a b)

/-- Uniformmeasure as an Instance of a Probabilitymeasure -/
instance instIsProbabilityMeasureUniform (a b : ℝ) :
    IsProbabilityMeasure (uniformMeasure a b) where
  measure_univ := by
    unfold uniformMeasure
    split_ifs with hab
    · exact measure_univ
    · simp [lintegral_uniformPdf_eq_one a b hab]

section UniformCdf

/-- The CDF of the uniform Distribution -/
noncomputable
def uniformCdfReal (a b : ℝ) : StieltjesFunction :=
  cdf (uniformMeasure a b)

/-- The uniform CDF equals the integration of the PDF -/
lemma uniformCdf_eq_lintegral {a b : ℝ} (hab : a ≠ b) :
    uniformCdfReal a b = fun x ↦ ENNReal.toReal (∫⁻ x in (Iic x), uniformPdf a b x) := by
  ext x
  simp only [cdf_eq_toReal, uniformCdfReal]
  simp [uniformMeasure, if_neg hab, uniformPdf, cdf_eq_toReal]

/-- Equality of the CDF of the uniform distribution in case of `a = b` -/
lemma uniformCdfReal_eq_dirac {a b x: ℝ} (hab : a = b) :
    uniformCdfReal a b x = ENNReal.toReal (if a ≤ x then 1 else 0) := by
  simp only [uniformCdfReal, cdf_eq_toReal, uniformMeasure, if_pos hab, measurableSet_Iic,
    dirac_apply', mem_Iic, not_le, indicator, ENNReal.toReal_eq_toReal_iff]
  left
  rfl

lemma uniformCdfReal_eq_zero {a b : ℝ} x (hx: x < a ⊓ b) : uniformCdfReal a b x = 0 := by
  by_cases hab : a = b
  · rw [uniformCdfReal_eq_dirac hab, if_neg (by simp at hx; linarith)]
    rfl
  · simp only [uniformCdf_eq_lintegral hab, uniformPdf_eq]
    rw [set_lintegral_congr_fun measurableSet_Iic, lintegral_zero]
    · rfl
    · apply ae_of_all
      rintro y (hy : y ≤ _)
      rw [if_neg fun ⟨_, _⟩ ↦ by linarith, ENNReal.ofReal_zero]

lemma uniformCdfReal_eq_fromInf {a b : ℝ} (x : ℝ) (h : a ⊓ b ≤ x) (hab : a ≠ b) :
    uniformCdfReal a b x =
    ENNReal.toReal (∫⁻ x' in Icc (a ⊓ b) x, uniformPdf a b x') := by
  simp [uniformCdf_eq_lintegral hab, lintegral_Iic_eq_lintegral_Iio_add_Icc _ h]

lemma uniformCdfReal_eq_toSup {a b : ℝ} (x : ℝ) (h : a ⊔ b ≤ x) (hab : a ≠ b) :
    uniformCdfReal a b x = ENNReal.toReal (∫⁻ x' in Icc (a ⊓ b) (a ⊔ b), uniformPdf a b x') := by
  rw [uniformCdfReal_eq_fromInf _ (le_trans inf_le_sup h) hab, ← Icc_union_Ioc_eq_Icc inf_le_sup h,
      lintegral_union measurableSet_Ioc]
  have : ∫⁻ y in Ioc (a ⊔ b) x, uniformPdf a b y = 0 := by
    rw [set_lintegral_congr_fun measurableSet_Ioc, lintegral_zero]
    apply ae_of_all
    rintro x' ⟨hx' : _ < x',_ ⟩
    rw [uniformPdf_eq, if_neg fun ⟨_, _⟩ ↦ by linarith, ENNReal.ofReal_zero]
  simp only [ge_iff_le, le_sup_iff, inf_le_left, inf_le_right, or_self, not_true, gt_iff_lt,
    lt_inf_iff, sup_lt_iff, lt_self_iff_false, false_and, and_false, and_self, not_and, not_lt,
    this, add_zero]
  rw [Set.disjoint_iff]
  rintro x ⟨⟨_, h2⟩, ⟨h3, _⟩⟩; linarith

/-- The CDF of the uniform distribution equals the known formular for `a ≠ b` -/
lemma uniformCdfReal_eq' {a b x: ℝ} (hab : a ≠ b) : uniformCdfReal a b x =
    if a ⊓ b ≤ x then if x < a ⊔ b then (x - a ⊓ b) / (a ⊔ b - a ⊓ b) else 1 else 0 := by
  split_ifs with h h'<;> push_neg at *
  · simp only [uniformCdfReal_eq_fromInf _ h hab, uniformPdf_eq]
    rw [set_lintegral_congr_fun measurableSet_Icc
        (g := fun _ ↦ ENNReal.ofReal (1 / (a ⊔ b - a ⊓ b)))]
    · simp only [inv_nonneg, sub_nonneg, le_sup_iff, inf_le_left, inf_le_right, one_div,
      lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter, Real.volume_Icc,
      ENNReal.toReal_mul, mem_Icc, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
      rw [inv_mul_eq_div, ENNReal.toReal_ofReal]
      linarith
    · exact ae_of_all _
        fun x ⟨h, _⟩ ↦ by rw [if_pos ⟨h, by linarith⟩, LatticeOrderedGroup.sup_sub_inf_eq_abs_sub]
  · simp only [uniformCdfReal_eq_toSup _ h' hab, uniformPdf_eq]
    rw [set_lintegral_congr_fun measurableSet_Icc
        (g := fun _ ↦ ENNReal.ofReal (1 / (a ⊔ b - a ⊓ b)))]
    · simp [inv_mul_cancel (sub_ne_zero.2 (ne_of_lt (inf_lt_sup.mpr hab)).symm)]
    · exact ae_of_all _ fun _ hx ↦ by rw [if_pos hx, LatticeOrderedGroup.sup_sub_inf_eq_abs_sub]
  · exact uniformCdfReal_eq_zero _ h

/-- General case of the equation of the CDF of the uniform distribution -/
lemma uniformCdfReal_eq (a b x : ℝ) : uniformCdfReal a b x =
    if a = b then ENNReal.toReal (if a ≤ x then 1 else 0) else
    if a ⊓ b ≤ x then if x < a ⊔ b then (x - a ⊓ b) / (a ⊔ b - a ⊓ b) else 1 else 0 := by
  by_cases a = b
  · rw [if_pos h, uniformCdfReal_eq_dirac h]
  · rw [if_neg h, uniformCdfReal_eq' h]
