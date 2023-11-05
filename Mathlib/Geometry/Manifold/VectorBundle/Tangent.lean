/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.Geometry.Manifold.VectorBundle.Basic

#align_import geometry.manifold.vector_bundle.tangent from "leanprover-community/mathlib"@"e473c3198bb41f68560cab68a0529c854b618833"

/-! # Tangent bundles

This file defines the tangent bundle as a smooth vector bundle.

Let `M` be a smooth manifold with corners with model `I` on `(E, H)`. We define the tangent bundle
of `M` using the `VectorBundleCore` construction indexed by the charts of `M` with fibers `E`.
Given two charts `i, j : LocalHomeomorph M H`, the coordinate change between `i` and `j` at a point
`x : M` is the derivative of the composite
```
  I.symm   i.symm    j     I
E -----> H -----> M --> H --> E
```
within the set `range I ⊆ E` at `I (i x) : E`.
This defines a smooth vector bundle `TangentBundle` with fibers `TangentSpace`.

## Main definitions

* `TangentSpace I M x` is the fiber of the tangent bundle at `x : M`, which is defined to be `E`.

* `TangentBundle I M` is the total space of `TangentSpace I M`, proven to be a smooth vector
  bundle.
-/


open Bundle Set SmoothManifoldWithCorners LocalHomeomorph ContinuousLinearMap

open scoped Manifold Topology Bundle

noncomputable section

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M'] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (I)

/-- Auxiliary lemma for tangent spaces: the derivative of a coordinate change between two charts is
  smooth on its source. -/
theorem contDiffOn_fderiv_coord_change (i j : atlas H M) :
    ContDiffOn 𝕜 ∞ (fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I))
      ((i.1.extend I).symm ≫ j.1.extend I).source := by
  have h : ((i.1.extend I).symm ≫ j.1.extend I).source ⊆ range I := by
    rw [i.1.extend_coord_change_source]; apply image_subset_range
  intro x hx
  refine' (ContDiffWithinAt.fderivWithin_right _ I.unique_diff le_top <| h hx).mono h
  refine' (LocalHomeomorph.contDiffOn_extend_coord_change I (subset_maximalAtlas I j.2)
    (subset_maximalAtlas I i.2) x hx).mono_of_mem _
  exact i.1.extend_coord_change_source_mem_nhdsWithin j.1 I hx

variable (M)

open SmoothManifoldWithCorners

/-- Let `M` be a smooth manifold with corners with model `I` on `(E, H)`.
Then `VectorBundleCore I M` is the vector bundle core for the tangent bundle over `M`.
It is indexed by the atlas of `M`, with fiber `E` and its change of coordinates from the chart `i`
to the chart `j` at point `x : M` is the derivative of the composite
```
  I.symm   i.symm    j     I
E -----> H -----> M --> H --> E
```
within the set `range I ⊆ E` at `I (i x) : E`. -/
@[simps indexAt coordChange]
def tangentBundleCore : VectorBundleCore 𝕜 M E (atlas H M) where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart H
  mem_baseSet_at := mem_chart_source H
  coordChange i j x :=
    fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I) (i.1.extend I x)
  coordChange_self i x hx v := by
    simp only
    rw [Filter.EventuallyEq.fderivWithin_eq, fderivWithin_id', ContinuousLinearMap.id_apply]
    · exact I.unique_diff_at_image
    · filter_upwards [i.1.extend_target_mem_nhdsWithin I hx] with y hy
      exact (i.1.extend I).right_inv hy
    · simp_rw [Function.comp_apply, i.1.extend_left_inv I hx]
  continuousOn_coordChange i j := by
    refine' (contDiffOn_fderiv_coord_change I i j).continuousOn.comp
      ((i.1.continuousOn_extend I).mono _) _
    · rw [i.1.extend_source]; exact inter_subset_left _ _
    simp_rw [← i.1.extend_image_source_inter, mapsTo_image]
  coordChange_comp := by
    rintro i j k x ⟨⟨hxi, hxj⟩, hxk⟩ v
    rw [fderivWithin_fderivWithin, Filter.EventuallyEq.fderivWithin_eq]
    · have := i.1.extend_preimage_mem_nhds I hxi (j.1.extend_source_mem_nhds I hxj)
      filter_upwards [nhdsWithin_le_nhds this] with y hy
      simp_rw [Function.comp_apply, (j.1.extend I).left_inv hy]
    · simp_rw [Function.comp_apply, i.1.extend_left_inv I hxi, j.1.extend_left_inv I hxj]
    · exact (contDiffWithinAt_extend_coord_change' I (subset_maximalAtlas I k.2)
        (subset_maximalAtlas I j.2) hxk hxj).differentiableWithinAt le_top
    · exact (contDiffWithinAt_extend_coord_change' I (subset_maximalAtlas I j.2)
        (subset_maximalAtlas I i.2) hxj hxi).differentiableWithinAt le_top
    · intro x _; exact mem_range_self _
    · exact I.unique_diff_at_image
    · rw [Function.comp_apply, i.1.extend_left_inv I hxi]

-- porting note: moved to a separate `simp high` lemma b/c `simp` can simplify the LHS
@[simp high]
theorem tangentBundleCore_baseSet (i) : (tangentBundleCore I M).baseSet i = i.1.source := rfl

variable {M}

theorem tangentBundleCore_coordChange_achart (x x' z : M) :
    (tangentBundleCore I M).coordChange (achart H x) (achart H x') z =
      fderivWithin 𝕜 (extChartAt I x' ∘ (extChartAt I x).symm) (range I) (extChartAt I x z) :=
  rfl

/-- The tangent space at a point of the manifold `M`. It is just `E`. We could use instead
`(tangentBundleCore I M).to_topological_vector_bundle_core.fiber x`, but we use `E` to help the
kernel.
-/
@[nolint unusedArguments]
def TangentSpace {𝕜} [NontriviallyNormedField 𝕜] {E} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M} [TopologicalSpace M]
    [ChartedSpace H M] [SmoothManifoldWithCorners I M] (_x : M) : Type* := E
-- porting note: was deriving TopologicalSpace, AddCommGroup, TopologicalAddGroup

instance {x : M} : TopologicalSpace (TangentSpace I x) := inferInstanceAs (TopologicalSpace E)
instance {x : M} : AddCommGroup (TangentSpace I x) := inferInstanceAs (AddCommGroup E)
instance {x : M} : TopologicalAddGroup (TangentSpace I x) := inferInstanceAs (TopologicalAddGroup E)

variable (M)

-- is empty if the base manifold is empty
/-- The tangent bundle to a smooth manifold, as a Sigma type. Defined in terms of
`Bundle.TotalSpace` to be able to put a suitable topology on it. -/
@[reducible] -- porting note: was nolint has_nonempty_instance
def TangentBundle :=
  Bundle.TotalSpace E (TangentSpace I : M → Type _)

local notation "TM" => TangentBundle I M

section TangentBundleInstances

/- In general, the definition of tangent_space is not reducible, so that type class inference
does not pick wrong instances. In this section, we record the right instances for
them, noting in particular that the tangent bundle is a smooth manifold. -/
section

variable {M} (x : M)

instance : Module 𝕜 (TangentSpace I x) := inferInstanceAs (Module 𝕜 E)

instance : Inhabited (TangentSpace I x) := ⟨0⟩

-- porting note: removed unneeded ContinuousAdd (TangentSpace I x)

end

instance : TopologicalSpace TM :=
  (tangentBundleCore I M).toTopologicalSpace

instance TangentSpace.fiberBundle : FiberBundle E (TangentSpace I : M → Type _) :=
  (tangentBundleCore I M).fiberBundle

instance TangentSpace.vectorBundle : VectorBundle 𝕜 E (TangentSpace I : M → Type _) :=
  (tangentBundleCore I M).vectorBundle

namespace TangentBundle

protected theorem chartAt (p : TM) :
    chartAt (ModelProd H E) p =
      ((tangentBundleCore I M).toFiberBundleCore.localTriv (achart H p.1)).toLocalHomeomorph ≫ₕ
        (chartAt H p.1).prod (LocalHomeomorph.refl E) :=
  rfl

theorem chartAt_toLocalEquiv (p : TM) :
    (chartAt (ModelProd H E) p).toLocalEquiv =
      (tangentBundleCore I M).toFiberBundleCore.localTrivAsLocalEquiv (achart H p.1) ≫
        (chartAt H p.1).toLocalEquiv.prod (LocalEquiv.refl E) :=
  rfl

theorem trivializationAt_eq_localTriv (x : M) :
    trivializationAt E (TangentSpace I) x =
      (tangentBundleCore I M).toFiberBundleCore.localTriv (achart H x) :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_source (x : M) :
    (trivializationAt E (TangentSpace I) x).source =
      π E (TangentSpace I) ⁻¹' (chartAt H x).source :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_target (x : M) :
    (trivializationAt E (TangentSpace I) x).target = (chartAt H x).source ×ˢ univ :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_baseSet (x : M) :
    (trivializationAt E (TangentSpace I) x).baseSet = (chartAt H x).source :=
  rfl

theorem trivializationAt_apply (x : M) (z : TM) :
    trivializationAt E (TangentSpace I) x z =
      (z.1, fderivWithin 𝕜 ((chartAt H x).extend I ∘ ((chartAt H z.1).extend I).symm) (range I)
        ((chartAt H z.1).extend I z.1) z.2) :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_fst (x : M) (z : TM) : (trivializationAt E (TangentSpace I) x z).1 = z.1 :=
  rfl

@[simp, mfld_simps]
theorem mem_chart_source_iff (p q : TM) :
    p ∈ (chartAt (ModelProd H E) q).source ↔ p.1 ∈ (chartAt H q.1).source := by
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]

@[simp, mfld_simps]
theorem mem_chart_target_iff (p : H × E) (q : TM) :
    p ∈ (chartAt (ModelProd H E) q).target ↔ p.1 ∈ (chartAt H q.1).target := by
  /- porting note: was
  simp (config := { contextual := true }) only [FiberBundle.chartedSpace_chartAt,
    and_iff_left_iff_imp, mfld_simps]
  -/
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]
  rw [LocalEquiv.prod_symm]
  simp (config := { contextual := true }) only [and_iff_left_iff_imp, mfld_simps]

@[simp, mfld_simps]
theorem coe_chartAt_fst (p q : TM) : ((chartAt (ModelProd H E) q) p).1 = chartAt H q.1 p.1 :=
  rfl

@[simp, mfld_simps]
theorem coe_chartAt_symm_fst (p : H × E) (q : TM) :
    ((chartAt (ModelProd H E) q).symm p).1 = ((chartAt H q.1).symm : H → M) p.1 :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_continuousLinearMapAt {b₀ b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet) :
    (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt 𝕜 b =
      (tangentBundleCore I M).coordChange (achart H b) (achart H b₀) b :=
  (tangentBundleCore I M).localTriv_continuousLinearMapAt hb

@[simp, mfld_simps]
theorem trivializationAt_symmL {b₀ b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet) :
    (trivializationAt E (TangentSpace I) b₀).symmL 𝕜 b =
      (tangentBundleCore I M).coordChange (achart H b₀) (achart H b) b :=
  (tangentBundleCore I M).localTriv_symmL hb

-- porting note: `simp` simplifies LHS to `.id _ _`
@[simp high, mfld_simps]
theorem coordChange_model_space (b b' x : F) :
    (tangentBundleCore 𝓘(𝕜, F) F).coordChange (achart F b) (achart F b') x = 1 := by
  simpa only [tangentBundleCore_coordChange, mfld_simps] using
    fderivWithin_id uniqueDiffWithinAt_univ

-- porting note: `simp` simplifies LHS to `.id _ _`
@[simp high, mfld_simps]
theorem symmL_model_space (b b' : F) :
    (trivializationAt F (TangentSpace 𝓘(𝕜, F)) b).symmL 𝕜 b' = (1 : F →L[𝕜] F) := by
  rw [TangentBundle.trivializationAt_symmL, coordChange_model_space]
  apply mem_univ

-- porting note: `simp` simplifies LHS to `.id _ _`
@[simp high, mfld_simps]
theorem continuousLinearMapAt_model_space (b b' : F) :
    (trivializationAt F (TangentSpace 𝓘(𝕜, F)) b).continuousLinearMapAt 𝕜 b' = (1 : F →L[𝕜] F) := by
  rw [TangentBundle.trivializationAt_continuousLinearMapAt, coordChange_model_space]
  apply mem_univ

end TangentBundle

instance tangentBundleCore.isSmooth : (tangentBundleCore I M).IsSmooth I := by
  refine' ⟨fun i j => _⟩
  rw [SmoothOn, contMDiffOn_iff_source_of_mem_maximalAtlas (subset_maximalAtlas I i.2),
    contMDiffOn_iff_contDiffOn]
  refine' ((contDiffOn_fderiv_coord_change I i j).congr fun x hx => _).mono _
  · rw [LocalEquiv.trans_source'] at hx
    simp_rw [Function.comp_apply, tangentBundleCore_coordChange, (i.1.extend I).right_inv hx.1]
  · exact (i.1.extend_image_source_inter j.1 I).subset
  · apply inter_subset_left

instance TangentBundle.smoothVectorBundle : SmoothVectorBundle E (TangentSpace I : M → Type _) I :=
  (tangentBundleCore I M).smoothVectorBundle _

end TangentBundleInstances

/-! ## The tangent bundle to the model space -/


/-- In the tangent bundle to the model space, the charts are just the canonical identification
between a product type and a sigma type, a.k.a. `TotalSpace.toProd`. -/
@[simp, mfld_simps]
theorem tangentBundle_model_space_chartAt (p : TangentBundle I H) :
    (chartAt (ModelProd H E) p).toLocalEquiv = (TotalSpace.toProd H E).toLocalEquiv := by
  ext x : 1
  · ext; · rfl
    exact (tangentBundleCore I H).coordChange_self (achart _ x.1) x.1 (mem_achart_source H x.1) x.2
  · -- porting note: was ext; · rfl; apply hEq_of_eq
    refine congr_arg (TotalSpace.mk _) ?_
    exact (tangentBundleCore I H).coordChange_self (achart _ x.1) x.1 (mem_achart_source H x.1) x.2
  simp_rw [TangentBundle.chartAt, FiberBundleCore.localTriv, FiberBundleCore.localTrivAsLocalEquiv,
    VectorBundleCore.toFiberBundleCore_baseSet, tangentBundleCore_baseSet]
  simp only [mfld_simps]

@[simp, mfld_simps]
theorem tangentBundle_model_space_coe_chartAt (p : TangentBundle I H) :
    ⇑(chartAt (ModelProd H E) p) = TotalSpace.toProd H E := by
  rw [← LocalHomeomorph.coe_coe, tangentBundle_model_space_chartAt]; rfl

@[simp, mfld_simps]
theorem tangentBundle_model_space_coe_chartAt_symm (p : TangentBundle I H) :
    ((chartAt (ModelProd H E) p).symm : ModelProd H E → TangentBundle I H) =
      (TotalSpace.toProd H E).symm := by
  rw [← LocalHomeomorph.coe_coe, LocalHomeomorph.symm_toLocalEquiv,
    tangentBundle_model_space_chartAt]; rfl

theorem tangentBundleCore_coordChange_model_space (x x' z : H) :
    (tangentBundleCore I H).coordChange (achart H x) (achart H x') z = ContinuousLinearMap.id 𝕜 E :=
  by ext v; exact (tangentBundleCore I H).coordChange_self (achart _ z) z (mem_univ _) v

variable (H)

/-- The canonical identification between the tangent bundle to the model space and the product,
as a homeomorphism -/
def tangentBundleModelSpaceHomeomorph : TangentBundle I H ≃ₜ ModelProd H E :=
  { TotalSpace.toProd H E with
    continuous_toFun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
      have : Continuous (chartAt (ModelProd H E) p) := by
        rw [continuous_iff_continuousOn_univ]
        convert (chartAt (ModelProd H E) p).continuousOn
        simp only [TangentSpace.fiberBundle, mfld_simps]
      simpa only [mfld_simps] using this
    continuous_invFun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
      have : Continuous (chartAt (ModelProd H E) p).symm := by
        rw [continuous_iff_continuousOn_univ]
        convert (chartAt (ModelProd H E) p).symm.continuousOn
        simp only [mfld_simps]
      simpa only [mfld_simps] using this }

@[simp, mfld_simps]
theorem tangentBundleModelSpaceHomeomorph_coe :
    (tangentBundleModelSpaceHomeomorph H I : TangentBundle I H → ModelProd H E) =
      TotalSpace.toProd H E :=
  rfl

@[simp, mfld_simps]
theorem tangentBundleModelSpaceHomeomorph_coe_symm :
    ((tangentBundleModelSpaceHomeomorph H I).symm : ModelProd H E → TangentBundle I H) =
      (TotalSpace.toProd H E).symm :=
  rfl

section inTangentCoordinates

variable (I') {M H} {N : Type*}

/-- The map `in_coordinates` for the tangent bundle is trivial on the model spaces -/
theorem inCoordinates_tangent_bundle_core_model_space (x₀ x : H) (y₀ y : H') (ϕ : E →L[𝕜] E') :
    inCoordinates E (TangentSpace I) E' (TangentSpace I') x₀ x y₀ y ϕ = ϕ := by
  erw [VectorBundleCore.inCoordinates_eq] <;> try trivial
  simp_rw [tangentBundleCore_indexAt, tangentBundleCore_coordChange_model_space,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]

/-- When `ϕ x` is a continuous linear map that changes vectors in charts around `f x` to vectors
in charts around `g x`, `inTangentCoordinates I I' f g ϕ x₀ x` is a coordinate change of
this continuous linear map that makes sense from charts around `f x₀` to charts around `g x₀`
by composing it with appropriate coordinate changes.
Note that the type of `ϕ` is more accurately
`Π x : N, TangentSpace I (f x) →L[𝕜] TangentSpace I' (g x)`.
We are unfolding `TangentSpace` in this type so that Lean recognizes that the type of `ϕ` doesn't
actually depend on `f` or `g`.

This is the underlying function of the trivializations of the hom of (pullbacks of) tangent spaces.
-/
def inTangentCoordinates (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') : N → N → E →L[𝕜] E' :=
  fun x₀ x => inCoordinates E (TangentSpace I) E' (TangentSpace I') (f x₀) (f x) (g x₀) (g x) (ϕ x)

theorem inTangentCoordinates_model_space (f : N → H) (g : N → H') (ϕ : N → E →L[𝕜] E') (x₀ : N) :
    inTangentCoordinates I I' f g ϕ x₀ = ϕ := by
  simp_rw [inTangentCoordinates, inCoordinates_tangent_bundle_core_model_space]

theorem inTangentCoordinates_eq (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') {x₀ x : N}
    (hx : f x ∈ (chartAt H (f x₀)).source) (hy : g x ∈ (chartAt H' (g x₀)).source) :
    inTangentCoordinates I I' f g ϕ x₀ x =
      (tangentBundleCore I' M').coordChange (achart H' (g x)) (achart H' (g x₀)) (g x) ∘L
        ϕ x ∘L (tangentBundleCore I M).coordChange (achart H (f x₀)) (achart H (f x)) (f x) :=
  (tangentBundleCore I M).inCoordinates_eq (tangentBundleCore I' M') (ϕ x) hx hy

end inTangentCoordinates

end General

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]

instance {x : M} : PathConnectedSpace (TangentSpace I x) := by unfold TangentSpace; infer_instance

end Real
