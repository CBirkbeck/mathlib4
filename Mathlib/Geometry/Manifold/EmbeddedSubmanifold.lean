/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.IsImmersionEmbedding

/-!
# Embedded submanifolds

TODO: write doc-string when things are clearer

-/

open scoped Manifold ContDiff
open Topology Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {J : ModelWithCorners 𝕜 E'' H''}
  {M M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] {n : WithTop ℕ∞}

variable (I I' F) in
/-- Two models with corners `I` and `I'` form a **slice model** if "I includes into I'".
More precisely, there are an embedding `H → H'` and a continuous linear map `E → E'` so the diagram
  H  -I  → E'
  |        |
  |        |
  H' -I' → E'
commutes. More precisely, we prescribe a linear equivalence `E × F → E`, for some normed space `F`,
which induces the map `E → E'` in the obvious way.
-/
class SliceModel where
  equiv: (E × F) ≃L[𝕜] E'
  map: H → H'
  hmap : Topology.IsEmbedding map
  compatible : I' ∘ map = equiv ∘ ((·, 0) : E → E × F) ∘ I

namespace SliceModel

/-- A choice of inverse of `map`: its value outside of `range map` is unspecified. -/
noncomputable def inverse [Nonempty H] (h : SliceModel F I I') : H' → H :=
  (Function.extend h.map id (fun _ ↦ (Classical.arbitrary H)))

-- warm-up: I' ∘ map ⊆ im equiv ∘ I: that's basically obvious, nothing to prove

lemma inverse_left_inv [Nonempty H] (h : SliceModel F I I') (x : H) :
    h.inverse (h.map x) = x :=
  Injective.extend_apply h.hmap.injective ..

lemma inverse_right_inv [Nonempty H] (h : SliceModel F I I') (z : H') (hz : z ∈ range h.map) :
    h.map (h.inverse z) = z := by
  choose x hx using hz
  rw [← hx, h.inverse_left_inv]

end SliceModel

section

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [Unique G]

variable (𝕜 E) in
def LinearEquiv.prodUnique : (E × G) ≃ₗ[𝕜] E where
  toEquiv := Equiv.prodUnique E G
  map_add' := sorry
  map_smul' := sorry

@[simp]
lemma LinearEquiv.prodUnique_toEquiv : (LinearEquiv.prodUnique 𝕜 E).toEquiv = Equiv.prodUnique E G := rfl

variable (𝕜 E) in
def ContinuousLinearEquiv.prodUnique : (E × G) ≃L[𝕜] E where
  toLinearEquiv := LinearEquiv.prodUnique 𝕜 E
  continuous_toFun := by
    show Continuous (Equiv.prodUnique E G)
    dsimp; fun_prop
  continuous_invFun := by
    dsimp
    show Continuous (Equiv.prodUnique E G).symm
    sorry -- dsimp; continuity--fun_prop

@[simp]
lemma ContinuousLinearEquiv.prodUnique_toEquiv :
    (ContinuousLinearEquiv.prodUnique 𝕜 E).toEquiv = Equiv.prodUnique E G := rfl

@[simp]
lemma ContinuousLinearEquiv.prodUnique_apply (x : E × G) :
    (ContinuousLinearEquiv.prodUnique 𝕜 E) x = x.1 := rfl

@[simp]
lemma ContinuousLinearEquiv.prodUnique_symm_apply (x : E) :
    (ContinuousLinearEquiv.prodUnique 𝕜 E (G := G)).symm x = (x, (sorry : G)) := sorry -- rfl

/- do I want all/any of these lemma?
@[simp]
lemma LinearEquiv.prodSingle_coe {y : G} :
    (LinearEquiv.prodSingleton 𝕜 E (y := y)) = ((·, y) : E → E × G) := rfl
-/

/-- Every model with corners is a slice model over itself. -/
instance : SliceModel (⊥ : Subspace 𝕜 E) I I where
  equiv := ContinuousLinearEquiv.prodUnique 𝕜 E
  map := id
  hmap := Topology.IsEmbedding.id
  compatible := by ext x; dsimp

-- apparently all missing: LinearEquiv.prodCongr, ContinuousLinearEquiv.prodCongr

instance [h : SliceModel F I I'] : SliceModel F (J.prod I) (J.prod I') where
  equiv := by
    let sdf := h.equiv
    -- want h.equiv.prodCongr (.id), and probably re-associating...
    sorry
  map := Prod.map id h.map
  hmap := IsEmbedding.id.prodMap h.hmap
  compatible := sorry

-- a bit more cumbersom, as equiv needs some reordering
instance [h : SliceModel F I I'] : SliceModel F (I.prod J) (I'.prod J) where
  equiv := sorry
  map := Prod.map h.map id
  hmap := h.hmap.prodMap IsEmbedding.id
  compatible := sorry

end

namespace PartialHomeomorph

variable [TopologicalSpace M] [IsManifold I' n M']

variable [Nonempty H] {φ : PartialHomeomorph M' H'} {f : M → M'}
omit [ChartedSpace H' M']

-- continuity of `toFun`
lemma continuousOn_source (h : SliceModel F I I') (hf : Continuous f)
    (hyp : φ.target ⊆ range h.map) : ContinuousOn (h.inverse ∘ φ ∘ f) (f ⁻¹' φ.source) := by
  rw [h.hmap.continuousOn_iff]
  have : ContinuousOn (φ ∘ f) (f ⁻¹' φ.source) :=
    φ.continuousOn_toFun.comp hf.continuousOn (fun ⦃x⦄ a ↦ a)
  apply this.congr
  intro x hx
  apply h.inverse_right_inv
  apply hyp
  rw [← φ.image_source_eq_target]
  exact mem_image_of_mem φ hx

-- auxiliary definition; will become the invFun of pullback_sliceModel
variable (f φ) in
noncomputable def aux_invFun [Nonempty M] (h : SliceModel F I I') : H → M :=
  (Function.extend f id (fun _ ↦ (Classical.arbitrary M))) ∘ φ.symm ∘ h.map

-- continuity of the inverse function
lemma continuousOn_aux_invFun [Nonempty M] (h : SliceModel F I I') (hf : IsEmbedding f)
    (hyp : φ.source ⊆ range f) :
    ContinuousOn (aux_invFun φ f h) (h.map ⁻¹' φ.target) := by
  have : ContinuousOn ((Function.extend f id fun x ↦ Classical.arbitrary M) ∘ φ.symm) φ.target := by
    refine ContinuousOn.comp ?_ φ.continuousOn_symm φ.symm_mapsTo
    -- This holds for any embedding, but seems to be missing.
    have missing : ContinuousOn (Function.extend f id fun x ↦ Classical.arbitrary M) (range f) := by
      -- does this help? refine IsOpenMap.continuousOn_range_of_leftInverse ?_ ?_
      sorry
    exact missing.mono hyp
  exact this.comp h.hmap.continuous.continuousOn (fun ⦃x⦄ a ↦ a)

omit [TopologicalSpace M] in
lemma aux' (h : SliceModel F I I') {y : H'} (hy : y ∈ range (φ ∘ f)) (hy' : y ∈ range h.map) :
    h.map (h.inverse y) = y := by
  choose x hx using hy
  choose x' hx' using hy'
  rw [← hx', h.inverse_left_inv x']

omit [TopologicalSpace M] [Nonempty H] in
theorem missing (h : SliceModel F I I') (hsource : φ.source ⊆ range f)
    {x : H} (hx : h.map x ∈ φ.target) : (φ.symm ∘ h.map) x ∈ range f := by
  rw [← φ.image_source_eq_target] at hx
  choose s hs hsx using hx
  rw [comp_apply, ← hsx, φ.left_inv hs]
  exact hsource hs

variable [Nonempty M]

variable (φ) in
/-- Pull back a partial homeomorphism using a slice model. -/
-- XXX: does this hold for merely inducing maps? depends on the missing sorry for the inverse
noncomputable def pullback_sliceModel (h : SliceModel F I I') (hf : IsEmbedding f)
    (hsource : φ.source ⊆ range f) (htarget : φ.target ⊆ range h.map) : PartialHomeomorph M H where
  toFun := h.inverse ∘ φ ∘ f
  invFun :=
    letI finv := Function.extend f id (fun _ ↦ (Classical.arbitrary M))
    (finv ∘ φ.symm ∘ h.map)
  source := f ⁻¹' φ.source
  open_source := IsOpen.preimage hf.continuous φ.open_source
  target := h.map ⁻¹' φ.target
  open_target := IsOpen.preimage h.hmap.continuous φ.open_target
  map_source' x hx := by
    rw [← φ.image_source_eq_target, mem_preimage]
    convert mem_image_of_mem φ hx
    apply aux' h (mem_range_self x) (htarget ?_)
    exact φ.image_source_eq_target ▸ mem_image_of_mem φ hx
  map_target' x hx := by
    rw [mem_preimage] at hx ⊢
    convert map_target φ hx
    choose x' hx' using missing h hsource hx
    calc
      _ = f (Function.extend f id (fun x ↦ Classical.arbitrary M) ((φ.symm ∘ h.map) x)) := rfl
      _ = (φ.symm ∘ h.map) x := by
        rw [← hx']
        congr
        apply hf.injective.extend_apply
  left_inv' x hx := calc
      _ = ((Function.extend f id fun x ↦ Classical.arbitrary M) ∘ φ.symm ∘
          (h.map ∘ h.inverse) ∘ φ ∘ f) x := rfl
      _ = ((Function.extend f id fun x ↦ Classical.arbitrary M) ∘ φ.symm ∘ φ ∘ f) x := by
        simp_rw [comp_apply]
        congr
        apply aux' h (mem_range_self x) (htarget ?_)
        exact φ.image_source_eq_target ▸ mem_image_of_mem φ hx
      _ = (Function.extend f id fun x ↦ Classical.arbitrary M) (f x) := by
        simp only [comp_apply]
        congr
        apply φ.left_inv' hx
      _ = x := hf.injective.extend_apply _ _ x
  right_inv' x hx := by
    choose x' hx' using missing h hsource hx
    have (x') : (Function.extend f id (fun x ↦ Classical.arbitrary M)) (f x') = x' := by
      simp [hf.injective.extend_apply]
    specialize this x'
    calc
      _ = (h.inverse ∘ φ ∘ f) ((Function.extend f id fun x ↦ Classical.arbitrary M)
          ((φ.symm ∘ h.map) x)) := rfl
      _ = (h.inverse ∘ φ) ((φ.symm ∘ h.map) x) := by
        rw [← hx', this]
        simp_rw [comp_apply]
      _ = h.inverse ((φ ∘ φ.symm) (h.map x)) := by simp [Function.comp_apply]
      _ = h.inverse (h.map x) := by congr; exact φ.right_inv' hx
      _ = x := h.inverse_left_inv x
  continuousOn_toFun := continuousOn_source h hf.continuous htarget
  continuousOn_invFun := continuousOn_aux_invFun h hf hsource

end PartialHomeomorph

variable (I I' F M M' n) in
class IsImmersedSubmanifold [TopologicalSpace M] [IsManifold I' n M'] (h: SliceModel F I I') where
  emb: M → M'
  hemb: IsEmbedding emb
  hcharts_source : ∀ ⦃y⦄, y ∈ range emb → (chartAt H' y).source ⊆ range emb
  hcharts_target : ∀ ⦃y⦄, (hy : y ∈ range emb) →
    (chartAt H' y).target ⊆ range (SliceModel.map F I I')

namespace IsImmersedSubmanifold

variable [TopologicalSpace M] [IsManifold I' n M'] [h: SliceModel F I I'] [Nonempty H] [Nonempty M]

noncomputable def myChart (inst : IsImmersedSubmanifold F I I' M M' n h) (x : M) :
    PartialHomeomorph M H :=
  (chartAt H' (inst.emb x)).pullback_sliceModel h inst.hemb (hcharts_source (mem_range_self x))
    (hcharts_target (mem_range_self x))

-- missing simp lemmas: source, target of pullback!
lemma myChart_source (inst : IsImmersedSubmanifold F I I' M M' n h) (x : M) :
    (inst.myChart x).source = inst.emb ⁻¹' ((chartAt H' (inst.emb x)).source) := by
  rfl

-- XXX: making this an instance makes Lean complain about synthesization order
noncomputable def chartedSpace (inst : IsImmersedSubmanifold F I I' M M' n h) :
    ChartedSpace H M where
  atlas := {inst.myChart x | x : M }
  chartAt x := inst.myChart x
  mem_chart_source x := by
    rw [myChart_source]
    exact mem_chart_source _ (emb n h x)
  chart_mem_atlas x := by rw [mem_setOf]; use x

-- cannot state this yet because of the synthesisation order issue
-- TODO fix, and make an instance
/- noncomputable def isManifold (inst : IsImmersedSubmanifold F I I' M M' n h) :
    haveI : ChartedSpace H M := inst.chartedSpace; IsManifold I n M where
  compatible := sorry -/

/- lemma isImmersion_emb (inst : IsImmersedSubmanifold F I I' M M' n h) :
    IsImmersion F I I' n inst.emb := sorry -/

-- TODO: define embedded submanifolds, deduce that `emb` is an embedding

-- TODO: conversely, if f: M → M' is an immersion (embedding), we can define the image model
-- I₀ on M', prove that this is a slice model and deduce IsImmersedSubmanifold via f
-- (same for embedded)

end IsImmersedSubmanifold
