/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv

/-!
# Local diffeomorphisms between smooth manifolds

In this file, we define `C^n` local diffeomorphisms between manifolds.

A `C^n` map `f : M → N` is a **local diffeomorphism at `x`** iff there are neighbourhoods `s`
and `t` of `x` and `f x`, respectively such that `f` restricts to a diffeomorphism from `s` and `t`.
`f` is called a **local diffeomorphism** iff it is a local diffeomorphism at every `x ∈ M`.

## Main definitions
* `LocalDiffeomorphAt I J M N n f x`: `f` is a `C^n` local diffeomorphism at `x`
* `LocalDiffeomorph I J M N n f`: `f` is a `C^n` local diffeomorphism

## Main results
* Each of `Diffeomorph`, `LocalDiffeomorph`, and `LocalDiffeomorphAt` implies the next condition.
* `LocalDiffeomorph.image`: the image of a local diffeomorphism is open

* `Diffeomorph.mfderiv_toContinuousLinearEquiv`: each differential of a `C^n` diffeomorphism
(`n ≥ 1`) is a linear equivalence.
* `LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv`: if `f` is a local diffeomorphism
at `x`, the differential `mfderiv I J n f x` is a continuous linear isomorphism.
* `LocalDiffeomorph.differential_toContinuousLinearEquiv`: if `f` is a local diffeomorphism,
each differential `mfderiv I J n f x` is a continuous linear isomorphism.

## TODO
* a local diffeomorphism is a diffeomorphism to its image
* a bijective local diffeomorphism is a diffeomorphism.
* if `f` is `C^n` at `x` and `mfderiv I J n f x` is a linear isomorphism,
`f` is a local diffeomorphism at `x`.
* if `f` is `C^n` and each differential is a linear isomorphism, `f` is a local diffeomorphism.

## Design decisions
TODO: flesh this out!

## Tags
local diffeomorphism, manifold

-/

open Function Manifold Set SmoothManifoldWithCorners TopologicalSpace Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G]
  (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F G)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  (N : Type*) [TopologicalSpace N] [ChartedSpace G N] (n : ℕ∞)

section LocalDiffeomorphAux
/-- A "diffeomorphism on" `s` is a function `f : M → N` such that `f` restricts to a diffeomorphism
`s → t` between open subsets of `M` and `N`, respectively.
This is an auxiliary definition and should not be used outside of this file. -/
structure LocalDiffeomorphAux extends LocalHomeomorph M N where
  contMDiffOn_toFun : ContMDiffOn I J n toFun source
  contMDiffOn_invFun : ContMDiffOn J I n invFun target

/-- Coercion of a `LocalDiffeomorphAux` to function.
Note that a `LocalDiffeomorphAux` is not `FunLike` (like `LocalHomeomorph`),
as `toFun` doesn't determine `invFun` outside of `target`. -/
instance : CoeFun (LocalDiffeomorphAux I J M N n) fun _ => M → N :=
  ⟨fun Φ => Φ.toFun'⟩

/-- A diffeomorphism is a local diffeomorphism. -/
def Diffeomorph.toLocalDiffeomorphAux (h : Diffeomorph I J M N n) : LocalDiffeomorphAux I J M N n :=
  {
    toLocalHomeomorph := h.toHomeomorph.toLocalHomeomorph
    contMDiffOn_toFun := fun x _ ↦ h.contMDiff_toFun x
    contMDiffOn_invFun := fun _ _ ↦ h.symm.contMDiffWithinAt
  }

-- Add the very basic API we need.
namespace LocalDiffeomorphAux
variable (Φ : LocalDiffeomorphAux I J M N n) (hn : 1 ≤ n)
protected theorem contMDiffOn : ContMDiffOn I J n Φ Φ.source :=
  Φ.contMDiffOn_toFun

protected theorem contMDiffOn_symm : ContMDiffOn J I n Φ.invFun Φ.target :=
  Φ.contMDiffOn_invFun

protected theorem mdifferentiableOn : MDifferentiableOn I J Φ Φ.source :=
  (Φ.contMDiffOn).mdifferentiableOn hn

protected theorem mdifferentiableOn_symm : MDifferentiableOn J I Φ.invFun Φ.target :=
  (Φ.contMDiffOn_symm).mdifferentiableOn hn

protected theorem mdifferentiableAt {x : M} (hx : x ∈ Φ.source) : MDifferentiableAt I J Φ x :=
  (Φ.mdifferentiableOn hn x hx).mdifferentiableAt (Φ.open_source.mem_nhds hx)

-- define symm just to make this easier to write?
protected theorem mdifferentiableAt_symm {x : M} (hx : x ∈ Φ.source) :
    MDifferentiableAt J I Φ.invFun (Φ x) :=
  (Φ.mdifferentiableOn_symm hn (Φ x) (Φ.map_source hx)).mdifferentiableAt
  (Φ.open_target.mem_nhds (Φ.map_source hx))

/- We could add lots of additional API (following `Diffeomorph` and `LocalHomeomorph*), such as
* further continuity and differentiability lemmas
* refl, symm and trans instances; lemmas between them.
As this declaration is meant for internal use only, we keep it simple. -/
end LocalDiffeomorphAux
end LocalDiffeomorphAux

variable {M N}

/-- `f : M → N` is called a **`C^n` local diffeomorphism at *x*** iff there exist
  open sets `U ∋ x` and `V ∋ f x` and a diffeomorphism `Φ : U → V` such that `f = Φ` on `U`. -/
def IsLocalDiffeomorphAt (f : M → N) (x : M) : Prop :=
  ∃ Φ : LocalDiffeomorphAux I J M N n, x ∈ Φ.source ∧ EqOn f Φ Φ.source

/-- `f : M → N` is a **`C^n` local diffeomorphism** iff it is a local diffeomorphism
at each `x ∈ M`. -/
def IsLocalDiffeomorph (f : M → N) : Prop := ∀ x : M, IsLocalDiffeomorphAt I J n f x

lemma isLocalDiffeomorph_iff {f : M → N} :
    IsLocalDiffeomorph I J n f ↔ ∀ x : M, IsLocalDiffeomorphAt I J n f x := by rfl

/-- A `C^n` diffeomorphism is a local diffeomorphism. -/
lemma Diffeomorph.isLocalDiffeomorph (Φ : M ≃ₘ^n⟮I, J⟯ N) : IsLocalDiffeomorph I J n Φ :=
  fun _ ↦ ⟨Φ.toLocalDiffeomorphAux, by trivial, eqOn_refl Φ _⟩

/-- The image of a local diffeomorphism is open. -/
def LocalDiffeomorph.image {f : M → N} (hf : IsLocalDiffeomorph I J n f) : Opens N := by
  refine ⟨range f, ?_⟩
  apply isOpen_iff_forall_mem_open.mpr
  intro y hy

  -- Given `y = f x ∈ range f`, we need to find `V ⊆ N` open containing `y`.
  rw [mem_range] at hy
  rcases hy with ⟨x, hxy⟩

  -- As f is a local diffeo at x, on some open set `U' ∋ x` it agrees with a diffeo `Φ : U' → V'`.
  choose Φ hyp using hf x
  rcases hyp with ⟨hxU, heq⟩
  -- Then `V:=Φ.target` has the desired properties.
  refine ⟨Φ.target, ?_, Φ.open_target, ?_⟩
  · rw [← LocalHomeomorph.image_source_eq_target, ← heq.image_eq]
    exact image_subset_range f Φ.source
  · rw [← hxy, heq hxU]
    exact Φ.toLocalHomeomorph.map_source hxU

lemma LocalDiffeomorph.image_coe {f : M → N} (hf : IsLocalDiffeomorph I J n f) :
    (LocalDiffeomorph.image I J n hf).1 = range f := rfl

section helper -- FIXME: move to Algebra.Module.Basic
variable {R : Type*} [Ring R]
variable {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module R E]
variable {F : Type*} [TopologicalSpace F] [AddCommMonoid F] [Module R F]

/-- `g ∘ f = id` as `ContinuousLinearMap`s implies `g ∘ f = id` as functions. -/
lemma LeftInverse.of_composition {f : E →L[R] F} {g : F →L[R] E}
    (hinv : g.comp f = ContinuousLinearMap.id R E) : LeftInverse g f := by
  have : g ∘ f = id := calc g ∘ f
      _ = ↑(g.comp f) := by rw [ContinuousLinearMap.coe_comp']
      _ = ↑( ContinuousLinearMap.id R E) := by rw [hinv]
      _ = id := by rw [ContinuousLinearMap.coe_id']
  exact congrFun this

/-- `f ∘ g = id` as `ContinuousLinearMap`s implies `f ∘ g = id` as functions. -/
lemma RightInverse.of_composition {f : E →L[R] F} {g : F →L[R] E}
    (hinv : f.comp g = ContinuousLinearMap.id R F) : RightInverse g f :=
  LeftInverse.of_composition hinv
end helper

section Differential
variable {I J n}
variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners J N]
  {f : M → N} {x : M} (hn : 1 ≤ n)

/-- If `f` is a `C^n` local diffeomorphism at `x`, for `n ≥ 1`,
  the differential `df_x` is a linear equivalence. -/
lemma LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv (hf : IsLocalDiffeomorphAt I J n f x)
    (hn : 1 ≤ n) : ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (f x)) :=
  by
  choose Φ hyp using hf
  rcases hyp with ⟨hxU, heq⟩
  let A := mfderiv I J f x
  have hA : A = mfderiv I J Φ x := calc A
    _ = mfderivWithin I J f Φ.source x := (mfderivWithin_of_isOpen Φ.open_source hxU).symm
    _ = mfderivWithin I J Φ Φ.source x :=
      mfderivWithin_congr (Φ.open_source.uniqueMDiffWithinAt hxU) heq (heq hxU)
    _ = mfderiv I J Φ x := mfderivWithin_of_isOpen Φ.open_source hxU
  let B := mfderiv J I Φ.invFun (Φ x)
  have inv1 : B.comp A = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := calc B.comp A
    _ = B.comp (mfderiv I J Φ x) := by rw [hA]
    _ = mfderiv I I (Φ.invFun ∘ Φ) x :=
      (mfderiv_comp x (Φ.mdifferentiableAt_symm hn hxU) (Φ.mdifferentiableAt hn hxU)).symm
    _ = mfderivWithin I I (Φ.invFun ∘ Φ) Φ.source x :=
      (mfderivWithin_of_isOpen Φ.open_source hxU).symm
    _ = mfderivWithin I I id Φ.source x := by
      have : EqOn (Φ.invFun ∘ Φ) id Φ.source := fun _ hx ↦ Φ.left_inv' hx
      apply mfderivWithin_congr (Φ.open_source.uniqueMDiffWithinAt hxU) this (this hxU)
    _ = mfderiv I I id x := mfderivWithin_of_isOpen Φ.open_source hxU
    _ = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := mfderiv_id I
  have inv2 : A.comp B = ContinuousLinearMap.id 𝕜 (TangentSpace J (Φ x)) := calc A.comp B
    _ = (mfderiv I J Φ x).comp B := by rw [hA]
    _ = mfderiv J J (Φ ∘ Φ.invFun) (Φ x) := by
        -- Use the chain rule: need to rewrite both the base point Φ (Φ.invFun x)
        -- and the map Φ.invFun ∘ Φ.
        have hΦ : MDifferentiableAt I J Φ x := Φ.mdifferentiableAt hn hxU
        rw [← (Φ.left_inv hxU)] at hΦ
        let r := mfderiv_comp (Φ x) hΦ (Φ.mdifferentiableAt_symm hn hxU)
        rw [(Φ.left_inv hxU)] at r
        exact r.symm
    _ = mfderivWithin J J (Φ ∘ Φ.invFun) Φ.target (Φ x) :=
      (mfderivWithin_of_isOpen Φ.open_target (Φ.map_source hxU)).symm
    _ = mfderivWithin J J id Φ.target (Φ x) := by
      have : EqOn (Φ ∘ Φ.invFun) id Φ.target := fun _ hx ↦ Φ.right_inv' hx
      apply mfderivWithin_congr ?_ this (this (Φ.map_source hxU))
      exact (Φ.open_target.uniqueMDiffWithinAt (Φ.map_source hxU))
    _ = mfderiv J J id (Φ x) := mfderivWithin_of_isOpen Φ.open_target (Φ.map_source hxU)
    _ = ContinuousLinearMap.id 𝕜 (TangentSpace J (Φ x)) := mfderiv_id J
  exact {
    toFun := A
    invFun := B
    left_inv := LeftInverse.of_composition inv1
    right_inv := RightInverse.of_composition inv2
    continuous_toFun := A.cont
    continuous_invFun := B.cont
    map_add' := fun x_1 y ↦ ContinuousLinearMap.map_add A x_1 y
    map_smul' := by intros; simp
  }

-- FIXME: for some reason, "rfl" fails.
lemma LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv_coe
    (hf : IsLocalDiffeomorphAt I J n f x) :
    LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv hf hn = mfderiv I J f x := by
  sorry

/-- Each differential of a `C^n` diffeomorphism (`n ≥ 1`) is a linear equivalence. -/
noncomputable def Diffeomorph.mfderiv_toContinuousLinearEquiv (hn : 1 ≤ n) (Φ : M ≃ₘ^n⟮I, J⟯ N)
    (x : M) : ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (Φ x)) :=
  LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv (Φ.isLocalDiffeomorph x) hn

-- TODO: make `by rfl` work
lemma Diffeomorph.mfderiv_toContinuousLinearEquiv_coe (Φ : M ≃ₘ^n⟮I, J⟯ N) {x : M} (hn : 1 ≤ n) :
    (Φ.mfderiv_toContinuousLinearEquiv hn x).toFun = mfderiv I J Φ x := sorry

variable (x) in
/-- If `f` is a `C^n` local diffeomorphism (`n ≥ 1`), each differential is a linear equivalence. -/
lemma LocalDiffeomorph.mfderiv_toContinuousLinearEquiv (hf : IsLocalDiffeomorph I J n f)
    (hn : 1 ≤ n) : ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (f x)) :=
  LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv (hf x) hn

variable (x) in
lemma LocalDiffeomorph.mfderiv_toContinuousLinearEquiv_coe (hf : IsLocalDiffeomorph I J n f):
    LocalDiffeomorph.mfderiv_toContinuousLinearEquiv x hf hn = mfderiv I J f x := by
  let r := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv_coe hn (hf x)
  have : (LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv (hf x) hn) =
    (LocalDiffeomorph.mfderiv_toContinuousLinearEquiv x hf hn) :=
    sorry -- TODO: why doesn't `rfl` work?
  exact this ▸ r

/-! # Differential under composition with a local diffeomorphism -/
variable
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  (M' : Type*) [TopologicalSpace M'] [ChartedSpace H' M']
  (I' : ModelWithCorners 𝕜 E' H') [SmoothManifoldWithCorners I' M'] [SmoothManifoldWithCorners I M]
  [SmoothManifoldWithCorners J N]

variable {f : M → M'} {g : M' → N} (hf : IsLocalDiffeomorphAt I I' n f x)
  (hg : ContMDiffAt I' J 1 g (f x))

/-- If `f` is a local diffeomorphism at `x` and `g` is differentiable at `f x`,
  d(g∘f)_x is surjective iff dg_(f x) is. -/
lemma sdfsdf : Surjective (mfderiv I' J g (f x)) ↔ Surjective (mfderiv I J (g ∘ f) x) := by
  set dg := mfderiv I' J g (f x)
  set df := mfderiv I I' f x
  let dfiso := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv hf hn
  have aux : dfiso.toFun = df := sorry
  --LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv_coe hf hn; except for a universe error...

  have hf' : HasMFDerivAt I I' f x df := sorry -- standard
  have hg' : HasMFDerivAt I' J g (f x) dg := sorry -- standard
  have : HasMFDerivAt I J (g ∘ f) x (dg.comp df) := hg'.comp hf' (M := M) (I := I) (x := x)
  -- simp_rw [← this] at r -- doesn't match... ?!
  -- try again: typeclass inference is stuck now...
  --have : HasMFDerivAt I J (g ∘ f) x (dg.comp dfiso) := sorry -- rw [aux] at this, or so
  have : mfderiv I J (g ∘ f) x = dg.comp df := sorry -- standard, from `this`
  rw [this]

  let r := Surjective.of_comp_iff dg dfiso.bijective.surjective
  rw [← r]
  -- remains to rewrite by aux
  sorry


/-- If `f` is a local diffeomorphism at `x` and `g` is differentiable at `f x`,
  d(g∘f)_x is injective iff dg_(f x) is. -/
lemma sdfsdf2 : Injective (mfderiv I' J g (f x)) ↔ Injective (mfderiv I J (g ∘ f) x) := by
  -- xxx: how to reduce repetition here?
  set dg := mfderiv I' J g (f x)
  set df := mfderiv I I' f x
  let dfiso := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv hf hn
  -- coe result, see above
  have hf' : HasMFDerivAt I I' f x df := sorry -- standard
  have hg' : HasMFDerivAt I' J g (f x) dg := sorry -- standard
  have : HasMFDerivAt I J (g ∘ f) x (dg.comp df) := hg'.comp hf' (M := M) (I := I) (x := x)
  have : mfderiv I J (g ∘ f) x = dg.comp df := sorry -- standard, from `this`
  rw [this]

  rw [← Injective.of_comp_iff' dg dfiso.bijective]
  -- remains to argue (using coe result) this is true
  sorry

/-- If `M` is finite-dimensional, then rk (dg\cdot f)_x = rk (dg_f(x)). -/
lemma todostate3 [FiniteDimensional 𝕜 E] : 0 = 1 := sorry

-- will need a similar lemma about rank of linear isos... surely exists

-- similar results for composition in the other direction

end Differential
