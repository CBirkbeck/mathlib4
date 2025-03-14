/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Topology.ContinuousOn

/-!
# Partial homeomorphisms

This file defines homeomorphisms between open subsets of topological spaces. An element `e` of
`PartialHomeomorph X Y` is an extension of `PartialEquiv X Y`, i.e., it is a pair of functions
`e.toFun` and `e.invFun`, inverse of each other on the sets `e.source` and `e.target`.
Additionally, we require that these sets are open, and that the functions are continuous on them.
Equivalently, they are homeomorphisms there.

As in equivs, we register a coercion to functions, and we use `e x` and `e.symm x` throughout
instead of `e.toFun x` and `e.invFun x`.

## Main definitions

* `Homeomorph.toPartialHomeomorph`: associating a partial homeomorphism to a homeomorphism, with
  `source = target = Set.univ`;
* `PartialHomeomorph.symm`: the inverse of a partial homeomorphism
* `PartialHomeomorph.trans`: the composition of two partial homeomorphisms
* `PartialHomeomorph.refl`: the identity partial homeomorphism
* `PartialHomeomorph.const`: a partial homeomorphism which is a constant map,
whose source and target are necessarily singleton sets
* `PartialHomeomorph.ofSet`: the identity on a set `s`
* `PartialHomeomorph.restr s`: restrict a partial homeomorphism `e` to `e.source ∩ interior s`
* `PartialHomeomorph.EqOnSource`: equivalence relation describing the "right" notion of equality
  for partial homeomorphisms
* `PartialHomeomorph.prod`: the product of two partial homeomorphisms,
  as a partial homeomorphism on the product space
* `PartialHomeomorph.pi`: the product of a finite family of partial homeomorphisms
* `PartialHomeomorph.disjointUnion`: combine two partial homeomorphisms with disjoint sources
  and disjoint targets
* `PartialHomeomorph.lift_openEmbedding`: extend a partial homeomorphism `X → Y`
  under an open embedding `X → X'`, to a partial homeomorphism `X' → Z`.
  (This is used to define the disjoint union of charted spaces.)

## Implementation notes

Most statements are copied from their `PartialEquiv` versions, although some care is required
especially when restricting to subsets, as these should be open subsets.

For design notes, see `PartialEquiv.lean`.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `PartialEquiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.
-/

open Function Set Filter Topology

namespace PartialHomeomorph

variable {X Y : Type*} [TopologicalSpaceWithoutAtlas X] [TopologicalSpaceWithoutAtlas Y]
(e : PartialHomeomorph X Y)

/-! Basic properties; inverse (symm instance) -/

/-- Coercion of a partial homeomorphisms to a function. We don't use `e.toFun` because it is
actually `e.toPartialEquiv.toFun`, so `simp` will apply lemmas about `toPartialEquiv`.
While we may want to switch to this behavior later, doing it mid-port will break a lot of proofs. -/
@[coe] def toFun' : X → Y := e.toFun

/-- Coercion of a `PartialHomeomorph` to function.
Note that a `PartialHomeomorph` is not `DFunLike`. -/
instance : CoeFun (PartialHomeomorph X Y) fun _ => X → Y :=
  ⟨fun e => e.toFun'⟩

/-- The inverse of a partial homeomorphism -/
@[symm]
protected def symm : PartialHomeomorph Y X where
  toPartialEquiv := e.toPartialEquiv.symm
  open_source' := e.open_target'
  open_target' := e.open_source'
  continuousOn_toFun := e.continuousOn_invFun
  continuousOn_invFun := e.continuousOn_toFun

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (e : PartialHomeomorph X Y) : X → Y := e

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : PartialHomeomorph X Y) : Y → X := e.symm

initialize_simps_projections PartialHomeomorph (toFun → apply, invFun → symm_apply)

end PartialHomeomorph

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

/-- This lemma can be used to simplify the phrasing of the continuity assumption in the definition
of partial homeomorphisms, which is phrased in terms of `nhdsWithoutAtlas` (to be avoided)
as it is set up before the definition of topological spaces. -/
@[simp] lemma tendsto_nhdsWithoutAtlas_inf_principal (s : Set X) (f : X → Y) :
    (∀ x ∈ s, Tendsto f (nhdsWithoutAtlas x ⊓ 𝓟 s)
      (nhdsWithoutAtlas (f x))) ↔ ContinuousOn f s := Iff.rfl

namespace PartialHomeomorph

variable (e : PartialHomeomorph X Y)

protected theorem open_source : IsOpen e.source := e.open_source'

protected theorem open_target : IsOpen e.target := e.open_target'

protected theorem continuousOn : ContinuousOn e e.source :=
  e.continuousOn_toFun

theorem continuousOn_symm : ContinuousOn e.symm e.target :=
  e.continuousOn_invFun

@[simp, mfld_simps]
theorem mk_coe (e : PartialEquiv X Y) (a b c d) : (PartialHomeomorph.mk e a b c d : X → Y) = e :=
  rfl

@[simp, mfld_simps]
theorem mk_coe_symm (e : PartialEquiv X Y) (a b c d) :
    ((PartialHomeomorph.mk e a b c d).symm : Y → X) = e.symm :=
  rfl

theorem toPartialEquiv_injective :
    Injective (toPartialEquiv : PartialHomeomorph X Y → PartialEquiv X Y)
  | ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, rfl => rfl

/- Register a few simp lemmas to make sure that `simp` puts the application of a local
homeomorphism in its normal form, i.e., in terms of its coercion to a function. -/
@[simp, mfld_simps]
theorem toFun_eq_coe (e : PartialHomeomorph X Y) : e.toFun = e :=
  rfl

@[simp, mfld_simps]
theorem invFun_eq_coe (e : PartialHomeomorph X Y) : e.invFun = e.symm :=
  rfl

@[simp, mfld_simps]
theorem coe_coe : (e.toPartialEquiv : X → Y) = e :=
  rfl

@[simp, mfld_simps]
theorem coe_coe_symm : (e.toPartialEquiv.symm : Y → X) = e.symm :=
  rfl

@[simp, mfld_simps]
theorem map_source {x : X} (h : x ∈ e.source) : e x ∈ e.target :=
  e.map_source' h

/-- Variant of `map_source`, stated for images of subsets of `source`. -/
lemma map_source'' : e '' e.source ⊆ e.target :=
  fun _ ⟨_, hx, hex⟩ ↦ mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

@[simp, mfld_simps]
theorem map_target {x : Y} (h : x ∈ e.target) : e.symm x ∈ e.source :=
  e.map_target' h

@[simp, mfld_simps]
theorem left_inv {x : X} (h : x ∈ e.source) : e.symm (e x) = x :=
  e.left_inv' h

@[simp, mfld_simps]
theorem right_inv {x : Y} (h : x ∈ e.target) : e (e.symm x) = x :=
  e.right_inv' h

theorem eq_symm_apply {x : X} {y : Y} (hx : x ∈ e.source) (hy : y ∈ e.target) :
    x = e.symm y ↔ e x = y :=
  e.toPartialEquiv.eq_symm_apply hx hy

protected theorem mapsTo : MapsTo e e.source e.target := fun _ => e.map_source

protected theorem symm_mapsTo : MapsTo e.symm e.target e.source :=
  e.symm.mapsTo

protected theorem leftInvOn : LeftInvOn e.symm e e.source := fun _ => e.left_inv

protected theorem rightInvOn : RightInvOn e.symm e e.target := fun _ => e.right_inv

protected theorem invOn : InvOn e.symm e e.source e.target :=
  ⟨e.leftInvOn, e.rightInvOn⟩

protected theorem injOn : InjOn e e.source :=
  e.leftInvOn.injOn

protected theorem bijOn : BijOn e e.source e.target :=
  e.invOn.bijOn e.mapsTo e.symm_mapsTo

protected theorem surjOn : SurjOn e e.source e.target :=
  e.bijOn.surjOn

/-- Replace `toPartialEquiv` field to provide better definitional equalities. -/
def replaceEquiv (e : PartialHomeomorph X Y) (e' : PartialEquiv X Y) (h : e.toPartialEquiv = e') :
    PartialHomeomorph X Y where
  toPartialEquiv := e'
  open_source' := h ▸ e.open_source
  open_target' := h ▸ e.open_target
  continuousOn_toFun := h ▸ e.continuousOn_toFun
  continuousOn_invFun := h ▸ e.continuousOn_invFun

theorem replaceEquiv_eq_self (e' : PartialEquiv X Y)
    (h : e.toPartialEquiv = e') : e.replaceEquiv e' h = e := by
  cases e
  subst e'
  rfl

theorem source_preimage_target : e.source ⊆ e ⁻¹' e.target :=
  e.mapsTo

theorem eventually_left_inverse {x} (hx : x ∈ e.source) :
    ∀ᶠ y in 𝓝 x, e.symm (e y) = y :=
  (e.open_source.eventually_mem hx).mono e.left_inv'

theorem eventually_left_inverse' {x} (hx : x ∈ e.target) :
    ∀ᶠ y in 𝓝 (e.symm x), e.symm (e y) = y :=
  e.eventually_left_inverse (e.map_target hx)

theorem eventually_right_inverse {x} (hx : x ∈ e.target) :
    ∀ᶠ y in 𝓝 x, e (e.symm y) = y :=
  (e.open_target.eventually_mem hx).mono e.right_inv'

theorem eventually_right_inverse' {x} (hx : x ∈ e.source) :
    ∀ᶠ y in 𝓝 (e x), e (e.symm y) = y :=
  e.eventually_right_inverse (e.map_source hx)

theorem eventually_ne_nhdsWithin {x} (hx : x ∈ e.source) :
    ∀ᶠ x' in 𝓝[≠] x, e x' ≠ e x :=
  eventually_nhdsWithin_iff.2 <|
    (e.eventually_left_inverse hx).mono fun x' hx' =>
      mt fun h => by rw [mem_singleton_iff, ← e.left_inv hx, ← h, hx']

theorem nhdsWithin_source_inter {x} (hx : x ∈ e.source) (s : Set X) : 𝓝[e.source ∩ s] x = 𝓝[s] x :=
  nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds e.open_source hx)

theorem nhdsWithin_target_inter {x} (hx : x ∈ e.target) (s : Set Y) : 𝓝[e.target ∩ s] x = 𝓝[s] x :=
  e.symm.nhdsWithin_source_inter hx s

theorem image_eq_target_inter_inv_preimage {s : Set X} (h : s ⊆ e.source) :
    e '' s = e.target ∩ e.symm ⁻¹' s :=
  e.toPartialEquiv.image_eq_target_inter_inv_preimage h

theorem image_source_inter_eq' (s : Set X) : e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' s :=
  e.toPartialEquiv.image_source_inter_eq' s

theorem image_source_inter_eq (s : Set X) :
    e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' (e.source ∩ s) :=
  e.toPartialEquiv.image_source_inter_eq s

theorem symm_image_eq_source_inter_preimage {s : Set Y} (h : s ⊆ e.target) :
    e.symm '' s = e.source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h

theorem symm_image_target_inter_eq (s : Set Y) :
    e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' (e.target ∩ s) :=
  e.symm.image_source_inter_eq _

theorem source_inter_preimage_inv_preimage (s : Set X) :
    e.source ∩ e ⁻¹' (e.symm ⁻¹' s) = e.source ∩ s :=
  e.toPartialEquiv.source_inter_preimage_inv_preimage s

theorem target_inter_inv_preimage_preimage (s : Set Y) :
    e.target ∩ e.symm ⁻¹' (e ⁻¹' s) = e.target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _

theorem source_inter_preimage_target_inter (s : Set Y) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.toPartialEquiv.source_inter_preimage_target_inter s

theorem image_source_eq_target : e '' e.source = e.target :=
  e.toPartialEquiv.image_source_eq_target

theorem symm_image_target_eq_source : e.symm '' e.target = e.source :=
  e.symm.image_source_eq_target

/-- Two partial homeomorphisms are equal when they have equal `toFun`, `invFun` and `source`.
It is not sufficient to have equal `toFun` and `source`, as this only determines `invFun` on
the target. This would only be true for a weaker notion of equality, arguably the right one,
called `EqOnSource`. -/
@[ext]
protected theorem ext (e' : PartialHomeomorph X Y) (h : ∀ x, e x = e' x)
    (hinv : ∀ x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
  toPartialEquiv_injective (PartialEquiv.ext h hinv hs)

@[simp, mfld_simps]
theorem symm_toPartialEquiv : e.symm.toPartialEquiv = e.toPartialEquiv.symm :=
  rfl

-- The following lemmas are already simp via `PartialEquiv`
theorem symm_source : e.symm.source = e.target :=
  rfl

theorem symm_target : e.symm.target = e.source :=
  rfl

@[simp, mfld_simps] theorem symm_symm : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective
    (PartialHomeomorph.symm : PartialHomeomorph X Y → PartialHomeomorph Y X) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/-- A partial homeomorphism is continuous at any point of its source -/
protected theorem continuousAt {x : X} (h : x ∈ e.source) : ContinuousAt e x :=
  (e.continuousOn x h).continuousAt (e.open_source.mem_nhds h)

/-- A partial homeomorphism inverse is continuous at any point of its target -/
theorem continuousAt_symm {x : Y} (h : x ∈ e.target) : ContinuousAt e.symm x :=
  e.symm.continuousAt h

theorem tendsto_symm {x} (hx : x ∈ e.source) : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
  simpa only [ContinuousAt, e.left_inv hx] using e.continuousAt_symm (e.map_source hx)

theorem map_nhds_eq {x} (hx : x ∈ e.source) : map e (𝓝 x) = 𝓝 (e x) :=
  le_antisymm (e.continuousAt hx) <|
    le_map_of_right_inverse (e.eventually_right_inverse' hx) (e.tendsto_symm hx)

theorem symm_map_nhds_eq {x} (hx : x ∈ e.source) : map e.symm (𝓝 (e x)) = 𝓝 x :=
  (e.symm.map_nhds_eq <| e.map_source hx).trans <| by rw [e.left_inv hx]

theorem image_mem_nhds {x} (hx : x ∈ e.source) {s : Set X} (hs : s ∈ 𝓝 x) : e '' s ∈ 𝓝 (e x) :=
  e.map_nhds_eq hx ▸ Filter.image_mem_map hs

theorem map_nhdsWithin_eq {x} (hx : x ∈ e.source) (s : Set X) :
    map e (𝓝[s] x) = 𝓝[e '' (e.source ∩ s)] e x :=
  calc
    map e (𝓝[s] x) = map e (𝓝[e.source ∩ s] x) :=
      congr_arg (map e) (e.nhdsWithin_source_inter hx _).symm
    _ = 𝓝[e '' (e.source ∩ s)] e x :=
      (e.leftInvOn.mono inter_subset_left).map_nhdsWithin_eq (e.left_inv hx)
        (e.continuousAt_symm (e.map_source hx)).continuousWithinAt
        (e.continuousAt hx).continuousWithinAt

theorem map_nhdsWithin_preimage_eq {x} (hx : x ∈ e.source) (s : Set Y) :
    map e (𝓝[e ⁻¹' s] x) = 𝓝[s] e x := by
  rw [e.map_nhdsWithin_eq hx, e.image_source_inter_eq', e.target_inter_inv_preimage_preimage,
    e.nhdsWithin_target_inter (e.map_source hx)]

theorem eventually_nhds {x : X} (p : Y → Prop) (hx : x ∈ e.source) :
    (∀ᶠ y in 𝓝 (e x), p y) ↔ ∀ᶠ x in 𝓝 x, p (e x) :=
  Iff.trans (by rw [e.map_nhds_eq hx]) eventually_map

theorem eventually_nhds' {x : X} (p : X → Prop) (hx : x ∈ e.source) :
    (∀ᶠ y in 𝓝 (e x), p (e.symm y)) ↔ ∀ᶠ x in 𝓝 x, p x := by
  rw [e.eventually_nhds _ hx]
  refine eventually_congr ((e.eventually_left_inverse hx).mono fun y hy => ?_)
  rw [hy]

theorem eventually_nhdsWithin {x : X} (p : Y → Prop) {s : Set X}
    (hx : x ∈ e.source) : (∀ᶠ y in 𝓝[e.symm ⁻¹' s] e x, p y) ↔ ∀ᶠ x in 𝓝[s] x, p (e x) := by
  refine Iff.trans ?_ eventually_map
  rw [e.map_nhdsWithin_eq hx, e.image_source_inter_eq', e.nhdsWithin_target_inter (e.mapsTo hx)]

theorem eventually_nhdsWithin' {x : X} (p : X → Prop) {s : Set X}
    (hx : x ∈ e.source) : (∀ᶠ y in 𝓝[e.symm ⁻¹' s] e x, p (e.symm y)) ↔ ∀ᶠ x in 𝓝[s] x, p x := by
  rw [e.eventually_nhdsWithin _ hx]
  refine eventually_congr <|
    (eventually_nhdsWithin_of_eventually_nhds <| e.eventually_left_inverse hx).mono fun y hy => ?_
  rw [hy]

/-- This lemma is useful in the manifold library in the case that `e` is a chart. It states that
  locally around `e x` the set `e.symm ⁻¹' s` is the same as the set intersected with the target
  of `e` and some other neighborhood of `f x` (which will be the source of a chart on `Z`). -/
theorem preimage_eventuallyEq_target_inter_preimage_inter {e : PartialHomeomorph X Y} {s : Set X}
    {t : Set Z} {x : X} {f : X → Z} (hf : ContinuousWithinAt f s x) (hxe : x ∈ e.source)
    (ht : t ∈ 𝓝 (f x)) :
    e.symm ⁻¹' s =ᶠ[𝓝 (e x)] (e.target ∩ e.symm ⁻¹' (s ∩ f ⁻¹' t) : Set Y) := by
  rw [eventuallyEq_set, e.eventually_nhds _ hxe]
  filter_upwards [e.open_source.mem_nhds hxe,
    mem_nhdsWithin_iff_eventually.mp (hf.preimage_mem_nhdsWithin ht)]
  intro y hy hyu
  simp_rw [mem_inter_iff, mem_preimage, mem_inter_iff, e.mapsTo hy, true_and, iff_self_and,
    e.left_inv hy, iff_true_intro hyu]

theorem isOpen_inter_preimage {s : Set Y} (hs : IsOpen s) : IsOpen (e.source ∩ e ⁻¹' s) :=
  e.continuousOn.isOpen_inter_preimage e.open_source hs

theorem isOpen_inter_preimage_symm {s : Set X} (hs : IsOpen s) : IsOpen (e.target ∩ e.symm ⁻¹' s) :=
  e.symm.continuousOn.isOpen_inter_preimage e.open_target hs

/-- A partial homeomorphism is an open map on its source:
  the image of an open subset of the source is open. -/
lemma isOpen_image_of_subset_source {s : Set X} (hs : IsOpen s) (hse : s ⊆ e.source) :
    IsOpen (e '' s) := by
  rw [(image_eq_target_inter_inv_preimage (e := e) hse)]
  exact ContinuousOn.isOpen_inter_preimage e.continuousOn_invFun e.open_target hs

/-- The image of the restriction of an open set to the source is open. -/
theorem isOpen_image_source_inter {s : Set X} (hs : IsOpen s) :
    IsOpen (e '' (e.source ∩ s)) :=
  e.isOpen_image_of_subset_source (e.open_source.inter hs) inter_subset_left

/-- The inverse of a partial homeomorphism `e` is an open map on `e.target`. -/
lemma isOpen_image_symm_of_subset_target {t : Set Y} (ht : IsOpen t) (hte : t ⊆ e.target) :
    IsOpen (e.symm '' t) :=
  isOpen_image_of_subset_source e.symm ht (e.symm_source ▸ hte)

lemma isOpen_symm_image_iff_of_subset_target {t : Set Y} (hs : t ⊆ e.target) :
    IsOpen (e.symm '' t) ↔ IsOpen t := by
  refine ⟨fun h ↦ ?_, fun h ↦ e.symm.isOpen_image_of_subset_source h hs⟩
  have hs' : e.symm '' t ⊆ e.source := by
    rw [e.symm_image_eq_source_inter_preimage hs]
    apply Set.inter_subset_left
  rw [← e.image_symm_image_of_subset_target hs]
  exact e.isOpen_image_of_subset_source h hs'

theorem isOpen_image_iff_of_subset_source {s : Set X} (hs : s ⊆ e.source) :
    IsOpen (e '' s) ↔ IsOpen s := by
  rw [← e.symm.isOpen_symm_image_iff_of_subset_target hs, e.symm_symm]

section IsImage

/-!
### `PartialHomeomorph.IsImage` relation

We say that `t : Set Y` is an image of `s : Set X` under a partial homeomorphism `e` if any of the
following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).

This definition is a restatement of `PartialEquiv.IsImage` for partial homeomorphisms.
In this section we transfer API about `PartialEquiv.IsImage` to partial homeomorphisms and
add a few `PartialHomeomorph`-specific lemmas like `PartialHomeomorph.IsImage.closure`.
-/

/-- We say that `t : Set Y` is an image of `s : Set X` under a partial homeomorphism `e`
if any of the following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
def IsImage (s : Set X) (t : Set Y) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)

namespace IsImage

variable {e} {s : Set X} {t : Set Y} {x : X} {y : Y}

theorem toPartialEquiv (h : e.IsImage s t) : e.toPartialEquiv.IsImage s t :=
  h

theorem apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s :=
  h hx

protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
  h.toPartialEquiv.symm

theorem symm_apply_mem_iff (h : e.IsImage s t) (hy : y ∈ e.target) : e.symm y ∈ s ↔ y ∈ t :=
  h.symm hy

@[simp]
theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩

protected theorem mapsTo (h : e.IsImage s t) : MapsTo e (e.source ∩ s) (e.target ∩ t) :=
  h.toPartialEquiv.mapsTo

theorem symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target ∩ t) (e.source ∩ s) :=
  h.symm.mapsTo

theorem image_eq (h : e.IsImage s t) : e '' (e.source ∩ s) = e.target ∩ t :=
  h.toPartialEquiv.image_eq

theorem symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target ∩ t) = e.source ∩ s :=
  h.symm.image_eq

theorem iff_preimage_eq : e.IsImage s t ↔ e.source ∩ e ⁻¹' t = e.source ∩ s :=
  PartialEquiv.IsImage.iff_preimage_eq

alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq

theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' s = e.target ∩ t :=
  symm_iff.symm.trans iff_preimage_eq

alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq

theorem iff_symm_preimage_eq' :
    e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' (e.source ∩ s) = e.target ∩ t := by
  rw [iff_symm_preimage_eq, ← image_source_inter_eq, ← image_source_inter_eq']

alias ⟨symm_preimage_eq', of_symm_preimage_eq'⟩ := iff_symm_preimage_eq'

theorem iff_preimage_eq' : e.IsImage s t ↔ e.source ∩ e ⁻¹' (e.target ∩ t) = e.source ∩ s :=
  symm_iff.symm.trans iff_symm_preimage_eq'

alias ⟨preimage_eq', of_preimage_eq'⟩ := iff_preimage_eq'

theorem of_image_eq (h : e '' (e.source ∩ s) = e.target ∩ t) : e.IsImage s t :=
  PartialEquiv.IsImage.of_image_eq h

theorem of_symm_image_eq (h : e.symm '' (e.target ∩ t) = e.source ∩ s) : e.IsImage s t :=
  PartialEquiv.IsImage.of_symm_image_eq h

protected theorem compl (h : e.IsImage s t) : e.IsImage sᶜ tᶜ := fun _ hx => (h hx).not

protected theorem inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∩ s') (t ∩ t') := fun _ hx => (h hx).and (h' hx)

protected theorem union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∪ s') (t ∪ t') := fun _ hx => (h hx).or (h' hx)

protected theorem diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl

theorem leftInvOn_piecewise {e' : PartialHomeomorph X Y} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) :=
  h.toPartialEquiv.leftInvOn_piecewise h'

theorem inter_eq_of_inter_eq_of_eqOn {e' : PartialHomeomorph X Y} (h : e.IsImage s t)
    (h' : e'.IsImage s t) (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    e.target ∩ t = e'.target ∩ t :=
  h.toPartialEquiv.inter_eq_of_inter_eq_of_eqOn h' hs Heq

theorem symm_eqOn_of_inter_eq_of_eqOn {e' : PartialHomeomorph X Y} (h : e.IsImage s t)
    (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    EqOn e.symm e'.symm (e.target ∩ t) :=
  h.toPartialEquiv.symm_eq_on_of_inter_eq_of_eqOn hs Heq

theorem map_nhdsWithin_eq (h : e.IsImage s t) (hx : x ∈ e.source) : map e (𝓝[s] x) = 𝓝[t] e x := by
  rw [e.map_nhdsWithin_eq hx, h.image_eq, e.nhdsWithin_target_inter (e.map_source hx)]

protected theorem closure (h : e.IsImage s t) : e.IsImage (closure s) (closure t) := fun x hx => by
  simp only [mem_closure_iff_nhdsWithin_neBot, ← h.map_nhdsWithin_eq hx, map_neBot_iff]

protected theorem interior (h : e.IsImage s t) : e.IsImage (interior s) (interior t) := by
  simpa only [closure_compl, compl_compl] using h.compl.closure.compl

protected theorem frontier (h : e.IsImage s t) : e.IsImage (frontier s) (frontier t) :=
  h.closure.diff h.interior

theorem isOpen_iff (h : e.IsImage s t) : IsOpen (e.source ∩ s) ↔ IsOpen (e.target ∩ t) :=
  ⟨fun hs => h.symm_preimage_eq' ▸ e.symm.isOpen_inter_preimage hs, fun hs =>
    h.preimage_eq' ▸ e.isOpen_inter_preimage hs⟩

/-- Restrict a `PartialHomeomorph` to a pair of corresponding open sets. -/
@[simps toPartialEquiv]
def restr (h : e.IsImage s t) (hs : IsOpen (e.source ∩ s)) : PartialHomeomorph X Y where
  toPartialEquiv := h.toPartialEquiv.restr
  open_source' := hs
  open_target' := h.isOpen_iff.1 hs
  continuousOn_toFun := e.continuousOn.mono inter_subset_left
  continuousOn_invFun := e.symm.continuousOn.mono inter_subset_left

end IsImage

theorem isImage_source_target : e.IsImage e.source e.target :=
  e.toPartialEquiv.isImage_source_target

theorem isImage_source_target_of_disjoint (e' : PartialHomeomorph X Y)
    (hs : Disjoint e.source e'.source) (ht : Disjoint e.target e'.target) :
    e.IsImage e'.source e'.target :=
  e.toPartialEquiv.isImage_source_target_of_disjoint e'.toPartialEquiv hs ht

/-- Preimage of interior or interior of preimage coincide for partial homeomorphisms,
when restricted to the source. -/
theorem preimage_interior (s : Set Y) :
    e.source ∩ e ⁻¹' interior s = e.source ∩ interior (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).interior.preimage_eq

theorem preimage_closure (s : Set Y) : e.source ∩ e ⁻¹' closure s = e.source ∩ closure (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).closure.preimage_eq

theorem preimage_frontier (s : Set Y) :
    e.source ∩ e ⁻¹' frontier s = e.source ∩ frontier (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).frontier.preimage_eq

end IsImage

/-- Restricting a partial homeomorphism `e` to `e.source ∩ s` when `s` is open.
This is sometimes hard to use because of the openness assumption, but it has the advantage that
when it can be used then its `PartialEquiv` is defeq to `PartialEquiv.restr`. -/
protected def restrOpen (s : Set X) (hs : IsOpen s) : PartialHomeomorph X Y :=
  (@IsImage.of_symm_preimage_eq X Y _ _ e s (e.symm ⁻¹' s) rfl).restr
    (IsOpen.inter e.open_source hs)

@[simp, mfld_simps]
theorem restrOpen_toPartialEquiv (s : Set X) (hs : IsOpen s) :
    (e.restrOpen s hs).toPartialEquiv = e.toPartialEquiv.restr s :=
  rfl

-- Already simp via `PartialEquiv`
theorem restrOpen_source (s : Set X) (hs : IsOpen s) : (e.restrOpen s hs).source = e.source ∩ s :=
  rfl

/-- Restricting a partial homeomorphism `e` to `e.source ∩ interior s`. We use the interior to make
sure that the restriction is well defined whatever the set s, since partial homeomorphisms are by
definition defined on open sets. In applications where `s` is open, this coincides with the
restriction of partial equivalences -/
@[simps! (config := mfld_cfg) apply symm_apply, simps! -isSimp source target]
protected def restr (s : Set X) : PartialHomeomorph X Y :=
  e.restrOpen (interior s) isOpen_interior

@[simp, mfld_simps]
theorem restr_toPartialEquiv (s : Set X) :
    (e.restr s).toPartialEquiv = e.toPartialEquiv.restr (interior s) :=
  rfl

theorem restr_source' (s : Set X) (hs : IsOpen s) : (e.restr s).source = e.source ∩ s := by
  rw [e.restr_source, hs.interior_eq]

theorem restr_toPartialEquiv' (s : Set X) (hs : IsOpen s) :
    (e.restr s).toPartialEquiv = e.toPartialEquiv.restr s := by
  rw [e.restr_toPartialEquiv, hs.interior_eq]

theorem restr_eq_of_source_subset {e : PartialHomeomorph X Y} {s : Set X} (h : e.source ⊆ s) :
    e.restr s = e :=
  toPartialEquiv_injective <| PartialEquiv.restr_eq_of_source_subset <|
    interior_maximal h e.open_source

@[simp, mfld_simps]
theorem restr_univ {e : PartialHomeomorph X Y} : e.restr univ = e :=
  restr_eq_of_source_subset (subset_univ _)

theorem restr_source_inter (s : Set X) : e.restr (e.source ∩ s) = e.restr s := by
  refine PartialHomeomorph.ext _ _ (fun x => rfl) (fun x => rfl) ?_
  simp [e.open_source.interior_eq, ← inter_assoc]

@[simp, mfld_simps]
theorem refl_partialEquiv : (PartialHomeomorph.refl X).toPartialEquiv = PartialEquiv.refl X :=
  rfl

@[simp, mfld_simps]
theorem refl_symm : (PartialHomeomorph.refl X).symm = PartialHomeomorph.refl X :=
  rfl

@[simp, mfld_simps]
theorem coe_refl : (PartialHomeomorph.refl X : X → X) = id := rfl

@[simp, mfld_simps]
theorem refl_apply (x : X) : (PartialHomeomorph.refl X) x = x := rfl

/-! const: `PartialEquiv.const` as a partial homeomorphism -/
section const

variable {a : X} {b : Y}

/--
This is `PartialEquiv.single` as a partial homeomorphism: a constant map,
whose source and target are necessarily singleton sets.
-/
def const (ha : IsOpen {a}) (hb : IsOpen {b}) : PartialHomeomorph X Y where
  toPartialEquiv := PartialEquiv.single a b
  open_source' := ha
  open_target' := hb
  continuousOn_toFun := by rw [tendsto_nhdsWithoutAtlas_inf_principal]; simp
  continuousOn_invFun := by rw [tendsto_nhdsWithoutAtlas_inf_principal]; simp

@[simp, mfld_simps]
lemma const_apply (ha : IsOpen {a}) (hb : IsOpen {b}) (x : X) : (const ha hb) x = b := rfl

@[simp, mfld_simps]
lemma const_source (ha : IsOpen {a}) (hb : IsOpen {b}) : (const ha hb).source = {a} := rfl

@[simp, mfld_simps]
lemma const_target (ha : IsOpen {a}) (hb : IsOpen {b}) : (const ha hb).target = {b} := rfl

end const

/-! ofSet: the identity on a set `s` -/
section ofSet

variable {s : Set X} (hs : IsOpen s)

/-- The identity partial equivalence on a set `s` -/
@[simps! (config := mfld_cfg) apply, simps! -isSimp source target]
def ofSet (s : Set X) (hs : IsOpen s) : PartialHomeomorph X X where
  toPartialEquiv := PartialEquiv.ofSet s
  open_source' := hs
  open_target' := hs
  continuousOn_toFun := continuous_id.continuousOn
  continuousOn_invFun := continuous_id.continuousOn

@[simp, mfld_simps]
theorem ofSet_toPartialEquiv : (ofSet s hs).toPartialEquiv = PartialEquiv.ofSet s :=
  rfl

@[simp, mfld_simps]
theorem ofSet_symm : (ofSet s hs).symm = ofSet s hs :=
  rfl

@[simp, mfld_simps]
theorem ofSet_univ_eq_refl : ofSet univ isOpen_univ = PartialHomeomorph.refl X := by ext <;> simp

end ofSet

/-! `trans`: composition of two partial homeomorphisms -/
section trans

variable (e' : PartialHomeomorph Y Z)

/-- Composition of two partial homeomorphisms when the target of the first and the source of
the second coincide. -/
@[simps! apply symm_apply toPartialEquiv, simps! -isSimp source target]
protected def trans' (h : e.target = e'.source) : PartialHomeomorph X Z where
  toPartialEquiv := PartialEquiv.trans' e.toPartialEquiv e'.toPartialEquiv h
  open_source' := e.open_source
  open_target' := e'.open_target
  continuousOn_toFun := e'.continuousOn.comp e.continuousOn <| h ▸ e.mapsTo
  continuousOn_invFun := e.continuousOn_symm.comp e'.continuousOn_symm <| h.symm ▸ e'.symm_mapsTo

/-- Composing two partial homeomorphisms, by restricting to the maximal domain where their
composition is well defined.
Within the `Manifold` namespace, there is the notation `e ≫ₕ f` for this. -/
@[trans]
protected def trans : PartialHomeomorph X Z :=
  PartialHomeomorph.trans' (e.symm.restrOpen e'.source e'.open_source).symm
    (e'.restrOpen e.target e.open_target) (by simp [inter_comm])

@[simp, mfld_simps]
theorem trans_toPartialEquiv :
    (e.trans e').toPartialEquiv = e.toPartialEquiv.trans e'.toPartialEquiv :=
  rfl

@[simp, mfld_simps]
theorem coe_trans : (e.trans e' : X → Z) = e' ∘ e :=
  rfl

@[simp, mfld_simps]
theorem coe_trans_symm : ((e.trans e').symm : Z → X) = e.symm ∘ e'.symm :=
  rfl

theorem trans_apply {x : X} : (e.trans e') x = e' (e x) :=
  rfl

theorem trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm := rfl

/- This could be considered as a simp lemma, but there are many situations where it makes something
simple into something more complicated. -/
theorem trans_source : (e.trans e').source = e.source ∩ e ⁻¹' e'.source :=
  PartialEquiv.trans_source e.toPartialEquiv e'.toPartialEquiv

theorem trans_source' : (e.trans e').source = e.source ∩ e ⁻¹' (e.target ∩ e'.source) :=
  PartialEquiv.trans_source' e.toPartialEquiv e'.toPartialEquiv

theorem trans_source'' : (e.trans e').source = e.symm '' (e.target ∩ e'.source) :=
  PartialEquiv.trans_source'' e.toPartialEquiv e'.toPartialEquiv

theorem image_trans_source : e '' (e.trans e').source = e.target ∩ e'.source :=
  PartialEquiv.image_trans_source e.toPartialEquiv e'.toPartialEquiv

theorem trans_target : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' e.target :=
  rfl

theorem trans_target' : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' (e'.source ∩ e.target) :=
  trans_source' e'.symm e.symm

theorem trans_target'' : (e.trans e').target = e' '' (e'.source ∩ e.target) :=
  trans_source'' e'.symm e.symm

theorem inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source ∩ e.target :=
  image_trans_source e'.symm e.symm

theorem trans_assoc (e'' : PartialHomeomorph Z Z') :
    (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  toPartialEquiv_injective <| e.1.trans_assoc _ _

@[simp, mfld_simps]
theorem trans_refl : e.trans (PartialHomeomorph.refl Y) = e :=
  toPartialEquiv_injective e.1.trans_refl

@[simp, mfld_simps]
theorem refl_trans : (PartialHomeomorph.refl X).trans e = e :=
  toPartialEquiv_injective e.1.refl_trans

theorem trans_ofSet {s : Set Y} (hs : IsOpen s) : e.trans (ofSet s hs) = e.restr (e ⁻¹' s) :=
  PartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) <| by
    rw [trans_source, restr_source, ofSet_source, ← preimage_interior, hs.interior_eq]

theorem trans_of_set' {s : Set Y} (hs : IsOpen s) :
    e.trans (ofSet s hs) = e.restr (e.source ∩ e ⁻¹' s) := by rw [trans_ofSet, restr_source_inter]

theorem ofSet_trans {s : Set X} (hs : IsOpen s) : (ofSet s hs).trans e = e.restr s :=
  PartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) <| by simp [hs.interior_eq, inter_comm]

theorem ofSet_trans' {s : Set X} (hs : IsOpen s) :
    (ofSet s hs).trans e = e.restr (e.source ∩ s) := by
  rw [ofSet_trans, restr_source_inter]

@[simp, mfld_simps]
theorem ofSet_trans_ofSet {s : Set X} (hs : IsOpen s) {s' : Set X} (hs' : IsOpen s') :
    (ofSet s hs).trans (ofSet s' hs') = ofSet (s ∩ s') (IsOpen.inter hs hs') := by
  rw [(ofSet s hs).trans_ofSet hs']
  ext <;> simp [hs'.interior_eq]

theorem restr_trans (s : Set X) : (e.restr s).trans e' = (e.trans e').restr s :=
  toPartialEquiv_injective <|
    PartialEquiv.restr_trans e.toPartialEquiv e'.toPartialEquiv (interior s)

end trans

/-! `EqOnSource`: equivalence on their source -/
section EqOnSource

/-- `EqOnSource e e'` means that `e` and `e'` have the same source, and coincide there. They
should really be considered the same partial equivalence. -/
def EqOnSource (e e' : PartialHomeomorph X Y) : Prop :=
  e.source = e'.source ∧ EqOn e e' e.source

theorem eqOnSource_iff (e e' : PartialHomeomorph X Y) :
    EqOnSource e e' ↔ PartialEquiv.EqOnSource e.toPartialEquiv e'.toPartialEquiv :=
  Iff.rfl

/-- `EqOnSource` is an equivalence relation. -/
instance eqOnSourceSetoid : Setoid (PartialHomeomorph X Y) :=
  { PartialEquiv.eqOnSourceSetoid.comap toPartialEquiv with r := EqOnSource }

theorem eqOnSource_refl : e ≈ e := Setoid.refl _

/-- If two partial homeomorphisms are equivalent, so are their inverses. -/
theorem EqOnSource.symm' {e e' : PartialHomeomorph X Y} (h : e ≈ e') : e.symm ≈ e'.symm :=
  PartialEquiv.EqOnSource.symm' h

/-- Two equivalent partial homeomorphisms have the same source. -/
theorem EqOnSource.source_eq {e e' : PartialHomeomorph X Y} (h : e ≈ e') : e.source = e'.source :=
  h.1

/-- Two equivalent partial homeomorphisms have the same target. -/
theorem EqOnSource.target_eq {e e' : PartialHomeomorph X Y} (h : e ≈ e') : e.target = e'.target :=
  h.symm'.1

/-- Two equivalent partial homeomorphisms have coinciding `toFun` on the source -/
theorem EqOnSource.eqOn {e e' : PartialHomeomorph X Y} (h : e ≈ e') : EqOn e e' e.source :=
  h.2

/-- Two equivalent partial homeomorphisms have coinciding `invFun` on the target -/
theorem EqOnSource.symm_eqOn_target {e e' : PartialHomeomorph X Y} (h : e ≈ e') :
    EqOn e.symm e'.symm e.target :=
  h.symm'.2

/-- Composition of partial homeomorphisms respects equivalence. -/
theorem EqOnSource.trans' {e e' : PartialHomeomorph X Y} {f f' : PartialHomeomorph Y Z}
    (he : e ≈ e') (hf : f ≈ f') : e.trans f ≈ e'.trans f' :=
  PartialEquiv.EqOnSource.trans' he hf

/-- Restriction of partial homeomorphisms respects equivalence -/
theorem EqOnSource.restr {e e' : PartialHomeomorph X Y} (he : e ≈ e') (s : Set X) :
    e.restr s ≈ e'.restr s :=
  PartialEquiv.EqOnSource.restr he _

/-- Two equivalent partial homeomorphisms are equal when the source and target are `univ`. -/
theorem Set.EqOn.restr_eqOn_source {e e' : PartialHomeomorph X Y}
    (h : EqOn e e' (e.source ∩ e'.source)) : e.restr e'.source ≈ e'.restr e.source := by
  constructor
  · rw [e'.restr_source' _ e.open_source]
    rw [e.restr_source' _ e'.open_source]
    exact Set.inter_comm _ _
  · rw [e.restr_source' _ e'.open_source]
    refine (EqOn.trans ?_ h).trans ?_ <;> simp only [mfld_simps, eqOn_refl]

/-- Composition of a partial homeomorphism and its inverse is equivalent to the restriction of the
identity to the source -/
theorem self_trans_symm : e.trans e.symm ≈ PartialHomeomorph.ofSet e.source e.open_source :=
  PartialEquiv.self_trans_symm _

theorem symm_trans_self : e.symm.trans e ≈ PartialHomeomorph.ofSet e.target e.open_target :=
  e.symm.self_trans_symm

theorem eq_of_eqOnSource_univ {e e' : PartialHomeomorph X Y} (h : e ≈ e') (s : e.source = univ)
    (t : e.target = univ) : e = e' :=
  toPartialEquiv_injective <| PartialEquiv.eq_of_eqOnSource_univ _ _ h s t

end EqOnSource

/-! combining two partial homeomorphisms using `Set.piecewise` -/
section Piecewise

/-- Combine two `PartialHomeomorph`s using `Set.piecewise`. The source of the new
`PartialHomeomorph` is `s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly for
target.  The function sends `e.source ∩ s` to `e.target ∩ t` using `e` and
`e'.source \ s` to `e'.target \ t` using `e'`, and similarly for the inverse function.
To ensure the maps `toFun` and `invFun` are inverse of each other on the new `source` and `target`,
the definition assumes that the sets `s` and `t` are related both by `e.is_image` and `e'.is_image`.
To ensure that the new maps are continuous on `source`/`target`, it also assumes that `e.source` and
`e'.source` meet `frontier s` on the same set and `e x = e' x` on this intersection. -/
@[simps! -fullyApplied toPartialEquiv apply]
def piecewise (e e' : PartialHomeomorph X Y) (s : Set X) (t : Set Y) [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) : PartialHomeomorph X Y where
  toPartialEquiv := e.toPartialEquiv.piecewise e'.toPartialEquiv s t H H'
  open_source' := e.open_source.ite e'.open_source Hs
  open_target' :=
    e.open_target.ite e'.open_target <| H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq
  continuousOn_toFun := continuousOn_piecewise_ite e.continuousOn e'.continuousOn Hs Heq
  continuousOn_invFun :=
    continuousOn_piecewise_ite e.continuousOn_symm e'.continuousOn_symm
      (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
      (H.frontier.symm_eqOn_of_inter_eq_of_eqOn Hs Heq)

@[simp]
theorem symm_piecewise (e e' : PartialHomeomorph X Y) {s : Set X} {t : Set Y}
    [∀ x, Decidable (x ∈ s)] [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) :
    (e.piecewise e' s t H H' Hs Heq).symm =
      e.symm.piecewise e'.symm t s H.symm H'.symm
        (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
        (H.frontier.symm_eqOn_of_inter_eq_of_eqOn Hs Heq) :=
  rfl

/-- Combine two `PartialHomeomorph`s with disjoint sources and disjoint targets. We reuse
`PartialHomeomorph.piecewise` then override `toPartialEquiv` to `PartialEquiv.disjointUnion`.
This way we have better definitional equalities for `source` and `target`. -/
def disjointUnion (e e' : PartialHomeomorph X Y) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] (Hs : Disjoint e.source e'.source)
    (Ht : Disjoint e.target e'.target) : PartialHomeomorph X Y :=
  (e.piecewise e' e.source e.target e.isImage_source_target
        (e'.isImage_source_target_of_disjoint e Hs.symm Ht.symm)
        (by rw [e.open_source.inter_frontier_eq, (Hs.symm.frontier_right e'.open_source).inter_eq])
        (by
          rw [e.open_source.inter_frontier_eq]
          exact eqOn_empty _ _)).replaceEquiv
    (e.toPartialEquiv.disjointUnion e'.toPartialEquiv Hs Ht)
    (PartialEquiv.disjointUnion_eq_piecewise _ _ _ _).symm

end Piecewise

section Continuity

/-- Continuity within a set at a point can be read under right composition with a local
homeomorphism, if the point is in its target -/
theorem continuousWithinAt_iff_continuousWithinAt_comp_right {f : Y → Z} {s : Set Y} {x : Y}
    (h : x ∈ e.target) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ∘ e) (e ⁻¹' s) (e.symm x) := by
  simp_rw [ContinuousWithinAt, ← @tendsto_map'_iff _ _ _ _ e,
    e.map_nhdsWithin_preimage_eq (e.map_target h), (· ∘ ·), e.right_inv h]

/-- Continuity at a point can be read under right composition with a partial homeomorphism, if the
point is in its target -/
theorem continuousAt_iff_continuousAt_comp_right {f : Y → Z} {x : Y} (h : x ∈ e.target) :
    ContinuousAt f x ↔ ContinuousAt (f ∘ e) (e.symm x) := by
  rw [← continuousWithinAt_univ, e.continuousWithinAt_iff_continuousWithinAt_comp_right h,
    preimage_univ, continuousWithinAt_univ]

/-- A function is continuous on a set if and only if its composition with a partial homeomorphism
on the right is continuous on the corresponding set. -/
theorem continuousOn_iff_continuousOn_comp_right {f : Y → Z} {s : Set Y} (h : s ⊆ e.target) :
    ContinuousOn f s ↔ ContinuousOn (f ∘ e) (e.source ∩ e ⁻¹' s) := by
  simp only [← e.symm_image_eq_source_inter_preimage h, ContinuousOn, forall_mem_image]
  refine forall₂_congr fun x hx => ?_
  rw [e.continuousWithinAt_iff_continuousWithinAt_comp_right (h hx),
    e.symm_image_eq_source_inter_preimage h, inter_comm, continuousWithinAt_inter]
  exact IsOpen.mem_nhds e.open_source (e.map_target (h hx))

/-- Continuity within a set at a point can be read under left composition with a local
homeomorphism if a neighborhood of the initial point is sent to the source of the local
homeomorphism -/
theorem continuousWithinAt_iff_continuousWithinAt_comp_left {f : Z → X} {s : Set Z} {x : Z}
    (hx : f x ∈ e.source) (h : f ⁻¹' e.source ∈ 𝓝[s] x) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (e ∘ f) s x := by
  refine ⟨(e.continuousAt hx).comp_continuousWithinAt, fun fe_cont => ?_⟩
  rw [← continuousWithinAt_inter' h] at fe_cont ⊢
  have : ContinuousWithinAt (e.symm ∘ e ∘ f) (s ∩ f ⁻¹' e.source) x :=
    haveI : ContinuousWithinAt e.symm univ (e (f x)) :=
      (e.continuousAt_symm (e.map_source hx)).continuousWithinAt
    ContinuousWithinAt.comp this fe_cont (subset_univ _)
  exact this.congr (fun y hy => by simp [e.left_inv hy.2]) (by simp [e.left_inv hx])

/-- Continuity at a point can be read under left composition with a partial homeomorphism if a
neighborhood of the initial point is sent to the source of the partial homeomorphism -/
theorem continuousAt_iff_continuousAt_comp_left {f : Z → X} {x : Z} (h : f ⁻¹' e.source ∈ 𝓝 x) :
    ContinuousAt f x ↔ ContinuousAt (e ∘ f) x := by
  have hx : f x ∈ e.source := (mem_of_mem_nhds h :)
  have h' : f ⁻¹' e.source ∈ 𝓝[univ] x := by rwa [nhdsWithin_univ]
  rw [← continuousWithinAt_univ, ← continuousWithinAt_univ,
    e.continuousWithinAt_iff_continuousWithinAt_comp_left hx h']

/-- A function is continuous on a set if and only if its composition with a partial homeomorphism
on the left is continuous on the corresponding set. -/
theorem continuousOn_iff_continuousOn_comp_left {f : Z → X} {s : Set Z} (h : s ⊆ f ⁻¹' e.source) :
    ContinuousOn f s ↔ ContinuousOn (e ∘ f) s :=
  forall₂_congr fun _x hx =>
    e.continuousWithinAt_iff_continuousWithinAt_comp_left (h hx)
      (mem_of_superset self_mem_nhdsWithin h)

/-- A function is continuous if and only if its composition with a partial homeomorphism
on the left is continuous and its image is contained in the source. -/
theorem continuous_iff_continuous_comp_left {f : Z → X} (h : f ⁻¹' e.source = univ) :
    Continuous f ↔ Continuous (e ∘ f) := by
  simp only [continuous_iff_continuousOn_univ]
  exact e.continuousOn_iff_continuousOn_comp_left (Eq.symm h).subset

end Continuity

end PartialHomeomorph
