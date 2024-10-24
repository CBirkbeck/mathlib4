/-
Copyright (c) 2022 Sebastian Monnet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Monnet
-/
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.Bases
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Tactic.ByContra

/-!
# Krull topology

We define the Krull topology on `L ≃ₐ[K] L` for an arbitrary field extension `L/K`. In order to do
this, we first define a `GroupFilterBasis` on `L ≃ₐ[K] L`, whose sets are `E.fixingSubgroup` for
all intermediate fields `E` with `E/K` finite dimensional.

## Main Definitions

- `finiteExts K L`. Given a field extension `L/K`, this is the set of intermediate fields that are
  finite-dimensional over `K`.

- `fixedByFinite K L`. Given a field extension `L/K`, `fixedByFinite K L` is the set of
  subsets `Gal(L/E)` of `Gal(L/K)`, where `E/K` is finite

- `galBasis K L`. Given a field extension `L/K`, this is the filter basis on `L ≃ₐ[K] L` whose
  sets are `Gal(L/E)` for intermediate fields `E` with `E/K` finite.

- `galGroupBasis K L`. This is the same as `galBasis K L`, but with the added structure
  that it is a group filter basis on `L ≃ₐ[K] L`, rather than just a filter basis.

- `krullTopology K L`. Given a field extension `L/K`, this is the topology on `L ≃ₐ[K] L`, induced
  by the group filter basis `galGroupBasis K L`.

## Main Results

- `krullTopology_t2 K L`. For an integral field extension `L/K`, the topology `krullTopology K L`
  is Hausdorff.

- `krullTopology_totallyDisconnected K L`. For an integral field extension `L/K`, the topology
  `krullTopology K L` is totally disconnected.

## Notations

- In docstrings, we will write `Gal(L/E)` to denote the fixing subgroup of an intermediate field
  `E`. That is, `Gal(L/E)` is the subgroup of `L ≃ₐ[K] L` consisting of automorphisms that fix
  every element of `E`. In particular, we distinguish between `L ≃ₐ[E] L` and `Gal(L/E)`, since the
  former is defined to be a subgroup of `L ≃ₐ[K] L`, while the latter is a group in its own right.

## Implementation Notes

- `krullTopology K L` is defined as an instance for type class inference.
-/

open scoped Pointwise

/-- Mapping intermediate fields along the identity does not change them -/
theorem IntermediateField.map_id {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) : E.map (AlgHom.id K L) = E :=
  SetLike.coe_injective <| Set.image_id _

/-- Mapping a finite dimensional intermediate field along an algebra equivalence gives
a finite-dimensional intermediate field. -/
instance im_finiteDimensional {K L : Type*} [Field K] [Field L] [Algebra K L]
    {E : IntermediateField K L} (σ : L ≃ₐ[K] L) [FiniteDimensional K E] :
    FiniteDimensional K (E.map σ.toAlgHom) :=
  LinearEquiv.finiteDimensional (IntermediateField.intermediateFieldMap σ E).toLinearEquiv

/-- For a field extension `L/K`, the intermediate field `K` is finite-dimensional over `K` -/
theorem IntermediateField.finiteDimensional_bot (K L : Type*) [Field K] [Field L] [Algebra K L] :
    FiniteDimensional K (⊥ : IntermediateField K L) :=
  .of_rank_eq_one IntermediateField.rank_bot

/-- This lemma says that `Gal(L/K) = L ≃ₐ[K] L` -/
theorem IntermediateField.fixingSubgroup.bot {K L : Type*} [Field K] [Field L] [Algebra K L] :
    IntermediateField.fixingSubgroup (⊥ : IntermediateField K L) = ⊤ := by
  ext f
  refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
  rintro ⟨x, hx : x ∈ (⊥ : IntermediateField K L)⟩
  rw [IntermediateField.mem_bot] at hx
  rcases hx with ⟨y, rfl⟩
  exact f.commutes y

/-- If `E1` and `E2` are finite-dimensional intermediate fields, then so is their compositum.
This rephrases a result already in mathlib so that it is compatible with our type classes -/
theorem finiteDimensional_sup {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E1 E2 : IntermediateField K L) (_ : FiniteDimensional K E1) (_ : FiniteDimensional K E2) :
    FiniteDimensional K (↥(E1 ⊔ E2)) :=
  IntermediateField.finiteDimensional_sup E1 E2

/-- An element of `L ≃ₐ[K] L` is in `Gal(L/E)` if and only if it fixes every element of `E`-/
theorem IntermediateField.mem_fixingSubgroup_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (σ : L ≃ₐ[K] L) : σ ∈ E.fixingSubgroup ↔ ∀ x : L, x ∈ E → σ x = x :=
  ⟨fun hσ x hx => hσ ⟨x, hx⟩, fun h ⟨x, hx⟩ => h x hx⟩

/-- The map `E ↦ Gal(L/E)` is inclusion-reversing -/
theorem IntermediateField.fixingSubgroup.antimono {K L : Type*} [Field K] [Field L] [Algebra K L]
    {E1 E2 : IntermediateField K L} (h12 : E1 ≤ E2) : E2.fixingSubgroup ≤ E1.fixingSubgroup := by
  rintro σ hσ ⟨x, hx⟩
  exact hσ ⟨x, h12 hx⟩

@[simp] lemma IntermediateField.fixingSubgroup_top (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IntermediateField.fixingSubgroup (⊤ : IntermediateField K L) = ⊥ := by
  ext
  simp [mem_fixingSubgroup_iff, DFunLike.ext_iff]

@[simp] lemma IntermediateField.fixingSubgroup_bot (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IntermediateField.fixingSubgroup (⊥ : IntermediateField K L) = ⊤ := by
  ext
  simp [mem_fixingSubgroup_iff, mem_bot]

def galBasis (K L : Type*) [Field K] [Field L] [Algebra K L] (E : IntermediateField K L) :
    Set (L ≃ₐ[K] L) :=
  IntermediateField.fixingSubgroup E

theorem galBasis_isBasis (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Filter.IsBasis (fun E : IntermediateField K L ↦ FiniteDimensional K E) (galBasis K L) where
  nonempty := ⟨⊥, IntermediateField.finiteDimensional_bot K L⟩
  inter {E F} hE hF := ⟨E ⊔ F, finiteDimensional_sup E F hE hF, Set.subset_inter_iff.mpr
    ⟨IntermediateField.fixingSubgroup.antimono le_sup_left,
      IntermediateField.fixingSubgroup.antimono le_sup_right⟩⟩

theorem galBasis_isGroupBasis (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Filter.IsGroupBasis (fun E : IntermediateField K L ↦ FiniteDimensional K E) (galBasis K L) :=
  .mk_of_subgroups (galBasis_isBasis K L) fun σ {E} hE ↦ by
    let F := E.map σ.symm.toAlgHom
    refine ⟨F, im_finiteDimensional σ.symm, fun g hg ↦ ?_⟩
    simp_rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change σ (g (σ⁻¹ x)) = x
    have h_in_F : σ⁻¹ x ∈ F := ⟨x, hx, by dsimp; rw [← AlgEquiv.invFun_eq_symm]; rfl⟩
    have h_g_fix : g (σ⁻¹ x) = σ⁻¹ x := by
      rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff F g] at hg
      exact hg (σ⁻¹ x) h_in_F
    rw [h_g_fix]
    exact AlgEquiv.apply_symm_apply σ x

/-- For a field extension `L/K`, `krullTopology K L` is the topological space structure on
`L ≃ₐ[K] L` induced by the group filter basis `galGroupBasis K L` -/
instance krullTopology (K L : Type*) [Field K] [Field L] [Algebra K L] :
    TopologicalSpace (L ≃ₐ[K] L) :=
  galBasis_isGroupBasis K L |>.topology

/-- For a field extension `L/K`, the Krull topology on `L ≃ₐ[K] L` makes it a topological group. -/
instance (K L : Type*) [Field K] [Field L] [Algebra K L] : TopologicalGroup (L ≃ₐ[K] L) :=
  galBasis_isGroupBasis K L |>.instTopologicalGroup

open scoped Topology in
lemma krullTopology_basis_nhds_one (K L : Type*) [Field K] [Field L] [Algebra K L] :
    (𝓝 1 : Filter (L ≃ₐ[K] L)).HasBasis (fun E : IntermediateField K L ↦ FiniteDimensional K E)
    (galBasis K L) :=
  galBasis_isGroupBasis K L |>.nhds_one_hasBasis

open scoped Topology in
lemma krullTopology_mem_nhds_one (K L : Type*) [Field K] [Field L] [Algebra K L]
    (s : Set (L ≃ₐ[K] L)) : s ∈ 𝓝 1 ↔ ∃ E : IntermediateField K L,
    FiniteDimensional K E ∧ (E.fixingSubgroup : Set (L ≃ₐ[K] L)) ⊆ s :=
  krullTopology_basis_nhds_one K L |>.mem_iff

/-- Let `L/E/K` be a tower of fields with `E/K` finite. Then `Gal(L/E)` is an open subgroup of
  `L ≃ₐ[K] L`. -/
theorem IntermediateField.fixingSubgroup_isOpen {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional K E] :
    IsOpen (E.fixingSubgroup : Set (L ≃ₐ[K] L)) :=
  Subgroup.isOpen_of_mem_nhds _ (krullTopology_basis_nhds_one K L |>.mem_of_mem inferInstance)

/-- Given a tower of fields `L/E/K`, with `E/K` finite, the subgroup `Gal(L/E) ≤ L ≃ₐ[K] L` is
  closed. -/
theorem IntermediateField.fixingSubgroup_isClosed {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional K E] :
    IsClosed (E.fixingSubgroup : Set (L ≃ₐ[K] L)) :=
  OpenSubgroup.isClosed ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen⟩

/-- For a field extension `L/K`, the Krull topology on `L ≃ₐ[K] L` makes it a topological group. -/
instance (K L : Type*) [Field K] [Field L] [Algebra K L] : NonarchimedeanGroup (L ≃ₐ[K] L) :=
  (galBasis_isGroupBasis K L).nonarchimedean_of_subgroups

-- TODO : remove the three following declarations ? They don't seem to be used anywhere else.
/-- Given a field extension `L/K`, `finiteExts K L` is the set of
intermediate field extensions `L/E/K` such that `E/K` is finite -/
def finiteExts (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L] :
    Set (IntermediateField K L) :=
  {E | FiniteDimensional K E}

/-- Given a field extension `L/K`, `fixedByFinite K L` is the set of
subsets `Gal(L/E)` of `L ≃ₐ[K] L`, where `E/K` is finite -/
def fixedByFinite (K L : Type*) [Field K] [Field L] [Algebra K L] : Set (Subgroup (L ≃ₐ[K] L)) :=
  IntermediateField.fixingSubgroup '' finiteExts K L

/-- If `L/K` is a field extension, then we have `Gal(L/K) ∈ fixedByFinite K L` -/
theorem top_fixedByFinite {K L : Type*} [Field K] [Field L] [Algebra K L] :
    ⊤ ∈ fixedByFinite K L :=
  ⟨⊥, IntermediateField.finiteDimensional_bot K L, IntermediateField.fixingSubgroup.bot⟩

section KrullT2

open scoped Topology Filter

/-- If `L/K` is an algebraic extension, then the Krull topology on `L ≃ₐ[K] L` is Hausdorff. -/
instance krullTopology_t2 {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsIntegral K L] : T2Space (L ≃ₐ[K] L) := by
  refine TopologicalGroup.t2Space_of_one_sep fun φ φ_ne ↦ ?_
  rcases DFunLike.exists_ne φ_ne with ⟨x, hx⟩
  let E : IntermediateField K L := IntermediateField.adjoin K {x}
  let h_findim : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral x)
  have hxE : x ∈ E := IntermediateField.subset_adjoin _ _ <| Set.mem_singleton _
  exact ⟨galBasis K L E, krullTopology_basis_nhds_one K L |>.mem_of_mem h_findim,
    fun H ↦ hx (H ⟨x, hxE⟩)⟩

end KrullT2

section TotallyDisconnected

/-- If `L/K` is an algebraic field extension, then the Krull topology on `L ≃ₐ[K] L` is
  totally disconnected. -/
instance krullTopology_totallySeparated {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsIntegral K L] : TotallySeparatedSpace (L ≃ₐ[K] L) :=
  inferInstance

/-- If `L/K` is an algebraic field extension, then the Krull topology on `L ≃ₐ[K] L` is
  totally disconnected. -/
instance krullTopology_totallyDisconnected {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsIntegral K L] : TotallyDisconnectedSpace (L ≃ₐ[K] L) :=
  inferInstance

end TotallyDisconnected

instance krullTopology_discreteTopology_of_finiteDimensional (K L : Type) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] : DiscreteTopology (L ≃ₐ[K] L) := by
  -- TODO: criterion `DiscreteTopology` in terms of `𝓝 1` ?
  rw [discreteTopology_iff_isOpen_singleton_one]
  change IsOpen (⊥ : Subgroup (L ≃ₐ[K] L))
  rw [← IntermediateField.fixingSubgroup_top]
  exact IntermediateField.fixingSubgroup_isOpen ⊤
