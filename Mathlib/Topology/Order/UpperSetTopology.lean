/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Order.Lattice
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Tactic.TFAE

/-!
# UpperSet topology

This file introduces the upper set topology on a preorder as the topology where the open sets are
the upper sets.

## Main statements

## Implementation notes

A type synonym `WithUpperSetTopology` is introduced and for a preorder `α`, `WithUpperSetTopology α`
is made an instance of `TopologicalSpace` by the topology where the upper sets are the open sets.

We define a mixin class `UpperSetTopology` for the class of types which are both a preorder and a
topology and where the open sets are the upper sets. It is shown that `WithUpperSetTopology α` is an
instance of `UpperSetTopology`.

## Motivation

I need to take a run at this.

## Tags

upper set topology, preorder, Alexandrov
-/


variable (α β : Type _)

section preorder

variable [Preorder α]

/--
The set of upper sets forms a topology
-/
def upperSetTopology' : TopologicalSpace α :=
{ IsOpen := IsUpperSet,
  isOpen_univ := isUpperSet_univ,
  isOpen_inter := fun _ _ => IsUpperSet.inter,
  isOpen_sUnion := fun _ h => isUpperSet_sUnion h, }

end preorder

open Set TopologicalSpace

/-- Type synonym for a preorder equipped with the upper set topology. -/
def WithUpperSetTopology := α

variable {α β}

namespace WithUpperSetTopology

/-- `toUpperSet` is the identity function to the `WithUpperSetTopology` of a type.  -/
@[match_pattern]
def toUpperSet : α ≃ WithUpperSetTopology α := Equiv.refl _

/-- `ofUpperSet` is the identity function from the `WithUpperSetTopology` of a type.  -/
@[match_pattern]
def ofUpperSet : WithUpperSetTopology α ≃ α := Equiv.refl _

@[simp]
theorem to_withUpperSetTopology_symm_eq : (@toUpperSet α).symm = ofUpperSet :=
  rfl

@[simp]
theorem of_withUpperSetTopology_symm_eq : (@ofUpperSet α).symm = toUpperSet :=
  rfl

@[simp]
theorem toUpperSet_ofUpperSet (a : WithUpperSetTopology α) : toUpperSet (ofUpperSet a) = a :=
  rfl

@[simp]
theorem ofUpperSet_toUpperSet (a : α) : ofUpperSet (toUpperSet a) = a :=
  rfl

theorem toUpperSet_inj {a b : α} : toUpperSet a = toUpperSet b ↔ a = b :=
  Iff.rfl

theorem ofUpperSet_inj {a b : WithUpperSetTopology α} : ofUpperSet a = ofUpperSet b ↔ a = b :=
  Iff.rfl

/-- A recursor for `WithUpperSetTopology`. Use as `induction x using WithUpperSetTopology.rec`. -/
protected def rec {β : WithUpperSetTopology α → Sort _} (h : ∀ a, β (toUpperSet a)) : ∀ a, β a :=
fun a => h (ofUpperSet a)

instance [Nonempty α] : Nonempty (WithUpperSetTopology α) :=
  ‹Nonempty α›

instance [Inhabited α] : Inhabited (WithUpperSetTopology α) :=
  ‹Inhabited α›

variable [Preorder α]

instance : Preorder (WithUpperSetTopology α) :=
  ‹Preorder α›

instance : TopologicalSpace (WithUpperSetTopology α) := upperSetTopology' α

end WithUpperSetTopology

/--
The upper set topology is the topology where the open sets are the upper sets.
-/
class UpperSetTopology (α : Type _) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_upperSetTopology : t = upperSetTopology' α

instance [Preorder α] : UpperSetTopology (WithUpperSetTopology α) :=
  ⟨rfl⟩

namespace UpperSetTopology

section Preorder

variable (α)
variable [Preorder α] [TopologicalSpace α] [UpperSetTopology α] {s : Set α}

lemma topology_eq : ‹_› = upperSetTopology' α := topology_eq_upperSetTopology

variable {α}

/-- If `α` is equipped with the upper set topology, then it is homeomorphic to
`WithUpperSetTopology α`.
-/
def withUpperSetTopologyHomeomorph : WithUpperSetTopology α ≃ₜ α :=
  WithUpperSetTopology.ofUpperSet.toHomeomorphOfInducing ⟨by erw [topology_eq α, induced_id]; rfl⟩

lemma IsOpen_iff_IsUpperSet : IsOpen s ↔ IsUpperSet s := by
  rw [topology_eq α]
  rfl

-- c.f. isClosed_iff_lower_and_subset_implies_LUB_mem
lemma isClosed_iff_isLower {s : Set α} : IsClosed s
  ↔ (IsLowerSet s) := by
  rw [← isOpen_compl_iff, IsOpen_iff_IsUpperSet,
    isLowerSet_compl.symm, compl_compl]

lemma isClosed_isLower {s : Set α} : IsClosed s → IsLowerSet s := fun h =>
  (isClosed_iff_isLower.mp h)

/--
The closure of a singleton `{a}` in the upper set topology is the right-closed left-infinite
interval (-∞,a].
-/
@[simp] lemma closure_singleton {a : α} : closure {a} = Iic a := by
  rw [← LowerSet.coe_Iic, ← lowerClosure_singleton]
  refine' subset_antisymm _ _
  . apply closure_minimal subset_lowerClosure
    rw [isClosed_iff_isLower]
    apply (lowerClosure {a}).lower
  . exact lowerClosure_min subset_closure (isClosed_isLower isClosed_closure)

end Preorder

section maps

variable [Preorder α] [Preorder β]

lemma upperSetTopology_coinduced {t₁ : TopologicalSpace α} [UpperSetTopology α]
  (hf : Monotone f) : coinduced f t₁ ≤ upperSetTopology' β := by
  intro s hs
  rw [isOpen_coinduced, IsOpen_iff_IsUpperSet]
  exact (IsUpperSet.preimage hs hf)

open Topology

lemma Monotone_tfae {t₁ : TopologicalSpace α} [UpperSetTopology α]
  {t₂ : TopologicalSpace β} [UpperSetTopology β] {f : α → β} :
    List.TFAE [ Monotone f,
           Continuous f,
           coinduced f t₁ ≤ t₂,
           t₁ ≤ induced f t₂ ] := by
  tfae_have 1 → 3
  . intro hf s hs
    rw [IsOpen_iff_IsUpperSet] at hs
    exact upperSetTopology_coinduced hf _ hs
  tfae_have 2 → 1
  . intros hf a b hab
    rw [← mem_Iic, ← closure_singleton, ← mem_preimage]
    apply (Continuous.closure_preimage_subset hf {f b})
    rw [← mem_Iic, ← closure_singleton] at hab
    apply mem_of_mem_of_subset hab
    apply closure_mono
    rw [singleton_subset_iff, mem_preimage, mem_singleton_iff]
  tfae_have 2 ↔ 4
  . exact continuous_iff_le_induced
  tfae_have 2 ↔ 3
  . exact continuous_iff_coinduced_le
  tfae_finish

end maps

end UpperSetTopology
