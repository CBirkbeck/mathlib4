/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury, Scott Carnahan
-/
import Mathlib.LinearAlgebra.PerfectPairing
import Mathlib.LinearAlgebra.Reflection

/-!
# Root data and root systems

This file contains basic definitions for root systems and root data.  We introduce a generalization
of both concepts, called a root pairing.  A typical example of a root pairing is given by choosing a
quadratic form and taking a union of spheres of various radii.  When integrality conditions are
imposed, the property that the set of roots is closed under reflection forces the radii to be small.

## Main definitions:

 * `RootPairing`: Given two perfectly-paired `R`-modules `M` and `N` (over some commutative ring
   `R`) a root pairing with indexing set `ι` is the data of an `ι`-indexed subset of `M`
   ("the roots") an `ι`-indexed subset of `N` ("the coroots"), and an `ι`-indexed set of
   permutations of `ι` such that each root-coroot pair
   evaluates to `2`, and the permutation attached to each element of `ι` is compatible with the
   reflections on the corresponding roots and coroots.
 * `RootDatum`: A root datum is a root pairing for which the roots and coroots take values in
   finitely-generated free Abelian groups.
 * `RootSystem`: A root system is a root pairing for which the roots span their ambient module.
 * `RootPairing.IsCrystallographic`: A root pairing is said to be crystallographic if the pairing
   between a root and coroot is always an integer.
 * `RootPairing.IsReduced`: A root pairing is said to be reduced if it never contains the double of
   a root.

## Todo

* Put more API theorems in the Defs file.
* Introduce the Weyl Group, and its action on the indexing set.
* Base change of root pairings (may need flatness).
* Isomorphism of root pairings.
* Crystallographic root systems are isomorphic to base changes of root systems over `ℤ`: Take
  `M₀` and `N₀` to be the `ℤ`-span of roots and coroots.

## Implementation details

A root datum is sometimes defined as two subsets: roots and coroots, together with a bijection
between them, subject to hypotheses. However the hypotheses ensure that the bijection is unique and
so the question arises of whether this bijection should be part of the data of a root datum or
whether one should merely assert its existence. For finite root systems, things are even more
extreme: the coroots are uniquely determined by the roots, and furthermore, there is a canonical
non-degenerate bilinear form on the ambient space.  Many informal accounts even include this form
as part of the data.

We have opted for a design in which the uniquely-determined data is included: the bijection
between roots and coroots is (implicitly) included and the coroots are included for root systems.
Empirically this seems to be by far the most convenient design and by providing extensionality
lemmas expressing the uniqueness we expect to get the best of both worlds.

Furthermore, we require roots and coroots to be injections from a base indexing type `ι` rather than
subsets of their codomains. This design was chosen to avoid the bijection between roots and coroots
being a dependently-typed object. A third option would be to have the roots and coroots be subsets
but to avoid having a dependently-typed bijection by defining it globally with junk value `0`
outside of the roots and coroots. This would work but lacks the convenient symmetry that the chosen
design enjoys: by introducing the indexing type `ι`, one does not have to pick a direction
(`roots → coroots` or `coroots → roots`) for the forward direction of the bijection. Besides,
providing the user with the additional definitional power to specify an indexing type `ι` is a
benefit and the junk-value pattern is a cost.

As a final point of divergence from the classical literature, we make the reflection permutation on
roots and coroots explicit, rather than specifying only that reflection preserves the sets of roots
and coroots. This is necessary when working with infinite root systems, where the coroots are not
uniquely determined by the roots, because without it, the reflection permutations on roots and
coroots may not correspond. For this purpose, we define a map from `ι` to permutations on `ι`, and
require that it is compatible with reflections and coreflections.

-/

open Set Function
open Module hiding reflection
open Submodule (span)
open AddSubgroup (zmultiples)

noncomputable section

variable (ι R M N : Type*)
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Given two perfectly-paired `R`-modules `M` and `N`, a root pairing with indexing set `ι`
is the data of an `ι`-indexed subset of `M` ("the roots"), an `ι`-indexed subset of `N`
("the coroots"), and an `ι`-indexed set of permutations of `ι`, such that each root-coroot pair
evaluates to `2`, and the permutation attached to each element of `ι` is compatible with the
reflections on the corresponding roots and coroots.

It exists to allow for a convenient unification of the theories of root systems and root data. -/
structure RootPairing extends PerfectPairing R M N :=
  /-- A parametrized family of vectors, called roots. -/
  root : ι ↪ M
  /-- A parametrized family of dual vectors, called coroots. -/
  coroot : ι ↪ N
  root_coroot_two : ∀ i, toLin (root i) (coroot i) = 2
  /-- A parametrized family of permutations, induced by reflection. -/
  reflection_perm : ι → (ι ≃ ι)
  reflection_perm_root : ∀ i j,
    root j - toLin (root j) (coroot i) • root i = root (reflection_perm i j)
  reflection_perm_coroot : ∀ i j,
    coroot j - toLin (root i) (coroot j) • coroot i = coroot (reflection_perm i j)

/-- A root datum is a root pairing with coefficients in the integers and for which the root and
coroot spaces are finitely-generated free Abelian groups.

Note that the latter assumptions `[Free ℤ X₁] [Finite ℤ X₁] [Free ℤ X₂] [Finite ℤ X₂]` should be
supplied as mixins. -/
abbrev RootDatum (X₁ X₂ : Type*) [AddCommGroup X₁] [AddCommGroup X₂] := RootPairing ι ℤ X₁ X₂

/-- A root system is a root pairing for which the roots span their ambient module.

Note that this is slightly more general than the usual definition in the sense that `N` is not
required to be spanned by coroots`. -/
structure RootSystem extends RootPairing ι R M N :=
  span_eq_top : span R (range root) = ⊤

namespace RootPairing

variable {ι R M N} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
(P : RootPairing ι R M N) (i j : ι)

lemma ne_zero [CharZero R] : (P.root i : M) ≠ 0 :=
  fun h ↦ by simpa [h] using P.root_coroot_two i

lemma ne_zero' [CharZero R] : (P.coroot i : N) ≠ 0 :=
  fun h ↦ by simpa [h] using P.root_coroot_two i

/-- If we interchange the roles of `M` and `N`, we still have a root pairing. -/
protected def flip : RootPairing ι R N M :=
  { P.toPerfectPairing.flip with
    root := P.coroot
    coroot := P.root
    root_coroot_two := P.root_coroot_two
    reflection_perm := P.reflection_perm
    reflection_perm_root := P.reflection_perm_coroot
    reflection_perm_coroot := P.reflection_perm_root }

@[simp]
lemma flip_flip : P.flip.flip = P :=
  rfl

/-- This is the pairing between roots and coroots. -/
def pairing : R :=
    P.toLin (P.root i) (P.coroot j)

@[simp]
lemma root_coroot_eq_pairing : P.toLin (P.root i) (P.coroot j) = P.pairing i j :=
  rfl

lemma coroot_root_eq_pairing : P.toLin.flip (P.coroot i) (P.root j) = P.pairing j i := by
  simp

@[simp]
lemma pairing_same : P.pairing i i = 2 := P.root_coroot_two i

lemma coroot_root_two :
    P.toLin.flip (P.coroot i) (P.root i) = 2 := by
  simp

/-- The reflection associated to a root. -/
def reflection : M ≃ₗ[R] M :=
  Module.reflection (P.flip.root_coroot_two i)

@[simp]
lemma root_reflection_perm (j : ι) :
    P.root ((P.reflection_perm i) j) = (P.reflection i) (P.root j) :=
  (P.reflection_perm_root i j).symm

theorem mapsTo_reflection_root : MapsTo (P.reflection i) (range P.root) (range P.root) := by
  rintro - ⟨j, rfl⟩
  exact P.root_reflection_perm i j ▸ mem_range_self (P.reflection_perm i j)


lemma reflection_apply (x : M) :
    P.reflection i x = x - (P.toLin x (P.coroot i)) • P.root i :=
  rfl

lemma reflection_apply_root :
    P.reflection i (P.root j) = P.root j - (P.pairing j i) • P.root i :=
  rfl

@[simp]
lemma reflection_apply_self :
    P.reflection i (P.root i) = - P.root i :=
  Module.reflection_apply_self (P.coroot_root_two i)

@[simp]
lemma reflection_same (x : M) :
    P.reflection i (P.reflection i x) = x :=
  Module.involutive_reflection (P.coroot_root_two i) x

lemma bijOn_reflection_root :
    BijOn (P.reflection i) (range P.root) (range P.root) :=
  Module.bijOn_reflection_of_mapsTo _ <| P.mapsTo_reflection_root i

@[simp]
lemma reflection_image_eq :
    P.reflection i '' (range P.root) = range P.root :=
  (P.bijOn_reflection_root i).image_eq

/-!
theorem involutive_reflection : Involutive (P.reflection i) :=
  Module.involutive_reflection (P.flip.root_coroot_two i)
-/

/-- The reflection associated to a coroot. -/
def coreflection : N ≃ₗ[R] N :=
  Module.reflection (P.root_coroot_two i)

@[simp]
lemma coroot_reflection_perm (j : ι) :
    P.coroot (P.reflection_perm i j) = (P.coreflection i) (P.coroot j) :=
  (P.reflection_perm_coroot i j).symm

theorem mapsTo_coreflection_coroot :
    MapsTo (P.coreflection i) (range P.coroot) (range P.coroot) := by
  rintro - ⟨j, rfl⟩
  exact P.coroot_reflection_perm i j ▸ mem_range_self (P.reflection_perm i j)

lemma coreflection_apply (f : N) :
    P.coreflection i f = f - (P.toLin (P.root i) f) • P.coroot i :=
  rfl

lemma coreflection_apply_coroot :
    P.coreflection i (P.coroot j) = P.coroot j - (P.pairing i j) • P.coroot i :=
  rfl

@[simp]
lemma coreflection_apply_self :
    P.coreflection i (P.coroot i) = - P.coroot i :=
  Module.reflection_apply_self (P.flip.coroot_root_two i)

@[simp]
lemma coreflection_same (x : N) :
    P.coreflection i (P.coreflection i x) = x :=
  Module.involutive_reflection (P.flip.coroot_root_two i) x

lemma bijOn_coreflection_coroot : BijOn (P.coreflection i) (range P.coroot) (range P.coroot) :=
  bijOn_reflection_root P.flip i

@[simp]
lemma coreflection_image_eq :
    P.coreflection i '' (range P.coroot) = range P.coroot :=
  (P.bijOn_coreflection_coroot i).image_eq

lemma coreflection_eq_flip_reflection :
    P.coreflection i = P.flip.reflection i :=
  rfl

lemma reflection_dualMap_eq_coreflection :
    (P.reflection i).dualMap ∘ₗ P.toLin.flip = P.toLin.flip ∘ₗ P.coreflection i := by
  ext n m
  simp [coreflection_apply, reflection_apply, mul_comm (P.toLin m (P.coroot i))]

lemma coroot_eq_coreflection_of_root_eq
    {i j k : ι} (hk : P.root k = P.reflection i (P.root j)) :
    P.coroot k = P.coreflection i (P.coroot j) := by
  rw [← P.root_reflection_perm, EmbeddingLike.apply_eq_iff_eq] at hk
  rw [← P.coroot_reflection_perm, hk]

@[simp]
lemma reflection_perm_self : P.reflection_perm i (P.reflection_perm i j) = j := by
  refine (Embedding.injective P.root) ?_
  simp only [root_reflection_perm, reflection_same]

lemma reflection_perm_square : (P.reflection_perm i) ^[2] = id := by
  ext j
  simp only [iterate_succ, iterate_zero, CompTriple.comp_eq, comp_apply, reflection_perm_self,
    id_eq]

lemma reflection_eq (x y : M) (h : P.reflection i x = P.reflection i y) : x = y := by
  simp only [reflection, Module.reflection, Equiv.invFun_as_coe, Involutive.toPerm_symm,
    Involutive.coe_toPerm, EmbeddingLike.apply_eq_iff_eq] at h
  exact h

lemma scalar_mul_eq_two (x : M) (c : R) (i : ι) (h : P.root i = c • x) :
    c * P.toLin x (P.coroot i) = 2 := by
  rw [← smul_eq_mul, (LinearMap.map_smul₂ P.toLin c x (P.coroot i)).symm, ← h, P.root_coroot_two i]

lemma reflection_eq_imp_scalar (j : ι) (h: P.reflection i = P.reflection j) :
    2 • P.root i = (P.toLin (P.root i) (P.coroot j)) • P.root j := by
  have hij: P.root i = -P.root i + P.toLin (P.root i) (P.coroot j) • P.root j := by
    nth_rw 1 [← reflection_same P i (P.root i), reflection_apply_self, h, reflection_apply]
    rw [LinearMap.map_neg₂, neg_smul, sub_neg_eq_add]
  rw [two_nsmul, eq_neg_add_iff_add_eq.mp hij]

lemma coreflection_eq_imp_scalar (j : ι) (h: P.coreflection i = P.coreflection j) :
    2 • P.coroot i = (P.toLin (P.root j) (P.coroot i)) • P.coroot j := by
  have hij: P.coroot i = -P.coroot i + P.toLin (P.root j) (P.coroot i) • P.coroot j := by
    nth_rw 1 [← coreflection_same P i (P.coroot i), coreflection_apply_self, h, coreflection_apply]
    rw [LinearMap.map_neg, neg_smul, sub_neg_eq_add]
  rw [two_nsmul, eq_neg_add_iff_add_eq.mp hij]

lemma reflection_mul (x : M) :
    (P.reflection i * P.reflection j) x = P.reflection i (P.reflection j x) := rfl

/-- A root pairing is said to be crystallographic if the pairing between a root and coroot is
always an integer. -/
def IsCrystallographic : Prop :=
  ∀ i, MapsTo (P.toLin (P.root i)) (range P.coroot) (zmultiples (1 : R))

lemma isCrystallographic_iff :
    P.IsCrystallographic ↔ ∀ i j, ∃ z : ℤ, z = P.pairing i j := by
  rw [IsCrystallographic]
  refine ⟨fun h i j ↦ ?_, fun h i _ ⟨j, hj⟩ ↦ ?_⟩
  · simpa [AddSubgroup.mem_zmultiples_iff] using h i (mem_range_self j)
  · simpa [← hj, AddSubgroup.mem_zmultiples_iff] using h i j

/-- A root pairing is said to be reduced if any linearly dependent pair of roots is related by a
sign. -/
def IsReduced : Prop :=
  ∀ i j, ¬ LinearIndependent R ![P.root i, P.root j] → (P.root i = P.root j ∨ P.root i = - P.root j)

lemma isReduced_iff : P.IsReduced ↔ ∀ i j : ι, i ≠ j →
    ¬ LinearIndependent R ![P.root i, P.root j] → P.root i = - P.root j := by
  rw [IsReduced]
  refine ⟨fun h i j hij hLin ↦ ?_, fun h i j hLin  ↦ ?_⟩
  · specialize h i j hLin
    simp_all only [ne_eq, EmbeddingLike.apply_eq_iff_eq, false_or]
  · by_cases h' : i = j
    · exact Or.inl (congrArg P.root h')
    · exact Or.inr (h i j h' hLin)

/-- The Weyl group of a root pairing is the group of automorphisms generated by
the fundamental reflections.-/
def WeylGroup : Subgroup (M ≃ₗ[R] M) :=
  Subgroup.closure ({reflection P i | i : ι })

section pairs

variable (j : ι)

/-- The Coxeter Weight of a pair gives the weight of an edge in a Coxeter diagram, when it is
finite.  It is `4 cos² θ`, where `θ` describes the dihedral angle between hyperplanes. -/
def coxeterWeight : R := pairing P i j * pairing P j i

lemma coxeterWeight_swap : coxeterWeight P i j = coxeterWeight P j i := by
  simp only [coxeterWeight, mul_comm]

/-- Two roots are orthogonal when they are fixed by each others' reflections. -/
def IsOrthogonal : Prop := pairing P i j = 0 ∧ pairing P j i = 0

lemma isOrthogonal.symm : IsOrthogonal P i j ↔ IsOrthogonal P j i := by
  simp only [IsOrthogonal, and_comm]

lemma isOrthogonal_comm (h : IsOrthogonal P i j) : Commute (P.reflection i) (P.reflection j) := by
  rw [Commute, SemiconjBy]
  ext v
  replace h : P.pairing i j = 0 ∧ P.pairing j i = 0 := by simpa [IsOrthogonal] using h
  erw [LinearMap.mul_apply, LinearMap.mul_apply]
  simp only [LinearEquiv.coe_coe, reflection_apply, map_sub, map_smul, root_coroot_eq_pairing,
    zero_smul, sub_zero, h]
  abel

/-- A pair of roots is nonsymmetrizable if the existence of a Weyl-invariant form on their span is
obstructed.  When `R` has no zero divisors, this happens when exactly one root is fixed by the
other's reflection. -/
def IsNonSymmetrizable : Prop := coxeterWeight P i j = 0 ∧ ¬ IsOrthogonal P i j

/-- Two roots are parallel if their Coxeter weight is exactly 4.  A linearly independent pair of
parallel roots generates an infinite dihedral group of reflections on their span, and their span
has an invariant singular line. -/
def IsParallel : Prop := coxeterWeight P i j = 4

variable [LT R]

/-- An imaginary pair is one whose Coxeter weight is negative.  Any symmetrization yields an
invariant form where one of the roots has negative norm and the other has positive norm. Root
systems with imaginary pairs are not often considered, since the geometry of reflection is
cumbersome. -/
def IsImaginary : Prop := coxeterWeight P i j < 0

/-- A pair of roots is definite if there is a unique (up to scalars) definite reflection-invariant
form on their span. This happens precisely when the Coxeter weight is strictly between `0` and `4`.
-/
def IsDefinite : Prop := 0 < coxeterWeight P i j ∧ coxeterWeight P i j < 4

/-- A pair of roots is ultraparallel if its Coxeter weight is strictly greater than 4.
Symmetrization induces a nondegenerate indefinite form on the span, and reflections generate an
infinite dihedral group. -/
def IsUltraParallel : Prop := 4 < coxeterWeight P i j

end pairs

section BaseChange

variable {S : Type*} [CommRing S] [Algebra R S] (P : RootPairing ι R M N)
/-!
/-- The base change of a root pairing. -/
def baseChange : RootPairing ι S (S ⊗[R] M) (S ⊗[R] N) :=
  { P.toPerfectPairing.baseChange with
    root := P.root
    coroot := P.coroot
    root_coroot_two := P.root_coroot_two
    mapsTo_preReflection_root := P.mapsTo_preReflection_root
    mapsTo_preReflection_coroot := P.mapsTo_preReflection_coroot }
-/

end BaseChange
