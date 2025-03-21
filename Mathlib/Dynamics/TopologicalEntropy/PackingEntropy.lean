/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy

/-!
# Topological entropy via packings
We implement Bowen-Dinaburg's definitions of the topological entropy, via packings.

The major design decisions are the same as in `Mathlib.Dynamics.TopologicalEntropy.CoverEntropy`,
and are explained in detail there: use of uniform spaces, definition of the topological entropy of
a subset, and values taken in `EReal`.

Given a map `T : X → X` and a subset `F ⊆ X`, the topological entropy is loosely defined using
packings as the exponential growth (in `n`) of the number of distinguishable orbits of length `n`
starting from `F`. More precisely, given an entourage `U`, two orbits of length `n` can be
distinguished if there exists some index `k < n` such that `T^[k] x` and `T^[k] y` are far enough
(i.e. `(T^[k] x, T^[k] y)` is not in `U`). The maximal number of distinguishable orbits of
length `n` is `packingMaxcard T F U n`, and its exponential growth `packingEntropyEntourage T F U`.
This quantity increases when `U` decreases, and a definition of the topological entropy is
`⨆ U ∈ 𝓤 X, packingEntropyInfEntourage T F U`.

The definition of topological entropy using packings coincides with the definition using covers.
Instead of defining a new notion of topological entropy, we prove that
`coverEntropy` coincides with `⨆ U ∈ 𝓤 X, packingEntropyEntourage T F U`.

## Main definitions
- `IsDynNetIn`: property that dynamical balls centered on a subset `s` of `F` are disjoint.
- `packingMaxcard`: maximal cardinality of a dynamical packing. Takes values in `ℕ∞`.
- `packingEntropyInfEntourage`/`packingEntropyEntourage`: exponential growth of `packingMaxcard`.
The former is defined with a `liminf`, the latter with a `limsup`. Take values in `EReal`.

## Implementation notes
As when using covers, there are two competing definitions `packingEntropyInfEntourage` and
`packingEntropyEntourage` in this file: one uses a `liminf`, the other a `limsup`.
When using covers, we chose the `limsup` definition as the default.

## Main results
- `coverEntropy_eq_iSup_packingEntropyEntourage`: equality between the notions of
topological entropy defined with covers and with packings. Has a variant for `coverEntropyInf`.

## Tags
packing, entropy

## TODO
Get versions of the topological entropy on (pseudo-e)metric spaces.
-/

namespace Dynamics

open Set Uniformity UniformSpace

variable {X : Type*}

/-! ### Dynamical packings -/

/-- Given a subset `F`, an entourage `U` and an integer `n`, a subset `s` of `F` is a
  `(U, n)`-dynamical packing of `F` if no two orbits of length `n` of points in `s`
  shadow each other. -/
def IsDynNetIn (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) (s : Set X) : Prop :=
  s ⊆ F ∧ s.PairwiseDisjoint (fun x : X ↦ ball x (dynEntourage T U n))

lemma IsDynNetIn.of_le {T : X → X} {F : Set X} {U : Set (X × X)} {m n : ℕ} (m_n : m ≤ n) {s : Set X}
    (h : IsDynNetIn T F U m s) :
    IsDynNetIn T F U n s :=
  ⟨h.1, PairwiseDisjoint.mono h.2 (fun x ↦ ball_mono (dynEntourage_antitone T U m_n) x)⟩

lemma IsDynNetIn.of_entourage_subset {T : X → X} {F : Set X} {U V : Set (X × X)} (U_V : U ⊆ V)
    {n : ℕ} {s : Set X} (h : IsDynNetIn T F V n s) :
    IsDynNetIn T F U n s :=
  ⟨h.1, PairwiseDisjoint.mono h.2 (fun x ↦ ball_mono (dynEntourage_monotone T n U_V) x)⟩

lemma isDynNetIn_empty {T : X → X} {F : Set X} {U : Set (X × X)} {n : ℕ} :
    IsDynNetIn T F U n ∅ :=
  ⟨empty_subset F, pairwise_empty _⟩

lemma isDynNetIn_singleton (T : X → X) {F : Set X} (U : Set (X × X)) (n : ℕ) {x : X} (h : x ∈ F) :
    IsDynNetIn T F U n {x} :=
  ⟨singleton_subset_iff.2 h, pairwise_singleton x _⟩

/-- Given an entourage `U` and a time `n`, a dynamical packing has a smaller cardinality than
  a dynamical cover. This lemma is the first of two key results to compare two versions of
  topological entropy: with cover and with packings,
  the second being `coverMincard_le_packingMaxcard`. -/
lemma IsDynNetIn.card_le_card_of_isDynCoverOf {T : X → X} {F : Set X} {U : Set (X × X)}
    (U_symm : IsSymmetricRel U) {n : ℕ} {s t : Finset X} (hs : IsDynNetIn T F U n s)
    (ht : IsDynCoverOf T F U n t) :
    s.card ≤ t.card := by
  have (x : X) (x_s : x ∈ s) : ∃ z ∈ t, x ∈ ball z (dynEntourage T U n) := by
    specialize ht (hs.1 x_s)
    simp only [Finset.coe_sort_coe, mem_iUnion, Subtype.exists, exists_prop] at ht
    exact ht
  choose! F s_t using this
  simp only [mem_ball_symmetry (U_symm.dynEntourage T n)] at s_t
  apply Finset.card_le_card_of_injOn F (fun x x_s ↦ (s_t x x_s).1)
  exact fun x x_s y y_s Fx_Fy ↦
    PairwiseDisjoint.elim_set hs.2 x_s y_s (F x) (s_t x x_s).2 (Fx_Fy ▸ (s_t y y_s).2)

/-! ### Maximal cardinality of dynamical packings -/

/-- The largest cardinality of a `(U, n)`-dynamical packing of `F`. Takes values in `ℕ∞`, and is
  infinite if and only if `F` admits packings of arbitrarily large size. -/
noncomputable def packingMaxcard (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) : ℕ∞ :=
  ⨆ (s : Finset X) (_ : IsDynNetIn T F U n s), (s.card : ℕ∞)

lemma IsDynNetIn.card_le_packingMaxcard {T : X → X} {F : Set X} {U : Set (X × X)} {n : ℕ}
    {s : Finset X} (h : IsDynNetIn T F U n s) :
    s.card ≤ packingMaxcard T F U n :=
  le_iSup₂ (α := ℕ∞) s h

lemma packingMaxcard_monotone_time (T : X → X) (F : Set X) (U : Set (X × X)) :
    Monotone (fun n : ℕ ↦ packingMaxcard T F U n) :=
  fun _ _ m_n ↦ biSup_mono (fun _ h ↦ h.of_le m_n)

lemma packingMaxcard_antitone (T : X → X) (F : Set X) (n : ℕ) :
    Antitone (fun U : Set (X × X) ↦ packingMaxcard T F U n) :=
  fun _ _ U_V ↦ biSup_mono (fun _ h ↦ h.of_entourage_subset U_V)

lemma packingMaxcard_finite_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    packingMaxcard T F U n < ⊤ ↔
    ∃ s : Finset X, IsDynNetIn T F U n s ∧ (s.card : ℕ∞) = packingMaxcard T F U n := by
  apply Iff.intro <;> intro h
  · obtain ⟨k, k_max⟩ := WithTop.ne_top_iff_exists.1 h.ne
    rw [← k_max]
    simp only [ENat.some_eq_coe, Nat.cast_inj]
    -- The criterion we want to use is `Nat.sSup_mem`. We rewrite `packingMaxcard` with an `sSup`,
    -- then check its `BddAbove` and `Nonempty` hypotheses.
    have : packingMaxcard T F U n
      = sSup (WithTop.some '' (Finset.card '' {s : Finset X | IsDynNetIn T F U n s})) := by
      rw [packingMaxcard, ← image_comp, sSup_image]
      simp only [mem_setOf_eq, ENat.some_eq_coe, Function.comp_apply]
    rw [this] at k_max
    have h_bdda : BddAbove (Finset.card '' {s : Finset X | IsDynNetIn T F U n s}) := by
      refine ⟨k, mem_upperBounds.2 ?_⟩
      simp only [mem_image, mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro s h
      rw [← WithTop.coe_le_coe, k_max]
      apply le_sSup
      simp only [ENat.some_eq_coe, mem_image, mem_setOf_eq, Nat.cast_inj, exists_eq_right]
      exact Filter.frequently_principal.mp fun a ↦ a h rfl
    have h_nemp : (Finset.card '' {s : Finset X | IsDynNetIn T F U n s}).Nonempty := by
      refine ⟨0, ?_⟩
      simp only [mem_image, mem_setOf_eq, Finset.card_eq_zero, exists_eq_right, Finset.coe_empty]
      exact isDynNetIn_empty
    rw [← WithTop.coe_sSup' h_bdda, ENat.some_eq_coe, Nat.cast_inj] at k_max
    have key := Nat.sSup_mem h_nemp h_bdda
    rw [← k_max, mem_image] at key
    simp only [mem_setOf_eq] at key
    exact key
  · obtain  ⟨s, _, s_card⟩ := h
    rw [← s_card]
    exact WithTop.coe_lt_top s.card

@[simp]
lemma packingMaxcard_empty {T : X → X} {U : Set (X × X)} {n : ℕ} :
    packingMaxcard T ∅ U n = 0 := by
  rw [packingMaxcard, ← bot_eq_zero, iSup₂_eq_bot]
  intro s s_pac
  replace s_pac := subset_empty_iff.1 s_pac.1
  norm_cast at s_pac
  rw [s_pac, Finset.card_empty, CharP.cast_eq_zero, bot_eq_zero']

lemma packingMaxcard_eq_zero_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    packingMaxcard T F U n = 0 ↔ F = ∅ := by
  refine Iff.intro (fun h ↦ ?_) (fun h ↦ by rw [h, packingMaxcard_empty])
  rw [eq_empty_iff_forall_not_mem]
  intro x x_F
  have key := isDynNetIn_singleton T U n x_F
  rw [← Finset.coe_singleton] at key
  replace key := key.card_le_packingMaxcard
  rw [Finset.card_singleton, Nat.cast_one, h] at key
  exact key.not_lt zero_lt_one

lemma one_le_packingMaxcard_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    1 ≤ packingMaxcard T F U n ↔ F.Nonempty := by
  rw [ENat.one_le_iff_ne_zero, nonempty_iff_ne_empty]
  exact not_iff_not.2 (packingMaxcard_eq_zero_iff T F U n)

lemma packingMaxcard_zero (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) :
    packingMaxcard T F U 0 = 1 := by
  apply (iSup₂_le _).antisymm ((one_le_packingMaxcard_iff T F U 0).2 h)
  intro s ⟨_, s_pac⟩
  simp only [ball, dynEntourage_zero, preimage_univ] at s_pac
  norm_cast
  refine Finset.card_le_one.2 (fun x x_s y y_s ↦ ?_)
  exact PairwiseDisjoint.elim_set s_pac x_s y_s x (mem_univ x) (mem_univ x)

lemma packingMaxcard_univ (T : X → X) {F : Set X} (h : F.Nonempty) (n : ℕ) :
    packingMaxcard T F univ n = 1 := by
  apply (iSup₂_le _).antisymm ((one_le_packingMaxcard_iff T F univ n).2 h)
  intro s ⟨_, s_pac⟩
  simp only [ball, dynEntourage_univ, preimage_univ] at s_pac
  norm_cast
  refine Finset.card_le_one.2 (fun x x_s y y_s ↦ ?_)
  exact PairwiseDisjoint.elim_set s_pac x_s y_s x (mem_univ x) (mem_univ x)

lemma packingMaxcard_infinite_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    packingMaxcard T F U n = ⊤ ↔ ∀ k : ℕ, ∃ s : Finset X, IsDynNetIn T F U n s ∧ k ≤ s.card := by
  apply Iff.intro <;> intro h
  · intro k
    rw [packingMaxcard, iSup_subtype', iSup_eq_top] at h
    specialize h k (ENat.coe_lt_top k)
    simp only [Nat.cast_lt, Subtype.exists, exists_prop] at h
    obtain ⟨s, s_pac, s_k⟩ := h
    exact ⟨s, s_pac, s_k.le⟩
  · refine WithTop.eq_top_iff_forall_gt.2 fun k ↦ ?_
    obtain ⟨s, s_pac, s_card⟩ := h (k + 1)
    apply s_pac.card_le_packingMaxcard.trans_lt'
    rw [ENat.some_eq_coe, Nat.cast_lt]
    exact (lt_add_one k).trans_le s_card

lemma packingMaxcard_le_coverMincard (T : X → X) (F : Set X) {U : Set (X × X)}
    (U_symm : IsSymmetricRel U) (n : ℕ) :
    packingMaxcard T F U n ≤ coverMincard T F U n := by
  rcases eq_top_or_lt_top (coverMincard T F U n) with h | h
  · exact h ▸ le_top
  · obtain ⟨t, t_cover, t_card⟩ := (coverMincard_finite_iff T F U n).1 h
    rw [← t_card]
    exact iSup₂_le (fun s s_pac ↦ Nat.cast_le.2 (s_pac.card_le_card_of_isDynCoverOf U_symm t_cover))

/-- Given an entourage `U` and a time `n`, a minimal dynamical cover by `U ○ U` has a smaller
  cardinality than a maximal dynamical packing by `U`. This lemma is the second of two key results
  to compare two versions topological entropy: with cover and with packings. -/
lemma coverMincard_le_packingMaxcard (T : X → X) (F : Set X) {U : Set (X × X)} (U_rfl : idRel ⊆ U)
    (U_symm : IsSymmetricRel U) (n : ℕ) :
    coverMincard T F (U ○ U) n ≤ packingMaxcard T F U n := by
  classical
  -- WLOG, there exists a maximal dynamical packing `s`.
  rcases (eq_top_or_lt_top (packingMaxcard T F U n)) with h | h
  · exact h ▸ le_top
  obtain ⟨s, s_pac, s_card⟩ := (packingMaxcard_finite_iff T F U n).1 h
  rw [← s_card]
  apply IsDynCoverOf.coverMincard_le_card
  --  We have to check that `s` is a cover for `dynEntourage T F (U ○ U) n`.
  -- If `s` is not a cover, then we can add to `s` a point `x` which is not covered
  -- and get a new packing. This contradicts the maximality of `s`.
  by_contra h
  obtain ⟨x, x_F, x_uncov⟩ := not_subset.1 h
  simp only [Finset.mem_coe, mem_iUnion, exists_prop, not_exists, not_and] at x_uncov
  have larger_packing : IsDynNetIn T F U n (insert x s) :=
    And.intro (insert_subset x_F s_pac.1) (pairwiseDisjoint_insert.2 (And.intro s_pac.2
      (fun y y_s _ ↦ (disjoint_left.2 (fun z z_x z_y ↦ x_uncov y y_s
        (mem_ball_dynEntourage_comp T n U_symm x y (nonempty_of_mem ⟨z_x, z_y⟩)))))))
  rw [← Finset.coe_insert x s] at larger_packing
  apply larger_packing.card_le_packingMaxcard.not_lt
  rw [← s_card, Nat.cast_lt]
  refine (lt_add_one s.card).trans_eq (Finset.card_insert_of_not_mem fun x_s ↦ ?_).symm
  apply x_uncov x x_s (ball_mono (dynEntourage_monotone T n (subset_comp_self U_rfl)) x
    (ball_mono (idRel_subset_dynEntourage T U_rfl n) x _))
  simp only [ball, mem_preimage, mem_idRel]

open ENNReal EReal

lemma log_packingMaxcard_nonneg (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) (n : ℕ) :
    0 ≤ log (packingMaxcard T F U n) := by
  apply zero_le_log_iff.2
  rw [← ENat.toENNReal_one, ENat.toENNReal_le]
  exact (one_le_packingMaxcard_iff T F U n).2 h

/-! ### Net entropy of entourages -/

open Filter

/-- The entropy of an entourage `U`, defined as the exponential rate of growth of the size of the
largest `(U, n)`-dynamical packing of `F`. Takes values in the space of extended real numbers
`[-∞,+∞]`. This version uses a `limsup`, and is chosen as the default definition. -/
noncomputable def packingEntropyEntourage (T : X → X) (F : Set X) (U : Set (X × X)) :=
  atTop.limsup fun n : ℕ ↦ log (packingMaxcard T F U n) / n

/-- The entropy of an entourage `U`, defined as the exponential rate of growth of the size of the
largest `(U, n)`-dynamical packing of `F`. Takes values in the space of extended real numbers
`[-∞,+∞]`. This version uses a `liminf`, and is an alternative definition. -/
noncomputable def packingEntropyInfEntourage (T : X → X) (F : Set X) (U : Set (X × X)) :=
  atTop.liminf fun n : ℕ ↦ log (packingMaxcard T F U n) / n

lemma packingEntropyInfEntourage_antitone (T : X → X) (F : Set X) :
    Antitone (fun U : Set (X × X) ↦ packingEntropyInfEntourage T F U) :=
  fun _ _ U_V ↦ (liminf_le_liminf) (Eventually.of_forall
    fun n ↦ monotone_div_right_of_nonneg n.cast_nonneg'
      (log_monotone (ENat.toENNReal_mono (packingMaxcard_antitone T F n U_V))))

lemma packingEntropyEntourage_antitone (T : X → X) (F : Set X) :
    Antitone (fun U : Set (X × X) ↦ packingEntropyEntourage T F U) :=
  fun _ _ U_V ↦ (limsup_le_limsup) (Eventually.of_forall
    fun n ↦ (monotone_div_right_of_nonneg n.cast_nonneg'
      (log_monotone (ENat.toENNReal_mono (packingMaxcard_antitone T F n U_V)))))

lemma packingEntropyInfEntourage_le_packingEntropyEntourage (T : X → X) (F : Set X)
    (U : Set (X × X)) :
    packingEntropyInfEntourage T F U ≤ packingEntropyEntourage T F U := liminf_le_limsup

@[simp]
lemma packingEntropyEntourage_empty {T : X → X} {U : Set (X × X)} :
    packingEntropyEntourage T ∅ U = ⊥ := by
  suffices h : ∀ᶠ n : ℕ in atTop, log (packingMaxcard T ∅ U n) / n = ⊥ by
    rw [packingEntropyEntourage, limsup_congr h]
    exact limsup_const ⊥
  simp only [packingMaxcard_empty, ENat.toENNReal_zero, log_zero, eventually_atTop]
  exact ⟨1, fun n n_pos ↦ bot_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)⟩

@[simp]
lemma packingEntropyInfEntourage_empty {T : X → X} {U : Set (X × X)} :
    packingEntropyInfEntourage T ∅ U = ⊥ :=
  eq_bot_mono (packingEntropyInfEntourage_le_packingEntropyEntourage T ∅ U)
    packingEntropyEntourage_empty

lemma packingEntropyInfEntourage_nonneg (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) :
    0 ≤ packingEntropyInfEntourage T F U :=
  (le_iInf fun n ↦ div_nonneg (log_packingMaxcard_nonneg T h U n) n.cast_nonneg').trans
    iInf_le_liminf

lemma packingEntropyEntourage_nonneg (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) :
    0 ≤ packingEntropyEntourage T F U :=
  (packingEntropyInfEntourage_nonneg T h U).trans
    (packingEntropyInfEntourage_le_packingEntropyEntourage T F U)

lemma packingEntropyInfEntourage_univ (T : X → X) {F : Set X} (h : F.Nonempty) :
    packingEntropyInfEntourage T F univ = 0 := by
  simp [packingEntropyInfEntourage, packingMaxcard_univ T h]

lemma packingEntropyEntourage_univ (T : X → X) {F : Set X} (h : F.Nonempty) :
    packingEntropyEntourage T F univ = 0 := by
  simp [packingEntropyEntourage, packingMaxcard_univ T h]

lemma packingEntropyInfEntourage_le_coverEntropyInfEntourage (T : X → X) (F : Set X)
    {U : Set (X × X)} (U_symm : IsSymmetricRel U) :
    packingEntropyInfEntourage T F U ≤ coverEntropyInfEntourage T F U :=
  (liminf_le_liminf) (Eventually.of_forall fun n ↦ (div_le_div_right_of_nonneg n.cast_nonneg'
    (log_monotone (ENat.toENNReal_le.2 (packingMaxcard_le_coverMincard T F U_symm n)))))

lemma coverEntropyInfEntourage_le_packingEntropyInfEntourage (T : X → X) (F : Set X)
    {U : Set (X × X)} (U_rfl : idRel ⊆ U) (U_symm : IsSymmetricRel U) :
    coverEntropyInfEntourage T F (U ○ U) ≤ packingEntropyInfEntourage T F U := by
  refine (liminf_le_liminf) (Eventually.of_forall fun n ↦ ?_)
  apply div_le_div_right_of_nonneg n.cast_nonneg' (log_monotone _)
  exact ENat.toENNReal_le.2 (coverMincard_le_packingMaxcard T F U_rfl U_symm n)

lemma packingEntropyEntourage_le_coverEntropyEntourage (T : X → X) (F : Set X) {U : Set (X × X)}
    (U_symm : IsSymmetricRel U) :
    packingEntropyEntourage T F U ≤ coverEntropyEntourage T F U := by
  refine (limsup_le_limsup) (Eventually.of_forall fun n ↦ ?_)
  apply div_le_div_right_of_nonneg n.cast_nonneg' (log_monotone _)
  exact ENat.toENNReal_le.2 (packingMaxcard_le_coverMincard T F U_symm n)

lemma coverEntropyEntourage_le_packingEntropyEntourage (T : X → X) (F : Set X) {U : Set (X × X)}
    (U_rfl : idRel ⊆ U) (U_symm : IsSymmetricRel U) :
    coverEntropyEntourage T F (U ○ U) ≤ packingEntropyEntourage T F U := by
  refine (limsup_le_limsup) (Eventually.of_forall fun n ↦ ?_)
  apply div_le_div_right_of_nonneg n.cast_nonneg' (log_monotone _)
  exact ENat.toENNReal_le.2 (coverMincard_le_packingMaxcard T F U_rfl U_symm n)

/-! ### Relationship with entropy via covers -/

variable [UniformSpace X] (T : X → X) (F : Set X)

/-- Bowen-Dinaburg's definition of topological entropy using packings is
  `⨆ U ∈ 𝓤 X, packingEntropyEntourage T F U`. This quantity is the same as the topological entropy
  using covers, so there is no need to define a new notion of topological entropy.
  This version of the theorem relates the `liminf` versions of topological entropy. -/
theorem coverEntropyInf_eq_iSup_packingEntropyInfEntourage :
    coverEntropyInf T F = ⨆ U ∈ 𝓤 X, packingEntropyInfEntourage T F U := by
  apply le_antisymm <;> refine iSup₂_le fun U U_u ↦ ?_
  · obtain ⟨V, V_u, V_s, V_U⟩ := comp_symm_mem_uniformity_sets U_u
    apply (coverEntropyInfEntourage_antitone T F V_U).trans (le_iSup₂_of_le V V_u _)
    exact coverEntropyInfEntourage_le_packingEntropyInfEntourage T F (refl_le_uniformity V_u) V_s
  · apply (packingEntropyInfEntourage_antitone T F (symmetrizeRel_subset_self U)).trans
    apply (le_iSup₂ (symmetrizeRel U) (symmetrize_mem_uniformity U_u)).trans'
    exact packingEntropyInfEntourage_le_coverEntropyInfEntourage T F (symmetric_symmetrizeRel U)

/-- Bowen-Dinaburg's definition of topological entropy using packings is
  `⨆ U ∈ 𝓤 X, packingEntropyEntourage T F U`. This quantity is the same as the topological entropy
  using covers, so there is no need to define a new notion of topological entropy.
  This version of the theorem relates the `limsup` versions of topological entropy. -/
theorem coverEntropy_eq_iSup_packingEntropyEntourage :
    coverEntropy T F = ⨆ U ∈ 𝓤 X, packingEntropyEntourage T F U := by
  apply le_antisymm <;> refine iSup₂_le fun U U_uni ↦ ?_
  · obtain ⟨V, V_u, V_s, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
    apply (coverEntropyEntourage_antitone T F V_U).trans (le_iSup₂_of_le V V_u _)
    exact coverEntropyEntourage_le_packingEntropyEntourage T F (refl_le_uniformity V_u) V_s
  · apply (packingEntropyEntourage_antitone T F (symmetrizeRel_subset_self U)).trans
    apply (le_iSup₂ (symmetrizeRel U) (symmetrize_mem_uniformity U_uni)).trans'
    exact packingEntropyEntourage_le_coverEntropyEntourage T F (symmetric_symmetrizeRel U)

lemma coverEntropyInf_eq_iSup_basis_packingEntropyInfEntourage {ι : Sort*} {p : ι → Prop}
    {s : ι → Set (X × X)} (h : (𝓤 X).HasBasis p s) (T : X → X) (F : Set X) :
    coverEntropyInf T F = ⨆ (i : ι) (_ : p i), packingEntropyInfEntourage T F (s i) := by
  rw [coverEntropyInf_eq_iSup_packingEntropyInfEntourage T F]
  apply (iSup₂_mono' fun i h_i ↦ ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩).antisymm'
  refine iSup₂_le fun U U_uni ↦ ?_
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  apply (packingEntropyInfEntourage_antitone T F si_U).trans
  exact le_iSup₂ (f := fun (i : ι) (_ : p i) ↦ packingEntropyInfEntourage T F (s i)) i h_i

lemma coverEntropy_eq_iSup_basis_packingEntropyEntourage {ι : Sort*} {p : ι → Prop}
    {s : ι → Set (X × X)} (h : (𝓤 X).HasBasis p s) (T : X → X) (F : Set X) :
    coverEntropy T F = ⨆ (i : ι) (_ : p i), packingEntropyEntourage T F (s i) := by
  rw [coverEntropy_eq_iSup_packingEntropyEntourage T F]
  apply (iSup₂_mono' fun i h_i ↦ ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩).antisymm'
  refine iSup₂_le fun U U_uni ↦ ?_
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  apply (packingEntropyEntourage_antitone T F si_U).trans _
  exact le_iSup₂ (f := fun (i : ι) (_ : p i) ↦ packingEntropyEntourage T F (s i)) i h_i

lemma packingEntropyInfEntourage_le_coverEntropyInf {U : Set (X × X)} (h : U ∈ 𝓤 X) :
    packingEntropyInfEntourage T F U ≤ coverEntropyInf T F :=
  coverEntropyInf_eq_iSup_packingEntropyInfEntourage T F ▸
    le_iSup₂ (f := fun (U : Set (X × X)) (_ : U ∈ 𝓤 X) ↦ packingEntropyInfEntourage T F U) U h

lemma packingEntropyEntourage_le_coverEntropy {U : Set (X × X)} (h : U ∈ 𝓤 X) :
    packingEntropyEntourage T F U ≤ coverEntropy T F :=
  coverEntropy_eq_iSup_packingEntropyEntourage T F ▸
    le_iSup₂ (f := fun (U : Set (X × X)) (_ : U ∈ 𝓤 X) ↦ packingEntropyEntourage T F U) U h

end Dynamics
