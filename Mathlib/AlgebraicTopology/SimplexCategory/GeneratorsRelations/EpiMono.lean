/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic
/-! # Epi-mono factorisation in the simplex category presented by generators and relations

This file aims to establish that there is a nice epi-mono factorisation in `SimplexCategoryGenRel`.
More precisely, we introduce two (inductively-defined) morphism property `P_δ` and `P_σ` that
single out morphisms that are compositions of `δ i` (resp. `σ i`).

The main result of this file is `exists_P_σ_P_δ_factorisation`, which asserts that every
moprhism as a decomposition of a `P_σ` followed by a `P_δ`.

-/

namespace AlgebraicTopology.SimplexCategoryGenRel
open CategoryTheory

section EpiMono

/-- `δ i` is a split monomorphism thanks to the simplicial identities. -/
def SplitMonoδ {n : ℕ} {i : Fin (n + 2)} : SplitMono (δ i) where
  retraction := by
    induction i using Fin.lastCases with
    | last => exact σ n
    | cast i => exact σ i
  id := by
    cases i using Fin.lastCases
    · simp only [Fin.natCast_eq_last, Fin.lastCases_last]
      exact δ_comp_σ_succ
    · simp only [Fin.natCast_eq_last, Fin.lastCases_castSucc]
      exact δ_comp_σ_self

instance {n : ℕ} {i : Fin (n + 2)} : IsSplitMono (δ i) := .mk' SplitMonoδ

/-- `δ i` is a split epimorphism thanks to the simplicial identities. -/
def SplitEpiσ {n : ℕ} {i : Fin (n + 1)} : SplitEpi (σ i) where
  section_ := δ i.castSucc
  id := δ_comp_σ_self

instance {n : ℕ} {i : Fin (n + 1)} : IsSplitEpi (σ i) := .mk' SplitEpiσ

/-- Auxiliary predicate to express that a morphism is purely a composition of `σ i`s. -/
inductive P_σ : MorphismProperty SimplexCategoryGenRel
  | σ {n : ℕ} (i : Fin (n + 1)) : P_σ <| σ i
  | id {n : ℕ} : P_σ <| 𝟙 (.mk n)
  | comp {n : ℕ} (i : Fin (n + 1)) {a : SimplexCategoryGenRel} (g : a ⟶ .mk (n + 1))
    (hg: P_σ g) : P_σ <| g ≫ σ i

/-- A version of `P_σ` where composition is taken on the right instead. It is equivalent to `P_σ`
(see `P_σ_eq_P_σ'`). -/
inductive P_σ' : MorphismProperty SimplexCategoryGenRel
  | σ {n : ℕ} (i : Fin (n + 1)) : P_σ' <| σ i
  | id {n : ℕ} : P_σ' <| 𝟙 (.mk n)
  | comp {n : ℕ} (i : Fin (n + 1)) {a : SimplexCategoryGenRel} (g :.mk n ⟶ a)
    (hg: P_σ' g) : P_σ' <| σ i ≫ g

/-- Auxiliary predicate to express that a morphism is purely a composition of `δ i`s. -/
inductive P_δ : MorphismProperty SimplexCategoryGenRel
  | δ {n : ℕ} (i : Fin (n + 2)) : P_δ <| δ i
  | id {n : ℕ} : P_δ <| 𝟙 (.mk n)
  | comp {n : ℕ} (i : Fin (n + 2)) {a : SimplexCategoryGenRel} (g : a ⟶ .mk n )
    (hg: P_δ g) : P_δ <| g ≫ δ i

/-- A version of `P_δ` where composition is taken on the right instead. It is equivalent to `P_δ`
(see `P_σ_eq_P_δ'`). -/
inductive P_δ' : MorphismProperty SimplexCategoryGenRel
  | δ {n : ℕ} (i : Fin (n + 2)) : P_δ' <| δ i
  | id {n : ℕ} : P_δ' <| 𝟙 (.mk n)
  | comp {a : SimplexCategoryGenRel} {n : ℕ} (i : Fin (n + 2)) (g : .mk (n + 1) ⟶ a)
    (hg: P_δ' g) : P_δ' <| δ i ≫ g

lemma P_σ_eqToHom {x y : SimplexCategoryGenRel} (h : x = y) : P_σ <| eqToHom h := by
  subst h
  rw [eqToHom_refl]
  exact P_σ.id

lemma P_δ_eqToHom {x y : SimplexCategoryGenRel} (h : x = y) : P_δ <| eqToHom h := by
  subst h
  rw [eqToHom_refl]
  exact P_δ.id

lemma P_δ_comp {x y z : SimplexCategoryGenRel} (f : x ⟶ y) (g : y ⟶ z) :
    P_δ f → P_δ g → P_δ (f ≫ g) := by
  intro hf hg
  induction hg with
  | δ i => exact P_δ.comp _ f hf
  | id => rwa [Category.comp_id]
  | comp i b _ h => specialize h f hf
                    rw [← Category.assoc]
                    exact P_δ.comp i (f ≫ b) h

lemma P_σ_comp {x y z : SimplexCategoryGenRel} (f : x ⟶ y) (g : y ⟶ z) :
    P_σ f → P_σ g → P_σ (f ≫ g) := by
  intro hf hg
  induction hg with
  | σ i => exact P_σ.comp _ f hf
  | id => rwa [Category.comp_id]
  | comp i b _ h => specialize h f hf
                    rw [← Category.assoc]
                    exact P_σ.comp i (f ≫ b) h

lemma P_σ'_comp {x y z : SimplexCategoryGenRel} (f : x ⟶ y) (g : y ⟶ z) :
    P_σ' f → P_σ' g → P_σ' (f ≫ g) := by
  intro hf hg
  induction hf with
  | σ i => exact P_σ'.comp _ g hg
  | id => rwa [Category.id_comp]
  | comp i b _ h => specialize h g hg
                    rw [Category.assoc]
                    exact P_σ'.comp i (b ≫ g) h

lemma P_δ'_comp {x y z : SimplexCategoryGenRel} (f : x ⟶ y) (g : y ⟶ z) :
    P_δ' f → P_δ' g → P_δ' (f ≫ g) := by
  intro hf hg
  induction hf with
  | δ i => exact P_δ'.comp _ g hg
  | id => rwa [Category.id_comp]
  | comp i b _ h => specialize h g hg
                    rw [Category.assoc]
                    exact P_δ'.comp i (b ≫ g) h

/-- The property `P_σ` is equivalent to `P_σ'`. -/
lemma P_σ_eq_P_σ' : P_σ = P_σ' := by
  apply le_antisymm <;> intro x y f h
  · induction h with
    | σ i => exact P_σ'.σ i
    | id => exact P_σ'.id
    | comp i f h h' => exact P_σ'_comp _ _ h' (P_σ'.σ _)
  · induction h with
    | σ i => exact P_σ.σ i
    | id => exact P_σ.id
    | comp i f h h' => exact P_σ_comp _ _ (P_σ.σ _) h'

/-- The property `P_δ` is equivalent to `P_δ'`. -/
lemma P_δ_eq_P_δ' : P_δ = P_δ' := by
  apply le_antisymm <;> intro x y f h
  · induction h with
    | δ i => exact P_δ'.δ i
    | id => exact P_δ'.id
    | comp i f h h' => exact P_δ'_comp _ _ h' (P_δ'.δ _)
  · induction h with
    | δ i => exact P_δ.δ i
    | id => exact P_δ.id
    | comp i f h h' => exact P_δ_comp _ _ (P_δ.δ _) h'

/-- All `P_σ` are split epis as composition of such. -/
lemma isSplitEpi_P_σ {x y : SimplexCategoryGenRel} {e : x ⟶ y} (he : P_σ e) : IsSplitEpi e := by
  induction he <;> infer_instance

/-- All `P_δ` are split monos as composition of such. -/
lemma isSplitMono_P_δ {x y : SimplexCategoryGenRel} {m : x ⟶ y} (hm : P_δ m) :
    IsSplitMono m := by
  induction hm <;> infer_instance

lemma isSplitEpi_P_σ_toSimplexCategory {x y : SimplexCategoryGenRel} {e : x ⟶ y} (he : P_σ e)
    : IsSplitEpi <| toSimplexCategory.map e := by
  constructor
  constructor
  apply SplitEpi.map
  exact isSplitEpi_P_σ he |>.exists_splitEpi.some

lemma isSplitMono_P_δ_toSimplexCategory {x y : SimplexCategoryGenRel} {m : x ⟶ y} (hm : P_δ m)
    : IsSplitMono <| toSimplexCategory.map m := by
  constructor
  constructor
  apply SplitMono.map
  exact isSplitMono_P_δ hm |>.exists_splitMono.some

lemma eq_or_len_le_of_P_δ {x y : SimplexCategoryGenRel} {f : x ⟶ y} (h_δ : P_δ f) :
    (∃ h : x = y, f = eqToHom h) ∨ x.len < y.len := by
  induction h_δ with
  | δ i => right; simp
  | id => left; use rfl; simp
  | comp i u _ h' =>
    rcases h' with ⟨e, _⟩ | h'
    · right; rw [e]; exact Nat.lt_add_one _
    · right; exact Nat.lt_succ_of_lt h'

end EpiMono

section ExistenceOfFactorisations

/-- An auxiliary lemma to show that one can always use the simplicial identities to simplify a term
in the form `δ ≫ σ` into either an identity, or a term of the form `σ ≫ δ`. This is the crucial
special case to induct on to get an epi-mono factorisation for all morphisms. -/
private lemma switch_δ_σ {n : ℕ} (i : Fin (n + 1 + 1)) (i' : Fin (n + 1 + 2)) :
   δ i' ≫ σ i = 𝟙 _ ∨ ∃ j j', δ i' ≫ σ i = σ j ≫ δ j' := by
  obtain h'' | h'' | h'' : i'= i.castSucc ∨ i' < i.castSucc ∨ i.castSucc < i' := by
      simp only [lt_or_lt_iff_ne, ne_eq]
      tauto
  · subst h''
    rw [δ_comp_σ_self]
    simp
  · obtain ⟨h₁, h₂⟩ : i' ≠ Fin.last _ ∧ i ≠ 0 := by
      constructor
      · exact Fin.ne_last_of_lt h''
      · rw [Fin.lt_def, Fin.coe_castSucc] at h''
        apply Fin.ne_of_val_ne
        exact Nat.not_eq_zero_of_lt h''
    rw [← i'.castSucc_castPred h₁, ← i.succ_pred h₂]
    have H : i'.castPred h₁ ≤ (i.pred h₂).castSucc := by
      simp only [Fin.le_def, Fin.coe_castPred, Fin.coe_castSucc, Fin.coe_pred]
      rw [Fin.lt_def, Nat.lt_iff_add_one_le] at h''
      exact Nat.le_sub_one_of_lt h''
    rw [δ_comp_σ_of_le H]
    right
    use i.pred h₂, i'.castPred h₁
  · by_cases h : i.succ = i'
    · subst h
      rw [δ_comp_σ_succ]
      simp
    · obtain ⟨h₁, h₂⟩ : i ≠ Fin.last _ ∧ i' ≠ 0 := by
        constructor
        · by_cases h' : i' = Fin.last _
          · simp_all
          · rw [← Fin.val_eq_val] at h' h
            apply Fin.ne_of_val_ne
            rw [Fin.lt_def, Fin.coe_castSucc] at h''
            rcases i with ⟨i, hi⟩; rcases i' with ⟨i', hi'⟩
            intro hyp; subst hyp
            rw [Nat.lt_iff_add_one_le] at h'' hi'
            simp_all only [add_le_add_iff_right, Fin.val_last, Fin.succ_mk]
            rw [← one_add_one_eq_two] at hi'
            exact h (Nat.le_antisymm hi' h'').symm
        · exact Fin.ne_zero_of_lt h''
      rw [← i'.succ_pred h₂, ← i.castSucc_castPred h₁]
      have H : (i.castPred h₁).castSucc < i'.pred h₂ := by
        rcases (Nat.le_iff_lt_or_eq.mp h'') with h' | h'
        · simp only [Fin.lt_def, Fin.coe_castSucc, Nat.succ_eq_add_one, Fin.castSucc_castPred,
            Fin.coe_pred] at *
          exact Nat.lt_sub_of_add_lt h'
        · exfalso
          exact Fin.val_ne_of_ne h h'
      rw [δ_comp_σ_of_gt H]
      right
      use i.castPred h₁, i'.pred h₂

/-- A low-dimensional special case of the previous -/
private lemma switch_δ_σ₀ (i : Fin 1) (i' : Fin 2) :
    δ i' ≫ σ i = 𝟙 _ := by
  rcases i with ⟨i, hi⟩
  rcases i' with ⟨i', hi'⟩
  simp at hi hi'
  rw [Nat.lt_iff_le_pred Nat.zero_lt_two] at hi'
  simp at hi'
  subst hi
  obtain h | h := Nat.le_one_iff_eq_zero_or_eq_one.mp hi'
  · subst h
    simp only [Fin.zero_eta, Fin.isValue, ← Fin.castSucc_zero, δ_comp_σ_self]
  · subst h
    simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta]
    rw [← Fin.succ_zero_eq_one, δ_comp_σ_succ]

private lemma factor_δ_σ {n : ℕ} (i : Fin (n + 1)) (i' : Fin (n + 2)) :
    ∃ (z : SimplexCategoryGenRel) (e : mk n ⟶ z) (m : z ⟶ mk n)
      (_ : P_σ e) (_ : P_δ m), δ i' ≫ σ i = e ≫ m := by
  cases n with
  | zero =>
    rw [switch_δ_σ₀]
    use mk 0, 𝟙 _, 𝟙 _, P_σ.id, P_δ.id
    simp
  | succ n =>
    obtain h | ⟨j, j', h⟩ := switch_δ_σ i i' <;> rw [h]
    · use mk (n + 1), 𝟙 _, 𝟙 _, P_σ.id, P_δ.id
      simp
    · use mk n, σ j, δ j', P_σ.σ _, P_δ.δ _

/-- An auxiliary lemma that shows there exists a factorisation as a P_δ followed by a P_σ for
morphisms of the form `P_δ ≫ σ`. -/
private lemma factor_P_δ_σ {n : ℕ} (i : Fin (n + 1)) {x : SimplexCategoryGenRel}
    (f : x ⟶ mk (n + 1)) (hf : P_δ f) : ∃ (z : SimplexCategoryGenRel) (e : x ⟶ z) (m : z ⟶ mk n)
      (_ : P_σ e) (_ : P_δ m), f ≫ σ i = e ≫ m := by
  induction n using Nat.case_strong_induction_on generalizing x with
  | hz => cases hf with
    | δ i => exact factor_δ_σ _ _
    | id  =>
      rw [Category.id_comp]
      use mk 0, σ i, 𝟙 _, P_σ.σ _, P_δ.id
      simp
    | comp j f hf =>
      obtain ⟨h', hf'⟩ | hf' := eq_or_len_le_of_P_δ hf
      · subst h'
        simp only [eqToHom_refl] at hf'
        subst hf'
        rw [Category.id_comp]
        exact factor_δ_σ _ _
      · simp at hf'
  | hi n h_rec =>
    cases hf with
    | δ i' => exact factor_δ_σ _ _
    | @id n =>
      rw [Category.id_comp]
      use mk (n + 1), σ i, 𝟙 _, P_σ.σ _, P_δ.id
      simp
    | @comp m i' _ g hg =>
      obtain ⟨h', h''⟩ | h := eq_or_len_le_of_P_δ hg
      · subst h'
        rw [eqToHom_refl] at h''; subst h''
        rw [Category.id_comp]
        exact factor_δ_σ _ _
      · obtain h' | ⟨j, j', h'⟩ := switch_δ_σ i i' <;> rw [Category.assoc, h']
        · rw [Category.comp_id]
          use x, 𝟙 x, g, P_σ.id, hg
          simp
        · rw [mk_len, Nat.lt_add_one_iff] at h
          obtain ⟨z, e, m₁, he, hm₁, h⟩ := h_rec n (Nat.le_refl _) j g hg
          rw [reassoc_of% h]
          use z, e, m₁ ≫ δ j', he, P_δ.comp _ m₁ hm₁

/-- Any morphism in `SimplexCategoryGenRel` can be decomposed as a `P_σ` followed by a `P_δ`. -/
theorem exists_P_σ_P_δ_factorisation {x y : SimplexCategoryGenRel} (f : x ⟶ y) :
    ∃ (z : SimplexCategoryGenRel) (e : x ⟶ z) (m : z ⟶ y)
        (_ : P_σ e) (_ : P_δ m), f = e ≫ m := by
  induction f using hom_induction with
  | @hi n => use (mk n), (𝟙 (mk n)), (𝟙 (mk n)), P_σ.id, P_δ.id; simp
  | @hc₁ n n' f j h =>
    obtain ⟨z, e, m, ⟨he, hm, h⟩⟩ := h
    rw [h, Category.assoc]
    use z, e, m ≫ δ j, he, P_δ.comp _ _ hm
  | @hc₂ n n' f j h =>
    obtain ⟨z, e, m, ⟨he, hm, h⟩⟩ := h
    rw [h]
    cases hm with
    | @δ i j' =>
      rw [Category.assoc]
      obtain ⟨z₁, e₁, m₁, ⟨he₁, hm₁, h₁⟩⟩ := factor_δ_σ j j'
      rw [h₁]
      use z₁, e ≫ e₁, m₁, P_σ_comp _ _ he he₁, hm₁
      simp
    | @id n =>
      simp only [Category.comp_id]
      use mk n', e ≫ σ j, 𝟙 _, P_σ.comp _ _ he, P_δ.id
      simp
    | @comp n'' i x' g hg =>
      rw [Category.assoc, Category.assoc]
      cases n' with
      | zero =>
        rw [switch_δ_σ₀, Category.comp_id]
        use z, e, g, he, hg
      | succ n =>
        obtain h' | ⟨j', j'', h'⟩ := switch_δ_σ j i <;> rw [h']
        · rw [Category.comp_id]
          use z, e, g, he, hg
        · obtain ⟨z₁, e₁, m₁, ⟨he₁, hm₁, h₁⟩⟩ := factor_P_δ_σ j' g hg
          rw [reassoc_of% h₁]
          use z₁, e ≫ e₁, m₁ ≫ δ j'', P_σ_comp _ _ he he₁, P_δ.comp _ _ hm₁
          simp

end ExistenceOfFactorisations

end AlgebraicTopology.SimplexCategoryGenRel
