/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import Mathlib.Tactic.Linarith
import Mathlib.CategoryTheory.Skeletal
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Category.NonemptyFinLinOrd
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.WithTerminal

#align_import algebraic_topology.simplex_category from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-! # The simplex category

We construct a skeletal model of the simplex category, with objects `ℕ` and the
morphism `n ⟶ m` being the monotone maps from `Fin (n+1)` to `Fin (m+1)`.

We show that this category is equivalent to `NonemptyFinLinOrd`.

## Remarks

The definitions `SimplexCategory` and `SimplexCategory.Hom` are marked as irreducible.

We provide the following functions to work with these objects:
1. `SimplexCategory.mk` creates an object of `SimplexCategory` out of a natural number.
  Use the notation `[n]` in the `Simplicial` locale.
2. `SimplexCategory.len` gives the "length" of an object of `SimplexCategory`, as a natural.
3. `SimplexCategory.Hom.mk` makes a morphism out of a monotone map between `Fin`'s.
4. `SimplexCategory.Hom.toOrderHom` gives the underlying monotone map associated to a
  term of `SimplexCategory.Hom`.

-/


universe v

open CategoryTheory CategoryTheory.Limits

/-- The simplex category:
* objects are natural numbers `n : ℕ`
* morphisms from `n` to `m` are monotone functions `Fin (n+1) → Fin (m+1)`
-/
def SimplexCategory :=
  ℕ
#align simplex_category SimplexCategory

namespace SimplexCategory

section


-- porting note: the definition of `SimplexCategory` is made irreducible below
/-- Interpret a natural number as an object of the simplex category. -/
def mk (n : ℕ) : SimplexCategory :=
  n
#align simplex_category.mk SimplexCategory.mk

/-- the `n`-dimensional simplex can be denoted `[n]` -/
scoped[Simplicial] notation "[" n "]" => SimplexCategory.mk n

-- TODO: Make `len` irreducible.
/-- The length of an object of `SimplexCategory`. -/
def len (n : SimplexCategory) : ℕ :=
  n
#align simplex_category.len SimplexCategory.len

@[ext]
theorem ext (a b : SimplexCategory) : a.len = b.len → a = b :=
  id
#align simplex_category.ext SimplexCategory.ext

attribute [irreducible] SimplexCategory

open Simplicial

@[simp]
theorem len_mk (n : ℕ) : [n].len = n :=
  rfl
#align simplex_category.len_mk SimplexCategory.len_mk

@[simp]
theorem mk_len (n : SimplexCategory) : ([n.len] : SimplexCategory) = n :=
  rfl
#align simplex_category.mk_len SimplexCategory.mk_len

/-- A recursor for `SimplexCategory`. Use it as `induction Δ using SimplexCategory.rec`. -/
protected def rec {F : SimplexCategory → Sort*} (h : ∀ n : ℕ, F [n]) : ∀ X, F X := fun n =>
  h n.len
#align simplex_category.rec SimplexCategory.rec

-- porting note: removed @[nolint has_nonempty_instance]
/-- Morphisms in the `SimplexCategory`. -/
protected def Hom (a b : SimplexCategory) :=
  Fin (a.len + 1) →o Fin (b.len + 1)
#align simplex_category.hom SimplexCategory.Hom

namespace Hom

/-- Make a morphism in `SimplexCategory` from a monotone map of `Fin`'s. -/
def mk {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1)) : SimplexCategory.Hom a b :=
  f
#align simplex_category.hom.mk SimplexCategory.Hom.mk

/-- Recover the monotone map from a morphism in the simplex category. -/
def toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) :
    Fin (a.len + 1) →o Fin (b.len + 1) :=
  f
#align simplex_category.hom.to_order_hom SimplexCategory.Hom.toOrderHom

theorem ext' {a b : SimplexCategory} (f g : SimplexCategory.Hom a b) :
    f.toOrderHom = g.toOrderHom → f = g :=
  id
#align simplex_category.hom.ext SimplexCategory.Hom.ext'

attribute [irreducible] SimplexCategory.Hom

@[simp]
theorem mk_toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) : mk f.toOrderHom = f :=
  rfl
#align simplex_category.hom.mk_to_order_hom SimplexCategory.Hom.mk_toOrderHom

@[simp]
theorem toOrderHom_mk {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1)) :
    (mk f).toOrderHom = f :=
  rfl
#align simplex_category.hom.to_order_hom_mk SimplexCategory.Hom.toOrderHom_mk

theorem mk_toOrderHom_apply {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1))
    (i : Fin (a.len + 1)) : (mk f).toOrderHom i = f i :=
  rfl
#align simplex_category.hom.mk_to_order_hom_apply SimplexCategory.Hom.mk_toOrderHom_apply

/-- Identity morphisms of `SimplexCategory`. -/
@[simp]
def id (a : SimplexCategory) : SimplexCategory.Hom a a :=
  mk OrderHom.id
#align simplex_category.hom.id SimplexCategory.Hom.id

/-- Composition of morphisms of `SimplexCategory`. -/
@[simp]
def comp {a b c : SimplexCategory} (f : SimplexCategory.Hom b c) (g : SimplexCategory.Hom a b) :
    SimplexCategory.Hom a c :=
  mk <| f.toOrderHom.comp g.toOrderHom
#align simplex_category.hom.comp SimplexCategory.Hom.comp

end Hom

@[simps]
instance smallCategory : SmallCategory.{0} SimplexCategory where
  Hom n m := SimplexCategory.Hom n m
  id m := SimplexCategory.Hom.id _
  comp f g := SimplexCategory.Hom.comp g f
#align simplex_category.small_category SimplexCategory.smallCategory

-- porting note: added because `Hom.ext'` is not triggered automatically
@[ext]
theorem Hom.ext {a b : SimplexCategory} (f g : a ⟶ b) :
    f.toOrderHom = g.toOrderHom → f = g :=
  Hom.ext' _ _

/-- The constant morphism from [0]. -/
def const (x : SimplexCategory) (i : Fin (x.len + 1)) : ([0] : SimplexCategory) ⟶ x :=
  Hom.mk <| ⟨fun _ => i, by tauto⟩
#align simplex_category.const SimplexCategory.const

-- porting note: removed @[simp] as the linter complains
theorem const_comp (x y : SimplexCategory) (i : Fin (x.len + 1)) (f : x ⟶ y) :
    const x i ≫ f = const y (f.toOrderHom i) :=
  rfl
#align simplex_category.const_comp SimplexCategory.const_comp

/-- Make a morphism `[n] ⟶ [m]` from a monotone map between fin's.
This is useful for constructing morphisms between `[n]` directly
without identifying `n` with `[n].len`.
-/
@[simp]
def mkHom {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1)) : ([n] : SimplexCategory) ⟶ [m] :=
  SimplexCategory.Hom.mk f
#align simplex_category.mk_hom SimplexCategory.mkHom

theorem hom_zero_zero (f : ([0] : SimplexCategory) ⟶ [0]) : f = 𝟙 _ := by
  ext : 3
  apply @Subsingleton.elim (Fin 1)
#align simplex_category.hom_zero_zero SimplexCategory.hom_zero_zero

end

open Simplicial

section Generators

/-!
## Generating maps for the simplex category

TODO: prove that the simplex category is equivalent to
one given by the following generators and relations.
-/


/-- The `i`-th face map from `[n]` to `[n+1]` -/
def δ {n} (i : Fin (n + 2)) : ([n] : SimplexCategory) ⟶ [n + 1] :=
  mkHom (Fin.succAboveEmb i).toOrderHom
#align simplex_category.δ SimplexCategory.δ

/-- The `i`-th degeneracy map from `[n+1]` to `[n]` -/
def σ {n} (i : Fin (n + 1)) : ([n + 1] : SimplexCategory) ⟶ [n] :=
  mkHom
    { toFun := Fin.predAbove i
      monotone' := Fin.predAbove_right_monotone i }
#align simplex_category.σ SimplexCategory.σ

/-- The generic case of the first simplicial identity -/
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    δ i ≫ δ j.succ = δ j ≫ δ (Fin.castSucc i) := by
  ext k
  dsimp [δ, Fin.succAbove]
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  split_ifs <;> · simp at * <;> linarith
#align simplex_category.δ_comp_δ SimplexCategory.δ_comp_δ

theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j) :
    δ i ≫ δ j =
      δ (j.pred fun (hj : j = 0) => by simp [hj, Fin.not_lt_zero] at H) ≫
        δ (Fin.castSucc i) := by
  rw [← δ_comp_δ]
  · rw [Fin.succ_pred]
  · simpa only [Fin.le_iff_val_le_val, ← Nat.lt_succ_iff, Nat.succ_eq_add_one, ← Fin.val_succ,
      j.succ_pred, Fin.lt_iff_val_lt_val] using H
#align simplex_category.δ_comp_δ' SimplexCategory.δ_comp_δ'

theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j) :
    δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) ≫ δ j.succ =
      δ j ≫ δ i := by
  rw [δ_comp_δ]
  · rfl
  · exact H
#align simplex_category.δ_comp_δ'' SimplexCategory.δ_comp_δ''

/-- The special case of the first simplicial identity -/
@[reassoc]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} : δ i ≫ δ (Fin.castSucc i) = δ i ≫ δ i.succ :=
  (δ_comp_δ (le_refl i)).symm
#align simplex_category.δ_comp_δ_self SimplexCategory.δ_comp_δ_self

@[reassoc]
theorem δ_comp_δ_self' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = Fin.castSucc i) :
    δ i ≫ δ j = δ i ≫ δ i.succ := by
  subst H
  rw [δ_comp_δ_self]
#align simplex_category.δ_comp_δ_self' SimplexCategory.δ_comp_δ_self'

/-- The second simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j) :
    δ (Fin.castSucc i) ≫ σ j.succ = σ j ≫ δ i := by
  ext k : 3
  dsimp [σ, δ]
  rcases le_or_lt i k with (hik | hik)
  · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hik),
    Fin.succ_predAbove_succ, Fin.succAbove_of_le_castSucc]
    rcases le_or_lt k (j.castSucc) with (hjk | hjk)
    · rwa [Fin.predAbove_of_le_castSucc _ _ hjk, Fin.castSucc_castPred]
    · rw [Fin.le_castSucc_iff, Fin.predAbove_of_castSucc_lt _ _ hjk, Fin.succ_pred]
      exact H.trans_lt hjk
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hik)]
    have hjk := H.trans_lt' hik
    rw [Fin.predAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr
      (hjk.trans (Fin.castSucc_lt_succ _)).le),
      Fin.predAbove_of_le_castSucc _ _ hjk.le, Fin.castPred_castSucc, Fin.succAbove_of_castSucc_lt,
      Fin.castSucc_castPred]
    rwa [Fin.castSucc_castPred]
#align simplex_category.δ_comp_σ_of_le SimplexCategory.δ_comp_σ_of_le

/-- The first part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} :
    δ (Fin.castSucc i) ≫ σ i = 𝟙 ([n] : SimplexCategory) := by
  rcases i with ⟨i, hi⟩
  ext ⟨j, hj⟩
  simp? at hj says simp only [len_mk] at hj
  dsimp [σ, δ, Fin.predAbove, Fin.succAbove]
  simp only [Fin.lt_iff_val_lt_val, Fin.dite_val, Fin.ite_val, Fin.coe_pred, ge_iff_le,
    Fin.coe_castLT, dite_eq_ite]
  split_ifs
  any_goals simp
  all_goals linarith
#align simplex_category.δ_comp_σ_self SimplexCategory.δ_comp_σ_self

@[reassoc]
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i) :
    δ j ≫ σ i = 𝟙 ([n] : SimplexCategory) := by
  subst H
  rw [δ_comp_σ_self]
#align simplex_category.δ_comp_σ_self' SimplexCategory.δ_comp_σ_self'

/-- The second part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : δ i.succ ≫ σ i = 𝟙 ([n] : SimplexCategory) := by
  ext j
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  dsimp [δ, σ, Fin.succAbove, Fin.predAbove]
  split_ifs <;> simp <;> simp at * <;> linarith
#align simplex_category.δ_comp_σ_succ SimplexCategory.δ_comp_σ_succ

@[reassoc]
theorem δ_comp_σ_succ' {n} (j : Fin (n + 2)) (i : Fin (n + 1)) (H : j = i.succ) :
    δ j ≫ σ i = 𝟙 ([n] : SimplexCategory) := by
  subst H
  rw [δ_comp_σ_succ]
#align simplex_category.δ_comp_σ_succ' SimplexCategory.δ_comp_σ_succ'

/-- The fourth simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i) :
    δ i.succ ≫ σ (Fin.castSucc j) = σ j ≫ δ i := by
  ext k : 3
  dsimp [δ, σ]
  rcases le_or_lt k i with (hik | hik)
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr hik)]
    rcases le_or_lt k (j.castSucc) with (hjk | hjk)
    · rw [Fin.predAbove_of_le_castSucc _ _
      (Fin.castSucc_le_castSucc_iff.mpr hjk), Fin.castPred_castSucc,
      Fin.predAbove_of_le_castSucc _ _ hjk, Fin.succAbove_of_castSucc_lt, Fin.castSucc_castPred]
      rw [Fin.castSucc_castPred]
      exact hjk.trans_lt H
    · rw [Fin.predAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hjk),
      Fin.predAbove_of_castSucc_lt _ _ hjk, Fin.succAbove_of_castSucc_lt,
      Fin.castSucc_pred_eq_pred_castSucc]
      rwa [Fin.castSucc_lt_iff_succ_le, Fin.succ_pred]
  · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.succ_le_castSucc_iff.mpr hik)]
    have hjk := H.trans hik
    rw [Fin.predAbove_of_castSucc_lt _ _ hjk, Fin.predAbove_of_castSucc_lt _ _
      (Fin.castSucc_lt_succ_iff.mpr hjk.le),
    Fin.pred_succ, Fin.succAbove_of_le_castSucc, Fin.succ_pred]
    rwa [Fin.le_castSucc_pred_iff]
#align simplex_category.δ_comp_σ_of_gt SimplexCategory.δ_comp_σ_of_gt

@[reassoc]
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    δ i ≫ σ j = σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) ≫
      δ (i.pred fun (hi : i = 0) => by simp only [Fin.not_lt_zero, hi] at H) := by
  rw [← δ_comp_σ_of_gt]
  · simp
  · rw [Fin.castSucc_castLT, ← Fin.succ_lt_succ_iff, Fin.succ_pred]
    exact H
#align simplex_category.δ_comp_σ_of_gt' SimplexCategory.δ_comp_σ_of_gt'

/-- The fifth simplicial identity -/
@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    σ (Fin.castSucc i) ≫ σ j = σ j.succ ≫ σ i := by
  ext k : 3
  dsimp [σ]
  cases' k using Fin.lastCases with k
  · simp only [len_mk, Fin.predAbove_right_last]
  · cases' k using Fin.cases with k
    · rw [Fin.castSucc_zero, Fin.predAbove_of_le_castSucc _ 0 (Fin.zero_le _),
      Fin.predAbove_of_le_castSucc _ _ (Fin.zero_le _), Fin.castPred_zero,
      Fin.predAbove_of_le_castSucc _ 0 (Fin.zero_le _),
      Fin.predAbove_of_le_castSucc _ _ (Fin.zero_le _)]
    · rcases le_or_lt i k with (h | h)
      · simp_rw [Fin.predAbove_of_castSucc_lt i.castSucc _ (Fin.castSucc_lt_castSucc_iff.mpr
        (Fin.castSucc_lt_succ_iff.mpr h)), ← Fin.succ_castSucc, Fin.pred_succ,
        Fin.succ_predAbove_succ]
        rw [Fin.predAbove_of_castSucc_lt i _ (Fin.castSucc_lt_succ_iff.mpr _), Fin.pred_succ]
        rcases le_or_lt k j with (hkj | hkj)
        · rwa [Fin.predAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hkj),
          Fin.castPred_castSucc]
        · rw [Fin.predAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hkj),
          Fin.le_pred_iff,
          Fin.succ_le_castSucc_iff]
          exact H.trans_lt hkj
      · simp_rw [Fin.predAbove_of_le_castSucc i.castSucc _ (Fin.castSucc_le_castSucc_iff.mpr
        (Fin.succ_le_castSucc_iff.mpr h)), Fin.castPred_castSucc, ← Fin.succ_castSucc,
        Fin.succ_predAbove_succ]
        rw [Fin.predAbove_of_le_castSucc _ k.castSucc
        (Fin.castSucc_le_castSucc_iff.mpr (h.le.trans H)),
        Fin.castPred_castSucc, Fin.predAbove_of_le_castSucc _ k.succ
        (Fin.succ_le_castSucc_iff.mpr (H.trans_lt' h)), Fin.predAbove_of_le_castSucc _ k.succ
        (Fin.succ_le_castSucc_iff.mpr h)]
#align simplex_category.σ_comp_σ SimplexCategory.σ_comp_σ

/--
If `f : [m] ⟶ [n+1]` is a morphism and `j` is not in the range of `f`,
then `factor_δ f j` is a morphism `[m] ⟶ [n]` such that
`factor_δ f j ≫ δ j = f` (as witnessed by `factor_δ_spec`).
-/
def factor_δ {m n : ℕ} (f : ([m] : SimplexCategory) ⟶ [n+1]) (j : Fin (n+2)) :
    ([m] : SimplexCategory) ⟶ [n] :=
  f ≫ σ (Fin.predAbove 0 j)

open Fin in
lemma factor_δ_spec {m n : ℕ} (f : ([m] : SimplexCategory) ⟶ [n+1]) (j : Fin (n+2))
    (hj : ∀ (k : Fin (m+1)), f.toOrderHom k ≠ j) :
    factor_δ f j ≫ δ j = f := by
  ext k : 3
  specialize hj k
  dsimp [factor_δ, δ, σ]
  cases' j using cases with j
  · rw [predAbove_of_le_castSucc _ _ (zero_le _), castPred_zero, predAbove_of_castSucc_lt 0 _
    (castSucc_zero ▸ pos_of_ne_zero hj),
    zero_succAbove, succ_pred]
  · rw [predAbove_of_castSucc_lt 0 _ (castSucc_zero ▸ succ_pos _), pred_succ]
    rcases hj.lt_or_lt with (hj | hj)
    · rw [predAbove_of_le_castSucc j _]
      swap
      · exact (le_castSucc_iff.mpr hj)
      · rw [succAbove_of_castSucc_lt]
        swap
        · rwa [castSucc_lt_succ_iff, castPred_le_iff, le_castSucc_iff]
        rw [castSucc_castPred]
    · rw [predAbove_of_castSucc_lt]
      swap
      · exact (castSucc_lt_succ _).trans hj
      rw [succAbove_of_le_castSucc]
      swap
      · rwa [succ_le_castSucc_iff, lt_pred_iff]
      rw [succ_pred]

end Generators

section Skeleton

/-- The functor that exhibits `SimplexCategory` as skeleton
of `NonemptyFinLinOrd` -/
@[simps obj map]
def skeletalFunctor : SimplexCategory ⥤ NonemptyFinLinOrd where
  obj a := NonemptyFinLinOrd.of (Fin (a.len + 1))
  map f := f.toOrderHom
#align simplex_category.skeletal_functor SimplexCategory.skeletalFunctor

theorem skeletalFunctor.coe_map {Δ₁ Δ₂ : SimplexCategory} (f : Δ₁ ⟶ Δ₂) :
    ↑(skeletalFunctor.map f) = f.toOrderHom :=
  rfl
#align simplex_category.skeletal_functor.coe_map SimplexCategory.skeletalFunctor.coe_map

theorem skeletal : Skeletal SimplexCategory := fun X Y ⟨I⟩ => by
  suffices Fintype.card (Fin (X.len + 1)) = Fintype.card (Fin (Y.len + 1)) by
    ext
    simpa
  apply Fintype.card_congr
  exact ((skeletalFunctor ⋙ forget NonemptyFinLinOrd).mapIso I).toEquiv
#align simplex_category.skeletal SimplexCategory.skeletal

namespace SkeletalFunctor

instance : Full skeletalFunctor where
  preimage f := SimplexCategory.Hom.mk f

instance : Faithful skeletalFunctor where
  map_injective {_ _ f g} h := by
    ext1
    exact h

instance : EssSurj skeletalFunctor where
  mem_essImage X :=
    ⟨mk (Fintype.card X - 1 : ℕ),
      ⟨by
        have aux : Fintype.card X = Fintype.card X - 1 + 1 :=
          (Nat.succ_pred_eq_of_pos <| Fintype.card_pos_iff.mpr ⟨⊥⟩).symm
        let f := monoEquivOfFin X aux
        have hf := (Finset.univ.orderEmbOfFin aux).strictMono
        refine'
          { hom := ⟨f, hf.monotone⟩
            inv := ⟨f.symm, _⟩
            hom_inv_id := by ext1; apply f.symm_apply_apply
            inv_hom_id := by ext1; apply f.apply_symm_apply }
        intro i j h
        show f.symm i ≤ f.symm j
        rw [← hf.le_iff_le]
        show f (f.symm i) ≤ f (f.symm j)
        simpa only [OrderIso.apply_symm_apply]⟩⟩

noncomputable instance isEquivalence : IsEquivalence skeletalFunctor :=
  Equivalence.ofFullyFaithfullyEssSurj skeletalFunctor
#align simplex_category.skeletal_functor.is_equivalence SimplexCategory.SkeletalFunctor.isEquivalence

end SkeletalFunctor

/-- The equivalence that exhibits `SimplexCategory` as skeleton
of `NonemptyFinLinOrd` -/
noncomputable def skeletalEquivalence : SimplexCategory ≌ NonemptyFinLinOrd :=
  Functor.asEquivalence skeletalFunctor
#align simplex_category.skeletal_equivalence SimplexCategory.skeletalEquivalence

end Skeleton

/-- `SimplexCategory` is a skeleton of `NonemptyFinLinOrd`.
-/
noncomputable def isSkeletonOf :
    IsSkeletonOf NonemptyFinLinOrd SimplexCategory skeletalFunctor where
  skel := skeletal
  eqv := SkeletalFunctor.isEquivalence
#align simplex_category.is_skeleton_of SimplexCategory.isSkeletonOf

/-- The truncated simplex category. -/
def Truncated (n : ℕ) :=
  FullSubcategory fun a : SimplexCategory => a.len ≤ n
#align simplex_category.truncated SimplexCategory.Truncated

instance (n : ℕ) : SmallCategory.{0} (Truncated n) :=
  FullSubcategory.category _

namespace Truncated

instance {n} : Inhabited (Truncated n) :=
  ⟨⟨[0], by simp⟩⟩

/-- The fully faithful inclusion of the truncated simplex category into the usual
simplex category.
-/
def inclusion {n : ℕ} : SimplexCategory.Truncated n ⥤ SimplexCategory :=
  fullSubcategoryInclusion _
#align simplex_category.truncated.inclusion SimplexCategory.Truncated.inclusion

instance (n : ℕ) : Full (inclusion : Truncated n ⥤ _) := FullSubcategory.full _
instance (n : ℕ) : Faithful (inclusion : Truncated n ⥤ _) := FullSubcategory.faithful _

end Truncated

section Concrete

instance : ConcreteCategory.{0} SimplexCategory where
  forget :=
    { obj := fun i => Fin (i.len + 1)
      map := fun f => f.toOrderHom }
  forget_faithful := ⟨fun h => by ext : 2; exact h⟩

end Concrete

section EpiMono

/-- A morphism in `SimplexCategory` is a monomorphism precisely when it is an injective function
-/
theorem mono_iff_injective {n m : SimplexCategory} {f : n ⟶ m} :
    Mono f ↔ Function.Injective f.toOrderHom := by
  rw [← Functor.mono_map_iff_mono skeletalEquivalence.functor]
  dsimp only [skeletalEquivalence, Functor.asEquivalence_functor]
  simp only [skeletalFunctor_obj, skeletalFunctor_map,
    NonemptyFinLinOrd.mono_iff_injective, NonemptyFinLinOrd.coe_of]
#align simplex_category.mono_iff_injective SimplexCategory.mono_iff_injective

/-- A morphism in `SimplexCategory` is an epimorphism if and only if it is a surjective function
-/
theorem epi_iff_surjective {n m : SimplexCategory} {f : n ⟶ m} :
    Epi f ↔ Function.Surjective f.toOrderHom := by
  rw [← Functor.epi_map_iff_epi skeletalEquivalence.functor]
  dsimp only [skeletalEquivalence, Functor.asEquivalence_functor]
  simp only [skeletalFunctor_obj, skeletalFunctor_map,
    NonemptyFinLinOrd.epi_iff_surjective, NonemptyFinLinOrd.coe_of]
#align simplex_category.epi_iff_surjective SimplexCategory.epi_iff_surjective

/-- A monomorphism in `SimplexCategory` must increase lengths-/
theorem len_le_of_mono {x y : SimplexCategory} {f : x ⟶ y} : Mono f → x.len ≤ y.len := by
  intro hyp_f_mono
  have f_inj : Function.Injective f.toOrderHom.toFun := mono_iff_injective.1 hyp_f_mono
  simpa using Fintype.card_le_of_injective f.toOrderHom.toFun f_inj
#align simplex_category.len_le_of_mono SimplexCategory.len_le_of_mono

theorem le_of_mono {n m : ℕ} {f : ([n] : SimplexCategory) ⟶ [m]} : CategoryTheory.Mono f → n ≤ m :=
  len_le_of_mono
#align simplex_category.le_of_mono SimplexCategory.le_of_mono

/-- An epimorphism in `SimplexCategory` must decrease lengths-/
theorem len_le_of_epi {x y : SimplexCategory} {f : x ⟶ y} : Epi f → y.len ≤ x.len := by
  intro hyp_f_epi
  have f_surj : Function.Surjective f.toOrderHom.toFun := epi_iff_surjective.1 hyp_f_epi
  simpa using Fintype.card_le_of_surjective f.toOrderHom.toFun f_surj
#align simplex_category.len_le_of_epi SimplexCategory.len_le_of_epi

theorem le_of_epi {n m : ℕ} {f : ([n] : SimplexCategory) ⟶ [m]} : Epi f → m ≤ n :=
  len_le_of_epi
#align simplex_category.le_of_epi SimplexCategory.le_of_epi

instance {n : ℕ} {i : Fin (n + 2)} : Mono (δ i) := by
  rw [mono_iff_injective]
  exact Fin.succAbove_right_injective

instance {n : ℕ} {i : Fin (n + 1)} : Epi (σ i) := by
  rw [epi_iff_surjective]
  intro b
  simp only [σ, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk]
  by_cases h : b ≤ i
  · use b
    -- This was not needed before leanprover/lean4#2644
    dsimp
    rw [Fin.predAbove_of_le_castSucc i b (by simpa only [Fin.coe_eq_castSucc] using h)]
    simp only [len_mk, Fin.coe_eq_castSucc, Fin.castPred_castSucc]
  · use b.succ
    -- This was not needed before leanprover/lean4#2644
    dsimp
    rw [Fin.predAbove_of_castSucc_lt i b.succ _, Fin.pred_succ]
    rw [not_le] at h
    rw [Fin.lt_iff_val_lt_val] at h ⊢
    simpa only [Fin.val_succ, Fin.coe_castSucc] using Nat.lt.step h

instance : ReflectsIsomorphisms (forget SimplexCategory) :=
  ⟨fun f hf =>
    IsIso.of_iso
      { hom := f
        inv := Hom.mk
            { toFun := inv ((forget SimplexCategory).map f)
              monotone' := fun y₁ y₂ h => by
                by_cases h' : y₁ < y₂
                · by_contra h''
                  apply not_le.mpr h'
                  convert f.toOrderHom.monotone (le_of_not_ge h'')
                  all_goals
                    exact (congr_hom (Iso.inv_hom_id
                      (asIso ((forget SimplexCategory).map f))) _).symm
                · rw [eq_of_le_of_not_lt h h'] }
        hom_inv_id := by
          ext1
          ext1
          exact Iso.hom_inv_id (asIso ((forget _).map f))
        inv_hom_id := by
          ext1
          ext1
          exact Iso.inv_hom_id (asIso ((forget _).map f)) }⟩

theorem isIso_of_bijective {x y : SimplexCategory} {f : x ⟶ y}
    (hf : Function.Bijective f.toOrderHom.toFun) : IsIso f :=
  haveI : IsIso ((forget SimplexCategory).map f) := (isIso_iff_bijective _).mpr hf
  isIso_of_reflects_iso f (forget SimplexCategory)
#align simplex_category.is_iso_of_bijective SimplexCategory.isIso_of_bijective

/-- An isomorphism in `SimplexCategory` induces an `OrderIso`. -/
@[simp]
def orderIsoOfIso {x y : SimplexCategory} (e : x ≅ y) : Fin (x.len + 1) ≃o Fin (y.len + 1) :=
  Equiv.toOrderIso
    { toFun := e.hom.toOrderHom
      invFun := e.inv.toOrderHom
      left_inv := fun i => by
        simpa only using congr_arg (fun φ => (Hom.toOrderHom φ) i) e.hom_inv_id
      right_inv := fun i => by
        simpa only using congr_arg (fun φ => (Hom.toOrderHom φ) i) e.inv_hom_id }
    e.hom.toOrderHom.monotone e.inv.toOrderHom.monotone
#align simplex_category.order_iso_of_iso SimplexCategory.orderIsoOfIso

theorem iso_eq_iso_refl {x : SimplexCategory} (e : x ≅ x) : e = Iso.refl x := by
  have h : (Finset.univ : Finset (Fin (x.len + 1))).card = x.len + 1 := Finset.card_fin (x.len + 1)
  have eq₁ := Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((orderIsoOfIso e) i)
  have eq₂ :=
    Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((orderIsoOfIso (Iso.refl x)) i)
  -- Porting note: the proof was rewritten from this point in #3414 (reenableeta)
  -- It could be investigated again to see if the original can be restored.
  ext x
  replace eq₁ := congr_arg (· x) eq₁
  replace eq₂ := congr_arg (· x) eq₂.symm
  simp_all
#align simplex_category.iso_eq_iso_refl SimplexCategory.iso_eq_iso_refl

theorem eq_id_of_isIso {x : SimplexCategory} (f : x ⟶ x) [IsIso f] : f = 𝟙 _ :=
  congr_arg (fun φ : _ ≅ _ => φ.hom) (iso_eq_iso_refl (asIso f))
#align simplex_category.eq_id_of_is_iso SimplexCategory.eq_id_of_isIso

theorem eq_σ_comp_of_not_injective' {n : ℕ} {Δ' : SimplexCategory} (θ : mk (n + 1) ⟶ Δ')
    (i : Fin (n + 1)) (hi : θ.toOrderHom (Fin.castSucc i) = θ.toOrderHom i.succ) :
    ∃ θ' : mk n ⟶ Δ', θ = σ i ≫ θ' := by
  use δ i.succ ≫ θ
  ext1; ext1; ext1 x
  simp only [Hom.toOrderHom_mk, Function.comp_apply, OrderHom.comp_coe, Hom.comp,
    smallCategory_comp, σ, mkHom, OrderHom.coe_mk]
  by_cases h' : x ≤ Fin.castSucc i
  · -- This was not needed before leanprover/lean4#2644
    dsimp
    rw [Fin.predAbove_of_le_castSucc i x h']
    dsimp [δ]
    erw [Fin.succAbove_of_castSucc_lt _ _ _]
    · rw [Fin.castSucc_castPred]
    · exact (Fin.castSucc_lt_succ_iff.mpr h')
  · simp only [not_le] at h'
    let y := x.pred <| by rintro (rfl : x = 0); simp at h'
    have hy : x = y.succ := (Fin.succ_pred x _).symm
    rw [hy] at h' ⊢
    -- This was not needed before leanprover/lean4#2644
    conv_rhs => dsimp
    rw [Fin.predAbove_of_castSucc_lt i y.succ h', Fin.pred_succ]
    by_cases h'' : y = i
    · rw [h'']
      refine hi.symm.trans ?_
      congr 1
      dsimp [δ]
      erw [Fin.succAbove_of_castSucc_lt i.succ]
      exact Fin.lt_succ
    · dsimp [δ]
      erw [Fin.succAbove_of_le_castSucc i.succ _]
      simp only [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc,
        Nat.lt_succ_iff, Fin.ext_iff] at h' h'' ⊢
      cases' Nat.le.dest h' with c hc
      cases c
      · exfalso
        simp only [Nat.zero_eq, add_zero, len_mk, Fin.coe_pred, ge_iff_le] at hc
        rw [hc] at h''
        exact h'' rfl
      · rw [← hc]
        simp only [add_le_add_iff_left, Nat.succ_eq_add_one, le_add_iff_nonneg_left, zero_le]
#align simplex_category.eq_σ_comp_of_not_injective' SimplexCategory.eq_σ_comp_of_not_injective'

theorem eq_σ_comp_of_not_injective {n : ℕ} {Δ' : SimplexCategory} (θ : mk (n + 1) ⟶ Δ')
    (hθ : ¬Function.Injective θ.toOrderHom) :
    ∃ (i : Fin (n + 1)) (θ' : mk n ⟶ Δ'), θ = σ i ≫ θ' := by
  simp only [Function.Injective, exists_prop, not_forall] at hθ
  -- as θ is not injective, there exists `x<y` such that `θ x = θ y`
  -- and then, `θ x = θ (x+1)`
  have hθ₂ : ∃ x y : Fin (n + 2), (Hom.toOrderHom θ) x = (Hom.toOrderHom θ) y ∧ x < y := by
    rcases hθ with ⟨x, y, ⟨h₁, h₂⟩⟩
    by_cases h : x < y
    · exact ⟨x, y, ⟨h₁, h⟩⟩
    · refine' ⟨y, x, ⟨h₁.symm, _⟩⟩
      rcases lt_or_eq_of_le (not_lt.mp h) with h' | h'
      · exact h'
      · exfalso
        exact h₂ h'.symm
  rcases hθ₂ with ⟨x, y, ⟨h₁, h₂⟩⟩
  use x.castPred ((Fin.le_last _).trans_lt' h₂).ne
  apply eq_σ_comp_of_not_injective'
  apply le_antisymm
  · exact θ.toOrderHom.monotone (le_of_lt (Fin.castSucc_lt_succ _))
  · rw [Fin.castSucc_castPred, h₁]
    exact θ.toOrderHom.monotone ((Fin.succ_castPred_le_iff _).mpr h₂)
#align simplex_category.eq_σ_comp_of_not_injective SimplexCategory.eq_σ_comp_of_not_injective

theorem eq_comp_δ_of_not_surjective' {n : ℕ} {Δ : SimplexCategory} (θ : Δ ⟶ mk (n + 1))
    (i : Fin (n + 2)) (hi : ∀ x, θ.toOrderHom x ≠ i) : ∃ θ' : Δ ⟶ mk n, θ = θ' ≫ δ i := by
  by_cases h : i < Fin.last (n + 1)
  · use θ ≫ σ (Fin.castPred i h.ne)
    ext1
    ext1
    ext1 x
    simp only [Hom.toOrderHom_mk, Function.comp_apply, OrderHom.comp_coe, Hom.comp,
      smallCategory_comp]
    by_cases h' : θ.toOrderHom x ≤ i
    · simp only [σ, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk]
      -- This was not needed before leanprover/lean4#2644
      dsimp
      -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
      erw [Fin.predAbove_of_le_castSucc _ _ (by rwa [Fin.castSucc_castPred])]
      dsimp [δ]
      erw [Fin.succAbove_of_castSucc_lt i]
      · rw [Fin.castSucc_castPred]
      · rw [(hi x).le_iff_lt] at h'
        exact h'
    · simp only [not_le] at h'
      -- The next three tactics used to be a simp only call before leanprover/lean4#2644
      rw [σ, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk, OrderHom.coe_mk]
      erw [OrderHom.coe_mk]
      erw [Fin.predAbove_of_castSucc_lt _ _ (by rwa [Fin.castSucc_castPred])]
      dsimp [δ]
      rw [Fin.succAbove_of_le_castSucc i _]
      -- This was not needed before leanprover/lean4#2644
      conv_rhs => dsimp
      erw [Fin.succ_pred]
      simpa only [Fin.le_iff_val_le_val, Fin.coe_castSucc, Fin.coe_pred] using
        Nat.le_sub_one_of_lt (Fin.lt_iff_val_lt_val.mp h')
  · obtain rfl := le_antisymm (Fin.le_last i) (not_lt.mp h)
    use θ ≫ σ (Fin.last _)
    ext x : 3
    dsimp [δ, σ]
    simp_rw [Fin.succAbove_last, Fin.predAbove_last_apply]
    erw [dif_neg (hi x)]
    rw [Fin.castSucc_castPred]
#align simplex_category.eq_comp_δ_of_not_surjective' SimplexCategory.eq_comp_δ_of_not_surjective'

theorem eq_comp_δ_of_not_surjective {n : ℕ} {Δ : SimplexCategory} (θ : Δ ⟶ mk (n + 1))
    (hθ : ¬Function.Surjective θ.toOrderHom) :
    ∃ (i : Fin (n + 2)) (θ' : Δ ⟶ mk n), θ = θ' ≫ δ i := by
  cases' not_forall.mp hθ with i hi
  use i
  exact eq_comp_δ_of_not_surjective' θ i (not_exists.mp hi)
#align simplex_category.eq_comp_δ_of_not_surjective SimplexCategory.eq_comp_δ_of_not_surjective

theorem eq_id_of_mono {x : SimplexCategory} (i : x ⟶ x) [Mono i] : i = 𝟙 _ := by
  suffices IsIso i by
    apply eq_id_of_isIso
  apply isIso_of_bijective
  dsimp
  rw [Fintype.bijective_iff_injective_and_card i.toOrderHom, ← mono_iff_injective,
    eq_self_iff_true, and_true_iff]
  infer_instance
#align simplex_category.eq_id_of_mono SimplexCategory.eq_id_of_mono

theorem eq_id_of_epi {x : SimplexCategory} (i : x ⟶ x) [Epi i] : i = 𝟙 _ := by
  suffices IsIso i by
    haveI := this
    apply eq_id_of_isIso
  apply isIso_of_bijective
  dsimp
  rw [Fintype.bijective_iff_surjective_and_card i.toOrderHom, ← epi_iff_surjective,
    eq_self_iff_true, and_true_iff]
  infer_instance
#align simplex_category.eq_id_of_epi SimplexCategory.eq_id_of_epi

theorem eq_σ_of_epi {n : ℕ} (θ : mk (n + 1) ⟶ mk n) [Epi θ] : ∃ i : Fin (n + 1), θ = σ i := by
  rcases eq_σ_comp_of_not_injective θ (by
    by_contra h
    simpa using le_of_mono (mono_iff_injective.mpr h)) with ⟨i, θ', h⟩
  use i
  haveI : Epi (σ i ≫ θ') := by
    rw [← h]
    infer_instance
  haveI := CategoryTheory.epi_of_epi (σ i) θ'
  rw [h, eq_id_of_epi θ', Category.comp_id]
#align simplex_category.eq_σ_of_epi SimplexCategory.eq_σ_of_epi

theorem eq_δ_of_mono {n : ℕ} (θ : mk n ⟶ mk (n + 1)) [Mono θ] : ∃ i : Fin (n + 2), θ = δ i := by
  rcases eq_comp_δ_of_not_surjective θ (by
    by_contra h
    simpa using le_of_epi (epi_iff_surjective.mpr h)) with ⟨i, θ', h⟩
  use i
  haveI : Mono (θ' ≫ δ i) := by
    rw [← h]
    infer_instance
  haveI := CategoryTheory.mono_of_mono θ' (δ i)
  rw [h, eq_id_of_mono θ', Category.id_comp]
#align simplex_category.eq_δ_of_mono SimplexCategory.eq_δ_of_mono

theorem len_lt_of_mono {Δ' Δ : SimplexCategory} (i : Δ' ⟶ Δ) [hi : Mono i] (hi' : Δ ≠ Δ') :
    Δ'.len < Δ.len := by
  rcases lt_or_eq_of_le (len_le_of_mono hi) with (h | h)
  · exact h
  · exfalso
    exact hi' (by ext; exact h.symm)
#align simplex_category.len_lt_of_mono SimplexCategory.len_lt_of_mono

noncomputable instance : SplitEpiCategory SimplexCategory :=
  skeletalEquivalence.inverse.splitEpiCategoryImpOfIsEquivalence

instance : HasStrongEpiMonoFactorisations SimplexCategory :=
  Functor.hasStrongEpiMonoFactorisations_imp_of_isEquivalence
    SimplexCategory.skeletalEquivalence.inverse

instance : HasStrongEpiImages SimplexCategory :=
  Limits.hasStrongEpiImages_of_hasStrongEpiMonoFactorisations

instance (Δ Δ' : SimplexCategory) (θ : Δ ⟶ Δ') : Epi (factorThruImage θ) :=
  StrongEpi.epi

theorem image_eq {Δ Δ' Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ Δ'} [Epi e] {i : Δ' ⟶ Δ''}
    [Mono i] (fac : e ≫ i = φ) : image φ = Δ' := by
  haveI := strongEpi_of_epi e
  let e := image.isoStrongEpiMono e i fac
  ext
  exact
    le_antisymm (len_le_of_epi (inferInstance : Epi e.hom))
      (len_le_of_mono (inferInstance : Mono e.hom))
#align simplex_category.image_eq SimplexCategory.image_eq

theorem image_ι_eq {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
    {i : image φ ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) : image.ι φ = i := by
  haveI := strongEpi_of_epi e
  rw [← image.isoStrongEpiMono_hom_comp_ι e i fac,
    SimplexCategory.eq_id_of_isIso (image.isoStrongEpiMono e i fac).hom, Category.id_comp]
#align simplex_category.image_ι_eq SimplexCategory.image_ι_eq

theorem factorThruImage_eq {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
    {i : image φ ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) : factorThruImage φ = e := by
  rw [← cancel_mono i, fac, ← image_ι_eq fac, image.fac]
#align simplex_category.factor_thru_image_eq SimplexCategory.factorThruImage_eq

end EpiMono

namespace WithInitial
open WithInitial

def len (X : WithInitial SimplexCategory) : ℕ :=
  match X with
  | star => 0
  | of x => Nat.succ x.len

def mk (i : ℕ) : WithInitial SimplexCategory :=
  match i with
  | Nat.zero => star
  | Nat.succ x => of (SimplexCategory.mk x)

lemma len_mk (i : ℕ) : len (mk i) = i := by
  match i with
  | Nat.zero => rfl
  | Nat.succ x => rfl

def toOrderHom {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) : Fin (len X) →o Fin (len Y) :=
  match X, Y, f with
  | of _, of _, f => f.toOrderHom
  | star, of x, _ => (OrderEmbedding.ofIsEmpty.toOrderHom :  (Fin 0) →o (Fin (len (of x))))
  | star, star, _ => OrderHom.id

lemma toOrderHom_id {Z : WithInitial SimplexCategory} : toOrderHom (𝟙 Z) = OrderHom.id := by
  match Z with
  | of z => rfl
  | star => rfl

lemma toOrderHom_comp {X Y Z: WithInitial SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z):
    toOrderHom (f ≫ g) = (toOrderHom g).comp (toOrderHom f) := by
  match X, Y, Z, f, g with
  | star, star, star, f, g => rfl
  | star, star, of z, f, g => rfl
  | star, of y, of z, f, g =>
    apply OrderHom.ext
    exact List.ofFn_inj.mp rfl
  | of x, of y, of z, f, g => rfl

def homMk {n m : ℕ} (f : Fin n →o Fin m) : mk n ⟶ mk m :=
  match n, m, f with
  | Nat.zero, Nat.zero, _ => 𝟙 star
  | Nat.zero, Nat.succ m', _ => starInitial.to (mk (Nat.succ m'))
  | Nat.succ _, Nat.succ _, f => SimplexCategory.Hom.mk f
  | Nat.succ _, Nat.zero, f =>  Fin.elim0 (f 0)

lemma homMk_id {n  : ℕ}: homMk (OrderHom.id ) = 𝟙 (mk n) :=
  match n with
  | Nat.zero => rfl
  | Nat.succ _ => rfl

lemma homMk_comp {n m r : ℕ} (f : Fin n →o Fin m) (g : Fin m →o Fin r) :
    (homMk f) ≫ (homMk g) = homMk (g.comp f) := by
  match n, m, r, f, g with
  | Nat.zero, Nat.zero, Nat.zero, f, g => rfl
  | Nat.zero, Nat.zero, Nat.succ _, f, g => rfl
  | Nat.zero, Nat.succ _, Nat.succ _, f, g => rfl
  | Nat.succ _, Nat.succ _, Nat.succ _, f, g => rfl
  | Nat.zero, Nat.succ _, Nat.zero, f, g => rfl
  | Nat.succ _, Nat.zero, Nat.zero, f, g => exact Fin.elim0 (f 0)
  | Nat.succ _, Nat.succ _, Nat.zero, f, g => exact Fin.elim0 (g 0)
  | Nat.succ _, Nat.zero, Nat.succ _, f, g => exact Fin.elim0 (f 0)

def rev : WithInitial SimplexCategory ⥤ WithInitial SimplexCategory where
  obj := fun X => X
  map {X Y} f :=
     match X, Y, f with
     | of _, of _, f =>
       homMk {
        toFun := fun a => (f.toOrderHom a.rev).rev
        monotone' := by
          let hf := f.toOrderHom.monotone'
          aesop_cat
       }
     | star, of y, _ => starInitial.to (of y)
     | star, star, _ => 𝟙 star
  map_id := by
    intro Z
    match Z with
    | star => rfl
    | of z =>
      simp [homMk_id, homMk]
      change _= Hom.mk (OrderHom.id)
      apply congrArg
      apply OrderHom.ext
      funext a
      change  (a).rev.rev =a
      exact Fin.rev_rev a
  map_comp := by
    intro X Y Z f g
    match X, Y, Z, f, g with
    | star, star, star, f, g => rfl
    | star, star, of z, f, g => rfl
    | star, of y, of z, f, g => rfl
    | of x, of y, of z, f, g =>
      simp
      rw [homMk_comp]
      apply congrArg
      apply OrderHom.ext
      funext a
      simp
      rw [show Hom.toOrderHom (f ≫ g) = (Hom.toOrderHom g).comp (Hom.toOrderHom f) by rfl]
      rfl

lemma rev_castIso {n m : ℕ} (h : n = m ) : homMk (Fin.castIso h : Fin n →o Fin m) =
    rev.map (homMk (Fin.castIso h : Fin n →o Fin m)) := by
  match n, m with
  | Nat.zero, Nat.zero => rfl
  | Nat.succ n, Nat.succ m =>
     simp [homMk]
     unfold rev mk homMk
     simp
     apply congrArg
     apply OrderHom.ext
     funext a
     change _ = Fin.rev (Fin.cast h (Fin.rev a))
     rw [Fin.eq_iff_veq]
     have h2 : n=m :=  Nat.succ_inj.mp h
     simp [← h2]
     rw [tsub_tsub_cancel_of_le a.is_le]

lemma rev_toOrderHom {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) (a : Fin (len X)):
    toOrderHom (rev.map f) a  = ((toOrderHom f) a.rev).rev := by
  match X, Y, f with
  | of _, of _, f => rfl
  | star, of y, _ => exact Fin.elim0 a
  | star, star, _ => exact Fin.elim0 a

@[simp]
def nat {n : ℕ} (k : Option (Fin (n))) : Fin (Nat.succ (n)) :=
  match k with
  | some k => k.castSucc
  | none => Fin.last n

lemma nat_true {n : ℕ} :
    nat (Fin.find (fun (_ : Fin n) => True)) = 0 := by
  match n with
  | Nat.zero => rfl
  | Nat.succ n =>
    have h : Fin.find (fun (_ : Fin (Nat.succ n)) => True) = some (0 : Fin (Nat.succ n)) := by
      rw [Fin.find_eq_some_iff]
      simp
    rw [h]
    rfl

lemma nat_rev {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
  (hp : (i : Fin n) → (j : Fin n) → i ≤ j → p i → p j)
  : (nat (Fin.find p)).rev =
    (nat (Fin.find (fun (a : Fin n) => ¬ p a.rev ))) := by
  let k := Fin.find p
  have  hk : Fin.find p = k := rfl
  rw [hk]
  match k with
  | none =>
     rw [Fin.find_eq_none_iff] at hk
     simp [hk]
     change _ = nat (Fin.find (fun (_ : Fin n) => True))
     rw [nat_true]
  | some k =>
    rw [Fin.find_eq_some_iff] at hk
    match k with
    | ⟨ Nat.zero, hx ⟩ =>
      have h :  (Fin.find fun a => ¬p (Fin.rev a)) = none := by
        rw [Fin.find_eq_none_iff]
        intro i
        simp
        refine hp ⟨ Nat.zero, hx ⟩ (Fin.rev i) ?_ hk.left
        rw [Fin.le_def]
        exact Nat.zero_le ↑(Fin.rev i)
      rw [h]
      simp [nat]
    | ⟨Nat.succ k, hx⟩ =>
      change  (⟨Nat.succ k, hx⟩ : Fin n).castSucc.rev =_
      let xn : Fin n :=  ⟨k, Nat.lt_of_succ_lt hx ⟩
      have h : (Fin.find fun a => ¬p (Fin.rev a)) = some xn.rev := by
        rw [Fin.find_eq_some_iff]
        simp
        apply And.intro
        by_contra hn
        exact Nat.not_succ_le_self k (hk.right xn hn)
        intro j hj
        rw [← Fin.rev_rev j, Fin.rev_le_rev]
        have hl := (hp ⟨Nat.succ k, hx⟩ (Fin.rev j)).mt
        simp  at hl
        exact Fin.succ_le_succ_iff.mp (hl hk.left hj)
      rw [h]
      ext
      simp only [Fin.castSucc_mk, Fin.val_rev, Nat.succ_sub_succ_eq_sub, nat, Fin.coe_castSucc]



def preimageInitialSegmentObj {X Y : WithInitial SimplexCategory} (f : X ⟶ Y)
    (i : Fin (Nat.succ (len Y))) : Option (Fin (len X)) :=
  Fin.find (fun a => i ≤ (toOrderHom f a).castSucc)

lemma fin_eq_to_val {n : ℕ} {i j : Fin n}  (h : i = j) : i.val = j.val := by rw [h]

lemma fin_eq_to_rev {n : ℕ} {i j : Fin n}  (h : i = j) : i.rev.val = j.rev.val := by rw [h]

lemma nat_id {Z : WithInitial SimplexCategory} (i : Fin (Nat.succ (len Z)))
    (k : Option (Fin (len Z))) (hk : k = (preimageInitialSegmentObj (𝟙 Z) i)) :
    nat k = i := by
  symm at hk
  simp [preimageInitialSegmentObj,toOrderHom_id] at hk
  match k with
  | some x =>
    rw [Fin.find_eq_some_iff] at hk
    let hkr := hk.right ⟨i, Nat.lt_of_le_of_lt hk.left x.prop ⟩
    simp at hkr
    simp [Fin.eq_iff_veq]
    exact Nat.le_antisymm hkr hk.left
  | none =>
    rw [Fin.find_eq_none_iff] at hk
    simp only [nat, add_right_eq_self]
    match Z with
    | star =>
      ext
      simp_all only [Fin.coe_fin_one]
    | of z =>
      have h1 := hk (Fin.last (z.len))
      ext
      simp  [Fin.lt_def] at h1
      exact Nat.le_antisymm h1 (Fin.is_le i)

lemma nat_id_val {Z : WithInitial SimplexCategory} (i : Fin (Nat.succ (len Z)))
    (k : Option (Fin (len Z))) (hk : k = (preimageInitialSegmentObj (𝟙 Z) i)) :
    (nat k).val = i.val := by
  rw [nat_id i k hk]



lemma preimageInitialSegmentObj_rev {X Y : WithInitial SimplexCategory} (f : X ⟶ Y)
    (i : Fin (Nat.succ (len Y))) :
    preimageInitialSegmentObj (rev.map f) i.rev
    = Fin.find (fun a => ¬ i ≤ (toOrderHom f a.rev).castSucc) := by
  let p  (a : Fin (len X)) := Fin.rev i ≤ Fin.castSucc ((toOrderHom (rev.toPrefunctor.map f)) a)
  let q (a : Fin (len X)) := ¬ i ≤ (toOrderHom f a.rev).castSucc
  have h : p = q := by
    funext a
    simp [toOrderHom, rev, homMk]
    match X, Y, f with
    | of _, of _, f =>
      change i.rev ≤ Fin.castSucc (Fin.rev ((Hom.toOrderHom f) (Fin.rev a))) ↔ _
      rw [← Fin.rev_succ, Fin.rev_le_rev]
      rfl
    | star, of y, _ => exact Fin.elim0 a
    | star, star, _ => exact Fin.elim0 a
  change Fin.find p =Fin.find q
  simp only [h, ge_iff_le]

lemma preimageInitialSegmentObj_neg_negRev  {X Y : WithInitial SimplexCategory} (f : X ⟶ Y)
    (i : Fin (Nat.succ (len Y))) : (nat (preimageInitialSegmentObj f i)).rev =
    (nat (preimageInitialSegmentObj (rev.map f) i.rev)) := by
  rw [preimageInitialSegmentObj_rev]
  let p : Fin (len X) → Prop := (fun a => i ≤ (toOrderHom f a).castSucc)
  change (nat (Fin.find p)).rev= nat ((Fin.find (fun (a : Fin (len X)) => ¬ p a.rev )))
  refine nat_rev p ?_
  intro m n h hm
  exact hm.trans ((toOrderHom f).monotone' h)

lemma preimageInitialSegmentObj_neg_negRev_val  {X Y : WithInitial SimplexCategory} (f : X ⟶ Y)
    (i : Fin (Nat.succ (len Y))) : (nat (preimageInitialSegmentObj f i)).rev.val =
    (nat (preimageInitialSegmentObj (rev.map f) i.rev)).val := by
  have h := preimageInitialSegmentObj_neg_negRev f i
  rw [Fin.eq_iff_veq] at h
  exact h
/-- This lemma is essentially pasting of pullbacks. -/
lemma preimageInitialSegmentObj_comp  {X Y Z: WithInitial SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : Fin (Nat.succ (len Z)))  (k : Option (Fin (len Y))) (hk : k = (preimageInitialSegmentObj g i)) :
   preimageInitialSegmentObj f (nat k) = preimageInitialSegmentObj (f ≫ g) i := by
  symm at hk
  simp [preimageInitialSegmentObj,toOrderHom_id] at hk
  match k with
  | some x =>
    rw [Fin.find_eq_some_iff] at hk
    simp [preimageInitialSegmentObj, toOrderHom_comp]
    let k2 := (Fin.find fun a ↦ x ≤ (toOrderHom f) a)
    have hk2 : (Fin.find fun a ↦ x ≤ (toOrderHom f) a) =k2  := rfl
    rw [hk2]
    match k2 with
    | some x2 =>
      symm
      rw [Fin.find_eq_some_iff]
      rw [Fin.find_eq_some_iff] at hk2
      apply And.intro
      · exact hk.left.trans ((toOrderHom g).monotone' hk2.left )
      · intro j hj
        exact hk2.right j (hk.right ((toOrderHom f) j) hj)
    | none =>
      symm
      rw [Fin.find_eq_none_iff]
      rw [Fin.find_eq_none_iff] at hk2
      intro j
      simp
      by_contra hn
      simp at hn
      exact hk2 j (hk.right ((toOrderHom f) j) hn )
  | none =>
    rw [Fin.find_eq_none_iff] at hk
    have h1 : preimageInitialSegmentObj (f ≫ g) i = none := by
      simp [preimageInitialSegmentObj]
      rw [Fin.find_eq_none_iff, toOrderHom_comp]
      exact fun i ↦ hk ((toOrderHom f) i)
    rw [h1]
    simp [preimageInitialSegmentObj]
    rw [Fin.find_eq_none_iff]
    intro i
    intro a
    have  := Fin.castSucc_lt_last ((toOrderHom f) i)
    simp_all  [lt_self_iff_false]

lemma nat_comp  {X Y Z: WithInitial SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : Fin (Nat.succ (len Z)))  :
    nat (preimageInitialSegmentObj f (nat (preimageInitialSegmentObj g i)))
    = nat (preimageInitialSegmentObj (f ≫ g) i) := by
  apply congrArg

  exact preimageInitialSegmentObj_comp f g i (preimageInitialSegmentObj g i) (by rfl)


def map₀ {X : WithInitial SimplexCategory} (k : Option (Fin (len X))) :
    Fin (nat k).val →o Fin (len X) := Fin.castLEEmb (Fin.is_le (nat k))

lemma LEcond₂ {X Y : WithInitial SimplexCategory} {f : X ⟶ Y} {i : Fin (Nat.succ (len Y))} (k : Option (Fin (len X)))
    (hk : k = (preimageInitialSegmentObj f i)) (a : Fin (nat k)) :
    (toOrderHom f).comp (map₀ k) a < i.val :=
  match k with
  | some x =>
    Nat.not_le.mp (((Fin.find_eq_some_iff.mp hk.symm).right
      (((map₀ (some x)) a))).mt (Fin.not_le.mpr a.prop))
  | none =>
    Nat.not_le.mp (Fin.find_eq_none_iff.mp hk.symm a)

def map₁ {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) (i :  Fin (Nat.succ (len Y))) :
    mk (nat (preimageInitialSegmentObj f i)).val ⟶ mk i.val :=
  homMk {
    toFun := fun a => ⟨(toOrderHom f).comp (map₀ (preimageInitialSegmentObj f i)) a,
      LEcond₂ (preimageInitialSegmentObj f i) (by rfl) a⟩
    monotone' := by
      intro a b h
      apply (toOrderHom f).monotone'
      apply (map₀ (preimageInitialSegmentObj f i)).monotone'
      exact h
  }

def revMap₁ {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) (i :  Fin (Nat.succ (len Y))) :
    mk (nat (preimageInitialSegmentObj f i)).rev.val ⟶ mk i.rev.val :=
  rev.map ((homMk (Fin.castIso (preimageInitialSegmentObj_neg_negRev_val f i))) ≫
     (map₁ (rev.map f) i.rev))

lemma map₁_comp {X Y Z: WithInitial SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : Fin (Nat.succ (len Z)))  :
    map₁ (f ≫ g) i
    = (homMk (Fin.castIso (fin_eq_to_val (nat_comp f g i)).symm)) ≫
        map₁ f (nat (preimageInitialSegmentObj g i)) ≫ map₁ g i
      := by
  match X, Y, Z, f, g with
  | star, star, star, f, g => rfl
  | star, star, of z, f, g => rfl
  | star, of y, of z, f, g => rfl
  | of x, of y, of z, f, g =>
     simp [map₁]
     rw [homMk_comp, homMk_comp]
     rfl

lemma revMap₁_comp {X Y Z: WithInitial SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : Fin (Nat.succ (len Z)))  :
    revMap₁ (f ≫ g) i
    = (homMk (Fin.castIso (fin_eq_to_rev (nat_comp f g i)).symm)) ≫
        revMap₁ f (nat (preimageInitialSegmentObj g i)) ≫ revMap₁ g i
      := by
  match X, Y, Z, f, g with
  | star, star, star, f, g => rfl
  | star, star, of z, f, g => rfl
  | star, of y, of z, f, g => rfl
  | of x, of y, of z, f, g =>
     rw [rev_castIso]
     simp [revMap₁]
     repeat rw [← rev.map_comp]
     apply congrArg
     simp [map₁]
     repeat rw [homMk_comp]
     rfl

lemma map₁_id {Z : WithInitial SimplexCategory} (i  : Fin (Nat.succ (len Z))) :
    (homMk (Fin.castIso (fin_eq_to_val (nat_id i (preimageInitialSegmentObj (𝟙 Z) i) (by rfl))).symm)) ≫ (map₁ (𝟙 Z) i) =
    𝟙 (mk i.val)  := by
  simp [map₁]
  rw [homMk_comp,←  homMk_id]
  match Z with
  | star => rfl
  | of z => rfl

lemma revMap₁_id {Z : WithInitial SimplexCategory} (i  : Fin (Nat.succ (len Z))) :
    (homMk (Fin.castIso (fin_eq_to_rev (nat_id i (preimageInitialSegmentObj (𝟙 Z) i) (by rfl))).symm)) ≫ (revMap₁ (𝟙 Z) i) =
    𝟙 (mk i.rev.val)  := by
  rw [rev_castIso]
  simp [revMap₁]
  repeat rw [← rev.map_comp]
  change _ = 𝟙 (rev.obj ((mk i.rev.val)))
  rw [← rev.map_id (mk i.rev.val)]
  apply congrArg
  simp [map₁]
  repeat rw [homMk_comp]
  rw [← homMk_id]
  match Z with
  | star => rfl
  | of x => rfl



lemma preimageInitialSegmentObj_eq_val { X Y: WithInitial SimplexCategory} ( f g : X ⟶ Y) (h : f=g)
    (i: Fin (Nat.succ (len Y))):
    (nat (preimageInitialSegmentObj f i)).val = (nat (preimageInitialSegmentObj g i)).val := by
  rw [h]

lemma map₁_eq { X Y: WithInitial SimplexCategory} ( f g : X ⟶ Y) (h : f=g) (i : ℕ) :
    map₁ f i = (homMk (Fin.castIso (preimageInitialSegmentObj_eq_val f g h i))) ≫ (map₁ g i)  := by
  match X, Y, f, g with
  | star, star, f, _ => rfl
  | star, of y, f, _=> rfl
  | of x, of y, f, g =>
    simp only [nat, Fin.val_nat_cast, map₁, OrderHom.comp_coe, Function.comp_apply]
    rw [homMk_comp]
    simp only [nat, Fin.val_nat_cast, h, map₀, OrderHomClass.coe_coe]
    rfl

end WithInitial

/-- This functor `SimplexCategory ⥤ Cat` sends `[n]` (for `n : ℕ`)
to the category attached to the ordered set `{0, 1, ..., n}` -/
@[simps! obj map]
def toCat : SimplexCategory ⥤ Cat.{0} :=
  SimplexCategory.skeletalFunctor ⋙ forget₂ NonemptyFinLinOrd LinOrd ⋙
      forget₂ LinOrd Lat ⋙ forget₂ Lat PartOrd ⋙
      forget₂ PartOrd Preord ⋙ preordToCat
set_option linter.uppercaseLean3 false in
#align simplex_category.to_Cat SimplexCategory.toCat

end SimplexCategory
