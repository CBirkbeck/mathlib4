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

namespace Join

@[simp]
def obj (X Y : SimplexCategory) : SimplexCategory := [X.len+Y.len+1]

def cond₁ (X Y : SimplexCategory) (a : Fin (X.len+1)): a.val < X.len + Y.len +1 + 1 := by
    have h2 : len X + len Y + 1 + 1 = len Y + 1 + (len X +1) := by
            rw [add_comm (len X) _, add_assoc (len Y) _ _, add_comm (len X) _]
            rw [add_assoc, add_assoc, add_comm (len X)]
            repeat rw [add_assoc]
    simp [h2]
    exact Nat.lt_add_left (len Y + 1) a.prop

def cond₂ (X Y : SimplexCategory) (a : Fin (Y.len+1)): a.val + X.len +1 < X.len + Y.len +1 + 1 := by
    have h2 : len X + len Y + 1 + 1 = len Y + 1 + (len X +1) := by
            rw [add_comm (len X) _, add_assoc (len Y) _ _, add_comm (len X) _]
            rw [add_assoc, add_assoc, add_comm (len X)]
            repeat rw [add_assoc]
    simp [h2]
    exact Nat.add_succ_lt_add a.prop Nat.le.refl

def cond₃ (X Y : SimplexCategory) (a : Fin (X.len+Y.len+1+1)): a.val - (X.len +1) < Y.len +1 := by
    have h1 := a.prop
    simp only [obj, len_mk] at h1
    have h2 : len X + len Y + 1 + 1 = len Y + 1 + (len X +1) := by
        rw [add_comm (len X) _, add_assoc (len Y) _ _, add_comm (len X) _]
        rw [add_assoc, add_assoc, add_comm (len X)]
        repeat rw [add_assoc]
    simp [h2] at h1
    by_cases h: a.val < X.len+1
    rw [Nat.lt_iff_add_one_le]
    simp_all only [add_le_add_iff_right, tsub_le_iff_right]
    exact _root_.le_add_left h.le
    exact (tsub_lt_iff_right (Nat.not_lt.mp h)).mpr h1

@[simp]
def map {X1 Y1 X2 Y2: SimplexCategory} (η : X1 ⟶ X2) (ε : Y1 ⟶ Y2) : obj X1 Y1 ⟶ obj X2 Y2 :=
  Hom.mk {
    toFun := fun a =>
      if h : a.val <  X1.len+1 then
        ⟨(η.toOrderHom ⟨a.val, h⟩).val, cond₁ X2 Y2 (η.toOrderHom ⟨a.val, h⟩)⟩
      else
        ⟨ε.toOrderHom ⟨a.val - (X1.len+1), cond₃ X1 Y1 a⟩ + (X2.len + 1),
         cond₂ X2 Y2 (ε.toOrderHom ⟨a.val - (X1.len+1), cond₃ X1 Y1 a⟩)⟩
    monotone' := by
      intro a b h
      simp only [obj, len_mk]
      split_ifs <;> rename_i ha hb
      · exact η.toOrderHom.monotone h
      · exact le_add_left (η.toOrderHom ⟨a.val, ha⟩).prop.le
      · exact (Nat.not_le.mpr hb ((Nat.not_lt.mp ha).trans h)).elim
      · rw [Fin.le_def]
        simp only [add_le_add_iff_right, Fin.val_fin_le]
        exact ε.toOrderHom.monotone' (Nat.sub_le_sub_right h (len X1 + 1))
  }


def func : SimplexCategory × SimplexCategory ⥤ SimplexCategory where
  obj X := obj X.1 X.2
  map η := map η.1 η.2
  map_id X := by
    simp
    apply congrArg
    apply OrderHom.ext
    funext a
    dsimp only [obj, len_mk, OrderHom.coe_mk, prod_id_snd, smallCategory_id, Hom.id,
      Hom.toOrderHom_mk, OrderHom.id_coe, id_eq]
    split_ifs with h
    rfl
    rw [Fin.eq_iff_veq]
    simp
    simp at h
    exact Nat.sub_add_cancel h
  map_comp {X Y Z} f g := by
    simp
    apply congrArg
    apply OrderHom.ext
    funext a
    dsimp
    split_ifs with h1 h2
    rfl
    simp only [Fin.is_lt, not_true_eq_false] at h2
    rename_i h2
    simp only [add_lt_iff_neg_right, not_lt_zero'] at h2
    simp only [add_tsub_cancel_right, Fin.eta]

def incl₁ (X Y : SimplexCategory) : X ⟶ Join.func.obj (X, Y) :=
   Hom.mk {
    toFun := fun a => ⟨a.val, cond₁ X Y a⟩
    monotone' := by
      intro a b h
      exact h
   }

def incl₂ (X Y : SimplexCategory) : Y ⟶ Join.func.obj (X, Y) :=
   Hom.mk {
    toFun := fun a => ⟨a.val + X.len + 1, cond₂ X Y a ⟩
    monotone' := by
      intro a b h
      simp only [Fin.mk_le_mk, add_le_add_iff_right, Fin.val_fin_le]
      exact h
   }

lemma incl₁_map {X Y : SimplexCategory × SimplexCategory} ( η : X⟶ Y) :
    incl₁ X.1 X.2 ≫ Join.func.map η =  η.1 ≫ incl₁  Y.1 Y.2 := by
  simp [incl₁]
  apply congrArg
  apply OrderHom.ext
  funext a
  simp [func, Fin.eq_iff_veq]
  rfl

lemma incl₂_map {X Y : SimplexCategory × SimplexCategory} ( η : X⟶ Y) :
    incl₂ X.1 X.2 ≫ Join.func.map η =  η.2 ≫ incl₂  Y.1 Y.2 := by
  simp [incl₂]
  apply congrArg
  apply OrderHom.ext
  funext a
  simp [func, Fin.eq_iff_veq]
  change _ = ((Hom.toOrderHom η.2) a).val +len Y.1 +1
  refine add_right_cancel_iff.mpr ?_
  apply congrArg
  apply congrArg
  rw [Fin.eq_iff_veq]
  change a.val + len X.1 +1 - (len X.1 +1) = _
  exact Nat.sub_eq_of_eq_add rfl


end Join


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

def join : WithInitial SimplexCategory × WithInitial SimplexCategory
    ⥤ WithInitial SimplexCategory where
  obj X :=
    match X with
    | (star, star) => star
    | (of x, star) => of x
    | (star, of x) => of x
    | (of x, of y) => of (Join.func.obj (x,y))
  map {X Y} f :=
    match X, Y, f with
    | (star, star), (star, star), _ => 𝟙 star
    | (star, star), (star, of y), _ => starInitial.to (of y)
    | (star, star), (of y, star), _ => starInitial.to (of y)
    | (star, star), (of y1, of y2), _ => starInitial.to (of (Join.func.obj (y1,y2)))
    | (star, of x), (star, of y), f => f.2
    | (of x, star), (of y, star), f => f.1
    | (of x1, of x2), (of y1, of y2), f => Join.func.map f
    | (of x1, star), (of y1, of y2), f => f.1 ≫ (Join.incl₁ y1 y2)
    | (star, of x2), (of y1, of y2), f => f.2 ≫ (Join.incl₂ y1 y2)
  map_id X :=
    match X with
    | (star, star) => rfl
    | (of x, star) => rfl
    | (star, of x) => rfl
    | (of x, of y) => Join.func.map_id (x,y)
  map_comp {X Y Z} f g := by
    match X, Y, Z, f, g with
    | (star, star), (star, star), (star, star), f, g => rfl
    | (star, star), (star, star), (star, of z), f, g => rfl
    | (star, star), (star, star), (of z, star), f, g => rfl
    | (star, star), (star, star), (of z1, of z2), f, g => rfl
    | (star, star), (star, of y), (star, of z), f, g => rfl
    | (star, star), (of y, star), (of z, star), f, g => rfl
    | (star, star), (star, of y), (of z1, of z2), f, g => rfl
    | (star, star), (of y, star), (of z1, of z2), f, g => rfl
    | (star, star), (of y1, of y2), (of z1, of z2), f, g => rfl
    | (star, of x), (star, of y), (star, of z), f, g => rfl
    | (of x, star), (of y, star), (of z, star), f, g => rfl
    | (star, of x), (star, of y), (of z1, of z2), f, g => rfl
    | (of x, star), (of y, star), (of z1, of z2), f, g => rfl
    | (star, of x), (of y1, of y2), (of z1, of z2), f, g =>
       simp
       apply congrArg
       let g' : (y1, y2) ⟶ (z1, z2) := g
       change g'.2 ≫ _ = Join.incl₂ y1 y2 ≫ Join.func.toPrefunctor.map g'
       exact (Join.incl₂_map g').symm
    | (of x, star), (of y1, of y2), (of z1, of z2), f, g =>
       simp
       apply congrArg
       let g' : (y1, y2) ⟶ (z1, z2) := g
       change g'.1 ≫ _ = Join.incl₁ y1 y2 ≫ Join.func.toPrefunctor.map g'
       exact (Join.incl₁_map g').symm
    | (of x1, of x2), (of y1, of y2), (of z1, of z2), f, g =>
       let g' : (y1, y2) ⟶ (z1, z2) := g
       let f' : (x1, x2) ⟶ (y1, y2) := f
       exact Join.func.map_comp f' g'

lemma join_len (X : WithInitial SimplexCategory × WithInitial SimplexCategory) :
    len (join.obj X) = (len X.1) + (len X.2) := by
  match X with
  | (star, star) => rfl
  | (star, of x) =>
    simp [join]
    rfl
  | (of x, star) =>
    simp [join]
    rfl
  | (of x, of y) =>
    simp [join, len, Join.func, Nat.succ_eq_add_one]
    omega

namespace Split

def obj (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))):
    WithInitial SimplexCategory × WithInitial SimplexCategory := (mk i, mk i.rev)

def sourceValue {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) (i : Fin (Nat.succ (len Y))) :
    Fin (Nat.succ (len X)) :=
  let k := Fin.find (fun a => i ≤ (toOrderHom f a).castSucc)
  match k with
  | some k => k.castSucc
  | none => Fin.last (len X)

lemma sourceValue_id {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X))) :
    sourceValue (𝟙 X) i = i := by
  simp [Split.sourceValue]
  let k := Fin.find (fun a => i ≤ (toOrderHom (𝟙 X) a).castSucc)
  have hk : Fin.find (fun a => i ≤ (toOrderHom (𝟙 X) a).castSucc) = k := rfl
  rw [hk]
  match k with
  | some x =>
    rw [Fin.find_eq_some_iff, toOrderHom_id] at hk
    let hkr := hk.right ⟨i, Nat.lt_of_le_of_lt hk.left x.prop ⟩
    simp at hkr
    simp [Fin.eq_iff_veq]
    exact Nat.le_antisymm hkr hk.left
  | none =>
    rw [Fin.find_eq_none_iff] at hk
    simp only [add_right_eq_self]
    match X with
    | star =>
      ext
      simp_all only [Fin.coe_fin_one]
    | of z =>
      have h1 := hk (Fin.last (z.len))
      ext
      simp  [Fin.lt_def] at h1
      exact Nat.le_antisymm h1 (Fin.is_le i)

lemma lt_sourceValue {X Y : WithInitial SimplexCategory} (f : X ⟶ Y)
    (i : Fin (Nat.succ (len Y)))  (a : Fin (len X)) (ha : a.castSucc < sourceValue f i):
    ((toOrderHom f) a).castSucc < i := by
  let k := Fin.find (fun a => i ≤ (toOrderHom f a).castSucc)
  have hk : Fin.find (fun a => i ≤ (toOrderHom f a).castSucc) = k := rfl
  simp [sourceValue, hk] at ha
  match k with
  | some k =>
    simp_all
    rw [Fin.find_eq_some_iff] at hk
    exact Fin.not_le.mp ((hk.right a).mt (Fin.not_le.mpr ha))
  | none =>
    simp_all
    rw [Fin.find_eq_none_iff] at hk
    exact Fin.not_le.mp (hk a)

lemma sourceValue_le {X Y : WithInitial SimplexCategory} (f : X ⟶ Y)
    (i : Fin (Nat.succ (len Y)))  (a : Fin (len X)) (ha :sourceValue f i ≤  a.castSucc):
    i ≤ ((toOrderHom f) a).castSucc  := by
  let k := Fin.find (fun a => i ≤ (toOrderHom f a).castSucc)
  have hk : Fin.find (fun a => i ≤ (toOrderHom f a).castSucc) = k := rfl
  simp [sourceValue, hk] at ha
  match k with
  | some k =>
    simp_all
    rw [Fin.find_eq_some_iff] at hk
    exact hk.left.trans ((toOrderHom f).monotone' ha )
  | none =>
    simp_all
    rw [Fin.find_eq_none_iff] at hk
    rw [Fin.eq_iff_veq] at ha
    simp at ha
    omega

lemma add_sourceValue_lt {X Y : WithInitial SimplexCategory} {f : X ⟶ Y}
    {i : Fin (Nat.succ (len Y))} (a : Fin (sourceValue f i).rev.val) :
    a.val + (sourceValue f i).val < len X := by
  have h1 := a.prop
  simp [Fin.val_rev] at h1
  exact Nat.add_lt_of_lt_sub h1

lemma sourceValue_lt_of_le {X Y : WithInitial SimplexCategory} (f : X ⟶ Y)
    (i : Fin (Nat.succ (len Y))) (a : Fin (len X))  (ha :sourceValue f i ≤  a.castSucc):
    ((toOrderHom f) a).val - i.val < i.rev.val := by
  rw [tsub_lt_iff_left]
  rw [Fin.val_rev]
  simp
  rw [add_comm]
  rw [tsub_add_cancel_iff_le.mpr i.is_le]
  exact ((toOrderHom f) a).prop
  exact sourceValue_le f i a ha

lemma sourceValue_comp  {X Y Z: WithInitial SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : Fin (Nat.succ (len Z))) :
    sourceValue f (sourceValue g i) = sourceValue (f ≫ g) i := by
  rw [sourceValue, sourceValue, sourceValue]
  apply congrFun
  apply congrFun
  apply congrArg
  let k := Fin.find fun a ↦ i ≤ Fin.castSucc ((toOrderHom g) a)
  have hk : Fin.find fun a ↦ i ≤ Fin.castSucc ((toOrderHom g) a) = k := rfl
  rw [hk]
  match k with
  | some x =>
    rw [Fin.find_eq_some_iff] at hk
    simp [toOrderHom_comp]
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
    simp
    have h1 : Fin.find fun a ↦ Fin.castSucc ((toOrderHom f) a) = Fin.last (len Y) = none := by
      rw [Fin.find_eq_none_iff]
      intro i
      have hi:= ((toOrderHom f) i).prop
      rw [Fin.eq_iff_veq]
      omega
    rw [h1]
    symm
    rw [Fin.find_eq_none_iff, toOrderHom_comp]
    exact fun l => hk ((toOrderHom f) l)

def objEquiv {X : WithInitial SimplexCategory} {i j : Fin (Nat.succ (len X))}
    (h : i = j) : obj X i ≅ obj X j where
  hom := (homMk (Fin.castIso (by rw [h]  : i.val = j.val)),
          homMk (Fin.castIso (by rw [h] : i.rev.val = j.rev.val)))
  inv := (homMk (Fin.castIso (by rw [h]  : i.val = j.val).symm),
          homMk (Fin.castIso (by rw [h] : i.rev.val = j.rev.val).symm))
  hom_inv_id := by
    simp only [obj, Fin.val_rev, prod_Hom, prod_comp, prod_id, Prod.mk.injEq]
    rw [homMk_comp, homMk_comp]
    change homMk (OrderHom.id) =_ ∧ homMk (OrderHom.id) =_
    rw [homMk_id, homMk_id]
    simp only [and_self]
  inv_hom_id := by
    simp [obj]
    rw [homMk_comp, homMk_comp]
    change homMk (OrderHom.id) =_ ∧ homMk (OrderHom.id) =_
    rw [homMk_id, homMk_id]
    simp only [and_self]

lemma objEquiv_refl {X : WithInitial SimplexCategory} {i  : Fin (Nat.succ (len X))} :
    objEquiv (by rfl : i = i) = Iso.refl (obj X i) := by
  ext
  simp [objEquiv]
  change (homMk (OrderHom.id), homMk (OrderHom.id)) =_
  rw [homMk_id, homMk_id, prod_id]
  rfl

def map {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) (i : Fin (Nat.succ (len Y))) :
    obj X (sourceValue f i) ⟶ obj Y i:=
  (homMk {
    toFun := fun a => ⟨(toOrderHom f) ⟨a.val, Nat.lt_of_lt_of_le a.prop (sourceValue f i).is_le⟩,
      (lt_sourceValue f i ⟨a.val, Nat.lt_of_lt_of_le a.prop (sourceValue f i).is_le⟩ a.prop)⟩
    monotone' := by
      intro a b h
      apply (toOrderHom f).monotone'
      exact h
  },
  homMk {
    toFun := fun a => ⟨(toOrderHom f) ⟨a.val + (sourceValue f i).val , add_sourceValue_lt a⟩
      - i.val, sourceValue_lt_of_le f i ⟨a.val + (sourceValue f i).val , add_sourceValue_lt a⟩
      (by rw [Fin.le_def]; exact le_of_add_le_right Nat.le.refl)
       ⟩
    monotone' := by
      intro a b h
      simp
      rw [tsub_add_cancel_iff_le.mpr]
      apply (toOrderHom f).monotone'
      simp
      exact h
      apply sourceValue_le
      rw [Fin.le_def]
      simp only [Fin.castSucc_mk, le_add_iff_nonneg_left, zero_le]
  })

lemma map_id {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X))) :
    (objEquiv (sourceValue_id i)).inv ≫ map (𝟙 X) i = 𝟙 (obj X i) := by
  simp [map, objEquiv]
  rw [prod_id, Prod.mk.injEq]
  simp [obj]
  rw [homMk_comp, homMk_comp, ← homMk_id, ← homMk_id]
  apply And.intro
  match X with
  | star => rfl
  | of x => rfl
  match X with
  | star =>
    simp_all only [Fin.val_rev, Fin.coe_fin_one, add_zero, Fin.eta, tsub_zero]
    rfl
  | of x =>
    apply congrArg
    apply OrderHom.ext
    funext a
    rw [Fin.eq_iff_veq]
    change a.val + (sourceValue (𝟙 (of x)) i).val -i = a.val
    rw [sourceValue_id i]
    exact Nat.add_sub_cancel ↑a ↑i

lemma map_comp {X Y Z: WithInitial SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : Fin (Nat.succ (len Z)))  : map (f ≫ g) i
    =  (objEquiv (sourceValue_comp f g i)).inv ≫ map f (sourceValue g i) ≫ map g i := by
  match X, Y, Z, f, g with
  | star, star, star, f, g => rfl
  | star, star, of z, f, g => rfl
  | star, of y, of z, f, g => rfl
  | of x, of y, of z, f, g =>
     simp [map, objEquiv]
     rw [homMk_comp, homMk_comp]
     apply And.intro
     apply congrArg
     rfl
     rw [homMk_comp, homMk_comp]
     apply congrArg
     apply OrderHom.ext
     funext a
     rw [Fin.eq_iff_veq]
     simp [(sourceValue_comp f g i)]
     simp [toOrderHom_comp]
     change ((toOrderHom g) ((toOrderHom f) ⟨a.val + (sourceValue (f ≫ g) i).val, _⟩)).val - i.val =
       ((toOrderHom g) ⟨((toOrderHom f) ⟨a.val + (sourceValue (f ≫ g) i).val, _⟩).val
        - (sourceValue g i).val + (sourceValue g i).val, _⟩)  - i.val
     apply congrFun
     repeat apply congrArg
     rw [Fin.eq_iff_veq]
     simp
     rw [tsub_add_cancel_of_le]
     simp [← (sourceValue_comp f g i)]
     apply sourceValue_le
     rw [Fin.le_def]
     simp only [Fin.castSucc_mk, le_add_iff_nonneg_left, zero_le]

end Split

lemma join_split_len (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))) :
    len (join.obj (Split.obj X i)) = len X := by
  rw [join_len]
  simp [Split.obj]
  rw [len_mk, len_mk]
  omega

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
