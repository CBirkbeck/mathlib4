/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.Tactic.Linarith
import Mathlib.CategoryTheory.Skeletal
import Mathlib.Data.Fin.Interval
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Category.FinLinOrd
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial

/-! # The augmented simplex category

We construct a skeletal model of the augmented simplex category, with objects `ℕ` and the
morphism `n ⟶ m` being the monotone maps from `Fin n` to `Fin m`.

We show the following:
* This category is equivalent to `FinLinOrd`.
* This category has a strict initial object given by `0`.

We define the following:
* The obvious functor of `SimplexCategory` into `AugmentedSimplexCategory`.
* The preimage of the above functor.
-/


universe v u

open CategoryTheory CategoryTheory.Limits

/-- The augmented simplex category:
* objects are natural numbers `n : ℕ`
* morphisms from `n` to `m` are monotone functions `Fin n → Fin m`
-/
def AugmentedSimplexCategory :=
  ℕ

namespace AugmentedSimplexCategory

/-- Interpret a natural number as an object of the augmented simplex category. -/
def mk (n : ℕ) : AugmentedSimplexCategory :=
  n


/-- The length of an object of `AugmentedSimplexCategory`. -/
def len (n : AugmentedSimplexCategory) : ℕ :=
  n

/-- the `n`-dimensional augmented simplex can be denoted `[n]ₐ` -/
 notation "[" n "]ₐ" => AugmentedSimplexCategory.mk n

@[ext]
theorem ext (a b : AugmentedSimplexCategory) : a.len = b.len → a = b :=
  id


/-- Morphisms in the `AugmentedSimplexCategory`. -/
protected def Hom (a b : AugmentedSimplexCategory) :=
  Fin a.len  →o Fin b.len

namespace Hom

/-- Make a morphism in `AugmentedSimplexCategory` from a monotone map of `Fin`'s. -/
def mk {a b : AugmentedSimplexCategory} (f : Fin a.len  →o Fin b.len ):
    AugmentedSimplexCategory.Hom a b :=
  f
/-- Recover the monotone map from a morphism in the augmented simplex category. -/
def toOrderHom {a b : AugmentedSimplexCategory} (f : AugmentedSimplexCategory.Hom a b) :
    Fin a.len →o Fin b.len  :=
  f

theorem ext' {a b : AugmentedSimplexCategory} (f g : AugmentedSimplexCategory.Hom a b) :
    f.toOrderHom = g.toOrderHom → f = g :=
  id

/-- Identity morphisms of `AugmentedSimplexCategory`. -/
@[simp]
def id (a : AugmentedSimplexCategory) : AugmentedSimplexCategory.Hom a a :=
  mk OrderHom.id

/-- Composition of morphisms of `AugmentedSimplexCategory`. -/
@[simp]
def comp {a b c : AugmentedSimplexCategory} (f : AugmentedSimplexCategory.Hom b c)
    (g : AugmentedSimplexCategory.Hom a b) :
    AugmentedSimplexCategory.Hom a c :=
  mk <| f.toOrderHom.comp g.toOrderHom

end Hom

@[simps]
instance smallCategory : SmallCategory.{0} AugmentedSimplexCategory where
  Hom n m := AugmentedSimplexCategory.Hom n m
  id m := AugmentedSimplexCategory.Hom.id _
  comp f g := AugmentedSimplexCategory.Hom.comp g f

@[ext]
theorem Hom.ext {a b : AugmentedSimplexCategory} (f g : a ⟶ b) :
    f.toOrderHom = g.toOrderHom → f = g :=
  Hom.ext' _ _
section Skeleton
/-- The functor that exhibits `AugmentedSimplexCategory` as skeleton
of `FinLinOrd` -/
@[simps obj map]
def skeletalFunctor : AugmentedSimplexCategory ⥤ FinLinOrd where
  obj a := FinLinOrd.of (Fin a.len)
  map f := f.toOrderHom

theorem skeletalFunctor.coe_map {Δ₁ Δ₂ : AugmentedSimplexCategory} (f : Δ₁ ⟶ Δ₂) :
    ↑(skeletalFunctor.map f) = f.toOrderHom :=
  rfl

theorem skeletal : Skeletal AugmentedSimplexCategory := fun X Y ⟨I⟩ => by
  suffices Fintype.card (Fin X.len) = Fintype.card (Fin Y.len) by
    ext
    simpa
  apply Fintype.card_congr
  exact ((skeletalFunctor ⋙ forget FinLinOrd).mapIso I).toEquiv

namespace SkeletalFunctor

instance : Full skeletalFunctor where
  preimage f := AugmentedSimplexCategory.Hom.mk f

instance : Faithful skeletalFunctor where
  map_injective {_ _ f g} h := by
    ext1
    exact h

instance : EssSurj skeletalFunctor where
  mem_essImage X :=
    ⟨mk (Fintype.card X : ℕ),
      ⟨by
        let f :Fin (Fintype.card X) ≃o X:= monoEquivOfFin X (by rfl)
        exact
          { hom := ⟨f, OrderIso.monotone f⟩
            inv := ⟨f.symm, OrderIso.monotone (f.symm)⟩
            hom_inv_id := by ext1; apply f.symm_apply_apply
            inv_hom_id := by ext1; apply f.apply_symm_apply }
      ⟩⟩
noncomputable instance isEquivalence : IsEquivalence skeletalFunctor :=
  Equivalence.ofFullyFaithfullyEssSurj skeletalFunctor

end SkeletalFunctor
/-- The equivalence that exhibits `AugmentedSimplexCategory` as skeleton
of `FinLinOrd` -/
noncomputable def skeletalEquivalence : AugmentedSimplexCategory ≌ FinLinOrd :=
  Functor.asEquivalence skeletalFunctor

end Skeleton

noncomputable instance  : IsInitial [0]ₐ := by
  have h : ReflectsColimit (Functor.empty AugmentedSimplexCategory) skeletalFunctor:=
   CreatesColimit.toReflectsColimit
  apply h.reflects
  exact
    isColimitChangeEmptyCocone FinLinOrd (IsInitial.ofUnique (FinLinOrd.of (Fin 0)))
    (skeletalFunctor.mapCocone (asEmptyCocone [0]ₐ)) (eqToIso (by rfl))

lemma zero_isInitial : IsInitial [0]ₐ := by
  exact instIsInitialAugmentedSimplexCategorySmallCategoryMkOfNatNatInstOfNatNat

lemma len_zero_isInitial {Z: AugmentedSimplexCategory} (hZ : Z.len=0):
 IsInitial Z:= by
   have h : Z= [0]ₐ := by
    ext
    exact hZ
   rw  [h]
   exact instIsInitialAugmentedSimplexCategorySmallCategoryMkOfNatNatInstOfNatNat
-- An isomorphism in `SimplexCategory` induces an `OrderIso`. -/
@[simp]
def orderIsoOfIso {x y : AugmentedSimplexCategory} (e : x ≅ y) : Fin x.len ≃o Fin y.len :=
  Equiv.toOrderIso
    { toFun := e.hom.toOrderHom
      invFun := e.inv.toOrderHom
      left_inv := fun i => by
        simpa only using congr_arg (fun φ => (Hom.toOrderHom φ) i) e.hom_inv_id
      right_inv := fun i => by
        simpa only using congr_arg (fun φ => (Hom.toOrderHom φ) i) e.inv_hom_id }
    e.hom.toOrderHom.monotone e.inv.toOrderHom.monotone

lemma iso_len {X Y : AugmentedSimplexCategory} ( f: X⟶ Y ) [IsIso f]: X.len =Y.len := by
    rename_i iso
    let isot: X≅ Y := asIso f
    let ioh:= orderIsoOfIso isot
    have hii:= ioh.toEquiv
    have hx:(Finset.univ :Finset (Fin (X.len))).card
    = Finset.card (Finset.image (⇑hii) (Finset.univ :Finset (Fin (X.len)))) := by
        symm
        apply Finset.card_image_of_injOn
        exact Set.injOn_of_injective (Equiv.injective hii) (Finset.univ :Finset (Fin (X.len)))
    have hx2 :Finset.card (Finset.image (⇑hii) (Finset.univ :Finset (Fin (X.len))))
     =  (Finset.univ :Finset (Fin (Y.len))).card := by
        congr
        exact Finset.image_univ_equiv hii
    rw [Finset.card_fin X.len] at hx
    rw [Finset.card_fin Y.len] at hx2
    rw [hx, hx2]

lemma isInitial_len_zero {Z: AugmentedSimplexCategory}  (h : IsInitial Z) :Z.len = 0 := by
  have heq: Z ≅ [0]ₐ := by
    apply IsInitial.uniqueUpToIso
    exact h
    exact zero_isInitial
  let f:= heq.hom
  have ft: IsIso f := IsIso.of_iso heq
  exact iso_len f

def strict_initial' {Y Z: AugmentedSimplexCategory} (f: Z ⟶ Y) (hZ : Z.len≠ 0):
    Y.len≠ 0:= by
      let f': Fin (Z.len) →o Fin (Y.len) := f.toOrderHom
      by_contra  hYn
      rw [hYn] at f'
      exact ((fun a ↦ IsEmpty.false a) ∘ f') (⟨ 0 ,Nat.pos_of_ne_zero hZ⟩:Fin (Z.len) )

lemma map_into_initial_eq {Z I : AugmentedSimplexCategory} (h:IsInitial I) (f : Z ⟶ I) : Z=I := by
  have hI2: I.len =0 :=isInitial_len_zero h
  by_cases hZ: Z.len=0
  · apply ext
    rw [hZ, hI2]
  · have hI: I.len ≠ 0 := strict_initial' f hZ
    exact (hI hI2).elim

lemma map_into_initial_eqToHom {Z I : AugmentedSimplexCategory} (h : IsInitial I) (f : Z ⟶ I) :
    f = eqToHom (map_into_initial_eq h f):= by
    have hZ: IsInitial Z := by
      rw [map_into_initial_eq h f]
      exact h
    apply IsInitial.hom_ext hZ

instance : HasStrictInitialObjects AugmentedSimplexCategory := by
  fconstructor
  intro I A f hIf
  rw [map_into_initial_eqToHom hIf f]
  exact instIsIsoEqToHom (map_into_initial_eq hIf f)


def map_from_initial (n: ℕ ): [0]ₐ ⟶  [n]ₐ :=(@OrderEmbedding.ofIsEmpty (Fin 0) (Fin n)).toOrderHom


section InitialSegements

def InitialSeg' {n:ℕ} (i : Fin (n+1)) : Fin (i.val) →o Fin (n):=
 OrderHom.comp (@Fin.castIso (i.val+(n-i.val)) n (add_tsub_cancel_of_le  (Fin.is_le i) ))
 (@Fin.castAddEmb i.val (n-i.val)).toOrderHom


def InitialSeg_comp' {n:ℕ} (i : Fin (n+1)) : Fin (n-i.val) →o Fin (n):=
OrderHom.comp (@Fin.castIso ((n-i.val)+i.val) n (tsub_add_cancel_of_le (Fin.is_le i)))
   (@Fin.addNatEmb (n-i.val) i.val).toOrderHom

def InitialSeg {n:ℕ} (i : Fin (n+1)) : [i.val]ₐ ⟶  [n]ₐ := InitialSeg' i

def InitialSeg_comp {n:ℕ} (i : Fin (n+1)) : [n-i.val]ₐ ⟶ [n]ₐ  := InitialSeg_comp' i

def preimage {m n : ℕ} (f : [m]ₐ ⟶ [n]ₐ) (i: Fin (n+1)) : Fin (m+1) :=
  ⟨ Finset.card  (Set.toFinset {a | (f.toOrderHom a).val < i.val}),by {
    rw [Nat.lt_succ]
    exact card_finset_fin_le _
  } ⟩

end InitialSegements
end AugmentedSimplexCategory

def SimplexCategory.augment : SimplexCategory ⥤ AugmentedSimplexCategory where
  obj X := (X.len+1)
  map f :=  f.toOrderHom

lemma SimplexCategory.augment_len (Z : SimplexCategory ):
    (SimplexCategory.augment.obj  Z).len ≠  0 := by
      unfold  SimplexCategory.augment
      exact Nat.succ_ne_zero (SimplexCategory.len Z)

namespace AugmentedSimplexCategory

def unaugment.obj (Z : AugmentedSimplexCategory)  : SimplexCategory :=
   SimplexCategory.mk (Z.len-1)

lemma unaugment_augment_obj {Z : AugmentedSimplexCategory} (hZ: Z.len ≠ 0) :
   SimplexCategory.augment.obj (unaugment.obj Z) = Z:= by
      unfold SimplexCategory.augment
      dsimp
      apply AugmentedSimplexCategory.ext
      exact Nat.succ_pred hZ

namespace unaugment
def map {Y Z: AugmentedSimplexCategory} (f: Z ⟶ Y)
    (hZ :Z.len≠ 0) : (obj Z) ⟶ (obj Y) := SimplexCategory.Hom.mk ((eqToHom (unaugment_augment_obj (hZ))) ≫  f≫
    (eqToHom (unaugment_augment_obj (strict_initial' f hZ)).symm) )

lemma map_id { Z: AugmentedSimplexCategory}  (hZ :Z.len≠ 0) :
    map (𝟙 Z) hZ = 𝟙 (SimplexCategory.mk (Z.len-1)) := by
       unfold map
       rw [← eqToHom_refl,← eqToHom_refl,eqToHom_trans,eqToHom_trans]
       all_goals rfl

lemma map_comp { Y Z  W: AugmentedSimplexCategory}  (hW :W.len≠ 0)
    (f: Z ⟶ Y) (g : W ⟶ Z) :
     map (g ≫ f) hW = (map g hW) ≫  (map f (strict_initial' g hW))   := by
       have ht: (map g hW) ≫  (map f (strict_initial' g hW)) =
       SimplexCategory.Hom.mk ( (eqToHom (unaugment_augment_obj (hW)))≫ g
       ≫  ((eqToHom (unaugment_augment_obj (strict_initial' g hW)).symm) ≫
      (eqToHom (unaugment_augment_obj (strict_initial' g hW)))) ≫ f ≫
      (eqToHom (unaugment_augment_obj (strict_initial' f (strict_initial' g hW))).symm)
      ) := rfl
       rw [ht,eqToHom_trans,eqToHom_refl]
       rfl
end unaugment

lemma unaugment_augment_map {X Z : AugmentedSimplexCategory  } (f: Z ⟶ X ) (hZ :Z.len ≠ 0):
   eqToHom (AugmentedSimplexCategory.unaugment_augment_obj hZ).symm≫ SimplexCategory.augment.map (AugmentedSimplexCategory.unaugment.map f hZ)
    ≫ eqToHom (AugmentedSimplexCategory.unaugment_augment_obj (AugmentedSimplexCategory.strict_initial' f hZ)) =  f
    := by
      rw [eqToHom_comp_iff,comp_eqToHom_iff]
      rfl


end AugmentedSimplexCategory

lemma SimplexCategory.augment_unaugment_map {X Z : SimplexCategory  } (f: Z ⟶ X):
 AugmentedSimplexCategory.unaugment.map (SimplexCategory.augment.map f)
  (SimplexCategory.augment_len Z) = f := by
    unfold SimplexCategory.augment AugmentedSimplexCategory.unaugment.map
    dsimp
    change _= SimplexCategory.Hom.mk (f.toOrderHom)
    congr
    apply OrderHom.ext
    rfl
