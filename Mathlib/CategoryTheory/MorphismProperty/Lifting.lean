/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.Tactic.ApplyFun

/-!

-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- `f : X ⟶ Y` is a retract of `g : Z ⟶ W` if there are morphisms `i : f ⟶ g`
and `r : g ⟶ f` in the arrow category of `C` such that `i ≫ r = 𝟙 f`. -/
class IsRetract {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ W) where
  i : Arrow.mk f ⟶ Arrow.mk g
  r : Arrow.mk g ⟶ Arrow.mk f
  retract : i ≫ r = 𝟙 Arrow.mk f

namespace MorphismProperty

/-- A class of morphisms is stable under retracts if the retract of a morphism still
lies in the class. -/
def IsStableUnderRetracts (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y Z W : C⦄ ⦃f : X ⟶ Y⦄ ⦃g : Z ⟶ W⦄ (_ : IsRetract f g)
    (_ : P g), P f

/-- The morphism property of having the left lifting property (llp) with respect to another class of
morphisms. -/
def Llp (T : MorphismProperty C) : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ ⦃g : X ⟶ Y⦄ (_ : T g), HasLiftingProperty f g

/-- The morphism property of having the right lifting property (rlp) with respect to a class of
morphisms. -/
def Rlp (T : MorphismProperty C) : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ ⦃g : X ⟶ Y⦄ (_ : T g), HasLiftingProperty g f

/-- Inductive definition of the class of a single morphism, to take advantage
of the `MorphismProperty` API. -/
inductive Morphism {A B : C} (p : A ⟶ B) : {X Y : C} → (X ⟶ Y) → Prop
  | mk : (Morphism p) p

/-- The class of a single morphism `p`. -/
def MorphismClass {X Y : C} (p : X ⟶ Y) : MorphismProperty C := fun _ _ i ↦ (Morphism p) i

lemma classRlp_iff_LlpMorphism (T : MorphismProperty C) {X Y : C} (p : X ⟶ Y) :
    T.Rlp p ↔ ∀ {A B} (i : A ⟶ B) (_ : T i), (MorphismClass p).Llp i := by
  refine ⟨fun hp _ _ _ hi _ _ _ h ↦ by induction h; exact hp hi, fun h _ _ i hi ↦ h i hi .mk⟩

lemma classLlp_iff_RlpMorphism (T : MorphismProperty C) {X Y : C} (p : X ⟶ Y) :
    T.Llp p ↔ ∀ {A B} (i : A ⟶ B) (_ : T i), (MorphismClass p).Rlp i := by
  refine ⟨fun hp _ _ _ hi _ _ _ h ↦ by induction h; exact hp hi, fun h _ _ i hi ↦ h i hi .mk⟩

instance monomorphisms.IsStableUnderRetracts : IsStableUnderRetracts (monomorphisms C) := by
  intro _ _ _ _ f g H p
  refine ⟨fun α β ω ↦ ?_⟩
  have h : IsRetract.i.left ≫ g = f ≫ IsRetract.i.right := H.i.w
  have := ω =≫ H.i.right
  rw [Category.assoc, Category.assoc, ← h, ← Category.assoc, ← Category.assoc] at this
  have ω' := (p.right_cancellation (α ≫ H.i.left) (β ≫ H.i.left) this) =≫ H.r.left
  have := Arrow.hom.congr_left H.retract
  aesop

instance Llp.IsStableUnderRetracts {T : MorphismProperty C} : IsStableUnderRetracts T.Llp := by
  intro _ _ _ _ f f' H L _ _ g h
  refine ⟨fun {u v} sq ↦ ?_⟩
  have : (H.r.left ≫ u) ≫ g = f' ≫ (H.r.right ≫ v) := by simp [sq.w]
  obtain lift := ((L h).sq_hasLift (CommSq.mk this)).exists_lift.some
  refine ⟨H.i.right ≫ lift.l, ?_, ?_⟩
  · rw [← Category.assoc]
    have := H.i.w
    dsimp at this
    rw [← this, Category.assoc, lift.fac_left, ← Category.assoc]
    have := Arrow.hom.congr_left H.retract
    aesop
  · rw [Category.assoc, lift.fac_right, ← Category.assoc]
    have := Arrow.hom.congr_right H.retract
    aesop

instance Rlp.IsStableUnderRetracts {T : MorphismProperty C} : IsStableUnderRetracts T.Rlp := by
  intro X Y _ _ f f' H L _ _ g h
  refine ⟨fun {u v} sq ↦ ?_⟩
  have : (u ≫ H.i.left) ≫ f' = g ≫ (v ≫ H.i.right) := by
    rw [← Category.assoc, ← sq.w]
    aesop
  obtain lift := ((L h).sq_hasLift (CommSq.mk this)).exists_lift.some
  refine ⟨lift.l ≫ H.r.left, ?_, ?_⟩
  · have h : H.i.left ≫ H.r.left = 𝟙 X := Arrow.hom.congr_left H.retract
    rw [← Category.assoc, lift.fac_left, Category.assoc, h, Category.comp_id]
  · have h : H.r.left ≫ f = f' ≫ H.r.right := H.r.w
    have h' : H.i.right ≫ H.r.right = 𝟙 Y := Arrow.hom.congr_right H.retract
    rw [Category.assoc, h, ← Category.assoc, lift.fac_right, Category.assoc, h', Category.comp_id]

open Limits.PushoutCocone in
instance Llp.IsStableUnderCobaseChange {T : MorphismProperty C} :
    IsStableUnderCobaseChange T.Llp := by
  refine ⟨fun {A B A' B'} f s f' t P L X Y g hg ↦ ⟨fun {u v} sq ↦ ?_⟩⟩
  have w : (s ≫ u) ≫ g = f ≫ (t ≫ v) := by
    rw [← Category.assoc, ← P.toCommSq.w, Category.assoc, Category.assoc, sq.w]
  obtain lift := ((L hg).sq_hasLift (CommSq.mk w)).exists_lift.some
  let lift' : B' ⟶ X := IsColimit.desc P.isColimit u lift.l (by rw [lift.fac_left])
  let l : f' ≫ lift' = u := IsColimit.inl_desc P.isColimit u lift.l (by rw [lift.fac_left])
  let l' : t ≫ lift' = lift.l := IsColimit.inr_desc P.isColimit u lift.l (by rw [lift.fac_left])
  let newCocone := mk (f' ≫ v) (t ≫ v) (by have := P.w; apply_fun (fun f ↦ f ≫ v) at this; aesop)
  refine ⟨lift', l,
    (P.isColimit.uniq newCocone (lift' ≫ g) ?_).trans (P.isColimit.uniq newCocone v ?_).symm⟩
  all_goals
    dsimp [newCocone]
    intro j
    cases j
    simp only [Limits.span_zero, condition_zero, IsPushout.cocone_inl, Category.assoc]
  · rw [← Category.assoc, ← Category.assoc, Category.assoc s f' lift', l, ← sq.w, Category.assoc]
  · rename_i k; cases k; all_goals dsimp
    · rw [← Category.assoc, l, sq.w]
    · rw [← Category.assoc, l', lift.fac_right]
  · rename_i k; cases k; all_goals dsimp

open Limits.PullbackCone in
instance Rlp.IsStableUnderBaseChange {T : MorphismProperty C} :
    IsStableUnderBaseChange T.Rlp := by
  refine ⟨fun {B' A A' B} t f s f' P L X Y g hg ↦ ⟨fun {u v} sq ↦ ?_⟩⟩
  have w : (u ≫ s) ≫ f = g ≫ v ≫ t := by
    rw [Category.assoc, P.toCommSq.w, ← Category.assoc, ← Category.assoc, sq.w]
  obtain lift := ((L hg).sq_hasLift (CommSq.mk w)).exists_lift.some
  let lift' : Y ⟶ A' := IsLimit.lift P.isLimit lift.l v (by rw [lift.fac_right])
  let l : lift' ≫ f' = v := IsLimit.lift_snd P.isLimit lift.l v (by rw [lift.fac_right])
  let l' : lift' ≫ s = lift.l := IsLimit.lift_fst P.isLimit lift.l v (by rw [lift.fac_right])
  have comm : (u ≫ s) ≫ f = (g ≫ v) ≫ t := by aesop
  let newCone := mk _ _ comm
  refine ⟨lift',
      (P.isLimit.uniq newCone (g ≫ lift') ?_).trans (P.isLimit.uniq newCone u ?_).symm, l⟩
  all_goals dsimp [newCone]; intro j; cases j; simp only [Limits.cospan_one, condition_one,
    IsPullback.cone_fst, Category.assoc]
  · rw [← Category.assoc u, ← lift.fac_left, ← l', Category.assoc, Category.assoc]
  · rename_i k; cases k; all_goals dsimp
    · rw [← lift.fac_left, ← l', Category.assoc]
    · rw [← sq.w, Category.assoc, l, sq.w]
  · rename_i k; cases k; all_goals dsimp
    exact sq.w

instance Rlp.IsStableUnderComposition (T : MorphismProperty C) :
    IsStableUnderComposition T.Rlp := by
  refine ⟨fun p q hp hq _ _ i hi ↦ ⟨fun {f g} sq ↦ ?_⟩⟩
  have q_sq_comm : (f ≫ p) ≫ q = i ≫ g := by rw [Category.assoc, sq.w]
  obtain ⟨q_lift, q_fac_left, q_fac_right⟩ :=
    ((hq hi).sq_hasLift (CommSq.mk q_sq_comm)).exists_lift.some
  obtain ⟨p_lift, p_fac_left, p_fac_right⟩ :=
    ((hp hi).sq_hasLift (CommSq.mk q_fac_left.symm)).exists_lift.some
  refine ⟨p_lift, p_fac_left, by rw [← Category.assoc, p_fac_right, q_fac_right]⟩

instance Llp.IsStableUnderComposition (T : MorphismProperty C) :
    IsStableUnderComposition T.Llp := by
  refine ⟨fun p q hp hq _ _ i hi ↦ ⟨fun {f g} sq ↦ ?_⟩⟩
  have q_sq_comm : f ≫ i = p ≫ (q ≫ g) := by rw [← Category.assoc, ← sq.w]
  obtain ⟨p_lift, p_fac_left, p_fac_right⟩ :=
    ((hp hi).sq_hasLift (CommSq.mk q_sq_comm)).exists_lift.some
  obtain ⟨q_lift, q_fac_left, q_fac_right⟩ :=
    ((hq hi).sq_hasLift (CommSq.mk p_fac_right)).exists_lift.some
  refine ⟨q_lift, by rw [Category.assoc, q_fac_left, p_fac_left], q_fac_right⟩

end MorphismProperty

end CategoryTheory
