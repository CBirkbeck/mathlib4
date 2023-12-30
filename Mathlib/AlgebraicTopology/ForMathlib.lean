import Mathlib.AlgebraicTopology.Nerve

open CategoryTheory CategoryTheory.Limits Opposite

open Simplicial

lemma Finset.card_le_three {α : Type*} [DecidableEq α] (a b c : α) :
  Finset.card {a, b, c} ≤ 3 := by
  apply (card_insert_le _ _).trans; apply Nat.succ_le_succ
  apply (card_insert_le _ _).trans; apply Nat.succ_le_succ
  simp only [card_singleton, le_refl]

-- TODO: move
instance fin_zero_le_one (n : ℕ) : ZeroLEOneClass (Fin (n+2)) where
  zero_le_one := by rw [← Fin.val_fin_le]; exact zero_le'

namespace CategoryTheory

namespace Functor

variable {C : Type*} [Category C] {D : Type*} [Category D]

lemma map_eqToHom (F : C ⥤ D) (X Y : C) (h : X = Y) :
    F.map (eqToHom h) = eqToHom (congrArg F.obj h) := by
  subst h
  simp only [eqToHom_refl, map_id]

end Functor

namespace ComposableArrows

variable {C : Type*} [inst : Category C] {n : ℕ}

lemma map'_def (F : ComposableArrows C n)
    (i j : ℕ) (hij : i ≤ j := by linarith) (hjn : j ≤ n := by linarith) :
    F.map' i j = F.map (homOfLE (Fin.mk_le_mk.mpr hij)) := rfl

end ComposableArrows

end CategoryTheory
