/-
Copyright (c) 2025 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet
-/
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Quasicompact and quasiseparated sheaves

Given a site `(C, J)`, we define structures for being quasicompact, quasiseparated
or qcqs sheaves.

-/

universe u v u' v' w

namespace CategoryTheory

open Category

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A] [HasWeakSheafify J A] [Limits.HasColimits A]

section Quasicompact

/-- An object `X` of a site `(C, J)` is quasicompact if given any presieve `S` that generates a
  covering sieve of `X`, there exists a finite subpresieve of `S` that generates a covering sieve
  of `X`. -/
structure GrothendieckTopology.Quasicompact (X : C) : Prop where
  isQuasicompact : ∀ S : Presieve X, J.sieves X (Sieve.generate S) → ∃ S' : Presieve X,
    S' ≤ S ∧ J.sieves X (Sieve.generate S')

theorem Sheaf.quasicompact_iff_quasicompact_yoneda [HasWeakSheafify J (Type v)] (X : C) :
    J.Quasicompact X ↔ (Sheaf.canonicalTopology (Sheaf J (Type v))).Quasicompact
    ((presheafToSheaf J (Type v)).obj (yoneda.obj X)) := by
  sorry

theorem Sheaf.quasicompact_iff_finite_subcover (F : Sheaf J A) :
    (Sheaf.canonicalTopology (Sheaf J A)).Quasicompact F
    ↔ ∀ (I : Type v') (G : I → Sheaf J A) (f : ∐ G ⟶ F),
    Epi f → ∃ J : Finset I, Epi ((Limits.Sigma.map' Subtype.val (fun (j : J) => 𝟙 (G j))) ≫ f) :=
  sorry

/-- A sheaf `F` is quasicompact if any cover `∐ G ⟶ F` admits a finite subcover. -/
structure Quasicompact' (F : Sheaf J A) : Prop where
  isQuasicompact : ∀ (I : Type v') (G : I → Sheaf J A) (f : ∐ G ⟶ F),
    Epi f → ∃ J : Finset I, Epi ((Limits.Sigma.map' Subtype.val (fun (j : J) => 𝟙 (G j))) ≫ f)

lemma quasicompact_of_finite_presieve_quasicompact (F : Sheaf J A) (I : Type v') (hI : Fintype I)
    (G : I → Sheaf J A) (hG : ∀ i : I, Quasicompact' (G i)) (f : ∐ G ⟶ F) (hf : Epi f) :
    Quasicompact' F where
  isQuasicompact I' G' f' hf' := by
    sorry
    --choose J' hJ' using (fun i : I => hG i I' (fun i' => Limits.pullback (Sigma.ι i ≫ f) f') _)

end Quasicompact

namespace Sheaf

variable [Limits.HasPullbacks A]

section Quasiseparated

/-- A morphism of sheaves `g : G ⟶ F` is quasicompact if the pullback of any morphism `F' ⟶ F`
  with quasicompact source is again quasicompact. -/
structure QuasicompactMap {F G : Sheaf J A} (g : G ⟶ F) : Prop where
  quasicompact_pullback : ∀ (F' : Sheaf J A) (f : F' ⟶ F),
    Quasicompact' F' → Quasicompact' (Limits.pullback f g)

/-- A sheaf `F` is quasiseparated if any morphism `F' ⟶ F` with quasicompact source is
  quasicompact. -/
structure Quasiseparated (F : Sheaf J A) : Prop where
  isQuasiseparated : ∀ (F' : Sheaf J A) (f : F' ⟶ F), Quasicompact' F' → QuasicompactMap f

end Quasiseparated

section Qcqs

/-- A sheaf `F` is qcqs if it is both quasicompact and quasiseparated. -/
structure Qcqs (F : Sheaf J A) : Prop extends Quasicompact' F, Quasiseparated F

end Qcqs

end Sheaf

end CategoryTheory
