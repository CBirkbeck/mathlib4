/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.Tactic.CategoryTheory.Coherence

/-!
# Adjunctions in bicategories

For a 1-morphisms `f : a ⟶ b` and `g : b ⟶ a` in a bicategory, an adjuntion between `f` and `g`
consists of a pair of 2-morphism `η : 𝟙 a ⟶ f ≫ g` and `ε : g ≫ f ⟶ 𝟙 b` satisfying the triangle
identities. The 2-morphism `η` is called the unit and `ε` is called the counit.

## Main definitions

* `Bicategiry.Adjunction`: adjunctions between two 1-morphisms.
* `Bicategory.Equivalence`: adjoint equivalences between two objects.
* `Bicategory.mkOfAdjointifyCounit`: construct an adjoint equivalence from 2-isomorphisms
  `η : 𝟙 a ≅ f ≫ g` and `ε : g ≫ f ≅ 𝟙 b`, by upgrading `ε` to a counit.
* `Bicategory.mkOfAdjointifyUnit`: construct an adjoint equivalence from 2-isomorphisms
  `η : 𝟙 a ≅ f ≫ g` and `ε : g ≫ f ≅ 𝟙 b`, by upgrading `η` to a unit.

-/

namespace CategoryTheory

namespace Bicategory

open Category

open scoped Bicategory

open Mathlib.Tactic.BicategoryCoherence (bicategoricalComp bicategoricalIsoComp)

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B} {f : a ⟶ b} {g : b ⟶ a}

/-- The 2-morphism defined by the following pasting diagram:
```
a －－－－－－ ▸ a
  ＼    η      ◥   ＼
  f ＼   g  ／       ＼ f
       ◢  ／     ε      ◢
        b －－－－－－ ▸ b
```
-/
@[simp]
def leftZigzag (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :=
  η ▷ f ⊗≫ f ◁ ε

/-- The 2-morphism defined by the following pasting diagram:
```
        a －－－－－－ ▸ a
       ◥  ＼     η      ◥
  g ／      ＼ f     ／ g
  ／    ε      ◢   ／
b －－－－－－ ▸ b
```
-/
@[simp]
def rightZigzag (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :=
  g ◁ η ⊗≫ ε ▷ g

/-- Adjunction between two 1-morphisms. -/
structure Adjunction (f : a ⟶ b) (g : b ⟶ a) where
  unit : 𝟙 a ⟶ f ≫ g
  counit : g ≫ f ⟶ 𝟙 b
  left_triangle : leftZigzag unit counit = (λ_ _).hom ≫ (ρ_ _).inv := by aesop_cat
  right_triangle : rightZigzag unit counit = (ρ_ _).hom ≫ (λ_ _).inv := by aesop_cat

scoped infixr:15 " ⊣ " => Bicategory.Adjunction

namespace Adjunction

attribute [simp] left_triangle right_triangle

/-- Adjunction between identities. -/
def id (a : B) : 𝟙 a ⊣ 𝟙 a where
  unit := (ρ_ _).inv
  counit := (ρ_ _).hom
  left_triangle := by dsimp [bicategoricalComp]; pure_coherence
  right_triangle := by dsimp [bicategoricalComp]; pure_coherence

instance : Inhabited (Adjunction (𝟙 a) (𝟙 a)) :=
  ⟨id a⟩

-- /- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option class.instance_max_depth -/
-- set_option class.instance_max_depth 60

set_option maxHeartbeats 500000 in
theorem right_adjoint_uniq_aux {f : a ⟶ b} {g₁ g₂ : b ⟶ a} (adj₁ : f ⊣ g₁) (adj₂ : f ⊣ g₂) :
    (𝟙 g₁ ⊗≫ g₁ ◁ adj₂.unit ⊗≫ adj₁.counit ▷ g₂ ⊗≫ 𝟙 g₂) ≫
        𝟙 g₂ ⊗≫ g₂ ◁ adj₁.unit ⊗≫ adj₂.counit ▷ g₁ ⊗≫ 𝟙 g₁ =
      𝟙 g₁ := by
  calc
    _ =
        𝟙 g₁ ⊗≫
          g₁ ◁ adj₂.unit ⊗≫
            (adj₁.counit ▷ (g₂ ≫ 𝟙 a) ≫ 𝟙 b ◁ g₂ ◁ adj₁.unit) ⊗≫ adj₂.counit ▷ g₁ ⊗≫ 𝟙 g₁ := ?_
    _ =
        𝟙 g₁ ⊗≫
          g₁ ◁ (adj₂.unit ▷ 𝟙 a ≫ (f ≫ g₂) ◁ adj₁.unit) ⊗≫
            (adj₁.counit ▷ (g₂ ≫ f) ≫ 𝟙 b ◁ adj₂.counit) ▷ g₁ ⊗≫ 𝟙 g₁ := ?_
    _ =
        𝟙 g₁ ⊗≫
          g₁ ◁ adj₁.unit ⊗≫
            g₁ ◁ (leftZigzag adj₂.unit adj₂.counit) ▷ g₁ ⊗≫ adj₁.counit ▷ g₁ ⊗≫ 𝟙 g₁ := ?_
    _ = 𝟙 g₁ ⊗≫ (rightZigzag adj₁.unit adj₁.counit) ⊗≫ 𝟙 g₁ := ?_
    _ = _ := ?_
  · dsimp [bicategoricalComp]; coherence
  · rw [← whisker_exchange]; dsimp [bicategoricalComp]; coherence
  · simp_rw [← whisker_exchange]; dsimp [bicategoricalComp]; coherence
  · rw [left_triangle]; dsimp [bicategoricalComp]; coherence
  · rw [right_triangle]; dsimp [bicategoricalComp]; coherence

set_option maxHeartbeats 500000 in
theorem left_adjoint_uniq_aux {f₁ f₂ : a ⟶ b} {g : b ⟶ a} (adj₁ : f₁ ⊣ g) (adj₂ : f₂ ⊣ g) :
    (𝟙 f₁ ⊗≫ adj₂.unit ▷ f₁ ⊗≫ f₂ ◁ adj₁.counit ⊗≫ 𝟙 f₂) ≫
        𝟙 f₂ ⊗≫ adj₁.unit ▷ f₂ ⊗≫ f₁ ◁ adj₂.counit ⊗≫ 𝟙 f₁ =
      𝟙 f₁ :=
  by
  calc
    _ =
        𝟙 f₁ ⊗≫
          adj₂.unit ▷ f₁ ⊗≫
            (𝟙 a ◁ f₂ ◁ adj₁.counit ≫ adj₁.unit ▷ (f₂ ≫ 𝟙 b)) ⊗≫ f₁ ◁ adj₂.counit ⊗≫ 𝟙 f₁ :=
      ?_
    _ =
        𝟙 f₁ ⊗≫
          (𝟙 a ◁ adj₂.unit ≫ adj₁.unit ▷ (f₂ ≫ g)) ▷ f₁ ⊗≫
            f₁ ◁ ((g ≫ f₂) ◁ adj₁.counit ≫ adj₂.counit ▷ 𝟙 b) ⊗≫ 𝟙 f₁ :=
      ?_
    _ =
        𝟙 f₁ ⊗≫
          adj₁.unit ▷ f₁ ⊗≫
            f₁ ◁ (rightZigzag adj₂.unit adj₂.counit) ▷ f₁ ⊗≫ f₁ ◁ adj₁.counit ⊗≫ 𝟙 f₁ :=
      ?_
    _ = 𝟙 f₁ ⊗≫ (leftZigzag adj₁.unit adj₁.counit) ⊗≫ 𝟙 f₁ := ?_
    _ = _ := ?_
  · dsimp [bicategoricalComp]; coherence
  · rw [whisker_exchange]; dsimp [bicategoricalComp]; coherence
  · simp_rw [whisker_exchange]; dsimp [bicategoricalComp]; coherence
  · rw [right_triangle]; dsimp [bicategoricalComp]; coherence
  · rw [left_triangle]; dsimp [bicategoricalComp]; coherence

/-- If `g₁` and `g₂` are both right adjoint to `f`, then they are isomorphic. -/
def right_adjoint_uniq {f : a ⟶ b} {g₁ g₂ : b ⟶ a} (adj₁ : f ⊣ g₁) (adj₂ : f ⊣ g₂) : g₁ ≅ g₂
    where
  hom := 𝟙 g₁ ⊗≫ g₁ ◁ adj₂.unit ⊗≫ adj₁.counit ▷ g₂ ⊗≫ 𝟙 g₂
  inv := 𝟙 g₂ ⊗≫ g₂ ◁ adj₁.unit ⊗≫ adj₂.counit ▷ g₁ ⊗≫ 𝟙 g₁
  hom_inv_id := right_adjoint_uniq_aux adj₁ adj₂
  inv_hom_id := right_adjoint_uniq_aux adj₂ adj₁

/-- If `f₁` and `f₂` are both left adjoint to `g`, then they are isomorphic. -/
def left_adjoint_uniq {f₁ f₂ : a ⟶ b} {g : b ⟶ a} (adj₁ : f₁ ⊣ g) (adj₂ : f₂ ⊣ g) : f₁ ≅ f₂
    where
  hom := 𝟙 f₁ ⊗≫ adj₂.unit ▷ f₁ ⊗≫ f₂ ◁ adj₁.counit ⊗≫ 𝟙 f₂
  inv := 𝟙 f₂ ⊗≫ adj₁.unit ▷ f₂ ⊗≫ f₁ ◁ adj₂.counit ⊗≫ 𝟙 f₁
  hom_inv_id := left_adjoint_uniq_aux adj₁ adj₂
  inv_hom_id := left_adjoint_uniq_aux adj₂ adj₁

section Composition

variable {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}

/-- Auxiliary definition for `adjunction.comp`. -/
@[simp]
def compunit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : 𝟙 a ⟶ (f₁ ≫ f₂) ≫ g₂ ≫ g₁ :=
  𝟙 _ ⊗≫ adj₁.unit ⊗≫ f₁ ◁ adj₂.unit ▷ g₁ ⊗≫ 𝟙 _

/-- Auxiliary definition for `adjunction.comp`. -/
@[simp]
def compCounit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : (g₂ ≫ g₁) ≫ f₁ ≫ f₂ ⟶ 𝟙 c :=
  𝟙 _ ⊗≫ g₂ ◁ adj₁.counit ▷ f₂ ⊗≫ adj₂.counit ⊗≫ 𝟙 _

open Mathlib.Tactic.BicategoryCoherence in
set_option maxHeartbeats 800000 in
theorem comp_left_triangle_aux (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    leftZigzag (compunit adj₁ adj₂) (compCounit adj₁ adj₂) = (λ_ _).hom ≫ (ρ_ _).inv :=
  by
  calc
    _ =
        𝟙 _ ⊗≫
          adj₁.unit ▷ (f₁ ≫ f₂) ⊗≫
            f₁ ◁ (adj₂.unit ▷ (g₁ ≫ f₁) ≫ (f₂ ≫ g₂) ◁ adj₁.counit) ▷ f₂ ⊗≫
              (f₁ ≫ f₂) ◁ adj₂.counit ⊗≫ 𝟙 _ :=
      ?_
    _ =
        𝟙 _ ⊗≫
          (leftZigzag adj₁.unit adj₁.counit) ▷ f₂ ⊗≫
            f₁ ◁ (leftZigzag adj₂.unit adj₂.counit) ⊗≫ 𝟙 _ :=
      ?_
    _ = _ := ?_
  · dsimp [bicategoricalComp, BicategoricalCoherence.hom, BicategoricalCoherence.hom']; simp; coherence
  · rw [← whisker_exchange]; dsimp [bicategoricalComp]; coherence
  · simp_rw [left_triangle]; dsimp [bicategoricalComp]; coherence

open Mathlib.Tactic.BicategoryCoherence in
set_option maxHeartbeats 800000 in
theorem comp_right_triangle_aux (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    rightZigzag (compunit adj₁ adj₂) (compCounit adj₁ adj₂) = (ρ_ _).hom ≫ (λ_ _).inv :=
  by
  calc
    _ =
        𝟙 _ ⊗≫
          (g₂ ≫ g₁) ◁ adj₁.unit ⊗≫
            g₂ ◁ ((g₁ ≫ f₁) ◁ adj₂.unit ≫ adj₁.counit ▷ (f₂ ≫ g₂)) ▷ g₁ ⊗≫
              adj₂.counit ▷ (g₂ ≫ g₁) ⊗≫ 𝟙 _ :=
      ?_
    _ =
        𝟙 _ ⊗≫
          g₂ ◁ (rightZigzag adj₁.unit adj₁.counit) ⊗≫
            (rightZigzag adj₂.unit adj₂.counit) ▷ g₁ ⊗≫ 𝟙 _ :=
      ?_
    _ = _ := ?_
  · dsimp [bicategoricalComp, BicategoricalCoherence.hom, BicategoricalCoherence.hom']; simp; coherence
  · rw [whisker_exchange]; dsimp [bicategoricalComp]; coherence
  · simp_rw [right_triangle]; dsimp [bicategoricalComp]; coherence

/-- Composition of adjunctions. -/
def comp (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : f₁ ≫ f₂ ⊣ g₂ ≫ g₁
    where
  unit := compunit adj₁ adj₂
  counit := compCounit adj₁ adj₂
  left_triangle := by apply comp_left_triangle_aux
  right_triangle := by apply comp_right_triangle_aux

end Composition

end Adjunction

noncomputable section

variable (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)

@[simp]
def leftZigzagIso (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :=
  whiskerRightIso η f ≪⊗≫ whiskerLeftIso f ε

@[simp]
def rightZigzagIso (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :=
  whiskerLeftIso g η ≪⊗≫ whiskerRightIso ε g

theorem leftZigzagIso_hom : (leftZigzagIso η ε).hom = leftZigzag η.hom ε.hom :=
  rfl

theorem rightZigzagIso_hom : (rightZigzagIso η ε).hom = rightZigzag η.hom ε.hom :=
  rfl

theorem leftZigzagIso_inv : (leftZigzagIso η ε).inv = rightZigzag ε.inv η.inv := by
  simp [bicategoricalComp, bicategoricalIsoComp]

theorem rightZigzagIso_inv : (rightZigzagIso η ε).inv = leftZigzag ε.inv η.inv := by
  simp [bicategoricalComp, bicategoricalIsoComp]

theorem leftZigzagIso_symm : (leftZigzagIso η ε).symm = rightZigzagIso ε.symm η.symm :=
  Iso.ext (leftZigzagIso_inv η ε)

theorem rightZigzagIso_symm : (rightZigzagIso η ε).symm = leftZigzagIso ε.symm η.symm :=
  Iso.ext (rightZigzagIso_inv η ε)

set_option maxHeartbeats 1000000 in
theorem right_triangle_of_left_triangle {η : 𝟙 a ≅ f ≫ g} {ε : g ≫ f ≅ 𝟙 b} :
    leftZigzagIso η ε = λ_ f ≪≫ (ρ_ f).symm → rightZigzagIso η ε = ρ_ g ≪≫ (λ_ g).symm :=
  by
  intro H
  replace H : leftZigzag η.hom ε.hom = (λ_ f).hom ≫ (ρ_ f).inv := congr_arg Iso.hom H
  apply Iso.ext
  dsimp [bicategoricalIsoComp] at H ⊢
  calc
    _ = 𝟙 _ ⊗≫ g ◁ η.hom ⊗≫ ε.hom ▷ g ⊗≫ 𝟙 (g ≫ 𝟙 a) ⊗≫ 𝟙 _ := ?_
    _ = 𝟙 _ ⊗≫ g ◁ η.hom ⊗≫ ε.hom ▷ g ⊗≫ g ◁ (η.hom ≫ η.inv) ⊗≫ 𝟙 _ := ?_
    _ = 𝟙 _ ⊗≫ g ◁ η.hom ⊗≫ ε.hom ▷ g ⊗≫ g ◁ η.hom ⊗≫ (ε.hom ≫ ε.inv) ▷ g ⊗≫ g ◁ η.inv ⊗≫ 𝟙 _ :=
      ?_
    _ =
        𝟙 _ ⊗≫
          g ◁ η.hom ⊗≫
            (ε.hom ▷ (g ≫ 𝟙 a) ≫ 𝟙 b ◁ g ◁ η.hom) ⊗≫ ε.hom ▷ g ⊗≫ ε.inv ▷ g ⊗≫ g ◁ η.inv ⊗≫ 𝟙 _ :=
      ?_
    _ =
        𝟙 _ ⊗≫
          g ◁ (η.hom ▷ 𝟙 a ≫ (f ≫ g) ◁ η.hom) ⊗≫
            ε.hom ▷ (g ≫ f ≫ g) ⊗≫ ε.hom ▷ g ⊗≫ ε.inv ▷ g ⊗≫ g ◁ η.inv ⊗≫ 𝟙 _ :=
      ?_
    _ =
        𝟙 _ ⊗≫
          g ◁ η.hom ⊗≫
            g ◁ η.hom ▷ f ▷ g ⊗≫
              (ε.hom ▷ (g ≫ f) ≫ 𝟙 b ◁ ε.hom) ▷ g ⊗≫ ε.inv ▷ g ⊗≫ g ◁ η.inv ⊗≫ 𝟙 _ :=
      ?_
    _ =
        𝟙 _ ⊗≫
          g ◁ η.hom ⊗≫
            g ◁ (η.hom ▷ f ⊗≫ f ◁ ε.hom) ▷ g ⊗≫ ε.hom ▷ g ⊗≫ ε.inv ▷ g ⊗≫ g ◁ η.inv ⊗≫ 𝟙 _ :=
      ?_
    _ = 𝟙 _ ⊗≫ g ◁ η.hom ⊗≫ (ε.hom ≫ ε.inv) ▷ g ⊗≫ g ◁ η.inv ⊗≫ 𝟙 _ := ?_
    _ = 𝟙 _ ⊗≫ g ◁ (η.hom ≫ η.inv) ⊗≫ 𝟙 _ := ?_
    _ = _ := ?_
  · rw [← comp_id (ε.hom ▷ g)]; dsimp [bicategoricalComp]; coherence
  · rw [Iso.hom_inv_id η, whiskerLeft_id]
  · rw [Iso.hom_inv_id ε]; dsimp [bicategoricalComp]; coherence
  · dsimp [bicategoricalComp]; coherence
  · rw [← whisker_exchange]; dsimp [bicategoricalComp]; coherence
  · rw [← whisker_exchange]; dsimp [bicategoricalComp]; coherence
  · rw [← whisker_exchange]; dsimp [bicategoricalComp]; coherence
  · rw [H]; dsimp [bicategoricalComp]; coherence
  · rw [Iso.hom_inv_id ε]; dsimp [bicategoricalComp]; coherence
  · rw [Iso.hom_inv_id η]; dsimp [bicategoricalComp]; coherence

theorem left_triangle_iff_right_triangle {η : 𝟙 a ≅ f ≫ g} {ε : g ≫ f ≅ 𝟙 b} :
    leftZigzagIso η ε = λ_ f ≪≫ (ρ_ f).symm ↔ rightZigzagIso η ε = ρ_ g ≪≫ (λ_ g).symm :=
  Iff.intro right_triangle_of_left_triangle
    (by
      intro H
      rw [← Iso.symm_eq_iff] at H ⊢
      rw [leftZigzagIso_symm]
      rw [rightZigzagIso_symm] at H
      exact right_triangle_of_left_triangle H)

def adjointifyUnit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : 𝟙 a ≅ f ≫ g :=
  η ≪≫ whiskerRightIso ((ρ_ f).symm ≪≫ rightZigzagIso ε.symm η.symm ≪≫ λ_ f) g

def adjointifyCounit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : g ≫ f ≅ 𝟙 b :=
  whiskerLeftIso g ((ρ_ f).symm ≪≫ rightZigzagIso ε.symm η.symm ≪≫ λ_ f) ≪≫ ε

set_option maxHeartbeats 1600000 in
@[simp]
theorem adjointifyCounit_symm (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
    (adjointifyCounit η ε).symm = adjointifyUnit ε.symm η.symm :=
  by
  apply Iso.ext
  rw [← cancel_mono (adjointifyUnit ε.symm η.symm).inv, Iso.hom_inv_id]
  dsimp [adjointifyUnit, adjointifyCounit, bicategoricalIsoComp]
  rw [← cancel_mono ε.inv, ← cancel_epi ε.hom]
  simp_rw [assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc]
  simp only [id_whiskerRight, id_comp, IsIso.Iso.inv_inv]
  calc
    _ =
        𝟙 _ ⊗≫
          g ◁ η.hom ▷ f ⊗≫
            (𝟙 b ◁ (g ≫ f) ◁ ε.hom ≫ ε.inv ▷ ((g ≫ f) ≫ 𝟙 b)) ⊗≫ (g ◁ η.inv) ▷ f ⊗≫ 𝟙 _ :=
      ?_
    _ =
        𝟙 _ ⊗≫
          (𝟙 b ◁ g ◁ η.hom ≫ ε.inv ▷ (g ≫ f ≫ g)) ▷ f ⊗≫
            g ◁ ((f ≫ g) ◁ f ◁ ε.hom ≫ η.inv ▷ (f ≫ 𝟙 b)) ⊗≫ 𝟙 _ :=
      ?_
    _ =
        𝟙 _ ⊗≫
          ε.inv ▷ g ▷ f ⊗≫ g ◁ ((f ≫ g) ◁ η.hom ≫ η.inv ▷ (f ≫ g)) ▷ f ⊗≫ g ◁ f ◁ ε.hom ⊗≫ 𝟙 _ :=
      ?_
    _ = 𝟙 _ ⊗≫ ε.inv ▷ g ▷ f ⊗≫ g ◁ (η.inv ≫ η.hom) ▷ f ⊗≫ g ◁ f ◁ ε.hom ⊗≫ 𝟙 _ := ?_
    _ = 𝟙 _ ⊗≫ (ε.inv ▷ (g ≫ f) ≫ (g ≫ f) ◁ ε.hom) ⊗≫ 𝟙 _ := ?_
    _ = 𝟙 _ ⊗≫ (ε.hom ≫ ε.inv) ⊗≫ 𝟙 _ := ?_
    _ = _ := ?_
  · dsimp [bicategoricalComp]; coherence
  · rw [whisker_exchange]; dsimp [bicategoricalComp]; coherence
  · rw [whisker_exchange, whisker_exchange]; dsimp [bicategoricalComp]; coherence
  · rw [whisker_exchange]; dsimp [bicategoricalComp]; coherence
  · rw [Iso.inv_hom_id]; dsimp [bicategoricalComp]; coherence
  · rw [← whisker_exchange]; dsimp [bicategoricalComp]; coherence
  · simp [bicategoricalComp]

@[simp]
theorem adjointifyUnit_symm (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
    (adjointifyUnit η ε).symm = adjointifyCounit ε.symm η.symm :=
  Iso.symm_eq_iff.mpr (adjointifyCounit_symm ε.symm η.symm).symm

set_option maxHeartbeats 500000 in
theorem adjointifyCounit_left_triangle (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
    leftZigzagIso η (adjointifyCounit η ε) = λ_ f ≪≫ (ρ_ f).symm :=
  by
  apply Iso.ext
  dsimp [adjointifyCounit, bicategoricalIsoComp]
  calc
    _ = 𝟙 _ ⊗≫ (η.hom ▷ (f ≫ 𝟙 b) ≫ (f ≫ g) ◁ f ◁ ε.inv) ⊗≫ f ◁ g ◁ η.inv ▷ f ⊗≫ f ◁ ε.hom := ?_
    _ = 𝟙 _ ⊗≫ f ◁ ε.inv ⊗≫ (η.hom ▷ (f ≫ g) ≫ (f ≫ g) ◁ η.inv) ▷ f ⊗≫ f ◁ ε.hom := ?_
    _ = 𝟙 _ ⊗≫ f ◁ ε.inv ⊗≫ (η.inv ≫ η.hom) ▷ f ⊗≫ f ◁ ε.hom := ?_
    _ = 𝟙 _ ⊗≫ f ◁ (ε.inv ≫ ε.hom) := ?_
    _ = _ := ?_
  · dsimp [bicategoricalComp]; coherence
  · rw [← whisker_exchange η.hom (f ◁ ε.inv)]; dsimp [bicategoricalComp]; coherence
  · rw [← whisker_exchange η.hom η.inv]; dsimp [bicategoricalComp]; coherence
  · rw [Iso.inv_hom_id]; dsimp [bicategoricalComp]; coherence
  · rw [Iso.inv_hom_id]; dsimp [bicategoricalComp]; coherence

theorem adjointifyUnit_right_triangle (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
    rightZigzagIso (adjointifyUnit η ε) ε = ρ_ g ≪≫ (λ_ g).symm :=
  by
  rw [← Iso.symm_eq_iff, rightZigzagIso_symm, adjointifyUnit_symm]
  exact adjointifyCounit_left_triangle ε.symm η.symm

structure Equivalence (a b : B) where
  hom : a ⟶ b
  inv : b ⟶ a
  unit : 𝟙 a ≅ hom ≫ inv
  counit : inv ≫ hom ≅ 𝟙 b
  left_triangle : leftZigzagIso unit counit = λ_ hom ≪≫ (ρ_ hom).symm := by aesop_cat

scoped infixr:10 " ≌ " => Bicategory.Equivalence

namespace Equivalence

attribute [simp] left_triangle

@[simp]
theorem right_triangle (f : a ≌ b) :
    rightZigzagIso f.unit f.counit = ρ_ f.inv ≪≫ (λ_ f.inv).symm :=
  right_triangle_of_left_triangle f.left_triangle

open Mathlib.Tactic.BicategoryCoherence in
def id (a : B) : a ≌ a :=
  ⟨_, _, (ρ_ _).symm, ρ_ _, by ext; dsimp [bicategoricalIsoComp, BicategoricalCoherence.hom, BicategoricalCoherence.hom']; coherence⟩

instance : Inhabited (Equivalence a a) :=
  ⟨id a⟩

def mkOfAdjointifyCounit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : a ≌ b
    where
  hom := f
  inv := g
  unit := η
  counit := adjointifyCounit η ε
  left_triangle := adjointifyCounit_left_triangle η ε

def mkOfAdjointifyunit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : a ≌ b
    where
  hom := f
  inv := g
  unit := adjointifyUnit η ε
  counit := ε
  left_triangle := left_triangle_iff_right_triangle.mpr (adjointifyUnit_right_triangle η ε)

end Equivalence

def Adjunction.ofEquivalence (f : a ≌ b) : f.hom ⊣ f.inv
    where
  unit := f.unit.hom
  counit := f.counit.hom
  left_triangle := congr_arg Iso.hom f.left_triangle
  right_triangle := congr_arg Iso.hom f.right_triangle

def Adjunction.ofEquivalenceSymm (f : a ≌ b) : f.inv ⊣ f.hom
    where
  unit := f.counit.inv
  counit := f.unit.inv
  left_triangle := rightZigzagIso_inv f.unit f.counit ▸ congr_arg Iso.inv f.right_triangle
  right_triangle := leftZigzagIso_inv f.unit f.counit ▸ congr_arg Iso.inv f.left_triangle

end

end Bicategory

end CategoryTheory
