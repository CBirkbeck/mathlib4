/-
Copyright (c) 2023 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Adjunctions in bicategories

For 1-morphisms `f : a ⟶ b` and `g : b ⟶ a` in a bicategory, an adjunction between `f` and `g`
consists of a pair of 2-morphism `η : 𝟙 a ⟶ f ≫ g` and `ε : g ≫ f ⟶ 𝟙 b` satisfying the triangle
identities. The 2-morphism `η` is called the unit and `ε` is called the counit.

## Main definitions

* `Bicategory.Adjunction`: adjunctions between two 1-morphisms.
* `Bicategory.Equivalence`: adjoint equivalences between two objects.
* `Bicategory.mkOfAdjointifyCounit`: construct an adjoint equivalence from 2-isomorphisms
  `η : 𝟙 a ≅ f ≫ g` and `ε : g ≫ f ≅ 𝟙 b`, by upgrading `ε` to a counit.

## TODO

* `Bicategory.mkOfAdjointifyUnit`: construct an adjoint equivalence from 2-isomorphisms
  `η : 𝟙 a ≅ f ≫ g` and `ε : g ≫ f ≅ 𝟙 b`, by upgrading `η` to a unit.
-/

namespace CategoryTheory

namespace Bicategory

open Category

open scoped Bicategory

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
abbrev leftZigzagable (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :=
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
abbrev rightZigzagable (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :=
  g ◁ η ⊗≫ ε ▷ g

theorem rightZigzagable_idempotent_of_left_triangle
    (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) (h : leftZigzagable η ε = (λ_ _).hom ≫ (ρ_ _).inv) :
    rightZigzagable η ε ⊗≫ rightZigzagable η ε = rightZigzagable η ε := by
  dsimp only [rightZigzagable]
  calc
    _ = g ◁ η ⊗≫ ((ε ▷ g ▷ 𝟙 a) ≫ (𝟙 b ≫ g) ◁ η) ⊗≫ ε ▷ g := by
      bicategory
    _ = 𝟙 _ ⊗≫ g ◁ (η ▷ 𝟙 a ≫ (f ≫ g) ◁ η) ⊗≫ (ε ▷ (g ≫ f) ≫ 𝟙 b ◁ ε) ▷ g ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = g ◁ η ⊗≫ g ◁ leftZigzagable η ε ▷ g ⊗≫ ε ▷ g := by
      rw [← whisker_exchange,  ← whisker_exchange, leftZigzagable]; bicategory
    _ = g ◁ η ⊗≫ ε ▷ g := by
      rw [h]; bicategory

/-- Adjunction between two 1-morphisms. -/
structure Adjunction (f : a ⟶ b) (g : b ⟶ a) where
  /-- The unit of an adjunction. -/
  unit : 𝟙 a ⟶ f ≫ g
  /-- The counit of an adjunction. -/
  counit : g ≫ f ⟶ 𝟙 b
  /-- The composition of the unit and the counit is equal to the identity up to unitors. -/
  left_triangle : leftZigzagable unit counit = (λ_ _).hom ≫ (ρ_ _).inv := by aesop_cat
  /-- The composition of the unit and the counit is equal to the identity up to unitors. -/
  right_triangle : rightZigzagable unit counit = (ρ_ _).hom ≫ (λ_ _).inv := by aesop_cat

@[inherit_doc] scoped infixr:15 " ⊣ " => Bicategory.Adjunction

namespace Adjunction

attribute [simp] left_triangle right_triangle

-- attribute [local simp] leftZigzagable rightZigzagable

/-- Adjunction between identities. -/
def id (a : B) : 𝟙 a ⊣ 𝟙 a where
  unit := (ρ_ _).inv
  counit := (ρ_ _).hom
  left_triangle := by bicategory_coherence
  right_triangle := by bicategory_coherence

instance : Inhabited (Adjunction (𝟙 a) (𝟙 a)) :=
  ⟨id a⟩

section Composition

variable {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}

/-- Auxiliary definition for `adjunction.comp`. -/
@[simp]
def compUnit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : 𝟙 a ⟶ (f₁ ≫ f₂) ≫ g₂ ≫ g₁ :=
  adj₁.unit ⊗≫ f₁ ◁ adj₂.unit ▷ g₁ ⊗≫ 𝟙 _

/-- Auxiliary definition for `adjunction.comp`. -/
@[simp]
def compCounit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : (g₂ ≫ g₁) ≫ f₁ ≫ f₂ ⟶ 𝟙 c :=
  𝟙 _ ⊗≫ g₂ ◁ adj₁.counit ▷ f₂ ⊗≫ adj₂.counit

theorem comp_left_triangle_aux (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    leftZigzagable (compUnit adj₁ adj₂) (compCounit adj₁ adj₂) = (λ_ _).hom ≫ (ρ_ _).inv := by
  calc
    _ = 𝟙 _ ⊗≫
          adj₁.unit ▷ (f₁ ≫ f₂) ⊗≫
            f₁ ◁ (adj₂.unit ▷ (g₁ ≫ f₁) ≫ (f₂ ≫ g₂) ◁ adj₁.counit) ▷ f₂ ⊗≫
              (f₁ ≫ f₂) ◁ adj₂.counit ⊗≫ 𝟙 _ := by
      dsimp only [compUnit, compCounit]; bicategory
    _ = 𝟙 _ ⊗≫
          (leftZigzagable adj₁.unit adj₁.counit) ▷ f₂ ⊗≫
            f₁ ◁ (leftZigzagable adj₂.unit adj₂.counit) ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = _ := by
      simp_rw [left_triangle]; bicategory

theorem comp_right_triangle_aux (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    rightZigzagable (compUnit adj₁ adj₂) (compCounit adj₁ adj₂) = (ρ_ _).hom ≫ (λ_ _).inv := by
  calc
    _ = 𝟙 _ ⊗≫
          (g₂ ≫ g₁) ◁ adj₁.unit ⊗≫
            g₂ ◁ ((g₁ ≫ f₁) ◁ adj₂.unit ≫ adj₁.counit ▷ (f₂ ≫ g₂)) ▷ g₁ ⊗≫
              adj₂.counit ▷ (g₂ ≫ g₁) ⊗≫ 𝟙 _ := by
      dsimp only [compUnit, compCounit]; bicategory
    _ = 𝟙 _ ⊗≫
          g₂ ◁ (rightZigzagable adj₁.unit adj₁.counit) ⊗≫
            (rightZigzagable adj₂.unit adj₂.counit) ▷ g₁ ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]; bicategory
    _ = _ := by
      simp_rw [right_triangle]; bicategory

/-- Composition of adjunctions. -/
@[simps]
def comp (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : f₁ ≫ f₂ ⊣ g₂ ≫ g₁ where
  unit := compUnit adj₁ adj₂
  counit := compCounit adj₁ adj₂
  left_triangle := by apply comp_left_triangle_aux
  right_triangle := by apply comp_right_triangle_aux

end Composition

end Adjunction

noncomputable section

variable (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)

/-- The isomorphism version of `leftZigzagable`. -/
abbrev leftZigzagableIso (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :=
  whiskerRightIso η f ≪⊗≫ whiskerLeftIso f ε

/-- The isomorphism version of `rightZigzagable`. -/
abbrev rightZigzagableIso (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :=
  whiskerLeftIso g η ≪⊗≫ whiskerRightIso ε g

@[simp]
theorem leftZigzagableIso_hom : (leftZigzagableIso η ε).hom = leftZigzagable η.hom ε.hom :=
  rfl

@[simp]
theorem rightZigzagableIso_hom : (rightZigzagableIso η ε).hom = rightZigzagable η.hom ε.hom :=
  rfl

@[simp]
theorem leftZigzagableIso_inv : (leftZigzagableIso η ε).inv = rightZigzagable ε.inv η.inv := by
  simp [bicategoricalComp, bicategoricalIsoComp]

@[simp]
theorem rightZigzagableIso_inv : (rightZigzagableIso η ε).inv = leftZigzagable ε.inv η.inv := by
  simp [bicategoricalComp, bicategoricalIsoComp]

@[simp]
theorem leftZigzagableIso_symm : (leftZigzagableIso η ε).symm = rightZigzagableIso ε.symm η.symm :=
  Iso.ext (leftZigzagableIso_inv η ε)

@[simp]
theorem rightZigzagableIso_symm : (rightZigzagableIso η ε).symm = leftZigzagableIso ε.symm η.symm :=
  Iso.ext (rightZigzagableIso_inv η ε)

instance : IsIso (leftZigzagable η.hom ε.hom) :=
  inferInstanceAs <| IsIso (leftZigzagableIso η ε).hom

instance : IsIso (rightZigzagable η.hom ε.hom) :=
  inferInstanceAs <| IsIso (rightZigzagableIso η ε).hom

theorem right_triangle_of_left_triangle (h : leftZigzagable η.hom ε.hom = (λ_ f).hom ≫ (ρ_ f).inv) :
    rightZigzagable η.hom ε.hom = (ρ_ g).hom ≫ (λ_ g).inv := by
  rw [← cancel_epi (rightZigzagable η.hom ε.hom ≫ (λ_ g).hom ≫ (ρ_ g).inv)]
  calc
    _ = rightZigzagable η.hom ε.hom ⊗≫ rightZigzagable η.hom ε.hom := by bicategory
    _ = rightZigzagable η.hom ε.hom := rightZigzagable_idempotent_of_left_triangle _ _ h
    _ = _ := by simp

/-- An auxiliary definition for `mkOfAdjointifyCounit`. -/
def adjointifyCounit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : g ≫ f ≅ 𝟙 b :=
  whiskerLeftIso g ((ρ_ f).symm ≪≫ rightZigzagableIso ε.symm η.symm ≪≫ λ_ f) ≪≫ ε

theorem adjointifyCounit_left_triangle (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
    leftZigzagableIso η (adjointifyCounit η ε) = λ_ f ≪≫ (ρ_ f).symm := by
  apply Iso.ext
  dsimp [adjointifyCounit, bicategoricalIsoComp]
  calc
    _ = 𝟙 _ ⊗≫ (η.hom ▷ (f ≫ 𝟙 b) ≫ (f ≫ g) ◁ f ◁ ε.inv) ⊗≫
          f ◁ g ◁ η.inv ▷ f ⊗≫ f ◁ ε.hom := by
      bicategory
    _ = 𝟙 _ ⊗≫ f ◁ ε.inv ⊗≫ (η.hom ▷ (f ≫ g) ≫ (f ≫ g) ◁ η.inv) ▷ f ⊗≫ f ◁ ε.hom := by
      rw [← whisker_exchange η.hom (f ◁ ε.inv)]; bicategory
    _ = 𝟙 _ ⊗≫ f ◁ ε.inv ⊗≫ (η.inv ≫ η.hom) ▷ f ⊗≫ f ◁ ε.hom := by
      rw [← whisker_exchange η.hom η.inv]; bicategory
    _ = 𝟙 _ ⊗≫ f ◁ (ε.inv ≫ ε.hom) := by
      rw [Iso.inv_hom_id]; bicategory
    _ = _ := by
      rw [Iso.inv_hom_id]; bicategory

/-- Adjoint equivalences between two objects. -/
structure Equivalence (a b : B) where
  /-- A 1-morphism in one direction. -/
  hom : a ⟶ b
  /-- A 1-morphism in the other direction. -/
  inv : b ⟶ a
  /-- The composition `hom ≫ inv` is isomorphic to the identity. -/
  unit : 𝟙 a ≅ hom ≫ inv
  /-- The composition `inv ≫ hom` is isomorphic to the identity. -/
  counit : inv ≫ hom ≅ 𝟙 b
  /-- The composition of the unit and the counit is equal to the identity up to unitors. -/
  left_triangle : leftZigzagableIso unit counit = λ_ hom ≪≫ (ρ_ hom).symm := by aesop_cat

@[inherit_doc] scoped infixr:10 " ≌ " => Bicategory.Equivalence

namespace Equivalence

/-- The identity 1-morphism is an equivalence. -/
def id (a : B) : a ≌ a := ⟨_, _, (ρ_ _).symm, ρ_ _, by ext; simp [bicategoricalIsoComp]⟩

instance : Inhabited (Equivalence a a) := ⟨id a⟩

theorem left_triangle_hom (e : a ≌ b) :
    leftZigzagable e.unit.hom e.counit.hom = (λ_ e.hom).hom ≫ (ρ_ e.hom).inv :=
  congrArg Iso.hom e.left_triangle

theorem right_triangle (e : a ≌ b) :
    rightZigzagableIso e.unit e.counit = ρ_ e.inv ≪≫ (λ_ e.inv).symm :=
  Iso.ext (right_triangle_of_left_triangle e.unit e.counit e.left_triangle_hom)

theorem right_triangle_hom (e : a ≌ b) :
    rightZigzagable e.unit.hom e.counit.hom = (ρ_ e.inv).hom ≫ (λ_ e.inv).inv :=
  congrArg Iso.hom e.right_triangle

/-- Construct an adjoint equivalence from 2-isomorphisms by upgrading `ε` to a counit. -/
def mkOfAdjointifyCounit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : a ≌ b where
  hom := f
  inv := g
  unit := η
  counit := adjointifyCounit η ε
  left_triangle := adjointifyCounit_left_triangle η ε

end Equivalence

end

noncomputable
section

/-- A structure giving a chosen right adjoint of a 1-morphism `left`. -/
structure RightAdjoint (left : a ⟶ b) where
  /-- The right adjoint to `left`. -/
  right : b ⟶ a
  /-- The adjunction between `left` and `right`. -/
  adj : left ⊣ right

/-- The existence of a right adjoint of `f`. -/
class IsLeftAdjoint (left : a ⟶ b) : Prop where mk' ::
  nonempty : Nonempty (RightAdjoint left)

theorem IsLeftAdjoint.mk (adj : f ⊣ g) : IsLeftAdjoint f :=
  ⟨⟨g, adj⟩⟩

/-- Use the axiom of choice to extract a right adjoint from an `IsLeftAdjoint` instance. -/
def getRightAdjoint (f : a ⟶ b) [IsLeftAdjoint f] : RightAdjoint f :=
  Classical.choice IsLeftAdjoint.nonempty

/-- The right adjoint of a 1-morphism. -/
def rightAdjoint (f : a ⟶ b) [IsLeftAdjoint f] : b ⟶ a :=
  (getRightAdjoint f).right

/-- Evidence that `f⁺⁺` is a right adjoint of `f`. -/
def Adjunction.ofIsLeftAdjoint (f : a ⟶ b) [IsLeftAdjoint f] : f ⊣ rightAdjoint f :=
  (getRightAdjoint f).adj

/-- A structure giving a chosen left adjoint of a 1-morphism `right`. -/
structure LeftAdjoint (right : b ⟶ a) where
  /-- The left adjoint to `right`. -/
  left : a ⟶ b
  /-- The adjunction between `left` and `right`. -/
  adj : left ⊣ right

/-- The existence of a left adjoint of `f`. -/
class IsRightAdjoint (right : b ⟶ a) : Prop where mk' ::
  nonempty : Nonempty (LeftAdjoint right)

theorem IsRightAdjoint.mk (adj : f ⊣ g) : IsRightAdjoint g :=
  ⟨⟨f, adj⟩⟩

/-- Use the axiom of choice to extract a left adjoint from an `IsRightAdjoint` instance. -/
def getLeftAdjoint (f : b ⟶ a) [IsRightAdjoint f] : LeftAdjoint f :=
  Classical.choice IsRightAdjoint.nonempty

/-- The left adjoint of a 1-morphism. -/
def leftAdjoint (f : b ⟶ a) [IsRightAdjoint f] : a ⟶ b :=
  (getLeftAdjoint f).left

/-- Evidence that `f⁺` is a left adjoint of `f`. -/
def Adjunction.ofIsRightAdjoint (f : b ⟶ a) [IsRightAdjoint f] : leftAdjoint f ⊣ f :=
  (getLeftAdjoint f).adj

end

end Bicategory

end CategoryTheory
