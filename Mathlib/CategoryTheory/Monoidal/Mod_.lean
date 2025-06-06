/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Paul Lezeau, Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Action.Basic

/-!
# The category of module objects over a monoid object.
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory Mon_Class

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalLeftAction C D]

section Mod_Class

open Mon_Class

variable (M : C) [Mon_Class M]

open scoped MonoidalLeftAction
/-- Given an action of a monoidal category `C` on a category `D`,
an action of a monoid object `M` in `C` on an object `X` in `D` is the data of a
map `smul : M ⊙ X ⟶ X` that satisfies unitality and associativity with
multiplication.

See `MulAction` for the non-categorical version. -/
class Mod_Class (X : D) where
  /-- The action map -/
  smul : M ⊙ X ⟶ X
  /-- The identity acts trivially. -/
  one_smul' (X) : η ⊵ X ≫ smul = (υ_ X).hom := by aesop_cat
  /-- The action map is compatible with multiplication. -/
  mul_smul' (X) : μ ⊵ X ≫ smul = (σ_ M M X).hom ≫ M ⊴ smul ≫ smul := by aesop_cat

attribute [reassoc] Mod_Class.mul_smul' Mod_Class.one_smul'

@[inherit_doc] scoped[Mon_Class] notation "γ" => Mod_Class.smul
@[inherit_doc] scoped[Mon_Class] notation "γ["Y"]" => Mod_Class.smul (X := Y)
@[inherit_doc] scoped[Mon_Class] notation "γ["N","Y"]" =>
  Mod_Class.smul (M := N) (X := Y)

variable {M}

namespace Mod_Class

@[reassoc (attr := simp)]
theorem one_smul (X : D) [Mod_Class M X] :
    η ⊵ X ≫ γ[M,X] = (υ_[C] X).hom :=
  Mod_Class.one_smul' X

@[reassoc (attr := simp)]
theorem mul_smul (X : D) [Mod_Class M X] :
    μ ⊵ X ≫ γ = (σ_ M M X).hom ≫ M ⊴ γ ≫ γ := Mod_Class.mul_smul' X

theorem assoc_flip (X : D) [Mod_Class M X] : M ⊴ γ ≫ γ =
    (σ_ M M X).inv ≫ μ[M] ⊵ X ≫ γ := by
  simp

variable (M) in
/-- The action of a monoid object on itself. -/
-- See note [reducible non instances]
abbrev regular : Mod_Class M M where
  smul := μ

/-- If `C` acts monoidally on `D`, then every object of `D` is canonically a
module over the trivial monoid. -/
@[simps]
instance (X : D) : Mod_Class (𝟙_ C) X where
  smul := υ_ _|>.hom

@[ext]
theorem ext {X : C} (h₁ h₂ : Mod_Class M X) (H : h₁.smul = h₂.smul) :
    h₁ = h₂ := by
  cases h₁
  cases h₂
  subst H
  rfl

end Mod_Class

end Mod_Class

open scoped Mod_Class MonoidalLeftAction

variable (A : C) [Mon_Class A]
/-- A morphism in `D` is a morphism of `A`-module objects if it commutes with
the action maps -/
class IsMod_Hom {M N : D} [Mod_Class A M] [Mod_Class A N] (f : M ⟶ N) where
  smul_hom : γ[M] ≫ f = A ⊴ f ≫ γ[N] := by aesop_cat

attribute [reassoc (attr := simp)] IsMod_Hom.smul_hom

variable {M N O: D} [Mod_Class A M] [Mod_Class A N] [Mod_Class A O]

instance : IsMod_Hom A (𝟙 M) where

instance (f : M ⟶ N) (g : N ⟶ O) [IsMod_Hom A f] [IsMod_Hom A g] :
    IsMod_Hom A (f ≫ g) where

instance (f : M ≅ N) [IsMod_Hom A f.hom] :
   IsMod_Hom A f.inv where
  smul_hom := by simp [Iso.comp_inv_eq]

variable (D) in
/-- A module object for a monoid object in a monoidal category acting on the
ambient category. -/
structure Mod_ (A : C) [Mon_Class A] where
  /-- The underlying object in the ambient category -/
  X : D
  [mod : Mod_Class A X]

attribute [instance] Mod_.mod

namespace Mod_

variable {A : C} [Mon_Class A] (M : Mod_ D A)

theorem assoc_flip : A ⊴ γ ≫ γ = (σ_ A A M.X).inv ≫ μ ⊵ M.X ≫ γ := by simp

/-- A morphism of monoid objects. -/
@[ext]
structure Hom (M N : Mod_ D A) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  smul_hom : γ[M.X] ≫ hom = A ⊴ hom ≫ γ[N.X] := by aesop_cat

attribute [reassoc (attr := simp)] Hom.smul_hom

instance Hom.isMod_Hom {M N : Mod_ D A} (f : Hom M N) : IsMod_Hom A f.hom where

/-- An alternative constructor for `Mod_.Hom`, taking a morphism with an
`[IsMod_Hom]' instance. -/
@[simps]
def Hom.mk' {M N : Mod_ D A} (f : M.X ⟶ N.X) [IsMod_Hom A f] : Hom M N where
  hom := f

/-- An alternative constructor for `Mod_.Hom`,
taking a morphism with an `[IsMod_Hom]` instance between objects with
a `Mod_Class` instance (rather than bundled as `Mod_`). -/
@[simps!]
def Hom.mk'' {M N : D} [Mod_Class A M] [Mod_Class A N] (f : M ⟶ N)
    [IsMod_Hom A f] :
    Hom (.mk (A := A) M) (.mk (A := A) N) :=
  letI : IsMod_Hom A f := ⟨by simp⟩
  .mk' f

/-- The identity morphism on a module object. -/
@[simps]
def id (M : Mod_ D A) : Hom M M where hom := 𝟙 M.X

instance homInhabited (M : Mod_ D A) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of module object morphisms. -/
@[simps]
def comp {M N O : Mod_ D A} (f : Hom M N) (g : Hom N O) :
    Hom M O where
  hom := f.hom ≫ g.hom

instance : Category (Mod_ D A) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

@[simp]
theorem id_hom' (M : Mod_ D A) : (𝟙 M : M ⟶ M).hom = 𝟙 M.X := by
  rfl

@[simp]
theorem comp_hom' {M N K : Mod_ D A} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

variable (A)

/-- A monoid object as a module over itself. -/
@[simps]
def regular : Mod_ C A :=
  letI : Mod_Class A A := .regular A
  ⟨A⟩

instance : Inhabited (Mod_ C A) :=
  ⟨regular A⟩

/-- The forgetful functor from module objects to the ambient category. -/
@[simps]
def forget : Mod_ D A ⥤ D where
  obj A := A.X
  map f := f.hom

section comap

variable {A B : C} [Mon_Class A] [Mon_Class B] (f : A ⟶ B) [IsMon_Hom f]

open MonoidalLeftAction in
/-- When `M` is a `B`-module in `D` and `f : A ⟶ B` is a morphism of internal
monoid objects, `M` inherits an `A`-module structure via
"restriction of scalars", i.e `γ[A, M] = f.hom ⊵ M ≫ γ[B, M]`. -/
@[simps!]
def scalarRestriction (M : D) [Mod_Class B M] : Mod_Class A M where
  smul := f ⊵ M ≫ γ[B, M]
  one_smul' := by
    rw [← comp_actionHomLeft_assoc]
    rw [IsMon_Hom.one_hom, Mod_Class.one_smul]
  mul_smul' := by
    -- oh, for homotopy.io in a widget!
    slice_rhs 2 3 => rw [action_exchange]
    simp only [actionHomLeft_action_assoc, Category.assoc, Iso.hom_inv_id_assoc,
      actionHomRight_comp]
    slice_rhs 4 6 => rw [Mod_Class.assoc_flip]
    slice_rhs 2 4 => rw [← action_assoc]
    slice_rhs 1 2 => rw [← comp_actionHomLeft]
    rw [← comp_actionHomLeft, Category.assoc, ← comp_actionHomLeft_assoc,
      IsMon_Hom.mul_hom, tensorHom_def, Category.assoc]

open MonoidalLeftAction in
/-- If `g : M ⟶ N` is a `B`-linear morphisms of `B`-modules, then it induces an
`A`-linear morphism when `M` and `N` have an `A`-module structure obtained
by restricting scalars along a monoid morphism `A ⟶ B`. -/
@[simps!]
lemma scalarRestriction_isMod_Hom
    (M N : D) [Mod_Class B M] [Mod_Class B N] (g : M ⟶ N) [IsMod_Hom B g] :
    letI := scalarRestriction f M
    letI := scalarRestriction f N
    IsMod_Hom A g :=
  letI := scalarRestriction f M
  letI := scalarRestriction f N
  { smul_hom := by
      dsimp
      slice_rhs 1 2 => rw [action_exchange]
      slice_rhs 2 3 => rw [← IsMod_Hom.smul_hom]
      rw [Category.assoc] }

/-- A morphism of monoid objects induces a "restriction" or "comap" functor
between the categories of module objects.
-/
@[simps]
def comap {A B : C} [Mon_Class A] [Mon_Class B] (f : A ⟶ B) [IsMon_Hom f] :
    Mod_ D B ⥤ Mod_ D A where
  obj M :=
    letI := scalarRestriction f M.X
    ⟨M.X⟩
  map {M N} g :=
    letI := scalarRestriction_isMod_Hom f M.X N.X g.hom
    { hom := g.hom, smul_hom := this.smul_hom }

-- Lots more could be said about `comap`, e.g. how it interacts with
-- identities, compositions, and equalities of monoid object morphisms.

end comap

end Mod_
