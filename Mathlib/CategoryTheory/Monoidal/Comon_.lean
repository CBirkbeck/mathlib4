/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Braided.Opposite
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The category of comonoids in a monoidal category.

We define comonoids in a monoidal category `C`,
and show that they are equivalently monoid objects in the opposite category.

We construct the monoidal structure on `Comon_Cat C`, when `C` is braided.

An oplax monoidal functor takes comonoid objects to comonoid objects.
That is, a oplax monoidal functor `F : C ⥤ D` induces a functor `Comon_Cat C ⥤ Comon_Cat D`.

## TODO
* Comonoid objects in `C` are "just"
  oplax monoidal functors from the trivial monoidal category to `C`.
-/

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- A comonoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called a "coalgebra object".
-/
class Comon_ (X : C) where
  /-- The counit morphism of a comonoid object. -/
  counit : X ⟶ 𝟙_ C
  /-- The comultiplication morphism of a comonoid object. -/
  comul : X ⟶ X ⊗ X
  counit_comul' : comul ≫ (counit ▷ X) = (λ_ X).inv := by aesop_cat
  comul_counit' : comul ≫ (X ◁ counit) = (ρ_ X).inv := by aesop_cat
  comul_assoc' : comul ≫ (X ◁ comul) = comul ≫ (comul ▷ X) ≫ (α_ X X X).hom := by aesop_cat

namespace Comon_

@[inherit_doc] scoped notation "Δ" => Comon_.comul
@[inherit_doc] scoped notation "ε" => Comon_.counit

@[reassoc, simp]
theorem counit_comul (X : C) [Comon_ X] : Δ ≫ (ε ▷ X) = (λ_ X).inv := counit_comul'

@[reassoc, simp]
theorem comul_counit (X : C) [Comon_ X] : Δ ≫ (X ◁ ε) = (ρ_ X).inv := comul_counit'

@[reassoc (attr := simp)]
theorem comul_assoc (X : C) [Comon_ X] : Δ ≫ (X ◁ Δ) = Δ ≫ (Δ ▷ X) ≫ (α_ X X X).hom := comul_assoc'

/-- The trivial comonoid object. We later show this is terminal in `Comon_Cat C`.
-/
@[simps]
instance trivial (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] : Comon_ (𝟙_ C) where
  counit := 𝟙 _
  comul := (λ_ _).inv
  comul_assoc' := by coherence
  counit_comul' := by coherence
  comul_counit' := by coherence

instance : Inhabited (Comon_ (𝟙_ C)) :=
  ⟨trivial C⟩

variable {M : C} [Comon_ M]

@[simp]
theorem counit_comul_hom {Z : C} (f : M ⟶ Z) : Δ ≫ (ε ⊗ f) = f ≫ (λ_ Z).inv := by
  rw [tensorHom_def, counit_comul_assoc, leftUnitor_inv_naturality]

@[simp]
theorem comul_counit_hom {Z : C} (f : M ⟶ Z) : Δ ≫ (f ⊗ ε) = f ≫ (ρ_ Z).inv := by
  rw [tensorHom_def', comul_counit_assoc, rightUnitor_inv_naturality]

theorem comul_assoc_flip : Δ ≫ (Δ ▷ M) = Δ ≫ (M ◁ Δ) ≫ (α_ M M M).inv := by simp

/-- A morphism of comonoid objects. -/
@[ext]
structure Hom (M N : C) [Comon_ M] [Comon_ N] where
  hom : M ⟶ N
  hom_counit : hom ≫ ε = ε := by aesop_cat
  hom_comul : hom ≫ Δ = Δ ≫ (hom ⊗ hom) := by aesop_cat

attribute [reassoc (attr := simp)] Hom.hom_counit Hom.hom_comul

/-- The identity morphism on a comonoid object. -/
@[simps]
def Hom.id (M : C) [Comon_ M] : Hom M M where
  hom := 𝟙 M

instance homInhabited (M : C) [Comon_ M] : Inhabited (Hom M M) :=
  ⟨Hom.id M⟩

/-- Composition of morphisms of comonoid objects. -/
@[simps]
def Hom.comp {M N O : C} [Comon_ M] [Comon_ N] [Comon_ O] (f : Hom M N) (g : Hom N O) :
    Hom M O where
  hom := f.hom ≫ g.hom

@[ext]
structure Iso (M N : C) [Comon_ M] [Comon_ N] where
  hom : Hom M N
  inv : Hom N M
  hom_inv_id : hom.hom ≫ inv.hom = 𝟙 M := by aesop_cat
  inv_hom_id : inv.hom ≫ hom.hom = 𝟙 N := by aesop_cat

attribute [simp] Iso.hom_inv_id Iso.inv_hom_id

end Comon_

structure Comon_Cat (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] where
  X : C
  [isComon_ : Comon_ X]

namespace Comon_Cat

open Comon_

attribute [instance] Comon_Cat.isComon_

instance : Inhabited (Comon_Cat C) :=
  ⟨⟨𝟙_ C⟩⟩

initialize_simps_projections Comon_Cat (-isComon_)

instance : Category.{v₁} (Comon_Cat C) where
  Hom M N := Comon_.Hom M.X N.X
  id M := Comon_.Hom.id M.X
  comp f g := Comon_.Hom.comp f g

@[simp]
theorem mk_X (X : Comon_Cat C) : Comon_Cat.mk X.X = X :=
  rfl

def mkHom {X Y : C} [Comon_ X] [Comon_ Y] (f : Comon_.Hom X Y) :
    mk X ⟶ mk Y :=
  f

@[simp]
theorem mkHom_hom {X Y : C} [Comon_ X] [Comon_ Y] (f : Hom X Y) : (mkHom f).hom = f.hom :=
  rfl

-- Porting note: added, as Hom.ext does not apply to a morphism.
@[ext]
lemma Hom.ext' {X Y : Comon_Cat C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g :=
  Hom.ext _ _ w

@[simp]
theorem id_hom' {M : Comon_Cat C} : (𝟙 M : Hom M.X M.X).hom = 𝟙 M.X :=
  rfl

@[simp]
theorem comp_hom' {M N K : Comon_Cat C} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[simps]
def mkIso {X Y : C} [Comon_ X] [Comon_ Y] (f : Comon_.Iso X Y) :
    mk X ≅ mk Y where
  hom := f.hom
  inv := f.inv

section

variable (C)

/-- The forgetful functor from comonoid objects to the ambient category. -/
@[simps]
def forget : Comon_Cat C ⥤ C where
  obj A := A.X
  map f := f.hom

end

instance forget_faithful : (forget C).Faithful where

instance {A B : C} [Comon_ A] [Comon_ B] (f : Hom A B)
    [e : IsIso ((forget C).map (Comon_Cat.mkHom f))] :
    IsIso f.hom :=
  e

instance {A B : Comon_Cat C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] :
    IsIso f.hom :=
  e

instance uniqueHomToTrivial (A : Comon_Cat C) : Unique (A ⟶ mk (𝟙_ C)) where
  default :=
  { hom := ε
    hom_comul := by dsimp; simp only [unitors_inv_equal, comul_counit_hom] }
  uniq f := by
    ext
    dsimp only [trivial_comul]
    rw [← Category.comp_id f.hom, ← Comon_.trivial_counit, f.hom_counit]

open CategoryTheory.Limits

instance : HasTerminal (Comon_Cat C) :=
  hasTerminal_of_unique (mk (𝟙_ C))

end Comon_Cat

namespace Comon_

/-- Construct an isomorphism of comonoids by giving an isomorphism between the underlying objects
and checking compatibility with counit and comultiplication only in the forward direction.
-/
@[simps]
def mkIso {M N : C} [Comon_ M] [Comon_ N] (f : M ≅ N) (f_counit : f.hom ≫ ε = ε)
    (f_comul : f.hom ≫ Δ = Δ ≫ (f.hom ⊗ f.hom)) :
    Iso M N where
  hom := { hom := f.hom }
  inv := {
    hom := f.inv
    hom_counit := by rw [← f_counit]; simp
    hom_comul := by
      rw [← cancel_epi f.hom]
      slice_rhs 1 2 => rw [f_comul]
      simp }

end Comon_

open Comon_

namespace CategoryTheory.OplaxMonoidalFunctor

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

@[simps!]
instance (F : OplaxMonoidalFunctor C D) {A : C} [Comon_ A] : Comon_ (F.obj A) where
  counit := F.map ε ≫ F.η
  comul := F.map Δ ≫ F.δ _ _
  counit_comul' := by
    simp_rw [comp_whiskerRight, Category.assoc, F.δ_natural_left_assoc, F.left_unitality,
      ← F.map_comp_assoc, counit_comul]
  comul_counit' := by
        simp_rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, F.δ_natural_right_assoc,
          F.right_unitality, ← F.map_comp_assoc, comul_counit]
  comul_assoc' := by
    simp_rw [comp_whiskerRight, Category.assoc, F.δ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, F.δ_natural_right_assoc,
      ← F.map_comp_assoc, comul_assoc, F.map_comp, Category.assoc, F.associativity]

/-- A oplax monoidal functor takes comonoid objects to comonoid objects.

That is, a oplax monoidal functor F : C ⥤ D induces a functor Comon_Cat C ⥤ Comon_ D.
-/
@[simps]
def mapComon (F : OplaxMonoidalFunctor C D) : Comon_Cat C ⥤ Comon_Cat D where
  obj A := Comon_Cat.mk (F.obj A.X)
  map {A B} f := Comon_Cat.mkHom
    { hom := F.map f.hom
      hom_counit := by dsimp; rw [← F.map_comp_assoc, f.hom_counit]
      hom_comul := by
        dsimp
        rw [Category.assoc, F.δ_natural, ← F.map_comp_assoc, ← F.map_comp_assoc, f.hom_comul] }

-- TODO We haven't yet set up the category structure on `OplaxMonoidalFunctor C D`
-- and so can't state `mapComonFunctor : OplaxMonoidalFunctor C D ⥤ Comon_ C ⥤ Comon_ D`.

end CategoryTheory.OplaxMonoidalFunctor
