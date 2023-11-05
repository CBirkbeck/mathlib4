/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Scott Morrison
-/
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.EqToHom
import Mathlib.Data.Sum.Basic

#align_import category_theory.pi.basic from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Categories of indexed families of objects.

We define the pointwise category structure on indexed families of objects in a category
(and also the dependent generalization).

-/

namespace CategoryTheory

universe w₀ w₁ w₂ v₁ v₂ u₁ u₂

variable {I : Type w₀} {J : Type w₁} (C : I → Type u₁) [∀ i, Category.{v₁} (C i)]


/-- `pi C` gives the cartesian product of an indexed family of categories.
-/
instance pi : Category.{max w₀ v₁} (∀ i, C i) where
  Hom X Y := ∀ i, X i ⟶ Y i
  id X i := 𝟙 (X i)
  comp f g i := f i ≫ g i

/-- This provides some assistance to typeclass search in a common situation,
which otherwise fails. (Without this `CategoryTheory.Pi.has_limit_of_has_limit_comp_eval` fails.)
-/
abbrev pi' {I : Type v₁} (C : I → Type u₁) [∀ i, Category.{v₁} (C i)] : Category.{v₁} (∀ i, C i) :=
  CategoryTheory.pi C

attribute [instance] pi'

namespace Pi

@[simp]
theorem id_apply (X : ∀ i, C i) (i) : (𝟙 X : ∀ i, X i ⟶ X i) i = 𝟙 (X i) :=
  rfl

@[simp]
theorem comp_apply {X Y Z : ∀ i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (i) :
    (f ≫ g : ∀ i, X i ⟶ Z i) i = f i ≫ g i :=
  rfl

-- Porting note: need to add an additional `ext` lemma.
@[ext]
lemma ext {X Y : ∀ i, C i} {f g : X ⟶ Y} (w : ∀ i, f i = g i) : f = g :=
  funext (w ·)

/--
The evaluation functor at `i : I`, sending an `I`-indexed family of objects to the object over `i`.
-/
@[simps]
def eval (i : I) : (∀ i, C i) ⥤ C i where
  obj f := f i
  map α := α i

section

variable {J : Type w₁}

/- Porting note: add this because Lean cannot see directly through the `∘` for
`Function.comp` -/

instance (f : J → I) : (j : J) → Category ((C ∘ f) j) := by
  dsimp
  infer_instance

/-- Pull back an `I`-indexed family of objects to a `J`-indexed family, along a function `J → I`.
-/
@[simps]
def comap (h : J → I) : (∀ i, C i) ⥤ (∀ j, C (h j)) where
  obj f i := f (h i)
  map α i := α (h i)

variable (I)

/-- The natural isomorphism between
pulling back a grading along the identity function,
and the identity functor. -/
@[simps]
def comapId : comap C (id : I → I) ≅ 𝟭 (∀ i, C i) where
  hom := { app := fun X => 𝟙 X }
  inv := { app := fun X => 𝟙 X }

example (g : J → I) : (j : J) → Category (C (g j)) := by infer_instance

variable {I}

variable {K : Type w₂}

/-- The natural isomorphism comparing between
pulling back along two successive functions, and
pulling back along their composition
-/
@[simps!]
def comapComp (f : K → J) (g : J → I) : comap C g ⋙ comap (C ∘ g) f ≅ comap C (g ∘ f) where
  hom :=
  { app := fun X b => 𝟙 (X (g (f b)))
    naturality := fun X Y f' => by simp only [comap, Function.comp]; funext; simp }
  inv :=
  { app := fun X b => 𝟙 (X (g (f b)))
    naturality := fun X Y f' => by simp only [comap, Function.comp]; funext; simp }

/-- The natural isomorphism between pulling back then evaluating, and just evaluating. -/
@[simps!]
def comapEvalIsoEval (h : J → I) (j : J) : comap C h ⋙ eval (C ∘ h) j ≅ eval C (h j) :=
  NatIso.ofComponents (fun f => Iso.refl _) (by simp only [Iso.refl]; aesop_cat)

end

section

variable {J : Type w₀} {D : J → Type u₁} [∀ j, Category.{v₁} (D j)]

/- Porting note: maybe mixing up universes -/
instance sumElimCategory : ∀ s : Sum I J, Category.{v₁} (Sum.elim C D s)
  | Sum.inl i => by
    dsimp
    infer_instance
  | Sum.inr j => by
    dsimp
    infer_instance

/- Porting note: replaced `Sum.rec` with `match`'s per the error about
current state of code generation -/

/-- The bifunctor combining an `I`-indexed family of objects with a `J`-indexed family of objects
to obtain an `I ⊕ J`-indexed family of objects.
-/
@[simps]
def sum : (∀ i, C i) ⥤ (∀ j, D j) ⥤ ∀ s : Sum I J, Sum.elim C D s where
  obj X :=
    { obj := fun Y s =>
        match s with
        | .inl i => X i
        | .inr j => Y j
      map := fun {Y} {Y'} f s =>
        match s with
        | .inl i => 𝟙 (X i)
        | .inr j => f j }
  map {X} {X'} f :=
    { app := fun Y s =>
        match s with
        | .inl i => f i
        | .inr j => 𝟙 (Y j) }

end

variable {C}

/-- An isomorphism between `I`-indexed objects gives an isomorphism between each
pair of corresponding components. -/
@[simps]
def isoApp {X Y : ∀ i, C i} (f : X ≅ Y) (i : I) : X i ≅ Y i :=
  ⟨f.hom i, f.inv i,
    by rw [← comp_apply, Iso.hom_inv_id, id_apply], by rw [← comp_apply, Iso.inv_hom_id, id_apply]⟩

@[simp]
theorem isoApp_refl (X : ∀ i, C i) (i : I) : isoApp (Iso.refl X) i = Iso.refl (X i) :=
  rfl

@[simp]
theorem isoApp_symm {X Y : ∀ i, C i} (f : X ≅ Y) (i : I) : isoApp f.symm i = (isoApp f i).symm :=
  rfl

@[simp]
theorem isoApp_trans {X Y Z : ∀ i, C i} (f : X ≅ Y) (g : Y ≅ Z) (i : I) :
    isoApp (f ≪≫ g) i = isoApp f i ≪≫ isoApp g i :=
  rfl

end Pi

namespace Functor

variable {C}

variable {D : I → Type u₁} [∀ i, Category.{v₁} (D i)] {A : Type u₁} [Category.{u₁} A]

/-- Assemble an `I`-indexed family of functors into a functor between the pi types.
-/
@[simps]
def pi (F : ∀ i, C i ⥤ D i) : (∀ i, C i) ⥤ ∀ i, D i where
  obj f i := (F i).obj (f i)
  map α i := (F i).map (α i)

/-- Similar to `pi`, but all functors come from the same category `A`
-/
@[simps]
def pi' (f : ∀ i, A ⥤ C i) : A ⥤ ∀ i, C i where
  obj a i := (f i).obj a
  map h i := (f i).map h

section EqToHom

@[simp]
theorem eqToHom_proj {x x' : ∀ i, C i} (h : x = x') (i : I) :
    (eqToHom h : x ⟶ x') i = eqToHom (Function.funext_iff.mp h i) := by
  subst h
  rfl

end EqToHom

-- One could add some natural isomorphisms showing
-- how `Functor.pi` commutes with `Pi.eval` and `Pi.comap`.
@[simp]
theorem pi'_eval (f : ∀ i, A ⥤ C i) (i : I) : pi' f ⋙ Pi.eval C i = f i := by
  apply Functor.ext
  intro _ _ _
  · simp
  · intro _
    rfl

/-- Two functors to a product category are equal iff they agree on every coordinate. -/
theorem pi_ext (f f' : A ⥤ ∀ i, C i) (h : ∀ i, f ⋙ (Pi.eval C i) = f' ⋙ (Pi.eval C i)) :
    f = f' := by
  apply Functor.ext; rotate_left
  · intro X
    ext i
    specialize h i
    have := congr_obj h X
    simpa
  · intro X Y g
    dsimp
    funext i
    specialize h i
    have := congr_hom h g
    simpa

end Functor

namespace NatTrans

variable {C}

variable {D : I → Type u₁} [∀ i, Category.{v₁} (D i)]

variable {F G : ∀ i, C i ⥤ D i}

/-- Assemble an `I`-indexed family of natural transformations into a single natural transformation.
-/
@[simps!]
def pi (α : ∀ i, F i ⟶ G i) : Functor.pi F ⟶ Functor.pi G where
  app f i := (α i).app (f i)

end NatTrans

end CategoryTheory
