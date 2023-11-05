/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Algebra.Category.GroupCat.Basic
import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
import Mathlib.CategoryTheory.Elementwise
import Mathlib.Algebra.Ring.Equiv

#align_import algebra.category.Ring.basic from "leanprover-community/mathlib"@"34b2a989ad80bce3a5de749d935a4f23726e26e9"

/-!
# Category instances for `Semiring`, `Ring`, `CommSemiring`, and `CommRing`.

We introduce the bundled categories:
* `SemiRingCat`
* `RingCat`
* `CommSemiRingCat`
* `CommRingCat`
along with the relevant forgetful functors between them.
-/

set_option autoImplicit true


universe u v

open CategoryTheory

/-- The category of semirings. -/
def SemiRingCat : Type (u + 1) :=
  Bundled Semiring

-- Porting note: typemax hack to fix universe complaints
/-- An alias for `Semiring.{max u v}`, to deal around unification issues. -/
@[nolint checkUnivs]
abbrev SemiRingCatMax.{u1, u2} := SemiRingCat.{max u1 u2}

namespace SemiRingCat

/-- `RingHom` doesn't actually assume associativity. This alias is needed to make the category
theory machinery work. We use the same trick in `MonCat.AssocMonoidHom`. -/
abbrev AssocRingHom (M N : Type*) [Semiring M] [Semiring N] :=
  RingHom M N

instance bundledHom : BundledHom AssocRingHom where
  toFun _ _ f := f
  id _ := RingHom.id _
  comp _ _ _ f g := f.comp g

deriving instance LargeCategory for SemiRingCat

--Porting note: deriving fails for ConcreteCategory, adding instance manually.
--deriving instance LargeCategory, ConcreteCategory for SemiRingCat
-- see https://github.com/leanprover-community/mathlib4/issues/5020

instance : ConcreteCategory SemiRingCat := by
  dsimp [SemiRingCat]
  infer_instance

instance : CoeSort SemiRingCat (Type*) where
  coe X := X.α

-- Porting note : Hinting to Lean that `forget R` and `R` are the same
unif_hint forget_obj_eq_coe (R : SemiRingCat) where ⊢
  (forget SemiRingCat).obj R ≟ R

instance instSemiring (X : SemiRingCat) : Semiring X := X.str

instance instSemiring' (X : SemiRingCat) : Semiring <| (forget SemiRingCat).obj X := X.str

-- Porting note: added
instance instRingHomClass {X Y : SemiRingCat} : RingHomClass (X ⟶ Y) X Y :=
  RingHom.instRingHomClass

-- porting note: added
lemma coe_id {X : SemiRingCat} : (𝟙 X : X → X) = id := rfl

-- porting note: added
lemma coe_comp {X Y Z : SemiRingCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

-- porting note: added
@[simp] lemma forget_map (f : X ⟶ Y) : (forget SemiRingCat).map f = (f : X → Y) := rfl

lemma ext {X Y : SemiRingCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  RingHom.ext w

/-- Construct a bundled SemiRing from the underlying type and typeclass. -/
def of (R : Type u) [Semiring R] : SemiRingCat :=
  Bundled.of R

@[simp]
theorem coe_of (R : Type u) [Semiring R] : (SemiRingCat.of R : Type u) = R :=
  rfl

@[simp]
lemma RingEquiv_coe_eq {X Y : Type _} [Semiring X] [Semiring Y] (e : X ≃+* Y) :
    (@FunLike.coe (SemiRingCat.of X ⟶ SemiRingCat.of Y) _ (fun _ => (forget SemiRingCat).obj _)
      ConcreteCategory.funLike (e : X →+* Y) : X → Y) = ↑e :=
  rfl

instance : Inhabited SemiRingCat :=
  ⟨of PUnit⟩

instance hasForgetToMonCat : HasForget₂ SemiRingCat MonCat :=
  BundledHom.mkHasForget₂
    (fun R hR => @MonoidWithZero.toMonoid R (@Semiring.toMonoidWithZero R hR))
    (fun {_ _} => RingHom.toMonoidHom)
    (fun _ => rfl)

instance hasForgetToAddCommMonCat : HasForget₂ SemiRingCat AddCommMonCat where
   -- can't use BundledHom.mkHasForget₂, since AddCommMon is an induced category
  forget₂ :=
    { obj := fun R => AddCommMonCat.of R
      -- Porting note: This doesn't work without the `(_ := _)` trick.
      map := fun {R₁ R₂} f => RingHom.toAddMonoidHom (α := R₁) (β := R₂) f }

/-- Typecheck a `RingHom` as a morphism in `SemiRingCat`. -/
def ofHom {R S : Type u} [Semiring R] [Semiring S] (f : R →+* S) : of R ⟶ of S :=
  f

-- Porting note: `simpNF` should not trigger on `rfl` lemmas.
-- see https://github.com/leanprover/std4/issues/86
@[simp, nolint simpNF]
theorem ofHom_apply {R S : Type u} [Semiring R] [Semiring S] (f : R →+* S) (x : R) :
    ofHom f x = f x :=
  rfl

/--
Ring equivalence are isomorphisms in category of semirings
-/
@[simps]
def _root_.RingEquiv.toSemiRingCatIso [Semiring X] [Semiring Y] (e : X ≃+* Y) :
    SemiRingCat.of X ≅ SemiRingCat.of Y where
  hom := e.toRingHom
  inv := e.symm.toRingHom

instance forgetReflectIsos : ReflectsIsomorphisms (forget SemiRingCat) where
  reflects {X Y} f _ := by
    let i := asIso ((forget SemiRingCat).map f)
    let ff : X →+* Y := f
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact ⟨(IsIso.of_iso e.toSemiRingCatIso).1⟩

end SemiRingCat

/-- The category of rings. -/
def RingCat : Type (u + 1) :=
  Bundled Ring

namespace RingCat

instance : BundledHom.ParentProjection @Ring.toSemiring :=
  ⟨⟩

-- Porting note: Another place where mathlib had derived a concrete category
-- but this does not work here, so we add the instance manually.
-- see https://github.com/leanprover-community/mathlib4/issues/5020
deriving instance LargeCategory for RingCat

instance : ConcreteCategory RingCat := by
  dsimp [RingCat]
  infer_instance

instance : CoeSort RingCat (Type*) where
  coe X := X.α

instance (X : RingCat) : Ring X := X.str

-- Porting note : Hinting to Lean that `forget R` and `R` are the same
unif_hint forget_obj_eq_coe (R : RingCat) where ⊢
  (forget RingCat).obj R ≟ R

instance instRing (X : RingCat) : Ring X := X.str

instance instRing' (X : RingCat) : Ring <| (forget RingCat).obj X := X.str

-- Porting note: added
instance instRingHomClass {X Y : RingCat} : RingHomClass (X ⟶ Y) X Y :=
  RingHom.instRingHomClass

-- porting note: added
lemma coe_id {X : RingCat} : (𝟙 X : X → X) = id := rfl

-- porting note: added
lemma coe_comp {X Y Z : RingCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

-- porting note: added
@[simp] lemma forget_map (f : X ⟶ Y) : (forget RingCat).map f = (f : X → Y) := rfl

lemma ext {X Y : RingCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  RingHom.ext w

/-- Construct a bundled `RingCat` from the underlying type and typeclass. -/
def of (R : Type u) [Ring R] : RingCat :=
  Bundled.of R

/-- Typecheck a `RingHom` as a morphism in `RingCat`. -/
def ofHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) : of R ⟶ of S :=
  f

-- Porting note: I think this is now redundant.
-- @[simp]
-- theorem ofHom_apply {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (x : R) : ofHom f x = f x :=
--   rfl
-- set_option linter.uppercaseLean3 false in
-- #align Ring.of_hom_apply RingCat.ofHom_apply

instance : Inhabited RingCat :=
  ⟨of PUnit⟩

instance (R : RingCat) : Ring R :=
  R.str

@[simp]
theorem coe_of (R : Type u) [Ring R] : (RingCat.of R : Type u) = R :=
  rfl

@[simp]
lemma RingEquiv_coe_eq {X Y : Type _} [Ring X] [Ring Y] (e : X ≃+* Y) :
    (@FunLike.coe (RingCat.of X ⟶ RingCat.of Y) _ (fun _ => (forget RingCat).obj _)
      ConcreteCategory.funLike (e : X →+* Y) : X → Y) = ↑e :=
  rfl

instance hasForgetToSemiRingCat : HasForget₂ RingCat SemiRingCat :=
  BundledHom.forget₂ _ _

instance hasForgetToAddCommGroupCat : HasForget₂ RingCat AddCommGroupCat where
  -- can't use BundledHom.mkHasForget₂, since AddCommGroup is an induced category
  forget₂ :=
    { obj := fun R => AddCommGroupCat.of R
      -- Porting note: use `(_ := _)` similar to above.
      map := fun {R₁ R₂} f => RingHom.toAddMonoidHom (α := R₁) (β := R₂) f }

end RingCat

/-- The category of commutative semirings. -/
def CommSemiRingCat : Type (u + 1) :=
  Bundled CommSemiring

namespace CommSemiRingCat

instance : BundledHom.ParentProjection @CommSemiring.toSemiring :=
  ⟨⟩

-- Porting note: again, deriving fails for concrete category instances.
-- see https://github.com/leanprover-community/mathlib4/issues/5020
deriving instance LargeCategory for CommSemiRingCat

instance : ConcreteCategory CommSemiRingCat := by
  dsimp [CommSemiRingCat]
  infer_instance

instance : CoeSort CommSemiRingCat (Type*) where
  coe X := X.α

instance (X : CommSemiRingCat) : CommSemiring X := X.str

-- Porting note : Hinting to Lean that `forget R` and `R` are the same
unif_hint forget_obj_eq_coe (R : CommSemiRingCat) where ⊢
  (forget CommSemiRingCat).obj R ≟ R

instance instCommSemiring (X : CommSemiRingCat) : CommSemiring X := X.str

instance instCommSemiring' (X : CommSemiRingCat) : CommSemiring <| (forget CommSemiRingCat).obj X :=
  X.str

-- Porting note: added
instance instRingHomClass {X Y : CommSemiRingCat} : RingHomClass (X ⟶ Y) X Y :=
  RingHom.instRingHomClass

-- porting note: added
lemma coe_id {X : CommSemiRingCat} : (𝟙 X : X → X) = id := rfl

-- porting note: added
lemma coe_comp {X Y Z : CommSemiRingCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

-- porting note: added
@[simp] lemma forget_map (f : X ⟶ Y) : (forget CommSemiRingCat).map f = (f : X → Y) := rfl

lemma ext {X Y : CommSemiRingCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  RingHom.ext w

/-- Construct a bundled `CommSemiRingCat` from the underlying type and typeclass. -/
def of (R : Type u) [CommSemiring R] : CommSemiRingCat :=
  Bundled.of R

/-- Typecheck a `RingHom` as a morphism in `CommSemiRingCat`. -/
def ofHom {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R →+* S) : of R ⟶ of S :=
  f

@[simp]
lemma RingEquiv_coe_eq {X Y : Type _} [CommSemiring X] [CommSemiring Y] (e : X ≃+* Y) :
    (@FunLike.coe (CommSemiRingCat.of X ⟶ CommSemiRingCat.of Y) _
      (fun _ => (forget CommSemiRingCat).obj _)
      ConcreteCategory.funLike (e : X →+* Y) : X → Y) = ↑e :=
  rfl

-- Porting note: I think this is now redundant.
-- @[simp]
-- theorem ofHom_apply {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R →+* S) (x : R) :
--     ofHom f x = f x :=
--   rfl
-- set_option linter.uppercaseLean3 false in
#noalign CommSemiRing.of_hom_apply

instance : Inhabited CommSemiRingCat :=
  ⟨of PUnit⟩

instance (R : CommSemiRingCat) : CommSemiring R :=
  R.str

@[simp]
theorem coe_of (R : Type u) [CommSemiring R] : (CommSemiRingCat.of R : Type u) = R :=
  rfl

instance hasForgetToSemiRingCat : HasForget₂ CommSemiRingCat SemiRingCat :=
  BundledHom.forget₂ _ _

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance hasForgetToCommMonCat : HasForget₂ CommSemiRingCat CommMonCat :=
  HasForget₂.mk' (fun R : CommSemiRingCat => CommMonCat.of R) (fun R => rfl)
    -- Porting note: `(_ := _)` trick
    (fun {R₁ R₂} f => RingHom.toMonoidHom (α := R₁) (β := R₂) f) (by rfl)

/--
Ring equivalence are isomorphisms in category of commutative semirings
-/
@[simps]
def _root_.RingEquiv.toCommSemiRingCatIso [CommSemiring X] [CommSemiring Y] (e : X ≃+* Y) :
    SemiRingCat.of X ≅ SemiRingCat.of Y where
  hom := e.toRingHom
  inv := e.symm.toRingHom

instance forgetReflectIsos : ReflectsIsomorphisms (forget CommSemiRingCat) where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommSemiRingCat).map f)
    let ff : X →+* Y := f
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact ⟨(IsIso.of_iso e.toSemiRingCatIso).1⟩

end CommSemiRingCat

/-- The category of commutative rings. -/
def CommRingCat : Type (u + 1) :=
  Bundled CommRing

namespace CommRingCat

instance : BundledHom.ParentProjection @CommRing.toRing :=
  ⟨⟩

-- Porting note: deriving fails for concrete category.
-- see https://github.com/leanprover-community/mathlib4/issues/5020
deriving instance LargeCategory for CommRingCat

instance : ConcreteCategory CommRingCat := by
  dsimp [CommRingCat]
  infer_instance

instance : CoeSort CommRingCat (Type*) where
  coe X := X.α

-- Porting note : Hinting to Lean that `forget R` and `R` are the same
unif_hint forget_obj_eq_coe (R : CommRingCat) where ⊢
  (forget CommRingCat).obj R ≟ R

instance instCommRing (X : CommRingCat) : CommRing X := X.str

instance instCommRing' (X : CommRingCat) : CommRing <| (forget CommRingCat).obj X := X.str

-- Porting note: added
instance instRingHomClass {X Y : CommRingCat} : RingHomClass (X ⟶ Y) X Y :=
  RingHom.instRingHomClass

-- porting note: added
lemma coe_id {X : CommRingCat} : (𝟙 X : X → X) = id := rfl

-- porting note: added
lemma coe_comp {X Y Z : CommRingCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

-- porting note: added
@[simp] lemma forget_map (f : X ⟶ Y) : (forget CommRingCat).map f = (f : X → Y) := rfl

lemma ext {X Y : CommRingCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  RingHom.ext w

/-- Construct a bundled `CommRingCat` from the underlying type and typeclass. -/
def of (R : Type u) [CommRing R] : CommRingCat :=
  Bundled.of R

/-- Typecheck a `RingHom` as a morphism in `CommRingCat`. -/
def ofHom {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : of R ⟶ of S :=
  f

@[simp]
lemma RingEquiv_coe_eq {X Y : Type _} [CommRing X] [CommRing Y] (e : X ≃+* Y) :
    (@FunLike.coe (CommRingCat.of X ⟶ CommRingCat.of Y) _ (fun _ => (forget CommRingCat).obj _)
      ConcreteCategory.funLike (e : X →+* Y) : X → Y) = ↑e :=
  rfl

-- Porting note: I think this is now redundant.
-- @[simp]
-- theorem ofHom_apply {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
--     ofHom f x = f x :=
--   rfl
-- set_option linter.uppercaseLean3 false in
#noalign CommRing.of_hom_apply

instance : Inhabited CommRingCat :=
  ⟨of PUnit⟩

instance (R : CommRingCat) : CommRing R :=
  R.str

@[simp]
theorem coe_of (R : Type u) [CommRing R] : (CommRingCat.of R : Type u) = R :=
  rfl

instance hasForgetToRingCat : HasForget₂ CommRingCat RingCat :=
  BundledHom.forget₂ _ _

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance hasForgetToCommSemiRingCat : HasForget₂ CommRingCat CommSemiRingCat :=
  HasForget₂.mk' (fun R : CommRingCat => CommSemiRingCat.of R) (fun R => rfl)
    (fun {R₁ R₂} f => f) (by rfl)

instance : Full (forget₂ CommRingCat CommSemiRingCat) where preimage {X Y} f := f

end CommRingCat

-- We verify that simp lemmas apply when coercing morphisms to functions.
example {R S : CommRingCat} (i : R ⟶ S) (r : R) (h : r = 0) : i r = 0 := by simp [h]

namespace RingEquiv

variable {X Y : Type u}

/-- Build an isomorphism in the category `RingCat` from a `RingEquiv` between `RingCat`s. -/
@[simps]
def toRingCatIso [Ring X] [Ring Y] (e : X ≃+* Y) : RingCat.of X ≅ RingCat.of Y
    where
  hom := e.toRingHom
  inv := e.symm.toRingHom

/-- Build an isomorphism in the category `CommRingCat` from a `RingEquiv` between `CommRingCat`s. -/
@[simps]
def toCommRingCatIso [CommRing X] [CommRing Y] (e : X ≃+* Y) : CommRingCat.of X ≅ CommRingCat.of Y
    where
  hom := e.toRingHom
  inv := e.symm.toRingHom

end RingEquiv

namespace CategoryTheory.Iso

/-- Build a `RingEquiv` from an isomorphism in the category `RingCat`. -/
def ringCatIsoToRingEquiv {X Y : RingCat} (i : X ≅ Y) : X ≃+* Y
    where
  toFun := i.hom
  invFun := i.inv
  -- Porting note: All these proofs were much easier in lean3.
  left_inv := fun x => show (i.hom ≫ i.inv) x = x by rw [i.hom_inv_id]; rfl
  right_inv := fun x => show (i.inv ≫ i.hom) x = x by rw [i.inv_hom_id]; rfl
  map_add' := fun x y => let ii : X →+* Y := i.hom; ii.map_add x y
  map_mul' := fun x y => let ii : X →+* Y := i.hom; ii.map_mul x y

/-- Build a `RingEquiv` from an isomorphism in the category `CommRingCat`. -/
def commRingCatIsoToRingEquiv {X Y : CommRingCat} (i : X ≅ Y) : X ≃+* Y
    where
  toFun := i.hom
  invFun := i.inv
  -- Porting note: All these proofs were much easier in lean3.
  left_inv := fun x => show (i.hom ≫ i.inv) x = x by rw [i.hom_inv_id]; rfl
  right_inv := fun x => show (i.inv ≫ i.hom) x = x by rw [i.inv_hom_id]; rfl
  map_add' := fun x y => let ii : X →+* Y := i.hom; ii.map_add x y
  map_mul' := fun x y => let ii : X →+* Y := i.hom; ii.map_mul x y

-- Porting note : make this high priority to short circuit simplifier
@[simp (high)]
theorem commRingIsoToRingEquiv_toRingHom {X Y : CommRingCat} (i : X ≅ Y) :
    i.commRingCatIsoToRingEquiv.toRingHom = i.hom := by
  ext
  rfl

-- Porting note : make this high priority to short circuit simplifier
@[simp (high)]
theorem commRingIsoToRingEquiv_symm_toRingHom {X Y : CommRingCat} (i : X ≅ Y) :
    i.commRingCatIsoToRingEquiv.symm.toRingHom = i.inv := by
  ext
  rfl

end CategoryTheory.Iso

/-- Ring equivalences between `RingCat`s are the same as (isomorphic to) isomorphisms in
`RingCat`. -/
def ringEquivIsoRingIso {X Y : Type u} [Ring X] [Ring Y] : X ≃+* Y ≅ RingCat.of X ≅ RingCat.of Y
    where
  hom e := e.toRingCatIso
  inv i := i.ringCatIsoToRingEquiv

/-- Ring equivalences between `CommRingCat`s are the same as (isomorphic to) isomorphisms
in `CommRingCat`. -/
def ringEquivIsoCommRingIso {X Y : Type u} [CommRing X] [CommRing Y] :
    X ≃+* Y ≅ CommRingCat.of X ≅ CommRingCat.of Y
    where
  hom e := e.toCommRingCatIso
  inv i := i.commRingCatIsoToRingEquiv

instance RingCat.forget_reflects_isos : ReflectsIsomorphisms (forget RingCat.{u}) where
  reflects {X Y} f _ := by
    let i := asIso ((forget RingCat).map f)
    let ff : X →+* Y := f
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact ⟨(IsIso.of_iso e.toRingCatIso).1⟩

instance CommRingCat.forget_reflects_isos : ReflectsIsomorphisms (forget CommRingCat.{u}) where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommRingCat).map f)
    let ff : X →+* Y := f
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact ⟨(IsIso.of_iso e.toCommRingCatIso).1⟩

theorem CommRingCat.comp_eq_ring_hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    f ≫ g = g.comp f :=
  rfl

theorem CommRingCat.ringHom_comp_eq_comp {R S T : Type _} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) : g.comp f = CommRingCat.ofHom f ≫ CommRingCat.ofHom g :=
  rfl

-- It would be nice if we could have the following,
-- but it requires making `reflectsIsomorphisms_forget₂` an instance,
-- which can cause typeclass loops:
-- Porting note: This was the case in mathlib3, perhaps it is different now?
attribute [local instance] reflectsIsomorphisms_forget₂

example : ReflectsIsomorphisms (forget₂ RingCat AddCommGroupCat) := by infer_instance
