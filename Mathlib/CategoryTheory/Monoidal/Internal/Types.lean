/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Types.Symmetric

/-!
# `Mon_ (Type u) ≌ MonCat.{u}`

The category of internal monoid objects in `Type`
is equivalent to the category of "native" bundled monoids.

Moreover, this equivalence is compatible with the forgetful functors to `Type`.
-/


universe v u

open CategoryTheory

open scoped Mon_Class

namespace MonTypeEquivalenceMon

instance monMonoid (A : Type u) [Mon_Class A] : Monoid A where
  one := η[A] PUnit.unit
  mul x y := μ[A] (x, y)
  one_mul x := by convert congr_fun (Mon_Class.one_mul' A) (PUnit.unit, x)
  mul_one x := by convert congr_fun (Mon_Class.mul_one' A) (x, PUnit.unit)
  mul_assoc x y z := by convert congr_fun (Mon_Class.mul_assoc' A) ((x, y), z)

/-- Converting a monoid object in `Type` to a bundled monoid.
-/
noncomputable def functor : Mon_ (Type u) ⥤ MonCat.{u} where
  obj A := MonCat.of A.X
  map f :=
    { toFun := f.hom
      map_one' := congr_fun f.one_hom PUnit.unit
      map_mul' := fun x y => congr_fun f.mul_hom (x, y) }

@[simps]
instance (A : Type u) [Monoid A] : Mon_Class A where
  one := fun _ => 1
  mul := fun p => p.1 * p.2
  one_mul := by ext ⟨_, _⟩; dsimp; simp
  mul_one := by ext ⟨_, _⟩; dsimp; simp
  mul_assoc := by ext ⟨⟨x, y⟩, z⟩; simp [mul_assoc]

/-- Converting a bundled monoid to a monoid object in `Type`.
-/
noncomputable def inverse : MonCat.{u} ⥤ Mon_ (Type u) where
  obj A := { X := A }
  map f := { hom := f }

end MonTypeEquivalenceMon

open MonTypeEquivalenceMon

/-- The category of internal monoid objects in `Type`
is equivalent to the category of "native" bundled monoids.
-/
noncomputable def monTypeEquivalenceMon : Mon_ (Type u) ≌ MonCat.{u} where
  functor := functor
  inverse := inverse
  unitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom := { hom := 𝟙 _ }
          inv := { hom := 𝟙 _ } })
      (by aesop_cat)
  counitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom :=
            { toFun := id
              map_one' := rfl
              map_mul' := fun x y => rfl }
          inv :=
            { toFun := id
              map_one' := rfl
              map_mul' := fun x y => rfl } })
      (by aesop_cat)

/-- The equivalence `Mon_ (Type u) ≌ MonCat.{u}`
is naturally compatible with the forgetful functors to `Type u`.
-/
noncomputable def monTypeEquivalenceMonForget :
    MonTypeEquivalenceMon.functor ⋙ forget MonCat ≅ Mon_.forget (Type u) :=
  NatIso.ofComponents (fun A => Iso.refl _) (by aesop_cat)

noncomputable instance monTypeInhabited : Inhabited (Mon_ (Type u)) :=
  ⟨MonTypeEquivalenceMon.inverse.obj (MonCat.of PUnit)⟩

namespace CommMonTypeEquivalenceCommMon

instance commMonCommMonoid (A : CommMon_ (Type u)) : CommMonoid A.X :=
  { MonTypeEquivalenceMon.monMonoid A.X with
    mul_comm := fun x y => by convert congr_fun A.mul_comm (y, x) }

/-- Converting a commutative monoid object in `Type` to a bundled commutative monoid.
-/
noncomputable def functor : CommMon_ (Type u) ⥤ CommMonCat.{u} where
  obj A := CommMonCat.of A.X
  map f := MonTypeEquivalenceMon.functor.map f

/-- Converting a bundled commutative monoid to a commutative monoid object in `Type`.
-/
noncomputable def inverse : CommMonCat.{u} ⥤ CommMon_ (Type u) where
  obj A :=
    { MonTypeEquivalenceMon.inverse.obj ((forget₂ CommMonCat MonCat).obj A) with
      mul_comm := by
        ext ⟨x : A, y : A⟩
        exact CommMonoid.mul_comm y x }
  map f := MonTypeEquivalenceMon.inverse.map ((forget₂ CommMonCat MonCat).map f)

end CommMonTypeEquivalenceCommMon

open CommMonTypeEquivalenceCommMon

/-- The category of internal commutative monoid objects in `Type`
is equivalent to the category of "native" bundled commutative monoids.
-/
noncomputable def commMonTypeEquivalenceCommMon : CommMon_ (Type u) ≌ CommMonCat.{u} where
  functor := functor
  inverse := inverse
  unitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom := { hom := 𝟙 _ }
          inv := { hom := 𝟙 _ } })
      (by aesop_cat)
  counitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom :=
            { toFun := id
              map_one' := rfl
              map_mul' := fun x y => rfl }
          inv :=
            { toFun := id
              map_one' := rfl
              map_mul' := fun x y => rfl } })
      (by aesop_cat)

/-- The equivalences `Mon_ (Type u) ≌ MonCat.{u}` and `CommMon_ (Type u) ≌ CommMonCat.{u}`
are naturally compatible with the forgetful functors to `MonCat` and `Mon_ (Type u)`.
-/
noncomputable def commMonTypeEquivalenceCommMonForget :
    CommMonTypeEquivalenceCommMon.functor ⋙ forget₂ CommMonCat MonCat ≅
      CommMon_.forget₂Mon_ (Type u) ⋙ MonTypeEquivalenceMon.functor :=
  NatIso.ofComponents (fun A => Iso.refl _) (by aesop_cat)

noncomputable instance commMonTypeInhabited : Inhabited (CommMon_ (Type u)) :=
  ⟨CommMonTypeEquivalenceCommMon.inverse.obj (CommMonCat.of PUnit)⟩
