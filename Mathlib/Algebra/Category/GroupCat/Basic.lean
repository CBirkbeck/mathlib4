/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Endomorphism

#align_import algebra.category.Group.basic from "leanprover-community/mathlib"@"524793de15bc4c52ee32d254e7d7867c7176b3af"

/-!
# Category instances for Group, AddGroup, CommGroup, and AddCommGroup.

We introduce the bundled categories:
* `GroupCat`
* `AddGroupCat`
* `CommGroupCat`
* `AddCommGroupCat`
along with the relevant forgetful functors between them, and to the bundled monoid categories.
-/

set_option autoImplicit true


universe u v

open CategoryTheory

/-- The category of groups and group morphisms. -/
@[to_additive]
def GroupCat : Type (u + 1) :=
  Bundled Group

/-- The category of additive groups and group morphisms -/
add_decl_doc AddGroupCat

namespace GroupCat

@[to_additive]
instance : BundledHom.ParentProjection
  (fun {α : Type*} (h : Group α) => h.toDivInvMonoid.toMonoid) := ⟨⟩

deriving instance LargeCategory for GroupCat
attribute [to_additive] instGroupCatLargeCategory

@[to_additive]
instance concreteCategory : ConcreteCategory GroupCat := by
  dsimp only [GroupCat]
  infer_instance

@[to_additive]
instance : CoeSort GroupCat (Type*) where
  coe X := X.α

@[to_additive]
instance (X : GroupCat) : Group X := X.str

-- porting note: this instance was not necessary in mathlib
@[to_additive]
instance {X Y : GroupCat} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →* Y) := f

@[to_additive]
instance FunLike_instance (X Y : GroupCat) : FunLike (X ⟶ Y) X (fun _ => Y) :=
  show FunLike (X →* Y) X (fun _ => Y) from inferInstance

-- porting note: added
@[to_additive (attr := simp)]
lemma coe_id {X : GroupCat} : (𝟙 X : X → X) = id := rfl

-- porting note: added
@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : GroupCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[to_additive]
lemma comp_def {X Y Z : GroupCat} {f : X ⟶ Y} {g : Y ⟶ Z} : f ≫ g = g.comp f := rfl

-- porting note: added
@[simp] lemma forget_map (f : X ⟶ Y) : (forget GroupCat).map f = (f : X → Y) := rfl

@[to_additive (attr := ext)]
lemma ext {X Y : GroupCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  MonoidHom.ext w

/-- Construct a bundled `Group` from the underlying type and typeclass. -/
@[to_additive]
def of (X : Type u) [Group X] : GroupCat :=
  Bundled.of X

/-- Construct a bundled `AddGroup` from the underlying type and typeclass. -/
add_decl_doc AddGroupCat.of

@[to_additive (attr := simp)]
theorem coe_of (R : Type u) [Group R] : ↑(GroupCat.of R) = R :=
  rfl

@[to_additive]
instance : Inhabited GroupCat :=
  ⟨GroupCat.of PUnit⟩

@[to_additive hasForgetToAddMonCat]
instance hasForgetToMonCat : HasForget₂ GroupCat MonCat :=
  BundledHom.forget₂ _ _

@[to_additive]
instance : Coe GroupCat.{u} MonCat.{u} where coe := (forget₂ GroupCat MonCat).obj

-- porting note: this instance was not necessary in mathlib
@[to_additive]
instance (G H : GroupCat) : One (G ⟶ H) := (inferInstance : One (MonoidHom G H))

@[to_additive (attr := simp)]
theorem one_apply (G H : GroupCat) (g : G) : ((1 : G ⟶ H) : G → H) g = 1 :=
  rfl

/-- Typecheck a `MonoidHom` as a morphism in `GroupCat`. -/
@[to_additive]
def ofHom {X Y : Type u} [Group X] [Group Y] (f : X →* Y) : of X ⟶ of Y :=
  f

/-- Typecheck an `AddMonoidHom` as a morphism in `AddGroup`. -/
add_decl_doc AddGroupCat.ofHom

@[to_additive]
theorem ofHom_apply {X Y : Type _} [Group X] [Group Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x :=
  rfl

@[to_additive]
instance ofUnique (G : Type*) [Group G] [i : Unique G] : Unique (GroupCat.of G) := i

-- We verify that simp lemmas apply when coercing morphisms to functions.
@[to_additive]
example {R S : GroupCat} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

end GroupCat

/-- The category of commutative groups and group morphisms. -/
@[to_additive]
def CommGroupCat : Type (u + 1) :=
  Bundled CommGroup

/-- The category of additive commutative groups and group morphisms. -/
add_decl_doc AddCommGroupCat

/-- `Ab` is an abbreviation for `AddCommGroup`, for the sake of mathematicians' sanity. -/
abbrev Ab := AddCommGroupCat

namespace CommGroupCat

@[to_additive]
instance : BundledHom.ParentProjection @CommGroup.toGroup := ⟨⟩

deriving instance LargeCategory for CommGroupCat
attribute [to_additive] instCommGroupCatLargeCategory

@[to_additive]
instance concreteCategory : ConcreteCategory CommGroupCat := by
  dsimp only [CommGroupCat]
  infer_instance

@[to_additive]
instance : CoeSort CommGroupCat (Type*) where
  coe X := X.α

@[to_additive]
instance commGroupInstance (X : CommGroupCat) : CommGroup X := X.str

-- porting note: this instance was not necessary in mathlib
@[to_additive]
instance {X Y : CommGroupCat} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →* Y) := f

@[to_additive]
instance FunLike_instance (X Y : CommGroupCat) : FunLike (X ⟶ Y) X (fun _ => Y) :=
  show FunLike (X →* Y) X (fun _ => Y) from inferInstance

-- porting note: added
@[to_additive (attr := simp)]
lemma coe_id {X : CommGroupCat} : (𝟙 X : X → X) = id := rfl

-- porting note: added
@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : CommGroupCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[to_additive]
lemma comp_def {X Y Z : CommGroupCat} {f : X ⟶ Y} {g : Y ⟶ Z} : f ≫ g = g.comp f := rfl

-- porting note: added
@[to_additive (attr := simp)]
lemma forget_map {X Y : CommGroupCat} (f : X ⟶ Y) :
    (forget CommGroupCat).map f = (f : X → Y) :=
  rfl

@[to_additive (attr := ext)]
lemma ext {X Y : CommGroupCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  MonoidHom.ext w

/-- Construct a bundled `CommGroup` from the underlying type and typeclass. -/
@[to_additive]
def of (G : Type u) [CommGroup G] : CommGroupCat :=
  Bundled.of G

/-- Construct a bundled `AddCommGroup` from the underlying type and typeclass. -/
add_decl_doc AddCommGroupCat.of

@[to_additive]
instance : Inhabited CommGroupCat :=
  ⟨CommGroupCat.of PUnit⟩

-- Porting note: removed `@[simp]` here, as it makes it harder to tell when to apply
-- bundled or unbundled lemmas.
-- (This change seems dangerous!)
@[to_additive]
theorem coe_of (R : Type u) [CommGroup R] : (CommGroupCat.of R : Type u) = R :=
  rfl

@[to_additive]
instance ofUnique (G : Type*) [CommGroup G] [i : Unique G] : Unique (CommGroupCat.of G) :=
  i

@[to_additive]
instance hasForgetToGroup : HasForget₂ CommGroupCat GroupCat :=
  BundledHom.forget₂ _ _

@[to_additive]
instance : Coe CommGroupCat.{u} GroupCat.{u} where coe := (forget₂ CommGroupCat GroupCat).obj

@[to_additive hasForgetToAddCommMonCat]
instance hasForgetToCommMonCat : HasForget₂ CommGroupCat CommMonCat :=
  InducedCategory.hasForget₂ fun G : CommGroupCat => CommMonCat.of G

@[to_additive]
instance : Coe CommGroupCat.{u} CommMonCat.{u} where coe := (forget₂ CommGroupCat CommMonCat).obj

-- porting note: this instance was not necessary in mathlib
@[to_additive]
instance (G H : CommGroupCat) : One (G ⟶ H) := (inferInstance : One (MonoidHom G H))

@[to_additive (attr := simp)]
theorem one_apply (G H : CommGroupCat) (g : G) : ((1 : G ⟶ H) : G → H) g = 1 :=
  rfl

/-- Typecheck a `MonoidHom` as a morphism in `CommGroup`. -/
@[to_additive]
def ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) : of X ⟶ of Y :=
  f

/-- Typecheck an `AddMonoidHom` as a morphism in `AddCommGroup`. -/
add_decl_doc AddCommGroupCat.ofHom

@[to_additive (attr := simp)]
theorem ofHom_apply {X Y : Type _} [CommGroup X] [CommGroup Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x :=
  rfl

-- We verify that simp lemmas apply when coercing morphisms to functions.
@[to_additive]
example {R S : CommGroupCat} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

end CommGroupCat

namespace AddCommGroupCat

-- Note that because `ℤ : Type 0`, this forces `G : AddCommGroup.{0}`,
-- so we write this explicitly to be clear.
-- TODO generalize this, requiring a `ULiftInstances.lean` file
/-- Any element of an abelian group gives a unique morphism from `ℤ` sending
`1` to that element. -/
def asHom {G : AddCommGroupCat.{0}} (g : G) : AddCommGroupCat.of ℤ ⟶ G :=
  zmultiplesHom G g

@[simp]
theorem asHom_apply {G : AddCommGroupCat.{0}} (g : G) (i : ℤ) : (asHom g) i = i • g :=
  rfl

theorem asHom_injective {G : AddCommGroupCat.{0}} : Function.Injective (@asHom G) := fun h k w => by
  convert congr_arg (fun k : AddCommGroupCat.of ℤ ⟶ G => (k : ℤ → G) (1 : ℤ)) w <;> simp

@[ext]
theorem int_hom_ext {G : AddCommGroupCat.{0}} (f g : AddCommGroupCat.of ℤ ⟶ G)
    (w : f (1 : ℤ) = g (1 : ℤ)) : f = g :=
  @AddMonoidHom.ext_int G _ f g w

-- TODO: this argument should be generalised to the situation where
-- the forgetful functor is representable.
theorem injective_of_mono {G H : AddCommGroupCat.{0}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  fun g₁ g₂ h => by
  have t0 : asHom g₁ ≫ f = asHom g₂ ≫ f := by aesop_cat
  have t1 : asHom g₁ = asHom g₂ := (cancel_mono _).1 t0
  apply asHom_injective t1

end AddCommGroupCat

/-- Build an isomorphism in the category `GroupCat` from a `MulEquiv` between `Group`s. -/
@[to_additive (attr := simps)]
def MulEquiv.toGroupCatIso {X Y : GroupCat} (e : X ≃* Y) : X ≅ Y where
  hom := e.toMonoidHom
  inv := e.symm.toMonoidHom

/-- Build an isomorphism in the category `AddGroup` from an `AddEquiv` between `AddGroup`s. -/
add_decl_doc AddEquiv.toAddGroupCatIso

/-- Build an isomorphism in the category `CommGroupCat` from a `MulEquiv`
between `CommGroup`s. -/
@[to_additive (attr := simps)]
def MulEquiv.toCommGroupCatIso {X Y : CommGroupCat} (e : X ≃* Y) : X ≅ Y where
  hom := e.toMonoidHom
  inv := e.symm.toMonoidHom

/-- Build an isomorphism in the category `AddCommGroupCat` from an `AddEquiv`
between `AddCommGroup`s. -/
add_decl_doc AddEquiv.toAddCommGroupCatIso

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `GroupCat`. -/
@[to_additive (attr := simp)]
def groupIsoToMulEquiv {X Y : GroupCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id

/-- Build an `addEquiv` from an isomorphism in the category `AddGroup` -/
add_decl_doc addGroupIsoToAddEquiv

/-- Build a `MulEquiv` from an isomorphism in the category `CommGroup`. -/
@[to_additive (attr := simps!)]
def commGroupIsoToMulEquiv {X Y : CommGroupCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id

/-- Build an `AddEquiv` from an isomorphism in the category `AddCommGroup`. -/
add_decl_doc addCommGroupIsoToAddEquiv

end CategoryTheory.Iso

/-- multiplicative equivalences between `Group`s are the same as (isomorphic to) isomorphisms
in `GroupCat` -/
@[to_additive]
def mulEquivIsoGroupIso {X Y : GroupCat.{u}} : X ≃* Y ≅ X ≅ Y where
  hom e := e.toGroupCatIso
  inv i := i.groupIsoToMulEquiv

/-- "additive equivalences between `add_group`s are the same
as (isomorphic to) isomorphisms in `AddGroup` -/
add_decl_doc addEquivIsoAddGroupIso

/-- multiplicative equivalences between `comm_group`s are the same as (isomorphic to) isomorphisms
in `CommGroup` -/
@[to_additive]
def mulEquivIsoCommGroupIso {X Y : CommGroupCat.{u}} : X ≃* Y ≅ X ≅ Y where
  hom e := e.toCommGroupCatIso
  inv i := i.commGroupIsoToMulEquiv

/-- additive equivalences between `AddCommGroup`s are
the same as (isomorphic to) isomorphisms in `AddCommGroup` -/
add_decl_doc addEquivIsoAddCommGroupIso

namespace CategoryTheory.Aut

/-- The (bundled) group of automorphisms of a type is isomorphic to the (bundled) group
of permutations. -/
def isoPerm {α : Type u} : GroupCat.of (Aut α) ≅ GroupCat.of (Equiv.Perm α) where
  hom :=
    { toFun := fun g => g.toEquiv
      map_one' := by aesop
      map_mul' := by aesop }
  inv :=
    { toFun := fun g => g.toIso
      map_one' := by aesop
      map_mul' := by aesop }

/-- The (unbundled) group of automorphisms of a type is `mul_equiv` to the (unbundled) group
of permutations. -/
def mulEquivPerm {α : Type u} : Aut α ≃* Equiv.Perm α :=
  isoPerm.groupIsoToMulEquiv

end CategoryTheory.Aut

@[to_additive]
instance GroupCat.forget_reflects_isos : ReflectsIsomorphisms (forget GroupCat.{u}) where
  reflects {X Y} f _ := by
    let i := asIso ((forget GroupCat).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := by aesop }
    exact IsIso.of_iso e.toGroupCatIso

@[to_additive]
instance CommGroupCat.forget_reflects_isos : ReflectsIsomorphisms (forget CommGroupCat.{u}) where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommGroupCat).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := by aesop }
    exact IsIso.of_iso e.toCommGroupCatIso

-- note: in the following definitions, there is a problem with `@[to_additive]`
-- as the `Category` instance is not found on the additive variant
-- this variant is then renamed with a `Aux` suffix

/-- An alias for `GroupCat.{max u v}`, to deal around unification issues. -/
@[to_additive (attr := nolint checkUnivs) GroupCatMaxAux
  "An alias for `AddGroupCat.{max u v}`, to deal around unification issues."]
abbrev GroupCatMax.{u1, u2} := GroupCat.{max u1 u2}
/-- An alias for `AddGroupCat.{max u v}`, to deal around unification issues. -/
@[nolint checkUnivs]
abbrev AddGroupCatMax.{u1, u2} := AddGroupCat.{max u1 u2}

/-- An alias for `CommGroupCat.{max u v}`, to deal around unification issues. -/
@[to_additive (attr := nolint checkUnivs) AddCommGroupCatMaxAux
  "An alias for `AddCommGroupCat.{max u v}`, to deal around unification issues."]
abbrev CommGroupCatMax.{u1, u2} := CommGroupCat.{max u1 u2}
/-- An alias for `AddCommGroupCat.{max u v}`, to deal around unification issues. -/
@[nolint checkUnivs]
abbrev AddCommGroupCatMax.{u1, u2} := AddCommGroupCat.{max u1 u2}
