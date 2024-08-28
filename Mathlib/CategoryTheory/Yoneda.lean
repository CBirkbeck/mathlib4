/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Functor.Hom
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.Data.ULift
import Mathlib.Logic.Function.ULift

/-!
# The Yoneda embedding

The Yoneda embedding as a functor `yoneda : C ⥤ (Cᵒᵖ ⥤ Type v₁)`,
along with an instance that it is `FullyFaithful`.

Also the Yoneda lemma, `yonedaLemma : (yoneda_pairing C) ≅ (yoneda_evaluation C)`.

## References
* [Stacks: Opposite Categories and the Yoneda Lemma](https://stacks.math.columbia.edu/tag/001L)
-/

namespace CategoryTheory

open Opposite

universe v₁ u₁ u₂

-- morphism levels before object levels. See note [CategoryTheory universes].
variable {C : Type u₁} [Category.{v₁} C]

/-- The Yoneda embedding, as a functor from `C` into presheaves on `C`.

See <https://stacks.math.columbia.edu/tag/001O>.
-/
@[simps]
def yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁ where
  obj X :=
    { obj := fun Y => unop Y ⟶ X
      map := fun f g => f.unop ≫ g }
  map f :=
    { app := fun Y g => g ≫ f }

/-- The co-Yoneda embedding, as a functor from `Cᵒᵖ` into co-presheaves on `C`.
-/
@[simps]
def coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁ where
  obj X :=
    { obj := fun Y => unop X ⟶ Y
      map := fun f g => g ≫ f }
  map f :=
    { app := fun Y g => f.unop ≫ g }

namespace Yoneda

theorem obj_map_id {X Y : C} (f : op X ⟶ op Y) :
    (yoneda.obj X).map f (𝟙 X) = (yoneda.map f.unop).app (op Y) (𝟙 Y) := by
  dsimp
  simp

@[simp]
theorem naturality {X Y : C} (α : yoneda.obj X ⟶ yoneda.obj Y) {Z Z' : C} (f : Z ⟶ Z')
    (h : Z' ⟶ X) : f ≫ α.app (op Z') h = α.app (op Z) (f ≫ h) :=
  (FunctorToTypes.naturality _ _ α f.op h).symm

/-- The Yoneda embedding is fully faithful. -/
def fullyFaithful : (yoneda (C := C)).FullyFaithful where
  preimage f := f.app _ (𝟙 _)

lemma fullyFaithful_preimage {X Y : C} (f : yoneda.obj X ⟶ yoneda.obj Y) :
    fullyFaithful.preimage f = f.app (op X) (𝟙 X) := rfl

/-- The Yoneda embedding is full.

See <https://stacks.math.columbia.edu/tag/001P>.
-/
instance yoneda_full : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Full :=
  fullyFaithful.full

/-- The Yoneda embedding is faithful.

See <https://stacks.math.columbia.edu/tag/001P>.
-/
instance yoneda_faithful : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Faithful :=
  fullyFaithful.faithful

/-- Extensionality via Yoneda. The typical usage would be
```
-- Goal is `X ≅ Y`
apply yoneda.ext,
-- Goals are now functions `(Z ⟶ X) → (Z ⟶ Y)`, `(Z ⟶ Y) → (Z ⟶ X)`, and the fact that these
-- functions are inverses and natural in `Z`.
```
-/
def ext (X Y : C) (p : ∀ {Z : C}, (Z ⟶ X) → (Z ⟶ Y))
    (q : ∀ {Z : C}, (Z ⟶ Y) → (Z ⟶ X))
    (h₁ : ∀ {Z : C} (f : Z ⟶ X), q (p f) = f) (h₂ : ∀ {Z : C} (f : Z ⟶ Y), p (q f) = f)
    (n : ∀ {Z Z' : C} (f : Z' ⟶ Z) (g : Z ⟶ X), p (f ≫ g) = f ≫ p g) : X ≅ Y :=
  fullyFaithful.preimageIso
    (NatIso.ofComponents fun Z =>
      { hom := p
        inv := q })

/-- If `yoneda.map f` is an isomorphism, so was `f`.
-/
theorem isIso {X Y : C} (f : X ⟶ Y) [IsIso (yoneda.map f)] : IsIso f :=
  isIso_of_fully_faithful yoneda f

end Yoneda

namespace Coyoneda

@[simp]
theorem naturality {X Y : Cᵒᵖ} (α : coyoneda.obj X ⟶ coyoneda.obj Y) {Z Z' : C} (f : Z' ⟶ Z)
    (h : unop X ⟶ Z') : α.app Z' h ≫ f = α.app Z (h ≫ f) :=
  (FunctorToTypes.naturality _ _ α f h).symm

/-- The co-Yoneda embedding is fully faithful. -/
def fullyFaithful : (coyoneda (C := C)).FullyFaithful where
  preimage f := (f.app _ (𝟙 _)).op

lemma fullyFaithful_preimage {X Y : Cᵒᵖ} (f : coyoneda.obj X ⟶ coyoneda.obj Y) :
    fullyFaithful.preimage f = (f.app X.unop (𝟙 X.unop)).op := rfl

/-- The morphism `X ⟶ Y` corresponding to a natural transformation
`coyoneda.obj X ⟶ coyoneda.obj Y`. -/
def preimage {X Y : Cᵒᵖ} (f : coyoneda.obj X ⟶ coyoneda.obj Y) : X ⟶ Y :=
  (f.app _ (𝟙 X.unop)).op

instance coyoneda_full : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Full :=
  fullyFaithful.full

instance coyoneda_faithful : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Faithful :=
  fullyFaithful.faithful

/-- If `coyoneda.map f` is an isomorphism, so was `f`.
-/
theorem isIso {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso (coyoneda.map f)] : IsIso f :=
  isIso_of_fully_faithful coyoneda f

/-- The identity functor on `Type` is isomorphic to the coyoneda functor coming from `PUnit`. -/
def punitIso : coyoneda.obj (Opposite.op PUnit) ≅ 𝟭 (Type v₁) :=
  NatIso.ofComponents fun X =>
    { hom := fun f => f ⟨⟩
      inv := fun x _ => x }

/-- Taking the `unop` of morphisms is a natural isomorphism. -/
@[simps!]
def objOpOp (X : C) : coyoneda.obj (op (op X)) ≅ yoneda.obj X :=
  NatIso.ofComponents fun _ => (opEquiv _ _).toIso

end Coyoneda

namespace Functor

/-- A functor `F : Cᵒᵖ ⥤ Type v₁` is representable if there is object `X` so `F ≅ yoneda.obj X`.

See <https://stacks.math.columbia.edu/tag/001Q>.
-/
class Representable (F : Cᵒᵖ ⥤ Type v₁) : Prop where
  /-- `Hom(-,X) ≅ F` via `f` -/
  has_representation : ∃ (X : _), Nonempty (yoneda.obj X ≅ F)

instance {X : C} : Representable (yoneda.obj X) where has_representation := ⟨X, ⟨Iso.refl _⟩⟩

/-- A functor `F : C ⥤ Type v₁` is corepresentable if there is object `X` so `F ≅ coyoneda.obj X`.

See <https://stacks.math.columbia.edu/tag/001Q>.
-/
class Corepresentable (F : C ⥤ Type v₁) : Prop where
  /-- `Hom(X,-) ≅ F` via `f` -/
  has_corepresentation : ∃ (X : _), Nonempty (coyoneda.obj X ≅ F)

instance {X : Cᵒᵖ} : Corepresentable (coyoneda.obj X) where
  has_corepresentation := ⟨X, ⟨Iso.refl _⟩⟩

-- instance : corepresentable (𝟭 (Type v₁)) :=
-- corepresentable_of_nat_iso (op punit) coyoneda.punit_iso
section Representable

variable (F : Cᵒᵖ ⥤ Type v₁)
variable [hF : F.Representable]

/-- The representing object for the representable functor `F`. -/
noncomputable def reprX : C := hF.has_representation.choose

/-- An isomorphism between a representable `F` and a functor of the
form `C(-, F.reprX)`.  Note the components `F.reprW.app X`
definitionally have type `(X.unop ⟶ F.repr_X) ≅ F.obj X`.
-/
noncomputable def reprW : yoneda.obj F.reprX ≅ F :=
  Representable.has_representation.choose_spec.some

/-- The representing element for the representable functor `F`, sometimes called the universal
element of the functor.
-/
noncomputable def reprx : F.obj (op F.reprX) :=
  F.reprW.hom.app (op F.reprX) (𝟙 F.reprX)

theorem reprW_app_hom (X : Cᵒᵖ) (f : unop X ⟶ F.reprX) :
    (F.reprW.app X).hom f = F.map f.op F.reprx := by
  simp only [yoneda_obj_obj, Iso.app_hom, op_unop, reprx, ← FunctorToTypes.naturality,
    yoneda_obj_map, unop_op, Quiver.Hom.unop_op, Category.comp_id]

end Representable

section Corepresentable

variable (F : C ⥤ Type v₁)
variable [hF : F.Corepresentable]

/-- The representing object for the corepresentable functor `F`. -/
noncomputable def coreprX : C :=
  hF.has_corepresentation.choose.unop

/-- An isomorphism between a corepresnetable `F` and a functor of the form
`C(F.corepr X, -)`. Note the components `F.coreprW.app X`
definitionally have type `F.corepr_X ⟶ X ≅ F.obj X`.
-/
noncomputable def coreprW : coyoneda.obj (op F.coreprX) ≅ F :=
  hF.has_corepresentation.choose_spec.some

/-- The representing element for the corepresentable functor `F`, sometimes called the universal
element of the functor.
-/
noncomputable def coreprx : F.obj F.coreprX :=
  F.coreprW.hom.app F.coreprX (𝟙 F.coreprX)

theorem coreprW_app_hom (X : C) (f : F.coreprX ⟶ X) :
    (F.coreprW.app X).hom f = F.map f F.coreprx := by
  simp only [coyoneda_obj_obj, unop_op, Iso.app_hom, coreprx, ← FunctorToTypes.naturality,
    coyoneda_obj_map, Category.id_comp]

end Corepresentable

end Functor

theorem representable_of_natIso (F : Cᵒᵖ ⥤ Type v₁) {G} (i : F ≅ G) [F.Representable] :
    G.Representable :=
  { has_representation := ⟨F.reprX, ⟨F.reprW ≪≫ i⟩⟩ }

theorem corepresentable_of_natIso (F : C ⥤ Type v₁) {G} (i : F ≅ G) [F.Corepresentable] :
    G.Corepresentable :=
  { has_corepresentation := ⟨op F.coreprX, ⟨F.coreprW ≪≫ i⟩⟩ }

instance : Functor.Corepresentable (𝟭 (Type v₁)) :=
  corepresentable_of_natIso (coyoneda.obj (op PUnit)) Coyoneda.punitIso

open Opposite

variable (C)

-- We need to help typeclass inference with some awkward universe levels here.
instance prodCategoryInstance1 : Category ((Cᵒᵖ ⥤ Type v₁) × Cᵒᵖ) :=
  CategoryTheory.prod.{max u₁ v₁, v₁} (Cᵒᵖ ⥤ Type v₁) Cᵒᵖ

instance prodCategoryInstance2 : Category (Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) :=
  CategoryTheory.prod.{v₁, max u₁ v₁} Cᵒᵖ (Cᵒᵖ ⥤ Type v₁)

open Yoneda

section YonedaLemma

variable {C}

/-- We have a type-level equivalence between natural transformations from the yoneda embedding
and elements of `F.obj X`, without any universe switching.
-/
def yonedaEquiv {X : C} {F : Cᵒᵖ ⥤ Type v₁} : (yoneda.obj X ⟶ F) ≃ F.obj (op X) where
  toFun η := η.app (op X) (𝟙 X)
  invFun ξ := { app := fun Y f ↦ F.map f.op ξ }
  left_inv := by
    intro η
    ext Y f
    dsimp
    rw [← FunctorToTypes.naturality]
    simp
  right_inv := by intro ξ; simp

theorem yonedaEquiv_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F) :
    yonedaEquiv f = f.app (op X) (𝟙 X) :=
  rfl

@[simp]
theorem yonedaEquiv_symm_app_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (x : F.obj (op X)) (Y : Cᵒᵖ)
    (f : Y.unop ⟶ X) : (yonedaEquiv.symm x).app Y f = F.map f.op x :=
  rfl

lemma yonedaEquiv_naturality {X Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.map g.op (yonedaEquiv f) = yonedaEquiv (yoneda.map g ≫ f) := by
  change (f.app (op X) ≫ F.map g.op) (𝟙 X) = f.app (op Y) (𝟙 Y ≫ g)
  rw [← f.naturality]
  dsimp
  simp

lemma yonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.map g (yonedaEquiv f) = yonedaEquiv (yoneda.map g.unop ≫ f) :=
  yonedaEquiv_naturality _ _

lemma yonedaEquiv_comp {X : C} {F G : Cᵒᵖ ⥤ Type v₁} (α : yoneda.obj X ⟶ F) (β : F ⟶ G) :
    yonedaEquiv (α ≫ β) = β.app _ (yonedaEquiv α) :=
  rfl

lemma yonedaEquiv_yoneda_map {X Y : C} (f : X ⟶ Y) : yonedaEquiv (yoneda.map f) = f := by
  rw [yonedaEquiv_apply]
  simp

lemma yonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Cᵒᵖ ⥤ Type v₁} (t : F.obj X) :
    yonedaEquiv.symm (F.map f t) = yoneda.map f.unop ≫ yonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := yonedaEquiv.surjective t
  rw [yonedaEquiv_naturality', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Two morphisms of presheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `yoneda.obj X ⟶ P` agree. -/
lemma hom_ext_yoneda {P Q : Cᵒᵖ ⥤ Type v₁} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : yoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using congr_arg (yonedaEquiv) (h _ (yonedaEquiv.symm x))

variable (C)

/-- The "Yoneda evaluation" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `F.obj X`, functorially in both `X` and `F`.
-/
def yonedaEvaluation : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  evaluationUncurried Cᵒᵖ (Type v₁) ⋙ uliftFunctor

@[simp]
theorem yonedaEvaluation_map_down (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q)
    (x : (yonedaEvaluation C).obj P) :
    ((yonedaEvaluation C).map α x).down = α.2.app Q.1 (P.2.map α.1 x.down) :=
  rfl

/-- The "Yoneda pairing" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `yoneda.op.obj X ⟶ F`, functorially in both `X` and `F`.
-/
def yonedaPairing : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  Functor.prod yoneda.op (𝟭 (Cᵒᵖ ⥤ Type v₁)) ⋙ Functor.hom (Cᵒᵖ ⥤ Type v₁)

-- Porting note (#5229): we need to provide this `@[ext]` lemma separately,
-- as `ext` will not look through the definition.
@[ext]
lemma yonedaPairingExt {X : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)} {x y : (yonedaPairing C).obj X}
    (w : ∀ Y, x.app Y = y.app Y) : x = y :=
  NatTrans.ext (funext w)

@[simp]
theorem yonedaPairing_map (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) (β : (yonedaPairing C).obj P) :
    (yonedaPairing C).map α β = yoneda.map α.1.unop ≫ β ≫ α.2 :=
  rfl

universe w in
variable {C} in
/-- A bijection `(yoneda.obj X ⋙ uliftFunctor ⟶ F) ≃ F.obj (op X)` which is a variant
of `yonedaEquiv` with heterogeneous universes. -/
def yonedaCompUliftFunctorEquiv (F : Cᵒᵖ ⥤ Type max v₁ w) (X : C) :
    (yoneda.obj X ⋙ uliftFunctor ⟶ F) ≃ F.obj (op X) where
  toFun φ := φ.app (op X) (ULift.up (𝟙 _))
  invFun f :=
    { app := fun Y x => F.map (ULift.down x).op f }
  left_inv φ := by
    ext Y f
    dsimp
    rw [← FunctorToTypes.naturality]
    dsimp
    rw [Category.comp_id]
    rfl
  right_inv f := by aesop_cat

/-- The Yoneda lemma asserts that the Yoneda pairing
`(X : Cᵒᵖ, F : Cᵒᵖ ⥤ Type) ↦ (yoneda.obj (unop X) ⟶ F)`
is naturally isomorphic to the evaluation `(X, F) ↦ F.obj X`.

See <https://stacks.math.columbia.edu/tag/001P>.
-/
def yonedaLemma : yonedaPairing C ≅ yonedaEvaluation C :=
  NatIso.ofComponents
    (fun X ↦ Equiv.toIso (yonedaEquiv.trans Equiv.ulift.symm))
    (by intro (X, F) (Y, G) f
        ext (a : yoneda.obj X.unop ⟶ F)
        apply ULift.ext
        simp only [Functor.prod_obj, Functor.id_obj, types_comp_apply, yonedaEvaluation_map_down]
        erw [Equiv.ulift_symm_down, Equiv.ulift_symm_down]
        dsimp [yonedaEquiv]
        simp [← FunctorToTypes.naturality])

variable {C}

/- Porting note: this used to be two calls to `tidy` -/
/-- The curried version of yoneda lemma when `C` is small. -/
def curriedYonedaLemma {C : Type u₁} [SmallCategory C] :
    (yoneda.op ⋙ coyoneda : Cᵒᵖ ⥤ (Cᵒᵖ ⥤ Type u₁) ⥤ Type u₁) ≅ evaluation Cᵒᵖ (Type u₁) :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun F ↦ Equiv.toIso yonedaEquiv)) (by
    intro X Y f
    ext a b
    dsimp [yonedaEquiv]
    simp [← FunctorToTypes.naturality])

/-- The curried version of the Yoneda lemma. -/
def largeCurriedYonedaLemma {C : Type u₁} [Category.{v₁} C] :
    yoneda.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type v₁) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun Y => Equiv.toIso <| yonedaEquiv.trans Equiv.ulift.symm)
      (by
        intros Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using yonedaEquiv_comp _ _))
    (by
      intros Y Z f
      ext F g
      rw [← ULift.down_inj]
      simpa using (yonedaEquiv_naturality _ _).symm)

/-- Version of the Yoneda lemma where the presheaf is fixed but the argument varies. -/
def yonedaOpCompYonedaObj {C : Type u₁} [Category.{v₁} C] (P : Cᵒᵖ ⥤ Type v₁) :
    yoneda.op ⋙ yoneda.obj P ≅ P ⋙ uliftFunctor.{u₁} :=
  isoWhiskerRight largeCurriedYonedaLemma ((evaluation _ _).obj P)

/-- The curried version of yoneda lemma when `C` is small. -/
def curriedYonedaLemma' {C : Type u₁} [SmallCategory C] :
    yoneda ⋙ (whiskeringLeft Cᵒᵖ (Cᵒᵖ ⥤ Type u₁)ᵒᵖ (Type u₁)).obj yoneda.op
      ≅ 𝟭 (Cᵒᵖ ⥤ Type u₁) :=
  NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun X ↦ Equiv.toIso yonedaEquiv) (by
    intro X Y f
    ext a
    dsimp [yonedaEquiv]
    simp [← FunctorToTypes.naturality]))

lemma isIso_of_yoneda_map_bijective {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (T : C), Function.Bijective (fun (x : T ⟶ X) => x ≫ f)) :
    IsIso f := by
  obtain ⟨g, hg : g ≫ f = 𝟙 Y⟩ := (hf Y).2 (𝟙 Y)
  exact ⟨g, (hf _).1 (by aesop_cat), hg⟩

attribute [nolint simpNF] CategoryTheory.yonedaEquiv_yoneda_map
end CategoryTheory
