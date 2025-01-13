/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# A categorical description of the center of a ring

In this file we prove that the center of a ring `R` is isomorphic to `End (𝟭 R-Mod)` the
endomorphism ring of the identity functor on the category of `R`-modules. Consequently, the ring
structure of a commutative ring is complete determined by its module category.

## Main results

- `Subring.centerEquivEndIdFunctor`: the center of a ring `R` is isomorphic to `End (𝟭 R-Mod)`.
- `RingEquiv.ofModuleCatEquiv`: if two commutative rings have equivalent module categories, they are
  isomorphic as rings.

-/

universe u u' v v'

variable (R : Type u) [Ring R]

open CategoryTheory

/--
For any ring `R`, the center of `R` is isomorphic to `End (𝟭 (ModuleCat R))`, the endomorphism ring
of the identity functor on the category of `R`-modules.
-/
@[simps]
def Subring.centerEquivEndIdFunctor [Small.{v} R] :
    Subring.center R ≃+* End (𝟭 (ModuleCat.{v} R)) where
  toFun x :=
  { app M := ModuleCat.ofHom
      { toFun := (x.1 • ·)
        map_add' := by aesop
        map_smul' r := by simp [← mul_smul, Subring.mem_center_iff.1 x.2 r] } }
  invFun f := ⟨(equivShrink R).symm <| f.app (.of R <| Shrink.{v} R) |>.hom (1 : Shrink.{v} R), by
    rw [Subring.mem_center_iff]
    intro r
    have := congr((equivShrink R).symm ($(f.naturality (X := .of R <| Shrink.{v} R) (Y := .of R <| Shrink.{v} R)
      (ModuleCat.ofHom
      { toFun x := x * equivShrink R r
        map_add' := by simp [add_mul]
        map_smul' := by intros; ext; simp [mul_assoc] })).hom (1 : Shrink.{v} R)))
    simp only [Functor.id_obj, Functor.id_map, ModuleCat.hom_comp, LinearMap.coe_comp,
      LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, one_mul, equivShrink_symm_mul,
      Equiv.symm_apply_apply] at this
    erw [← this]
    have := congr((equivShrink R).symm
      $((f.app (ModuleCat.of R <| Shrink.{v} R)).hom.map_smul r (1 : Shrink.{v} R)))
    rw [show r • (1 : Shrink.{v} R) = equivShrink R r by ext; simp] at this
    simp only [Functor.id_obj, equivShrink_symm_smul, smul_eq_mul] at this
    exact this.symm⟩
  left_inv _ := by simp
  right_inv f := by
    apply NatTrans.ext
    ext M (m : M)
    simp only [Functor.id_obj, LinearMap.coe_mk, AddHom.coe_mk]
    have := congr($(f.naturality (X := .of R <| Shrink.{v} R) (Y := .of R M)
      (ModuleCat.ofHom
        { toFun x := (equivShrink R).symm x • m
          map_add' := by simp [add_smul]
          map_smul' x y := by simp [mul_smul] })).hom (1 : Shrink R))
    simp only [ModuleCat.of_coe, Functor.id_obj, Functor.id_map, ModuleCat.hom_comp,
      LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      equivShrink_symm_one, one_smul] at this
    exact this.symm
  map_mul' x y := by
    apply NatTrans.ext
    ext M (m : M)
    exact mul_smul x.1 y.1 m
  map_add' x y := by
    apply NatTrans.ext
    ext M (m : M)
    exact add_smul x.1 y.1 m

/--
For any two commutative rings `R` and `S`, if the categories of `R`-modules and `S`-modules are
equivalent, then `R` and `S` are isomorphic as rings.
-/
noncomputable def RingEquiv.ofModuleCatEquiv {R : Type u} {S : Type u'} [CommRing R] [CommRing S]
    [Small.{v} R] [Small.{v'} S]
    (e : ModuleCat.{v} R ≌ ModuleCat.{v'} S) : R ≃+* S :=
  letI : e.functor.Additive := Functor.additive_of_preserves_binary_products e.functor
  let i₁ : R ≃+* (⊤ : Subring R) := Subring.topEquiv.symm
  let i₂ : (⊤ : Subring R) ≃+* Subring.center R := Subring.center_eq_top R ▸ .refl _
  let i₄ : Subring.center S ≃+* (⊤ : Subring S) := Subring.center_eq_top S ▸ .refl _
  let i₅ : (⊤ : Subring S) ≃+* S := Subring.topEquiv
  let i : End (𝟭 (ModuleCat.{v} R)) ≃+* End (𝟭 (ModuleCat.{v'} S)) :=
  { toFun f := .of
      { app N :=
          e.counitInv.app N ≫ e.functor.map (f.app (e.inverse.obj N)) ≫
          e.counit.app N
        naturality M N g := by
          -- Is `aesop_cat` expected to solve this?
          have eq :=
            e.counitInv.app M ≫=
            congr(e.functor.map $(f.naturality (e.inverse.map g))) =≫
            e.counit.app N
          simpa using eq}
    invFun f := .of
      { app N := e.unit.app N ≫ e.inverse.map (f.app (e.functor.obj N)) ≫ e.unitInv.app N
        naturality M N g := by
          -- Is `aesop_cat` expected to solve this?
          have eq :=
            e.unit.app M ≫=
            congr(e.inverse.map $(f.naturality (e.functor.map g))) =≫
            e.unitInv.app N
          simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.map_comp,
            Equivalence.inv_fun_map, Category.assoc, Iso.hom_inv_id_app_assoc,
            Iso.hom_inv_id_app, Category.comp_id] at eq
          simpa using eq }
    left_inv f := by
      apply NatTrans.ext
      ext N : 1
      have eq := f.naturality (e.unit.app N) =≫ e.unitInv.app N
      simpa [End.of] using eq
    right_inv f := by
      apply NatTrans.ext
      ext N : 1
      have eq := e.counitInv.app N ≫= f.naturality (e.counit.app N) |>.symm
      simpa [End.of] using eq
    map_mul' f g := by
      apply NatTrans.ext
      ext N : 1
      simp only [Functor.id_obj, Functor.comp_obj, End.mul_def, NatTrans.comp_app, Functor.map_comp,
        Category.assoc]
      simp [End.of]
    map_add' f g := by
      apply NatTrans.ext
      ext N : 1
      change _≫ e.functor.map (_ + _) ≫ _  = _ ≫ _ + _ ≫ _
      simp [Functor.map_add] }
  i₁.trans <| i₂.trans <| (Subring.centerEquivEndIdFunctor R).trans <|
    i.trans <| (Subring.centerEquivEndIdFunctor S).symm.trans <| i₄.trans i₅
