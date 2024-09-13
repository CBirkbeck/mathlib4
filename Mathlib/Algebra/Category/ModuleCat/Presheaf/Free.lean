/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Joel Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-! The free presheaf of modules on a presheaf of sets

In this file, given a presheaf of rings `R` on a category `C`,
we construct the functor
`PresheafOfModules.free (Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules.{u} R`
which sends a presheaf of types to the corresponding presheaf of free modules.
`PresheafOfModules.freeAdjunction` shows that this functor is the left
adjoint to the forget functor.

## Notes

This contribution was created as part of the AIM workshop
"Formalizing algebraic geometry" in June 2024.

-/

universe u v₁ u₁

open CategoryTheory

-- this should be moved to `ModuleCat.Adjunctions`
namespace ModuleCat

section

variable {R : Type u} [Ring R]

noncomputable def freeMk {X : Type u} (x : X) : (free R).obj X := Finsupp.single x 1

@[ext 1200]
lemma free_hom_ext {X : Type u} {M : ModuleCat.{u} R} {f g : (free R).obj X ⟶ M}
    (h : ∀ (x : X), f (freeMk x) = g (freeMk x)) :
    f = g :=
  (Finsupp.lhom_ext' (fun x ↦ LinearMap.ext_ring (h x)))

noncomputable def freeDesc {X : Type u} {M : ModuleCat.{u} R} (f : X ⟶ M) :
    (free R).obj X ⟶ M :=
  Finsupp.lift M R X f

@[simp]
lemma freeDesc_apply {X : Type u} {M : ModuleCat.{u} R} (f : X ⟶ M) (x : X) :
    freeDesc f (freeMk x : of R (X →₀ R)) = f x := by
  dsimp [freeDesc]
  erw [Finsupp.lift_apply, Finsupp.sum_single_index]
  all_goals simp

@[simp]
lemma free_map_apply {X Y : Type u} (f : X → Y) (x : X) :
    (free R).map f (freeMk x) = freeMk (f x) := by
  apply Finsupp.mapDomain_single

end

end ModuleCat

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{u})

variable {R} in
@[simps]
noncomputable def freeObj (F : Cᵒᵖ ⥤ Type u) : PresheafOfModules.{u} R where
  obj := fun X ↦ (ModuleCat.free (R.obj X)).obj (F.obj X)
  map := fun {X Y} f ↦ ModuleCat.freeDesc
      (fun x ↦ ModuleCat.freeMk (R := R.obj Y) (F.map f x))
  map_id := by aesop

@[simps]
noncomputable def free : (Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules.{u} R where
  obj := freeObj
  map {F G} φ :=
    { app := fun X ↦ (ModuleCat.free (R.obj X)).map (φ.app X)
      naturality := fun {X Y} f ↦ by
        dsimp
        ext x
        simp only [ModuleCat.coe_comp, Function.comp_apply, ModuleCat.freeDesc_apply,
          ModuleCat.restrictScalars.map_apply, ModuleCat.free_map_apply]
        congr 1
        exact NatTrans.naturality_apply φ f x }

section

variable {R}

variable {F : Cᵒᵖ ⥤ Type u} {G : PresheafOfModules.{u} R}

@[simps]
noncomputable def freeObjDesc (φ : F ⟶ G.presheaf ⋙ forget _) : freeObj F ⟶ G where
  app X := ModuleCat.freeDesc (φ.app X)
  naturality {X Y} f := by
    dsimp
    ext x
    simpa using NatTrans.naturality_apply φ f x

variable (F R) in
@[simps]
noncomputable def freeAdjunctionUnit : F ⟶ (freeObj (R := R) F).presheaf ⋙ forget _ where
  app X x := ModuleCat.freeMk x
  naturality X Y f := by ext; simp [presheaf]

noncomputable def freeHomEquiv : (freeObj F ⟶ G) ≃ (F ⟶ G.presheaf ⋙ forget _) where
  toFun ψ := freeAdjunctionUnit R F ≫ whiskerRight ((toPresheaf _).map ψ) _
  invFun φ := freeObjDesc φ
  left_inv ψ := by ext1 X; dsimp; ext x; simp [toPresheaf]
  right_inv φ := by ext; simp [toPresheaf]

lemma free_hom_ext {ψ ψ' : freeObj F ⟶ G}
    (h : freeAdjunctionUnit R F ≫ whiskerRight ((toPresheaf _).map ψ) _ =
      freeAdjunctionUnit R F ≫ whiskerRight ((toPresheaf _).map ψ') _ ): ψ = ψ' :=
  freeHomEquiv.injective h

variable (R)

noncomputable def freeAdjunction :
    free.{u} R ⊣ (toPresheaf R ⋙ (whiskeringRight _ _ _).obj (forget Ab)) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦ freeHomEquiv
      homEquiv_naturality_left_symm := fun {F₁ F₂ G} f g ↦ free_hom_ext
        (by ext; simp [freeHomEquiv, toPresheaf])
      homEquiv_naturality_right := fun {F G₁ G₂} f g ↦ rfl }

variable (F G) in
@[simp]
lemma freeAdjunction_homEquiv : (freeAdjunction R).homEquiv F G = freeHomEquiv := rfl

@[simp]
lemma freeAdjunction_unit_app :
    (freeAdjunction R).unit.app F = freeAdjunctionUnit R F := rfl

end

end PresheafOfModules
