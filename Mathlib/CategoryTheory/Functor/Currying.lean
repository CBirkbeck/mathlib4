/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Products.Bifunctor

#align_import category_theory.functor.currying from "leanprover-community/mathlib"@"369525b73f229ccd76a6ec0e0e0bf2be57599768"

/-!
# Curry and uncurry, as functors.

We define `curry : ((C × D) ⥤ E) ⥤ (C ⥤ (D ⥤ E))` and `uncurry : (C ⥤ (D ⥤ E)) ⥤ ((C × D) ⥤ E)`,
and verify that they provide an equivalence of categories
`currying : (C ⥤ (D ⥤ E)) ≌ ((C × D) ⥤ E)`.

-/


namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {B : Type u₁} [Category.{v₁} B] {C : Type u₂} [Category.{v₂} C] {D : Type u₃}
  [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E]

/-- The uncurrying functor, taking a functor `C ⥤ (D ⥤ E)` and producing a functor `(C × D) ⥤ E`.
-/
@[simps]
def uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E
    where
  obj F :=
    { obj := fun X => (F.obj X.1).obj X.2
      map := fun {X} {Y} f => (F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2
      map_comp := fun f g => by
        simp only [prod_comp_fst, prod_comp_snd, Functor.map_comp, NatTrans.comp_app,
          Category.assoc]
        slice_lhs 2 3 => rw [← NatTrans.naturality]
        -- ⊢ NatTrans.app (F.map f.fst) X✝.snd ≫ ((F.obj Y✝.fst).map f.snd ≫ NatTrans.app …
        rw [Category.assoc] }
        -- 🎉 no goals
  map T :=
    { app := fun X => (T.app X.1).app X.2
      naturality := fun X Y f => by
        simp only [prod_comp_fst, prod_comp_snd, Category.comp_id, Category.assoc, Functor.map_id,
          Functor.map_comp, NatTrans.id_app, NatTrans.comp_app]
        slice_lhs 2 3 => rw [NatTrans.naturality]
        -- ⊢ NatTrans.app (X✝.map f.fst) X.snd ≫ NatTrans.app (NatTrans.app T Y.fst) X.sn …
        slice_lhs 1 2 => rw [← NatTrans.comp_app, NatTrans.naturality, NatTrans.comp_app]
        -- ⊢ (NatTrans.app (NatTrans.app T X.fst) X.snd ≫ NatTrans.app (Y✝.map f.fst) X.s …
        rw [Category.assoc] }
        -- 🎉 no goals
#align category_theory.uncurry CategoryTheory.uncurry

/-- The object level part of the currying functor. (See `curry` for the functorial version.)
-/
def curryObj (F : C × D ⥤ E) : C ⥤ D ⥤ E
    where
  obj X :=
    { obj := fun Y => F.obj (X, Y)
      map := fun g => F.map (𝟙 X, g)
      map_id := fun Y => by simp only [F.map_id]; rw [←prod_id]; exact F.map_id ⟨X,Y⟩
                            -- ⊢ F.map (𝟙 X, 𝟙 Y) = 𝟙 (F.obj (X, Y))
                                                  -- ⊢ F.map (𝟙 (X, Y)) = 𝟙 (F.obj (X, Y))
                                                                 -- 🎉 no goals
      map_comp := fun f g => by simp [←F.map_comp]}
                                -- 🎉 no goals
  map f :=
    { app := fun Y => F.map (f, 𝟙 Y)
      naturality := fun {Y} {Y'} g => by simp [←F.map_comp] }
                                         -- 🎉 no goals
  map_id := fun X => by ext Y; exact F.map_id _
                        -- ⊢ NatTrans.app ({ obj := fun X => Functor.mk { obj := fun Y => F.obj (X, Y), m …
                               -- 🎉 no goals
  map_comp := fun f g => by ext Y; dsimp; simp [←F.map_comp]
                            -- ⊢ NatTrans.app ({ obj := fun X => Functor.mk { obj := fun Y => F.obj (X, Y), m …
                                   -- ⊢ F.map (f ≫ g, 𝟙 Y) = F.map (f, 𝟙 Y) ≫ F.map (g, 𝟙 Y)
                                          -- 🎉 no goals
#align category_theory.curry_obj CategoryTheory.curryObj

/-- The currying functor, taking a functor `(C × D) ⥤ E` and producing a functor `C ⥤ (D ⥤ E)`.
-/
@[simps! obj_obj_obj obj_obj_map obj_map_app map_app_app]
def curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E where
  obj F := curryObj F
  map T :=
    { app := fun X =>
        { app := fun Y => T.app (X, Y)
          naturality := fun Y Y' g => by
            dsimp [curryObj]
            -- ⊢ X✝.map (𝟙 X, g) ≫ NatTrans.app T (X, Y') = NatTrans.app T (X, Y) ≫ Y✝.map (𝟙 …
            rw [NatTrans.naturality] }
            -- 🎉 no goals
      naturality := fun X X' f => by
        ext; dsimp [curryObj]
        -- ⊢ NatTrans.app (((fun F => curryObj F) X✝).map f ≫ (fun X => NatTrans.mk fun Y …
             -- ⊢ X✝.map (f, 𝟙 x✝) ≫ NatTrans.app T (X', x✝) = NatTrans.app T (X, x✝) ≫ Y✝.map …
        rw [NatTrans.naturality] }
        -- 🎉 no goals
#align category_theory.curry CategoryTheory.curry

-- create projection simp lemmas even though this isn't a `{ .. }`.
/-- The equivalence of functor categories given by currying/uncurrying.
-/
@[simps!]
def currying : C ⥤ D ⥤ E ≌ C × D ⥤ E :=
  Equivalence.mk uncurry curry
    (NatIso.ofComponents fun F =>
        NatIso.ofComponents fun X => NatIso.ofComponents fun Y => Iso.refl _)
    (NatIso.ofComponents fun F => NatIso.ofComponents (fun X => eqToIso (by simp))
                                                                            -- 🎉 no goals
      (by intros X Y f; cases X; cases Y; cases f; dsimp at *; rw [←F.map_comp]; simp ))
          -- ⊢ ((curry ⋙ uncurry).obj F).map f ≫ ((fun X => eqToIso (_ : F.obj (X.fst, X.sn …
                        -- ⊢ ((curry ⋙ uncurry).obj F).map f ≫ ((fun X => eqToIso (_ : F.obj (X.fst, X.sn …
                                 -- ⊢ ((curry ⋙ uncurry).obj F).map f ≫ ((fun X => eqToIso (_ : F.obj (X.fst, X.sn …
                                          -- ⊢ ((curry ⋙ uncurry).obj F).map (fst✝, snd✝) ≫ ((fun X => eqToIso (_ : F.obj ( …
                                                   -- ⊢ (F.map (fst✝, 𝟙 snd✝²) ≫ F.map (𝟙 fst✝¹, snd✝)) ≫ 𝟙 (F.obj (fst✝¹, snd✝¹)) = …
                                                               -- ⊢ F.map ((fst✝, 𝟙 snd✝²) ≫ (𝟙 fst✝¹, snd✝)) ≫ 𝟙 (F.obj (fst✝¹, snd✝¹)) = 𝟙 (F. …
                                                                                 -- 🎉 no goals
#align category_theory.currying CategoryTheory.currying

/-- `F.flip` is isomorphic to uncurrying `F`, swapping the variables, and currying. -/
@[simps!]
def flipIsoCurrySwapUncurry (F : C ⥤ D ⥤ E) : F.flip ≅ curry.obj (Prod.swap _ _ ⋙ uncurry.obj F) :=
  NatIso.ofComponents fun d => NatIso.ofComponents fun c => Iso.refl _
#align category_theory.flip_iso_curry_swap_uncurry CategoryTheory.flipIsoCurrySwapUncurry

/-- The uncurrying of `F.flip` is isomorphic to
swapping the factors followed by the uncurrying of `F`. -/
@[simps!]
def uncurryObjFlip (F : C ⥤ D ⥤ E) : uncurry.obj F.flip ≅ Prod.swap _ _ ⋙ uncurry.obj F :=
  NatIso.ofComponents fun p => Iso.refl _
#align category_theory.uncurry_obj_flip CategoryTheory.uncurryObjFlip

variable (B C D E)

/-- A version of `CategoryTheory.whiskeringRight` for bifunctors, obtained by uncurrying,
applying `whiskeringRight` and currying back
-/
@[simps!]
def whiskeringRight₂ : (C ⥤ D ⥤ E) ⥤ (B ⥤ C) ⥤ (B ⥤ D) ⥤ B ⥤ E :=
  uncurry ⋙
    whiskeringRight _ _ _ ⋙ (whiskeringLeft _ _ _).obj (prodFunctorToFunctorProd _ _ _) ⋙ curry
#align category_theory.whiskering_right₂ CategoryTheory.whiskeringRight₂

end CategoryTheory
