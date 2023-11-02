/-
Copyright (c) 2023 Andrea Laretto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Laretto
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.Tactic.CategoryTheory.Reassoc

/-!
# Dinatural transformations

Dinatural transformations are special kinds of transformations between
functors `F G : Cᵒᵖ × C ⥤ D` which depend both covariantly and contravariantly
on the same category (also known as difunctors).

A dinatural transformation is a family of morphisms given only on *the diagonal* of the two
functors, and is such that a certain naturality hexagon commutes.

Note that dinatural transformations cannot be composed with each other (since the outer
hexagon does not commute in general), but can still be "pre/post-composed" with
ordinary natural transformations.
-/

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

open Opposite

/-- Dinatural transformations between two (di)functors.
-/
structure DinatTrans (F G : Cᵒᵖ × C ⥤ D) : Type max u₁ v₂ where
  /-- The component of a natural transformation. -/
  app : ∀ X : C, F.obj (op X, X) ⟶ G.obj (op X, X)
  /-- The commutativity square for a given morphism. -/
  dinaturality :
    ∀ {X Y : C}
      (f : X ⟶ Y),
      F.map (X := ⟨_,_⟩) (Y := ⟨_,_⟩) (f.op, 𝟙 _) ≫ app X ≫ G.map (Y := ⟨_,_⟩) (𝟙 (op _), f) =
      F.map (X := ⟨_,_⟩) (Y := ⟨_,_⟩) (𝟙 (op _), f) ≫ app Y ≫ G.map (Y := ⟨_,_⟩) (f.op, 𝟙 _) :=
        by aesop_cat

/-- Notation for dinatural transformations. -/
infixr:50 " ⤞ " => DinatTrans

/-- Opposite of a product category.
-/
@[simp]
def op_prod : (Cᵒᵖ × C) ⥤ (Cᵒᵖ × C)ᵒᵖ where
  obj := λ ⟨Cop,C⟩ => op ⟨op C, Cop.unop⟩
  map := λ ⟨f,g⟩ => op ⟨g.op, f.unop⟩

/-- Opposite of a difunctor.
-/
@[simp]
def Functor.diop (F : Cᵒᵖ × C ⥤ D) : Cᵒᵖ × C ⥤ Dᵒᵖ := op_prod ⋙ F.op

variable {F G H : Cᵒᵖ × C ⥤ D}

/-- Post-composition with a natural transformation.
-/
def DinatTrans.nat_comp (δ : F ⤞ G) (α : G ⟶ H) : F ⤞ H
    where
  app X := δ.app X ≫ α.app (op X, X)
  dinaturality f := by
    simp;
    rw [←α.naturality]
    rw [reassoc_of% δ.dinaturality f]
    rw [←α.naturality]

/-- Pre-composition with a natural transformation.
-/
def DinatTrans.comp_nat (δ : G ⤞ H) (α : F ⟶ G) : F ⤞ H
    where
  app X := α.app (op X, X) ≫ δ.app X
  dinaturality f := by
    simp
    erw [reassoc_of% α.naturality]
    rw [δ.dinaturality f]
    erw [reassoc_of% α.naturality]

/-- Opposite of a dinatural transformation.
-/
def DinatTrans.op (α : F ⤞ G) : G.diop ⤞ F.diop
    where
  app X := (α.app X).op
  dinaturality f := Quiver.Hom.unop_inj (by simp; exact α.dinaturality f)
