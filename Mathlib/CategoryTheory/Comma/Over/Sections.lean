/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Closed.Cartesian

/-!
# The section functor as a right adjoint to the star functor

We show that if `C` is cartesian closed then `star I : C ⥤ Over I`
has a right adjoint `sectionsFunctor` whose object part is the object of sections
of `X` over `I`.

-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits MonoidalCategory CartesianClosed Adjunction Over

variable {C : Type u₁} [Category.{v₁} C]

-- this lemma is already PR'd in #21574
--https://github.com/leanprover-community/mathlib4/pull/21574/files
lemma Over.homMk_comp {I : C} {U V W : Over I}
    (f : U.left ⟶ V.left) (g : V.left ⟶ W.left) (w_f w_g) (w_fg := by aesop) :
    homMk (f ≫ g) w_fg = homMk f w_f ≫ homMk g w_g := by
  ext
  simp

attribute [local instance] hasBinaryProducts_of_hasTerminal_and_pullbacks
attribute [local instance] hasFiniteProducts_of_has_binary_and_terminal
attribute [local instance] ChosenFiniteProducts.ofFiniteProducts
attribute [local instance] monoidalOfChosenFiniteProducts

variable [HasTerminal C] [HasPullbacks C] [CartesianClosed C]

/-- The first leg of a cospan constructing a pullback diagram in `C used to define
the pushforward along `f`. -/
def curryId (I : C) : ⊤_ C ⟶ (I ⟹ I) :=
  CartesianClosed.curry (ChosenFiniteProducts.fst I (⊤_ C))

variable {I : C}

/-- The second leg of a cospan constructing a pullback diagram in `Over J` used to define
the pushforward along `f`. -/
def expMapFstProj (X : Over I) :
    (I ⟹ X.left) ⟶ (I ⟹ I) :=
  (exp I).map X.hom

namespace Over

/-- The object of sections of `X` over `I` in `C` defined by the following pullback diagram:

```
 sections X -->  I ⟹ X
   |               |
   |               |
   v               v
  ⊤_ C    ---->  I ⟹ I
```-/
abbrev sections (X : Over I) : C :=
  Limits.pullback (curryId I) ((exp I).map X.hom)

/-- The functoriality of `section`. -/
def sectionsMap {X X' : Over I} (u : X ⟶ X') :
    sections X ⟶ sections X' := by
  fapply pullback.map
  · exact 𝟙 _
  · exact (exp I).map u.left
  · exact 𝟙 _
  · simp only [comp_id, id_comp]
  · simp only [comp_id, ← Functor.map_comp, w]

@[simp]
lemma sectionsMap_id {X : Over I} : sectionsMap (𝟙 X) = 𝟙 _ := by
  apply pullback.hom_ext
  · aesop
  · simp [sectionsMap]

@[simp]
lemma sectionsMap_comp {X X' X'' : Over I} (u : X ⟶ X') (v : X' ⟶ X'') :
    sectionsMap (u ≫ v) = sectionsMap u ≫ sectionsMap v := by
  apply pullback.hom_ext
  · aesop
  · simp [sectionsMap]

variable (I)

@[simps]
def sectionsFunctor :
    Over I ⥤ C where
  obj X := sections X
  map u := sectionsMap u

variable {I}

/-- An auxiliary morphism used to define the currying of a morphism in `Over I` to a morphism
in `Over J`. See `pushforwardCurry`. -/
def sectionsCurryAux {X : Over I} {A : C} (u : (star I).obj A ⟶ X) :
    A ⟶ (I ⟹ X.left) :=
  CartesianClosed.curry (u.left)

/-- The currying operation `Hom ((star I).obj A) X → Hom A (I ⟹ X.left)`. -/
def sectionsCurry {X : Over I} {A : C} (u : (star I).obj A ⟶ X) :
    A ⟶ (sections X) := by
  apply pullback.lift (terminal.from A) (CartesianClosed.curry (u.left)) (uncurry_injective _)
  rw [uncurry_natural_left]
  simp [curryId, uncurry_natural_right, uncurry_curry]
  rfl

/-- The uncurrying operation `Hom A (I ⟹ section X) → Hom ((star I).obj A) X`. -/
def sectionsUncurry {X : Over I} {A : C} (v : A ⟶ (sections X)) :
    (star I).obj A ⟶ X := by
  let v₂ : A ⟶ (I ⟹ X.left) := v ≫ pullback.snd ..
  have w : terminal.from A ≫ (curryId I) = v₂ ≫ (exp I).map X.hom := by
    rw [IsTerminal.hom_ext terminalIsTerminal (terminal.from A ) (v ≫ (pullback.fst ..))]
    simp [v₂, pullback.condition]
  dsimp [curryId] at w
  have w' := homEquiv_naturality_right_square (F := MonoidalCategory.tensorLeft I)
    (adj := exp.adjunction I) _ _ _ _ w
  simp [CartesianClosed.curry] at w'
  refine Over.homMk (CartesianClosed.uncurry v₂) ?_
  · dsimp [CartesianClosed.uncurry] at *
    rw [← w']
    simp [star_obj_hom]
    rfl

@[reassoc (attr := simp)]
theorem sections_curry_uncurry {X : Over I} {A : C} (v : A ⟶ sections X) :
    sectionsCurry (sectionsUncurry v) = v := by
  dsimp [sectionsCurry, sectionsUncurry]
  let v₂ : A ⟶ (I ⟹ X.left) := v ≫ pullback.snd _ _
  apply pullback.hom_ext
  · simp
    rw [IsTerminal.hom_ext terminalIsTerminal (terminal.from A ) (v ≫ (pullback.fst ..))]
  · simp

@[reassoc (attr := simp)]
theorem sections_uncurry_curry {X : Over I} {A : C} (u : (star I).obj A ⟶ X) :
    sectionsUncurry (sectionsCurry u) = u := by
  dsimp [sectionsCurry, sectionsUncurry]
  ext
  simp

-- Thanks to Andrew Yang this proof got 8 lines shorter!
lemma whiskerLeft_prod_map {A A' : C} {g : A ⟶ A'} : I ◁ g = prod.map (𝟙 I) g := by
  ext
  · simp only [ChosenFiniteProducts.whiskerLeft_fst]
    exact (Category.comp_id _).symm.trans (prod.map_fst (𝟙 I) g).symm
  · simp only [ChosenFiniteProducts.whiskerLeft_snd]
    exact (prod.map_snd (𝟙 I) g).symm

def coreHomEquiv : CoreHomEquiv (star I)  (sectionsFunctor I) where
  homEquiv A X := {
    toFun := sectionsCurry
    invFun := sectionsUncurry
    left_inv := sections_uncurry_curry
    right_inv := sections_curry_uncurry
  }
  homEquiv_naturality_left_symm := by
    intro A' A X g v
    dsimp [sectionsCurry, sectionsUncurry, curryId]
    simp only [star_map]
    rw [← Over.homMk_comp]
    congr 1
    simp only [CartesianClosed.uncurry_natural_left, MonoidalCategory.whiskerLeft_comp]
    simp [whiskerLeft_prod_map]
  homEquiv_naturality_right := by
    intro A X' X u g
    dsimp [sectionsCurry, sectionsUncurry, curryId]
    apply pullback.hom_ext (IsTerminal.hom_ext terminalIsTerminal _ _)
    simp [sectionsMap, curryId]
    rw [← CartesianClosed.curry_natural_right]

/-- The adjunction between the star functor and the sections functor. -/
def starSectionAdjunction : (star I) ⊣ (sectionsFunctor I) :=
  .mkOfHomEquiv coreHomEquiv

end Over

end CategoryTheory
