/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Whiskering

#align_import category_theory.sites.adjunction from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!

In this file, we show that an adjunction `F ⊣ G` induces an adjunction between
categories of sheaves, under certain hypotheses on `F` and `G`.

-/


namespace CategoryTheory

open GrothendieckTopology CategoryTheory Limits Opposite

universe w₁' w₁ w₂' w₂ v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {D : Type w₁} [Category.{w₁'} D]

variable {E : Type w₂} [Category.{w₂'} E]

variable {F : D ⥤ E} {G : E ⥤ D}

variable [HasWeakSheafify J D] [HasSheafCompose J F]

-- variable [∀ (X : C) (S : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (S.index P).multicospan F]

namespace Sheaf

noncomputable section

/-- This is the functor sending a sheaf `X : Sheaf J E` to the sheafification
of `X ⋙ G`. -/
abbrev composeAndSheafify (G : E ⥤ D) : Sheaf J E ⥤ Sheaf J D :=
  sheafToPresheaf J E ⋙ (whiskeringRight _ _ _).obj G ⋙ presheafToSheaf J D

/-- An adjunction `adj : G ⊣ F` with `F : D ⥤ E` and `G : E ⥤ D` induces an adjunction
between `Sheaf J D` and `Sheaf J E`, in contexts where one can sheafify `D`-valued presheaves,
and `F` preserves the correct limits. -/
def adjunction (adj : G ⊣ F) : composeAndSheafify J G ⊣ sheafCompose J F :=
  Adjunction.restrictFullyFaithful (sheafToPresheaf _ _) (𝟭 _)
    ((adj.whiskerRight Cᵒᵖ).comp (sheafificationAdjunction J D)) (Iso.refl _) (Iso.refl _)
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.adjunction CategoryTheory.Sheaf.adjunction

instance [IsRightAdjoint F] : IsRightAdjoint (sheafCompose J F) :=
  ⟨_, adjunction J (Adjunction.ofRightAdjoint F)⟩

section ForgetToType

/-- This is the functor sending a sheaf of types `X` to the sheafification of `X ⋙ G`. -/
abbrev composeAndSheafifyFromTypes (G : Type max v u ⥤ D) : SheafOfTypes J ⥤ Sheaf J D :=
  (sheafEquivSheafOfTypes J).inverse ⋙ composeAndSheafify _ G
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.compose_and_sheafify_from_types CategoryTheory.Sheaf.composeAndSheafifyFromTypes

variable [ConcreteCategory D] [HasSheafCompose J (forget D)]

/-- The forgetful functor from `Sheaf J D` to sheaves of types, for a concrete category `D`
whose forgetful functor preserves the correct limits. -/
abbrev _root_.CategoryTheory.sheafForget : Sheaf J D ⥤ SheafOfTypes J :=
  sheafCompose J (forget D) ⋙ (sheafEquivSheafOfTypes J).functor
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf_forget CategoryTheory.sheafForget

/-- A variant of the adjunction between sheaf categories, in the case where the right adjoint
is the forgetful functor to sheaves of types. -/
def adjunctionToTypes {G : Type max v u ⥤ D} (adj : G ⊣ forget D) :
    composeAndSheafifyFromTypes J G ⊣ sheafForget J :=
  (sheafEquivSheafOfTypes J).symm.toAdjunction.comp (adjunction J adj)
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.adjunction_to_types CategoryTheory.Sheaf.adjunctionToTypes

instance [IsRightAdjoint (forget D)] : IsRightAdjoint (sheafForget J : Sheaf J D ⥤ _) :=
  ⟨_, adjunctionToTypes J (Adjunction.ofRightAdjoint (forget D))⟩

end ForgetToType

end

end Sheaf

end CategoryTheory
