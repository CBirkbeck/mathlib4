import Mathlib.Tactic.CategoryTheory.Monoidal.Normalize

open CategoryTheory Mathlib.Tactic BicategoryLike
open MonoidalCategory

/-- `normalize% η` is the normalization of the 2-morphism `η`.
1. The normalized 2-morphism is of the form `α₀ ≫ η₀ ≫ α₁ ≫ η₁ ≫ ... αₘ ≫ ηₘ ≫ αₘ₊₁` where
  each `αᵢ` is a structural 2-morphism (consisting of associators and unitors),
2. each `ηᵢ` is a non-structural 2-morphism of the form `f₁ ◁ ... ◁ fₘ ◁ θ`, and
3. `θ` is of the form `ι ▷ g₁ ▷ ... ▷ gₗ`
-/
elab "normalize% " t:term:51 : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  let ctx : Monoidal.Context ← mkContext e
  CoherenceM.run ctx do
    return (← BicategoryLike.eval `monoidal (← MkMor₂.ofExpr e)).expr.e.e

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z)

#guard_expr normalize% X ◁ 𝟙 Y = (whiskerLeftIso X (Iso.refl Y)).hom
#guard_expr normalize% 𝟙 X ▷ Y = (whiskerRightIso (Iso.refl X) Y).hom
#guard_expr normalize% X ◁ (f ≫ g) = _ ≫ X ◁ f ≫ _ ≫ X ◁ g ≫ _
#guard_expr normalize% (f ≫ g) ▷ Y = _ ≫ f ▷ Y ≫ _ ≫ g ▷ Y ≫ _
#guard_expr normalize% 𝟙_ C ◁ f = _ ≫ f ≫ _
#guard_expr normalize% (X ⊗ Y) ◁ f = _ ≫ X ◁ Y ◁ f ≫ _
#guard_expr normalize% f ▷ 𝟙_ C = _ ≫ f ≫ _
#guard_expr normalize% f ▷ (X ⊗ Y) = _ ≫ f ▷ X ▷ Y ≫ _
#guard_expr normalize% (X ◁ f) ▷ Y = _ ≫ X ◁ f ▷ Y ≫ _
#guard_expr normalize% (λ_ X).hom = (λ_ X).hom
#guard_expr normalize% (λ_ X).inv = ((λ_ X).symm).hom
#guard_expr normalize% (ρ_ X).hom = (ρ_ X).hom
#guard_expr normalize% (ρ_ X).inv = ((ρ_ X).symm).hom
#guard_expr normalize% (α_ X Y Z).hom = (α_ _ _ _).hom
#guard_expr normalize% (α_ X Y Z).inv = ((α_ X Y Z).symm).hom
#guard_expr normalize% 𝟙 (X ⊗ Y) = (Iso.refl (X ⊗ Y)).hom
#guard_expr normalize% f ⊗ g = _ ≫ (f ⊗ g) ≫ _
variable {V₁ V₂ V₃ : C} (R : ∀ V₁ V₂ : C, V₁ ⊗ V₂ ⟶ V₂ ⊗ V₁) in
#guard_expr normalize% R V₁ V₂ ▷ V₃ ⊗≫ V₂ ◁ R V₁ V₃ = _ ≫ R V₁ V₂ ▷ V₃ ≫ _ ≫ V₂ ◁ R V₁ V₃ ≫ _

example (f : U ⟶ V ⊗ (W ⊗ X)) (g : (V ⊗ W) ⊗ X ⟶ Y) :
    f ⊗≫ g = f ≫ 𝟙 _ ≫ (α_ _ _ _).inv ≫ g := by
  monoidal

example : (X ⊗ Y) ◁ f = (α_ _ _ _).hom ≫ X ◁ Y ◁ f ≫ (α_ _ _ _).inv := by
  monoidal

example : f ≫ g = f ≫ g := by
  monoidal

example : (f ⊗ g) ▷ X = (α_ _ _ _).hom ≫ (f ⊗ g ▷ X) ≫ (α_ _ _ _).inv := by
  monoidal

example {V₁ V₂ V₃ : C} (R : ∀ V₁ V₂ : C, V₁ ⊗ V₂ ⟶ V₂ ⊗ V₁) :
    R V₁ V₂ ▷ V₃ ⊗≫ V₂ ◁ R V₁ V₃ =
      R V₁ V₂ ▷ V₃ ≫ (α_ _ _ _).hom ⊗≫ 𝟙 _ ≫ V₂ ◁ R V₁ V₃ := by
  monoidal
