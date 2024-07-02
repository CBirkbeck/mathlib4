import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

universe w v v' v'' u u' u''

namespace CategoryTheory

open Limits Opposite AlgebraicTopology

variable {C : Type u} [Category.{v} C] (J : Type u') [Category.{v'} J]
  (A : Type u'') [Category.{v''} A]

variable [∀ (I : Type w), HasProductsOfShape I A]

variable (C) in
structure FormalCoproduct where
  I : Type w
  obj (i : I) : C

namespace FormalCoproduct

@[ext] structure Hom (X Y : FormalCoproduct.{w} C) where
  f : X.I → Y.I
  φ (i : X.I) : X.obj i ⟶ Y.obj (f i)

-- this category identifies to the fullsubcategory of the category of
-- presheaves of sets on `C` which are coproducts of representable presheaves
@[simps!] instance category : Category (FormalCoproduct.{w} C) where
  Hom := Hom
  id X := { f := id, φ := fun _ ↦ 𝟙 _ }
  comp α β := { f := β.f ∘ α.f, φ := fun _ ↦ α.φ _ ≫ β.φ _ }

@[simps] noncomputable def eval (X : FormalCoproduct.{w} C) : (Cᵒᵖ ⥤ A) ⥤ A where
  obj F := ∏ᶜ (fun (i : X.I) ↦ F.obj (op (X.obj i)))
  map α := Pi.map (fun _ ↦ α.app _)

variable (C)

@[simps] noncomputable def evalFunctor : (FormalCoproduct.{w} C)ᵒᵖ ⥤ (Cᵒᵖ ⥤ A) ⥤ A where
  obj X := X.unop.eval A
  map {X Y} π :=
    { app := fun F ↦ Pi.map' π.unop.f (fun i ↦ F.map (π.unop.φ i).op) }

noncomputable def evalFunctor' : (Jᵒᵖ ⥤ FormalCoproduct.{w} C)ᵒᵖ ⥤ (Cᵒᵖ ⥤ A) ⥤ (J ⥤ A) :=
  ((whiskeringRight Jᵒᵖ _ _).obj ((evalFunctor C A).rightOp)).op ⋙ (by
    let φ : (Jᵒᵖ ⥤ ((Cᵒᵖ ⥤ A) ⥤ A)ᵒᵖ)ᵒᵖ ⥤ (J ⥤ ((Cᵒᵖ ⥤ A) ⥤ A)) := sorry
    let ψ : (J ⥤ (Cᵒᵖ ⥤ A) ⥤ A) ⥤ (Cᵒᵖ ⥤ A) ⥤ J ⥤ A := sorry -- Functor.flip as a functor...
    exact φ ⋙ ψ)

noncomputable abbrev simplicialEvalFunctor : (SimplicialObject (FormalCoproduct.{w} C))ᵒᵖ ⥤
    (Cᵒᵖ ⥤ A) ⥤ CosimplicialObject A :=
  evalFunctor' C SimplexCategory A

noncomputable abbrev cochainComplexFunctor [Preadditive A] :
    (SimplicialObject (FormalCoproduct.{w} C))ᵒᵖ ⥤
      (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  simplicialEvalFunctor C A ⋙ ((whiskeringRight _ _ _).obj (alternatingCofaceMapComplex A))

variable {C} in
def cechSimplicial {I : Type w} (U : I → C) [HasFiniteProducts C] :
    SimplicialObject (FormalCoproduct C) := by
  -- variant of `cechNerve` where in degree `n` we take the formal coproduct
  -- over maps `a : {0,...,n} → I` of the finite product of the `U (a i)`.
  sorry

end FormalCoproduct

noncomputable def cechComplexFunctor {I : Type w} (U : I → C)
    [HasFiniteProducts C] [Preadditive A] :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  (FormalCoproduct.cochainComplexFunctor.{w} C A).obj (op (FormalCoproduct.cechSimplicial U))

-- apply this to a family of objects `U : I → C` which satisfies `J.CoversTop U` for
-- a Grothendieck topology, or if `X : C` and we have a covering family of arrows
--  `f i : U i ⟶ X` identified as a family of objects in `Over X`.

-- next step: show that if `V` refines `U`, then the induced maps are homotopic

end CategoryTheory
