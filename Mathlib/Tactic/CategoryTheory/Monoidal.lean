/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.Tactic.CategoryTheory.Coherence

/-!
# Normalization of morphisms in monoidal categories

This file provides a tactic that normalizes morphisms in monoidal categories. This is used in the
string diagram widget given in `Mathlib.Tactic.StringDiagram`.

We say that the morphism `η` in a monoidal category is in normal form if
1. `η` is of the form `α₀ ≫ η₀ ≫ α₁ ≫ η₁ ≫ ... αₘ ≫ ηₘ ≫ αₘ₊₁` where each `αᵢ` is a
  structural 2-morphism (consisting of associators and unitors),
2. each `ηᵢ` is a non-structural 2-morphism of the form `f₁ ◁ ... ◁ fₘ ◁ θ`, and
3. `θ` is of the form `ι ▷ g₁ ▷ ... ▷ gₗ`

-/


open Lean Meta Elab
open CategoryTheory
open Mathlib.Tactic.Coherence

namespace Mathlib.Tactic.Monoidal

/-- Expressions for atomic 1-morphisms. -/
structure Atom₁ : Type where
  /-- Extract a Lean expression from an `Atom₁` expression. -/
  e : Expr

/-- Expressions for 1-morphisms. -/
inductive Mor₁ : Type
  /-- `id` is the expression for `𝟙_ C`. -/
  | id : Mor₁
  /-- `comp X Y` is the expression for `X ⊗ Y` -/
  | comp : Mor₁ → Mor₁ → Mor₁
  /-- Construct the expression for an atomic 1-morphism. -/
  | of : Atom₁ → Mor₁
  deriving Inhabited

/-- Converts a 1-morphism into a list of its components. -/
def Mor₁.toList : Mor₁ → List Atom₁
  | .id => []
  | .comp f g => f.toList ++ g.toList
  | .of f => [f]

/-- Returns `𝟙_ C` if the expression `e` is of the form `𝟙_ C`. -/
def isTensorUnit? (e : Expr) : MetaM (Option Expr) := do
  let C ← mkFreshExprMVar none
  let instC ← mkFreshExprMVar none
  let instMC ← mkFreshExprMVar none
  let unit := mkAppN (← mkConstWithFreshMVarLevels
    ``MonoidalCategoryStruct.tensorUnit) #[C, instC, instMC]
  if ← withDefault <| isDefEq e unit then
    return ← instantiateMVars unit
  else
    return none

/-- Returns `(f, g)` if the expression `e` is of the form `f ⊗ g`. -/
def isTensorObj? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let C ← mkFreshExprMVar none
  let f ← mkFreshExprMVar C
  let g ← mkFreshExprMVar C
  let instC ← mkFreshExprMVar none
  let instMC ← mkFreshExprMVar none
  let fg := mkAppN (← mkConstWithFreshMVarLevels
    ``MonoidalCategoryStruct.tensorObj) #[C, instC, instMC, f, g]
  if ← withDefault <| isDefEq e fg then
    return (← instantiateMVars f, ← instantiateMVars g)
  else
    return none

/-- Construct a `Mor₁` expression from a Lean expression. -/
partial def toMor₁ (e : Expr) : MetaM Mor₁ := do
  if let some _ ← isTensorUnit? e then
    return Mor₁.id
  else if let some (f, g) ← isTensorObj? e then
    return (← toMor₁ f).comp (← toMor₁ g)
  else
    return Mor₁.of ⟨e⟩

/-- Expressions for atomic structural 2-morphisms. -/
inductive StructuralAtom : Type
  /-- The expression for the associator `(α_ f g h).hom`. -/
  | associator (f g h : Mor₁) : StructuralAtom
  /-- The expression for the inverse of the associator `(α_ f g h).inv`. -/
  | associatorInv (f g h : Mor₁) : StructuralAtom
  /-- The expression for the left unitor `(λ_ f).hom`. -/
  | leftUnitor (f : Mor₁) : StructuralAtom
  /-- The expression for the inverse of the left unitor `(λ_ f).inv`. -/
  | leftUnitorInv (f : Mor₁) : StructuralAtom
  /-- The expression for the right unitor `(ρ_ f).hom`. -/
  | rightUnitor (f : Mor₁) : StructuralAtom
  /-- The expression for the inverse of the right unitor `(ρ_ f).inv`. -/
  | rightUnitorInv (f : Mor₁) : StructuralAtom
  deriving Inhabited

/-- Construct a `StructuralAtom` expression from a Lean expression. -/
def structuralAtom? (e : Expr) : MetaM (Option StructuralAtom) := do
  match e.getAppFnArgs with
  | (``Iso.hom, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) =>
      return some <| .associator (← toMor₁ f) (← toMor₁ g) (← toMor₁ h)
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) =>
      return some <| .leftUnitor (← toMor₁ f)
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) =>
      return some <| .rightUnitor (← toMor₁ f)
    | _ => return none
  | (``Iso.inv, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) =>
      return some <| .associatorInv (← toMor₁ f) (← toMor₁ g) (← toMor₁ h)
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) =>
      return some <| .leftUnitorInv (← toMor₁ f)
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) =>
      return some <| .rightUnitorInv (← toMor₁ f)
    | _ => return none
  | _ => return none

/-- Expressions for atomic non-structural 2-morphisms. -/
structure Atom where
  /-- Extract a Lean expression from an `Atom` expression. -/
  e : Expr
  deriving Inhabited

/-- Expressions of the form `η ▷ f₁ ▷ ... ▷ fₙ`. -/
inductive WhiskerRightExpr : Type
  /-- Construct the expression for an atomic 2-morphism. -/
  | of (η : Atom) : WhiskerRightExpr
  /-- Construct the expression for `η ▷ f`. -/
  | whisker (η : WhiskerRightExpr) (f : Atom₁) : WhiskerRightExpr
  deriving Inhabited

/-- Expressions of the form `η₁ ⊗ ... ⊗ ηₙ`. -/
inductive TensorHomExpr : Type
  | of (η : WhiskerRightExpr) : TensorHomExpr
  | cons (head : WhiskerRightExpr) (tail : TensorHomExpr) : TensorHomExpr
  deriving Inhabited

/-- Expressions of the form `f₁ ◁ ... ◁ fₙ ◁ η`. -/
inductive WhiskerLeftExpr : Type
  /-- Construct the expression for a right-whiskered 2-morphism. -/
  | of (η : TensorHomExpr) : WhiskerLeftExpr
  /-- Construct the expression for `f ◁ η`. -/
  | whisker (f : Atom₁) (η : WhiskerLeftExpr) : WhiskerLeftExpr
  deriving Inhabited

/-- Expressions for structural 2-morphisms. -/
inductive Structural : Type
  /-- Expressions for atomic structural 2-morphisms. -/
  | atom (η : StructuralAtom) : Structural
  /-- Expressions for the identity `𝟙 f`. -/
  | id (f : Mor₁) : Structural
  /-- Expressions for the composition `η ≫ θ`. -/
  | comp (α β : Structural) : Structural
  /-- Expressions for the left whiskering `f ◁ η`. -/
  | whiskerLeft (f : Mor₁) (η : Structural) : Structural
  /-- Expressions for the right whiskering `η ▷ f`. -/
  | whiskerRight (η : Structural) (f : Mor₁) : Structural
  /-- Expressions for the tensor `α ⊗ β`. -/
  | tensorHom (α β : Structural) : Structural
  /-- Expressions for `α` in the monoidal composition `η ⊗≫ θ := η ≫ α ≫ θ`. -/
  | monoidalCoherence (f g : Mor₁) (e : Expr) : Structural
  deriving Inhabited

/-- Normalized expressions for 2-morphisms. -/
inductive NormalExpr : Type
  /-- Construct the expression for a structural 2-morphism. -/
  | nil (α : Structural) : NormalExpr
  /-- Construct the normalized expression of 2-morphisms recursively. -/
  | cons (head_structural : Structural) (head : WhiskerLeftExpr) (tail : NormalExpr) : NormalExpr
  deriving Inhabited

/-- The domain of a morphism. -/
def src (η : Expr) : MetaM Mor₁ := do
  match (← whnfR <| ← inferType η).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) => toMor₁ f
  | _ => throwError "{η} is not a morphism"

/-- The codomain of a morphism. -/
def tar (η : Expr) : MetaM Mor₁ := do
  match (← whnfR <| ← inferType η).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, _, g]) => toMor₁ g
  | _ => throwError "{η} is not a morphism"

/-- The domain of a 2-morphism. -/
def Atom.src (η : Atom) : MetaM Mor₁ := do Monoidal.src η.e

/-- The codomain of a 2-morphism. -/
def Atom.tar (η : Atom) : MetaM Mor₁ := do Monoidal.tar η.e

/-- The domain of a 2-morphism. -/
def WhiskerRightExpr.src : WhiskerRightExpr → MetaM Mor₁
  | WhiskerRightExpr.of η => η.src
  | WhiskerRightExpr.whisker η f => return (← WhiskerRightExpr.src η).comp (Mor₁.of f)

/-- The codomain of a 2-morphism. -/
def WhiskerRightExpr.tar : WhiskerRightExpr → MetaM Mor₁
  | WhiskerRightExpr.of η => η.tar
  | WhiskerRightExpr.whisker η f => return (← WhiskerRightExpr.tar η).comp (Mor₁.of f)

/-- The domain of a 2-morphism. -/
def TensorHomExpr.src : TensorHomExpr → MetaM Mor₁
  | TensorHomExpr.of η => η.src
  | TensorHomExpr.cons η ηs => return (← η.src).comp (← ηs.src)

/-- The codomain of a 2-morphism. -/
def TensorHomExpr.tar : TensorHomExpr → MetaM Mor₁
  | TensorHomExpr.of η => η.tar
  | TensorHomExpr.cons η ηs => return (← η.tar).comp (← ηs.tar)

/-- The domain of a 2-morphism. -/
def WhiskerLeftExpr.src : WhiskerLeftExpr → MetaM Mor₁
  | WhiskerLeftExpr.of η => TensorHomExpr.src η
  | WhiskerLeftExpr.whisker f η => return (Mor₁.of f).comp (← WhiskerLeftExpr.src η)

/-- The codomain of a 2-morphism. -/
def WhiskerLeftExpr.tar : WhiskerLeftExpr → MetaM Mor₁
  | WhiskerLeftExpr.of η => TensorHomExpr.tar η
  | WhiskerLeftExpr.whisker f η => return (Mor₁.of f).comp (← WhiskerLeftExpr.tar η)

/-- The domain of a 2-morphism. -/
def StructuralAtom.src : StructuralAtom → Mor₁
  | .associator f g h => (f.comp g).comp h
  | .associatorInv f g h => f.comp (g.comp h)
  | .leftUnitor f => Mor₁.id.comp f
  | .leftUnitorInv f => f
  | .rightUnitor f => f.comp Mor₁.id
  | .rightUnitorInv f => f

/-- The codomain of a 2-morphism. -/
def StructuralAtom.tar : StructuralAtom → Mor₁
  | .associator f g h => f.comp (g.comp h)
  | .associatorInv f g h => (f.comp g).comp h
  | .leftUnitor f => f
  | .leftUnitorInv f => Mor₁.id.comp f
  | .rightUnitor f => f
  | .rightUnitorInv f => f.comp Mor₁.id

/-- The domain of a 2-morphism. -/
def Structural.src : Structural → Mor₁
  | .atom η => η.src
  | .id f => f
  | .comp α _ => α.src
  | .whiskerLeft f η => f.comp η.src
  | .whiskerRight η f => η.src.comp f
  | .tensorHom α β => α.src.comp β.src
  | .monoidalCoherence f _ _ => f

/-- The codomain of a 2-morphism. -/
def Structural.tar : Structural → Mor₁
  | .atom η => η.tar
  | .id f => f
  | .comp _ β => β.tar
  | .whiskerLeft f η => f.comp η.tar
  | .whiskerRight η f => η.tar.comp f
  | .tensorHom α β => α.tar.comp β.tar
  | .monoidalCoherence _ g _ => g

/-- The domain of a 2-morphism. -/
def NormalExpr.src : NormalExpr → Mor₁
  | NormalExpr.nil η => η.src
  | NormalExpr.cons α _ _ => α.src

/-- The codomain of a 2-morphism. -/
def NormalExpr.tar : NormalExpr → Mor₁
  | NormalExpr.nil η => η.tar
  | NormalExpr.cons _ _ ηs => ηs.tar

/-- The associator as a term of `normalExpr`. -/
def NormalExpr.associator (f g h : Mor₁) : NormalExpr :=
  .nil <| .atom <| .associator f g h

/-- The inverse of the associator as a term of `normalExpr`. -/
def NormalExpr.associatorInv (f g h : Mor₁) : NormalExpr :=
  .nil <| .atom <| .associatorInv f g h

/-- The left unitor as a term of `normalExpr`. -/
def NormalExpr.leftUnitor (f : Mor₁) : NormalExpr :=
  .nil <| .atom <| .leftUnitor f

/-- The inverse of the left unitor as a term of `normalExpr`. -/
def NormalExpr.leftUnitorInv (f : Mor₁) : NormalExpr :=
  .nil <| .atom <| .leftUnitorInv f

/-- The right unitor as a term of `normalExpr`. -/
def NormalExpr.rightUnitor (f : Mor₁) : NormalExpr :=
  .nil <| .atom <| .rightUnitor f

/-- The inverse of the right unitor as a term of `normalExpr`. -/
def NormalExpr.rightUnitorInv (f : Mor₁) : NormalExpr :=
  .nil <| .atom <| .rightUnitorInv f

-- /-- Return `η` for `η ▷ g₁ ▷ ... ▷ gₙ`. -/
-- def WhiskerRightExpr.atom : WhiskerRightExpr → Atom
--   | WhiskerRightExpr.of η => η
--   | WhiskerRightExpr.whisker η _ => η.atom

--   /-- Return `η` for `η ▷ g₁ ▷ ... ▷ gₙ`. -/
-- def TensorHomExpr.atom : TensorHomExpr → Atom
--   | TensorHomExpr.of η => η
--   | TensorHomExpr.cons η _ => η.atom

-- /-- Return `η` for `f₁ ◁ ... ◁ fₙ ◁ η ▷ g₁ ▷ ... ▷ gₙ`. -/
-- def WhiskerLeftExpr.atom : WhiskerLeftExpr → Atom
--   | WhiskerLeftExpr.of η => η.atom
--   | WhiskerLeftExpr.whisker _ η => η.atom

/-- Construct a `Structural` expression from a Lean expression for a structural 2-morphism. -/
partial def structural? (e : Expr) : MetaM Structural := do
  match (← whnfR e).getAppFnArgs with
  | (``CategoryStruct.comp, #[_, _, _, α, β]) =>
    return .comp (← structural? α) (← structural? β)
  | (``CategoryStruct.id, #[_, f]) => return .id (← toMor₁ f)
  | (``MonoidalCategoryStruct.whiskerLeft, #[f, η]) =>
    return .whiskerLeft (← toMor₁ f) (← structural? η)
  | (``MonoidalCategoryStruct.whiskerRight, #[η, f]) =>
    return .whiskerRight (← structural? η) (← toMor₁ f)
  | (``MonoidalCoherence.hom, #[_, _, f, g, inst]) =>
    return .monoidalCoherence (← toMor₁ f) (← toMor₁ g) inst
  | _ => match ← structuralAtom? e with
    | some η => return .atom η
    | none => throwError "not a structural 2-morphism"

/-- Construct a `NormalExpr` expression from a `WhiskerLeftExpr` expression. -/
def NormalExpr.of (η : WhiskerLeftExpr) : MetaM NormalExpr := do
  return .cons (.id (← η.src)) η (.nil (.id (← η.tar)))

/-- Construct a `NormalExpr` expression from a Lean expression for an atomic 2-morphism. -/
def NormalExpr.ofExpr (η : Expr) : MetaM NormalExpr :=
  NormalExpr.of <| .of <| .of <| .of ⟨η⟩

/-- If `e` is an expression of the form `η ⊗≫ θ := η ≫ α ≫ θ` in the monoidal category `C`,
return the expression for `α` .-/
def structuralOfMonoidalComp (C e : Expr) : MetaM Structural := do
  let W ← mkFreshExprMVar none
  let X ← mkFreshExprMVar none
  let Y ← mkFreshExprMVar none
  let Z ← mkFreshExprMVar none
  let f ← mkFreshExprMVar none
  let g ← mkFreshExprMVar none
  let α₀ ← mkFreshExprMVar none
  let instC ← mkFreshExprMVar none
  let αg := mkAppN (← mkConstWithFreshMVarLevels ``CategoryStruct.comp) #[C, instC, X, Y, Z, α₀, g]
  let fαg := mkAppN (← mkConstWithFreshMVarLevels
    ``CategoryStruct.comp) #[C, instC, W, X, Z, f, αg]
  _ ← isDefEq e fαg
  structural? α₀

/-- Construct a `NormalExpr` expression from another `NormalExpr` expression by adding a structural
2-morphism at the head. -/
def NormalExpr.ofNormalExpr (α : Structural) (e : NormalExpr) : MetaM NormalExpr :=
  match e with
  | .nil β => return .nil (α.comp β)
  | .cons β η ηs => return .cons (α.comp β) η ηs

mutual

/-- Evaluate the expression `η ≫ θ` into a normalized form. -/
partial def evalComp : NormalExpr → NormalExpr → MetaM NormalExpr
  | .nil α, .cons β η ηs => do
    return (.cons (α.comp β) η ηs)
  | .nil α, .nil α' => do
    return .nil (α.comp α')
  | .cons α η ηs, θ => do
    let ι ← evalComp ηs θ
    return .cons α η ι

/-- Evaluate the expression `f ◁ η` into a normalized form. -/
partial def evalWhiskerLeftExpr : Mor₁ → NormalExpr → MetaM NormalExpr
  | f, .nil α => return .nil (.whiskerLeft f α)
  | .of f, .cons α η ηs => do
    let η' := WhiskerLeftExpr.whisker f η
    let θ ← evalWhiskerLeftExpr (.of f) ηs
    return .cons (.whiskerLeft (.of f) α) η' θ
  | .comp f g, η => do
    let θ ← evalWhiskerLeftExpr g η
    let ι ← evalWhiskerLeftExpr f θ
    let h := η.src
    let h' := η.tar
    let ι' ← evalComp ι (NormalExpr.associatorInv f g h')
    let ι'' ← evalComp (NormalExpr.associator f g h) ι'
    return ι''
  | .id, η => do
    let f := η.src
    let g := η.tar
    let η' ← evalComp η (NormalExpr.leftUnitorInv g)
    let η'' ← evalComp (NormalExpr.leftUnitor f) η'
    return η''

/-- Evaluate the expression `η ▷ f` into a normalized form. -/
partial def evalWhiskerRightExprAux : TensorHomExpr → Atom₁ → MetaM NormalExpr
  | .of η, f => NormalExpr.of <| .of <| .of <| .whisker η f
  | .cons η ηs, f => do
    let ηs' ← evalWhiskerRightExprAux ηs f
    let η₁ ← evalTensorHomExpr (← NormalExpr.of <| .of <| .of η) ηs'
    let η₂ ← evalComp η₁ (.associatorInv (← η.tar) (← ηs.tar) (.of f))
    let η₃ ← evalComp (.associator (← η.src) (← ηs.src) (.of f)) η₂
    return η₃

/-- Evaluate the expression `η ▷ f` into a normalized form. -/
partial def evalWhiskerRightExpr : NormalExpr → Mor₁ → MetaM NormalExpr
  | .nil α, h => return .nil (.whiskerRight α h)
  | .cons α (.of η) ηs, .of f => do
    let ηs₁ ← evalWhiskerRightExpr ηs (.of f)
    let η₁ ← evalWhiskerRightExprAux η f
    let η₂ ← evalComp η₁ ηs₁
    let η₃ ← NormalExpr.ofNormalExpr (.whiskerRight α (.of f)) η₂
    return η₃
  | .cons α (.whisker f η) ηs, h => do
    let g ← η.src
    let g' ← η.tar
    let η₁ ← evalWhiskerRightExpr (← NormalExpr.of η) h
    let η₂ ← evalWhiskerLeftExpr (.of f) η₁
    let ηs₁ ← evalWhiskerRightExpr ηs h
    let ηs₂ ← evalComp (.associatorInv (.of f) g' h) ηs₁
    let η₃ ← evalComp η₂ ηs₂
    let η₄ ← evalComp (.associator (.of f) g h) η₃
    let η₅ ← NormalExpr.ofNormalExpr (.whiskerRight α h) η₄
    return η₅
  | η, .comp g h => do
    let η₁ ← evalWhiskerRightExpr η g
    let η₂ ← evalWhiskerRightExpr η₁ h
    let f := η.src
    let f' := η.tar
    let η₃ ← evalComp η₂ (.associator f' g h)
    let η₄ ← evalComp (.associatorInv f g h) η₃
    return η₄
  | η, .id => do
    let f := η.src
    let g := η.tar
    let η₁ ← evalComp η (.rightUnitorInv g)
    let η₂ ← evalComp (.rightUnitor f) η₁
    return η₂

/-- Evaluate the expression `η ⊗ θ` into a normalized form. -/
partial def evalTensorHomAux : TensorHomExpr → TensorHomExpr → MetaM NormalExpr
  | .of η, θ => NormalExpr.of <| .of <| .cons η θ
  | .cons η ηs, θ => do
    let α := NormalExpr.associator (← η.src) (← ηs.src) (← θ.src)
    let α' := NormalExpr.associatorInv (← η.tar) (← ηs.tar) (← θ.tar)
    let ηθ ← evalTensorHomAux ηs θ
    let η₁ ← evalTensorHomExpr (← NormalExpr.of <| .of <| .of η) ηθ
    let ηθ₁ ← evalComp η₁ α'
    let ηθ₂ ← evalComp α ηθ₁
    return ηθ₂

/-- Evaluate the expression `η ⊗ θ` into a normalized form. -/
partial def evalTensorHomAux' : WhiskerLeftExpr → WhiskerLeftExpr → MetaM NormalExpr
  | .of η, .of θ => evalTensorHomAux η θ
  | .whisker f η, θ => do
    let ηθ ← evalTensorHomAux' η θ
    let ηθ₁ ← evalWhiskerLeftExpr (.of f) ηθ
    let ηθ₂ ← evalComp ηθ₁ (.associatorInv (.of f) (← η.tar) (← θ.tar))
    let ηθ₃ ← evalComp (.associator (.of f) (← η.src) (← θ.src)) ηθ₂
    return ηθ₃
  | .of η, .whisker f θ => do
    let η₁ ← evalWhiskerRightExprAux η f
    let ηθ ← evalTensorHomExpr η₁ (← NormalExpr.of θ)
    let ηθ₁ ← evalComp ηθ (.associator (← η.tar) (.of f) (← θ.tar))
    let ηθ₂ ← evalComp (.associatorInv (← η.src) (.of f) (← θ.src)) ηθ₁
    return ηθ₂

/-- Evaluate the expression `η ⊗ θ` into a normalized form. -/
partial def evalTensorHomExpr : NormalExpr → NormalExpr → MetaM NormalExpr
  | .nil α, .nil β => do
    return .nil (α.tensorHom β)
  | .nil α, .cons β η ηs => do
    let η₁ ← evalWhiskerLeftExpr α.tar (← NormalExpr.of η)
    let ηs₁ ← evalWhiskerLeftExpr α.tar ηs
    let η₂ ← evalComp η₁ ηs₁
    let η₃ ← NormalExpr.ofNormalExpr (α.tensorHom β) η₂
    return η₃
  | .cons α η ηs, .nil β => do
    let η₁ ← evalWhiskerRightExpr (← NormalExpr.of η) β.tar
    let ηs₁ ← evalWhiskerRightExpr ηs β.tar
    let η₂ ← evalComp η₁ ηs₁
    let η₃ ← NormalExpr.ofNormalExpr (α.tensorHom β) η₂
    return η₃
  | .cons α η ηs, .cons β θ θs => do
    let ηθ ← evalTensorHomAux' η θ
    let ηθs ← evalTensorHomExpr ηs θs
    let ηθ₁ ← evalComp ηθ ηθs
    let ηθ₂ ← NormalExpr.ofNormalExpr (α.tensorHom β) ηθ₁
    return ηθ₂

end

/-- Evaluate the expression of a 2-morphism into a normalized form. -/
partial def eval (e : Expr) : MetaM NormalExpr := do
  if let .some e' ← structuralAtom? e then return .nil <| .atom e' else
    match e.getAppFnArgs with
    | (``CategoryStruct.id, #[_, _, f]) =>
      return .nil (.id (← toMor₁ f))
    | (``CategoryStruct.comp, #[_, _, _, _, _, η, θ]) =>
      let η_e ← eval η
      let θ_e ← eval θ
      let ηθ ← evalComp η_e θ_e
      return ηθ
    | (``MonoidalCategoryStruct.whiskerLeft, #[_, _, _, f, _, _, η]) =>
      evalWhiskerLeftExpr (← toMor₁ f) (← eval η)
    | (``MonoidalCategoryStruct.whiskerRight, #[_, _, _, _, _, η, h]) =>
      evalWhiskerRightExpr (← eval η) (← toMor₁ h)
    | (``monoidalComp, #[C, _, _, _, _, _, _, η, θ]) =>
      let η_e ← eval η
      let α₀ ← structuralOfMonoidalComp C e
      let α := NormalExpr.nil α₀
      let θ_e ← eval θ
      let αθ ← evalComp α θ_e
      let ηαθ ← evalComp η_e αθ
      return ηαθ
    | (``MonoidalCategoryStruct.tensorHom, #[_, _, _, _, _, _, _, η, θ]) =>
      evalTensorHomExpr (← eval η) (← eval θ)
    | _ => NormalExpr.ofExpr e

/-- Convert a `NormalExpr` expression into a list of `WhiskerLeftExpr` expressions. -/
def NormalExpr.toList : NormalExpr → List WhiskerLeftExpr
  | NormalExpr.nil _ => []
  | NormalExpr.cons _ η ηs => η :: NormalExpr.toList ηs

/- ## Test for `eval`. -/

/-- The context for evaluating expressions. -/
structure Context where
  /-- The expression for the underlying category. -/
  C : Expr

/-- Populate a `context` object for evaluating `e`. -/
def mkContext (e : Expr) : MetaM (Context) := do
  match (← whnfR <| ← inferType e).getAppFnArgs with
  | (``Quiver.Hom, #[C, _, _, _]) =>
    return { C := C }
  | _ => throwError "not a morphism"

/-- The monad for the normalization of 2-morphisms. -/
abbrev MonoidalM := ReaderT Context MetaM

/-- Run a computation in the `M` monad. -/
abbrev MonoidalM.run {α : Type} (c : Context) (m : MonoidalM α) : MetaM α :=
  ReaderT.run m c

/-- Extract a Lean expression from a `Mor₁` expression. -/
def Mor₁.e : Mor₁ → MonoidalM Expr
  | .id => do
    let ctx ← read
    mkAppOptM ``MonoidalCategoryStruct.tensorUnit #[ctx.C, none, none]
  | .comp f g => do
    mkAppM ``MonoidalCategoryStruct.tensorObj #[← Mor₁.e f, ← Mor₁.e g]
  | .of f => return f.e

/-- Extract a Lean expression from a `StructuralAtom` expression. -/
def StructuralAtom.e : StructuralAtom → MonoidalM Expr
  | .associator f g h => do
    mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategoryStruct.associator #[← f.e, ← g.e, ← h.e]]
  | .associatorInv f g h => do
    mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategoryStruct.associator #[← f.e, ← g.e, ← h.e]]
  | .leftUnitor f => do
    mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategoryStruct.leftUnitor #[← f.e]]
  | .leftUnitorInv f => do
    mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategoryStruct.leftUnitor #[← f.e]]
  | .rightUnitor f => do
    mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategoryStruct.rightUnitor #[← f.e]]
  | .rightUnitorInv f => do
    mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategoryStruct.rightUnitor #[← f.e]]

/-- Extract a Lean expression from a `Structural` expression. -/
partial def Structural.e : Structural → MonoidalM Expr
  | .atom η => η.e
  | .id f => do mkAppM ``CategoryStruct.id #[← f.e]
  | .comp α β => do match α, β with
    | _, _ => mkAppM ``CategoryStruct.comp #[← α.e, ← β.e]
  | .whiskerLeft f η => do mkAppM ``MonoidalCategoryStruct.whiskerLeft #[← f.e, ← η.e]
  | .whiskerRight η f => do mkAppM ``MonoidalCategoryStruct.whiskerRight #[← η.e, ← f.e]
  | .tensorHom α β => do mkAppM ``MonoidalCategoryStruct.tensorHom #[← α.e, ← β.e]
  | .monoidalCoherence _ _ e => do
    mkAppOptM ``MonoidalCoherence.hom #[none, none, none, none, e]

/-- Extract a Lean expression from a `WhiskerRightExpr` expression. -/
def WhiskerRightExpr.e : WhiskerRightExpr → MonoidalM Expr
  | WhiskerRightExpr.of η => return η.e
  | WhiskerRightExpr.whisker η f => do
    mkAppM ``MonoidalCategoryStruct.whiskerRight #[← η.e, f.e]

/-- Extract a Lean expression from a `TensorHomExpr` expression. -/
def TensorHomExpr.e : TensorHomExpr → MonoidalM Expr
  | TensorHomExpr.of η => η.e
  | TensorHomExpr.cons η ηs => do
    mkAppM ``MonoidalCategoryStruct.tensorHom #[← η.e, ← ηs.e]

/-- Extract a Lean expression from a `WhiskerLeftExpr` expression. -/
def WhiskerLeftExpr.e : WhiskerLeftExpr → MonoidalM Expr
  | WhiskerLeftExpr.of η => η.e
  | WhiskerLeftExpr.whisker f η => do
    mkAppM ``MonoidalCategoryStruct.whiskerLeft #[f.e, ← η.e]

/-- Extract a Lean expression from a `NormalExpr` expression. -/
def NormalExpr.e : NormalExpr → MonoidalM Expr
  | NormalExpr.nil α => α.e
  | NormalExpr.cons α η θ => do
    mkAppM ``CategoryStruct.comp #[← α.e, ← mkAppM ``CategoryStruct.comp #[← η.e, ← θ.e]]

/-- `normalize% η` is the normalization of the 2-morphism `η`. It is of the form
`α₀ ≫ η₀ ≫ α₁ ≫ η₁ ≫ ... αₙ ≫ ηₙ ≫ αₙ₊₁`, where `αᵢ` are structural 2-morphisms
and `ηᵢ` are non-structural 2-morphisms. -/
elab "normalize% " t:term:51 : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  MonoidalM.run (← mkContext e) do (← eval e).e

end Mathlib.Tactic.Monoidal
