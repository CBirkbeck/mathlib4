/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import ProofWidgets.Component.PenroseDiagram
import ProofWidgets.Presentation.Expr
import Mathlib.Tactic.CategoryTheory.Coherence

/-!
# String Diagrams

This file provides tactic/meta infrastructure for displaying string diagrams for morphisms
in monoidal categories in the infoview.

-/

namespace Mathlib.Tactic.Widget.StringDiagram

open Lean Meta Elab
open CategoryTheory
open Mathlib.Tactic.Coherence

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

/-- Converts a 1-morphism into a list of its underlying expressions. -/
def Mor₁.toList : Mor₁ → List Atom₁
  | .id => []
  | .comp f g => f.toList ++ g.toList
  | .of f => [f]

/-- Returns `𝟙_ C` if the expression `e` is of the form `𝟙_ C`. -/
def isTensorUnit? (e : Expr) : MetaM (Option Expr) := do
  let v ← mkFreshLevelMVar
  let u ← mkFreshLevelMVar
  let C ← mkFreshExprMVar none
  let instC ← mkFreshExprMVar none
  let instMC ← mkFreshExprMVar none
  let unit := mkAppN (.const ``MonoidalCategoryStruct.tensorUnit [v, u]) #[C, instC, instMC]
  if ← isDefEq e unit then
    return ← instantiateMVars unit
  else
    return none

/-- Returns `(f, g)` if the expression `e` is of the form `f ⊗ g`. -/
def isTensorObj? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let v ← mkFreshLevelMVar
  let u ← mkFreshLevelMVar
  let C ← mkFreshExprMVar none
  let f ← mkFreshExprMVar C
  let g ← mkFreshExprMVar C
  let instC ← mkFreshExprMVar none
  let instMC ← mkFreshExprMVar none
  let fg := mkAppN (.const ``MonoidalCategoryStruct.tensorObj [v, u]) #[C, instC, instMC, f, g]
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
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) => return some <| .leftUnitor (← toMor₁ f)
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) => return some <| .rightUnitor (← toMor₁ f)
    | _ => return none
  | (``Iso.inv, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) =>
      return some <| .associatorInv (← toMor₁ f) (← toMor₁ g) (← toMor₁ h)
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) => return some <| .leftUnitorInv (← toMor₁ f)
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) => return some <| .rightUnitorInv (← toMor₁ f)
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
  | atom (α : StructuralAtom) : Structural
  /-- Expressions for the identity `𝟙 f`. -/
  | id (f : Mor₁) : Structural
  /-- Expressions for the composition `α ≫ β`. -/
  | comp (α β : Structural) : Structural
  /-- Expressions for the left whiskering `f ◁ α`. -/
  | whiskerLeft (f : Mor₁) (α : Structural) : Structural
  /-- Expressions for the right whiskering `α ▷ f`. -/
  | whiskerRight (α : Structural) (f : Mor₁) : Structural
  /-- Expressions for the tensor `α ⊗ β`. -/
  | tensorHom (α β : Structural) : Structural
  /-- Expressions for `α : f ⟶ g` in the monoidal composition `η ⊗≫ θ := η ≫ α ≫ θ` where
  `e` is the expression for an instance of `MonoidalCoherence f g`. -/
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
  match (← inferType η).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) => toMor₁ f
  | _ => throwError "{η} is not a morphism"

/-- The codomain of a morphism. -/
def tar (η : Expr) : MetaM Mor₁ := do
  match (← inferType η).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, _, g]) => toMor₁ g
  | _ => throwError "{η} is not a morphism"

/-- The domain of a 2-morphism. -/
def Atom.src (η : Atom) : MetaM Mor₁ := do StringDiagram.src η.e

/-- The codomain of a 2-morphism. -/
def Atom.tar (η : Atom) : MetaM Mor₁ := do StringDiagram.tar η.e

/-- The domain of a 2-morphism. -/
def WhiskerRightExpr.src : WhiskerRightExpr → MetaM Mor₁
  | WhiskerRightExpr.of η => η.src
  | WhiskerRightExpr.whisker η f => return (← η.src).comp (Mor₁.of f)

/-- The codomain of a 2-morphism. -/
def WhiskerRightExpr.tar : WhiskerRightExpr → MetaM Mor₁
  | WhiskerRightExpr.of η => η.tar
  | WhiskerRightExpr.whisker η f => return (← η.tar).comp (Mor₁.of f)

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
  | WhiskerLeftExpr.of η => η.src
  | WhiskerLeftExpr.whisker f η => return (Mor₁.of f).comp (← η.src)

/-- The codomain of a 2-morphism. -/
def WhiskerLeftExpr.tar : WhiskerLeftExpr → MetaM Mor₁
  | WhiskerLeftExpr.of η => η.tar
  | WhiskerLeftExpr.whisker f η => return (Mor₁.of f).comp (← η.tar)

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
  | .atom α => α.src
  | .id f => f
  | .comp α _ => α.src
  | .whiskerLeft f α => f.comp α.src
  | .whiskerRight α f => α.src.comp f
  | .tensorHom α β => α.src.comp β.src
  | .monoidalCoherence f _ _ => f

/-- The codomain of a 2-morphism. -/
def Structural.tar : Structural → Mor₁
  | .atom α => α.tar
  | .id f => f
  | .comp _ β => β.tar
  | .whiskerLeft f α => f.comp α.tar
  | .whiskerRight α f => α.tar.comp f
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
  | (``Mathlib.Tactic.Coherence.MonoidalCoherence.hom, #[_, _, f, g, _, _, inst]) =>
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
  let v ← mkFreshLevelMVar
  let u ← mkFreshLevelMVar
  _ ← isDefEq (.sort (.succ v)) (← inferType (← inferType e))
  _ ← isDefEq (.sort (.succ u)) (← inferType C)
  let W ← mkFreshExprMVar none
  let X ← mkFreshExprMVar none
  let Y ← mkFreshExprMVar none
  let Z ← mkFreshExprMVar none
  let f ← mkFreshExprMVar none
  let g ← mkFreshExprMVar none
  let α₀ ← mkFreshExprMVar none
  let instC ← mkFreshExprMVar none
  let αg := mkAppN (.const ``CategoryStruct.comp [v, u]) #[C, instC, X, Y, Z, α₀, g]
  let fαg := mkAppN (.const ``CategoryStruct.comp [v, u]) #[C, instC, W, X, Z, f, αg]
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
partial def tensorHomWhiskerRight : TensorHomExpr → Atom₁ → MetaM NormalExpr
  | .of η, f => NormalExpr.of <| .of <| .of <| .whisker η f
  | .cons η ηs, f => do
    let ηs' ← tensorHomWhiskerRight ηs f
    let η₁ ← evalTensorHomExpr (← NormalExpr.of <| .of <| .of η) ηs'
    let η₂ ← evalComp η₁ (.associatorInv (← η.tar) (← ηs.tar) (.of f))
    let η₃ ← evalComp (.associator (← η.src) (← ηs.src) (.of f)) η₂
    return η₃

/-- Evaluate the expression `η ▷ f` into a normalized form. -/
partial def evalWhiskerRightExpr : NormalExpr → Mor₁ → MetaM NormalExpr
  | .nil α, h => return .nil (.whiskerRight α h)
  | .cons α (.of η) ηs, .of f => do
    let ηs₁ ← evalWhiskerRightExpr ηs (.of f)
    let η₁ ← tensorHomWhiskerRight η f
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
partial def tensorHomTensor : TensorHomExpr → TensorHomExpr → MetaM NormalExpr
  | .of η, θ => NormalExpr.of <| .of <| .cons η θ
  | .cons η ηs, θ => do
    let α := NormalExpr.associator (← η.src) (← ηs.src) (← θ.src)
    let α' := NormalExpr.associatorInv (← η.tar) (← ηs.tar) (← θ.tar)
    let ηθ ← tensorHomTensor ηs θ
    let η₁ ← evalTensorHomExpr (← NormalExpr.of <| .of <| .of η) ηθ
    let ηθ₁ ← evalComp η₁ α'
    let ηθ₂ ← evalComp α ηθ₁
    return ηθ₂

/-- Evaluate the expression `η ⊗ θ` into a normalized form. -/
partial def evalTensorHomAux : WhiskerLeftExpr → WhiskerLeftExpr → MetaM NormalExpr
  | .of η, .of θ => tensorHomTensor η θ
  | .whisker f η, θ => do
    let ηθ ← evalTensorHomAux η θ
    let ηθ₁ ← evalWhiskerLeftExpr (.of f) ηθ
    let ηθ₂ ← evalComp ηθ₁ (.associatorInv (.of f) (← η.tar) (← θ.tar))
    let ηθ₃ ← evalComp (.associator (.of f) (← η.src) (← θ.src)) ηθ₂
    return ηθ₃
  | .of η, .whisker f θ => do
    let η₁ ← tensorHomWhiskerRight η f
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
    let ηθ ← evalTensorHomAux η θ
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
    | (``monoidalComp, #[C, _, _, _, _, _, _, _, _, η, θ]) =>
      let η_e ← eval η
      let α₀' ← structuralOfMonoidalComp C e
      let α := NormalExpr.nil α₀'
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

structure AtomNode : Type where
  vPos : ℕ
  hPosSrc : ℕ
  hPosTar : ℕ
  atom : Atom

structure IdNode : Type where
  vPos : ℕ
  hPosSrc : ℕ
  hPosTar : ℕ
  id : Atom₁

inductive Node : Type
  | atom : AtomNode → Node
  | id : IdNode → Node

def Node.e : Node → Expr
  | Node.atom n => n.atom.e
  | Node.id n => n.id.e

def Node.srcLength : Node → MetaM ℕ
  | Node.atom n => do return (← n.atom.src).toList.length
  | Node.id _ => return 1

def Node.tarLength : Node → MetaM ℕ
  | Node.atom n => do return (← n.atom.tar).toList.length
  | Node.id _ => return 1

def Node.vPos : Node → ℕ
  | Node.atom n => n.vPos
  | Node.id n => n.vPos

def Node.hPosSrc : Node → ℕ
  | Node.atom n => n.hPosSrc
  | Node.id n => n.hPosSrc

def Node.hPosTar : Node → ℕ
  | Node.atom n => n.hPosTar
  | Node.id n => n.hPosTar

def Node.lengthSumSrc : List Node → MetaM ℕ
  | [] => return 0
  | n :: ns => do
    let l ← n.srcLength
    let ls ← Node.lengthSumSrc ns
    return l + ls

def Node.lengthSumTar : List Node → MetaM ℕ
  | [] => return 0
  | n :: ns => do
    let l ← n.tarLength
    let ls ← Node.lengthSumTar ns
    return l + ls

def WhiskerRightExpr.nodes (v h₁ h₂ : ℕ) : WhiskerRightExpr → MetaM (List Node)
  | WhiskerRightExpr.of η => do
    return [.atom ⟨v, h₁, h₂, η⟩]
  | WhiskerRightExpr.whisker η f => do
    let ηs ← η.nodes v h₁ h₂
    let k₁ ← Node.lengthSumSrc ηs
    let k₂ ← Node.lengthSumTar ηs
    let s : Node := .id ⟨v, h₁ + k₁, h₂ + k₂, f⟩
    return ηs ++ [s]

def TensorHomExpr.nodes (v h₁ h₂ : ℕ) : TensorHomExpr → MetaM (List Node)
  | TensorHomExpr.of η => η.nodes v h₁ h₂
  | TensorHomExpr.cons η ηs => do
    let s₁ ← η.nodes v h₁ h₂
    let k₁ ← Node.lengthSumSrc s₁
    let k₂ ← Node.lengthSumTar s₁
    let s₂ ← ηs.nodes v (h₁ + k₁) (h₂ + k₂)
    return s₁ ++ s₂

def WhiskerLeftExpr.nodes (v h₁ h₂ : ℕ) : WhiskerLeftExpr → MetaM (List Node)
  | WhiskerLeftExpr.of η => η.nodes v h₁ h₂
  | WhiskerLeftExpr.whisker f η => do
    let s : Node := .id ⟨v, h₁, h₂, f⟩
    let ss ← η.nodes v (h₁ + 1) (h₂ + 1)
    return s :: ss

def topNodes (η : WhiskerLeftExpr) : MetaM (List Node) := do
  return (← η.src).toList.enum.map (fun (i, f) => .id ⟨0, i, i, f⟩)

def NormalExpr.nodesAux (v : ℕ) : NormalExpr → MetaM (List (List Node))
  | NormalExpr.nil α => return [(α.src).toList.enum.map (fun (i, f) => .id ⟨v, i, i, f⟩)]
  | NormalExpr.cons _ η ηs => do
    let s₁ ← η.nodes v 0 0
    let s₂ ← ηs.nodesAux (v + 1)
    return s₁ :: s₂

def NormalExpr.nodes (e : NormalExpr) : MetaM (List (List Node)) := do
  let l := e.toList
  match l.head? with
  | some x₁ => return (← topNodes x₁) :: (← e.nodesAux 1)
  | _ => return []

/-- `pairs [a, b, c, d]` is `[(a, b), (b, c), (c, d)]`. -/
def pairs {α : Type} : List α → List (α × α)
  | [] => []
  | [_] => []
  | (x :: y :: ys) => (x, y) :: pairs (y :: ys)

/-- A type for Penrose variables. -/
structure PenroseVar : Type where
  /-- The identifier of the variable. -/
  ident : String
  /-- The indices of the variable. -/
  indices : List ℕ
  /-- The underlying expression of the variable. -/
  e : Expr
  deriving Inhabited

instance : BEq PenroseVar := ⟨fun x y => x.ident == y.ident && x.indices == y.indices⟩

instance : Hashable PenroseVar := ⟨fun v ↦ hash (v.ident, v.indices)⟩

instance : ToString PenroseVar :=
  ⟨fun v => v.ident ++ v.indices.foldl (fun s x => s ++ s!"_{x}") ""⟩

/-- Expressions to display as labels in a diagram. -/
abbrev ExprEmbeds := Array (String × Expr)

/-! ## Widget for general string diagrams -/

open ProofWidgets

/-- The state of a diagram builder. -/
structure DiagramState where
  /-- The Penrose substance program.
  Note that `embeds` are added lazily at the end. -/
  sub : String := ""
  /-- Components to display as labels in the diagram,
  mapped as name ↦ (type, html). -/
  embeds : HashMap String (String × Html) := .empty
  /-- The start point of a string. -/
  startPoint : HashMap PenroseVar PenroseVar := .empty
  /-- The end point of a string. -/
  endPoint : HashMap PenroseVar PenroseVar := .empty

/-- The monad for building a string diagram. -/
abbrev DiagramBuilderM := StateT DiagramState MetaM

open scoped Jsx in
/-- Build a string diagram from state. -/
def buildDiagram : DiagramBuilderM (Option Html) := do
  let st ← get
  if st.sub == "" && st.embeds.isEmpty then
    return none
  let mut sub := "AutoLabel All\n"
  let mut embedHtmls := #[]
  for (n, (tp, h)) in st.embeds.toArray do
    sub := sub ++ s!"{tp} {n}\n"
    embedHtmls := embedHtmls.push (n, h)
  sub := sub ++ st.sub
  return <PenroseDiagram
    embeds={embedHtmls}
    dsl={include_str ".."/".."/".."/"widget"/"src"/"penrose"/"monoidal.dsl"}
    sty={include_str ".."/".."/".."/"widget"/"src"/"penrose"/"monoidal.sty"}
    sub={sub} />

/-- Add a substance `nm` of Penrose type `tp`,
labelled by `h` to the substance program. -/
def addEmbed (nm : String) (tp : String) (h : Html) : DiagramBuilderM Unit := do
  modify fun st => { st with embeds := st.embeds.insert nm (tp, h )}

open scoped Jsx in
/-- Add the variable `v` with the type `tp` to the substance program. -/
def addPenroseVar (tp : String) (v : PenroseVar) : DiagramBuilderM Unit := do
  let h := <InteractiveCode fmt={← Widget.ppExprTagged v.e} />
  addEmbed (toString v) tp h

/-- Add instruction `i` to the substance program. -/
def addInstruction (i : String) : DiagramBuilderM Unit := do
  modify fun st => { st with sub := st.sub ++ s!"{i}\n" }

/-- Add constructor `tp v := nm (vs)` to the substance program. -/
def addConstructor (tp : String) (v : PenroseVar) (nm : String) (vs : List PenroseVar) :
    DiagramBuilderM Unit := do
  let vs' := ", ".intercalate (vs.map (fun v => toString v))
  addInstruction s!"{tp} {v} := {nm} ({vs'})"

/-- Run the program in the diagram builder monad. -/
def DiagramBuilderM.run {α : Type} (x : DiagramBuilderM α) : MetaM α :=
  x.run' {}

open scoped Jsx in
/-- Construct a string diagram from a Penrose `sub`stance program and expressions `embeds` to
display as labels in the diagram. -/
def mkStringDiag (e : Expr) : MetaM Html := do
  DiagramBuilderM.run do
    let nodes ← (← eval e).nodes
    /- Check that the numbers of the start and end points of strings are the same. -/
    for (l₁, l₂) in pairs nodes do
      if (← Node.lengthSumTar l₁) ≠ (← Node.lengthSumSrc l₂) then
        throwError "The number of the start and end points of a string does not match."
    for x in nodes.join do
      match x with
      | .atom x => do
        let v : PenroseVar := ⟨"E", [x.vPos, x.hPosSrc, x.hPosTar], x.atom.e⟩
        addPenroseVar "Atom" v
        for (k, y) in (← x.atom.src).toList.enum do
          let v_mor : PenroseVar := ⟨"f", [x.vPos, x.hPosSrc + k], y.e⟩
          modify fun st => { st with endPoint := st.endPoint.insert v_mor v }
        for (k, y) in (← x.atom.tar).toList.enum do
          let v_mor : PenroseVar := ⟨"f", [x.vPos + 1, x.hPosTar + k], y.e⟩
          modify fun st => { st with startPoint := st.startPoint.insert v_mor v }
      | .id x => do
        let v : PenroseVar := ⟨"E", [x.vPos, x.hPosSrc, x.hPosTar], x.id.e⟩
        addPenroseVar "Id" v
        let v_mor : PenroseVar := ⟨"f", [x.vPos, x.hPosSrc], x.id.e⟩
        let v_mor' : PenroseVar := ⟨"f", [x.vPos + 1, x.hPosTar], x.id.e⟩
        modify fun st => { st with
          endPoint := st.endPoint.insert v_mor v
          startPoint := st.startPoint.insert v_mor' v }
    for l in nodes do
      for (x, y) in pairs l do
        let v₁ : PenroseVar := ⟨"E", [x.vPos, x.hPosSrc, x.hPosTar], x.e⟩
        let v₂ : PenroseVar := ⟨"E", [y.vPos, y.hPosSrc, y.hPosTar], y.e⟩
        addInstruction s!"Left({v₁}, {v₂})"
    for (l₁, l₂) in pairs nodes do
      if let .some x := l₁.head? then
        if let .some y := l₂.head? then
          let v₁ : PenroseVar := ⟨"E", [x.vPos, x.hPosSrc, x.hPosTar], x.e⟩
          let v₂ : PenroseVar := ⟨"E", [y.vPos, y.hPosSrc, y.hPosTar], y.e⟩
          addInstruction s!"Above({v₁}, {v₂})"
    for l in nodes do
      for x in l do
        let s ← show MetaM (List Atom₁) from match x with
        | .atom x => do return (← x.atom.src).toList
        | .id x => return [x.id]
        for (k, f) in s.enum do
          let v : PenroseVar := ⟨"f", [x.vPos, x.hPosSrc + k], f.e⟩
          let st ← get
          if let .some vStart := st.startPoint.find? v then
            if let .some vEnd := st.endPoint.find? v then
              addConstructor "Mor1" v "MakeString" [vStart, vEnd]
    match ← buildDiagram with
    | some html => return html
    | none => return <span>No 2-morphisms.</span>

/-- Given a 2-morphism, return a string diagram. Otherwise `none`. -/
def stringM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  return some <| ← mkStringDiag e

/-- Given an equality between 2-morphisms, return a string diagram of the LHS. Otherwise `none`. -/
def stringLeftM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  let some (_, lhs, _) := e.eq? | return none
  return some <| ← mkStringDiag lhs

/-- Given an equality between 2-morphisms, return a string diagram of the RHS. Otherwise `none`. -/
def stringRightM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  let some (_, _, rhs) := e.eq? | return none
  return some <| ← mkStringDiag rhs

/-- The string diagram widget. -/
@[expr_presenter]
def stringPresenter : ExprPresenter where
  userName := "String diagram"
  layoutKind := .block
  present type := do
    if let some d ← stringM? type then
      return d
    throwError "Couldn't find a string diagram."

/-- The string diagram widget. -/
@[expr_presenter]
def stringPresenterLeft : ExprPresenter where
  userName := "String diagram of LHS"
  layoutKind := .block
  present type := do
    if let some d ← stringLeftM? type then
      return d
    throwError "Couldn't find a string diagram."

/-- The string diagram widget. -/
@[expr_presenter]
def stringPresenterRight : ExprPresenter where
  userName := "String diagram of RHS"
  layoutKind := .block
  present type := do
    if let some d ← stringRightM? type then
      return d
    throwError "Couldn't find a string diagram."

end Mathlib.Tactic.Widget.StringDiagram
