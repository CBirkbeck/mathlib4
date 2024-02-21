/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Anand Rao
-/
import Lean
import ProofWidgets
import Mathlib.Lean.Meta.RefinedDiscrTree.RefinedDiscrTree
import Aesop.Util.Basic

namespace Mathlib.Tactic.LibraryRewrite

open Lean Meta Server

/-- The structure that is stored in the `RefinedDiscrTree`. -/
structure RewriteLemma where
  name : Name
  symm : Bool
  numParams : Nat
deriving BEq, Inhabited

/-- Return the string length of the lemma name. -/
def RewriteLemma.length (rwLemma : RewriteLemma) : Nat :=
  rwLemma.name.toString.length

/--
We sort lemmata by the following conditions (in order):
- number of parameters
- left-to-right rewrites come first
- length of the name
- alphabetical order
-/
def RewriteLemma.lt (a b : RewriteLemma) : Bool :=
  a.numParams < b.numParams || a.numParams == b.numParams &&
    (!a.symm && b.symm || a.symm == b.symm &&
      (a.length < b.length || a.length == b.length &&
        Name.lt a.name b.name))

instance : LT RewriteLemma := ⟨fun a b => RewriteLemma.lt a b⟩
instance (a b : RewriteLemma) : Decidable (a < b) :=
  inferInstanceAs (Decidable (RewriteLemma.lt a b))

/-- Similar to `Name.isBlackListed`. -/
def isBadDecl (name : Name) (cinfo : ConstantInfo) (env : Environment) : Bool :=
  (match cinfo with
    | .axiomInfo v => v.isUnsafe
    | .thmInfo .. => false
    | _ => true)
  || (match name with
    | .str _ "inj"
    | .str _ "injEq"
    | .str _ "sizeOf_spec"
    | .str _ "noConfusionType" => true
    | _ => false)
  || name.isInternalDetail
  || (`Mathlib).isPrefixOf name
  || isAuxRecursor env name
  || isNoConfusion env name
  || isMatcherCore env name

/-- Extract the left and right hand sides of an equality or iff statement. -/
def matchEqn? (e : Expr) : Option (Expr × Expr) :=
  match e.eq? with
  | some (_, lhs, rhs) => some (lhs, rhs)
  | none => e.iff?

/-- Try adding the lemma to the `RefinedDiscrTree`. -/
def updateDiscrTree (name : Name) (cinfo : ConstantInfo) (d : RefinedDiscrTree RewriteLemma) :
    MetaM (RefinedDiscrTree RewriteLemma) := do
  if isBadDecl name cinfo (← getEnv) then
    return d
  let (vars, _, eqn) ← forallMetaTelescope cinfo.type
  let some (lhs, rhs) := matchEqn? eqn | return d
  d.insertEqn lhs rhs
    { name, symm := false, numParams := vars.size }
    { name, symm := true,  numParams := vars.size }

section

open Std.Tactic

@[reducible]
def RewriteCache := DeclCache (RefinedDiscrTree RewriteLemma × RefinedDiscrTree RewriteLemma)

def RewriteCache.mk
  (init : Option (RefinedDiscrTree RewriteLemma) := none) :
    IO RewriteCache :=
  DeclCache.mk "rw??: init cache" pre ({}, {}) addDecl addLibraryDecl post
where
  pre := do
    let .some libraryTree := init | failure
    return ({}, libraryTree)

  addDecl (name : Name) (cinfo : ConstantInfo)
    | (currentTree, libraryTree) => do
    return (← updateDiscrTree name cinfo currentTree, libraryTree)

  addLibraryDecl (name : Name) (cinfo : ConstantInfo)
    | (currentTree, libraryTree) => do
    return (currentTree, ← updateDiscrTree name cinfo libraryTree)

  post
    | (currentTree, libraryTree) => do
    return (currentTree, libraryTree.mapArrays (·.qsort (· < ·)))

def cachePath : IO System.FilePath := do
  try
    return (← findOLean `MathlibExtras.LibraryRewrites).withExtension "extra"
  catch _ =>
    return ".lake" / "build" / "lib" / "MathlibExtras" / "LibraryRewrites.extra"

initialize cachedData : RewriteCache ← unsafe do
  let path ← cachePath
  if (← path.pathExists) then
    let (d, _r) ← unpickle (RefinedDiscrTree RewriteLemma) path
    -- We can drop the `CompactedRegion` value; we do not plan to free it
    RewriteCache.mk (init := some d)
  else
    RewriteCache.mk

def getRewriteLemmas : MetaM (RefinedDiscrTree RewriteLemma × RefinedDiscrTree RewriteLemma) := do
  let (currentTree, libraryTree) ← cachedData.get
  return (currentTree.mapArrays (·.qsort (· < ·)), libraryTree)

end


/-- The `Expr` at a `SubExpr.GoalsLocation`. -/
def _root_.Lean.SubExpr.GoalsLocation.rootExpr : SubExpr.GoalsLocation → MetaM Expr
  | ⟨mvarId, .hyp fvarId⟩        => mvarId.withContext fvarId.getType
  | ⟨mvarId, .hypType fvarId _⟩  => mvarId.withContext fvarId.getType
  | ⟨mvarId, .hypValue fvarId _⟩ => mvarId.withContext do return (← fvarId.getDecl).value
  | ⟨mvarId, .target _⟩          => mvarId.getType

/-- The `SubExpr.Pos` of a `SubExpr.GoalsLocation`. -/
def _root_.Lean.SubExpr.GoalsLocation.pos : SubExpr.GoalsLocation → SubExpr.Pos
  | ⟨_, .hyp _⟩          => .root
  | ⟨_, .hypType _ pos⟩  => pos
  | ⟨_, .hypValue _ pos⟩ => pos
  | ⟨_, .target pos⟩     => pos

/-- find the positions of the pattern that `kabstract` would find -/
def findPositions (p e : Expr) : MetaM (Array SubExpr.Pos) := do
  let e ← instantiateMVars e
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let rec visit (e : Expr) (pos : SubExpr.Pos) (positions : Array SubExpr.Pos) :
      MetaM (Array SubExpr.Pos) := do
    let visitChildren : Array SubExpr.Pos → MetaM (Array SubExpr.Pos) :=
      match e with
      | .app f a         => visit f pos.pushAppFn
                        >=> visit a pos.pushAppArg
      | .mdata _ b       => visit b pos
      | .proj _ _ b      => visit b pos.pushProj
      | .letE _ t v b _  => visit t pos.pushLetVarType
                        >=> visit v pos.pushLetValue
                        >=> visit b pos.pushLetBody
      | .lam _ d b _     => visit d pos.pushBindingDomain
                        >=> visit b pos.pushBindingBody
      | .forallE _ d b _ => visit d pos.pushBindingDomain
                        >=> visit b pos.pushBindingBody
      | _                => pure
    if e.hasLooseBVars || e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren positions
    else
      let mctx ← getMCtx
      if (← isDefEq e p) then
        setMCtx mctx
        visitChildren (positions.push pos)
      else
        visitChildren positions
  visit e .root #[]


open Widget ProofWidgets Jsx

structure RewriteApplication extends RewriteLemma where
  tactic : String
  replacement : CodeWithInfos
  extraGoals : Array CodeWithInfos

/-- Return `e` as a string for pasting into the editor. -/
def toReadableString (e : Expr) : MetaM String :=
  withOptions (·.setBool ``pp.universes false) do
    return toString $ Format.pretty (← ppExpr e)

def mkMap (k v : String) : Json :=
  let map : RBMap String String compare := RBMap.empty.insert k v
  toJson map

def rewriteCall (loc : SubExpr.GoalsLocation) (rwLemma : RewriteLemma) :
    MetaM (Option RewriteApplication) := do
  let thm ← mkConstWithFreshMVarLevels rwLemma.name
  let (mvars, bis, eqn) ← forallMetaTelescope (← inferType thm)
  let some (lhs, rhs) := matchEqn? eqn | return none
  let target ← loc.rootExpr
  let subExpr ← Core.viewSubexpr loc.pos target
  let (lhs, rhs) := if rwLemma.symm then (rhs, lhs) else (lhs, rhs)
  unless ← isDefEq lhs subExpr do return none

  let mut extraGoals := #[]
  for mvar in mvars, bi in bis do
    let mvarId := mvar.mvarId!
    -- we need to check that all instances can be synthesized
    if bi.isInstImplicit then
      unless (← trySynthInstance (← mvarId.getType)) matches .some _ do
        return none
    else if bi.isExplicit then
      if !(← mvarId.isAssigned) then
        -- if the userName has macro scopes, we can't use the name, so we use `?_` instead
        if (← mvarId.getDecl).userName.hasMacroScopes then
          mvarId.setUserName `«_»
        let extraGoal ← instantiateMVars (← mvarId.getType)
        extraGoals := extraGoals.push (← Widget.ppExprTagged extraGoal)

  let replacement ← Widget.ppExprTagged (← instantiateMVars rhs)
  let lemmaApplication ← instantiateMVars (mkAppN thm mvars)

  let location ← (do match loc.loc with
    | .hyp fvarId
    | .hypType fvarId _ => return s! " at {← fvarId.getUserName}"
    | _ => return "")
  let symm := if rwLemma.symm then "← " else ""
  let lhs ← instantiateMVars lhs
  let positions ← findPositions lhs target
  let cfg := match positions.findIdx? (· == loc.pos) with
    | none => " /- Error: couldn't find a suitable occurrence -/"
    | some pos =>
      if positions.size == 1 then "" else
        s! " (config := \{ occs := .pos [{pos+1}]})"
  let tactic := s! "rw{cfg} [{symm}{← toReadableString lemmaApplication}]{location}"
  return some { rwLemma with tactic, extraGoals, replacement }


def renderResults (results : Array (Array RewriteApplication)) (isEverything : Bool)
    (range : Lsp.Range) (doc : FileWorker.EditableDocument) : Html :=
  let htmls := results.map renderBlock
  let htmls := htmls.concatMap (#[·, <hr/>])
  let title := s! "{if isEverything then "All" else "Some"} rewrite suggestions:"
  (<details «open»={true}>
    <summary className="mv2 pointer"> {.text title}</summary>
    {.element "div" #[] htmls}
  </details>)
where
  renderBlock (results : Array RewriteApplication) : Html :=
    .element "div" #[] $ results.map fun rw =>
      let button := Html.ofComponent MakeEditLink
            (.ofReplaceRange doc.meta range rw.tactic none)
            #[.text s! "{rw.name}"]
      let replacement := <InteractiveCode fmt={rw.replacement} />
      let extraGoals := rw.extraGoals.concatMap
        (#[<br/>, <strong «class»="goal-vdash">⊢ </strong>, <InteractiveCode fmt={·} />])
      .element "p" #[] (#[replacement] ++ extraGoals ++ #[<br/>, button])

/-- Return all potenital rewrite lemmata -/
def getCandidates (e : Expr) : MetaM (Array (Array RewriteLemma × Nat)) := do
  let (localLemmas, libraryLemmas) ← getRewriteLemmas
  let localResults ← localLemmas.getMatchWithScore e (unify := true) (config := {})
  let libraryResults ← libraryLemmas.getMatchWithScore e (unify := true) (config := {})
  let allResults := localResults ++ libraryResults
  return allResults

/-- `Props` for interactive tactics.
    Keeps track of the range in the text document of the piece of syntax to replace. -/
structure InteractiveTacticProps extends PanelWidgetProps where
  replaceRange : Lsp.Range
  factor : Nat
deriving RpcEncodable

@[specialize]
def filterLemmata {α β} (ass : Array (Array α × Nat)) (f : α → MetaM (Option β))
  (maxTotal := 10000) (max := 1000) : MetaM (Array (Array β × Nat) × Bool) :=
  let maxTotal := maxTotal * 1000
  let max := max * 1000
  withCatchingRuntimeEx do
  let startHeartbeats ← IO.getNumHeartbeats
  let mut currHeartbeats := startHeartbeats
  let mut bss := #[]
  let mut isEverything := true
  for (as, n) in ass do
    let mut bs := #[]
    for a in as do
      try
        if let some b ← withTheReader Core.Context ({· with
            initHeartbeats := currHeartbeats
            maxHeartbeats := max }) do
              withoutCatchingRuntimeEx (f a) then
          bs := bs.push b
      catch _ =>
        isEverything := false

      currHeartbeats ← IO.getNumHeartbeats
      if currHeartbeats - startHeartbeats > maxTotal then
        break

    unless bs.isEmpty do
      bss := bss.push (bs, n)
    if currHeartbeats - startHeartbeats > maxTotal then
      return (bss, false)
  return (bss, isEverything)

@[server_rpc_method]
def LibraryRewrite.rpc (props : InteractiveTacticProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
  let doc ← RequestM.readDoc
  let some loc := props.selectedLocations.back?
    | return <p> rw??: Please shift-click an expression. </p>
  if loc.loc matches .hypValue .. then
    return <p> rw doesn't work on the value of a let-bound free variable. </p>
  let some goal := props.goals.find? (·.mvarId == loc.mvarId)
    | return <p> Couln't find the goal. </p>
  goal.ctx.val.runMetaM {} do -- similar to `SelectInsertConv`
    let md ← goal.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do
      let subExpr ← Core.viewSubexpr loc.pos (← loc.rootExpr)
      if subExpr.hasLooseBVars then
        return <p> rw doesn't work with bound variables. </p>
      let rwLemmas ← getCandidates subExpr
      if rwLemmas.isEmpty then
        return <p> No rewrite lemmata found. </p>
      let (results, isEverything) ← filterLemmata rwLemmas (rewriteCall loc)
        (max := props.factor * 1000) (maxTotal := props.factor * 10000)
      if results.isEmpty then
        return <p> No applicable rewrite lemmata found. </p>
      return renderResults (results.map (·.1)) isEverything props.replaceRange doc

@[widget_module]
def LibraryRewrite : Component InteractiveTacticProps :=
  mk_rpc_widget% LibraryRewrite.rpc

/--
After writing `rw??`, shift-click an expression in the tactic state.
This creates a list of rewrite suggestions for the selected expression.
Clicking on the lemma name of a suggestion will paste the `rw` tactic into the editor.

`rw??` is constrained in runtime. To increase the maximum heartbeats, specify a factor by which
to increase it, e.g. `rw?? 5` for 5 times as high a maximum.
If all potential results have been checked successfully, it will say `All rewrite results:`.
-/
syntax (name := rw??) "rw??" (num)? : tactic

@[tactic Mathlib.Tactic.LibraryRewrite.rw??]
def elabRw?? : Elab.Tactic.Tactic := fun stx => match stx with
  | `(tactic| rw?? $(factor)?) => do
    let some range := (← getFileMap).rangeOfStx? stx | return
    let factor := match factor with | some n => n.raw.isNatLit?.getD 1 | none => 1
    Widget.savePanelWidgetInfo (hash LibraryRewrite.javascript)
      (pure $ json% { replaceRange : $(range), factor : $(factor) }) stx
  | _ => Elab.throwUnsupportedSyntax
