/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Init
import Lean.Meta.WHNF

/-!
# Basic Definitions for `RefinedDiscrTree`

We define
* `Key`, the discrimination tree key
* `LazyEntry`, the partial, lazy computation of a sequence of `Key`s
* `Trie`, a node of the discrimination tree, which is indexed with `Key`s
  and stores an array of pending `LazyEntry`s
* `RefinedDiscrTree`, the discrimination tree itself.
-/

namespace Lean.Meta.RefinedDiscrTree


/-- Discrimination tree key. -/
inductive Key where
  /-- A metavariable. This key matches with anything. It stores an identifier. -/
  | star (id : Nat)
  /-- An opaque variable. This key only matches with `Key.star`. -/
  | opaque
  /-- A constant. It stores the name and the arity. -/
  | const (declName : Name) (nargs : Nat)
  /-- A free variable. It stores the `FVarId` and the arity. -/
  | fvar (fvarId : FVarId) (nargs : Nat)
  /-- A bound variable, from a lambda or forall binder.
  It stores the De Bruijn index and the arity. -/
  | bvar (deBruijnIndex nargs : Nat)
  /-- A literal. -/
  | lit (v : Literal)
  /-- A sort. Universe levels are ignored. -/
  | sort
  /-- A lambda function. -/
  | lam
  /-- A dependent arrow. -/
  | forall
  /-- A projection. It stores the structure name, the projection index and the arity. -/
  | proj (typeName : Name) (idx nargs : Nat)
  deriving Inhabited, BEq

/-
At the root, `.const` is the most common key, and it is very uncommon
to get the same contant name with a different arity.
So for performance, we just use `hash name` to hash `.const name _`.
-/
private nonrec def Key.hash : Key → UInt64
  | .star id             => mixHash 7883 <| hash id
  | .opaque              => 342
  | .const name _        => hash name
  | .fvar fvarId nargs   => mixHash 8765 <| mixHash (hash fvarId) (hash nargs)
  | .bvar idx nargs      => mixHash 4323 <| mixHash (hash idx) (hash nargs)
  | .lit v               => mixHash 1879 <| hash v
  | .sort                => 2411
  | .lam                 => 4742
  | .«forall»            => 9752
  | .proj name idx nargs => mixHash (hash nargs) <| mixHash (hash name) (hash idx)

instance : Hashable Key := ⟨Key.hash⟩

private def Key.format : Key → Format
  | .star id                => f!"*{id}"
  | .opaque                 => "◾"
  | .const name nargs       => f!"⟨{name}, {nargs}⟩"
  | .fvar fvarId nargs      => f!"⟨{fvarId.name}, {nargs}⟩"
  | .lit (Literal.natVal n) => f!"{n}"
  | .lit (Literal.strVal s) => f!"{s.quote}"
  | .sort                   => "Sort"
  | .bvar i nargs           => f!"⟨#{i}, {nargs}⟩"
  | .lam                    => "λ"
  | .forall                 => "∀"
  | .proj name idx nargs    => f!"⟨{name}.{idx}, {nargs}⟩"

instance : ToFormat Key := ⟨Key.format⟩

/--
Converts an entry (i.e., `List Key`) to the discrimination tree into
`MessageData` that is more user-friendly.
-/
partial def keysAsPattern (keys : Array Key) : CoreM MessageData := do
  let (msg, keys) ← go (paren := false) |>.run keys.toList
  if !keys.isEmpty then
    throwError "illegal discrimination tree entry: {keys.map Key.format}"
  return msg
where
  /-- Get the next key. -/
  next : StateRefT (List Key) CoreM Key := do
    let key :: keys ← get | throwError "illegal discrimination tree entry: {keys.map Key.format}"
    set keys
    return key
  /-- Format the application `f args`. -/
  mkApp (f : MessageData) (args : Array MessageData) (paren : Bool) : CoreM MessageData := do
    if args.isEmpty then
      return f
    else
      let mut r := f
      for arg in args do
        r := r ++ m!" {arg}"
      if paren then
        return m!"({r})"
      else
        return r
  /-- Format the next expression. -/
  go (paren := true) : StateRefT (List Key) CoreM MessageData := do
    let key ← next
    match key with
    | .const declName nargs =>
      mkApp m!"{← mkConstWithLevelParams declName}" (← goN nargs) paren
    | .fvar fvarId nargs =>
      mkApp m!"{mkFVar fvarId}" (← goN nargs) paren
    | .proj _ i nargs =>
      mkApp m!"{← go}.{i+1}" (← goN nargs) paren
    | .bvar i nargs =>
      mkApp m!"#{i}" (← goN nargs) paren
    | .lam =>
      let r := m!"λ, {← go (paren := false)}"
      if paren then return m!"({r})" else return r
    | .forall =>
      let r := m!"{← go} → {← go (paren := false)}";
      if paren then return m!"({r})" else return r
    | _ => return key.format
  /-- Format the next `n` expressions. -/
  goN (num : Nat) : StateRefT (List Key) CoreM (Array MessageData) := do
    let mut r := #[]
    for _ in [: num] do
      r := r.push (← go)
    return r

/-- Return the number of arguments that the `Key` takes. -/
def Key.arity : Key → Nat
  | .const _ nargs  => nargs
  | .fvar _ nargs   => nargs
  | .bvar _ nargs   => nargs
  | .lam            => 1
  | .forall         => 2
  | .proj _ _ nargs => nargs + 1
  | _               => 0

/-- The information for computing the keys of a subexpression. -/
structure ExprInfo where
  /-- The expression -/
  expr : Expr
  /-- Variables that come from a lambda or forall binder.
  The list index gives the De Bruijn index. -/
  bvars : List FVarId := []
  /-- The local context, which contains the introduced bound variables. -/
  lctx : LocalContext
  /-- The local instances, which may contain the introduced bound variables. -/
  localInsts : LocalInstances

/-- The possible values that can appear in the stack:
- `.star` is an expression that will not be explicitly indexed
- `.expr` is an expression that will be indexed
- `.cache` is a cache entry, used for computations that can have multiple outcomes,
  so that they always give the same outcome. -/
inductive StackEntry where
  | star
  | expr (info : ExprInfo)
  | cache (key : Expr) (value : List Key)

private def StackEntry.format : StackEntry → Format
  | .star => f!".star"
  | .expr info => f!".expr {info.expr}"
  | .cache key value => f!".cache {key} {value}"

instance : ToFormat StackEntry := ⟨StackEntry.format⟩

/-- A `LazyEntry` represents a snapshot of the computation of encoding an `Expr` as `Array Key`.
This is used for computing the keys one by one. -/
structure LazyEntry where
  /-- If the previous expression creates more StackEntries, then we store its `ExprInfo`. -/
  previous : Option ExprInfo := none
  /-- The stack, used to emulate recursion. -/
  stack    : List StackEntry := []
  /-- The configuration for normalization.
  It could also be stored in the `RefinedDiscrTree` instead, but that is less convenient -/
  config : WhnfCoreConfig
  /-- The metavariable context, which may contain variables appearing in this entry. -/
  mctx     : MetavarContext
  /-- The `MVarId` assignments for converting into `.star` keys. -/
  stars    : AssocList MVarId Nat := {}
  /-- The number to be used for the next new `.star` key. -/
  nStars   : Nat := 0
  /-- The `Key`s that have already been computed. -/
  results  : List Key := []
  /-- The cache of past computations that have multiple possible outcomes. -/
  cache    : AssocList Expr (List Key) := {}

instance : Inhabited (LazyEntry) where
  default := { config := {}, mctx := {} }

private def LazyEntry.format (entry : LazyEntry) : Format :=
  let results := if entry.results matches [] then f!"" else f!", results: {entry.results}, "
  f!"stack: {entry.stack}{results}"

instance : ToFormat LazyEntry := ⟨LazyEntry.format⟩

/-- Array index of a `Trie α` in the `tries` of a `RefinedDiscrTree`. -/
abbrev TrieIndex := Nat

/--
Discrimination tree trie. See `RefinedDiscrTree`.

A `Trie` will normally have exactly one of the following
- nonempty `values`
- nonempty`stars` or `children`
- nonempty `pending`
But defining it as a structure that can have all at the same time turns out to be easier.
-/
structure Trie (α : Type) where
  node ::
    /-- Return values, at a leaf -/
    values : Array α
    /-- Following `Trie`s based on a `Key.star`. -/
    stars : Std.HashMap Nat TrieIndex
    /-- Following `Trie`s based on the `Key`. -/
    children : Std.HashMap Key TrieIndex
    /-- Lazy entries that still have to be evaluated. -/
    pending : Array (LazyEntry × α)

instance {α : Type} : Inhabited (Trie α) := ⟨.node #[] {} {} #[]⟩

end RefinedDiscrTree

open RefinedDiscrTree in

/--
Discrimination tree. It is an index from expressions to values of type `α`.

We store all of the nodes in one `Array`, `tries`, instead of using a 'normal' inductive type.
This is so that we can modify the tree globally, which is very useful when evaluating lazy
entries and saving the result globally.
-/
structure RefinedDiscrTree (α : Type) where
  /-- `Trie`s at the root based of the `Key`. -/
  root : Std.HashMap Key TrieIndex := {}
  /-- Array of trie entries. Should be owned by this trie. -/
  tries : Array (Trie α) := #[]

namespace RefinedDiscrTree

variable {α : Type}

instance : Inhabited (RefinedDiscrTree α) := ⟨{}⟩

private partial def format [ToFormat α] (tree : RefinedDiscrTree α) : Format :=
  let lines := tree.root.fold (init := #[]) fun lines key trie =>
    lines.push (Format.nest 2 f! "{key} =>{Format.line}{go trie}")
  if lines.size = 0 then
    f! "<empty discrimination tree>"
  else
    lines.foldl (init := "Discrimination tree flowchart:") (· ++ Format.line ++ ·)
where
  go (trie : TrieIndex) : Format :=
    let { values, stars, children, pending } := tree.tries[trie]!
    let lines := if pending.isEmpty then #[] else
      #[f! "pending entries: {pending.map (·.2)}"]
    let lines := if values.isEmpty then lines else
      lines.push f! "entries: {values}"
    let lines := stars.fold (init := lines) fun lines key trie =>
      lines.push (Format.nest 2 f! "*{key} =>{Format.line}{go trie}")
    let lines := children.fold (init := lines) fun lines key trie =>
      lines.push (Format.nest 2 f! "{key} =>{Format.line}{go trie}")
    if h : lines.size = 0 then
      f! "<empty node>"
    else
      lines.foldl (init := lines[0]) (· ++ Format.line ++ ·) (start := 1)

instance [ToFormat α] : ToFormat (RefinedDiscrTree α) := ⟨format⟩

end Lean.Meta.RefinedDiscrTree
