/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Simon Hudon, Thomas Murrills, Mario Carneiro
-/
import Qq
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Util.AtomM
import Mathlib.Data.List.TFAE

/-!
# The Following Are Equivalent (TFAE)

This file provides the tactics `tfae_have` and `tfae_finish` for proving goals of the form
`TFAE [P₁, P₂, ...]`.
-/

namespace Mathlib.Tactic.TFAE

/-! # Parsing and syntax

We implement `tfae_have` in terms of a syntactic `have`. To support as much of the same syntax as
possible, we recreate the parsers for `have`, except with the changes necessary for `tfae_have`.
-/

open Lean.Parser Term

namespace Parser

/- An arrow of the form `←`, `→`, or `↔`. -/
private def impTo : Parser := leading_parser unicodeSymbol " → " " -> "
private def impFrom : Parser := leading_parser unicodeSymbol " ← " " <- "
private def impIff : Parser := leading_parser unicodeSymbol " ↔ " " <-> "
private def impArrow : Parser := leading_parser impTo <|> impFrom <|> impIff

/-- A `tfae_have` type specification, e.g. `: 1 ↔ 3`. -/
private def tfaeType := " : " >> num >> impArrow >> num

/-!
The following parsers are exactly the same as those for `have` in `Lean.Parser.Term`, but
instead of `optType`, we use `tfaeType := num >> impArrow >> num` (as a `tfae_have` invocation must
always include this specification). Also, we disallow including extra binders, as that makes no
sense in this context.
-/

/-- See `haveIdLhs`.

We omit `many (ppSpace >> letIdBinder)`, as it makes no sense to add extra arguments to a
`tfae_have` decl.  -/
private def tfaeHaveIdLhs := ((ppSpace >> binderIdent) <|> hygieneInfo)  >> tfaeType
/-- See `haveIdDecl`. E.g. `h : 1 → 3 := term`. -/
private def tfaeHaveIdDecl   := leading_parser (withAnonymousAntiquot := false)
  atomic (tfaeHaveIdLhs >> " := ") >> termParser
/-- See `haveEqnsDecl`. E.g. `h : 1 → 3 | p => f p`. -/
private def tfaeHaveEqnsDecl := leading_parser (withAnonymousAntiquot := false)
  tfaeHaveIdLhs >> matchAlts
/-- See `letPatDecl`. E.g. `⟨mp, mpr⟩ : 1 ↔ 3 := term`. -/
private def tfaeHavePatDecl  := leading_parser (withAnonymousAntiquot := false)
  atomic (termParser >> pushNone >> tfaeType >> " := ") >> termParser
/-- See `haveDecl`. Any of `tfaeHaveIdDecl`, `tfaeHavePatDecl`, or `tfaeHaveEqnsDecl`. -/
private def tfaeHaveDecl     := leading_parser (withAnonymousAntiquot := false)
  tfaeHaveIdDecl <|> (ppSpace >> tfaeHavePatDecl) <|> tfaeHaveEqnsDecl

end Parser

open Parser

/--
`tfae_have` introduces hypotheses for proving goals of the form `TFAE [P₁, P₂, ...]`. Specifically,
`tfae_have : i <arrow> j := ...` introduces a hypothesis of type `Pᵢ <arrow> Pⱼ` to the local
context, where `<arrow>` can be `→`, `←`, or `↔`. Note that `i` and `j` are natural number indices
(beginning at 1) used to specify the propositions `P₁, P₂, ...` that appear in the goal.

```lean
example (h : P → R) : TFAE [P, Q, R] := by
  tfae_have : 1 → 3 := h
  ...
```
The resulting context now includes `tfae_1_to_3 : P → R`.

Once sufficient hypotheses have been introduced by `tfae_have`, `tfae_finish` can be used to close
the goal. For example,

```lean
example : TFAE [P, Q, R] := by
  tfae_have : 1 → 2 := sorry /- proof of P → Q -/
  tfae_have : 2 → 1 := sorry /- proof of Q → P -/
  tfae_have : 2 ↔ 3 := sorry /- proof of Q ↔ R -/
  tfae_finish
```

All relevant features of `have` are supported by `tfae_have`, including naming, destructuring, goal
creation, and matching. These are demonstrated below.

```lean
example : TFAE [P, Q] := by

  tfae_have : 1 → 2 := sorry -- `tfae_1_to_2 : P → Q`
  tfae_have hpq : 1 → 2 := sorry -- `hpq : P → Q`
  tfae_have _ : 1 → 2 := sorry -- inaccessible `h✝ : P → Q`
  tfae_have : 1 → 2 := f ?a -- `tfae_1_to_2 : P → Q`, and `?a` is a new goal
  tfae_have : 1 → 2
  | p => f p -- match on `p : P` and prove `Q`
  tfae_have ⟨pq, qp⟩ : 1 ↔ 2 := sorry -- introduces `pq : P → Q`, `qp : Q → P`

  tfae_finish
```
-/
syntax (name := tfaeHave) "tfae_have " tfaeHaveDecl : tactic

/--
`tfae_finish` is used to close goals of the form `TFAE [P₁, P₂, ...]` once a sufficient collection
of hypotheses of the form `Pᵢ → Pⱼ` or `Pᵢ ↔ Pⱼ` have been introduced to the local context.

`tfae_have` can be used to conveniently introduce these hypotheses; see `tfae_have`.

Example:
```lean
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2 := sorry /- proof of P → Q -/
  tfae_have 2 → 1 := sorry /- proof of Q → P -/
  tfae_have 2 ↔ 3 := sorry /- proof of Q ↔ R -/
  tfae_finish
```
-/
syntax (name := tfaeFinish) "tfae_finish" : tactic


/-! # Setup -/

open List Lean Meta Expr Elab Tactic Mathlib.Tactic Qq

/-- Extract a list of `Prop` expressions from an expression of the form `TFAE [P₁, P₂, ...]` as
long as `[P₁, P₂, ...]` is an explicit list. -/
partial def getTFAEList (t : Expr) : MetaM (Q(List Prop) × List Q(Prop)) := do
  let .app tfae (l : Q(List Prop)) ← whnfR <|← instantiateMVars t
    | throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  unless (← withNewMCtxDepth <| isDefEq tfae q(TFAE)) do
    throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  return (l, ← getExplicitList l)
where
  /-- Convert an expression representing an explicit list into a list of expressions. -/
  getExplicitList (l : Q(List Prop)) : MetaM (List Q(Prop)) := do
    match l with
    | ~q([]) => return ([] : List Expr)
    | ~q($a :: $l') => return (a :: (← getExplicitList l'))
    | e => throwError "{e} must be an explicit list of propositions"

/-! # Proof construction -/

variable (hyps : Array (ℕ × ℕ × Expr)) (atoms : Array Q(Prop))

/-- Uses depth-first search to find a path from `P` to `P'`. -/
partial def dfs (i j : ℕ) (P P' : Q(Prop)) (hP : Q($P)) : StateT (HashSet ℕ) MetaM Q($P') := do
  if i == j then
    return hP
  modify (·.insert i)
  for (a, b, h) in hyps do
    if i == a then
      if !(← get).contains b then
        have Q := atoms[b]!
        have h : Q($P → $Q) := h
        try return ← dfs b j Q P' q($h $hP) catch _ => pure ()
  failure

/-- Prove an implication via depth-first traversal. -/
def proveImpl (i j : ℕ) (P P' : Q(Prop)) : MetaM Q($P → $P') := do
  try
    withLocalDeclD (← mkFreshUserName `h) P fun (h : Q($P)) => do
      mkLambdaFVars #[h] <|← dfs hyps atoms i j P P' h |>.run' {}
  catch _ =>
    throwError "couldn't prove {P} → {P'}"

/-- Generate a proof of `Chain (· → ·) P l`. We assume `P : Prop` and `l : List Prop`, and that `l`
is an explicit list. -/
partial def proveChain (i : ℕ) (is : List ℕ) (P : Q(Prop)) (l : Q(List Prop)) :
    MetaM Q(Chain (· → ·) $P $l) := do
  match l with
  | ~q([]) => return q(Chain.nil)
  | ~q($P' :: $l') =>
    -- `id` is a workaround for https://github.com/leanprover-community/quote4/issues/30
    let i' :: is' := id is | unreachable!
    have cl' : Q(Chain (· → ·) $P' $l') := ← proveChain i' is' q($P') q($l')
    let p ← proveImpl hyps atoms i i' P P'
    return q(Chain.cons $p $cl')

/-- Attempt to prove `getLastD l P' → P` given an explicit list `l`. -/
partial def proveGetLastDImpl (i i' : ℕ) (is : List ℕ) (P P' : Q(Prop)) (l : Q(List Prop)) :
    MetaM Q(getLastD $l $P' → $P) := do
  match l with
  | ~q([]) => proveImpl hyps atoms i' i P' P
  | ~q($P'' :: $l') =>
    -- `id` is a workaround for https://github.com/leanprover-community/quote4/issues/30
    let i'' :: is' := id is | unreachable!
    proveGetLastDImpl i i'' is' P P'' l'

/-- Attempt to prove a statement of the form `TFAE [P₁, P₂, ...]`. -/
def proveTFAE (is : List ℕ) (l : Q(List Prop)) : MetaM Q(TFAE $l) := do
  match l with
  | ~q([]) => return q(tfae_nil)
  | ~q([$P]) => return q(tfae_singleton $P)
  | ~q($P :: $P' :: $l') =>
    -- `id` is a workaround for https://github.com/leanprover-community/quote4/issues/30
    let i :: i' :: is' := id is | unreachable!
    let c ← proveChain hyps atoms i (i'::is') P q($P' :: $l')
    let il ← proveGetLastDImpl hyps atoms i i' is' P P' l'
    return q(tfae_of_cycle $c $il)

/-! # `tfae_have` components -/

/-- Construct a name for a hypothesis introduced by `tfae_have`. -/
def mkTFAEId (i : TSyntax `num) (arr : TSyntax ``impArrow) (j : TSyntax `num) : MacroM Name := do
  let arr ← match arr with
  | `(impArrow| ← ) => pure "from"
  | `(impArrow| → ) => pure "to"
  | `(impArrow| ↔ ) => pure "iff"
  | _ => Macro.throwUnsupported
  return String.intercalate "_" ["tfae", s!"{i.getNat}", arr, s!"{j.getNat}"]

/-- Turn syntax for a given index into a natural number, as long as it lies between `1` and
`maxIndex`. -/
def elabIndex (i : TSyntax `num) (maxIndex : ℕ) : MetaM ℕ := do
  let i' := i.getNat
  unless 1 ≤ i' && i' ≤ maxIndex do
    throwErrorAt i "{i} must be between 1 and {maxIndex}"
  return i'

/-! # Tactic implementation -/

/-- Accesses the propositions at indices `i` and `j` of `tfaeList`, and constructs the expression
`Pi <arr> Pj`, which will be the type of our `tfae_have` hypothesis -/
def elabTFAEHaveType (tfaeList : List Q(Prop)) (i : TSyntax `num)
    (arr : TSyntax ``impArrow) (j : TSyntax `num) : MetaM Expr := do
  let l := tfaeList.length
  let i' ← elabIndex i l
  let j' ← elabIndex j l
  let Pi := tfaeList.get! (i'-1)
  let Pj := tfaeList.get! (j'-1)
  match arr with
  | `(impArrow| ← ) => pure q($Pj → $Pi)
  | `(impArrow| → ) => pure q($Pi → $Pj)
  | `(impArrow| ↔ ) => pure q($Pi ↔ $Pj)
  | _ => throwErrorAt arr "expected '→', '←', or '↔'"

/- Convert `tfae_have : i <arr> j ...` to `tfae_have tfae_i_arr_j : i <arr> j ...`. See
`expandHave`, which is responsible for inserting `this` in `have : A := ...`. Note that we
require some extra help for `tfaeHave'` (Mathlib `have`). -/
macro_rules
| `(tfaeHave|tfae_have $hy:hygieneInfo : $i:num $arr:impArrow $j:num := $val) => do
  let id := HygieneInfo.mkIdent hy (← mkTFAEId i arr j) (canonical := true)
  `(tfaeHave|tfae_have $id : $i $arr $j := $val)
| `(tfaeHave|tfae_have $hy:hygieneInfo : $i:num $arr:impArrow $j:num $alts:matchAlts) => do
  let id := HygieneInfo.mkIdent hy (← mkTFAEId i arr j) (canonical := true)
  `(tfaeHave|tfae_have $id : $i $arr $j $alts)

elab_rules : tactic
| `(tfaeHave|tfae_have $d:tfaeHaveDecl) => withMainContext do
  let goal ← getMainGoal
  let (_, tfaeList) ← getTFAEList (← goal.getType)
  match d with
  | `(tfaeHaveDecl| $b : $i:num $arr:impArrow $j:num := $t:term) =>
    let type ← elabTFAEHaveType tfaeList i arr j
    evalTactic <|← `(tactic|have $b : $(← type.toSyntax) := $t)
  | `(tfaeHaveDecl| $b : $i:num $arr:impArrow $j:num $alts:matchAlts) =>
    let type ← elabTFAEHaveType tfaeList i arr j
    evalTactic <|← `(tactic|have $b : $(← type.toSyntax) $alts:matchAlts)
  | `(tfaeHaveDecl| $pat:term : $i:num $arr:impArrow $j:num := $t:term) =>
    let type ← elabTFAEHaveType tfaeList i arr j
    evalTactic <|← `(tactic|have $pat:term : $(← type.toSyntax) := $t)
  | _ => throwUnsupportedSyntax


elab_rules : tactic
| `(tactic| tfae_finish) => do
  let goal ← getMainGoal
  goal.withContext do
    let (tfaeListQ, tfaeList) ← getTFAEList (← goal.getType)
    closeMainGoal <|← AtomM.run .reducible do
      let is ← tfaeList.mapM AtomM.addAtom
      let mut hyps := #[]
      for hyp in ← getLocalHyps do
        let ty ← whnfR <|← instantiateMVars <|← inferType hyp
        if let (``Iff, #[p1, p2]) := ty.getAppFnArgs then
          let q1 ← AtomM.addAtom p1
          let q2 ← AtomM.addAtom p2
          hyps := hyps.push (q1, q2, ← mkAppM ``Iff.mp #[hyp])
          hyps := hyps.push (q2, q1, ← mkAppM ``Iff.mpr #[hyp])
        else if ty.isArrow then
          let q1 ← AtomM.addAtom ty.bindingDomain!
          let q2 ← AtomM.addAtom ty.bindingBody!
          hyps := hyps.push (q1, q2, hyp)
      proveTFAE hyps (← get).atoms is tfaeListQ
