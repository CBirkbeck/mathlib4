/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Lean.Parser.Syntax

/-!
#  The `commandStart` linter

The `commandStart` linter emits a warning if
* a command does not start at the beginning of a line;
* the "hypotheses segment" of a declaration does not coincide with its pretty-printed version.
-/

open Lean Elab Command

namespace Mathlib.Linter

/--
The `commandStart` linter emits a warning if
* a command does not start at the beginning of a line;
* the "hypotheses segment" of a declaration does not coincide with its pretty-printed version.

In practice, this makes sure that the spacing in a typical declaration looks like
```lean
example (a : Nat) {R : Type} [Add R] : <not linted part>
```
as opposed to
```lean
example (a: Nat) {R:Type}  [Add  R] : <not linted part>
```
-/
register_option linter.style.commandStart : Bool := {
  defValue := true
  descr := "enable the commandStart linter"
}

/-- If the `linter.style.commandStart.verbose` is `true`, the `commandStart` linter
reports some helpful diagnostic information. -/
register_option linter.style.commandStart.verbose : Bool := {
  defValue := false
  descr := "enable the commandStart linter"
}

/-- `lintUpTo stx` returns the position up until the `commandStart` linter checks the formatting.
This is every declaration until the type-specification, if there is one, or the value,
as well as all `variable` commands.
-/
def lintUpTo (stx : Syntax) : Option String.Pos :=
  if let some cmd := stx.find? (·.isOfKind ``Parser.Command.declaration) then
    if let some ind := cmd.find? (·.isOfKind ``Parser.Command.inductive) then
      match ind.find? (·.isOfKind ``Parser.Command.optDeclSig) with
      | none => dbg_trace "unreachable?"; none
      | some sig => sig.getTailPos?
    else
    match cmd.find? (·.isOfKind ``Parser.Term.typeSpec) with
      | some s => s.getPos?
      | none => match cmd.find? (·.isOfKind ``Parser.Command.declValSimple) with
        | some s => s.getPos?
        | none => none
  else if stx.isOfKind ``Parser.Command.variable then
    stx.getTailPos?
  else none

/--
A `FormatError` is the main structure for keeping track of how different the user syntax is
from the pretty-printed version of itself.

It contains information about position within an ambient string of where the exception lies.
-/
structure FormatError where
  /-- The distance to the end of the source string, as number of characters. -/
  srcNat : Nat
  /-- The distance to the end of the source string, as number of string positions. -/
  srcEndPos : String.Pos
  /-- The distance to the end of the formatted string, as number of characters. -/
  fmtPos : Nat
  /-- The kind of formatting error: `extra space`, `remove line break` or `missing space`. -/
  msg : String
  /-- The length of the mismatch, as number of characters. -/
  length : Nat
  /-- The length of the mismatch, as a `String.pos`. -/
  srcStartPos : String.Pos
  deriving Inhabited

instance : ToString FormatError where
  toString f :=
    s!"srcNat: {f.srcNat}, srcPos: {f.srcEndPos}, fmtPos: {f.fmtPos}, \
      msg: {f.msg}, length: {f.length}\n"

/-- Produces a `FormatError` from the input data.  In particular, it extracts the position
information within the string, both as number of characters and as `String.Pos`. -/
def mkFormatError (ls ms : String) (msg : String) (length : Nat := 1) : FormatError where
  srcNat := ls.length
  srcEndPos := ls.endPos
  fmtPos := ms.length
  msg := msg
  length := length
  srcStartPos := ls.endPos

/--
Add a new `FormatError` `f` to the array `fs`, trying, as much as possible, to merge the new
`FormatError` with the last entry of `fs`.
-/
def pushFormatError (fs : Array FormatError) (f : FormatError) : Array FormatError :=
  -- If there are no errors already, we simply add the new one.
  if fs.isEmpty then fs.push f else
  let back := fs.back!
  -- If the latest error is of a different kind that then new one, we simply add the new one.
  if back.msg != f.msg || back.srcNat - back.length != f.srcNat then fs.push f else
  -- Otherwise, we are adding a further error of the same kind and we therefore merge the two.
  fs.pop.push {back with length := back.length + f.length, srcStartPos := f.srcEndPos}

/--
It scans the two input strings `L` and `M`, assuming that they `M` is the pretty-printed version
of `L`.
This almost means that `L` and `M` only differ in whitespace.

While it scans the two strings, it accumulates the discrepancies that it finds with some heuristics
for not flagging all line-break changes, since the pretty-printer does not always produce desirably
formatted code.
-/
partial
def parallelScanAux (as : Array FormatError) (L M : String) : Array FormatError :=
  --dbg_trace "'{L}'\n'{M}'\n---\n"
  if M.trim.isEmpty then as else
  if L.take 3 == "/--" && M.take 3 == "/--" then
    parallelScanAux as (L.drop 3) (M.drop 3) else
  if L.take 2 == "--" then
    let newL := L.dropWhile (· != '\n')
    let diff := L.length - newL.length
    let newM := M.dropWhile (· != '-') |>.drop diff
    parallelScanAux as newL.trimLeft newM.trimLeft else
  if L.take 2 == "-/" then
    let newL := L.drop 2 |>.trimLeft
    let newM := M.drop 2 |>.trimLeft
    parallelScanAux as newL newM else
  let ls := L.drop 1
  let ms := M.drop 1
  match L.get 0, M.get 0 with
  | ' ', m =>
    if m.isWhitespace then
      parallelScanAux as ls ms.trimLeft
    else
      parallelScanAux (pushFormatError as (mkFormatError L M "extra space")) ls M
  | '\n', m =>
    if m.isWhitespace then
      parallelScanAux as ls.trimLeft ms.trimLeft
    else
      parallelScanAux (pushFormatError as (mkFormatError L M "remove line break")) ls.trimLeft M
  | l, m => -- `l` is not whitespace
    if l == m then
      parallelScanAux as ls ms
    else
      if m.isWhitespace then
        parallelScanAux (pushFormatError as (mkFormatError L M "missing space")) L ms.trimLeft
    else
      pushFormatError as (mkFormatError ls ms "Oh no! (Unreachable?)")

@[inherit_doc parallelScanAux]
def parallelScan (src fmt : String) : Array FormatError :=
  parallelScanAux ∅ src fmt

namespace Style.CommandStart

/--
`unlintedNodes` contains the `SyntaxNodeKind`s for which there is no clear formatting preference:
if they appear in surface syntax, the linter will ignore formatting.

Currently, the unlined nodes are mostly related to `Subtype`, `Set` and `Finset` notation and
list notation.
-/
abbrev unlintedNodes := #[
  -- # set-like notations, have extra spaces around the braces `{` `}`

  -- subtype, the pretty-printer prefers `{ a // b }`
  ``«term{_:_//_}»,
  -- set notation, the pretty-printer prefers `{ a | b }`
  `«term{_}»,
  -- empty set, the pretty-printer prefers `{ }`
  ``«term{}»,
  -- set builder notation, the pretty-printer prefers `{ a : X | p a }`
  `Mathlib.Meta.setBuilder,

  -- # misc exceptions

  -- We ignore literal strings.
  `str,

  -- list notation, the pretty-printer prefers `a :: b`
  ``«term_::_»,

  -- negation, the pretty-printer prefers `¬a`
  ``«term¬_»,

  -- declaration name, avoids dealing with guillemets pairs `«»`
  ``Parser.Command.declId,

  `Mathlib.Tactic.superscriptTerm, `Mathlib.Tactic.subscript,

  -- notation for `Bundle.TotalSpace.proj`, the total space of a bundle
  -- the pretty-printer prefers `π FE` over `π F E` (which we want)
  `Bundle.termπ__,

  -- notation for `Finset.slice`, the pretty-printer prefers `𝒜 #r` over `𝒜 # r` (mathlib style)
  `Finset.«term_#_»,

  -- The docString linter already takes care of formatting doc-strings.
  ``Parser.Command.docComment,

  -- `omit [A] [B]` prints as `omit [A][B]`, see https://github.com/leanprover/lean4/pull/8169
  ``Parser.Command.omit,

  -- https://github.com/leanprover-community/aesop/pull/203
  `Aesop.Frontend.Parser.aesop,
  ]

/--
Given an array `a` of `SyntaxNodeKind`s, we accumulate the ranges of the syntax nodes of the
input syntax whose kind is in `a`.

The linter uses this information to avoid emitting a warning for nodes with kind contained in
`unlintedNodes`.
-/
def getUnlintedRanges(a : Array SyntaxNodeKind) :
    Std.HashSet String.Range → Syntax → Std.HashSet String.Range
  | curr, s@(.node _ kind args) =>
    let new := args.foldl (init := curr) (·.union <| getUnlintedRanges a curr ·)
    if a.contains kind then
      new.insert (s.getRange?.getD default)
    else
      new
  | curr, _ => curr

/-- Given a `HashSet` of `String.Ranges` `rgs` and a further `String.Range` `rg`,
`outside rgs rg` returns `true` if and only if `rgs` contains a range the completely contains
`rg`.

The linter uses this to figure out which nodes should be ignored.
-/
def outside? (rgs : Std.HashSet String.Range) (rg : String.Range) : Bool :=
  let superRanges := rgs.filter fun {start := a, stop := b} => (a ≤ rg.start && rg.stop ≤ b)
  superRanges.isEmpty

@[inherit_doc Mathlib.Linter.linter.style.commandStart]
def commandStartLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.style.commandStart (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  if stx.find? (·.isOfKind ``runCmd) |>.isSome then
    return
  -- If a command does not start on the first column, emit a warning.
  if let some pos := stx.getPos? then
    let colStart := ((← getFileMap).toPosition pos).column
    if colStart ≠ 0 then
      Linter.logLint linter.style.commandStart stx
        m!"'{stx}' starts on column {colStart}, \
          but all commands should start at the beginning of the line."
  -- We skip `macro_rules`, since they cause parsing issues.
  if stx.find? (·.isOfKind ``Lean.Parser.Command.macro_rules) |>.isSome then
    return

  let fmt : Option Format := ←
      try
        liftCoreM <| PrettyPrinter.ppCategory `command stx
      catch _ =>
        Linter.logLintIf linter.style.commandStart.verbose (stx.getHead?.getD stx)
          m!"The `commandStart` linter had some parsing issues: \
            feel free to silence it and report this error!"
        return none
  if let some fmt := fmt then
    let st := fmt.pretty
    let origSubstring := stx.getSubstring?.getD default
    let orig := origSubstring.toString
    let scan := parallelScan orig st

    let some upTo := lintUpTo stx | return
    let docStringEnd := stx.find? (·.isOfKind ``Parser.Command.docComment) |>.getD default
    let docStringEnd := docStringEnd.getTailPos? |>.getD default
    let forbidden := getUnlintedRanges unlintedNodes ∅ stx
    for s in scan do
      let center := origSubstring.stopPos - s.srcEndPos
      let rg : String.Range := ⟨center, center + s.srcEndPos - s.srcStartPos + ⟨1⟩⟩
      if s.msg.startsWith "Oh no" then
        Linter.logLintIf linter.style.commandStart.verbose (.ofRange rg)
          m!"This should not have happened: please report this issue!"
        Linter.logLintIf linter.style.commandStart.verbose (.ofRange rg)
          m!"Formatted string:\n{fmt}\nOriginal string:\n{origSubstring}"
        continue
      unless outside? forbidden rg do
        continue
      unless rg.stop ≤ upTo do return
      unless docStringEnd ≤ rg.start do return

      let ctx := 5 -- the number of characters before and after of the mismatch that linter prints
      let srcWindow :=
        orig.takeRight (s.srcNat + ctx) |>.take (s.length + 2 * ctx -  1) |>.replace "\n" "⏎"
      let expectedWindow :=
        st.takeRight (s.fmtPos + ctx) |>.take (2 * ctx) |>.replace "\n" "⏎"
      Linter.logLint linter.style.commandStart (.ofRange rg)
        m!"{s.msg}\n\n\
          Current syntax:  '{srcWindow}'\n\
          Expected syntax: '{expectedWindow}'\n"
      Linter.logLintIf linter.style.commandStart.verbose (.ofRange rg)
        m!"Formatted string:\n{fmt}\nOriginal string:\n{origSubstring}"

initialize addLinter commandStartLinter

end Style.CommandStart

end Mathlib.Linter
