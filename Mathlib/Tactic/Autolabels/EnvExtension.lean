/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command

/-!
# Automatic labelling of PRs

This file contains the basic definitions, the environment extension and the API commands
to automatically assign a GitHub label to a PR.

The heuristic used to assign a label is to assign labels to certain folder inside `Mathlib/`
and assign a label to a PR if the PR modifies files within the corresponding folders.

Ultimately, this produces a `HashMap String String` that takes a string representing a path
to a modified file and returns the corresponding GitHub label.

Since the labels are independent of the modified file, we define a `PersistentEnvExtension`
that keeps track of an array of `Label`s.

## The `Label` structure

A `Label` is a structure containing
* the GitHub label (as a `String` -- `Label.label`);
* the array of folders associated to the given label (as an `Array String` -- `Label.dirs`);
* the array of folders that forbid a given label, even though a path may satisfy the conditions
  implied by `dirs` (as an `Array String` -- `Label.exclusions`).

For example, the files in the `Tactic` folder should be labelled as `t-meta`,
except the ones in `Tactic/Linter` that should be labelled `t-linter`.
This would be encoded by
```lean
{ Label.label      := "t-meta"
  Label.dirs       := #["Tactic"]
  Label.exclusions := #["Tactic/Linter"] }`
```
a term of type `Label`.

## The `add_label` command

Since `Label`s are managed by an environment extension, there is a user command to add them.
Thus, the previous label would be added using
```
add_label meta dirs: Tactic exclusions Tactic.Linter
```
The "strings" are passed as identifiers, so that the path-separators `/` should be entered as `.`.
The prefix `t-` in front of `meta` is automatically added by `add_label`.

Look at the documentation for `add_label` for further shortcuts.

## Further commands

The file also defines the commands `check_labels` and `produce_labels(!)? str`.
They display what `Label`s are currently present in the environment and they test-run the automatic
application of the labels to user-input/`git diff` output.
These commands are mostly intended as "debugging commands", even though
`produce_labels "git"` is used in the `autolabel` CI action.

See the doc-strings of `check_labels` and `produce_labels` for more details.
-/

open Lean

namespace AutoLabel

/-- `getLast n` takes as input a name `n` and return the last (string) component, if there is one,
returning the empty string `""` otherwise. -/
def getLast : Name → String
  | .str _ s => s
  | _ => ""

/-- A `Label` is the main structure for converting a folder into a `t-`label.
* The `label` field is the actual GitHub label.
* The `dirs` field is the array of all "root paths" such that a modification in a file contained
  in one of these paths should be labeled by `label`.
* The `exclusions` field is the array of all "root paths" that are excluded, among the
  ones that start with the ones in `dirs`.

It is not really intended to be used directly.
The command `add_label` manages `Label`s: it creates them and adds them to the `Environment`.
-/
structure Label where
  /-- The GitHub label.  This is expected to be in the form `t-label-name-kebab-case]`. -/
  label : String
  /-- The array of "root paths". -/
  dirs : Array System.FilePath
  /-- The array of paths that satisfy the `dirs` constraint, but are nonetheless excluded.
  This gives finer control: for instance, all `Tactic` modifications should get the `t-meta` label,
  *except* for the `Tactic/Linter` modifications that should get the `t-linter` label.
  Most of the times, this field is empty. -/
  exclusions : Array System.FilePath

namespace Label

open System.FilePath (pathSeparator) in
/--
`findLabel? l modifiedFile` takes as input a `Label` `l` and a string `modifiedFile` and checks
if there is a string in `l.dirs` that is a prefix to `s`.
If it finds (at least) one, then it returns `some l.label`, otherwise it returns `none`.
-/
def findLabel? (l : Label) (modifiedFile : String) : Option String :=
  -- check that the path does not match any of the forbidden ones in `exclusions`
  if (l.exclusions.map fun d => d.toString.isPrefixOf modifiedFile).any (·) then
    none
  -- if the path is not excluded, then check if it is among the ones allowed in `dirs`.
  else if (l.dirs.map fun d => d.toString.isPrefixOf modifiedFile).any (·) then
  some l.label else none

/-- `addAllLabels gitDiffs ls` takes as input an array of string `gitDiffs` and an array of
`Label`s `ls`.
It returns the `HashMap` that assigns to each entry of `gitDiffs` the `.label` field from the
appropriate `Label` in `ls`. -/
def addAllLabels (gitDiffs : Array String) (ls : Array Label) : HashMap String String :=
  Id.run do
  let mut tot := {}
  for l in ls do
    for modifiedFile in gitDiffs do
      if let some lab := findLabel? l modifiedFile then
        tot := tot.insert modifiedFile lab
  return tot

/-- Defines the `labelsExt` extension for adding an `Array` of `Label`s to the environment. -/
initialize labelsExt :
    PersistentEnvExtension Label Label (Array Label) ←
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := (pure <| .flatten ·)
    addEntryFn := .push
    exportEntriesFn := id
  }

/--
`formatIdsToDirs dirs` takes as input an array of identifiers `dirs` and converts them
to an array of paths.
It assumes that the identifiers are in `snake_case.with_several.parts`, in converts them to
`Mathlib.SnakeCase.WithSeveral.Parts.` and finally replaces `.` by the path-separator, e.g. `/`.
-/
def formatIdsToDirs (dirs : TSyntaxArray `ident) : Array System.FilePath :=
  dirs.map fun d =>
    let str := (d.getId.toString.splitOn "_").foldl (· ++ ·.capitalize) ""
    -- we prepend `Mathlib` and we append an "empty" segment at the end to ensure that
    -- the path ends with the path separator (e.g. `/`).
    -- This means that, for instance, `Algebra` does not match `AlgebraicGeometry`
    System.mkFilePath (["Mathlib"] ++ str.splitOn "." ++ [""])

/-- The simplest way to add a label is to use `add_label label_name`. This adds
* `t-label-name` as a label and
* `LabelName` as root folder,
meaning that any change to `Mathlib.LabelName` will be labeled by `t-label-name`.

If you want to customize the root folders that are relevant to your label, you can use
`add_label label_name dirs: d₁ d₂ ... dₙ`.  This adds
* `t-label-name` as a label and
* `Mathlib.d₁, Mathlib.d₂, ..., Mathlib.dₙ` as root folders.

Finally, if you also want to filter out of the previous root folders some subfolders, you can use
`add_label label_name dirs: d₁ d₂ ... dₙ exclusions: e₁ e₂ ... eₘ`.  This adds
* `t-label-name` as a label and
* `Mathlib.d₁, Mathlib.d₂, ..., Mathlib.dₙ` as root folders, unless the folder matches
* `Mathlib.e₁, Mathlib.e₂, ..., Mathlib.eₘ`.

The helper command `check_labels` displays all the labels that have already been declared.
-/
syntax (name := addLabelStx)
  "add_label " ident ("dirs: " ident*)? ("exclusions: " ident*)? : command

open Elab.Command in
@[inherit_doc addLabelStx]
elab_rules : command
  | `(command| add_label $id dirs: $dirs* exclusions: $excs*) => do
    setEnv <| labelsExt.addEntry (← getEnv)
      { label := "t-" ++ id.getId.toString.replace "_" "-"
        dirs := formatIdsToDirs dirs
        exclusions := formatIdsToDirs excs }
  | `(command| add_label $id dirs: $dirs*) => do
    elabCommand (← `(command| add_label $id dirs: $dirs* exclusions:))
  | `(command| add_label $id) => do
    elabCommand (← `(command| add_label $id dirs: $id))

/--
`check_labels` is a helper command to `add_labels`.
It displays all the labels that have already been declared.
`check_labels "t-abc"` shows only the labels starting with `t-abc`.
-/
elab "check_labels" st:(ppSpace str)? : command => do
  let str := (st.getD default).getString
  for l in labelsExt.getState (← getEnv) do
    if str.isPrefixOf l.label then
      logInfo m!"label: {l.label}\ndirs: {l.dirs}\nexclusions: {l.exclusions}"

/--
`labelsToFiles env gitDiffs` takes as input an `Environment` `env` and a string `gitDiffs`.
It assumes that `gitDiffs` is a line-break-separated list of paths to files.
It returns the pairings `Label.label → Array filenames` as a `HashMap`.
-/
def labelsToFiles (env : Environment) (gitDiffs : String) : HashMap String (Array String) :=
  let labels := labelsExt.getState env
  let gitDiffs := (gitDiffs.splitOn "\n").toArray
  let hash := addAllLabels gitDiffs labels
  let grouped := gitDiffs.groupByKey (hash.find? · |>.getD "")
  let matched := grouped.erase ""
  let unmatched := ((grouped.find? "").getD #[]).filter (!·.isEmpty)
  if unmatched.isEmpty then
      matched
    else
      matched.insert "unlabeled" unmatched

/--
`produceLabels env gitDiffs` takes as input an `Environment` `env` and a string `gitDiffs`.
It assumes that `gitDiffs` is a line-break-separate list of paths to files.
It uses the paths to check if any of the labels in the environment is applicable.
It returns the sorted array of the applicable labels with no repetitions.
-/
def produceLabels (env : Environment) (gitDiffs : String) : Array String :=
  let grouped := labelsToFiles env gitDiffs
  ((grouped.toArray.map Prod.fst).filter (· != "")).qsort (· < ·)

/--
`produce_labels "A/B/C.lean⏎D/E.lean"` takes as input a string, assuming that it is a
line-break-separated list of paths to files.
It uses the paths to check if any of the labels in the environment are applicable.
It prints the sorted, comma-separated string of the applicable labels with no repetitions.

`produce_labels! "A/B/C.lean⏎D/E.lean"`, with the `!` flag, displays, for each label,
the paths that have that label.

Finally, if the input string is `"git"`, then `produce_labels "git"`/`produce_labels! "git"`
use the output of `git diff --name-only master...HEAD`, instead of literally `"git"`,
to show what labels would get assigned to the current modifications.
-/
elab (name := produceLabelsCmd) tk:"produce_labels" lab:("!")? st:(ppSpace str) : command => do
  let str := ← if st.getString != "git" then return st.getString else
    IO.Process.run { cmd := "git", args := #["diff", "--name-only", "origin/master...HEAD"] }
  let labToFiles := (labelsToFiles (← getEnv) str).toArray.qsort (·.1 < ·.1)
  match lab with
    | some _ => logInfoAt tk m!"{labToFiles}"
    | none =>
      let labels := ((labToFiles.map Prod.fst).filter (· != "unlabeled")).toList
      if labels.isEmpty then
        logInfoAt tk m!"No applicable label."
      else
        logInfoAt tk m!"Applicable labels: {String.intercalate "," labels}"

@[inherit_doc produceLabelsCmd]
macro "produce_labels! " st:str : command => `(produce_labels ! $st)

end AutoLabel.Label
