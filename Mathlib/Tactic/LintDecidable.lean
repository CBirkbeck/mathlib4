import Std.Tactic.Lint
import Mathlib.Lean.Expr.Basic

namespace Std.Tactic.Lint
open Lean Meta

/--
Linter that checks for theorems that assume `[Decidable p]`
but don't use this assumption in the type.
-/
@[std_linter] def decidableClassical : Linter where
  noErrorsFound := "No uses of `Decidable` arguments should be replaced with `classical`"
  errorsFound := "USES OF `Decidable` SHOULD BE REPLACED WITH `classical` IN THE PROOF."
  test declName := do
    if (← isAutoDecl declName) then return none
    let info ← getConstInfo declName
    let type := info.type
    let names :=
      if Name.isPrefixOf `Decidable declName then #[`Fintype, `Encodable]
      else #[`Decidable, `DecidableEq, `DecidablePred, `Inhabited, `Fintype, `Encodable]
    let mut impossibleArgs ← forallTelescopeReducing type fun args ty => do
      let argTys ← args.mapM inferType
      let ty ← ty.eraseProofs
      return ← (args.zip argTys.zipWithIndex).filterMapM fun (arg, t, i) => do
        unless names.any t.cleanupAnnotations.getForallBody.isAppOf do return none
        let fv := arg.fvarId!
        if ty.containsFVar fv then return none
        if argTys[i+1:].any (·.containsFVar fv) then return none
        return some (i, (← addMessageContextFull m!"argument {i+1} {arg} : {t}"))
    if !(← isProp type) then
      if let some e := info.value? then
        impossibleArgs ← lambdaTelescope e fun args e => do
          let e ← e.eraseProofs
          return impossibleArgs.filter fun (k, _) =>
            k < args.size && !e.containsFVar args[k]!.fvarId!
    if impossibleArgs.isEmpty then return none
    return some <| .joinSep (impossibleArgs.toList.map Prod.snd) ", "
