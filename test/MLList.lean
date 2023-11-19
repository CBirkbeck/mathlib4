/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.MLList.Basic
import Mathlib.Control.Basic
import Mathlib.Tactic.RunCmd
import Std.Tactic.GuardMsgs
import Mathlib.Data.MLList.Meta

@[reducible] def S (α : Type) := StateT (List Nat) Option α
def append (x : Nat) : S Unit :=
  fun s => some ((), x :: s)

def F : Nat → S Nat
  | 0 => failure
  | (n+1) => do
      append (n+1)
      pure n

open Lean

run_cmd Lean.Elab.Command.liftTermElabM do
  -- Note that `fix` fails if any invocation of `F` fails.
  -- This is different from previous behaviour, where it just terminated the lazy list.
  -- Hence we must use `.takeAsList 11` here rather than `.force`.
  let x := ((MLList.fix F 10).takeAsList 11).run []
  guard $ x = some ([10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10])

example : ((MLList.fix F 10).takeAsList 4).run [] = some ([10, 9, 8, 7], [8, 9, 10]) := by
  native_decide
example :
    (((MLList.fix F 10).map fun n => n*n).takeAsList 3).run [] =
      some ([100, 81, 64], [9, 10]) := by
  native_decide

def l1 : MLList S Nat := MLList.ofList [0,1,2]
def l2 : MLList S Nat := MLList.ofList [3,4,5]
def ll : MLList S Nat := (MLList.ofList [l1, l2]).join

run_cmd Lean.Elab.Command.liftTermElabM do
  let x := ll.force.run []
  guard $ x = some ([0, 1, 2, 3, 4, 5], [])

def half_or_fail (n : Nat) : MetaM Nat :=
do guard (n % 2 = 0)
   pure (n / 2)

run_cmd Lean.Elab.Command.liftTermElabM do
  let x : MLList MetaM Nat := MLList.range
  let y := x.filterMapM fun n => try? <| half_or_fail n
  let z ← y.takeAsList 10
  guard $ z.length = 10

run_cmd Lean.Elab.Command.liftTermElabM do
  let R : MLList MetaM Nat := MLList.range
  let S : MLList MetaM Nat := R.filterMapM fun n => try? do
    guard (n % 5 = 0)
    pure n
  let n ← R.takeAsList 5
  let m ← S.head
  guard $ n = [0,1,2,3,4]
  guard $ m = 0

run_cmd Lean.Elab.Command.liftTermElabM do
  let R : MLList MetaM Nat := MLList.range
  let n ← R.firstM fun n => try? do
    guard (n = 5)
    pure n
  guard $ n = 5

/-!
Tests for `runGreedily`, which converts a `List (MetaM α)` into a `MLList MetaM α`,
streaming results as they become available.
-/

def busy_wait (millis : Nat) : IO Unit := do
  let start ← IO.monoMsNow
  while !(← IO.checkCanceled) && (← IO.monoMsNow) < start + millis do pure ()
  if (← IO.checkCanceled) then throw <| IO.userError "cancelled"

open Lean.Meta.MetaM

/--
info: 0
-/
#guard_msgs in
#eval show MetaM _ from do
  -- We put an `IO.sleep 0` in the long calculation to prevent Lean from optimizing away the `do`.
  let t : List (MetaM Nat) := [do busy_wait 1000; pure 1000, do busy_wait 0; pure 0]
  let r := runGreedily' t
  r.head

/--
info: 1
-/
#guard_msgs in
#eval show MetaM _ from do
  let t : List (MetaM Nat) := [do busy_wait 0; pure 1, do busy_wait 5; pure 0]
  let r := runGreedily' t
  r.head

/--
info: Without cancellation:
Result: 0
Results after waiting: [10, 0]
With cancellation:
Result: 0
Results after waiting: [0]
-/
#guard_msgs in
#eval show MetaM _ from do
  let ref : IO.Ref (List Nat) ← IO.mkRef []
  let store : Nat → IO Nat := fun n => do ref.modify fun l => n :: l; pure n
  let t : List (MetaM Nat) := [do busy_wait 10; store 10, do busy_wait 0; store 0]
  let r := runGreedily' t
  IO.println "Without cancellation:"
  IO.println s!"Result: {← r.head}"
  IO.sleep 20
  IO.println s!"Results after waiting: {← ref.get}"
  IO.println "With cancellation:"
  ref.set []
  let (c, r) ← runGreedily t
  IO.println s!"Result: {← r.head}"
  _ ← c
  IO.sleep 20
  IO.println s!"Results after waiting: {← ref.get}"
