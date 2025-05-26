/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Order.CollectFacts
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Translating linear orders to ℤ

In this file we implement the translation of a problem in any linearly ordered type to a problem in
`ℤ`. This allows us to use the `omega` tactic to solve it.

While the core algorithm of the `order` tactic is complete for the theory of linear orders in the
signature (`<`, `≤`),
it becomes incomplete in the signature with lattices operations `⊓` and `⊔`. With this operations
the problem becomes NP-hard, and the idea is to reuse some smart and efficient procedure, such as
`omega`.

## TODO

Migrate to `grind` when it is ready.

-/

namespace Mathlib.Tactic.Order.ToInt

variable {α : Type*} [LinearOrder α]

lemma exists_max {n : ℕ} (val : Fin (n + 1) → α) :
    ∃ imax, ∀ j, val j ≤ val imax := by
  induction n with
  | zero => simp [Fin.forall_fin_one, Fin.exists_fin_one]
  | succ n ih =>
    cases val using Fin.consCases with | _ x val =>
    obtain ⟨i, hi⟩ := ih val
    by_cases h_max : val i < x
    · use 0
      intro j
      cases j using Fin.cases with
      | zero => simp
      | succ j =>
        simp only [Fin.cons_succ, Fin.cons_zero]
        apply (hi _).trans
        exact le_of_lt h_max
    · use i.succ
      intro j
      cases j using Fin.cases with
      | zero => simpa using h_max
      | succ j => simp [hi]

lemma exists_bound {n : ℕ} (tr : Fin n → ℤ) : ∃ M, ∀ i, tr i < M := by
  cases n with
  | zero => simp
  | succ n =>
    obtain ⟨i, hi⟩ := exists_max tr
    use tr i + 1
    intro j
    specialize hi j
    omega

variable {n : ℕ} (val : Fin n → α)

theorem exists_translation : ∃ tr : Fin n → ℤ, ∀ i j, val i ≤ val j ↔ tr i ≤ tr j := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨imax, h_imax⟩ := exists_max val
    obtain ⟨tr, h2⟩ := ih (Fin.removeNth imax val)
    by_cases h_imax' : ∃ j : Fin n, val (imax.succAbove j) = val imax
    · obtain ⟨imax2, h3⟩ := h_imax'
      use Fin.insertNth imax (tr imax2) tr
      intro i j
      cases i using Fin.succAboveCases imax <;> cases j using Fin.succAboveCases imax
        <;> simp [← h3, ← h2, Fin.removeNth]
    · push_neg at h_imax'
      obtain ⟨M, hM⟩ : ∃ M, ∀ i, tr i < M := exists_bound tr
      use Fin.insertNth imax M tr
      have h_succ (i : Fin n) : val (Fin.succAbove imax i) < val imax :=
        lt_of_le_of_ne (h_imax (Fin.succAbove imax i)) (h_imax' i)
      intro i j
      cases i using Fin.succAboveCases imax <;> cases j using Fin.succAboveCases imax
        <;> simp [(hM _).not_le, (hM _).le, h_succ, h_imax, ← h2, Fin.removeNth]

/-- Auxiliary definition used by the `order` tactic to transfer facts in a linear order to `ℤ`. -/
noncomputable def toInt (k : Fin n) : ℤ :=
  (exists_translation val).choose k

variable (i j k : Fin n)

theorem toInt_le_toInt : toInt val i ≤ toInt val j ↔ val i ≤ val j := by
  simp [toInt, (exists_translation val).choose_spec]

theorem toInt_lt_toInt : toInt val i < toInt val j ↔ val i < val j := by
  simpa using (toInt_le_toInt val j i).not

theorem toInt_eq_toInt : toInt val i = toInt val j ↔ val i = val j := by
  simp [toInt_le_toInt, le_antisymm_iff]

theorem toInt_ne_toInt : toInt val i ≠ toInt val j ↔ val i ≠ val j := by
  simpa using (toInt_eq_toInt val i j).not

theorem toInt_nle_toInt : ¬toInt val i ≤ toInt val j ↔ ¬val i ≤ val j := by
  simpa using toInt_lt_toInt val j i

theorem toInt_nlt_toInt : ¬toInt val i < toInt val j ↔ ¬val i < val j := by
  simpa using toInt_le_toInt val j i

theorem toInt_sup_toInt_eq_toInt :
    toInt val i ⊔ toInt val j = toInt val k ↔ val i ⊔ val j = val k := by
  simp [le_antisymm_iff, sup_le_iff, le_sup_iff, toInt_le_toInt]

theorem toInt_inf_toInt_eq_toInt :
    toInt val i ⊓ toInt val j = toInt val k ↔ val i ⊓ val j = val k := by
  simp [le_antisymm_iff, inf_le_iff, le_inf_iff, toInt_le_toInt]

open Lean Meta Qq

/-- Given an array `atoms : Array α`, create an expression representing a function
`f : Fin atoms.size → α` such that `f n` is defeq to `atoms[n]` for `n : Fin atoms.size`. -/
def mkFinFun {u : Level} {α : Q(Type $u)} (atoms : Array Q($α)) : MetaM Expr := do
  if h : atoms.isEmpty then
    return q(Fin.elim0 : Fin 0 → $α)
  else
    let rarray := RArray.ofArray atoms (by simpa [Array.size_pos_iff] using h)
    let rarrayExpr : Q(RArray $α) ← rarray.toExpr α (fun x ↦ x)
    haveI m : Q(ℕ) := mkNatLit atoms.size
    return q(fun (x : Fin $m) ↦ ($rarrayExpr).get x.val)

/-- Translates a set of values in a linear ordered type to `ℤ`,
preserving all the facts except for `.isTop` and `.isBot`. These facts are filtered at the
preprocessing step. -/
def translateToInt {u : Lean.Level} (type : Q(Type u)) (inst : Q(LinearOrder $type))
    (idxToAtom : Std.HashMap ℕ Q($type))
    (facts : Array AtomicFact) :
    MetaM <| Std.HashMap ℕ Q(ℤ) × Array AtomicFact := do
  haveI mkNatQ : ℕ → Q(ℕ) := Lean.mkNatLit
  haveI nE : Q(ℕ) := mkNatQ idxToAtom.size
  haveI finFun : Q(Fin $nE → $type) :=
    ← mkFinFun (Array.ofFn fun (n : Fin idxToAtom.size) => idxToAtom[n]!)
  let toFinUnsafe : ℕ → Q(Fin $nE) := fun k =>
    haveI kE := mkNatQ k
    haveI heq : decide ($kE < $nE) =Q true := ⟨⟩
    q(⟨$kE, of_decide_eq_true $heq⟩)
  return Prod.snd <| facts.foldl (fun (curr, map, facts) fact =>
    match fact with
    | .eq lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q($finFun $lhsFin = $finFun $rhsFin) := prf
        .eq lhs rhs q((toInt_eq_toInt $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .ne lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q($finFun $lhsFin ≠ $finFun $rhsFin) := prf
        .ne lhs rhs q((toInt_ne_toInt $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .le lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q($finFun $lhsFin ≤ $finFun $rhsFin) := prf
        .le lhs rhs q((toInt_le_toInt $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .lt lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q($finFun $lhsFin < $finFun $rhsFin) := prf
        .lt lhs rhs q((toInt_lt_toInt $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .nle lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q(¬$finFun $lhsFin ≤ $finFun $rhsFin) := prf
        .nle lhs rhs q((toInt_nle_toInt $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .nlt lhs rhs prf =>
      (curr, map, facts.push (
        haveI lhsFin := toFinUnsafe lhs
        haveI rhsFin := toFinUnsafe rhs
        haveI prfQ : Q(¬$finFun $lhsFin < $finFun $rhsFin) := prf
        .nlt lhs rhs q((toInt_nlt_toInt $finFun $lhsFin $rhsFin).mpr $prfQ)
      ))
    | .isBot _
    | .isTop _ => (curr, map, facts)
    | .isSup lhs rhs val =>
      haveI lhsFin := toFinUnsafe lhs
      haveI rhsFin := toFinUnsafe rhs
      haveI valFin := toFinUnsafe val
      haveI heq : max («$finFun» «$lhsFin») («$finFun» «$rhsFin») =Q «$finFun» «$valFin» := ⟨⟩
      (curr + 1, map.insert curr q(toInt $finFun $lhsFin ⊔ toInt $finFun $rhsFin),
        (facts.push (.isSup lhs rhs curr)).push (.eq curr val
          q((toInt_sup_toInt_eq_toInt $finFun $lhsFin $rhsFin $valFin).mpr $heq)
        )
      )
    | .isInf lhs rhs val =>
      haveI lhsFin := toFinUnsafe lhs
      haveI rhsFin := toFinUnsafe rhs
      haveI valFin := toFinUnsafe val
      haveI heq : min («$finFun» «$lhsFin») («$finFun» «$rhsFin») =Q «$finFun» «$valFin» := ⟨⟩
      (curr + 1, map.insert curr q(toInt $finFun $lhsFin ⊓ toInt $finFun $rhsFin),
        (facts.push (.isInf lhs rhs curr)).push (.eq curr val
          q((toInt_inf_toInt_eq_toInt $finFun $lhsFin $rhsFin $valFin).mpr $heq)
        )
      ))
    (idxToAtom.size, idxToAtom.map fun k _ =>
      haveI kFin := toFinUnsafe k
      q(toInt $finFun $kFin), Array.emptyWithCapacity idxToAtom.size)

end Mathlib.Tactic.Order.ToInt

export Mathlib.Tactic.Order.ToInt (translateToInt)
