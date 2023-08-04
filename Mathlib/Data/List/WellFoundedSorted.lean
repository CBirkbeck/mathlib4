/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Dagur Asgeirsson
-/
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Lex
import Mathlib.Data.List.MinMax
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.OrderIsoNat

/-!
# Decreasing lists in a well founded linear order are well founded.

If `α` is linearly ordered with `[WellFoundedLT α]`, then the lexicographic ordering on
"decreasing lists" (i.e. `{l : List α // l.Sorted (· > ·)}`) is well founded.

## Main results

* `wellFoundedLT_iff_not_strictAnti`: A preorder `α` is well founded if and only if there is no
  strictly antitone sequence in `α`.
* `wellFoundedLT_sorted`: If a linear order `α` is well founded, then the the lexicographic
  ordering on `{l : List α // l.Sorted (· > ·)}` is well founded.

## Proof sketch of `wellFoundedLT_sorted`

By `wellFoundedLT_iff_not_strictAnti`, it suffieces to construct a strictly antitone sequence in `α`
given a stricly antitone sequence `f : ℕ → {l : List α // l.Sorted (· > ·)}`. The idea is as
follows:

We prove that for all `n : ℕ`, the sequence of `l n` of lists given by taking the first `n` elements
of the terms of `f` is eventually constant. Define `a : ℕ → α` such that `a n` is the `n`-th term
of the limit of the sequence `l n`. By the `List.Sorted` condition on the terms of `f`, this
sequence is strictly decreasing.

## See also

Related files are:
* `Mathlib.Data.List.Lex`: Lexicographic order on lists.
* `Mathlib.Order.OrderIsoNat`: Results about antitone sequences in well founded orders

-/

variable (α : Type _)

/-- A preorder `α` is well founded if and only if there exists no strictly antitone sequence in
    `α`. -/
theorem wellFoundedLT_iff_not_strictAnti [Preorder α] :
    WellFoundedLT α ↔ ∀ f : ℕ → α, ¬ StrictAnti f := by
  rw [WellFoundedLT, IsWellFounded_iff, RelEmbedding.wellFounded_iff_no_descending_seq]
  refine' ⟨fun h f hf ↦ isEmpty_iff.mp h (RelEmbedding.natGT f (fun n ↦ hf (Nat.lt_succ_self n))),
    fun h ↦ isEmpty_iff.mpr (fun f ↦ h f.toEmbedding (fun _ _ _ ↦ _))⟩
  rwa [f.map_rel_iff']

variable {α} [LinearOrder α]

/--
Constructs the smallest monotone function larger than a given function,
defined by `leastOrderHom f n = [f 0, f 1, ..., f n].maximum_of_length_pos (by simp)`.
-/
def leastOrderHom (f : ℕ → α) : ℕ →o α where
  toFun n := (List.range (n + 1)).map f |>.maximum_of_length_pos (by simp)
  monotone' n m h := by
    apply List.le_maximum_of_length_pos_of_mem
    dsimp
    obtain ⟨a, m, w⟩ :=
      List.exists_mem_eq_maximum_of_length_pos ((List.range (n + 1)).map f) (by simp)
    rw [← w]
    simp at m
    obtain ⟨b, w', rfl⟩ := m
    simp only [List.mem_map, List.mem_range]
    exact ⟨b, (lt_of_lt_of_le w' (Nat.add_le_add_right h 1)), rfl⟩

theorem le_leastOrderHom (f : ℕ → α) : f ≤ leastOrderHom f := by
  intro n
  dsimp [leastOrderHom]
  apply List.le_maximum_of_length_pos_of_mem
  simp only [List.mem_map, List.mem_range]
  exact ⟨n, Nat.lt_succ_self _, rfl⟩

namespace wellFoundedLT_sorted

variable (α)
variable [WellFoundedLT α]

/-- The type of decreasing lists in `α` -/
def DecreasingList := { l : List α // l.Sorted (· > · ) }

instance : LinearOrder (DecreasingList α) := inferInstanceAs <| LinearOrder { _l : List α // _ }

@[simp] lemma DecreasingList.lt_iff (x y : DecreasingList α) : x < y ↔ x.1 < y.1 := Iff.rfl

/-- The type of **S**trictly **D**ecreasing **S**equences in `DecreasingList α` -/
def SDS := { f : ℕ → DecreasingList α // StrictAnti f }

variable {α}

/-- For `n : ℕ` and `L : SDS α`, `Q n L` is a pair `(N : ℕ, S : List α)` such that the sequence
    of lists obtained by taking the first `n` elements of the terms of `L` is constant from index
    `N` with value `S`. -/
def Q (n : ℕ) (L : SDS α) :=
  Σ' N, Σ' S : List α, S.length = n ∧ ∀ (m), N ≤ m → (L.1 m).1.take n = S

def DecreasingList.drop (l : DecreasingList α) (m : ℕ) : DecreasingList α :=
  ⟨l.1.drop m, l.2.drop⟩

/-- Translate a stricly decreasing sequence by `m` -/
def SDS.translate (L : SDS α) (m : ℕ) : SDS α :=
  ⟨fun n => L.1 (n + m), fun _ _ h => L.2 (Nat.add_lt_add_right h m)⟩

def SDS.dropQ_aux (L : SDS α) (S : List α) (m : ℕ) (w : ∀ n, (L.1 n).1.take m = S) : SDS α :=
  ⟨fun n => (L.1 n).drop m, by
    intro a b h
    have := L.2 h
    change (L.1 b).1 < (L.1 a).1 at this
    rw [← List.take_append_drop m (L.1 a).1, ← List.take_append_drop m (L.1 b).1, w, w] at this
    simpa using this⟩

/-- Take an `L : SDS` such that the sequence of lists given by taking the first `n` elements of
    its terms is constant from index `N`. Translate it by `N` and then drop the first `n` elements
    of each term. This gives a new `SDS`. -/
def SDS.dropQ (L : SDS α) (w : Q n L) : SDS α := by
  obtain ⟨N, S, w⟩ := w
  refine (L.translate N).dropQ_aux S n ?_
  intro m
  exact (w.2 (m + N) (Nat.le_add_left N m))

theorem SDS.dropQ_apply (L : SDS α) (w : Q n L) : ((L.dropQ w).1 m).1 = (L.1 (m + w.1)).1.drop n :=
  rfl

def Q_succ (L : SDS α) (w' : Q n L) (w₁ : Q 1 (L.dropQ w')) : Q (n+1) L := by
  obtain ⟨N', S', s', w'⟩ := w'
  obtain ⟨N₁, S₁, s₁, w₁⟩ := w₁
  use N' + N₁
  use S' ++ S₁
  constructor
  · simp [s', s₁]
  intro m h
  specialize w' m (le_of_add_le_left h)
  specialize w₁ (m - N') (le_tsub_of_add_le_left h)
  simp only [SDS.dropQ_apply] at w₁
  rw [Nat.sub_add_cancel (le_of_add_le_left h)] at w₁
  rw [List.take_add]
  rw [w', w₁]

def SDS.head? (L : SDS α) : ℕ → Option α := fun n => (L.1 n).1.head?

lemma SDS.head?_isSome (L : SDS α) (n : ℕ) : (L.head? n).isSome := by
  by_contra h
  simp [SDS.head?] at h
  have := L.2 (Nat.lt_succ_self n)
  simp [h] at this

def SDS.head (L : SDS α) : ℕ → α := fun n => (L.head? n).get (L.head?_isSome n)

lemma SDS.head_antitone (L : SDS α) : Antitone L.head := by
  intro a b h
  rcases lt_or_eq_of_le h with (h | rfl)
  · have := L.2 h
    simp [SDS.head, SDS.head?]
    apply List.head?_get_mono _ _ _ _ this
  · rfl

lemma SDS.head_eventually_constant (L : SDS α) : ∃ N a, ∀ n, N ≤ n → L.head n = a := by
  obtain ⟨N, hN⟩ := WellFounded.antitone_chain_condition.mp IsWellFounded.wf _ L.head_antitone
  exact ⟨N, L.head N, hN⟩

theorem Q_one {L : SDS α} : Nonempty (Q 1 L) := by
  obtain ⟨N, a, w⟩ := L.head_eventually_constant
  apply Nonempty.intro
  use N
  use [a]
  use rfl
  intro m h
  specialize w m h
  simp [SDS.head, SDS.head?, Option.get?_eq_some] at w
  simpa [List.take_one_eq_singleton_iff]

/-- For every `n : ℕ`, the sequence given by taking the first `n` elements of each term of an
    `SDS` is eventually constant. -/
noncomputable
def SDS.EventuallyConstant (L : SDS α) : ∀ n, Q n L := fun n ↦ Nonempty.some (by
  induction n using Nat.strong_induction_on generalizing L
  case h n a =>
    cases n
    case zero =>
      exact ⟨0, [], rfl, fun m _ ↦ by simp⟩
    case succ n =>
      cases n
      case zero =>
        apply Q_one
      case succ n =>
        apply Nonempty.intro
        apply Q_succ
        · apply Nonempty.some
          apply a
          exact Nat.one_lt_succ_succ n
        · apply Nonempty.some
          apply a
          exact Nat.lt_succ_self _ )

/-- For every `n : ℕ`, the sequence given by taking the first `n` elements of each term of an
    `SDS` is eventually constant, where the index from which it is eventually constant is
    controlled by a `g : ℕ →o ℕ` -/
theorem SDS.exists_orderHom_eventuallyConstant (L : SDS α) :
    ∃ g : ℕ →o ℕ, ∀ n, ∃ S : List α, S.length = n ∧ ∀ m, g n ≤ m → (L.1 m).1.take n = S := by
  use leastOrderHom fun n => (L.EventuallyConstant n).1
  intro n
  use (L.EventuallyConstant n).2.1
  use (L.EventuallyConstant n).2.2.1
  intro m h
  apply (L.EventuallyConstant n).2.2.2
  exact (le_leastOrderHom _ _).trans h

/-- Let `L : SDS α`. Then there exists a `g : ℕ →o ℕ` such that for all `n`, from index `g n` on
    two things hold:
    1) The terms of `L` have length at least `n`
    2) The `x`-th elements of the terms of `L` are all equal for `x < n`. -/
theorem main (L : SDS α) : ∃ g : ℕ →o ℕ, ∀ (n : ℕ), ∀ (m₁ : ℕ), g n ≤ m₁ → n ≤ (L.1 m₁).1.length ∧
    ∀ m₂, g n ≤ m₂ → ∀ x, x < n → (h₁ : _) → (h₂ : _) →
    (L.1 m₁).1.get ⟨x, h₁⟩ = (L.1 m₂).1.get ⟨x, h₂⟩ := by
  obtain ⟨g, w⟩ := L.exists_orderHom_eventuallyConstant
  use g
  intro n m₁ mh₁
  constructor
  · obtain ⟨S, s, w⟩ := w n
    specialize w m₁ mh₁
    rw [←List.take_append_drop n (L.1 m₁).1]
    simp [s, w]
  · intro m₂ mh₂ x lt h₁ h₂
    obtain ⟨S, _, w⟩ := w n
    have w₁ := w m₁ mh₁
    have w₂ := w m₂ mh₂
    apply List.get_eq_get_of_take_eq_take _ _ _ _ _ lt
    simp [w₁, w₂]

end wellFoundedLT_sorted

open wellFoundedLT_sorted

instance wellFoundedLT_sorted [WellFoundedLT α] :
    WellFoundedLT { l : List α // l.Sorted (· > · ) } :=
  (wellFoundedLT_iff_not_strictAnti _).mpr (fun f w => by
    obtain ⟨g, h⟩ := main ⟨f, w⟩
    have lt_length : ∀ n, n < (f (g (n + 1))).1.length :=
      fun n => lt_of_lt_of_le (Nat.lt_succ_self n) (h (n + 1) (g (n + 1)) (le_refl _)).1
    let z : ℕ → α := fun n => (f (g (n + 1))).1.get ⟨n, lt_length n⟩
    apply (wellFoundedLT_iff_not_strictAnti α).mp ‹_› z
    intro a b lt
    calc
      z b = (f (g (b + 1))).1.get ⟨b, lt_length b⟩ := rfl
      _   < (f (g (b + 1))).1.get ⟨a, lt.trans (lt_length _)⟩ :=
              List.pairwise_iff_get.mp (f (g (b + 1))).2 _ _ lt
      _   = (f (g (a + 1))).1.get ⟨a, lt_length a⟩ :=
              ((h (a + 1) (g (a + 1)) (le_refl _)).2
                (g (b + 1)) (g.2 (Nat.succ_le_succ lt.le)) a (Nat.lt_succ_self _) _ _).symm
      _   = z a := rfl)
