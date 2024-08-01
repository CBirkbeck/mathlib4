/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta, Huỳnh Trần Khanh, Stuart Presnell
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod

/-!
# Stars and bars

In this file, we prove (in `Sym.card_sym_eq_multichoose`) that the function `multichoose n k`
defined in `Data/Nat/Choose/Basic` counts the number of multisets of cardinality `k` over an
alphabet of cardinality `n`. In conjunction with `Nat.multichoose_eq` proved in
`Data/Nat/Choose/Basic`, which shows that `multichoose n k = choose (n + k - 1) k`,
this is central to the "stars and bars" technique in combinatorics, where we switch between
counting multisets of size `k` over an alphabet of size `n` to counting strings of `k` elements
("stars") separated by `n-1` dividers ("bars").

## Informal statement

Many problems in mathematics are of the form of (or can be reduced to) putting `k` indistinguishable
objects into `n` distinguishable boxes; for example, the problem of finding natural numbers
`x1, ..., xn` whose sum is `k`. This is equivalent to forming a multiset of cardinality `k` from
an alphabet of cardinality `n` -- for each box `i ∈ [1, n]` the multiset contains as many copies
of `i` as there are items in the `i`th box.

The "stars and bars" technique arises from another way of presenting the same problem. Instead of
putting `k` items into `n` boxes, we take a row of `k` items (the "stars") and separate them by
inserting `n-1` dividers (the "bars").  For example, the pattern `*|||**|*|` exhibits 4 items
distributed into 6 boxes -- note that any box, including the first and last, may be empty.
Such arrangements of `k` stars and `n-1` bars are in 1-1 correspondence with multisets of size `k`
over an alphabet of size `n`, and are counted by `choose (n + k - 1) k`.

Note that this problem is one component of Gian-Carlo Rota's "Twelvefold Way"
https://en.wikipedia.org/wiki/Twelvefold_way

## Formal statement

Here we generalise the alphabet to an arbitrary fintype `α`, and we use `Sym α k` as the type of
multisets of size `k` over `α`. Thus the statement that these are counted by `multichoose` is:
`Sym.card_sym_eq_multichoose : card (Sym α k) = multichoose (card α) k`
while the "stars and bars" technique gives
`Sym.card_sym_eq_choose : card (Sym α k) = choose (card α + k - 1) k`


## Tags

stars and bars, multichoose
-/


open Finset Fintype Function Sum Nat

variable {α β : Type*}

namespace Sym

section Sym

variable (α) (n : ℕ)

/-- Over `Fin (n + 1)`, the multisets of size `k + 1` containing `0` are equivalent to those of size
`k`, as demonstrated by respectively erasing or appending `0`. -/
protected def e1 {n k : ℕ} : { s : Sym (Fin (n + 1)) (k + 1) // ↑0 ∈ s } ≃ Sym (Fin n.succ) k where
  toFun s := s.1.erase 0 s.2
  invFun s := ⟨cons 0 s, mem_cons_self 0 s⟩
  left_inv s := by simp
  right_inv s := by simp

/-- The multisets of size `k` over `Fin n+2` not containing `0`
are equivalent to those of size `k` over `Fin n+1`,
as demonstrated by respectively decrementing or incrementing every element of the multiset.
-/
protected def e2 {n k : ℕ} : { s : Sym (Fin n.succ.succ) k // ↑0 ∉ s } ≃ Sym (Fin n.succ) k where
  toFun s := map (Fin.predAbove 0) s.1
  invFun s :=
    ⟨map (Fin.succAbove 0) s,
      (mt mem_map.1) (not_exists.2 fun t => not_and.2 fun _ => Fin.succAbove_ne _ t)⟩
  left_inv s := by
    ext1
    simp only [map_map]
    refine (Sym.map_congr fun v hv ↦ ?_).trans (map_id' _)
    exact Fin.succAbove_predAbove (ne_of_mem_of_not_mem hv s.2)
  right_inv s := by
    simp only [map_map, comp_apply, ← Fin.castSucc_zero, Fin.predAbove_succAbove, map_id']

-- Porting note: use eqn compiler instead of `pincerRecursion` to make cases more readable
theorem card_sym_fin_eq_multichoose : ∀ n k : ℕ, card (Sym (Fin n) k) = multichoose n k
  | n, 0 => by simp
  | 0, k + 1 => by rw [multichoose_zero_succ]; exact card_eq_zero
  | 1, k + 1 => by simp
  | n + 2, k + 1 => by
    rw [multichoose_succ_succ, ← card_sym_fin_eq_multichoose (n + 1) (k + 1),
      ← card_sym_fin_eq_multichoose (n + 2) k, add_comm (Fintype.card _), ← card_sum]
    refine Fintype.card_congr (Equiv.symm ?_)
    apply (Sym.e1.symm.sumCongr Sym.e2.symm).trans
    apply Equiv.sumCompl

/-- For any fintype `α` of cardinality `n`, `card (Sym α k) = multichoose (card α) k`. -/
theorem card_sym_eq_multichoose (α : Type*) (k : ℕ) [Fintype α] [Fintype (Sym α k)] :
    card (Sym α k) = multichoose (card α) k := by
  rw [← card_sym_fin_eq_multichoose]
  -- FIXME: Without the `Fintype` namespace, why does it complain about `Finset.card_congr` being
  -- deprecated?
  exact Fintype.card_congr (equivCongr (equivFin α))

/-- The *stars and bars* lemma: the cardinality of `Sym α k` is equal to
`Nat.choose (card α + k - 1) k`. -/
theorem card_sym_eq_choose {α : Type*} [Fintype α] (k : ℕ) [Fintype (Sym α k)] :
    card (Sym α k) = (card α + k - 1).choose k := by
  rw [card_sym_eq_multichoose, Nat.multichoose_eq]

end Sym

end Sym
