/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.List.Indexes
import Mathlib.Data.Rel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.IntervalCases

/-!
# Series of a relation

If `r` is a relation on `α` then a relation series of length `n` is a series
`a_0, a_1, ..., a_n` such that `r a_i a_{i+1}` for all `i < n`

-/

variable {α : Type*} (r : Rel α α)

/--
Let `r` be a relation on `α`, a relation series of `r` of length `n` is a series
`a_0, a_1, ..., a_n` such that `r a_i a_{i+1}` for all `i < n`
-/
structure RelSeries where
  /-- The number of inequalities in the series -/
  length : ℕ
  /-- The underlying function of a relation series -/
  toFun : Fin (length + 1) → α
  /-- Adjacent elements are related -/
  step : ∀ (i : Fin length), r (toFun (Fin.castSucc i)) (toFun i.succ)

namespace RelSeries

instance : CoeFun (RelSeries r) (fun x ↦ Fin (x.length + 1) → α) :=
{ coe := RelSeries.toFun }

instance membership : Membership α (RelSeries r) :=
  ⟨fun x s => x ∈ Set.range s⟩

theorem mem_def {x : α} {s : RelSeries r} : x ∈ s ↔ x ∈ Set.range s :=
  Iff.rfl

/-- start of a series -/
def head (x : RelSeries r) : α := x 0
/-- end of a series -/
def last (x : RelSeries r) : α := x <| Fin.last _
lemma head_mem (x : RelSeries r) : x.head ∈ x := ⟨_, rfl⟩
lemma last_mem (x : RelSeries r) : x.last ∈ x := ⟨_, rfl⟩

/--
For any type `α`, each term of `α` gives a relation series with the right most index to be 0.
-/
@[simps!] def singleton (a : α) : RelSeries r where
  length := 0
  toFun _ := a
  step := Fin.elim0

instance [IsEmpty α] : IsEmpty (RelSeries r) where
  false x := IsEmpty.false (x 0)

instance [Inhabited α] : Inhabited (RelSeries r) where
  default := singleton r default

instance [Nonempty α] : Nonempty (RelSeries r) :=
  Nonempty.map (singleton r) inferInstance

variable {r}

@[ext]
lemma ext {x y : RelSeries r} (length_eq : x.length = y.length)
    (toFun_eq : x.toFun = y.toFun ∘ Fin.cast (by rw [length_eq])) : x = y := by
  rcases x with ⟨nx, fx⟩
  dsimp only at length_eq toFun_eq
  subst length_eq toFun_eq
  rfl

lemma rel_of_lt [IsTrans α r] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i < j) :
    r (x i) (x j) :=
  (Fin.liftFun_iff_succ r).mpr x.step h

lemma rel_or_eq_of_le [IsTrans α r] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i ≤ j) :
    r (x i) (x j) ∨ x i = x j :=
  h.lt_or_eq.imp (x.rel_of_lt ·) (by rw [·])

/--
Given two relations `r, s` on `α` such that `r ≤ s`, any relation series of `r` induces a relation
series of `s`
-/
@[simps!]
def ofLE (x : RelSeries r) {s : Rel α α} (h : r ≤ s) : RelSeries s where
  length := x.length
  toFun := x
  step _ := h _ _ <| x.step _

lemma coe_ofLE (x : RelSeries r) {s : Rel α α} (h : r ≤ s) :
    (x.ofLE h : _ → _) = x := rfl

/-- Every relation series gives a list -/
abbrev toList (x : RelSeries r) : List α := List.ofFn x

lemma length_toList (x : RelSeries r) : x.toList.length = x.length + 1 := by
  rw [List.length_ofFn]

lemma toList_chain' (x : RelSeries r) : x.toList.Chain' r := by
  rw [List.chain'_iff_get]
  intros i h
  have h' : i < x.length := by simpa [List.length_ofFn] using h
  convert x.step ⟨i, h'⟩ <;>
  · rw [List.get_ofFn]; congr 1

lemma toList_ne_empty (x : RelSeries r) : x.toList ≠ ∅ := fun m =>
  List.eq_nil_iff_forall_not_mem.mp m (x 0) <| (List.mem_ofFn _ _).mpr ⟨_, rfl⟩

lemma mem_toList {s : RelSeries r} {x : α} : x ∈ s.toList ↔ x ∈ s := by
  rw [List.mem_ofFn, mem_def]

theorem length_pos_of_mem_ne {s : RelSeries r} {x y : α} (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) : 0 < s.length := by
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  contrapose! hxy
  simp only [nonpos_iff_eq_zero] at hxy
  congr
  apply_fun Fin.castIso (by rw [hxy, zero_add] : s.length + 1 = 1)
  · exact Subsingleton.elim (α := Fin 1) _ _
  · exact OrderIso.injective _

theorem forall_mem_eq_of_length_eq_zero {s : RelSeries r} (hs : s.length = 0) {x y}
    (hx : x ∈ s) (hy : y ∈ s) : x = y := by
  rcases hx with ⟨i, rfl⟩
  rcases hy with ⟨j, rfl⟩
  congr
  apply_fun Fin.castIso (by rw [hs, zero_add] : s.length + 1 = 1)
  · exact Subsingleton.elim (α := Fin 1) _ _
  · exact OrderIso.injective _

/-- Every nonempty list satisfying the chain condition gives a relation series-/
@[simps]
def fromListChain' (x : List α) (x_ne_empty : x ≠ ∅) (hx : x.Chain' r) : RelSeries r where
  length := x.length.pred
  toFun := x.get ∘ Fin.cast (Nat.succ_pred_eq_of_pos <| List.length_pos.mpr x_ne_empty)
  step := fun i => List.chain'_iff_get.mp hx i i.2


/-- Relation series of `r` and nonempty list of `α` satisfying `r`-chain condition bijectively
corresponds to each other.-/
protected def Equiv : RelSeries r ≃ {x : List α | x ≠ [] ∧ x.Chain' r} where
  toFun x := ⟨_, x.toList_ne_empty, x.toList_chain'⟩
  invFun x := fromListChain' _ x.2.1 x.2.2
  left_inv x := ext (by simp) <| by ext; apply List.get_ofFn
  right_inv x := by
    refine Subtype.ext (List.ext_get ?_ <| fun n hn1 _ => List.get_ofFn _ _)
    simp [Nat.succ_pred_eq_of_pos <| List.length_pos.mpr x.2.1]

-- TODO : build a similar bijection between `RelSeries α` and `Quiver.Path`
end RelSeries

namespace Rel

/-- A relation `r` is said to be finite dimensional iff there is a relation series of `r` with the
  maximum length. -/
class FiniteDimensional : Prop where
  /-- A relation `r` is said to be finite dimensional iff there is a relation series of `r` with the
    maximum length. -/
  exists_longest_relSeries : ∃ (x : RelSeries r), ∀ (y : RelSeries r), y.length ≤ x.length

/-- A relation `r` is said to be infinite dimensional iff there exists relation series of arbitrary
  length. -/
class InfiniteDimensional : Prop where
  /-- A relation `r` is said to be infinite dimensional iff there exists relation series of
    arbitrary length. -/
  exists_relSeries_with_length : ∀ (n : ℕ), ∃ (x : RelSeries r), x.length = n

end Rel

namespace RelSeries

/-- The longest relational series when a relation is finite dimensional -/
protected noncomputable def longestOf [r.FiniteDimensional] : RelSeries r :=
  Rel.FiniteDimensional.exists_longest_relSeries.choose

lemma length_le_length_longestOf [r.FiniteDimensional] (x : RelSeries r) :
    x.length ≤ (RelSeries.longestOf r).length :=
  Rel.FiniteDimensional.exists_longest_relSeries.choose_spec _

/-- A relation series with length `n` if the relation is infinite dimensional -/
protected noncomputable def withLength [r.InfiniteDimensional] (n : ℕ) : RelSeries r :=
  (Rel.InfiniteDimensional.exists_relSeries_with_length n).choose

@[simp] lemma length_withLength [r.InfiniteDimensional] (n : ℕ) :
    (RelSeries.withLength r n).length = n :=
  (Rel.InfiniteDimensional.exists_relSeries_with_length n).choose_spec

/-- If a relation on `α` is infinite dimensional, then `α` is nonempty. -/
lemma nonempty_of_infiniteDimensional [r.InfiniteDimensional] : Nonempty α :=
  ⟨RelSeries.withLength r 0 0⟩

variable {r}

/--
If `a_0 --r-> a_1 --r-> ... --r-> a_n` and `b_0 --r-> b_1 --r-> ... --r-> b_m` are two strict series
such that `r a_n b_0`, then there is a chain of length `n + m + 1` given by
`a_0 --r-> a_1 --r-> ... --r-> a_n --r-> b_0 --r-> b_1 --r-> ... --r-> b_m`.
-/
@[simps]
def append (p q : RelSeries r) (connect : r p.last q.head) : RelSeries r where
  length := p.length + q.length + 1
  toFun := Fin.append p q ∘ Fin.cast (by ring)
  step := fun i => by
    obtain (hi|rfl|hi) :=
      lt_trichotomy i (Fin.castLE (by linarith) (Fin.last _ : Fin (p.length + 1)))
    · convert p.step ⟨i.1, hi⟩ <;>
      · convert Fin.append_left p q _
        rfl
    · convert connect
      convert Fin.append_left p q _
      · rfl
      · convert Fin.append_right p q _
        rfl
    · set x := _; set y := _
      change r (Fin.append p q x) (Fin.append p q y)
      have hx : x = Fin.natAdd _ ⟨i - (p.length + 1), Nat.sub_lt_left_of_lt_add hi <|
        i.2.trans <| by linarith⟩
      · ext
        change _ = _ + (_ - _)
        rw [Nat.add_sub_cancel']
        dsimp
        exact hi
      have hy : y = Fin.natAdd _ ⟨i - p.length,
        by
          apply Nat.sub_lt_left_of_lt_add (le_of_lt hi)
          exact i.2⟩
      · ext
        change _ = _ + (_ - _)
        conv_rhs => rw [Nat.add_comm p.length 1, add_assoc]
        rw [Nat.add_sub_cancel']
        swap; exact le_of_lt hi
        conv_rhs => rw [add_comm]
      rw [hx, Fin.append_right, hy, Fin.append_right]
      convert q.step _
      pick_goal 3
      · refine ⟨i - (p.length + 1), ?_⟩
        apply Nat.sub_lt_left_of_lt_add hi
        convert i.2 using 1
        dsimp
        rw [Nat.succ_eq_add_one]
        ring
      · rfl
      · dsimp
        rw [Nat.sub_eq_iff_eq_add (le_of_lt hi : p.length ≤ i),
          Nat.add_assoc _ 1, add_comm 1, Nat.sub_add_cancel]
        exact hi

/--
If `a_0 --r-> a_1 --r-> ... --r-> a_n` is an `r`-series and `a` is such that
`a_i --r-> a --r-> a_{i + 1}`, then
`a_0 --r-> a_1 --r-> ... --r-> a_i --r-> a --r-> a_{i + 1} --r-> ... --r-> a_n`
is another `r`-series
-/
@[simps]
def insertNth (p : RelSeries r) (i : Fin p.length) (a : α)
    (prev_connect : r (p (Fin.castSucc i)) a) (connect_next : r a (p i.succ)) : RelSeries r where
  length := p.length + 1
  toFun :=  (Fin.castSucc i.succ).insertNth a p
  step := fun m => by
    set x := _; set y := _
    change r x y
    obtain (hm|hm|hm) := lt_trichotomy m.1 i.1
    · have hx : x = p m
      · change Fin.insertNth _ _ _ _ = _
        rw [Fin.insertNth_apply_below]
        swap; exact hm.trans (lt_add_one _)
        simp only [Fin.castLT_castSucc, eq_rec_constant]
      convert p.step ⟨m, hm.trans i.2⟩
      change Fin.insertNth _ _ _ _ = _
      rw [Fin.insertNth_apply_below]
      simp only [eq_rec_constant]
      congr
      change m.1 + 1 < i.1 + 1
      simpa only [add_lt_add_iff_right]
    · have hx : x = p m
      · change Fin.insertNth _ _ _ _ = _
        rw [Fin.insertNth_apply_below]
        swap
        · change m.1 < i.1 + 1
          rw [hm]
          exact lt_add_one _
        simp only [Fin.castLT_castSucc, eq_rec_constant]
      rw [hx]
      convert prev_connect
      · ext; exact hm
      · change Fin.insertNth _ _ _ _ = _
        have H : m.succ = i.succ.castSucc
        · ext; change _ + 1 = _ + 1; rw [hm]
        rw [H, Fin.insertNth_apply_same]
    · rw [Nat.lt_iff_add_one_le, le_iff_lt_or_eq] at hm
      obtain (hm|hm) := hm
      · have hx : x = p ⟨m.1 - 1, (Nat.sub_lt (by linarith) (by linarith)).trans m.2⟩
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above]
          swap; exact hm
          simp only [eq_rec_constant]
          congr
        have hy : y = p m
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above]
          swap; exact hm.trans (lt_add_one _)
          simp only [Fin.pred_succ, eq_rec_constant]
        rw [hy]
        convert p.step ⟨m.1 - 1, Nat.sub_lt_right_of_lt_add (by linarith) m.2⟩
        ext
        symm
        exact Nat.succ_pred_eq_of_pos (lt_trans (Nat.zero_lt_succ _) hm)
      · have hx : x = a
        · change Fin.insertNth _ _ _ _ = _
          have H : m.castSucc = i.succ.castSucc
          · ext; change m.1 = i.1 + 1; rw [hm]
          rw [H, Fin.insertNth_apply_same]
        have hy : y = p m
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above]
          swap; change i.1 + 1 < m.1 + 1; rw [hm]; exact lt_add_one _
          simp only [Fin.pred_succ, eq_rec_constant]
        rw [hy]
        convert connect_next
        ext
        exact hm.symm

variable {β} (s : Rel β β)

/--
For two sets `α, β` and relation on them `r, s`, if `f : α → β` preserves relation `r`, then an
`r`-series can be pushed out to an `s`-series by
`a₀ --r-> a₁ --r-> ... --r-> aₙ ↦ f a₀ --s-> f a₁ --s-> ... --s-> f aₙ`
-/
@[simps]
def map (p : RelSeries r) (f : α → β) (map : ∀ ⦃x y : α⦄, r x y → s (f x) (f y)) : RelSeries s where
  length := p.length
  toFun := f.comp p
  step := (map <| p.step .)

/--
A strict series `a_0 --r-> a_1 --r-> ... --r-> a_n` in `α` gives a strict series in `αᵒᵈ` by
reversing the series `a_n <-r-- a_{n - 1} <-r-- ... <-r-- a_1 <-r-- a_0`.
-/
def rev (p : RelSeries r) : RelSeries (fun (a b : α) => r b a) where
  length := p.length
  toFun := p ∘ Fin.rev
    -- p ∘ (Sub.sub ⟨p.length, lt_add_one _⟩)
  step := fun i => by
    rw [Function.comp_apply, Function.comp_apply]
    have hi : i.1 + 1 ≤ p.length
    · linarith [i.2]
    convert p.step ⟨p.length - (i.1 + 1), _⟩
    · ext
      simp only [Fin.val_rev, Fin.val_succ, Nat.succ_sub_succ_eq_sub, Fin.coe_castSucc]
    · ext
      simp only [Fin.val_rev, Fin.coe_castSucc, Nat.succ_sub_succ_eq_sub, Fin.val_succ]
      rw [Nat.sub_eq_iff_eq_add, add_assoc, add_comm 1 i.1, Nat.sub_add_cancel]
      · assumption
      · linarith
    exact Nat.sub_lt_self (by linarith) hi

/--
given a series `a_0 --r-> a_1 --r-> ... --r-> a_n` and an `a` such that `r a_0 a` holds, there is
a series of length `n+1`: `a --r-> a_0 --r-> a_1 --r-> ... --r-> a_n`.
-/
@[simps!]
def cons (p : RelSeries r) (a : α) (rel : r a (p 0)) : RelSeries r :=
  (singleton r a).append p rel

lemma cons_zero (p : RelSeries r) (a : α) (rel : r a (p 0)) : p.cons a rel 0 = a := by
  rw [cons_toFun]
  exact Fin.append_left _ _ 0

lemma cons_succ (p : RelSeries r) (a : α) (rel : r a (p 0)) (x) :
    p.cons a rel x.succ = p x := by
  rw [cons_toFun]
  convert Fin.append_right _ _ _
  ext
  simp only [Fin.val_succ, Fin.coe_natAdd]
  rw [add_comm 1 x.1]
  change _ % _ = _
  simp only [cons_length, Nat.mod_succ_eq_iff_lt]
  linarith [x.2]
/--
given a series `a_0 --r-> a_1 --r-> ... --r-> a_n` and an `a` such that `r a_n a`, there is a series
of length `n+1`: `a_0 --r-> a_1 --r-> ... --r-> a_n --r-> a`.
-/
@[simps!]
def snoc (p : RelSeries r) (a : α) (rel : r (p (Fin.last _)) a) : RelSeries r :=
p.append (singleton r a) rel

lemma snoc_last (p : RelSeries r) (a : α) (rel : r (p (Fin.last _)) a) :
    p.snoc a rel (Fin.last _) = a := by
  rw [snoc_toFun]
  exact Fin.append_right _ _ 0

lemma snoc_castSucc (s : RelSeries r) (a : α) (connect : r s.last a)
    (i : Fin (s.length + 1)) : snoc s a connect (Fin.castSucc i) = s i := by
  unfold snoc
  simp only [append_toFun]
  exact Fin.append_left _ _ i

lemma head_snoc (s : RelSeries r) (a : α) (connect : r s.last a) :
    (snoc s a connect).head = s.head := by
  unfold snoc head
  simp only [append_toFun]
  exact Fin.append_left _ _ 0

theorem mem_snoc {s : RelSeries r} {x y : α} (connect : r s.last x) :
    y ∈ snoc s x connect ↔ y ∈ s ∨ y = x := by
  simp only [snoc]
  constructor
  · rintro ⟨i, rfl⟩
    refine' Fin.lastCases _ (fun i => _) i
    · right
      simp only [append_toFun]
      convert Fin.append_right _ _ 0
    · left
      simp only [append_toFun]
      refine ⟨⟨i.1, ?_⟩, ?_⟩
      · exact i.2
      convert (Fin.append_left _ _ _).symm
  · intro h
    rcases h with (⟨i, rfl⟩ | rfl)
    · use Fin.castSucc i
      simp only [append_toFun]
      convert Fin.append_left _ _ _
    · use Fin.last _
      simp only [append_toFun]
      convert Fin.append_right _ _ 0

/--
If a series `a_0 --r-> a_1 --r-> ...` has positive length, then `a_1 --r-> ...` is another series
-/
@[simps]
def tail (p : RelSeries r) (h : p.length ≠ 0) : RelSeries r where
  length := p.length.pred
  toFun := fun j ↦ p ⟨j + 1, Nat.succ_lt_succ (by
    have hj := j.2
    conv_rhs at hj =>
      rw [← Nat.succ_eq_add_one, Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero h)]
    exact hj)⟩
  step := fun i => p.step ⟨i.1 + 1, Nat.lt_pred_iff.mp i.2⟩

lemma tail_zero (p : RelSeries r) (h : p.length ≠ 0) : p.tail h 0 = p 1 := by
  rw [tail_toFun]
  congr
  change (0 : ℕ) % (p.length.pred + 1) + 1 = 1 % (p.length + 1)
  rw [Nat.zero_mod, Nat.mod_eq_of_lt]
  rw [lt_add_iff_pos_left]
  exact Nat.pos_of_ne_zero h

/--
If a series `a_0 --r-> a_1 --r-> ... a_n` has positive length, then `a_0 --r-> ... a_{n-1}` is
another series -/
@[simps]
def eraseLast (p : RelSeries r) : RelSeries r where
  length := p.length - 1
  toFun i := p ⟨i, lt_of_lt_of_le i.2 (Nat.succ_le_succ tsub_le_self)⟩
  step i := by
    have := p.step ⟨i, lt_of_lt_of_le i.2 tsub_le_self⟩
    cases i
    exact this

@[elab_as_elim]
lemma snoc_induction {motive : (x : RelSeries r) → Prop}
    (x : RelSeries r)
    (single : ∀ (a : α), motive (singleton r a))
    (snoc : ∀ (x : RelSeries r) (a : α) (ha : r x.last a), motive x → motive (x.snoc a ha)) :
    motive x := by
  induction' hn : x.length with n ih generalizing x
  · have x_eq : x = singleton r (x 0)
    · ext i
      · exact hn
      · simp only [singleton_length, Function.comp_apply, singleton_toFun]
        congr
        ext
        have hi := i.2
        simp_rw [hn] at hi
        simpa using hi
    rw [x_eq]
    apply single
  · have x_eq : x = x.eraseLast.snoc x.last (by
      simp only [eraseLast_length, eraseLast_toFun, Fin.val_last]
      convert x.step ⟨x.length - 1, Nat.pred_lt (show x.length ≠ 0 by rw [hn]; norm_num)⟩
      delta last; congr; ext
      simpa using Nat.succ_pred_eq_of_pos (by rw [hn]; norm_num) |>.symm)
    · ext i
      · simpa using Nat.succ_pred_eq_of_pos (by rw [hn]; norm_num) |>.symm
      · rw [Function.comp_apply]
        generalize_proofs h1 h2
        by_cases ineq1 : i = Fin.last _
        · subst ineq1
          have eq1 : Fin.cast h2 (Fin.last _) = Fin.last _
          · ext; simp
          erw [eq1, snoc_last]
          rfl
        have eq1 : Fin.cast h2 i = Fin.castSucc ⟨i.1, by
          simp only [snoc_length, eraseLast_length]
          rw [show x.length - 1 + 1 = x.length from
            @Nat.succ_pred_eq_of_ne_zero x.length (by rw [hn]; norm_num)]
          change i < ⊤
          rw [lt_top_iff_ne_top]
          exact ineq1⟩
        · ext; rfl
        rw [eq1, RelSeries.snoc_toFun]
        erw [Fin.append_left]
        rfl
    rw [x_eq]
    exact snoc _ _ _ (ih _ <| by simp [hn])

@[simp] lemma last_eraseLast (p : RelSeries r) :
    p.eraseLast.last = p ⟨p.length - 1, lt_of_le_of_lt tsub_le_self (Nat.lt_succ_self _)⟩ :=
  show p _ = p _ from congr_arg p <| by ext; simp

lemma rel_last_eraseLast_last_of_pos_length (p : RelSeries r) (h : 0 < p.length) :
    r p.eraseLast.last p.last := by
  convert p.step ⟨p.length - 1, Nat.pred_lt (n := p.length) <| by linarith⟩
  delta last
  congr
  ext
  exact (Nat.succ_pred_eq_of_pos h).symm

theorem mem_eraseLast_of_ne_of_mem {s : RelSeries r} {x : α} (hx : x ≠ s.last) (hxs : x ∈ s) :
    x ∈ s.eraseLast := by
  rcases hxs with ⟨i, rfl⟩
  refine ⟨i, ?_⟩
  dsimp
  congr
  by_cases H : s.length = 0
  · simp only [Nat.mod_succ_eq_iff_lt]
    have H' := i.2
    simp_rw [H] at H'
    linarith
  · have H' : s.length - 1 + 1 = s.length
    · exact Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero H)
    simp_rw [H']
    rw [Nat.mod_eq_of_lt]
    have H'' := i.2
    rw [Nat.lt_succ_iff, le_iff_lt_or_eq] at H''
    refine H''.elim id <| fun h => (False.elim <| hx ?_)
    congr
    ext
    exact h

/--
Give two series `a₀ --r-> ... --r-> X` and `X --r-> b ---> ...` can be combined together to form
`a₀ --r-> ... --r-> x --r-> b ...`
-/
@[simps]
def combine (p q : RelSeries r) (connect : p.last = q.head) : RelSeries r where
  length := p.length + q.length
  toFun := fun i =>
    if H : i.1 < p.length
    then p ⟨i.1, H.trans (lt_add_one _)⟩
    else q ⟨i.1 - p.length, by
      apply Nat.sub_lt_left_of_lt_add
      · rwa [not_lt] at H
      · rw [← add_assoc]; exact i.2⟩
  step := fun i => by
    dsimp only []
    by_cases h₂ : i.1 + 1 < p.length
    · have h₁ : i.1 < p.length := lt_trans (lt_add_one _) h₂
      erw [dif_pos h₁, dif_pos h₂]
      convert p.step ⟨i, h₁⟩ using 1
    · erw [dif_neg h₂]
      by_cases h₁ : i.1 < p.length
      · erw [dif_pos h₁]
        have h₃ : p.length = i.1 + 1
        · linarith
        convert p.step ⟨i, h₁⟩ using 1
        convert connect.symm
        · congr
          simp only [Nat.zero_mod, tsub_eq_zero_iff_le]
          simp_rw [h₃]
          rfl
        · congr
          ext
          exact h₃.symm
      · erw [dif_neg h₁]
        convert q.step ⟨i.1 - p.length, _⟩ using 1
        · congr
          change (i.1 + 1) - _ = _
          rw [Nat.sub_add_comm]
          rw [not_lt] at h₁
          exact h₁
        · refine Nat.sub_lt_left_of_lt_add ?_ i.2
          rw [not_lt] at h₁
          exact h₁

lemma combine_castAdd {p q : RelSeries r} (connect : p.last = q.head) (i : Fin p.length) :
    p.combine q connect (Fin.castSucc <| Fin.castAdd q.length i) = p (Fin.castSucc i) := by
  unfold combine
  dsimp
  rw [dif_pos i.2]
  rfl

lemma combine_succ_castAdd {s₁ s₂ : RelSeries r} (h : s₁.last = s₂.head)
    (i : Fin s₁.length) : combine s₁ s₂ h (Fin.castAdd s₂.length i).succ = s₁ i.succ := by
  rw [combine_toFun]
  split_ifs with H
  · congr
  · simp only [Fin.val_succ, Fin.coe_castAdd] at H
    convert h.symm
    · congr
      simp only [Fin.val_succ, Fin.coe_castAdd, Nat.zero_mod, tsub_eq_zero_iff_le]
      linarith [i.2]
    · congr
      ext
      change i.1 + 1 = s₁.length
      linarith [i.2]

lemma combine_natAdd {s₁ s₂ : RelSeries r} (h : s₁.last = s₂.head) (i : Fin s₂.length) :
    combine s₁ s₂ h (Fin.castSucc <| Fin.natAdd s₁.length i) = s₂ (Fin.castSucc i) := by
  rw [combine_toFun]
  split_ifs with H
  · simp only [Fin.coe_castSucc, Fin.coe_natAdd, add_lt_iff_neg_left, not_lt_zero'] at H
  · congr
    exact Nat.add_sub_self_left _ _

lemma combine_succ_natAdd {s₁ s₂ : RelSeries r} (h : s₁.last = s₂.head) (i : Fin s₂.length) :
    combine s₁ s₂ h (Fin.natAdd s₁.length i).succ = s₂ i.succ := by
  rw [combine_toFun]
  split_ifs with H
  · have H' : s₁.length < s₁.length + (i.1 + 1)
    · linarith
    exact (lt_irrefl _ (H.trans H')).elim
  · congr
    simp only [Fin.val_succ, Fin.coe_natAdd]
    rw [add_assoc, Nat.add_sub_cancel_left]

@[simp] lemma combine_head {s₁ s₂ : RelSeries r} (h : s₁.last = s₂.head) :
    (combine s₁ s₂ h).head = s₁.head := by
  delta combine head
  simp only [Fin.val_zero, Fin.zero_eta, ge_iff_le, zero_le, tsub_eq_zero_of_le, dite_eq_ite,
    ite_eq_left_iff, not_lt, nonpos_iff_eq_zero]
  intro H; symm; convert h
  congr
  rw [H]
  rfl

@[simp] lemma combine_last {s₁ s₂ : RelSeries r} (h : s₁.last = s₂.head) :
    (combine s₁ s₂ h).last = s₂.last := by
  delta combine last
  simp only [Fin.val_last, add_lt_iff_neg_left, not_lt_zero', add_tsub_cancel_left, dite_false]
  congr

variable (r)
lemma exists_len_gt_of_infiniteDimensional [r.InfiniteDimensional] (n : ℕ) :
    ∃ (p : RelSeries r), n < p.length :=
  ⟨RelSeries.withLength r (n + 1), RelSeries.length_withLength r _ ▸ lt_add_one _⟩

end RelSeries

/-- A type is finite dimensional if its `LTSeries` has bounded length. -/
abbrev FiniteDimensionalOrder (γ : Type*) [Preorder γ] :=
  Rel.FiniteDimensional ((. < .) : γ → γ → Prop)

/-- A type is infinite dimensional if it has `LTSeries` of at least arbitrary length -/
abbrev InfiniteDimensionalOrder (γ : Type*) [Preorder γ] :=
  Rel.InfiniteDimensional ((. < .) : γ → γ → Prop)

section LTSeries

variable (α β) [Preorder α] [Preorder β]
/--
If `α` is a preorder, a LTSeries is a relation series of the less than relation.
-/
abbrev LTSeries := RelSeries ((. < .) : Rel α α)

namespace LTSeries

/-- The longest `<`-series when a type is finite dimensional -/
protected noncomputable def longestOf [FiniteDimensionalOrder α] : LTSeries α :=
  RelSeries.longestOf _

/-- A `<`-series with length `n` if the relation is infinite dimensional -/
protected noncomputable def withLength [InfiniteDimensionalOrder α] (n : ℕ) : LTSeries α :=
  RelSeries.withLength _ n

@[simp] lemma length_withLength [InfiniteDimensionalOrder α] (n : ℕ) :
    (LTSeries.withLength α n).length = n :=
  RelSeries.length_withLength _ _

/-- if `α` is infinite dimensional, then `α` is nonempty. -/
lemma nonempty_of_infiniteDimensionalOrder [InfiniteDimensionalOrder α] : Nonempty α :=
  ⟨LTSeries.withLength α 0 0⟩

variable {α}

lemma longestOf_is_longest [FiniteDimensionalOrder α] (x : LTSeries α) :
    x.length ≤ (LTSeries.longestOf α).length :=
  RelSeries.length_le_length_longestOf _ _

lemma longestOf_len_unique [FiniteDimensionalOrder α] (p : LTSeries α)
    (is_longest : ∀ (q : LTSeries α), q.length ≤ p.length) :
    p.length = (LTSeries.longestOf α).length :=
  le_antisymm (longestOf_is_longest _) (is_longest _)

lemma longestOf_is_compositionSeries [FiniteDimensionalOrder α]
    (i : Fin (LTSeries.longestOf α).length) :
    LTSeries.longestOf α i.castSucc ⋖ LTSeries.longestOf α i.succ := by
  refine ⟨(LTSeries.longestOf α).step i, ?_⟩
  by_contra! rid
  obtain ⟨a, ha1, ha2⟩ := rid
  let x := RelSeries.insertNth (LTSeries.longestOf α) i a ha1 ha2
  have := LTSeries.longestOf_is_longest x
  simp only [RelSeries.insertNth_length, add_le_iff_nonpos_right, nonpos_iff_eq_zero] at this

variable {β}

instance [Unique β] : Unique (LTSeries β) where
  default := RelSeries.singleton _ default
  uniq := λ x ↦ by
    have h : x.length = 0
    · rcases (lt_trichotomy x.length 0) with (h|h|h)
      · linarith
      · exact h
      · exact (ne_of_lt (x.step ⟨0, h⟩) <| Subsingleton.allEq _ _).elim
    exact RelSeries.ext h <| funext λ b ↦ Subsingleton.allEq _ _

instance [Unique β] : FiniteDimensionalOrder β :=
⟨default, fun y => le_of_eq <| show _ = 0 by
  by_contra h
  exact ne_of_lt (y.step ⟨0, Nat.pos_iff_ne_zero.mpr h⟩) <| Subsingleton.elim _ _⟩

/-- an alternative constructor of `LTSeries` using `StrictMono` functions. -/
def mk (length : ℕ) (toFun : Fin (length + 1) → α) (strictMono : StrictMono toFun) : LTSeries α :=
{ toFun := toFun
  step := fun i => strictMono <| lt_add_one i.1 }

lemma strictMono (x : LTSeries α) : StrictMono x :=
  fun _ _ h => x.rel_of_lt h

lemma monotone (x : LTSeries α) : Monotone x :=
  x.strictMono.monotone

/--
For two pre-ordered sets `α, β`, if `f : α → β` is strictly monotonic, then a strict chain of `α`
can be pushed out to a strict chain of `β` by
`a₀ < a₁ < ... < aₙ ↦ f a₀ < f a₁ < ... < f aₙ`
-/
@[simps!]
def map (p : LTSeries α) (f : α → β) (hf : StrictMono f) : LTSeries β :=
  LTSeries.mk p.length (f.comp p) (hf.comp p.strictMono)

/--
For two pre-ordered sets `α, β`, if `f : α → β` is surjective and strictly comonotonic, then a
strict series of `β` can be pulled back to a strict chain of `α` by
`b₀ < b₁ < ... < bₙ ↦ f⁻¹ b₀ < f⁻¹ b₁ < ... < f⁻¹ bₙ` where `f⁻¹ bᵢ` is an arbitrary element in the
preimage of `f⁻¹ {bᵢ}`.
-/
@[simps!]
noncomputable def comap (p : LTSeries β) (f : α → β)
  (hf1 : ∀ ⦃x y⦄, f x < f y → x < y)
  (hf2 : Function.Surjective f) :
  LTSeries α := mk p.length (fun i ↦ (hf2 (p i)).choose)
    (fun i j h ↦ hf1 (by simpa only [(hf2 _).choose_spec] using p.strictMono h))

lemma exists_len_gt_of_noTopOrder [InfiniteDimensionalOrder α] (n : ℕ) :
    ∃ (p : LTSeries α), n < p.length :=
  RelSeries.exists_len_gt_of_infiniteDimensional _ n

end LTSeries
