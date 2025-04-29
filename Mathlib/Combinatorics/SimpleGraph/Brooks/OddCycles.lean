/-
Copyright (c) 2025 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import Mathlib.Combinatorics.SimpleGraph.Finsubgraph
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings

/-!
We extend some of the walk decomposition API : we already have `Walk.takeUntil` and `Walk.dropUntil`
which satisfy `(w.takeUntil _ hx) ++ (w.dropUntil _ hx) = w`, where `w.takeUntil _ hx` is the part
of `w` from its start to the first occurence of `x` (given `hx : x ∈ w.support`).

We define two new walks `Walk.shortCut` and `Walk.shortClosed` where `w.shortCut hx` is the walk
that travels along `w` from `u` to `x` and then back to `v` without revisiting `x` and
`w.shortClosed hx` is the closed walk that travels along `w` from the first visit of `x` to the last
 visit.

We use these to construct an odd cycle from an odd length closed walk.

[More generally we could define the `w.CyclesAndPaths` (of a walk `w : G.Walk u v`)
to be a list of walks that when appended give `w` while each is either a cycle or
path.]
-/

namespace SimpleGraph
open Walk List
variable {α : Type*} {u v x: α}  {G : SimpleGraph α}

lemma Walk.IsPath.length_one_of_end_start_mem_edges {u v : α} {w : G.Walk u v}
    (hp : w.IsPath) (h1 : s(v, u) ∈ w.edges) : w.length = 1 := by
  cases w with
  | nil => simp at h1
  | cons h p =>
    cases p with
    | nil => simp
    | cons h' p =>
      exfalso
      simp_all only [cons_isPath_iff, edges_cons, mem_cons, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
        Prod.swap_prod_mk, and_true, support_cons, not_or, and_false, false_or, or_false]
      obtain ( rfl | ⟨rfl, rfl⟩ | hf) := h1
      · apply hp.1.2 p.end_mem_support
      · apply hp.2.2 p.start_mem_support
      · apply hp.2.2 (p.snd_mem_support_of_mem_edges hf)

/--
If `w : G.Walk u u` is a closed walk and `w.support.tail.Nodup` then it is almost a cycle, in
the sense that is either a cycle or nil or has length 2.
-/
lemma Walk.isCycle_or_nil_or_length_two_of_support_tail_nodup {u : α} (w : G.Walk u u)
    (hn : w.support.tail.Nodup) : w.IsCycle ∨ w.Nil ∨ w.length = 2 := by
  by_cases hnc : w.IsCycle
  · exact Or.inl hnc
  right
  contrapose! hnc
  rw [isCycle_def]
  refine ⟨?_, fun hf ↦ hnc.1 <| nil_iff_eq_nil.mpr hf, hn⟩
  apply IsTrail.mk
  cases w with
  | nil => simp
  | @cons _ b _ h w =>
    have : s(u, b) ∉ w.edges := by
      intro hf
      apply hnc.2
      simp only [support_cons, List.tail_cons] at hn
      simpa using (IsPath.mk' hn).length_one_of_end_start_mem_edges hf
    cases w with
    | nil => simp
    | cons h w =>
      rw [support_cons, List.tail_cons] at hn
      rw [edges_cons]
      apply nodup_cons.2 ⟨?_, edges_nodup_of_support_nodup hn⟩
      intro hf
      aesop

lemma Walk.isCycle_odd_support_tail_nodup {u : α} (w : G.Walk u u) (hn : w.support.tail.Nodup)
    (ho : Odd w.length) : w.IsCycle := by
  apply (w.isCycle_or_nil_or_length_two_of_support_tail_nodup hn).resolve_right
  rintro (hf | hf)
  · rw [nil_iff_length_eq.mp hf] at ho
    exact (Nat.not_odd_zero ho).elim
  · rw [hf] at ho
    exact (Nat.not_odd_iff_even.2 (by decide) ho).elim

variable [DecidableEq α]

lemma Walk.support_tail_nodup_iff_count_le {u : α} (w : G.Walk u u) : w.support.tail.Nodup ↔
    w.support.count u ≤ 2 ∧ ∀ x ∈ w.support, x ≠ u → count x w.support ≤ 1 := by
  rw [List.nodup_iff_count_le_one]
  constructor
  · intro h
    constructor
    · have := h u
      rw [List.count_tail (by simp)] at this
      simpa using this
    · intro x _ h'
      have := h x
      rw [List.count_tail (by simp)] at this
      simpa [head_support, beq_iff_eq, tsub_le_iff_right, if_neg (Ne.symm h')] using this
  · intro ⟨_, h1⟩ a
    by_cases ha : a ∈ w.support
    · rw [count_tail (by simp)]
      by_cases ha' : a = u
      · subst a
        simpa
      · have :=  h1 _ ha ha'
        omega
    · rw [count_eq_zero_of_not_mem (fun hf ↦ ha (mem_of_mem_tail hf))]
      omega

/-- Given a vertex `x` in a walk `w : G.Walk u v` form the walk that travels along `w` from `u`
to `x` and then back to `v` without revisiting `x` -/
abbrev Walk.shortCut (w : G.Walk u v) (hx : x ∈ w.support) : G.Walk u v :=
  (w.takeUntil _ hx).append (w.reverse.takeUntil _ (w.mem_support_reverse.2 hx)).reverse

-- TODO change this definition to w.drop.rev.drop.rev (drop_rev_comm says they are the same)
/-- Given a vertex `x` in a walk `w` form the walk that travels along `w` from the first visit of
`x` to the last visit of `x` (which may be the same in which case this is `nil' x`) -/
abbrev Walk.shortClosed (w : G.Walk u v) (hx : x ∈ w.support) : G.Walk x x :=
  (w.reverse.dropUntil _ (w.mem_support_reverse.2 hx)).reverse.dropUntil _ (by simp)

@[simp]
lemma Walk.shortCut_start (w : G.Walk u v) : w.shortCut w.start_mem_support =
    (w.reverse.takeUntil _ (w.mem_support_reverse.2 (by simp))).reverse:= by
  cases w <;> simp [shortCut];

@[simp]
lemma Walk.mem_support_shortCut (w : G.Walk u v) (hx : x ∈ w.support) :
    x ∈ (w.shortCut hx).support := by
  simp [shortCut]

@[simp]
lemma Walk.shortClosed_start (w : G.Walk u v) : (w.shortClosed (w.start_mem_support)) =
    (w.reverse.dropUntil _ (by simp)).reverse := by
  cases w <;> simp [shortClosed]

@[simp]
lemma Walk.shortClosed_of_eq {y: α} (w : G.Walk u v) (hx : x ∈ w.support) (hy : y ∈ w.support)
    (h : y = x) : w.shortClosed hx = (w.shortClosed hy).copy h h := by
  subst h
  rfl

lemma Walk.shortCut_not_nil (w : G.Walk u v) (hx : x ∈ w.support) (hu : x ≠ u) :
    ¬(w.shortCut hx).Nil := by
  rw [shortCut]
  simp only [nil_append_iff, nil_takeUntil, nil_reverse, not_and]
  rintro rfl; contradiction

@[simp]
lemma Walk.dropUntil_reverse_comm (w : G.Walk u v) (hx : x ∈ w.support) :
  ((w.dropUntil _ hx).reverse.dropUntil _ (by simp)).reverse =
  (((w.reverse.dropUntil _ (w.mem_support_reverse.2 hx)).reverse.dropUntil _ (by simp))):= by
  by_cases hu : x = u
  · subst x; simp
  induction w with
  | nil => rw [mem_support_nil_iff] at hx; exact (hu hx).elim
  | @cons _ b _ _ p ih =>
    simp_rw [reverse_cons]
    rw [dropUntil_cons_ne_start hx hu]
    rw [support_cons, List.mem_cons] at hx
    cases hx with
  | inl hx => contradiction
  | inr hx =>
    simp_rw [dropUntil_append_of_mem_left _ _ ((p.mem_support_reverse.2 hx)), reverse_append]
    by_cases hb : x = b
    · subst b
      simp [hu]
    · simpa [hu, hb] using ih _ hb

lemma Walk.shortClosed_reverse (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.reverse.shortClosed ((w.mem_support_reverse.2 hx))).reverse = w.shortClosed hx := by
  simp

@[simp]
lemma Walk.dropUntil_spec (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.shortClosed hx).append (w.reverse.takeUntil x (w.mem_support_reverse.2 hx)).reverse =
    w.dropUntil x hx := by
  have hc := congr_arg Walk.reverse <| take_spec (w.dropUntil _ hx).reverse (end_mem_support _)
  rw [Walk.reverse_reverse, ← hc, Walk.reverse_append] at *
  symm
  congr! 1
  · exact w.dropUntil_reverse_comm hx
  · congr! 1
    conv_rhs =>
      enter [1]
      rw [← take_spec w hx, Walk.reverse_append]
    rw [takeUntil_append_of_mem_left]

/-- w.shortCut1 ++ w.shortClosed ++ w.shortCut2 = w -/
lemma Walk.take_shortClosed_reverse_spec (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.takeUntil _ hx).append ((w.shortClosed hx).append
      (w.reverse.takeUntil _ (w.mem_support_reverse.2 hx)).reverse) = w := by
  conv_rhs =>
    rw [← take_spec w hx]
  rw [w.dropUntil_spec hx]

lemma Walk.count_reverse {y : α} (w : G.Walk u v) :
    w.reverse.support.count y = w.support.count y := by
  simp

lemma Walk.takeUntil_count_le {y : α} (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.takeUntil _ hx).support.count y ≤ w.support.count y := by
  conv_rhs =>
    rw [← take_spec w hx]
  rw [support_append, count_append]
  omega

@[simp]
lemma Walk.dropUntil_count_le {y : α} (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.dropUntil _ hx).support.count y ≤ w.support.count y := by
  conv_rhs =>
    rw [← take_spec w hx]
  rw [support_append, count_append, count_tail (by simp)]
  by_cases hy : x = y
  · simp only [head_support, hy, beq_self_eq_true, ↓reduceIte]
    subst y
    rw [w.count_support_takeUntil_eq_one hx]
    omega
  · simp [hy]

lemma Walk.shortClosed_count_le {y : α} (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.shortClosed hx).support.count y ≤ w.support.count y := by
  by_cases hu : x = u
  · subst x; rw [shortClosed_start, support_reverse, ← w.count_reverse]
    rw [List.count_reverse]
    apply w.reverse.dropUntil_count_le
  · conv_rhs =>
      rw [← w.take_shortClosed_reverse_spec hx]
    simp_rw [support_append, count_append]
    by_cases hy : x = y
    · rw [List.count_tail (by simp)]
      subst y
      rw [w.count_support_takeUntil_eq_one hx]
      simp
      omega
    · rw [List.count_tail (by simp), add_comm]
      simp [hy, add_assoc]

/-- If `w.count u ≤ 2` and `x ≠ u` then `u ∉ w.shortClosed x` -/
lemma Walk.shortClosed_count_le_two {u x : α} (w : G.Walk u u) (hx : x ∈ w.support) (hne : x ≠ u)
  (h2 : w.support.count u ≤ 2) : u ∉ (w.shortClosed hx).support := by
  intro hf
  have := congr_arg Walk.support <| w.take_shortClosed_reverse_spec hx
  apply_fun List.count u at this
  rw [← this] at h2
  simp_rw [support_append, count_append] at h2
  simp at h2
  rw [List.count_tail (by simp)] at h2
  simp [hne] at h2
  rw [← List.reverse_reverse (w.reverse.takeUntil _ (by simp [hx])).support] at h2
  rw [List.dropLast_reverse, List.count_reverse] at h2
  rw [List.count_tail (by simp)] at h2
  simp [hne] at h2
  rw [← List.count_pos_iff] at hf
  have h1 : 0 < count u (w.takeUntil _ hx).support :=
    List.count_pos_iff.2 (start_mem_support ..)
  have h3 : 0 < count u (w.reverse.takeUntil x (by simp [hx])).support :=
    List.count_pos_iff.2 (start_mem_support ..)
  omega

lemma Walk.shortCut_count_le {y : α} (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.shortCut hx).support.count y ≤ w.support.count y := by
  rw [shortCut]
  conv_rhs =>
    rw [← w.take_shortClosed_reverse_spec hx]
  simp_rw [support_append, count_append]
  gcongr
  rw [List.count_tail (by simp), List.count_tail (by simp)]
  by_cases hy : x = y
  · subst y
    simp
  · simp only [support_reverse, List.count_reverse, head_reverse, getLast_support, beq_iff_eq,
    hy, ↓reduceIte, tsub_zero, tail_reverse, count_append, ne_eq, support_ne_nil,
    not_false_eq_true, head_append_of_ne_nil, head_support]
    rw [← List.reverse_reverse (w.reverse.takeUntil _ (by simp [hx])).support]
    rw [List.dropLast_reverse, List.reverse_reverse, List.count_reverse]
    rw [List.count_tail (by simp)]
    simp [hy]

lemma Walk.not_mem_support_reverse_tail_takeUntil (w : G.Walk u v) (hx : x ∈ w.support) :
    x ∉ (w.takeUntil x hx).support.reverse.tail := by
  intro hx2
  rw [← List.count_pos_iff, List.count_tail (by simp)] at hx2
  simp at hx2

open List
/-- If `x` is a repeated vertex of the walk `w` then `w.shortClosed hx` is
a non-nil closed walk. -/
lemma Walk.shortClosed_not_nil_of_one_lt_count (w : G.Walk u v) (hx : x ∈ w.support)
    (h2 : 1 < w.support.count x) : ¬(w.shortClosed hx).Nil := by
  intro h
  have hs := dropUntil_spec w hx
  have : w.dropUntil x hx = (w.reverse.takeUntil x (w.mem_support_reverse.2 hx)).reverse := by
    rw [← hs, h.eq_nil]
    exact Walk.nil_append _
  have hw :=  congr_arg Walk.support <| take_spec w hx
  rw [this, support_append] at hw
  apply_fun List.count x at hw
  rw [List.count_append] at hw
  simp only [count_support_takeUntil_eq_one, support_reverse] at *
  have : 0 < count x (w.reverse.takeUntil x (w.mem_support_reverse.2 hx)).support.reverse.tail := by
    omega
  rw [List.count_pos_iff]at this
  exact (w.reverse.not_mem_support_reverse_tail_takeUntil _) this

lemma Walk.length_shortCut_add_shortClosed (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.shortCut hx).length + (w.shortClosed hx).length = w.length := by
  simp_rw [← Walk.length_takeUntil_add_dropUntil hx, ← w.dropUntil_spec hx, shortClosed, shortCut,
            length_append, length_reverse]
  omega

lemma Walk.count_support_rotate_new (w : G.Walk u u) (hx : x ∈ w.support) (hne : x ≠ u) :
  (w.rotate hx).support.count x = w.support.count x + 1 := by
  nth_rw 2 [← take_spec w hx]
  simp_rw [rotate, Walk.support_append, List.count_append]
  rw [List.count_tail (by simp), List.count_tail (by simp)]
  simp [if_neg (Ne.symm hne)]

lemma Walk.count_support_rotate_old (w : G.Walk u u) (hx : x ∈ w.support) (hne : x ≠ u) :
  (w.rotate hx).support.count u = w.support.count u - 1 := by
  nth_rw 2 [← take_spec w hx]
  simp_rw [rotate, Walk.support_append, List.count_append]
  rw [List.count_tail (by simp), List.count_tail (by simp)]
  simp [head_support, beq_self_eq_true, ↓reduceIte,if_neg hne]
  rw [← Nat.add_sub_assoc (by simp), add_comm]

lemma Walk.count_support_rotate_other (w : G.Walk u u) (hx : x ∈ w.support) (hvx : x ≠ v)
  (hvu : u ≠ v) : (w.rotate hx).support.count v = w.support.count v := by
  nth_rw 2 [← take_spec w hx]
  simp_rw [rotate, Walk.support_append, List.count_append]
  rw [List.count_tail (by simp), List.count_tail (by simp)]
  simp [head_support, beq_iff_eq, if_neg hvu, if_neg hvx, add_comm]

/--
Given a closed walk `w : G.Walk u u` and a vertex `x ∈ w.support` we can form a new closed walk
`w.shorterOdd hx`. If `w.length` is odd then this walk is also odd. Morever if `x` occured more
than once in `w` and `x ≠ u` then `w.shorterOdd hx` is strictly shorter than `w`.
-/
def Walk.shorterOdd {u : α} (p : G.Walk u u) {x : α} (hx : x ∈ p.support) : G.Walk x x :=
  if ho : Odd (p.shortClosed hx).length then
    p.shortClosed hx
  else
  -- We rotate this walk to be able to return a `G.Walk x x` in both cases
    (p.shortCut hx).rotate (by simp)

lemma Walk.darts_shorterOdd_subset {u : α} (p : G.Walk u u) {x : α} (hx : x ∈ p.support) :
    (p.shorterOdd hx).darts ⊆ p.darts := by
  intro d hd
  rw [shorterOdd] at hd
  split_ifs at hd with h1
  · rw [shortClosed] at hd
    have := darts_dropUntil_subset _ _ hd
    rw [ mem_darts_reverse] at this
    have := darts_dropUntil_subset _ _ this
    rwa [mem_darts_reverse] at this
  · have := rotate_darts (p.shortCut hx) (show x ∈ _ by simp [hx])
    rw [this.mem_iff, shortCut, darts_append, mem_append] at hd
    cases hd with
    | inl hd => apply darts_takeUntil_subset _ _ hd
    | inr hd =>
      rw [ mem_darts_reverse] at hd
      have := darts_takeUntil_subset _ _ hd
      rwa [mem_darts_reverse] at this

lemma Walk.length_shorterOdd_odd {p : G.Walk u u} {x : α} (hx : x ∈ p.support)
    (ho : Odd p.length) : Odd (p.shorterOdd hx).length := by
  rw [← p.length_shortCut_add_shortClosed hx] at ho
  rw [shorterOdd]
  split_ifs with h1
  · exact h1
  · rw [Walk.length_rotate]
    exact (Nat.odd_add.1 ho).2 (Nat.not_odd_iff_even.1 h1)

lemma Walk.length_shorterOdd_le {u : α} (p : G.Walk u u) {x : α} (hx : x ∈ p.support) :
    (p.shorterOdd hx).length ≤ p.length := by
  by_cases ho : Odd (p.shortClosed hx).length
  · rw [shorterOdd, dif_pos ho]
    rw [← p.length_shortCut_add_shortClosed hx]
    omega
  · rw [shorterOdd, dif_neg ho]
    rw [← p.length_shortCut_add_shortClosed hx, length_rotate]
    omega

lemma Walk.length_shorterOdd_lt_length {p : G.Walk u u} {x : α} (hx : x ∈ p.support) (hne : x ≠ u)
    (h2 : 1 < p.support.count x) : (p.shorterOdd hx).length < p.length := by
  rw [shorterOdd, ← p.length_shortCut_add_shortClosed hx]
  split_ifs with ho
  · rw [lt_add_iff_pos_left, ← not_nil_iff_lt_length]
    exact p.shortCut_not_nil hx hne
  · rw [Walk.length_rotate, lt_add_iff_pos_right, ← not_nil_iff_lt_length]
    exact p.shortClosed_not_nil_of_one_lt_count hx h2

lemma Walk.length_shorterOdd_lt_length' {p : G.Walk u u}
    (h : p.support.filter (fun x ↦ x ≠ u ∧ 1 < p.support.count x) ≠ []) :
    (p.shorterOdd (head_filter_mem _ _ h)).length < p.length := by
  have hm := List.head_mem h
  rw [List.mem_filter, decide_eq_true_eq] at hm
  exact p.length_shorterOdd_lt_length hm.1 hm.2.1 hm.2.2

/--
shorterOdd' is useful to convert a closed walk `p : G.Walk u u` where `u` occurs more
than twice but all other vertices occur once into an (odd) cycle (see `cutVert`).
-/
private def Walk.shorterOdd' {u : α} (p : G.Walk u u) : G.Walk u u  :=
  match p with
  | .nil' u => nil' u
  | .cons h p => by
    have hy : (p.cons h).snd ∈ (p.cons h).support := by simp
    have hu : u ∈ ((p.cons h).rotate hy).support :=
      (mem_support_rotate_iff hy).2 (p.cons h).start_mem_support
    exact ((p.cons h).rotate hy).shorterOdd hu

lemma Walk.length_shorterOdd' {u : α} (p : G.Walk u u) (hp : 2 < p.support.count u):
    p.shorterOdd'.length < p.length := by
  cases p with
  | nil => simp at hp
  | cons h p =>
    have hy : (p.cons h).snd ∈ (p.cons h).support := by simp
    have hu : u ∈ ((p.cons h).rotate hy).support :=
       (mem_support_rotate_iff hy).2 (p.cons h).start_mem_support
    rw [shorterOdd']
    have : ((p.cons h).rotate hy).length = (p.cons h).length := by simp
    rw [← this]
    have : u ≠ (p.cons h).snd := by simpa using h.ne
    apply length_shorterOdd_lt_length hu this
    rw [count_support_rotate_old _ hy (Ne.symm this)]
    omega

lemma Walk.count_le_shorterOdd' {u x : α} (p : G.Walk u u) (hne : x ≠ u) (h2 : p.snd ≠ x):
    p.shorterOdd'.support.count x ≤ p.support.count x := by
  cases p with
  | nil => simp [shorterOdd']
  | @cons _ y _ h p =>
    have hy : (p.cons h).snd ∈ (p.cons h).support := by simp
    have hu : u ∈ ((p.cons h).rotate hy).support := by
      exact (mem_support_rotate_iff hy).2 (p.cons h).start_mem_support
    by_cases ho : Odd (((p.cons h).rotate hy).shortClosed hu).length
    · simp only [shorterOdd', shorterOdd, getVert_cons_succ, ho, ↓reduceDIte]
      apply le_trans
      · apply Walk.shortClosed_count_le
      · rw [Walk.count_support_rotate_other _  hy (by simpa using h2) (Ne.symm hne) ]
    · simp only [shorterOdd', shorterOdd, getVert_cons_succ, ho, ↓reduceDIte]
      rw [Walk.count_support_rotate_other _ (by simp) (Ne.symm hne) (by simpa using h2)]
      apply le_trans
      · apply Walk.shortCut_count_le
      · rw [Walk.count_support_rotate_other _  hy (by simpa using h2) (Ne.symm hne) ]

lemma Walk.count_le_shorterOdd'_of_snd {u : α} (p : G.Walk u u) (hne : p.snd ≠ u)
    (h1 : p.support.count p.snd ≤ 1) : p.shorterOdd'.support.count p.snd ≤ 1 := by
  apply h1.trans'
  cases p with
  | nil => simp [shorterOdd']
  | cons h p =>
    have hy : (p.cons h).snd ∈ (p.cons h).support := by simp
    have hu : u ∈ ((p.cons h).rotate hy).support := by
      exact (mem_support_rotate_iff hy).2 (p.cons h).start_mem_support
    by_cases ho : Odd (((p.cons h).rotate hy).shortClosed hu).length
    · simp only [shorterOdd', shorterOdd, ho, ↓reduceDIte]
      have := shortClosed_count_le_two  ((p.cons h).rotate hy) hu (Ne.symm hne)
        (by rw [count_support_rotate_new _ (by simp) hne]; omega)
      have := List.count_eq_zero_of_not_mem  this
      omega
    · simp only [shorterOdd', shorterOdd,ho, ↓reduceDIte]
      rw [count_support_rotate_old _ _ (Ne.symm hne)]
      simp only [tsub_le_iff_right, ge_iff_le]
      rw [← count_support_rotate_new _ (by simp) hne]
      apply shortCut_count_le

private def Walk.cutVert {u : α} (w : G.Walk u u) : G.Walk u u  :=
  if h : w.support.count u ≤ 2 then w
  else
    have := w.length_shorterOdd' (by rwa [not_le] at h)
    w.shorterOdd'.cutVert
  termination_by w.length

@[simp]
lemma Walk.cutVert_of_count_le_two {u : α} (w : G.Walk u u) (h : w.support.count u ≤ 2) :
    w.cutVert = w := by
  simp [cutVert,h]

@[simp]
lemma Walk.cutVert_of_two_lt_count {u : α} (w : G.Walk u u) (h : 2 < w.support.count u) :
    w.cutVert = w.shorterOdd'.cutVert := by
  rw [cutVert, dif_neg]
  omega

lemma Walk.cutVert_cutVert {u : α} (p : G.Walk u u) :
    p.cutVert.cutVert = p.cutVert := by
  induction hn : p.length using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases h : p.support.count u ≤ 2
    · simp [h]
    · push_neg at h
      rw [cutVert_of_two_lt_count _ h]
      apply ih _ (hn ▸ p.length_shorterOdd' h) p.shorterOdd' rfl

lemma Walk.cutVert_odd {u : α} (p : G.Walk u u) (ho : Odd p.length) : Odd p.cutVert.length := by
  induction hn : p.length using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases h : p.support.count u ≤ 2
    · simpa [h]
    · push_neg at h
      rw [cutVert_of_two_lt_count _ h]
      apply ih _ (hn ▸ p.length_shorterOdd' h) p.shorterOdd' _ rfl
      cases p with
      | nil => simp at ho
      | cons h p =>
        rw [shorterOdd']
        apply length_shorterOdd_odd
        rwa [length_rotate]

lemma Walk.cutVert_count_start {u : α} (p : G.Walk u u) : p.cutVert.support.count u ≤ 2 := by
  induction hn : p.length using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases h : p.support.count u ≤ 2
    · rwa [cutVert_of_count_le_two _ h]
    · push_neg at h
      rw [cutVert_of_two_lt_count _ h]
      exact ih _ (hn ▸ p.length_shorterOdd' h) p.shorterOdd' rfl

lemma Walk.cutVert_count_ne_start {u x : α} (p : G.Walk u u) (hx : x ≠ u)
    (h1 : p.support.count x ≤ 1) : p.cutVert.support.count x ≤ 1 := by
  induction hn : p.length using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases h : p.support.count u ≤ 2
    · rwa [cutVert_of_count_le_two _ h]
    · push_neg at h
      rw [cutVert_of_two_lt_count _ h]
      apply ih _ (hn ▸ p.length_shorterOdd' h) p.shorterOdd' _ rfl
      by_cases h' : p.snd = x
      · subst x
        exact p.count_le_shorterOdd'_of_snd  hx h1
      · exact (p.count_le_shorterOdd' hx h').trans h1

lemma Walk.darts_cutVert_subset {u : α} (p : G.Walk u u) : p.cutVert.darts ⊆ p.darts := by
  induction hn : p.length using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases h : p.support.count u ≤ 2
    · rw [cutVert_of_count_le_two _ h]
      simp
    · push_neg at h
      rw [cutVert_of_two_lt_count _ h]
      intro d hd
      have := ih _ (hn ▸ p.length_shorterOdd' h) p.shorterOdd' rfl hd
      cases p with
      | nil => simp at h
      | cons h' p =>
        rw [shorterOdd'] at hd
        have hs := darts_shorterOdd_subset _ _ this
        have := rotate_darts (p.cons h') (show p.getVert 0 ∈ _ by simp)
        exact this.mem_iff.1 hs

/-- Return an almost minimal odd closed subwalk from an odd length closed walk
(if p.length is not odd then this just returns some closed subwalk).
-/
private def Walk.minOdd_aux {u : α} (p : G.Walk u u) : Σ v, G.Walk v v :=
  if h : p.support.filter (fun x ↦ x ≠ u ∧ 1 < p.support.count x) = []
    then ⟨_,p⟩
  else
    have := p.length_shorterOdd_lt_length' h
    (p.shorterOdd (head_filter_mem _ _ h)).minOdd_aux
  termination_by p.length

lemma Walk.minOdd_aux_nil {u : α} (p : G.Walk u u)
    (hx : ∀ v ∈ p.support, v ≠ u → p.support.count v ≤ 1) : p.minOdd_aux = ⟨_, p⟩ := by
  have h : (p.support.filter (fun x ↦ x ≠ u ∧ 1 < p.support.count x)) = [] := by
    simp_all
  rw [minOdd_aux, dif_pos h]

lemma Walk.minOdd_aux_filter_ne {u v : α} (p : G.Walk u u)
  (hv : v ∈ p.support ∧ v ≠ u ∧ 1 < p.support.count v) :
  (p.support.filter (fun x ↦ x ≠ u ∧ 1 < p.support.count x)) ≠ [] := by
  simpa using ⟨v, hv⟩

lemma Walk.minOdd_aux_ne_nil {u v : α} (p : G.Walk u u)
    (hv : v ∈ p.support ∧ v ≠ u ∧ 1 < p.support.count v) : p.minOdd_aux =
    (p.shorterOdd ((head_filter_mem _ _ (p.minOdd_aux_filter_ne hv)))).minOdd_aux := by
  rw [minOdd_aux, dif_neg (p.minOdd_aux_filter_ne hv)]

lemma Walk.minOdd_aux_minOdd_aux {u : α} (p : G.Walk u u) :
    p.minOdd_aux.2.minOdd_aux = p.minOdd_aux := by
  induction hn : p.length using Nat.strong_induction_on generalizing p u with
  | h n ih =>
    by_cases hv : ∃ v ∈ p.support, v ≠ u ∧ 1 < p.support.count v
    · obtain ⟨v, hv⟩ := hv
      rw [p.minOdd_aux_ne_nil hv]
      exact ih _ (hn ▸ p.length_shorterOdd_lt_length' (p.minOdd_aux_filter_ne hv)) _ rfl
    · push_neg at hv
      rw [minOdd_aux_nil _ hv, minOdd_aux_nil _ hv]

lemma Walk.minOdd_aux_length_le {u : α} (p : G.Walk u u) : p.minOdd_aux.2.length ≤ p.length := by
  induction hn : p.length using Nat.strong_induction_on generalizing p u with
  | h n ih =>
    by_cases hv : ∃ v ∈ p.support, v ≠ u ∧ 1 < p.support.count v
    · obtain ⟨v, hv⟩ := hv
      rw [p.minOdd_aux_ne_nil hv]
      have hlt : (p.shorterOdd (head_filter_mem _ _ (p.minOdd_aux_filter_ne hv))).length < n :=
        hn ▸ p.length_shorterOdd_lt_length' (p.minOdd_aux_filter_ne hv)
      apply (ih _ hlt _ rfl).trans hlt.le
    · push_neg at hv
      rw [minOdd_aux_nil _ hv, hn]

lemma Walk.minOdd_aux_count_le_one_of_ne_start  {u v : α} (p : G.Walk u u)
    (hn : v ≠ p.minOdd_aux.1) : count v p.minOdd_aux.2.support ≤ 1 := by
  by_cases hv : v ∈ p.minOdd_aux.2.support
  · by_contra! hc
    have := p.minOdd_aux.2.minOdd_aux_ne_nil ⟨hv, hn, hc⟩
    rw [minOdd_aux_minOdd_aux] at this
    have hnil := p.minOdd_aux.2.minOdd_aux_filter_ne ⟨hv, hn, hc⟩
    have ht :=(p.minOdd_aux.2.shorterOdd (head_filter_mem _ _ hnil)).minOdd_aux_length_le
    rw [← this] at ht
    have := p.minOdd_aux.2.length_shorterOdd_lt_length' hnil
    omega
  · rw [count_eq_zero_of_not_mem hv]
    omega

lemma Walk.minOdd_aux_odd {u : α} (p : G.Walk u u) (ho : Odd p.length) :
    Odd p.minOdd_aux.2.length := by
  induction hn : p.length using Nat.strong_induction_on generalizing p u with
  | h n ih =>
    by_cases hv : ∃ v ∈ p.support, v ≠ u ∧ 1 < p.support.count v
    · obtain ⟨v, hv⟩ := hv
      rw [p.minOdd_aux_ne_nil hv]
      have hnil := (p.minOdd_aux_filter_ne hv)
      have hm := List.head_mem hnil
      rw [List.mem_filter, decide_eq_true_eq] at hm
      exact ih _ (hn ▸ p.length_shorterOdd_lt_length' hnil) _ (p.length_shorterOdd_odd hm.1 ho) rfl
    · push_neg at hv
      rw [minOdd_aux_nil _ hv, hn]
      exact hn ▸ ho

lemma Walk.darts_minOdd_aux_subset {u : α} (p : G.Walk u u) :
  p.minOdd_aux.2.darts ⊆ p.darts := by
  induction hn : p.length using Nat.strong_induction_on generalizing p u with
  | h n ih =>
    by_cases hv : ∃ v ∈ p.support, v ≠ u ∧ 1 < p.support.count v
    · obtain ⟨v, hv⟩ := hv
      rw [p.minOdd_aux_ne_nil hv]
      have hnil := (p.minOdd_aux_filter_ne hv)
      have hm := List.head_mem hnil
      rw [List.mem_filter, decide_eq_true_eq] at hm
      intro d hd
      exact darts_shorterOdd_subset _ _ <| ih _ (hn ▸ p.length_shorterOdd_lt_length' hnil) _ rfl hd
    · push_neg at hv
      rw [minOdd_aux_nil _ hv]
      intro d hd ; exact hd

/-- Returns an odd cycle (given an odd closed walk) -/
def Walk.oddCycle {u : α} (p : G.Walk u u) : Σ v, G.Walk v v := ⟨_, p.minOdd_aux.2.cutVert⟩

lemma Walk.oddCycle_is_odd {u : α} (p : G.Walk u u) (ho : Odd p.length) :
    Odd p.oddCycle.2.length := cutVert_odd _ <| p.minOdd_aux_odd ho

lemma Walk.oddCycle_isCycle {u : α} (p : G.Walk u u) (ho : Odd p.length) :
    p.oddCycle.2.IsCycle := by
  apply isCycle_odd_support_tail_nodup  _ _ <| p.oddCycle_is_odd ho
  apply (support_tail_nodup_iff_count_le _).2
      ⟨cutVert_count_start _,
      fun _ _ h ↦ cutVert_count_ne_start _ h <| minOdd_aux_count_le_one_of_ne_start p h⟩

lemma Walk.oddCycle_spec {u : α} (p : G.Walk u u) (ho : Odd p.length) :
    Odd p.oddCycle.2.length ∧ p.oddCycle.2.IsCycle := ⟨p.oddCycle_is_odd ho, p.oddCycle_isCycle ho⟩

lemma Walk.exists_odd_cycle_of_odd_closed_walk  (p : G.Walk u u) (ho : Odd p.length) :
    ∃ x, ∃ (c : G.Walk x x), Odd c.length ∧ c.IsCycle :=
  ⟨_, _, p.oddCycle_spec ho⟩

lemma Walk.darts_oddCycle_subset (p : G.Walk u u) : p.oddCycle.2.darts ⊆ p.darts :=
  fun _ hd ↦ p.darts_minOdd_aux_subset <| p.minOdd_aux.2.darts_cutVert_subset hd

end SimpleGraph
