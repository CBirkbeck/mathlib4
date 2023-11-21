/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.LazyList
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Stream
import Mathlib.Data.Seq.Computation

#align_import data.seq.seq from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Possibly infinite lists

This file provides a `Seq' α` type representing possibly infinite lists
(referred here as sequences).
It is encoded as a function of options such that if `get s n = none`, then
`get s m = none` for all `m ≥ n` in the kernel, but a lazily evaluated list in the runtime.

Note that we already have `Seq` to represent an notation class, hence the awkward naming.
-/

open Function

universe u v w

namespace LazyList

variable {α : Type u} {β : Type v} {δ : Type w}

/-- Destructor for a lazy list, resulting in either `none` (for `nil`) or
  `some (a, l.get)` (for `cons a l`). -/
def dest : (l : LazyList α) → Option (α × LazyList α)
  | nil      => none
  | cons a t => some (a, Thunk.get t)

/-- Corecursor for `LazyList α` as a coinductive type. Iterates `f` to produce new elements
  of the sequence until `none` is obtained. -/
unsafe def corec (f : β → Option (α × β)) (b : β) : LazyList α :=
  match f b with
  | none        => nil
  | some (a, b) => cons a ⟨fun _ => corec f b⟩

end LazyList

open LazyList

#noalign stream.is_seq

/-- `Seq' α` is the type of possibly infinite lists (referred here as sequences).
This type has special support in the runtime. -/
@[opaque_repr]
structure Seq' (α : Type u) : Type u where
  /-- Convert a `ℕ → Option α` into a `Seq' α`. Consider using other functions like `corec`
  before use this. -/
  mk ::
  /-- Get the nth element of a sequence (if it exists) -/
  get? : ℕ → Option α
  /-- `get? s n = none` implies `get? s (n + 1) = none`. -/
  succ_stable : ∀ ⦃n⦄, get? n = none → get? (n + 1) = none
#align stream.seq Seq'
#align stream.seq.nth Seq'.get?

/-- `Seq1 α` is the type of nonempty sequences. -/
structure Seq1 (α : Type u) : Type u where
  /-- Head of an nonempty sequence. -/
  head : α
  /-- Tail of an nonempty sequence. -/
  tail : Seq' α
#align stream.seq1 Seq1

namespace Seq'

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The empty sequence. -/
@[inline]
unsafe def nilUnsafe : Seq' α :=
  unsafeCast (nil : LazyList α)

@[inherit_doc nilUnsafe, implemented_by nilUnsafe]
def nil : Seq' α where
  get? _ := none
  succ_stable _ _ := rfl
#align stream.seq.nil Seq'.nil

instance : Inhabited (Seq' α) :=
  ⟨nil⟩

/-- Prepend an element to a sequence -/
@[inline]
unsafe def consUnsafe (a : α) (s : Seq' α) : Seq' α :=
  unsafeCast (cons a (Thunk.pure (unsafeCast s)))

@[inherit_doc consUnsafe, implemented_by consUnsafe]
def cons (a : α) (s : Seq' α) : Seq' α where
  get?
  | 0     => some a
  | n + 1 => get? s n
  succ_stable
  | _ + 1, h => succ_stable s h
#align stream.seq.cons Seq'.cons

/-- Prepend an element to a s**e**quence -/
infixr:67 " ::ₑ " => cons

#noalign stream.seq.val_cons

#noalign stream.seq.nth_mk

@[simp]
theorem get?_nil (n : ℕ) : get? (nil : Seq' α) n = none :=
  rfl
#align stream.seq.nth_nil Seq'.get?_nil

theorem get?_cons_zero (a : α) (s : Seq' α) : get? (a ::ₑ s) 0 = some a :=
  rfl
#align stream.seq.nth_cons_zero Seq'.get?_cons_zero

theorem get?_cons_succ (a : α) (s : Seq' α) (n : ℕ) : get? (a ::ₑ s) (n + 1) = get? s n :=
  rfl
#align stream.seq.nth_cons_succ Seq'.get?_cons_succ

@[ext]
protected theorem ext {s t : Seq' α} (h : ∀ n : ℕ, s.get? n = t.get? n) : s = t := by
  cases s; cases t
  congr; funext n; apply h
#align stream.seq.ext Seq'.ext

theorem cons_injective2 : Function.Injective2 (cons : α → Seq' α → Seq' α) := fun x y s t h =>
  ⟨by rw [← Option.some_inj, ← get?_cons_zero, h, get?_cons_zero],
    Seq'.ext fun n => by simp_rw [← get?_cons_succ x s n, h, get?_cons_succ]⟩
#align stream.seq.cons_injective2 Seq'.cons_injective2

@[simp]
theorem cons_inj {a b : α} {s t : Seq' α} : a ::ₑ s = b ::ₑ t ↔ a = b ∧ s = t :=
  cons_injective2.eq_iff

theorem cons_left_injective (s : Seq' α) : Function.Injective (· ::ₑ s) :=
  cons_injective2.left _
#align stream.seq.cons_left_injective Seq'.cons_left_injective

theorem cons_right_injective (x : α) : Function.Injective (x ::ₑ ·) :=
  cons_injective2.right _
#align stream.seq.cons_right_injective Seq'.cons_right_injective

/-- A sequence has terminated at position `n` if the value at position `n` equals `none`. -/
def TerminatedAt (s : Seq' α) (n : ℕ) : Prop :=
  s.get? n = none
#align stream.seq.terminated_at Seq'.TerminatedAt

@[simp]
theorem nil_terminatedAt (n : ℕ) : (nil : Seq' α).TerminatedAt n :=
  rfl

@[simp]
theorem not_cons_terminatedAt_zero (a : α) (s : Seq' α) : ¬(a ::ₑ s).TerminatedAt 0 :=
  Option.some_ne_none a

@[simp]
theorem cons_terminatedAt_succ (a : α) (s : Seq' α) (n : ℕ) :
    (a ::ₑ s).TerminatedAt (n + 1) ↔ s.TerminatedAt n :=
  Iff.rfl

#noalign stream.seq.omap

/-- Get the first element of a sequence -/
noncomputable def head (s : Seq' α) : Option α :=
  get? s 0
#align stream.seq.head Seq'.head

@[simp]
theorem get?_zero (s : Seq' α) : get? s 0 = head s :=
  rfl

/-- Get the tail of a sequence (or `nil` if the sequence is `nil`) -/
noncomputable def tail (s : Seq' α) : Seq' α where
  get? n := get? s (n + 1)
  succ_stable _ h := succ_stable s h
#align stream.seq.tail Seq'.tail

/-- member definition for `Seq`-/
protected def Mem (a : α) (s : Seq' α) :=
  ∃ n, get? s n = a
#align stream.seq.mem Seq'.Mem

instance : Membership α (Seq' α) :=
  ⟨Seq'.Mem⟩

theorem mem_def (a : α) (s : Seq' α) : a ∈ s ↔ ∃ n, get? s n = a :=
  Iff.rfl

theorem le_stable (s : Seq' α) {m n} (h : m ≤ n) : s.get? m = none → s.get? n = none := by
  cases' s with f al
  induction' h with n _ IH
  exacts [id, fun h2 => al (IH h2)]
#align stream.seq.le_stable Seq'.le_stable

/-- If a sequence terminated at position `n`, it also terminated at `m ≥ n`. -/
theorem terminated_stable : ∀ (s : Seq' α) {m n : ℕ}, m ≤ n → s.TerminatedAt m → s.TerminatedAt n :=
  le_stable
#align stream.seq.terminated_stable Seq'.terminated_stable

/-- If `s.get? n = some aₙ` for some value `aₙ`, then there is also some value `aₘ` such
that `s.get? = some aₘ` for `m ≤ n`.
-/
theorem ge_stable (s : Seq' α) {aₙ : α} {n m : ℕ} (m_le_n : m ≤ n)
    (s_get?_eq_some : s.get? n = some aₙ) : ∃ aₘ : α, s.get? m = some aₘ :=
  have : s.get? n ≠ none := by simp [s_get?_eq_some]
  have : s.get? m ≠ none := mt (s.le_stable m_le_n) this
  Option.ne_none_iff_exists'.mp this
#align stream.seq.ge_stable Seq'.ge_stable

@[simp]
theorem not_mem_nil (a : α) : a ∉ @nil α := fun ⟨_, (h : none = some a)⟩ => by injection h
#align stream.seq.not_mem_nil Seq'.not_mem_nil

theorem mem_cons (a : α) (s : Seq' α) : a ∈ a ::ₑ s :=
  ⟨0, rfl⟩
#align stream.seq.mem_cons Seq'.mem_cons

theorem mem_cons_of_mem (y : α) {a : α} {s : Seq' α} : a ∈ s → a ∈ y ::ₑ s
  | ⟨n, h⟩ => ⟨n + 1, h⟩
#align stream.seq.mem_cons_of_mem Seq'.mem_cons_of_mem

theorem eq_or_mem_of_mem_cons {a b : α} {s : Seq' α} : a ∈ b ::ₑ s → a = b ∨ a ∈ s
  | ⟨0, h⟩ => Or.inl (Option.some_injective _ h.symm)
  | ⟨n + 1, h⟩ => Or.inr ⟨n, h⟩
#align stream.seq.eq_or_mem_of_mem_cons Seq'.eq_or_mem_of_mem_cons

@[simp]
theorem mem_cons_iff {a b : α} {s : Seq' α} : a ∈ b ::ₑ s ↔ a = b ∨ a ∈ s :=
  ⟨eq_or_mem_of_mem_cons, by rintro (rfl | m) <;> [apply mem_cons; exact mem_cons_of_mem _ m]⟩
#align stream.seq.mem_cons_iff Seq'.mem_cons_iff

/-- Destructor for a sequence, resulting in either `none` (for `nil`) or
  `some (a, s)` (for `a ::ₑ s`). -/
@[inline]
unsafe def destUnsafe (s : Seq' α) : Option (α × Seq' α) :=
  unsafeCast (dest (unsafeCast s : LazyList α))

@[inherit_doc destUnsafe, implemented_by destUnsafe]
def dest (s : Seq' α) : Option (α × Seq' α) :=
  Option.map ((·, s.tail)) (head s)
#align stream.seq.destruct Seq'.dest

theorem dest_eq_nil {s : Seq' α} : dest s = none → s = nil := by
  dsimp [dest]
  induction' f0 : head s <;> intro h
  · ext1 n
    induction' n with n IH
    exacts [f0, s.2 IH]
  · contradiction
#align stream.seq.destruct_eq_nil Seq'.dest_eq_nil

theorem dest_eq_cons {s : Seq' α} {a s'} : dest s = some (a, s') → s = a ::ₑ s' := by
  dsimp [dest]
  induction' f0 : head s with a' <;> intro h
  · contradiction
  · cases' s with f hf
    injections _ h1 h2
    rw [← h2]
    ext1 n
    dsimp [tail, cons]
    rw [h1] at f0
    rw [← f0]
    cases n <;> rfl
#align stream.seq.destruct_eq_cons Seq'.dest_eq_cons

@[simp]
theorem dest_nil : dest (nil : Seq' α) = none :=
  rfl
#align stream.seq.destruct_nil Seq'.dest_nil

@[simp]
theorem dest_cons (a : α) (s) : dest (a ::ₑ s) = some (a, s) := by
  unfold cons dest
  apply congr_arg fun s => some (a, s)
  ext1 n; dsimp [tail]
#align stream.seq.destruct_cons Seq'.dest_cons

theorem head_eq_dest (s : Seq' α) : head s = Option.map Prod.fst (dest s) := by
  unfold dest; cases head s <;> rfl
#align stream.seq.head_eq_destruct Seq'.head_eq_dest

@[simp]
theorem head_nil : head (nil : Seq' α) = none :=
  rfl
#align stream.seq.head_nil Seq'.head_nil

@[simp]
theorem head_cons (a : α) (s) : head (a ::ₑ s) = some a := by
  rw [head_eq_dest, dest_cons, Option.map_some']
#align stream.seq.head_cons Seq'.head_cons

@[simp]
theorem tail_nil : tail (nil : Seq' α) = nil :=
  rfl
#align stream.seq.tail_nil Seq'.tail_nil

@[simp]
theorem tail_cons (a : α) (s) : tail (a ::ₑ s) = s := by
  cases' s with f al
  ext1 n
  dsimp [tail, cons]
#align stream.seq.tail_cons Seq'.tail_cons

@[simp]
theorem get?_succ (s : Seq' α) (n) : get? s (n + 1) = get? (tail s) n :=
  rfl
#align stream.seq.nth_tail Seq'.get?_succ

/-- Recursion principle for sequences, compare with `List.recOn`. -/
@[elab_as_elim]
def recOn' {C : Seq' α → Sort v} (s : Seq' α) (nil : C nil) (cons : ∀ x s, C (x ::ₑ s)) : C s :=
  match H : dest s with
  | none => cast (congr_arg C (dest_eq_nil H)).symm nil
  | some (a, s') => cast (congr_arg C (dest_eq_cons H)).symm (cons a s')
#align stream.seq.rec_on Seq'.recOn'

@[elab_as_elim]
theorem mem_rec_on {a} {C : (s : Seq' α) → a ∈ s → Prop} {s} (M : a ∈ s)
    (mem_cons : ∀ s, C (a ::ₑ s) (mem_cons a s))
    (mem_cons_of_mem : ∀ (y) {s} (h : a ∈ s), C s h → C (y ::ₑ s) (mem_cons_of_mem y h)) :
    C s M := by
  cases M with
  | intro k e =>
    induction k using Nat.recAux generalizing s with
    | zero =>
      induction s using recOn' with
      | nil => injection e
      | cons b s' =>
        injection e with e'
        induction e'
        exact mem_cons s'
    | succ k IH =>
      induction s using recOn' with
      | nil => injection e
      | cons b s' =>
        rw [get?_cons_succ] at e
        exact mem_cons_of_mem b _ (IH e)
#align stream.seq.mem_rec_on Seq'.mem_rec_onₓ

@[inherit_doc head]
def headComputable (s : Seq' α) : Option α :=
  Option.map Prod.fst (dest s)

@[csimp]
theorem head_eq_headComputable : @head.{u} = @headComputable.{u} := by
  funext α s
  rw [headComputable, head_eq_dest]

@[inherit_doc tail, simp]
def tailComputable (s : Seq' α) : Seq' α :=
  Option.elim (dest s) nil Prod.snd

@[csimp]
theorem tail_eq_tailComputable : @tail.{u} = @tailComputable.{u} := by
  funext α s
  cases s using recOn' <;> simp

@[inherit_doc get?, simp]
def get?Computable (s : Seq' α) : ℕ → Option α
  | 0     => head s
  | n + 1 => Option.elim (dest s) none (fun (_, s) => get?Computable s n)

@[csimp]
theorem get?_eq_get?Computable : @get?.{u} = @get?Computable.{u} := by
  funext α s n
  induction n using Nat.recAux generalizing s with
  | zero => cases s using recOn' <;> simp
  | succ n hn => cases s using recOn' <;> simp [hn]

/-- The implemention of `Seq'.casesOn`. -/
@[inline]
protected def casesOnComputable {α : Type u} {motive : Seq' α → Sort*}
    (s : Seq' α)
    (mk : (get? : ℕ → Option α) →
      (succ_stable : ∀ ⦃n⦄, get? n = none → get? (n + 1) = none) →
      motive (mk get? succ_stable)) : motive s :=
  mk (get? s) (succ_stable s)

@[csimp]
theorem casesOn_eq_casesOnComputable :
    @Seq'.casesOn.{v, u} = @Seq'.casesOnComputable.{v, u} :=
  rfl

/-- It is decidable whether a sequence terminates at a given position. -/
instance terminatedAtDecidable (s : Seq' α) (n : ℕ) : Decidable (s.TerminatedAt n) :=
  decidable_of_iff' (s.get? n).isNone <| by unfold TerminatedAt; cases s.get? n <;> simp
#align stream.seq.terminated_at_decidable Seq'.terminatedAtDecidable

theorem not_terminatedAt_iff {s : Seq' α} {n : ℕ} : ¬s.TerminatedAt n ↔ (s.get? n).isSome := by
  simp only [TerminatedAt, ← Ne.def, Option.ne_none_iff_isSome]

instance : GetElem (Seq' α) ℕ α (fun s n => ¬s.TerminatedAt n) where
  getElem s n h := Option.get (get? s n) (not_terminatedAt_iff.mp h)

@[simp]
theorem getElem?_eq_get? (s : Seq' α) (n : ℕ) : s[n]? = get? s n := by
  simp [getElem?, getElem, not_terminatedAt_iff, Option.isNone_iff_eq_none, eq_comm (a := none)]

theorem get?_eq_getElem {s : Seq' α} {n : ℕ} (h : ¬s.TerminatedAt n) : get? s n = some (s[n]'h) :=
  Option.some_get _ |>.symm

/-- A sequence terminates if there is some position `n` at which it has terminated. -/
def Terminates (s : Seq' α) : Prop :=
  ∃ n : ℕ, s.TerminatedAt n
#align stream.seq.terminates Seq'.Terminates

theorem terminates_of_terminatedAt {s : Seq' α} {n : ℕ} (h : s.TerminatedAt n) : s.Terminates :=
  Exists.intro n h

@[simp]
theorem nil_terminates : (nil : Seq' α).Terminates :=
  terminates_of_terminatedAt <| nil_terminatedAt 0

@[simp]
theorem cons_terminates (a : α) (s : Seq' α) : (a ::ₑ s).Terminates ↔ s.Terminates := by
  unfold Terminates; nth_rw 1 [← Nat.or_exists_succ]; simp

theorem not_terminates_iff {s : Seq' α} : ¬s.Terminates ↔ ∀ n, (s.get? n).isSome := by
  simp only [Terminates, not_terminatedAt_iff, not_exists]
#align stream.seq.not_terminates_iff Seq'.not_terminates_iff

set_option linter.uppercaseLean3 false in
#noalign stream.seq.corec.F

/-- Corecursor for `Seq' α` as a coinductive type. Iterates `f` to produce new elements
  of the sequence until `none` is obtained. -/
unsafe def corecUnsafe (f : β → Option (α × β)) (b : β) : Seq' α :=
  unsafeCast (corec f b)

@[inherit_doc corecUnsafe, implemented_by corecUnsafe]
def corec (f : β → Option (α × β)) (b : β) : Seq' α where
  get? n := Option.map Prod.fst ((fun o => Option.bind o (f ∘ Prod.snd))^[n] (f b))
  succ_stable n h := by
    simp at h
    simp [iterate_succ', h, - iterate_succ]
#align stream.seq.corec Seq'.corec

@[simp]
theorem get?_corec (f : β → Option (α × β)) (b : β) (n : ℕ) :
    get? (corec f b) n = Option.map Prod.fst ((fun o => Option.bind o (f ∘ Prod.snd))^[n] (f b)) :=
  rfl

@[simp]
theorem dest_corec (f : β → Option (α × β)) (b : β) :
    dest (corec f b) = Option.map (Prod.map id (corec f)) (f b) := by
  rcases hb : f b with (_ | ⟨_, _⟩) <;> simp [corec, dest, head, tail, hb]
#align stream.seq.corec_eq Seq'.dest_corec

section Bisim

variable (R : Seq' α → Seq' α → Prop)

#noalign stream.seq.bisim_o

/-- a relation is bisimilar if it meets the `BisimO` test-/
def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, R s₁ s₂ → Option.Rel (Prod.RProd Eq R) (dest s₁) (dest s₂)
#align stream.seq.is_bisimulation Seq'.IsBisimulation

-- If two streams are bisimilar, then they are equal
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} (r : R s₁ s₂) : s₁ = s₂ := by
  ext1 n
  induction n using Nat.recAux generalizing s₁ s₂ with
  | zero =>
    specialize bisim r
    match hs₁ : dest s₁, hs₂ : dest s₂, bisim with
    | none, none, Option.Rel.none =>
      simp [dest_eq_nil hs₁, dest_eq_nil hs₂]
    | some (a₁, s₁'), some (a₂, s₂'), Option.Rel.some (Prod.RProd.intro ha _) =>
      simp [dest_eq_cons hs₁, dest_eq_cons hs₂, ha]
  | succ n hn =>
    specialize bisim r
    match hs₁ : dest s₁, hs₂ : dest s₂, bisim with
    | none, none, Option.Rel.none =>
      simp [dest_eq_nil hs₁, dest_eq_nil hs₂]
    | some (a₁, s₁'), some (a₂, s₂'), Option.Rel.some (Prod.RProd.intro ha hs') =>
      simp [dest_eq_cons hs₁, dest_eq_cons hs₂, ha, hn hs']
#align stream.seq.eq_of_bisim Seq'.eq_of_bisim

end Bisim

theorem coinduction {s₁ s₂ : Seq' α} (hh : head s₁ = head s₂)
    (ht : ∀ (β : Type u) (fr : Seq' α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) :
    s₁ = s₂ :=
  eq_of_bisim
    (fun s₁ s₂ =>
      head s₁ = head s₂ ∧
        ∀ (β : Type u) (fr : Seq' α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂))
    (by
      rintro s₁ s₂ ⟨hh, ht⟩
      cases s₁ using recOn' <;> cases s₂ using recOn' <;> simp at hh
      case nil.nil =>
        simp
        constructor
      case cons.cons a₁ s₁ a₂ s₂ =>
        simp
        constructor; constructor
        · exact hh
        · constructor
          · specialize ht (Option α) head
            simp at ht
            exact ht hh
          · intro β fr
            specialize ht β (fr ∘ tail)
            simp at ht
            exact ht)
    ⟨hh, ht⟩
#align stream.seq.coinduction Seq'.coinduction

theorem coinduction2 (s) (f g : Seq' α → Seq' β)
    (H : ∀ s,
      Option.Rel (Prod.RProd Eq (fun s₁ s₂ => ∃ s, s₁ = f s ∧ s₂ = g s))
        (dest (f s)) (dest (g s))) :
    f s = g s := by
  refine' eq_of_bisim (fun s₁ s₂ => ∃ s, s₁ = f s ∧ s₂ = g s) _ ⟨s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨s, h1, h2⟩
  rw [h1, h2]; apply H
#align stream.seq.coinduction2 Seq'.coinduction2

@[inherit_doc mk, nolint unusedArguments, specialize, simp]
def mkComputable (f : ℕ → Option α) (_ : ∀ ⦃n⦄, f n = none → f (n + 1) = none) : Seq' α :=
  corec (fun n => Option.map ((·, n + 1)) (f n)) 0

@[csimp]
theorem mk_eq_mkComputable : @mk.{u} = @mkComputable.{u} := by
  funext α f hf
  ext1 n
  simp; symm
  induction n using Nat.recAux with
  | zero => cases f 0 <;> simp
  | succ n hn =>
    cases hfn : f n with
    | none =>
      simp [hfn] at hn
      simp [iterate_succ', hn, hf hfn, - iterate_succ]
    | some a =>
      clear hn
      simp [iterate_succ', hfn, - iterate_succ]
      suffices he :
          ((fun o ↦ Option.bind o ((fun n ↦ Option.map (fun x ↦ (x, n + 1)) (f n)) ∘ Prod.snd))^[n]
            (Option.map (fun x ↦ (x, 1)) (f 0))) = some (a, n + 1) by
        simp [iterate_succ', he, hfn, - iterate_succ]
        cases f (n + 1) <;> simp
      induction n using Nat.recAux generalizing a with
      | zero => simp [hfn]
      | succ n hn =>
        cases hfn' : f n with
        | none => simp [hf hfn'] at hfn
        | some a =>
          simp [iterate_succ', hn a hfn', hfn, - iterate_succ]

/-- Embed a list as a sequence -/
@[coe]
def ofList : (l : List α) → Seq' α
  | [] => nil
  | a :: l => a ::ₑ ofList l
#align stream.seq.of_list Seq'.ofList

instance coeList : Coe (List α) (Seq' α) :=
  ⟨ofList⟩
#align stream.seq.coe_list Seq'.coeList

@[simp, norm_cast]
theorem ofList_nil : (↑([] : List α) : Seq' α) = nil :=
  rfl
#align stream.seq.of_list_nil Seq'.ofList_nil

@[simp, norm_cast]
theorem ofList_cons (a : α) (l : List α) : (↑(a :: l) : Seq' α) = a ::ₑ ↑l :=
  rfl
#align stream.seq.of_list_cons Seq'.ofList_cons

@[simp, norm_cast]
theorem get?_ofList (l : List α) (n : ℕ) : get? (↑l : Seq' α) n = List.get? l n := by
  induction l generalizing n with
  | nil => simp
  | cons a l hl =>
    cases n using Nat.casesAuxOn with
    | zero => simp
    | succ n => simp [hl]
#align stream.seq.of_list_nth Seq'.get?_ofList

theorem ofList_injective : Function.Injective ((↑) : List α → Seq' α) := by
  intro l₁ l₂ h
  ext1 n
  rw [← get?_ofList, ← get?_ofList, h]

@[simp, norm_cast]
theorem ofList_inj {l₁ l₂ : List α} : (↑l₁ : Seq' α) = ↑l₂ ↔ l₁ = l₂ :=
  ofList_injective.eq_iff

theorem ofList_terminatedAt_length (l : List α) : (↑l : Seq' α).TerminatedAt l.length := by
  simp [TerminatedAt]

@[simp]
theorem ofList_terminatedAt_iff {l : List α} {n : ℕ} :
    (↑l : Seq' α).TerminatedAt n ↔ l.length ≤ n := by
  rw [TerminatedAt, get?_ofList, List.get?_eq_none]

@[simp]
theorem ofList_terminates (l : List α) : (↑l : Seq' α).Terminates :=
  Exists.intro l.length <| ofList_terminatedAt_length l

/-- Embed an infinite stream as a sequence -/
@[coe]
def ofStream (s : Stream' α) : Seq' α :=
  ⟨s.map some, fun {n} h => by contradiction⟩
#align stream.seq.of_stream Seq'.ofStream

instance coeStream : Coe (Stream' α) (Seq' α) :=
  ⟨ofStream⟩
#align stream.seq.coe_stream Seq'.coeStream

@[simp, norm_cast]
theorem ofStream_get? (s : Stream' α) (n : ℕ) : (↑s : Seq' α).get? n = some (s.get n) :=
  rfl

theorem ofStream_injective : Function.Injective ((↑) : Stream' α → Seq' α) := by
  intro s₁ s₂ h
  ext1 n
  rw [← Option.some_inj, ← ofStream_get?, ← ofStream_get?, h]

@[simp, norm_cast]
theorem ofStream_inj {s₁ s₂ : Stream' α} : (↑s₁ : Seq' α) = ↑s₂ ↔ s₁ = s₂ :=
  ofStream_injective.eq_iff

@[simp]
theorem not_ofStream_terminatedAt (s : Stream' α) (n : ℕ) : ¬(↑s : Seq' α).TerminatedAt n :=
  Option.some_ne_none (get s n)

@[simp]
theorem not_ofStream_terminates (s : Stream' α) : ¬(↑s : Seq' α).Terminates :=
  fun ⟨n, h⟩ => not_ofStream_terminatedAt s n h

/-- Embed a `LazyList α` as a sequence. Note that even though this
  is non-meta, it will produce infinite sequences if used with
  cyclic `LazyList`s created by meta constructions. -/
def ofLazyList : LazyList α → Seq' α :=
  corec fun
        | LazyList.nil => none
        | LazyList.cons a l' => some (a, l'.get)
#align stream.seq.of_lazy_list Seq'.ofLazyList

instance coeLazyList : Coe (LazyList α) (Seq' α) :=
  ⟨ofLazyList⟩
#align stream.seq.coe_lazy_list Seq'.coeLazyList

/-- Translate a sequence into a `LazyList`. Since `LazyList` and `List`
  are isomorphic as non-meta types, this function is necessarily meta. -/
unsafe def toLazyList : Seq' α → LazyList α
  | s =>
    match dest s with
    | none => LazyList.nil
    | some (a, s') => LazyList.cons a (toLazyList s')
#align stream.seq.to_lazy_list Seq'.toLazyList

/-- Translate a sequence to a list. This function will run forever if
  run on an infinite sequence. -/
unsafe def forceToList (s : Seq' α) : List α :=
  (toLazyList s).toList
#align stream.seq.force_to_list Seq'.forceToList

/-- The sequence of natural numbers some 0, some 1, ... -/
def nats : Seq' ℕ :=
  Stream'.nats
#align stream.seq.nats Seq'.nats

@[simp]
theorem nats_get? (n : ℕ) : nats.get? n = some n :=
  rfl
#align stream.seq.nats_nth Seq'.nats_get?

@[simp, norm_cast]
theorem ofStream_nats : (Stream'.nats : Seq' ℕ) = nats :=
  rfl

/-- Append two sequences. If `s₁` is infinite, then `s₁ ++ s₂ = s₁`,
  otherwise it puts `s₂` at the location of the `nil` in `s₁`. -/
def append (s₁ s₂ : Seq' α) : Seq' α :=
  @corec α (Seq' α × Seq' α)
    (fun ⟨s₁, s₂⟩ =>
      match dest s₁ with
      | none => omap (fun s₂ => (nil, s₂)) (dest s₂)
      | some (a, s₁') => some (a, s₁', s₂))
    (s₁, s₂)
#align stream.seq.append Seq'.append

instance : Append (Seq' α) where
  append := append

theorem append_def (s₁ s₂ : Seq' α) :
    s₁ ++ s₂ =
      @corec α (Seq' α × Seq' α)
        (fun ⟨s₁, s₂⟩ =>
          match dest s₁ with
          | none => omap (fun s₂ => (nil, s₂)) (dest s₂)
          | some (a, s₁') => some (a, s₁', s₂))
        (s₁, s₂) :=
  rfl

/-- Map a function over a sequence. -/
def map (f : α → β) : Seq' α → Seq' β
  | ⟨s, al⟩ =>
    ⟨s.map (Option.map f), fun {n} => by
      dsimp [Stream'.map]
      induction' e : s.get n with e <;> intro
      · rw [al e]
        assumption
      · contradiction⟩
#align stream.seq.map Seq'.map

/-- Flatten a sequence of sequences. (It is required that the
  sequences be nonempty to ensure productivity; in the case
  of an infinite sequence of `nil`, the first element is never
  generated.) -/
def join : Seq' (Seq1 α) → Seq' α :=
  corec fun S =>
    match dest S with
    | none => none
    | some (⟨a, s⟩, S') =>
      some
        (a,
          match dest s with
          | none => S'
          | some (b, s') => ⟨b, s'⟩ ::ₑ S')
#align stream.seq.join Seq'.join

/-- Remove the first `n` elements from the sequence. -/
@[simp]
def drop : ℕ → Seq' α → Seq' α
  | 0    , s => s
  | n + 1, s => drop n (tail s)
#align stream.seq.drop Seq'.dropₓ

@[simp]
theorem drop_nil : ∀ n, drop n (nil : Seq' α) = nil
  | 0     => rfl
  | n + 1 => by rw [drop, tail_nil, drop_nil n]

theorem drop_add (m) : ∀ (n) (s : Seq' α), drop (m + n) s = drop m (drop n s)
  | 0    , _ => rfl
  | n + 1, s => drop_add m n (tail s)
#align stream.seq.dropn_add Seq'.drop_addₓ

theorem tail_drop (n) (s : Seq' α) : tail (drop n s) = drop (n + 1) s := by
  rw [add_comm]; symm; apply drop_add
#align stream.seq.dropn_tail Seq'.tail_dropₓ

@[simp]
theorem head_drop (n) (s : Seq' α) : head (drop n s) = get? s n := by
  induction' n with n IH generalizing s; · rfl
  rw [Nat.succ_eq_add_one, ← get?_tail, drop]; apply IH
#align stream.seq.head_dropn Seq'.head_dropₓ

/-- Take the first `n` elements of the sequence (producing a list) -/
def take : ℕ → Seq' α → List α
  | 0, _ => []
  | n + 1, s =>
    match dest s with
    | none => []
    | some (x, r) => x :: take n r
#align stream.seq.take Seq'.take

@[simp]
theorem get?_take :
    ∀ (m n : ℕ) (s : Seq' α), List.get? (take n s) m = if m < n then get? s m else none
  | 0     , 0     , s => rfl
  | 0     , n' + 1, s => by
    simp [take]
    induction s using recOn' <;> rfl
  | m' + 1, 0     , s => rfl
  | m' + 1, n' + 1, s => by
    simp [take]
    induction s using recOn' with
    | nil       => simp
    | cons a s' =>
      simp
      exact get?_take m' n' s'

/-- Split a sequence at `n`, producing a finite initial segment
  and an infinite tail. -/
def splitAt : ℕ → Seq' α → List α × Seq' α
  | 0, s => ([], s)
  | n + 1, s =>
    match dest s with
    | none => ([], nil)
    | some (x, s') =>
      let (l, r) := splitAt n s'
      (x :: l, r)
#align stream.seq.split_at Seq'.splitAt

@[simp]
theorem splitAt_eq_take_drop : ∀ (n : ℕ) (s : Seq' α), splitAt n s = (take n s, drop n s)
  | 0    , s => rfl
  | n + 1, s => by
    simp [splitAt, take]
    induction s using recOn' with
    | nil       => simp
    | cons a s' => simp [splitAt_eq_take_drop n s']

section ZipWith

/-- Combine two sequences with a function -/
def zipWith (f : α → β → γ) (s₁ : Seq' α) (s₂ : Seq' β) : Seq' γ :=
  ⟨ₛ[ Option.map₂ f (s₁.get? n) (s₂.get? n) | n ], fun {_} hn =>
    Option.map₂_eq_none_iff.2 <| (Option.map₂_eq_none_iff.1 hn).imp s₁.2 s₂.2⟩
#align stream.seq.zip_with Seq'.zipWith

variable {s : Seq' α} {s' : Seq' β} {n : ℕ}

@[simp]
theorem get?_zipWith (f : α → β → γ) (s s' n) :
    (zipWith f s s').get? n = Option.map₂ f (s.get? n) (s'.get? n) :=
  rfl
#align stream.seq.nth_zip_with Seq'.get?_zipWith

end ZipWith

/-- Pair two sequences into a sequence of pairs -/
def zip : Seq' α → Seq' β → Seq' (α × β) :=
  zipWith Prod.mk
#align stream.seq.zip Seq'.zip

theorem get?_zip (s : Seq' α) (t : Seq' β) (n : ℕ) :
    get? (zip s t) n = Option.map₂ Prod.mk (get? s n) (get? t n) :=
  get?_zipWith _ _ _ _
#align stream.seq.nth_zip Seq'.get?_zip

/-- Separate a sequence of pairs into two sequences -/
def unzip (s : Seq' (α × β)) : Seq' α × Seq' β :=
  (map Prod.fst s, map Prod.snd s)
#align stream.seq.unzip Seq'.unzip

/-- Enumerate a sequence by tagging each element with its index. -/
def enum (s : Seq' α) : Seq' (ℕ × α) :=
  Seq'.zip nats s
#align stream.seq.enum Seq'.enum

@[simp]
theorem get?_enum (s : Seq' α) (n : ℕ) : get? (enum s) n = Option.map (Prod.mk n) (get? s n) :=
  get?_zip _ _ _
#align stream.seq.nth_enum Seq'.get?_enum

@[simp]
theorem enum_nil : enum (nil : Seq' α) = nil :=
  rfl
#align stream.seq.enum_nil Seq'.enum_nil

/-- Convert a sequence which is known to terminate into a list -/
def toList (s : Seq' α) (h : s.Terminates) : List α :=
  take (Nat.find h) s
#align stream.seq.to_list Seq'.toList

@[simp]
theorem get?_toList {s : Seq' α} (h : s.Terminates) (n : ℕ) :
    List.get? (toList s h) n = get? s n := by
  simp [toList]
  intro m hmn ht
  symm; exact Seq.terminated_stable s hmn ht

@[simp, norm_cast]
theorem toList_ofList {l : List α} (h : (↑l : Seq' α).Terminates) : toList ↑l h = l := by
  ext1 n; rw [get?_toList, get?_ofList]

@[simp, norm_cast]
theorem ofList_toList {s : Seq' α} (h : s.Terminates) : (toList s h : List α) = s := by
  ext1 n; rw [get?_ofList, get?_toList]

instance : CanLift (Seq' α) (List α) (↑) (·.Terminates) where
  prf s h := ⟨toList s h, ofList_toList h⟩

/-- Convert a sequence which is known not to terminate into a stream -/
def toStream (s : Seq' α) (h : ¬s.Terminates) : Stream' α :=
  ₛ[ Option.get _ <| not_terminates_iff.1 h n | n ]
#align stream.seq.to_stream Seq'.toStream

@[simp]
theorem get_toStream {s : Seq' α} (h : ¬s.Terminates) (n : ℕ) :
    Stream'.get (toStream s h) n = Option.get (get? s n) (not_terminates_iff.1 h n) :=
  rfl

@[simp, norm_cast]
theorem toStream_ofStream {s : Stream' α} (h : ¬(↑s : Seq' α).Terminates) : toStream ↑s h = s :=
  rfl

@[simp, norm_cast]
theorem ofStream_toStream {s : Seq' α} (h : ¬s.Terminates) : (toStream s h : Seq' α) = s := by
  ext1 n; rw [ofStream_get?, get_toStream, Option.some_get]

instance : CanLift (Seq' α) (Stream' α) (↑) (¬·.Terminates) where
  prf s h := ⟨toStream s h, ofStream_toStream h⟩

/-- Convert a sequence into either a list or a stream depending on whether
  it is finite or infinite. (Without decidability of the infiniteness predicate,
  this is not constructively possible.) -/
@[simp]
def toListOrStream (s : Seq' α) [Decidable s.Terminates] : List α ⊕ Stream' α :=
  if h : s.Terminates then Sum.inl (toList s h) else Sum.inr (toStream s h)
#align stream.seq.to_list_or_stream Seq'.toListOrStream

open Classical in
/-- `Seq' α` is (noncomputably) equivalent to `List α ⊕ Stream' α` -/
@[simps]
noncomputable def _root_.Equiv.seqEquivListSumStream : Seq' α ≃ List α ⊕ Stream' α where
  toFun s := toListOrStream s
  invFun := Sum.elim (↑) (↑)
  left_inv s := by by_cases h : s.Terminates <;> simp [h]
  right_inv s := by cases s <;> simp

@[simp]
theorem nil_append (s : Seq' α) : nil ++ s = s := by
  apply coinduction2; intro s
  dsimp [append_def]; rw [dest_corec]
  dsimp [append_def]
  induction s using recOn' with
  | nil => trivial
  | cons x s =>
    rw [dest_cons]
    dsimp
    exact ⟨rfl, s, rfl, rfl⟩
#align stream.seq.nil_append Seq'.nil_append

@[simp]
theorem cons_append (a : α) (s t) : a ::ₑ s ++ t = a ::ₑ (s ++ t) :=
  dest_eq_cons <| by
    dsimp [append_def]; rw [dest_corec]
    dsimp [append_def]; rw [dest_cons]
#align stream.seq.cons_append Seq'.cons_append

@[simp]
theorem append_nil (s : Seq' α) : s ++ nil = s := by
  apply coinduction2 s; intro s
  induction s using recOn' with
  | nil => trivial
  | cons x s =>
    rw [cons_append, dest_cons, dest_cons]
    dsimp
    exact ⟨rfl, s, rfl, rfl⟩
#align stream.seq.append_nil Seq'.append_nil

@[simp]
theorem append_assoc (s t u : Seq' α) : s ++ t ++ u = s ++ (t ++ u) := by
  apply eq_of_bisim fun s1 s2 => ∃ s t u, s1 = s ++ t ++ u ∧ s2 = s ++ (t ++ u)
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, t, u, rfl, rfl⟩ => by
        induction' s using recOn' with _ s <;> simp
        · induction' t using recOn' with _ t <;> simp
          · induction' u using recOn' with _ u <;> simp
            · refine' ⟨nil, nil, u, _, _⟩ <;> simp
          · refine' ⟨nil, t, u, _, _⟩ <;> simp
        · exact ⟨s, t, u, rfl, rfl⟩
  · exact ⟨s, t, u, rfl, rfl⟩
#align stream.seq.append_assoc Seq'.append_assoc

@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl
#align stream.seq.map_nil Seq'.map_nil

@[simp]
theorem map_cons (f : α → β) (a) : ∀ s, map f (a ::ₑ s) = f a ::ₑ map f s
  | ⟨s, al⟩ => by apply Subtype.eq; dsimp [cons, map]; rw [Stream'.map_cons]; rfl
#align stream.seq.map_cons Seq'.map_cons

@[simp]
theorem map_id : ∀ s : Seq' α, map id s = s
  | ⟨s, al⟩ => by
    apply Subtype.eq; dsimp [map]
    rw [Option.map_id, Stream'.map_id]
#align stream.seq.map_id Seq'.map_id

@[simp]
theorem map_tail (f : α → β) : ∀ s, map f (tail s) = tail (map f s)
  | ⟨s, al⟩ => by apply Subtype.eq; dsimp [tail, map]
#align stream.seq.map_tail Seq'.map_tail

theorem map_comp (f : α → β) (g : β → γ) : ∀ s : Seq' α, map (g ∘ f) s = map g (map f s)
  | ⟨s, al⟩ => by
    apply Subtype.eq; dsimp [map]
    apply congr_arg fun f : _ → Option γ => Stream'.map f s
    ext ⟨⟩ <;> rfl
#align stream.seq.map_comp Seq'.map_comp

@[simp]
theorem map_append (f : α → β) (s t) : map f (s ++ t) = map f s ++ map f t := by
  apply
    eq_of_bisim (fun s1 s2 => ∃ s t, s1 = map f (s ++ t) ∧ s2 = map f s ++ map f t) _
      ⟨s, t, rfl, rfl⟩
  intro s1 s2 h
  exact
    match s1, s2, h with
    | _, _, ⟨s, t, rfl, rfl⟩ => by
      induction' s using recOn' with _ s <;> simp
      · induction' t using recOn' with _ t <;> simp
        · refine' ⟨nil, t, _, _⟩ <;> simp
      · exact ⟨s, t, rfl, rfl⟩
#align stream.seq.map_append Seq'.map_append

@[simp]
theorem map_get? (f : α → β) : ∀ s n, get? (map f s) n = (get? s n).map f
  | ⟨_, _⟩, _ => rfl
#align stream.seq.map_nth Seq'.map_get?

instance : Functor Seq' where map := @map

instance : LawfulFunctor Seq' where
  id_map := @map_id
  comp_map := @map_comp
  map_const := rfl

@[simp]
theorem map_eq_map {α β : Type u} (f : α → β) : Functor.map f = map f :=
  rfl

@[simp, norm_cast]
theorem ofList_map (f : α → β) (l : List α) : (List.map f l : Seq' β) = map f ↑l := by
  ext1 n; simp

@[simp, norm_cast]
theorem ofStream_map (f : α → β) (s : Stream' α) : (Stream'.map f s : Seq' β) = map f ↑s := by
  ext1 n; simp

@[simp]
theorem join_nil : join nil = (nil : Seq' α) :=
  dest_eq_nil rfl
#align stream.seq.join_nil Seq'.join_nil

--@[simp] -- porting note: simp can prove: `join_cons` is more general
theorem join_cons_nil (a : α) (S) : join ((a, nil) ::ₑ S) = a ::ₑ join S :=
  dest_eq_cons <| by simp [join]
#align stream.seq.join_cons_nil Seq'.join_cons_nil

--@[simp] -- porting note: simp can prove: `join_cons` is more general
theorem join_cons_cons (a b : α) (s S) :
    join ((a, b ::ₑ s) ::ₑ S) = a ::ₑ join ((b, s) ::ₑ S) :=
  dest_eq_cons <| by simp [join]
#align stream.seq.join_cons_cons Seq'.join_cons_cons

@[simp]
theorem join_cons (a : α) (s S) : join ((a, s) ::ₑ S) = a ::ₑ (s ++ (join S)) := by
  apply
    eq_of_bisim
      (fun s1 s2 => s1 = s2 ∨ ∃ a s S, s1 = join ((a, s) ::ₑ S) ∧ s2 = a ::ₑ (s ++ (join S)))
      _ (Or.inr ⟨a, s, S, rfl, rfl⟩)
  intro s1 s2 h
  exact
    match s1, s2, h with
    | s, _, Or.inl <| Eq.refl s => by
      induction s using recOn' with
      | nil => trivial
      | cons x s =>
        rw [dest_cons]
        exact ⟨rfl, Or.inl rfl⟩
    | _, _, Or.inr ⟨a, s, S, rfl, rfl⟩ => by
      induction s using recOn' with
      | nil => simp [join_cons_cons, join_cons_nil]
      | cons x s =>
        simp [join_cons_cons, join_cons_nil]
        refine' Or.inr ⟨x, s, S, rfl, rfl, rfl⟩
#align stream.seq.join_cons Seq'.join_cons

@[simp]
theorem join_append (S T : Seq' (Seq1 α)) : join (S ++ T) = join S ++ join T := by
  apply
    eq_of_bisim fun s1 s2 =>
      ∃ s S T, s1 = s ++ join (S ++ T) ∧ s2 = s ++ (join S ++ join T)
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, S, T, rfl, rfl⟩ => by
        induction' s using recOn' with _ s <;> simp
        · induction' S using recOn' with s S <;> simp
          · induction' T using recOn' with s T
            · simp
            · cases' s with a s; simp
              refine' ⟨s, nil, T, _, _⟩ <;> simp
          · cases' s with a s; simp
            exact ⟨s, S, T, rfl, rfl⟩
        · exact ⟨s, S, T, rfl, rfl⟩
  · refine' ⟨nil, S, T, _, _⟩ <;> simp
#align stream.seq.join_append Seq'.join_append

@[simp, norm_cast]
theorem ofStream_cons (a : α) (s) : (a ::ₛ s : Seq' α) = a ::ₑ ↑s := by
  apply Subtype.eq; simp [ofStream, cons]
#align stream.seq.of_stream_cons Seq'.ofStream_cons

@[simp, norm_cast]
theorem ofList_append (l l' : List α) : ((l ++ l' : List α) : Seq' α) = (l : Seq' α) ++ ↑l' := by
  induction l <;> simp [*]
#align stream.seq.of_list_append Seq'.ofList_append

@[simp, norm_cast]
theorem ofStream_append (l : List α) (s : Stream' α) :
    ((l ++ s : Stream' α) : Seq' α) = (l : Seq' α) ++ ↑s := by
  induction l <;> simp [*, Stream'.nil_append, Stream'.cons_append]
#align stream.seq.of_stream_append Seq'.ofStream_append

/-- Convert a sequence into a list, embedded in a computation to allow for
  the possibility of infinite sequences (in which case the computation
  never returns anything). -/
def toList' {α} (s : Seq' α) : Computation (List α) :=
  Computation.corec
    (fun ⟨l, s⟩ =>
      match dest s with
      | none => Sum.inl l.reverse
      | some (a, s') => Sum.inr (a :: l, s'))
    ([], s)
#align stream.seq.to_list' Seq'.toList'

theorem mem_map (f : α → β) {a : α} : ∀ {s : Seq' α}, a ∈ s → f a ∈ map f s
  | ⟨_, _⟩ => Stream'.mem_map (Option.map f)
#align stream.seq.mem_map Seq'.mem_map

theorem exists_of_mem_map {f} {b : β} : ∀ {s : Seq' α}, b ∈ map f s → ∃ a, a ∈ s ∧ f a = b :=
  fun {s} h => by match s with
  | ⟨g, al⟩ =>
    let ⟨o, om, oe⟩ := @Stream'.exists_of_mem_map _ _ (Option.map f) (some b) g h
    cases' o with a
    · injection oe
    · injection oe with h'; exact ⟨a, om, h'⟩
#align stream.seq.exists_of_mem_map Seq'.exists_of_mem_map

theorem of_mem_append {s₁ s₂ : Seq' α} {a : α} (h : a ∈ s₁ ++ s₂) : a ∈ s₁ ∨ a ∈ s₂ := by
  generalize e : s₁ ++ s₂ = ss at h
  induction h using mem_rec_on generalizing s₁ with
  | mem_cons s' =>
    induction s₁ using recOn' with
    | nil =>
      simp at e
      simp [e]
    | cons c t₁ =>
      simp at e
      simp [e]
  | @mem_cons_of_mem b s' m o =>
    induction s₁ using recOn' with
    | nil =>
      simp at e
      simp [e, m]
    | cons c t₁ =>
      simp at e
      rcases e with ⟨rfl, e⟩
      simp [o e, or_assoc]
#align stream.seq.of_mem_append Seq'.of_mem_append

theorem mem_append_left {s₁ s₂ : Seq' α} {a : α} (h : a ∈ s₁) : a ∈ s₁ ++ s₂ := by
  induction h using mem_rec_on <;> simp [*]
#align stream.seq.mem_append_left Seq'.mem_append_left

@[simp]
theorem enum_cons (s : Seq' α) (x : α) :
    enum (x ::ₑ s) = (0, x) ::ₑ map (Prod.map Nat.succ id) (enum s) := by
  ext ⟨n⟩ : 1
  · simp
  · simp only [get?_enum, get?_cons_succ, map_get?, Option.map_map]
    congr
#align stream.seq.enum_cons Seq'.enum_cons

end Seq'

namespace Seq1

variable {α : Type u} {β : Type v} {γ : Type w}

open Seq'

/-- Convert a `Seq1` to a sequence. -/
def toSeq' : Seq1 α → Seq' α
  | (a, s) => a ::ₑ s
#align stream.seq1.to_seq Seq1.toSeq

instance coeSeq' : Coe (Seq1 α) (Seq' α) :=
  ⟨toSeq⟩
#align stream.seq1.coe_seq Seq1.coeSeq

/-- Map a function on a `Seq1` -/
def map (f : α → β) : Seq1 α → Seq1 β
  | (a, s) => (f a, Seq.map f s)
#align stream.seq1.map Seq1.map

-- Porting note: New theorem.
theorem map_pair {f : α → β} {a s} : map f (a, s) = (f a, Seq.map f s) := rfl

theorem map_id : ∀ s : Seq1 α, map id s = s
  | ⟨a, s⟩ => by simp [map]
#align stream.seq1.map_id Seq1.map_id

/-- Flatten a nonempty sequence of nonempty sequences -/
def join : Seq1 (Seq1 α) → Seq1 α
  | ((a, s), S) =>
    match dest s with
    | none => (a, Seq.join S)
    | some s' => (a, Seq.join (s' ::ₑ S))
#align stream.seq1.join Seq1.join

@[simp]
theorem join_nil (a : α) (S) : join ((a, nil), S) = (a, Seq.join S) :=
  rfl
#align stream.seq1.join_nil Seq1.join_nil

@[simp]
theorem join_cons (a b : α) (s S) :
    join ((a, b ::ₑ s), S) = (a, Seq.join ((b, s) ::ₑ S)) := by
  dsimp [join]; rw [dest_cons]
#align stream.seq1.join_cons Seq1.join_cons

/-- The `pure` operator for the `Seq1` monad,
  which produces a singleton sequence. -/
def pure (a : α) : Seq1 α :=
  (a, nil)
#align stream.seq1.ret Seq1.pure

instance [Inhabited α] : Inhabited (Seq1 α) :=
  ⟨pure default⟩

/-- The `bind` operator for the `Seq1` monad,
  which maps `f` on each element of `s` and appends the results together.
  (Not all of `s` may be evaluated, because the first few elements of `s`
  may already produce an infinite result.) -/
def bind (s : Seq1 α) (f : α → Seq1 β) : Seq1 β :=
  join (map f s)
#align stream.seq1.bind Seq1.bind

@[simp]
theorem join_map_pure (s : Seq' α) : Seq.join (Seq.map pure s) = s := by
  apply coinduction2 s; intro s; induction s using recOn' <;> simp [pure]
#align stream.seq1.join_map_ret Seq1.join_map_pure

@[simp]
theorem bind_pure (f : α → β) : ∀ s, bind s (pure ∘ f) = map f s
  | ⟨a, s⟩ => by
    dsimp [bind, map]
    -- Porting note: Was `rw [map_comp]; simp [Function.comp, pure]`
    rw [map_comp, pure]
    simp
#align stream.seq1.bind_ret Seq1.bind_pure

@[simp]
theorem pure_bind (a : α) (f : α → Seq1 β) : bind (pure a) f = f a := by
  simp [pure, bind, map]
  cases' f a with a s
  induction s using recOn' <;> simp
#align stream.seq1.ret_bind Seq1.pure_bind

@[simp]
theorem map_join' (f : α → β) (S) : Seq.map f (Seq.join S) = Seq.join (Seq.map (map f) S) := by
  apply
    Seq.eq_of_bisim fun s1 s2 =>
      ∃ s S,
        s1 = s ++ Seq.map f (Seq.join S) ∧ s2 = s ++ Seq.join (Seq.map (map f) S)
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, S, rfl, rfl⟩ => by
        induction' s using recOn' with _ s <;> simp
        · induction' S using recOn' with x S <;> simp
          · cases' x with a s; simp [map]
            exact ⟨_, _, rfl, rfl⟩
        · exact ⟨s, S, rfl, rfl⟩
  · refine' ⟨nil, S, _, _⟩ <;> simp
#align stream.seq1.map_join' Seq1.map_join'

@[simp]
theorem map_join (f : α → β) : ∀ S, map f (join S) = join (map (map f) S)
  | ((a, s), S) => by induction s using recOn' <;> simp [map]
#align stream.seq1.map_join Seq1.map_join

@[simp]
theorem join_join (SS : Seq' (Seq1 (Seq1 α))) :
    Seq.join (Seq.join SS) = Seq.join (Seq.map join SS) := by
  apply
    Seq.eq_of_bisim fun s1 s2 =>
      ∃ s SS,
        s1 = s ++ Seq.join (Seq.join SS) ∧ s2 = s ++ Seq.join (Seq.map join SS)
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, SS, rfl, rfl⟩ => by
        induction' s using recOn' with _ s <;> simp
        · induction' SS using recOn' with S SS <;> simp
          · cases' S with s S; cases' s with x s; simp [map]
            induction' s using recOn' with x s <;> simp
            · exact ⟨_, _, rfl, rfl⟩
            · refine' ⟨x ::ₑ (s ++ Seq.join S), SS, _, _⟩ <;> simp
        · exact ⟨s, SS, rfl, rfl⟩
  · refine' ⟨nil, SS, _, _⟩ <;> simp
#align stream.seq1.join_join Seq1.join_join

@[simp]
theorem bind_assoc (s : Seq1 α) (f : α → Seq1 β) (g : β → Seq1 γ) :
    bind (bind s f) g = bind s fun x : α => bind (f x) g := by
  cases' s with a s
  -- Porting note: Was `simp [bind, map]`.
  simp only [bind, map_pair, map_join]
  rw [← map_comp]
  simp only [show (fun x => join (map g (f x))) = join ∘ (map g ∘ f) from rfl]
  rw [map_comp _ join]
  generalize Seq.map (map g ∘ f) s = SS
  rcases map g (f a) with ⟨⟨a, s⟩, S⟩
  induction' s using recOn' with x s_1 <;> induction' S using recOn' with x_1 s_2 <;> simp
  · cases' x_1 with x t
    induction t using recOn' <;> simp
  · cases' x_1 with y t; simp
#align stream.seq1.bind_assoc Seq1.bind_assoc

instance monad : Monad Seq1 where
  map := @map
  pure := @pure
  bind := @bind
#align stream.seq1.monad Seq1.monad

instance lawfulMonad : LawfulMonad Seq1 := LawfulMonad.mk'
  (id_map := @map_id)
  (bind_pure_comp := @bind_pure)
  (pure_bind := @pure_bind)
  (bind_assoc := @bind_assoc)
#align stream.seq1.is_lawful_monad Seq1.lawfulMonad

end Seq1
