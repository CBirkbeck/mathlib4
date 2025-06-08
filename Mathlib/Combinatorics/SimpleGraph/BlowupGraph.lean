/-
Copyright (c) 2025 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
  # Blow-up graphs and counting induced subgraphs
-/
namespace SimpleGraph

variable {ι : Type*} (H : SimpleGraph ι) --[DecidableRel H.Adj]
(V : ι → Type*) --[∀ i, DecidableEq (V i)]


/--
Given a family of vertex types indexed by `ι`, pulling back from `H : SimpleGraph ι`
yields the blow-up graph on the family. Two vertices are adjacent if and only if their
indices are adjacent in `H`.
-/
abbrev blowupGraph  : SimpleGraph (Σ i, V i) := SimpleGraph.comap Sigma.fst H

lemma blowupGraph_adj (x y : Σ i, V i) :
    (blowupGraph H V).Adj x y ↔ H.Adj (Sigma.fst x) (Sigma.fst y) := by rfl

lemma blowupGraph_not_adj_fst_eq {i : ι} (x y : V i) : ¬ (blowupGraph H V).Adj ⟨_, x⟩ ⟨_, y⟩ := by
  intro hf
  rw [blowupGraph_adj] at hf
  exact H.loopless i hf

lemma edgeSet_eq : H.edgeSet = {e | H.Adj e.out.1 e.out.2} := by
  ext e
  constructor <;> intro h <;>
  · change s(e.out.1, e.out.2) ∈ H.edgeSet at *
    convert h; ext; simp


lemma blowupGraph_edgeSet :
    (blowupGraph H V).edgeSet = {e | H.Adj (e.out.1.1) (e.out.2.1)} := edgeSet_eq _

/-- Embedding of `H` into `blowupGraph H V` with nonempty parts. -/
def blowupGraph.selfEmbedding (f : ∀ (i : ι), V i) :
    H ↪g (blowupGraph H V) := ⟨⟨fun i ↦ ⟨i, f i⟩, fun _ _ h ↦ (Sigma.mk.inj_iff.1 h).1⟩, by simp⟩

lemma blowupGraph_top : blowupGraph ⊤ V = completeMultipartiteGraph V := rfl

lemma blowupGraph_bot : blowupGraph ⊥ V = ⊥ := rfl

lemma blowupGraph_cliqueFree_iff  {n : ℕ} (f : ∀ i, (V i)) :
    H.CliqueFree n ↔ (blowupGraph H V).CliqueFree n := by
  constructor <;> intro h
  · rw [cliqueFree_iff, isEmpty_iff] at *
    intro e
    apply h
    use ⟨Sigma.fst ∘ e, fun a b (h : (e a).fst = (e b).fst) ↦ by
      by_contra!
      rw [← top_adj, ← e.map_adj_iff, blowupGraph_adj, h] at this
      exact H.loopless _ this⟩
    dsimp
    intros
    rw [← blowupGraph_adj, e.map_adj_iff]
  · exact h.comap (blowupGraph.selfEmbedding _ _ f)

lemma blowupGraph_colorable_iff {n : ℕ} (f : ∀ i, (V i)) :
    H.Colorable n ↔ (blowupGraph H V).Colorable n := by
  constructor <;> intro ⟨c⟩
  · exact ⟨fun x ↦ c x.fst, fun h1 h2 ↦ c.valid h1 h2⟩
  · exact ⟨fun x ↦ c ⟨x, f x⟩, by intro a b had; exact c.valid (by rwa [blowupGraph_adj])⟩

variable {α β ι : Type*} {k : ℕ}

/--
A `Flag α ι` consists of `G : SimpleGraph α` and a labelling of `ι` vertices of `G` by an
injective map `θ : ι ↪ α`. (We call this a `σ`-flag if the labelled subgraph is
`σ : SimpleGraph ι`).
-/
structure Flag (α ι : Type*) where
  G : SimpleGraph α
  θ : ι ↪ α
#check Embedding
/-- Added to prove `Fintype` instance later -/
def Flag_equiv_prod (α ι : Type*) : Flag α ι ≃ (SimpleGraph α) × (ι ↪ α) where
  toFun := fun F ↦ (F.G, F.θ)
  invFun := fun p ↦ { G := p.1, θ := p.2 }
  left_inv := fun F ↦ by cases F; rfl
  right_inv := fun p ↦ by cases p; rfl

/-- An embedding of flags is an embedding of the underlying graphs that preserves labels. -/
@[ext]
structure Flag.Embedding {α β ι : Type*} (F₁ : Flag α ι) (F₂ : Flag β ι) extends F₁.G ↪g F₂.G where
 labels : F₂.θ = toEmbedding ∘ F₁.θ

/-- An isomorphims of flags is an isomorphism of the underlying graphs that preserves labels. -/
@[ext]
structure Flag.Iso {α β ι : Type*} (F₁ : Flag α ι) (F₂ : Flag β ι) extends F₁.G ≃g F₂.G where
 labels : F₂.θ = toEquiv ∘ F₁.θ

@[inherit_doc] infixl:50 " ↪f " => Flag.Embedding
@[inherit_doc] infixl:50 " ≃f " => Flag.Iso

def Flag.Embedding_equiv {α β ι : Type*} (F₁ : Flag α ι) (F₂ : Flag β ι) :
    (F₁ ↪f F₂) ≃ {e : F₁.G ↪g F₂.G // F₂.θ = e ∘ F₁.θ} where
  toFun := fun e ↦ ⟨e.toRelEmbedding, e.labels⟩
  invFun := fun e ↦ ⟨e.val, e.2⟩
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

variable [Fintype α] [Fintype β] (G : SimpleGraph α) (H : SimpleGraph β)
#synth Fintype (G ↪g H)
noncomputable instance Flag.instfintypeOfEmbeddings {α β ι : Type*}  {F₁ : Flag α ι} {F₂ : Flag β ι}
    [Fintype α] [Fintype β] : Fintype (F₁ ↪f F₂) := by
  classical exact Fintype.ofEquiv _  (Flag.Embedding_equiv F₁ F₂).symm


variable {α β ι : Type*} {F₁ : Flag α ι} {F₂ : Flag β ι} {e : F₁ ↪f F₂}


lemma Flag.Iso_symm {α β ι : Type*} {F₁ : Flag α ι} {F₂ : Flag β ι} (e : F₁ ≃f F₂)
     : F₁.θ = e.symm ∘ F₂.θ := by
  ext x; simp [e.labels]

/--
`F` is a `σ`-flag iff the labelled subgraph given by `θ` is `σ`
-/
def Flag.IsSigma (F : Flag α ι) (σ : SimpleGraph ι) : Prop :=
  F.G.comap F.θ = σ

lemma Flag.isSigma_self (F : Flag α ι) : F.IsSigma (F.G.comap F.θ) := rfl

lemma Flag.isSigma_of_embedding {α β ι : Type*} {σ : SimpleGraph ι} {F₁ : Flag α ι}
    {F₂ : Flag β ι} (e : F₁ ↪f F₂)  (h1 : F₁.IsSigma σ) : F₂.IsSigma σ := by
  rw [IsSigma, e.labels, ← h1] at *
  ext; simp

variable {α ι  : Type*} [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]

noncomputable instance : Fintype (Flag α ι) :=  Fintype.ofEquiv _ (Flag_equiv_prod α ι).symm

open Classical in
/--
The Finset of all `σ`-flags with vertex type `α` (where both `α` and `ι` are finite).
-/
noncomputable def SigmaFlags (σ : SimpleGraph ι) : Finset (Flag α ι) := {F | F.IsSigma σ}

variable {k m n : ℕ}
local notation "‖" x "‖" => Fintype.card x

open Finset
/--
Embeddings of `H` in `G[t]` are equivalent to embeddings of `H` in `G` that map into `t`.
-/
def induceEquiv (G : SimpleGraph α) (H : SimpleGraph β) (t : Set α) : H ↪g (G.induce t) ≃
    {e : H ↪g G | Set.range e ⊆ t} where
  toFun := fun e ↦ ⟨Embedding.induce _|>.comp e, by rintro x ⟨y , rfl⟩; simp⟩
  invFun := fun e ↦ ⟨⟨(fun b ↦ ⟨_, e.2 ⟨b , rfl⟩⟩), fun _ _ _ ↦ e.1.inj' (by aesop)⟩,
                     by simp, by simp⟩
  left_inv := fun e ↦ by ext; simp
  right_inv := fun e ↦ by ext; simp

/--
Given `s : Finset α`, the number of super-sets of `s` of size `k` is `choose (‖α‖ - #s) (k - #s)`,
for `#s ≤ k`.
-/
lemma card_supersets {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α} (hk : #s ≤ k) :
    #{t : Finset α | #t = k ∧ s ⊆ t} = Nat.choose (‖α‖ - #s) (k - #s) := by
  simp_rw [← card_compl, ← card_powersetCard]
  apply card_nbij (i := (· \ s))
  · intro t ht
    simp only [mem_filter, mem_univ, true_and, mem_powersetCard] at *
    exact ⟨fun _ ↦ by simp, (ht.1 ▸ card_sdiff ht.2)⟩
  · intro t₁ ht1 t₂ ht2 he
    dsimp at he
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ht1 ht2
    rw [← sdiff_union_of_subset ht1.2, ← sdiff_union_of_subset ht2.2, he]
  · intro t ht
    simp only [mem_coe, mem_powersetCard] at ht
    use (t ∪ s)
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, subset_union_right, and_true]
    have hd := disjoint_left.2 fun _ ha hs ↦ (mem_compl.1 <| ht.1 ha) hs
    exact ⟨by rw [card_union_of_disjoint hd]; omega, union_sdiff_cancel_right hd⟩

/-- **The principle of counting induced subgraphs by averaging**
If `G` is a graph on `α` and `H` is a graph on `β`, then
`#(H ↪g G) * (choose (‖α‖ - ‖β‖) (k - ‖β‖))` is equal to the sum of the number of embeddings
`H ↪g (G.induce t)` over subsets `t` of `α` of size `k`, for any `‖β‖ ≤ k`.
-/
lemma sum_card_embeddings_induce_eq (G : SimpleGraph α) (H : SimpleGraph β) [Fintype β] {k : ℕ}
    (hk : ‖β‖ ≤ k) : ∑ t : Finset α with t.card = k , ‖H ↪g (G.induce t)‖
                              = ‖H ↪g G‖ * Nat.choose (‖α‖ - ‖β‖) (k - ‖β‖) := by
  classical
  calc
    _ = ∑ t : Finset α with t.card = k , ‖{e : H ↪g G | Set.range e ⊆ t}‖  := by
      simp_rw [Fintype.card_congr <| induceEquiv ..]
    _ = ∑ t : Finset α  with t.card = k, ∑ e : H ↪g G,
      ite (Set.range e ⊆ t) 1 0 := by
      congr; simp only [Set.coe_setOf, sum_boole, Nat.cast_id]
      ext t; apply Fintype.card_subtype
    _ = ∑ e : H ↪g G, ∑ t : Finset α with #t = k,
      ite (Set.range e ⊆ t) 1 0 := Finset.sum_comm
    _ = ∑ e : H ↪g G, ∑ t : Finset α with (#t = k ∧ Set.range e ⊆ t), 1 := by
      simp_rw [sum_ite, sum_const_zero, add_zero]
      congr; ext e; congr 1; ext s; simp
    _ = _ := by
      simp_rw [← card_eq_sum_ones]
      rw [← card_univ (α := (H ↪g G)), card_eq_sum_ones, sum_mul, one_mul]
      congr; ext e
      have hs : #((Set.range e).toFinset) = ‖β‖ := by
        simp_rw [Set.toFinset_range]
        apply card_image_of_injective _ (RelEmbedding.injective e)
      rw [← hs, ← card_supersets (hs ▸ hk)]
      congr
      ext t
      constructor <;> intro ⟨ht1, ht2⟩ <;> exact ⟨ht1, fun x hx ↦ ht2 (by simpa using hx)⟩

theorem monotoneOn_nat_Ici_of_le_succ {γ : Type*} [Preorder γ] {f : ℕ → γ} {k : ℕ}
    (hf : ∀ n ≥ k, f n ≤ f (n + 1)) :
    MonotoneOn f { x | k ≤ x } :=
  fun _ hab _ _ hle ↦ Nat.rel_of_forall_rel_succ_of_le_of_le (· ≤ ·) hf hab hle

theorem antitoneOn_nat_Ici_of_succ_le {γ : Type*} [Preorder γ]  {f : ℕ → γ} {k : ℕ}
    (hf : ∀ n ≥ k, f (n + 1) ≤ f n) :
    AntitoneOn f { x | k ≤ x } :=
  @monotoneOn_nat_Ici_of_le_succ γᵒᵈ _ f k hf

lemma antitoneOn_div_choose (e : ℕ → ℕ) (k : ℕ)
    (h : ∀ n, (n + 1 - k) * e (n + 1) ≤ (n + 1) * (e n)) :
    AntitoneOn (fun n ↦ (e n / n.choose k : ℚ)) {x | k ≤ x} := by
  apply antitoneOn_nat_Ici_of_succ_le
  intro n hₙ
  have hn := h n
  apply_fun (fun a ↦ (n.choose k) * a) at hn
  · dsimp at hn
    simp_rw [← mul_assoc, Nat.choose_mul_succ_eq] at hn
    have : (n.choose k) * (e (n + 1)) ≤ ((n + 1).choose k) * (e n) := by
      simp_rw [mul_comm _ (n + 1 - k), mul_assoc] at hn
      apply le_of_mul_le_mul_left hn (by omega)
    apply (div_le_div_iff₀ (mod_cast Nat.choose_pos (by omega))
              (mod_cast Nat.choose_pos (by omega))).2
    norm_cast
    simpa [mul_comm]
  · exact mul_left_mono

/--
The following version yields `(n + 1 - |V(H)|) * exᵢ(n + 1, H) ≤ (n + 1) * exᵢ(n, H)`, where
`exᵢ(n, H)` is the maximum number of embeddings `H` into any `n`-vertex graph `G`.
Which in turn implies that `{exᵢ(n + 1, H) / (n + 1).choose |V(H)|}`} is monotone decreasing in `n`.
In particular if `H = K₂` is an edge this implies that the standard induced-Turan density is
well-defined.
(This doesn't use anything about graphs, it would work as well in hypergraphs/multigraphs/flags..)
-/
lemma sum_card_embeddings_induce_n {n : ℕ} (G : SimpleGraph (Fin (n + 1))) (H : SimpleGraph β)
  [Fintype β] : ∑ t : Finset (Fin (n + 1)) with t.card = n , ‖H ↪g (G.induce t)‖
                              = ‖H ↪g G‖ *(n + 1 - ‖β‖) := by
  by_cases hk : ‖β‖ ≤ n
  · rw [sum_card_embeddings_induce_eq G H hk, Fintype.card_fin]
    have : n + 1 - ‖β‖ = n - ‖β‖ + 1 := by omega
    rw [this, Nat.choose_succ_self_right]
  · push_neg at hk
    have : n + 1 - ‖β‖ = 0 := by omega
    rw [this, mul_zero]
    convert sum_const_zero
    apply Fintype.card_eq_zero_iff.2 <| isEmpty_iff.2
      fun e ↦ (Fintype.card_le_of_embedding e.toEmbedding).not_lt (by simp_all)

def topBoolEmbeddingDartsEquiv (G : SimpleGraph α) : ((⊤ : SimpleGraph Bool) ↪g G) ≃ G.Dart where
  toFun := fun e ↦ ⟨⟨e true, e false⟩, by simp⟩
  invFun := fun d ↦ ⟨⟨fun i ↦
    match i with
    | true => d.1.1
    | false => d.1.2,
    fun i j h ↦ by
    cases i <;> cases j <;> dsimp at h <;> try rfl
    · exact (G.loopless _ (h ▸ d.adj)).elim
    · exact (G.loopless _ (h ▸ d.adj)).elim⟩,
    by intro i j; cases i <;> cases j <;> simp [d.adj.symm]⟩
  left_inv := fun e ↦ by ext a; cases a <;> simp
  right_inv := fun d ↦ rfl

omit [DecidableEq α] in
lemma card_embedding_top_two_eq_twice_card_edges (G : SimpleGraph α)
    [DecidableRel G.Adj] : ‖(⊤ : SimpleGraph Bool) ↪g G‖ = 2 * #G.edgeFinset :=
  (Fintype.card_congr G.topBoolEmbeddingDartsEquiv).trans <| dart_card_eq_twice_card_edges _

lemma card_edgeFinset_eq_average {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] :
    ∑ t : Finset (Fin (n + 1)) with t.card = n , #(G.induce t).edgeFinset =
    #G.edgeFinset * (n - 1) := by
  apply_fun (fun a ↦ 2 * a)
  · dsimp; rw [mul_sum, ← mul_assoc]
    simp_rw [← card_embedding_top_two_eq_twice_card_edges]
    rw [sum_card_embeddings_induce_n G (⊤ : SimpleGraph Bool)]
    simp
  · intro a b hab; simpa using hab

open Finset Fintype

section IsExtremal

variable {α γ : Type*} [Fintype α] [Fintype γ] {G : SimpleGraph α} [DecidableRel G.Adj]
{H : SimpleGraph γ} [DecidableRel H.Adj]

/--
`G` is an exᵢ graph satisfying `p` if `G` has the maximum number of induced copies of
`H` of any simple graph satisfying `p`.
-/
def IsExtremalH (G : SimpleGraph α) (H : SimpleGraph γ) [DecidableRel H.Adj]
  [DecidableRel G.Adj] (p : SimpleGraph α → Prop) :=
  p G ∧ ∀ ⦃G' : SimpleGraph α⦄ [DecidableRel G'.Adj], p G' → ‖H ↪g G'‖ ≤ ‖H ↪g G‖

lemma IsExtremalH.prop {p : SimpleGraph α → Prop} (h : G.IsExtremalH H p) : p G := h.1

open Classical in
/-- If one simple graph satisfies `p`, then there exists an extremal graph satisfying `p`. -/
theorem exists_isExtremalH_iff_exists (p : SimpleGraph α → Prop) :
    (∃ G : SimpleGraph α, ∃ _ : DecidableRel G.Adj, G.IsExtremalH H p) ↔ ∃ G, p G := by
  refine ⟨fun ⟨_, _, h⟩ ↦ ⟨_, h.1⟩, fun ⟨G, hp⟩ ↦ ?_⟩
  obtain ⟨G', hp', h⟩ := by
    apply exists_max_image { G | p G } (fun G ↦ ‖H ↪g G‖)
    use G, by simpa using hp
  use G', inferInstance
  exact ⟨by simpa using hp', fun _ _ hp ↦ by convert h _ (by simpa using hp)⟩

/-- If `F` has at least one edge, then there exists an extremal `F.Free` graph. -/
theorem exists_isExtremalH_free {β : Type*} {F : SimpleGraph β} (h : F ≠ ⊥) :
    ∃ G : SimpleGraph α, ∃ _ : DecidableRel G.Adj, G.IsExtremalH H F.Free :=
  (exists_isExtremalH_iff_exists F.Free).mpr ⟨⊥, free_bot h⟩

end IsExtremal

section ExtremalInduced

open Classical in
/--
The `exᵢ n H F` is the the maximum number of embeddings of `H` in an `F`-free graph on `n`
vertices, e.g. if `H = K₂` then this is twice the max number of edges in an `F`-free graph on `n`.
-/
noncomputable def extremalInduced (n : ℕ) {β γ : Type*} (H : SimpleGraph γ) (F : SimpleGraph β)
  [Fintype γ] : ℕ :=
  sup { G : SimpleGraph (Fin n) | F.Free G } (fun G ↦ ‖H ↪g G‖)
local notation "exᵢ" => extremalInduced
variable {n : ℕ} {β γ : Type*} [Fintype γ] {G : SimpleGraph α} {F : SimpleGraph β}
{H : SimpleGraph γ}

def Iso.embeddings_equiv_of_equiv {α' γ' : Type*} {G' : SimpleGraph α'} {H' : SimpleGraph γ'}
    (e : G ≃g G') (e' : H ≃g H') : (H ↪g G) ≃ (H' ↪g G') where
  toFun := fun f ↦ (e.toEmbedding.comp f).comp e'.symm.toEmbedding
  invFun := fun f ↦ (e.symm.toEmbedding.comp f).comp e'.toEmbedding
  left_inv := fun _ ↦ by ext; simp
  right_inv := fun _ ↦ by ext; simp

open Classical in
theorem extremalInduced_of_fintypeCard_eq (hc : card α = n) :
    exᵢ n H F = sup { G : SimpleGraph α | F.Free G } (fun G ↦ ‖H ↪g G‖) := by
  let e := Fintype.equivFinOfCardEq hc
  rw [extremalInduced, le_antisymm_iff]
  and_intros
  on_goal 1 =>
    replace e := e.symm
  all_goals
  rw [Finset.sup_le_iff]
  intro G h
  let G' := G.map e.toEmbedding
  replace h' : G' ∈ univ.filter (F.Free ·) := by
    rw [mem_filter, ← free_congr .refl (.map e G)]
    simpa using h
  convert @le_sup _ _ _ _ { G | F.Free G } (fun G ↦ ‖H ↪g G‖) G' h'
  exact Fintype.card_congr (Iso.embeddings_equiv_of_equiv (.map e G) (by rfl))

/--
If `G` is `F`-free, then `G` has at most `exᵢ (card α) F H` induced copies of `H`.
-/
theorem card_embeddings_le_extremalInduced (h : F.Free G) :
     ‖H ↪g G‖ ≤ exᵢ (card α) H F := by
  rw [extremalInduced_of_fintypeCard_eq rfl]
  convert @le_sup _ _ _ _ { G | F.Free G } (fun G ↦ ‖H ↪g G‖) G (by simpa using h)

/-- If `G` has more than `exᵢ (card V) H` edges, then `G` contains a copy of `H`. -/
theorem IsContained.of_extremalInduced_lt_card_embeddings
    (h : exᵢ (card α) H F <  ‖H ↪g G‖) : F ⊑ G := by
  contrapose! h
  exact card_embeddings_le_extremalInduced h

/-- `exᵢ (card V) H F` is at most `x` if and only if every `F`-free simple graph `G` has
at most `x` embeddings of `H`. -/
theorem extremalInduced_le_iff (F : SimpleGraph β) (m : ℕ) :
    exᵢ (card α) H F ≤ m ↔
      ∀ ⦃G : SimpleGraph α⦄ [DecidableRel G.Adj], F.Free G →  ‖H ↪g G‖ ≤ m := by
  simp_rw [extremalInduced_of_fintypeCard_eq rfl, Finset.sup_le_iff, mem_filter, mem_univ, true_and]
  classical
  exact ⟨fun h _ _ h' ↦ by convert h _ h', fun h _ h' ↦ h h'⟩

/-- `exᵢ (card V) F H` is greater than `x` if and only if there exists a `F`-free simple
graph `G` with more than `x` embeddings of `H`. -/
theorem lt_extremalInduced_iff (F : SimpleGraph β) (m : ℕ) :
    m < exᵢ (card α) H F ↔
      ∃ G : SimpleGraph α, ∃ _ : DecidableRel G.Adj, F.Free G ∧ m < ‖H ↪g G‖ := by
  simp_rw [extremalInduced_of_fintypeCard_eq rfl, Finset.lt_sup_iff, mem_filter, mem_univ, true_and]
  exact ⟨fun ⟨_, h, h'⟩ ↦ ⟨_, Classical.decRel _, h, h'⟩, fun ⟨_, _, h, h'⟩ ↦ ⟨_, h, by convert h'⟩⟩

variable {R : Type*} [Semiring R] [LinearOrder R] [FloorSemiring R]

@[inherit_doc extremalInduced_le_iff]
theorem extremalInduced_le_iff_of_nonneg (F : SimpleGraph β) {m : R} (h : 0 ≤ m) :
    exᵢ (card α) H F ≤ m ↔
      ∀ ⦃G : SimpleGraph α⦄ [DecidableRel G.Adj], F.Free G → ‖H ↪g G‖ ≤ m := by
  simp_rw [← Nat.le_floor_iff h]
  exact extremalInduced_le_iff F ⌊m⌋₊

@[inherit_doc lt_extremalInduced_iff]
theorem lt_extremalInduced_iff_of_nonneg (F : SimpleGraph β) {m : R} (h : 0 ≤ m) :
    m < exᵢ (card α) H F ↔
      ∃ G : SimpleGraph α, ∃ _ : DecidableRel G.Adj, F.Free G ∧ m < ‖H ↪g G‖ := by
  simp_rw [← Nat.floor_lt h]
  exact lt_extremalInduced_iff F ⌊m⌋₊

theorem IsContained.extremalInduced_le {β' : Type*} {F' : SimpleGraph β'} (h : F' ⊑ F) :
    exᵢ n H F' ≤ exᵢ n H F := by
  rw [← Fintype.card_fin n, extremalInduced_le_iff]
  intro _ _ h'
  contrapose! h'
  rw [not_not]
  exact h.trans (IsContained.of_extremalInduced_lt_card_embeddings h')

@[congr]
theorem extremalInduced_congr {n₁ n₂ : ℕ} {β₁ β₂ : Type*} {F₁ : SimpleGraph β₁}
    {F₂ : SimpleGraph β₂} (h : n₁ = n₂) (e₁ : F₁ ≃g F₂) :
    exᵢ n₁ H F₁  = exᵢ n₂ H F₂ := by
  rw [h, le_antisymm_iff]
  and_intros
  on_goal 2 =>
    replace e₁ := e₁.symm
  all_goals
    rw [← Fintype.card_fin n₂, extremalInduced_le_iff]
    intro G _ h
    apply card_embeddings_le_extremalInduced
    contrapose! h
    rw [not_free] at h ⊢
    exact h.trans' ⟨e₁.toCopy⟩

/-- If `H₁ ≃g H₂`, then `exᵢ n H₁ F` equals `exᵢ n H₂ F`. -/
theorem extremalInduced_congr_left {γ₁ γ₂ : Type*} {F : SimpleGraph β} {H₁ : SimpleGraph γ₁}
    {H₂ : SimpleGraph γ₂} [Fintype γ₁] [Fintype γ₂] (e : H₁ ≃g H₂) :
    exᵢ n H₁ F = exᵢ n H₂ F := by
  apply le_antisymm
  all_goals
    rw [← Fintype.card_fin n, extremalInduced_le_iff]
    intro G _ h
    classical
    apply (card_embeddings_le_extremalInduced h).trans'
    rw [Fintype.card_congr (Iso.embeddings_equiv_of_equiv (by rfl) (e.symm))]

/-- If `F₁ ≃g F₂`, then `exᵢ n F₁ H` equals `exᵢ n F₂ H`. -/
theorem extremalInduced_congr_right {β₁ β₂ : Type*} {F₁ : SimpleGraph β₁}
    {F₂ : SimpleGraph β₂} (e : F₁ ≃g F₂) : exᵢ n H F₁ = exᵢ n H F₂ :=
  extremalInduced_congr rfl e

variable [DecidableRel H.Adj] [DecidableRel G.Adj]
/-- `H`-free extremal graphs are `H`-free simple graphs having `exᵢ (card V) H` many
edges. -/
theorem isExtremalH_free_iff :
    G.IsExtremalH H F.Free ↔ F.Free G ∧ ‖H ↪g G‖ = exᵢ (card α) H F := by
  rw [IsExtremalH, and_congr_right_iff, ← extremalInduced_le_iff]
  exact fun h ↦ ⟨eq_of_le_of_le (card_embeddings_le_extremalInduced h), ge_of_eq⟩

lemma card_embeddings_of_isExtremalH_free (h : G.IsExtremalH H F.Free) :
    ‖H ↪g G‖ = exᵢ (card α) H F := (isExtremalH_free_iff.mp h).2


lemma antitone_extremalInduced_div_choose (H : SimpleGraph γ) (F : SimpleGraph β)
    [DecidableRel H.Adj] [DecidableRel F.Adj] :
    AntitoneOn (fun n ↦ (exᵢ n H F / n.choose ‖γ‖ : ℚ)) {x | ‖γ‖ ≤ x} := by
  apply antitoneOn_div_choose _ ‖γ‖
  intro n
  by_cases hn : n < ‖γ‖
  · have : n + 1 - ‖γ‖ = 0 := by omega
    simp [this]
  push_neg at hn
  have hp : 0 < (n : ℚ) + 1 - ‖γ‖ := by
    rw [← Nat.cast_add_one, ← Nat.cast_sub (by omega)]
    norm_cast; omega
  have : exᵢ (n + 1) H F ≤ ((((n + 1) * exᵢ n H F) : ℚ)/(n + 1 - ‖γ‖)) := by
    rw [← Fintype.card_fin (n + 1)]
    apply (extremalInduced_le_iff_of_nonneg F (α := (Fin (n + 1))) ?_).2
    · intro G hG hF
      rw [le_div_iff₀ hp]
      rw [← Nat.cast_add_one, ← Nat.cast_sub (by omega)]
      norm_cast
      calc
      _ = ∑ t : Finset (Fin (n + 1)) with t.card = n , ‖H ↪g (G.induce t)‖ :=
          (sum_card_embeddings_induce_n G H).symm
      _ ≤ _ := by
        rw [mul_comm]
        apply (sum_le_card_nsmul {t : Finset (Fin (n + 1)) | t.card = n} _ (exᵢ n H F) ?_).trans
        · simp [mul_comm]
        intro t ht
        simp only [univ_filter_card_eq, mem_powersetCard, subset_univ, true_and] at ht
        have : Fintype.card (( t.toSet): Type) = n := by simp [ht]
        simp_rw [← this]
        apply card_embeddings_le_extremalInduced
        intro hf
        exact hF <| hf.trans ⟨(Embedding.comap _ G).toHom, fun _ _ h ↦ by simpa using h⟩
    · apply div_nonneg (by norm_cast; omega) hp.le
  rw [← Nat.cast_add_one, ← Nat.cast_sub (by omega)] at this
  rw [le_div_iff₀ (mod_cast (by omega)), mul_comm] at this
  norm_cast at this

end ExtremalInduced
end SimpleGraph


-- /--
-- Given a `k`-set `s` in `[n + m + k]`, the number of `m + k` super-sets of `s` is
-- `choose (n + m) m`
-- -/

-- lemma card_superset {k m n : ℕ} {s t : Finset (Fin (n + m + k))} (hs : #s = k) (ht : #t = m + k):
--     s ⊆ t ↔ #(t \ s) = m := by
--   constructor <;> intro h
--   · rw [card_sdiff h]; omega
--   · have : #(t \ s) + #s = #t := by omega
--     rw [card_sdiff_add_card] at this
--     have : t = t ∪ s := by apply eq_of_subset_of_card_le subset_union_left this.le
--     exact left_eq_union.mp this

-- lemma card_supersets {k m n : ℕ} {s : Finset (Fin (n + m + k))} (hs : s.card = k) :
--     #{t : Finset (Fin (n + m + k)) | #t = m + k ∧ s ⊆ t} = Nat.choose (n + m) m := by
--   have : #(sᶜ) = n + m := by rw [card_compl, Fintype.card_fin]; omega
--   simp_rw [← this]
--   rw [← card_powersetCard]
--   apply card_nbij (i := fun t ↦ (t \ s))
--   · intro t ht
--     simp only [mem_filter, mem_univ, true_and] at ht
--     simp only [mem_powersetCard]
--     exact ⟨fun _ ↦ by simp, (card_superset hs ht.1).1 ht.2⟩
--   · intro t₁ ht1 t₂ ht2 he
--     dsimp at he
--     simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ht1 ht2
--     rw [← sdiff_union_of_subset ht1.2, ← sdiff_union_of_subset ht2.2, he]
--   · intro t ht
--     simp only [mem_coe, mem_powersetCard] at ht
--     use (t ∪ s)
--     simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, subset_union_right, and_true]
--     refine ⟨?_,?_⟩
--     · simp_rw [← hs,← ht.2]
--       exact card_union_of_disjoint <| disjoint_left.2 fun _ ha hs ↦ (mem_compl.1 <| ht.1 ha) hs
--     · rw [union_sdiff_cancel_right]
--       exact disjoint_left.2 fun _ ha hs ↦ (mem_compl.1 <| ht.1 ha) hs

-- /-- **The principle of counting subgraphs by averaging**
-- If `G` is a graph on `[n + m + k]` and `H` is a graph on `[k]`, then the number of embeddings
-- `#(H ↪g G) * (choose (n + m) m)` is equal to the sum of the number of embeddings
-- `H ↪g (G.induce t)`
-- over subsets `t` of `[n + m + k]` of size `m + k`.
-- -/
-- lemma sum_embeddings_induce_eq (G : SimpleGraph (Fin (n + m + k))) (H : SimpleGraph (Fin k)) :
--    ∑ t : Finset (Fin (n + m + k)) with t.card = m + k, ‖H ↪g (G.induce t)‖
--      = ‖H ↪g G‖ * Nat.choose (n + m) m := by
--   classical
--   calc
--     _ = ∑ t : Finset (Fin (n + m + k)) with t.card = m + k, ‖{e : H ↪g G | Set.range e ⊆ t}‖
--  := by
--       simp_rw [Fintype.card_congr <| induceEquiv ..]
--     _ = ∑ t : Finset (Fin (n + m + k)) with t.card = m + k, ∑ e : H ↪g G,
--       ite (Set.range e ⊆ t) 1 0 := by
--       congr; simp only [Set.coe_setOf, sum_boole, Nat.cast_id]
--       ext t; apply Fintype.card_subtype
--     _ = ∑ e : H ↪g G, ∑ t : Finset (Fin (n + m + k)) with #t =  m + k,
--       ite (Set.range e ⊆ t) 1 0 := Finset.sum_comm
--     _ = ∑ e : H ↪g G, ∑ t : Finset (Fin (n + m + k)) with (#t =  m + k ∧ Set.range e ⊆ t), 1
-- := by
--       simp_rw [sum_ite, sum_const_zero, add_zero]
--       congr; ext e; congr 1; ext s; simp
--     _ = _ := by
--       simp_rw [← card_eq_sum_ones]
--       rw [← card_univ, card_eq_sum_ones, sum_mul, one_mul]
--       congr; ext e
--       have hs : #((Set.range e).toFinset) = k := by
--         simp_rw [Set.toFinset_range, ← card_fin k]
--         apply card_image_of_injective _ (RelEmbedding.injective e)
--       rw [← card_supersets hs]
--       congr
--       ext t
--       constructor <;> intro ⟨ht1, ht2⟩ <;> exact ⟨ht1, fun x hx ↦ ht2 (by simpa using hx)⟩

-- lemma edges_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
--     2 * #G.edgeFinset = ‖(⊤ : SimpleGraph (Fin 2)) ↪g G‖ := by

--   sorry
