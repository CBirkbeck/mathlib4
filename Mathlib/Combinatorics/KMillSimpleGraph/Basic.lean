/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov, Hunter Monroe

! This file was ported from Lean 3 source module combinatorics.simple_graph.basic
! leanprover-community/mathlib commit c6ef6387ede9983aee397d442974e61f89dfd87b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Combinatorics.KMillSimpleGraph.Init
import Mathlib.Combinatorics.KMillDigraph.Basic
import Mathlib.Data.Rel
import Mathlib.Data.Set.Finite
import Mathlib.Data.Sym.Sym2

/-!
# Simple graphs

This module defines simple graphs on a vertex type `V` as an
irreflexive symmetric relation.

There is a basic API for locally finite graphs and for graphs with
finitely many vertices.

## Main definitions

* `SimpleGraph` is a structure for symmetric, irreflexive relations

* `SimpleGraph.neighborSet` is the `Set` of vertices adjacent to a given vertex

* `SimpleGraph.commonNeighbors` is the intersection of the neighbor sets of two given vertices

* `SimpleGraph.neighborFinset` is the `Finset` of vertices adjacent to a given vertex,
   if `neighborSet` is finite

* `SimpleGraph.incidenceSet` is the `Set` of edges containing a given vertex

* `SimpleGraph.incidenceFinset` is the `Finset` of edges containing a given vertex,
   if `incidenceSet` is finite

* `CompleteBooleanAlgebra` instance: Under the subgraph relation, `SimpleGraph` forms a
  `CompleteBooleanAlgebra`. In other words, this is the complete lattice of spanning subgraphs of
  the complete graph.

## Implementation notes

* A locally finite graph is one with instances `Π v, Fintype (G.neighborSet v)`.

* Given instances `DecidableRel (Adj G)` and `Fintype V`, then the graph
  is locally finite, too.

* Morphisms of graphs are abbreviations for `RelHom`, `RelEmbedding`, and `RelIso`.
  To make use of pre-existing simp lemmas, definitions involving morphisms are
  abbreviations as well.

## Naming Conventions

* If the vertex type of a graph is finite, we refer to its cardinality as `CardVerts`.

## Todo

* This is the simplest notion of an unoriented graph.  This should
  eventually fit into a more complete combinatorics hierarchy which
  includes multigraphs and directed graphs.  We begin with simple graphs
  in order to start learning what the combinatorics hierarchy should
  look like.
-/

-- porting note: using `aesop` for automation

-- porting note: These attributes are needed to use `aesop` as a replacement for `obviously`
attribute [aesop norm unfold (rule_sets [SimpleGraph])] Symmetric
attribute [aesop norm unfold (rule_sets [SimpleGraph])] Irreflexive

-- porting note: a thin wrapper around `aesop` for graph lemmas, modelled on `aesop_cat`
/--
A variant of the `aesop` tactic for use in the graph library. Changes relative
to standard `aesop`:

- We use the `SimpleGraph` rule set in addition to the default rule sets.
- We instruct Aesop's `intro` rule to unfold with `default` transparency.
- We instruct Aesop to fail if it can't fully solve the goal. This allows us to
  use `aesop_graph` for auto-params.
-/
macro (name := aesop_graph) "aesop_graph" c:Aesop.tactic_clause*: tactic =>
  `(tactic|
    aesop $c*
      (options := { introsTransparency? := some .default, terminal := true })
      (rule_sets [$(Lean.mkIdent `SimpleGraph):ident]))

/--
A variant of `aesop_graph` which does not fail if it is unable to solve the
goal. Use this only for exploration! Nonterminal Aesop is even worse than
nonterminal `simp`.
-/
macro (name := aesop_graph_nonterminal) "aesop_graph_nonterminal" c:Aesop.tactic_clause*: tactic =>
  `(tactic|
    aesop $c*
      (options := { introsTransparency? := some .default, warnOnNonterminal := false })
      (rule_sets [$(Lean.mkIdent `SimpleGraph):ident]))

open Finset Function Graph

universe u v w

/-- A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
@[aesop safe constructors (rule_sets [SimpleGraph])]
structure SimpleGraph (V : Type u) extends Digraph V where
  symm : Symmetric Adj := by aesop_graph
  loopless : Irreflexive Adj := by aesop_graph
-- porting note: changed `obviously` to `aesop` in the `structure`

instance : HasAdj (SimpleGraph V) (fun _ ↦ V) where
  Adj G := G.Adj

/- Perhaps there is an elaborator/delaborator that could help here. -/
@[simp] theorem SimpleGraph.adj_eq_adj (G : SimpleGraph V) : G.Adj = Adj G := rfl

@[simp] theorem SimpleGraph.adj_coe (G : SimpleGraph V) : Adj G.toDigraph = Adj G := rfl

/-- See Note [custom simps projection] -/
def SimpleGraph.Simps.Adj (G : SimpleGraph V) : V → V → Prop := Graph.Adj G

initialize_simps_projections SimpleGraph

instance : Graph.IsAdjSymmetric (SimpleGraph V) (fun _ ↦ V) := ⟨SimpleGraph.symm⟩

instance : Graph.IsAdjIrreflexive (SimpleGraph V) (fun _ ↦ V) := ⟨SimpleGraph.loopless⟩

@[simp]
theorem SimpleGraph.Adj_mk (G : Digraph V) (hs hi) :
    Adj (SimpleGraph.mk G hs hi) = Adj G := rfl

@[ext]
protected theorem SimpleGraph.ext (G H : SimpleGraph V) : Adj G = Adj H → G = H := by
  cases G; cases H; simp

/-- Constructor for simple graphs using a symmetric irreflexive boolean function. -/
@[simps]
def SimpleGraph.mk' :
    {adj : V → V → Bool // (∀ x y, adj x y = adj y x) ∧ (∀ x, ¬ adj x x)} ↪ SimpleGraph V where
  toFun x := ⟨⟨fun v w ↦ x.1 v w⟩, fun v w ↦ by simp [x.2.1], fun v ↦ by simp [x.2.2]⟩
  inj' := by
    rintro ⟨adj, _⟩ ⟨adj', _⟩
    simp only [mk.injEq, Digraph.mk.injEq, Subtype.mk.injEq]
    intro h
    funext v w
    simpa [Bool.coe_bool_iff] using congr_fun₂ h v w

instance {V : Type u} [Fintype V] [DecidableEq V] : Fintype (SimpleGraph V) where
  elems := Finset.univ.map SimpleGraph.mk'
  complete := by
    classical
    rintro ⟨⟨Adj⟩, hs, hi⟩
    simp only [mem_map, mem_univ, true_and, Subtype.exists, Bool.not_eq_true]
    refine ⟨fun v w ↦ Adj v w, ⟨?_, ?_⟩, ?_⟩
    · intro v w; dsimp at hs; simpa using hs.iff v w
    · dsimp at hi; intro v; simpa using hi v
    · ext
      simp

/-- Construct the simple graph induced by the given relation. It
symmetrizes the relation and makes it irreflexive. -/
def SimpleGraph.fromRel {V : Type u} (r : V → V → Prop) : SimpleGraph V
    where
  Adj a b := a ≠ b ∧ (r a b ∨ r b a)
  symm := fun _ _ ⟨hn, hr⟩ => ⟨hn.symm, hr.symm⟩
  loopless := fun _ ⟨hn, _⟩ => hn rfl

@[simp]
theorem SimpleGraph.fromRel_adj {V : Type u} (r : V → V → Prop) (v w : V) :
    Adj (SimpleGraph.fromRel r) v w ↔ v ≠ w ∧ (r v w ∨ r w v) :=
  Iff.rfl

-- porting note: attributes needed for `completeGraph`
attribute [aesop safe (rule_sets [SimpleGraph])] Ne.symm
attribute [aesop safe (rule_sets [SimpleGraph])] Ne.irrefl

/-- The complete graph on a type `V` is the simple graph with all pairs of distinct vertices
adjacent. In `Mathlib`, this is usually referred to as `⊤`. -/
def completeGraph (V : Type u) : SimpleGraph V where Adj := Ne

/-- The graph with no edges on a given vertex type `V`. `Mathlib` prefers the notation `⊥`. -/
def emptyGraph (V : Type u) : SimpleGraph V where Adj _ _ := False

/-- Two vertices are adjacent in the complete bipartite graph on two vertex types
if and only if they are not from the same side.
Bipartite graphs in general may be regarded as being subgraphs of one of these.

TODO also introduce complete multi-partite graphs, where the vertex type is a sigma type of an
indexed family of vertex types
-/
@[simps]
def completeBipartiteGraph (V W : Type _) : SimpleGraph (Sum V W)
    where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft
  symm := by
    intro v w
    cases v <;> cases w <;> simp
  loopless := by
    intro v
    cases v <;> simp

namespace SimpleGraph

variable {ι : Sort _} {𝕜 : Type _} {V : Type u} {W : Type v} {X : Type w} (G : SimpleGraph V)
  (G' : SimpleGraph W) {a b c u v w : V} {e : Sym2 V}

theorem ne_of_adj (h : Adj G a b) : a ≠ b := by
  rintro rfl
  exact adj_irrefl G h

theorem ne_of_adj_of_not_adj {v w x : V} (h : Adj G v x) (hn : ¬Adj G w x) : v ≠ w := fun h' =>
  hn (h' ▸ h)

theorem adj_injective : Injective (fun (G : SimpleGraph V) => Adj G) :=
  SimpleGraph.ext

@[simp]
theorem adj_inj {G H : SimpleGraph V} : Adj G = Adj H ↔ G = H :=
  adj_injective.eq_iff

section Order

/-- The relation that one `SimpleGraph` is a subgraph of another.
Note that this should be spelled `≤`. -/
def IsSubgraph (G H : SimpleGraph V) : Prop :=
  ∀ ⦃v w : V⦄, Adj G v w → Adj H v w

instance : LE (SimpleGraph V) :=
  ⟨IsSubgraph⟩

@[simp]
theorem isSubgraph_eq_le : (IsSubgraph : SimpleGraph V → SimpleGraph V → Prop) = (· ≤ ·) :=
  rfl

/-- The supremum of two graphs `G ⊔ H` has edges where either `G` or `H` have edges. -/
instance : Sup (SimpleGraph V) where
  sup G H :=
    { Adj := Adj G ⊔ Adj H
      symm := fun v w h => by change _ ∨ _; rwa [adj_comm G, adj_comm H]
      -- Porting note: aesop was able to do this before Adj refactor:
      loopless := fun v => by change ¬ (_ ∨ _); simp [adj_irrefl] }

@[simp]
theorem sup_adj (G H : SimpleGraph V) (v w : V) : Adj (G ⊔ H) v w ↔ Adj G v w ∨ Adj H v w := Iff.rfl

/-- The infimum of two graphs `G ⊓ H` has edges where both `G` and `H` have edges. -/
instance : Inf (SimpleGraph V) where
  inf G H :=
    { Adj := Adj G ⊓ Adj H
      symm := fun v w h => by change _ ∧ _; rwa [adj_comm G, adj_comm H]
      -- Porting note: aesop was able to do this before Adj refactor
      loopless := fun v => by change ¬ (_ ∧ _); simp [adj_irrefl] }

@[simp]
theorem inf_adj (G H : SimpleGraph V) (v w : V) : Adj (G ⊓ H) v w ↔ Adj G v w ∧ Adj H v w := Iff.rfl

/-- We define `Gᶜ` to be the `SimpleGraph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent
(still ensuring that vertices are not adjacent to themselves). -/
instance hasCompl : HasCompl (SimpleGraph V) where
  compl G :=
    { Adj := fun v w => v ≠ w ∧ ¬Adj G v w
      symm := fun v w ⟨hne, _⟩ => ⟨hne.symm, by rwa [adj_comm]⟩
      loopless := fun v ⟨hne, _⟩ => (hne rfl).elim }

@[simp]
theorem compl_adj (G : SimpleGraph V) (v w : V) : Adj (Gᶜ) v w ↔ v ≠ w ∧ ¬ Adj G v w := Iff.rfl

/-- The difference of two graphs `G \ H` has the edges of `G` with the edges of `H` removed. -/
instance sdiff : SDiff (SimpleGraph V) where
  sdiff G H :=
    { Adj := Adj G \ Adj H
      symm := fun v w h => by change _ ∧ ¬_; rwa [adj_comm G, adj_comm H]
      loopless := fun v => by change ¬(_ ∧ ¬_); simp [adj_irrefl] }

@[simp]
theorem sdiff_adj (v w : V) : Adj (G \ H) v w ↔ Adj G v w ∧ ¬ Adj H v w :=
  Iff.rfl

instance supSet : SupSet (SimpleGraph V) where
  sSup s :=
    { Adj := fun a b => ∃ G ∈ s, Adj G a b
      symm := fun a b => Exists.imp $ fun _ => And.imp_right (adj_symm _)
      loopless := by
        rintro a ⟨G, _, ha⟩
        exact ha.ne rfl }

instance infSet : InfSet (SimpleGraph V) where
  sInf s :=
    { Adj := fun a b => (∀ ⦃G⦄, G ∈ s → Adj G a b) ∧ a ≠ b
      symm := fun _ _ => And.imp (forall₂_imp fun _ _ => adj_symm _) Ne.symm
      loopless := fun _ h => h.2 rfl }

@[simp]
theorem sSup_adj {s : Set (SimpleGraph V)} {a b : V} : Adj (sSup s) a b ↔ ∃ G ∈ s, Adj G a b :=
  Iff.rfl

@[simp]
theorem sInf_adj {s : Set (SimpleGraph V)} : Adj (sInf s) a b ↔ (∀ G ∈ s, Adj G a b) ∧ a ≠ b :=
  Iff.rfl

@[simp]
theorem iSup_adj {f : ι → SimpleGraph V} : Adj (⨆ i, f i) a b ↔ ∃ i, Adj (f i) a b := by simp [iSup]

@[simp]
theorem iInf_adj {f : ι → SimpleGraph V} : Adj (⨅ i, f i) a b ↔ (∀ i, Adj (f i) a b) ∧ a ≠ b := by
  simp [iInf]

theorem sInf_adj_of_nonempty {s : Set (SimpleGraph V)} (hs : s.Nonempty) :
    Adj (sInf s) a b ↔ ∀ G ∈ s, Adj G a b :=
  sInf_adj.trans <|
    and_iff_left_of_imp <| by
      obtain ⟨G, hG⟩ := hs
      exact fun h => (h _ hG).ne

theorem iInf_adj_of_nonempty [Nonempty ι] {f : ι → SimpleGraph V} :
    Adj (⨅ i, f i) a b ↔ ∀ i, Adj (f i) a b := by
  rw [iInf, sInf_adj_of_nonempty (Set.range_nonempty _), Set.forall_range_iff]

/-- For graphs `G`, `H`, we have `G ≤ H` iff `∀ a b, Adj G a b → Adj H a b`. -/
instance distribLattice : DistribLattice (SimpleGraph V) :=
  { show DistribLattice (SimpleGraph V) from
      adj_injective.distribLattice _ (fun _ _ => rfl) fun _ _ => rfl with
    le := IsSubgraph }

instance completeBooleanAlgebra : CompleteBooleanAlgebra (SimpleGraph V) :=
  { SimpleGraph.distribLattice with
    le := (· ≤ ·)
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    compl := HasCompl.compl
    sdiff := (· \ ·)
    top := completeGraph V
    bot := emptyGraph V
    le_top := fun x v w h => x.ne_of_adj h
    bot_le := fun x v w h => h.elim
    sdiff_eq := fun x y => by
      ext (v w)
      refine' ⟨fun h => ⟨h.1, ⟨_, h.2⟩⟩, fun h => ⟨h.1, h.2.2⟩⟩
      rintro rfl
      exact adj_irrefl x h.1
    inf_compl_le_bot := fun G v w h => False.elim <| h.2.2 h.1
    top_le_sup_compl := fun G v w hvw => by
      by_cases Adj G v w
      · exact Or.inl h
      · exact Or.inr ⟨hvw, h⟩
    sSup := sSup
    le_sSup := fun s G hG a b hab => ⟨G, hG, hab⟩
    sSup_le := fun s G hG a b => by
      rintro ⟨H, hH, hab⟩
      exact hG _ hH hab
    sInf := sInf
    sInf_le := fun s G hG a b hab => hab.1 hG
    le_sInf := fun s G hG a b hab => ⟨fun H hH => hG _ hH hab, hab.ne⟩
    inf_sSup_le_iSup_inf := fun G s a b hab => by simpa using hab
    iInf_sup_le_sup_sInf := fun G s a b hab => by
      simpa [forall_and, forall_or_left, or_and_right, and_iff_left_of_imp (ne_of_adj _)]
        using hab }

@[simp]
theorem top_adj (v w : V) : Adj (⊤ : SimpleGraph V) v w ↔ v ≠ w :=
  Iff.rfl

@[simp]
theorem bot_adj (v w : V) : Adj (⊥ : SimpleGraph V) v w ↔ False :=
  Iff.rfl

@[simp]
theorem completeGraph_eq_top (V : Type u) : completeGraph V = ⊤ :=
  rfl

@[simp]
theorem emptyGraph_eq_bot (V : Type u) : emptyGraph V = ⊥ :=
  rfl

@[simps]
instance (V : Type u) : Inhabited (SimpleGraph V) :=
  ⟨⊥⟩

section Decidable

variable (V) (H : SimpleGraph V) [DecidableRel (Adj G)] [DecidableRel (Adj H)]

instance Bot.adjDecidable : DecidableRel (Adj (⊥ : SimpleGraph V)) :=
  inferInstanceAs <| DecidableRel fun _ _ => False

instance Sup.adjDecidable : DecidableRel (Adj (G ⊔ H)) :=
  inferInstanceAs <| DecidableRel fun v w => Adj G v w ∨ Adj H v w

instance Inf.adjDecidable : DecidableRel (Adj (G ⊓ H)) :=
  inferInstanceAs <| DecidableRel fun v w => Adj G v w ∧ Adj H v w

instance Sdiff.adjDecidable : DecidableRel (Adj (G \ H)) :=
  inferInstanceAs <| DecidableRel fun v w => Adj G v w ∧ ¬Adj H v w

variable [DecidableEq V]

instance Top.adjDecidable : DecidableRel (Adj (⊤ : SimpleGraph V)) :=
  inferInstanceAs <| DecidableRel fun v w => v ≠ w

instance Compl.adjDecidable : DecidableRel (Adj (Gᶜ)) :=
  inferInstanceAs <| DecidableRel fun v w => v ≠ w ∧ ¬Adj G v w

end Decidable

end Order

/-- `G.support` is the set of vertices that form edges in `G`. -/
def support : Set V := Rel.dom (Adj G)

theorem mem_support {v : V} : v ∈ G.support ↔ ∃ w, Adj G v w :=
  Iff.rfl

theorem support_mono {G G' : SimpleGraph V} (h : G ≤ G') : G.support ⊆ G'.support :=
  Rel.dom_mono h

/-- `G.neighborSet v` is the set of vertices adjacent to `v` in `G`. -/
def neighborSet (v : V) : Set V := {w | Adj G v w}

instance neighborSet.memDecidable (v : V) [DecidableRel (Adj G)] :
    DecidablePred (· ∈ G.neighborSet v) :=
  inferInstanceAs <| DecidablePred (Adj G v)

section EdgeSet

variable {G₁ G₂ : SimpleGraph V}

/-- The edges of G consist of the unordered pairs of vertices related by
`Adj G`. This is the order embedding; for the edge set of a particular graph, see
`SimpleGraph.edgeSet`.

The way `edgeSet` is defined is such that `mem_edgeSet` is proved by `refl`.
(That is, `⟦(v, w)⟧ ∈ G.edgeSet` is definitionally equal to `Adj G v w`.)
-/
-- porting note: We need a separate definition so that dot notation works.
def edgeSetEmbedding (V : Type _) : SimpleGraph V ↪o Set (Sym2 V) :=
  OrderEmbedding.ofMapLEIff (fun G => Sym2.fromRel G.symm) fun _ _ =>
    ⟨fun h a b => @h ⟦(a, b)⟧, fun h e => Sym2.ind @h e⟩

/-- `G.edgeSet` is the edge set for `G`.
This is an abbreviation for `edgeSetEmbedding G` that permits dot notation. -/
abbrev edgeSet (G : SimpleGraph V) : Set (Sym2 V) := edgeSetEmbedding V G


@[simp]
theorem mem_edgeSet : ⟦(v, w)⟧ ∈ G.edgeSet ↔ Adj G v w :=
  Iff.rfl

theorem not_isDiag_of_mem_edgeSet : e ∈ edgeSet G → ¬e.IsDiag :=
  Sym2.ind (fun _ _ => ne_of_adj G) e

theorem edgeSet_inj : G₁.edgeSet = G₂.edgeSet ↔ G₁ = G₂ := (edgeSetEmbedding V).eq_iff_eq

@[simp]
theorem edgeSet_subset_edgeSet : edgeSet G₁ ⊆ edgeSet G₂ ↔ G₁ ≤ G₂ :=
  (edgeSetEmbedding V).le_iff_le

@[simp]
theorem edgeSet_ssubset_edgeSet : edgeSet G₁ ⊂ edgeSet G₂ ↔ G₁ < G₂ :=
  (edgeSetEmbedding V).lt_iff_lt

theorem edgeSet_injective : Injective (edgeSet : SimpleGraph V → Set (Sym2 V)) :=
  (edgeSetEmbedding V).injective

alias edgeSet_subset_edgeSet ↔ _ edgeSet_mono

alias edgeSet_ssubset_edgeSet ↔ _ edgeSet_strict_mono

attribute [mono] edgeSet_mono edgeSet_strict_mono

variable (G₁ G₂)

@[simp]
theorem edgeSet_bot : (⊥ : SimpleGraph V).edgeSet = ∅ :=
  Sym2.fromRel_bot

@[simp]
theorem edgeSet_sup : (G₁ ⊔ G₂).edgeSet = G₁.edgeSet ∪ G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl

@[simp]
theorem edgeSet_inf : (G₁ ⊓ G₂).edgeSet = G₁.edgeSet ∩ G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl

@[simp]
theorem edgeSet_sdiff : (G₁ \ G₂).edgeSet = G₁.edgeSet \ G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl

/-- This lemma, combined with `edgeSet_sdiff` and `edgeSet_from_edgeSet`,
allows proving `(G \ from_edgeSet s).edge_set = G.edgeSet \ s` by `simp`. -/
@[simp]
theorem edgeSet_sdiff_sdiff_isDiag (G : SimpleGraph V) (s : Set (Sym2 V)) :
    G.edgeSet \ (s \ { e | e.IsDiag }) = G.edgeSet \ s := by
  ext e
  simp only [Set.mem_diff, Set.mem_setOf_eq, not_and, not_not, and_congr_right_iff]
  intro h
  simp only [G.not_isDiag_of_mem_edgeSet h, imp_false]

/-- Two vertices are adjacent iff there is an edge between them. The
condition `v ≠ w` ensures they are different endpoints of the edge,
which is necessary since when `v = w` the existential
`∃ (e ∈ G.edgeSet), v ∈ e ∧ w ∈ e` is satisfied by every edge
incident to `v`. -/
theorem adj_iff_exists_edge {v w : V} : Adj G v w ↔ v ≠ w ∧ ∃ e ∈ G.edgeSet, v ∈ e ∧ w ∈ e := by
  refine' ⟨fun _ => ⟨G.ne_of_adj ‹_›, ⟦(v, w)⟧, by simpa⟩, _⟩
  rintro ⟨hne, e, he, hv⟩
  rw [Sym2.mem_and_mem_iff hne] at hv
  subst e
  rwa [mem_edgeSet] at he

theorem adj_iff_exists_edge_coe : Adj G a b ↔ ∃ e : G.edgeSet, e.val = ⟦(a, b)⟧ := by
  simp only [mem_edgeSet, exists_prop, SetCoe.exists, exists_eq_right, Subtype.coe_mk]

theorem edge_other_ne {e : Sym2 V} (he : e ∈ G.edgeSet) {v : V} (h : v ∈ e) :
    Sym2.Mem.other h ≠ v := by
  erw [← Sym2.other_spec h, Sym2.eq_swap] at he
  exact G.ne_of_adj he

instance decidableMemEdgeSet [DecidableRel (Adj G)] : DecidablePred (· ∈ G.edgeSet) :=
  Sym2.fromRel.decidablePred G.symm

instance fintypeEdgeSet [Fintype (Sym2 V)] [DecidableRel (Adj G)] : Fintype G.edgeSet :=
  Subtype.fintype _

instance fintypeEdgeSetBot : Fintype (⊥ : SimpleGraph V).edgeSet := by
  rw [edgeSet_bot]
  infer_instance

instance fintypeEdgeSetSup [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ ⊔ G₂).edgeSet := by
  rw [edgeSet_sup]
  infer_instance

instance fintypeEdgeSetInf [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ ⊓ G₂).edgeSet := by
  rw [edgeSet_inf]
  exact Set.fintypeInter _ _

instance fintypeEdgeSetSdiff [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ \ G₂).edgeSet := by
  rw [edgeSet_sdiff]
  exact Set.fintypeDiff _ _

end EdgeSet

section FromEdgeSet

variable (s : Set (Sym2 V))

/-- `fromEdgeSet` constructs a `SimpleGraph` from a set of edges, without loops. -/
def fromEdgeSet : SimpleGraph V where
  Adj := Sym2.ToRel s ⊓ Ne
  symm v w h := ⟨Sym2.toRel_symmetric s h.1, h.2.symm⟩

@[simp]
theorem fromEdgeSet_adj : Adj (fromEdgeSet s) v w ↔ ⟦(v, w)⟧ ∈ s ∧ v ≠ w :=
  Iff.rfl

-- Note: we need to make sure `fromEdgeSet_adj` and this lemma are confluent.
-- In particular, both yield `⟦(u, v)⟧ ∈ (fromEdgeSet s).edgeSet` ==> `⟦(v, w)⟧ ∈ s ∧ v ≠ w`.
@[simp]
theorem edgeSet_fromEdgeSet : (fromEdgeSet s).edgeSet = s \ { e | e.IsDiag } := by
  ext e
  exact Sym2.ind (by simp) e

@[simp]
theorem fromEdgeSet_edgeSet : fromEdgeSet G.edgeSet = G := by
  ext (v w)
  exact ⟨fun h => h.1, fun h => ⟨h, G.ne_of_adj h⟩⟩

@[simp]
theorem fromEdgeSet_empty : fromEdgeSet (∅ : Set (Sym2 V)) = ⊥ := by
  ext (v w)
  simp only [fromEdgeSet_adj, Set.mem_empty_iff_false, false_and_iff, bot_adj]

@[simp]
theorem fromEdgeSet_univ : fromEdgeSet (Set.univ : Set (Sym2 V)) = ⊤ := by
  ext (v w)
  simp only [fromEdgeSet_adj, Set.mem_univ, true_and_iff, top_adj]

@[simp]
theorem fromEdgeSet_inf (s t : Set (Sym2 V)) :
    fromEdgeSet s ⊓ fromEdgeSet t = fromEdgeSet (s ∩ t) := by
  ext (v w)
  simp only [fromEdgeSet_adj, Set.mem_inter_iff, Ne.def, inf_adj]
  tauto

@[simp]
theorem fromEdgeSet_sup (s t : Set (Sym2 V)) :
    fromEdgeSet s ⊔ fromEdgeSet t = fromEdgeSet (s ∪ t) := by
  ext (v w)
  simp [Set.mem_union, or_and_right]

@[simp]
theorem fromEdgeSet_sdiff (s t : Set (Sym2 V)) :
    fromEdgeSet s \ fromEdgeSet t = fromEdgeSet (s \ t) := by
  ext (v w)
  constructor <;> simp (config := { contextual := true })

@[mono]
theorem fromEdgeSet_mono {s t : Set (Sym2 V)} (h : s ⊆ t) : fromEdgeSet s ≤ fromEdgeSet t := by
  rintro v w
  simp (config := { contextual := true }) only [fromEdgeSet_adj, Ne.def, not_false_iff,
    and_true_iff, and_imp]
  exact fun vws _ => h vws

instance [DecidableEq V] [Fintype s] : Fintype (fromEdgeSet s).edgeSet := by
  rw [edgeSet_fromEdgeSet s]
  infer_instance

end FromEdgeSet

/-! ## Darts -/

section Darts

variable {G}

/-- The edge associated to the dart. -/
def _root_.Graph.Dart.edge (d : Dart G) : Sym2 V :=
  ⟦d.toProd⟧

@[simp]
theorem Dart.edge_mk {p : V × V} (h : Adj G p.1 p.2) : (Dart.mk p h).edge = ⟦p⟧ :=
  rfl

@[simp]
theorem _root_.Graph.Dart.edge_mem (d : Dart G) : d.edge ∈ G.edgeSet :=
  d.is_adj

/-- The dart with reversed orientation from a given dart. -/
@[simps]
def _root_.Graph.Dart.symm (d : Dart G) : Dart G :=
  ⟨d.toProd.swap, G.symm d.is_adj⟩

@[simp]
theorem Dart.symm_mk {p : V × V} (h : Adj G p.1 p.2) : (Dart.mk p h).symm = Dart.mk p.swap h.symm :=
  rfl

@[simp]
theorem Dart.edge_symm (d : Dart G) : d.symm.edge = d.edge :=
  Sym2.mk''_prod_swap_eq

@[simp]
theorem Dart.edge_comp_symm : Dart.edge ∘ Dart.symm = (Dart.edge : Dart G → Sym2 V) :=
  funext Dart.edge_symm

@[simp]
theorem Dart.symm_symm (d : Dart G) : d.symm.symm = d :=
  Dart.ext _ _ <| Prod.swap_swap _

@[simp]
theorem Dart.symm_involutive : Function.Involutive (Dart.symm : Dart G → Dart G) :=
  Dart.symm_symm

theorem Dart.symm_ne (d : Dart G) : d.symm ≠ d :=
  ne_of_apply_ne (Prod.snd ∘ Dart.toProd) d.is_adj.ne

theorem dart_edge_eq_iff : ∀ d₁ d₂ : Dart G, d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.symm := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  simp [Sym2.mk''_eq_mk''_iff, -Quotient.eq]

theorem dart_edge_eq_mk'_iff :
    ∀ {d : Dart G} {p : V × V}, d.edge = ⟦p⟧ ↔ d.toProd = p ∨ d.toProd = p.swap := by
  rintro ⟨p, h⟩
  apply Sym2.mk''_eq_mk''_iff

theorem dart_edge_eq_mk'_iff' :
    ∀ {d : Dart G} {u v : V},
      d.edge = ⟦(u, v)⟧ ↔ d.fst = u ∧ d.snd = v ∨ d.fst = v ∧ d.snd = u := by
  rintro ⟨⟨a, b⟩, h⟩ u v
  rw [dart_edge_eq_mk'_iff]
  simp

variable (G)

/-- Two darts are said to be adjacent if they could be consecutive
darts in a walk -- that is, the first dart's second vertex is equal to
the second dart's first vertex. -/
def DartAdj (d d' : Dart G) : Prop := d.snd = d'.fst

/-- For a given vertex `v`, this is the bijective map from the neighbor set at `v`
to the darts `d` with `d.fst = v`. -/
@[simps]
def dartOfNeighborSet (v : V) (w : G.neighborSet v) : Dart G :=
  ⟨(v, w), w.property⟩

theorem dartOfNeighborSet_injective (v : V) : Function.Injective (G.dartOfNeighborSet v) :=
  fun e₁ e₂ h =>
  Subtype.ext <| by
    injection h with h'
    convert congr_arg Prod.snd h'

instance nonempty_dart_top [Nontrivial V] : Nonempty (Dart (⊤ : SimpleGraph V)) := by
  obtain ⟨v, w, h⟩ := exists_pair_ne V
  exact ⟨⟨(v, w), h⟩⟩

end Darts

/-! ### Incidence set -/

/-- Set of edges incident to a given vertex, aka incidence set. -/
def incidenceSet (v : V) : Set (Sym2 V) :=
  { e ∈ G.edgeSet | v ∈ e }

theorem incidenceSet_subset (v : V) : G.incidenceSet v ⊆ G.edgeSet := fun _ h => h.1

theorem mk'_mem_incidenceSet_iff : ⟦(b, c)⟧ ∈ G.incidenceSet a ↔ Adj G b c ∧ (a = b ∨ a = c) :=
  and_congr_right' Sym2.mem_iff

theorem mk'_mem_incidenceSet_left_iff : ⟦(a, b)⟧ ∈ G.incidenceSet a ↔ Adj G a b :=
  and_iff_left <| Sym2.mem_mk''_left _ _

theorem mk'_mem_incidenceSet_right_iff : ⟦(a, b)⟧ ∈ G.incidenceSet b ↔ Adj G a b :=
  and_iff_left <| Sym2.mem_mk''_right _ _

theorem edge_mem_incidenceSet_iff {e : G.edgeSet} : ↑e ∈ G.incidenceSet a ↔ a ∈ (e : Sym2 V) :=
  and_iff_right e.2

theorem incidenceSet_inter_incidenceSet_subset (h : a ≠ b) :
    G.incidenceSet a ∩ G.incidenceSet b ⊆ {⟦(a, b)⟧} := fun _e he =>
  (Sym2.mem_and_mem_iff h).1 ⟨he.1.2, he.2.2⟩

theorem incidenceSet_inter_incidenceSet_of_adj (h : Adj G a b) :
    G.incidenceSet a ∩ G.incidenceSet b = {⟦(a, b)⟧} := by
  refine' (G.incidenceSet_inter_incidenceSet_subset <| h.ne).antisymm _
  rintro _ (rfl : _ = ⟦(a, b)⟧)
  exact ⟨G.mk'_mem_incidenceSet_left_iff.2 h, G.mk'_mem_incidenceSet_right_iff.2 h⟩

theorem adj_of_mem_incidenceSet (h : a ≠ b) (ha : e ∈ G.incidenceSet a)
    (hb : e ∈ G.incidenceSet b) : Adj G a b := by
  rwa [← mk'_mem_incidenceSet_left_iff, ←
    Set.mem_singleton_iff.1 <| G.incidenceSet_inter_incidenceSet_subset h ⟨ha, hb⟩]

theorem incidenceSet_inter_incidenceSet_of_not_adj (h : ¬Adj G a b) (hn : a ≠ b) :
    G.incidenceSet a ∩ G.incidenceSet b = ∅ := by
  simp_rw [Set.eq_empty_iff_forall_not_mem, Set.mem_inter_iff, not_and]
  intro u ha hb
  exact h (G.adj_of_mem_incidenceSet hn ha hb)

instance decidableMemIncidenceSet [DecidableEq V] [DecidableRel (Adj G)] (v : V) :
    DecidablePred (· ∈ G.incidenceSet v) :=
  inferInstanceAs <| DecidablePred fun e => e ∈ G.edgeSet ∧ v ∈ e

section EdgeFinset

variable {G₁ G₂ : SimpleGraph V} [Fintype G.edgeSet] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]

/-- The `edgeSet` of the graph as a `Finset`. -/
@[reducible]
def edgeFinset : Finset (Sym2 V) :=
  Set.toFinset G.edgeSet

@[norm_cast]
theorem coe_edgeFinset : (G.edgeFinset : Set (Sym2 V)) = G.edgeSet :=
  Set.coe_toFinset _

variable {G}

theorem mem_edgeFinset : e ∈ G.edgeFinset ↔ e ∈ G.edgeSet :=
  Set.mem_toFinset

theorem not_isDiag_of_mem_edgeFinset : e ∈ G.edgeFinset → ¬e.IsDiag :=
  not_isDiag_of_mem_edgeSet _ ∘ mem_edgeFinset.1

theorem edgeFinset_inj : G₁.edgeFinset = G₂.edgeFinset ↔ G₁ = G₂ := by simp

theorem edgeFinset_subset_edgeFinset : G₁.edgeFinset ⊆ G₂.edgeFinset ↔ G₁ ≤ G₂ := by simp

theorem edgeFinset_ssubset_edgeFinset : G₁.edgeFinset ⊂ G₂.edgeFinset ↔ G₁ < G₂ := by simp

alias edgeFinset_subset_edgeFinset ↔ _ edgeFinset_mono

alias edgeFinset_ssubset_edgeFinset ↔ _ edgeFinset_strict_mono

attribute [mono] edgeFinset_mono edgeFinset_strict_mono

@[simp]
theorem edgeFinset_bot : (⊥ : SimpleGraph V).edgeFinset = ∅ := by simp [edgeFinset]

@[simp]
theorem edgeFinset_sup [DecidableEq V] : (G₁ ⊔ G₂).edgeFinset = G₁.edgeFinset ∪ G₂.edgeFinset := by
  simp [edgeFinset]

@[simp]
theorem edgeFinset_inf [DecidableEq V] : (G₁ ⊓ G₂).edgeFinset = G₁.edgeFinset ∩ G₂.edgeFinset := by
  simp [edgeFinset]

@[simp]
theorem edgeFinset_sdiff [DecidableEq V] : (G₁ \ G₂).edgeFinset = G₁.edgeFinset \ G₂.edgeFinset :=
  by simp [edgeFinset]

theorem edgeFinset_card : G.edgeFinset.card = Fintype.card G.edgeSet :=
  Set.toFinset_card _

@[simp]
theorem edgeSet_univ_card : (univ : Finset G.edgeSet).card = G.edgeFinset.card :=
  Fintype.card_of_subtype G.edgeFinset fun _ => mem_edgeFinset

end EdgeFinset

@[simp]
theorem mem_neighborSet (v w : V) : w ∈ G.neighborSet v ↔ Adj G v w :=
  Iff.rfl

@[simp]
theorem mem_incidenceSet (v w : V) : ⟦(v, w)⟧ ∈ G.incidenceSet v ↔ Adj G v w := by
  simp [incidenceSet]

theorem mem_incidence_iff_neighbor {v w : V} : ⟦(v, w)⟧ ∈ G.incidenceSet v ↔ w ∈ G.neighborSet v :=
  by simp only [mem_incidenceSet, mem_neighborSet]

theorem adj_incidenceSet_inter {v : V} {e : Sym2 V} (he : e ∈ G.edgeSet) (h : v ∈ e) :
    G.incidenceSet v ∩ G.incidenceSet (Sym2.Mem.other h) = {e} := by
  ext e'
  simp only [incidenceSet, Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
  refine' ⟨fun h' => _, _⟩
  · rw [← Sym2.other_spec h]
    exact (Sym2.mem_and_mem_iff (edge_other_ne G he h).symm).mp ⟨h'.1.2, h'.2.2⟩
  · rintro rfl
    exact ⟨⟨he, h⟩, he, Sym2.other_mem _⟩

theorem compl_neighborSet_disjoint (G : SimpleGraph V) (v : V) :
    Disjoint (G.neighborSet v) (Gᶜ.neighborSet v) := by
  rw [Set.disjoint_iff]
  rintro w ⟨h, h'⟩
  rw [mem_neighborSet, compl_adj] at h'
  exact h'.2 h

theorem neighborSet_union_compl_neighborSet_eq (G : SimpleGraph V) (v : V) :
    G.neighborSet v ∪ Gᶜ.neighborSet v = {v}ᶜ := by
  ext w
  have h := @ne_of_adj _ G
  simp_rw [Set.mem_union, mem_neighborSet, compl_adj, Set.mem_compl_iff, Set.mem_singleton_iff]
  tauto

theorem card_neighborSet_union_compl_neighborSet [Fintype V] (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v ∪ Gᶜ.neighborSet v : Set V)] :
    (Set.toFinset (G.neighborSet v ∪ Gᶜ.neighborSet v)).card = Fintype.card V - 1 := by
  classical simp_rw [neighborSet_union_compl_neighborSet_eq, Set.toFinset_compl,
      Finset.card_compl, Set.toFinset_card, Set.card_singleton]

theorem neighborSet_compl (G : SimpleGraph V) (v : V) :
    Gᶜ.neighborSet v = G.neighborSet vᶜ \ {v} := by
  ext w
  simp [and_comm, eq_comm]

/-- The set of common neighbors between two vertices `v` and `w` in a graph `G` is the
intersection of the neighbor sets of `v` and `w`. -/
def commonNeighbors (v w : V) : Set V :=
  G.neighborSet v ∩ G.neighborSet w

theorem commonNeighbors_eq (v w : V) : G.commonNeighbors v w = G.neighborSet v ∩ G.neighborSet w :=
  rfl

theorem mem_commonNeighbors {u v w : V} : u ∈ G.commonNeighbors v w ↔ Adj G v u ∧ Adj G w u :=
  Iff.rfl

theorem commonNeighbors_symm (v w : V) : G.commonNeighbors v w = G.commonNeighbors w v :=
  Set.inter_comm _ _

theorem not_mem_commonNeighbors_left (v w : V) : v ∉ G.commonNeighbors v w := fun h =>
  ne_of_adj G h.1 rfl

theorem not_mem_commonNeighbors_right (v w : V) : w ∉ G.commonNeighbors v w := fun h =>
  ne_of_adj G h.2 rfl

theorem commonNeighbors_subset_neighborSet_left (v w : V) :
    G.commonNeighbors v w ⊆ G.neighborSet v :=
  Set.inter_subset_left _ _

theorem commonNeighbors_subset_neighborSet_right (v w : V) :
    G.commonNeighbors v w ⊆ G.neighborSet w :=
  Set.inter_subset_right _ _

instance decidableMemCommonNeighbors [DecidableRel (Adj G)] (v w : V) :
    DecidablePred (· ∈ G.commonNeighbors v w) :=
  inferInstanceAs <| DecidablePred fun u => u ∈ G.neighborSet v ∧ u ∈ G.neighborSet w

theorem commonNeighbors_top_eq {v w : V} :
    (⊤ : SimpleGraph V).commonNeighbors v w = Set.univ \ {v, w} := by
  ext u
  simp [commonNeighbors, eq_comm, not_or]

section Incidence

variable [DecidableEq V]

/-- Given an edge incident to a particular vertex, get the other vertex on the edge. -/
def otherVertexOfIncident {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) : V :=
  Sym2.Mem.other' h.2

theorem edge_other_incident_set {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) :
    e ∈ G.incidenceSet (G.otherVertexOfIncident h) := by
  use h.1
  simp [otherVertexOfIncident, Sym2.other_mem']

theorem incidence_other_prop {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) :
    G.otherVertexOfIncident h ∈ G.neighborSet v := by
  cases' h with he hv
  rwa [← Sym2.other_spec' hv, mem_edgeSet] at he

-- Porting note: as a simp lemma this does not apply even to itself
theorem incidence_other_neighbor_edge {v w : V} (h : w ∈ G.neighborSet v) :
    G.otherVertexOfIncident (G.mem_incidence_iff_neighbor.mpr h) = w :=
  Sym2.congr_right.mp (Sym2.other_spec' (G.mem_incidence_iff_neighbor.mpr h).right)

/-- There is an equivalence between the set of edges incident to a given
vertex and the set of vertices adjacent to the vertex. -/
@[simps]
def incidenceSetEquivNeighborSet (v : V) : G.incidenceSet v ≃ G.neighborSet v
    where
  toFun e := ⟨G.otherVertexOfIncident e.2, G.incidence_other_prop e.2⟩
  invFun w := ⟨⟦(v, w.1)⟧, G.mem_incidence_iff_neighbor.mpr w.2⟩
  left_inv x := by simp [otherVertexOfIncident]
  right_inv := fun ⟨w, hw⟩ => by
    simp only [mem_neighborSet, Subtype.mk.injEq]
    exact incidence_other_neighbor_edge _ hw

end Incidence

/-! ## Edge deletion -/


/-- Given a set of vertex pairs, remove all of the corresponding edges from the
graph's edge set, if present.

See also: `SimpleGraph.Subgraph.deleteEdges`. -/
def deleteEdges (s : Set (Sym2 V)) : SimpleGraph V
    where
  Adj := Adj G \ Sym2.ToRel s
  symm a b := by simp [adj_comm, Sym2.eq_swap]
  loopless a := by simp [SDiff.sdiff] -- porting note: used to be handled by `obviously`

@[simp]
theorem deleteEdges_adj (s : Set (Sym2 V)) (v w : V) :
    Adj (G.deleteEdges s) v w ↔ Adj G v w ∧ ¬⟦(v, w)⟧ ∈ s :=
  Iff.rfl

theorem sdiff_eq_deleteEdges (G G' : SimpleGraph V) : G \ G' = G.deleteEdges G'.edgeSet := by
  ext
  simp

theorem deleteEdges_eq_sdiff_fromEdgeSet (s : Set (Sym2 V)) :
    G.deleteEdges s = G \ fromEdgeSet s := by
  ext
  exact ⟨fun h => ⟨h.1, not_and_of_not_left _ h.2⟩, fun h => ⟨h.1, not_and'.mp h.2 h.ne⟩⟩

theorem compl_eq_deleteEdges : Gᶜ = (⊤ : SimpleGraph V).deleteEdges G.edgeSet := by
  ext
  simp

@[simp]
theorem deleteEdges_deleteEdges (s s' : Set (Sym2 V)) :
    (G.deleteEdges s).deleteEdges s' = G.deleteEdges (s ∪ s') := by
  ext
  simp [and_assoc, not_or]

@[simp]
theorem deleteEdges_empty_eq : G.deleteEdges ∅ = G := by
  ext
  simp

@[simp]
theorem deleteEdges_univ_eq : G.deleteEdges Set.univ = ⊥ := by
  ext
  simp

theorem deleteEdges_le (s : Set (Sym2 V)) : G.deleteEdges s ≤ G := by
  intro
  simp (config := { contextual := true })

theorem deleteEdges_le_of_le {s s' : Set (Sym2 V)} (h : s ⊆ s') :
    G.deleteEdges s' ≤ G.deleteEdges s := fun v w => by
  simp (config := { contextual := true }) only [deleteEdges_adj, and_imp, true_and_iff]
  exact fun _ hn hs => hn (h hs)

theorem deleteEdges_eq_inter_edgeSet (s : Set (Sym2 V)) :
    G.deleteEdges s = G.deleteEdges (s ∩ G.edgeSet) := by
  ext
  simp (config := { contextual := true }) [imp_false]

theorem deleteEdges_sdiff_eq_of_le {H : SimpleGraph V} (h : H ≤ G) :
    G.deleteEdges (G.edgeSet \ H.edgeSet) = H := by
  ext (v w)
  constructor <;> simp (config := { contextual := true }) [@h v w]

theorem edgeSet_deleteEdges (s : Set (Sym2 V)) : (G.deleteEdges s).edgeSet = G.edgeSet \ s := by
  ext e
  refine' Sym2.ind _ e
  simp

-- porting note: added `Fintype (Sym2 V)` argument rather than have it be inferred.
-- As a consequence, deleted the `Fintype V` argument.
theorem edgeFinset_deleteEdges [Fintype (Sym2 V)] [DecidableEq V] [DecidableRel (Adj G)]
    (s : Finset (Sym2 V)) [DecidableRel (Adj (G.deleteEdges s))] :
    (G.deleteEdges s).edgeFinset = G.edgeFinset \ s := by
  ext e
  simp [edgeSet_deleteEdges]

section DeleteFar

-- porting note: added `Fintype (Sym2 V)` argument.
variable [OrderedRing 𝕜] [Fintype V] [Fintype (Sym2 V)] [DecidableEq V] [DecidableRel (Adj G)]
  {p : SimpleGraph V → Prop} {r r₁ r₂ : 𝕜}

/-- A graph is `r`-*delete-far* from a property `p` if we must delete at least `r` edges from it to
get a graph with the property `p`. -/
def DeleteFar (p : SimpleGraph V → Prop) (r : 𝕜) : Prop :=
  ∀ ⦃s⦄, s ⊆ G.edgeFinset → p (G.deleteEdges s) → r ≤ s.card

open Classical

variable {G}

theorem deleteFar_iff :
    G.DeleteFar p r ↔ ∀ ⦃H⦄, H ≤ G → p H → r ≤ G.edgeFinset.card - H.edgeFinset.card := by
  refine' ⟨fun h H hHG hH => _, fun h s hs hG => _⟩
  · have := h (sdiff_subset G.edgeFinset H.edgeFinset)
    simp only [deleteEdges_sdiff_eq_of_le _ hHG, edgeFinset_mono hHG, card_sdiff,
      card_le_of_subset, coe_sdiff, coe_edgeFinset, Nat.cast_sub] at this
    exact this hH
  · simpa [card_sdiff hs, edgeFinset_deleteEdges, -Set.toFinset_card, Nat.cast_sub,
      card_le_of_subset hs] using h (G.deleteEdges_le s) hG

alias deleteFar_iff ↔ DeleteFar.le_card_sub_card _

theorem DeleteFar.mono (h : G.DeleteFar p r₂) (hr : r₁ ≤ r₂) : G.DeleteFar p r₁ := fun _ hs hG =>
  hr.trans <| h hs hG

end DeleteFar

/-! ## Map and comap -/


/-- Given an injective function, there is an covariant induced map on graphs by pushing forward
the adjacency relation.

This is injective (see `SimpleGraph.map_injective`). -/
protected def map (f : V ↪ W) (G : SimpleGraph V) : SimpleGraph W where
  Adj := Relation.Map (Adj G) f f
  symm a b := by -- porting note: `obviously` used to handle this
    rintro ⟨v, w, h, rfl, rfl⟩
    use w, v, h.symm, rfl
  loopless a := by -- porting note: `obviously` used to handle this
    rintro ⟨v, w, h, rfl, h'⟩
    exact h.ne (f.injective h'.symm)

@[simp]
theorem map_adj (f : V ↪ W) (G : SimpleGraph V) (u v : W) :
    Adj (G.map f) u v ↔ ∃ u' v' : V, Adj G u' v' ∧ f u' = u ∧ f v' = v :=
  Iff.rfl

theorem map_monotone (f : V ↪ W) : Monotone (SimpleGraph.map f) := by
  rintro G G' h _ _ ⟨u, v, ha, rfl, rfl⟩
  exact ⟨_, _, h ha, rfl, rfl⟩

/-- Given a function, there is a contravariant induced map on graphs by pulling back the
adjacency relation.
This is one of the ways of creating induced graphs. See `SimpleGraph.induce` for a wrapper.

This is surjective when `f` is injective (see `SimpleGraph.comap_surjective`).-/
@[simps]
protected def comap (f : V → W) (G : SimpleGraph W) : SimpleGraph V where
  Adj u v := Adj G (f u) (f v)
  symm _ _ h := h.symm
  loopless _ := G.loopless _

theorem comap_monotone (f : V ↪ W) : Monotone (SimpleGraph.comap f) := by
  intro G G' h _ _ ha
  exact h ha

@[simp]
theorem comap_map_eq (f : V ↪ W) (G : SimpleGraph V) : (G.map f).comap f = G := by
  ext
  simp

theorem leftInverse_comap_map (f : V ↪ W) :
    Function.LeftInverse (SimpleGraph.comap f) (SimpleGraph.map f) :=
  comap_map_eq f

theorem map_injective (f : V ↪ W) : Function.Injective (SimpleGraph.map f) :=
  (leftInverse_comap_map f).injective

theorem comap_surjective (f : V ↪ W) : Function.Surjective (SimpleGraph.comap f) :=
  (leftInverse_comap_map f).surjective

theorem map_le_iff_le_comap (f : V ↪ W) (G : SimpleGraph V) (G' : SimpleGraph W) :
    G.map f ≤ G' ↔ G ≤ G'.comap f :=
  ⟨fun h u v ha => h ⟨_, _, ha, rfl, rfl⟩, by
    rintro h _ _ ⟨u, v, ha, rfl, rfl⟩
    exact h ha⟩

theorem map_comap_le (f : V ↪ W) (G : SimpleGraph W) : (G.comap f).map f ≤ G := by
  rw [map_le_iff_le_comap]

/-! ## Induced graphs -/

/- Given a set `s` of vertices, we can restrict a graph to those vertices by restricting its
adjacency relation. This gives a map between `SimpleGraph V` and `SimpleGraph s`.

There is also a notion of induced subgraphs (see `SimpleGraph.subgraph.induce`). -/
/-- Restrict a graph to the vertices in the set `s`, deleting all edges incident to vertices
outside the set. This is a wrapper around `SimpleGraph.comap`. -/
@[reducible]
def induce (s : Set V) (G : SimpleGraph V) : SimpleGraph s :=
  G.comap (Function.Embedding.subtype _)

/-- Given a graph on a set of vertices, we can make it be a `SimpleGraph V` by
adding in the remaining vertices without adding in any additional edges.
This is a wrapper around `SimpleGraph.map`. -/
@[reducible]
def spanningCoe {s : Set V} (G : SimpleGraph s) : SimpleGraph V :=
  G.map (Function.Embedding.subtype _)

theorem induce_spanningCoe {s : Set V} {G : SimpleGraph s} : G.spanningCoe.induce s = G :=
  comap_map_eq _ _

theorem spanningCoe_induce_le (s : Set V) : (G.induce s).spanningCoe ≤ G :=
  map_comap_le _ _

section FiniteAt

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote this condition by
`Fintype (G.neighborSet v)`.

We define `G.neighborFinset v` to be the `Finset` version of `G.neighborSet v`.
Use `neighborFinset_eq_filter` to rewrite this definition as a `Finset.filter` expression.
-/

variable (v) [Fintype (G.neighborSet v)]

/-- `G.neighbors v` is the `Finset` version of `Adj G v` in case `G` is
locally finite at `v`. -/
def neighborFinset : Finset V :=
  (G.neighborSet v).toFinset

theorem neighborFinset_def : G.neighborFinset v = (G.neighborSet v).toFinset :=
  rfl

@[simp]
theorem mem_neighborFinset (w : V) : w ∈ G.neighborFinset v ↔ Adj G v w :=
  Set.mem_toFinset

theorem not_mem_neighborFinset_self : v ∉ G.neighborFinset v := by simp

theorem neighborFinset_disjoint_singleton : Disjoint (G.neighborFinset v) {v} :=
  Finset.disjoint_singleton_right.mpr <| not_mem_neighborFinset_self _ _

theorem singleton_disjoint_neighborFinset : Disjoint {v} (G.neighborFinset v) :=
  Finset.disjoint_singleton_left.mpr <| not_mem_neighborFinset_self _ _

/-- `G.degree v` is the number of vertices adjacent to `v`. -/
def degree : ℕ :=
  (G.neighborFinset v).card

-- Porting note: in Lean 3 we could do `simp [← degree]`, but that gives
-- "invalid '←' modifier, 'SimpleGraph.degree' is a declaration name to be unfolded".
-- In any case, having this lemma is good since there's no guarantee we won't still change
-- the definition of `degree`.
@[simp]
theorem card_neighborFinset_eq_degree : (G.neighborFinset v).card = G.degree v := rfl

@[simp]
theorem card_neighborSet_eq_degree : Fintype.card (G.neighborSet v) = G.degree v :=
  (Set.toFinset_card _).symm

theorem degree_pos_iff_exists_adj : 0 < G.degree v ↔ ∃ w, Adj G v w := by
  simp only [degree, card_pos, Finset.Nonempty, mem_neighborFinset]

theorem degree_compl [Fintype (Gᶜ.neighborSet v)] [Fintype V] :
    Gᶜ.degree v = Fintype.card V - 1 - G.degree v := by
  classical
    rw [← card_neighborSet_union_compl_neighborSet G v, Set.toFinset_union]
    simp [card_disjoint_union (Set.disjoint_toFinset.mpr (compl_neighborSet_disjoint G v))]

instance incidenceSetFintype [DecidableEq V] : Fintype (G.incidenceSet v) :=
  Fintype.ofEquiv (G.neighborSet v) (G.incidenceSetEquivNeighborSet v).symm

/-- This is the `Finset` version of `incidenceSet`. -/
def incidenceFinset [DecidableEq V] : Finset (Sym2 V) :=
  (G.incidenceSet v).toFinset

@[simp]
theorem card_incidenceSet_eq_degree [DecidableEq V] :
    Fintype.card (G.incidenceSet v) = G.degree v := by
  rw [Fintype.card_congr (G.incidenceSetEquivNeighborSet v)]
  simp

@[simp]
theorem card_incidenceFinset_eq_degree [DecidableEq V] :
    (G.incidenceFinset v).card = G.degree v := by
  rw [← G.card_incidenceSet_eq_degree]
  apply Set.toFinset_card

@[simp]
theorem mem_incidenceFinset [DecidableEq V] (e : Sym2 V) :
    e ∈ G.incidenceFinset v ↔ e ∈ G.incidenceSet v :=
  Set.mem_toFinset

theorem incidenceFinset_eq_filter [DecidableEq V] [Fintype G.edgeSet] :
    G.incidenceFinset v = G.edgeFinset.filter (Membership.mem v) := by
  ext e
  refine' Sym2.ind (fun x y => _) e
  simp [mk'_mem_incidenceSet_iff]

end FiniteAt

section LocallyFinite

/-- A graph is locally finite if every vertex has a finite neighbor set. -/
@[reducible]
def LocallyFinite :=
  ∀ v : V, Fintype (G.neighborSet v)

variable [LocallyFinite G]

/-- A locally finite simple graph is regular of degree `d` if every vertex has degree `d`. -/
def IsRegularOfDegree (d : ℕ) : Prop :=
  ∀ v : V, G.degree v = d

variable {G}

theorem IsRegularOfDegree.degree_eq {d : ℕ} (h : G.IsRegularOfDegree d) (v : V) : G.degree v = d :=
  h v

theorem IsRegularOfDegree.compl [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel (Adj G)]
    {k : ℕ} (h : G.IsRegularOfDegree k) : Gᶜ.IsRegularOfDegree (Fintype.card V - 1 - k) := by
  intro v
  rw [degree_compl, h v]

end LocallyFinite

section Finite

variable [Fintype V]

instance neighborSetFintype [DecidableRel (Adj G)] (v : V) : Fintype (G.neighborSet v) :=
  @Subtype.fintype _ _
    (by
      simp_rw [mem_neighborSet]
      infer_instance)
    _

theorem neighborFinset_eq_filter {v : V} [DecidableRel (Adj G)] :
    G.neighborFinset v = Finset.univ.filter (Adj G v) := by
  ext
  simp

theorem neighborFinset_compl [DecidableEq V] [DecidableRel (Adj G)] (v : V) :
    Gᶜ.neighborFinset v = G.neighborFinset vᶜ \ {v} := by
  simp only [neighborFinset, neighborSet_compl, Set.toFinset_diff, Set.toFinset_compl,
    Set.toFinset_singleton]

@[simp]
theorem complete_graph_degree [DecidableEq V] (v : V) :
    (⊤ : SimpleGraph V).degree v = Fintype.card V - 1 := by
  erw [degree, neighborFinset_eq_filter, filter_ne, card_erase_of_mem (mem_univ v), card_univ]

theorem bot_degree (v : V) : (⊥ : SimpleGraph V).degree v = 0 := by
  erw [degree, neighborFinset_eq_filter, filter_False]
  exact Finset.card_empty

theorem IsRegularOfDegree.top [DecidableEq V] :
    (⊤ : SimpleGraph V).IsRegularOfDegree (Fintype.card V - 1) := by
  intro v
  simp

/-- The minimum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_minimal_degree_vertex`, `minDegree_le_degree`
and `le_minDegree_of_forall_le_degree`. -/
def minDegree [DecidableRel (Adj G)] : ℕ :=
  WithTop.untop' 0 (univ.image fun v => G.degree v).min

/-- There exists a vertex of minimal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex. -/
theorem exists_minimal_degree_vertex [DecidableRel (Adj G)] [Nonempty V] :
    ∃ v, G.minDegree = G.degree v := by
  obtain ⟨t, ht : _ = _⟩ := min_of_nonempty (univ_nonempty.image fun v => G.degree v)
  obtain ⟨v, _, rfl⟩ := mem_image.mp (mem_of_min ht)
  refine' ⟨v, by simp [minDegree, ht]⟩

/-- The minimum degree in the graph is at most the degree of any particular vertex. -/
theorem minDegree_le_degree [DecidableRel (Adj G)] (v : V) : G.minDegree ≤ G.degree v := by
  obtain ⟨t, ht⟩ := Finset.min_of_mem (mem_image_of_mem (fun v => G.degree v) (mem_univ v))
  have := Finset.min_le_of_eq (mem_image_of_mem _ (mem_univ v)) ht
  rwa [minDegree, ht]

/-- In a nonempty graph, if `k` is at most the degree of every vertex, it is at most the minimum
degree. Note the assumption that the graph is nonempty is necessary as long as `G.minDegree` is
defined to be a natural. -/
theorem le_minDegree_of_forall_le_degree [DecidableRel (Adj G)] [Nonempty V] (k : ℕ)
    (h : ∀ v, k ≤ G.degree v) : k ≤ G.minDegree := by
  rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩
  rw [hv]
  apply h

/-- The maximum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_maximal_degree_vertex`, `degree_le_maxDegree`
and `maxDegree_le_of_forall_degree_le`. -/
def maxDegree [DecidableRel (Adj G)] : ℕ :=
  Option.getD (univ.image fun v => G.degree v).max 0

/-- There exists a vertex of maximal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex. -/
theorem exists_maximal_degree_vertex [DecidableRel (Adj G)] [Nonempty V] :
    ∃ v, G.maxDegree = G.degree v := by
  obtain ⟨t, ht⟩ := max_of_nonempty (univ_nonempty.image fun v => G.degree v)
  have ht₂ := mem_of_max ht
  simp only [mem_image, mem_univ, exists_prop_of_true] at ht₂
  rcases ht₂ with ⟨v, _, rfl⟩
  refine' ⟨v, _⟩
  rw [maxDegree, ht]
  rfl

/-- The maximum degree in the graph is at least the degree of any particular vertex. -/
theorem degree_le_maxDegree [DecidableRel (Adj G)] (v : V) : G.degree v ≤ G.maxDegree := by
  obtain ⟨t, ht : _ = _⟩ := Finset.max_of_mem (mem_image_of_mem (fun v => G.degree v) (mem_univ v))
  have := Finset.le_max_of_eq (mem_image_of_mem _ (mem_univ v)) ht
  rwa [maxDegree, ht]

/-- In a graph, if `k` is at least the degree of every vertex, then it is at least the maximum
degree. -/
theorem maxDegree_le_of_forall_degree_le [DecidableRel (Adj G)] (k : ℕ) (h : ∀ v, G.degree v ≤ k) :
    G.maxDegree ≤ k := by
  by_cases hV : (univ : Finset V).Nonempty
  · haveI : Nonempty V := univ_nonempty_iff.mp hV
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    rw [hv]
    apply h
  · rw [not_nonempty_iff_eq_empty] at hV
    rw [maxDegree, hV, image_empty]
    exact zero_le k

theorem degree_lt_card_verts [DecidableRel (Adj G)] (v : V) : G.degree v < Fintype.card V := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  exact ⟨v, by simp, Finset.subset_univ _⟩

/--
The maximum degree of a nonempty graph is less than the number of vertices. Note that the assumption
that `V` is nonempty is necessary, as otherwise this would assert the existence of a
natural number less than zero. -/
theorem maxDegree_lt_card_verts [DecidableRel (Adj G)] [Nonempty V] :
    G.maxDegree < Fintype.card V := by
  cases' G.exists_maximal_degree_vertex with v hv
  rw [hv]
  apply G.degree_lt_card_verts v

theorem card_commonNeighbors_le_degree_left [DecidableRel (Adj G)] (v w : V) :
    Fintype.card (G.commonNeighbors v w) ≤ G.degree v := by
  rw [← card_neighborSet_eq_degree]
  exact Set.card_le_of_subset (Set.inter_subset_left _ _)

theorem card_commonNeighbors_le_degree_right [DecidableRel (Adj G)] (v w : V) :
    Fintype.card (G.commonNeighbors v w) ≤ G.degree w := by
  simp_rw [commonNeighbors_symm _ v w, card_commonNeighbors_le_degree_left]

theorem card_commonNeighbors_lt_card_verts [DecidableRel (Adj G)] (v w : V) :
    Fintype.card (G.commonNeighbors v w) < Fintype.card V :=
  Nat.lt_of_le_of_lt (G.card_commonNeighbors_le_degree_left _ _) (G.degree_lt_card_verts v)

/-- If the condition `Adj G v w` fails, then `card_commonNeighbors_le_degree` is
the best we can do in general. -/
theorem Adj.card_commonNeighbors_lt_degree {G : SimpleGraph V} [DecidableRel (Adj G)] {v w : V}
    (h : Adj G v w) : Fintype.card (G.commonNeighbors v w) < G.degree v := by
  classical
  erw [← Set.toFinset_card]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  use w
  constructor
  · rw [Finset.insert_subset]
    constructor
    · simpa
    · rw [neighborFinset, Set.toFinset_subset_toFinset]
      exact G.commonNeighbors_subset_neighborSet_left _ _
  · rw [Set.mem_toFinset]
    apply not_mem_commonNeighbors_right

theorem card_commonNeighbors_top [DecidableEq V] {v w : V} (h : v ≠ w) :
    Fintype.card ((⊤ : SimpleGraph V).commonNeighbors v w) = Fintype.card V - 2 := by
  simp only [commonNeighbors_top_eq, ← Set.toFinset_card, Set.toFinset_diff]
  rw [Finset.card_sdiff]
  · simp [Finset.card_univ, h]
  · simp only [Set.toFinset_subset_toFinset, Set.subset_univ]

end Finite

section Maps

namespace Hom

variable {G G'} (f : G →g G')

theorem map_mem_edgeSet {e : Sym2 V} (h : e ∈ G.edgeSet) : e.map f ∈ G'.edgeSet :=
  Sym2.ind (fun _ _ => f.map_rel') e h

theorem apply_mem_neighborSet {v w : V} (h : w ∈ G.neighborSet v) : f w ∈ G'.neighborSet (f v) :=
  Hom.map_adj f h

/-- The map between edge sets induced by a homomorphism.
The underlying map on edges is given by `Sym2.map`. -/
@[simps]
def mapEdgeSet (e : G.edgeSet) : G'.edgeSet :=
  ⟨Sym2.map f e, map_mem_edgeSet f e.property⟩

/-- The map between neighbor sets induced by a homomorphism. -/
@[simps]
def mapNeighborSet (v : V) (w : G.neighborSet v) : G'.neighborSet (f v) :=
  ⟨f w, apply_mem_neighborSet f w.property⟩

/-- The induced map for spanning subgraphs, which is the identity on vertices. -/
@[simps]
def mapSpanningSubgraphs {G G' : SimpleGraph V} (h : G ≤ G') : G →g G' where
  toFun x := x
  map_rel' ha := h ha

theorem mapEdgeSet.injective (hinj : Function.Injective f) : Function.Injective (mapEdgeSet f) := by
  rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
  dsimp [Hom.mapEdgeSet]
  repeat' rw [Subtype.mk_eq_mk]
  apply Sym2.map.injective hinj

/-- Every graph homomomorphism from a complete graph is injective. -/
theorem injective_of_top_hom (f : (⊤ : SimpleGraph V) →g G') : Function.Injective f := by
  intro v w h
  contrapose! h
  exact G'.ne_of_adj (Hom.map_adj f ((top_adj _ _).mpr h))

/-- There is a homomorphism to a graph from a comapped graph.
When the function is injective, this is an embedding (see `SimpleGraph.Embedding.comap`). -/
@[simps]
protected def comap (f : V → W) (G : SimpleGraph W) : G.comap f →g G where
  toFun := f
  map_rel' := by simp

end Hom

namespace Embedding

variable {G G'} (f : G ↪g G')

theorem map_mem_edgeSet_iff {e : Sym2 V} : e.map f ∈ G'.edgeSet ↔ e ∈ G.edgeSet :=
  Sym2.ind (fun _ _ => f.map_adj_iff) e

theorem apply_mem_neighborSet_iff {v w : V} : f w ∈ G'.neighborSet (f v) ↔ w ∈ G.neighborSet v :=
  Embedding.map_adj_iff f

/-- A graph embedding induces an embedding of edge sets. -/
@[simps]
def mapEdgeSet : G.edgeSet ↪ G'.edgeSet where
  toFun := Hom.mapEdgeSet f
  inj' := Hom.mapEdgeSet.injective f f.injective

/-- A graph embedding induces an embedding of neighbor sets. -/
@[simps]
def mapNeighborSet (v : V) : G.neighborSet v ↪ G'.neighborSet (f v)
    where
  toFun w := ⟨f w, (apply_mem_neighborSet_iff f).mpr w.2⟩
  inj' := by
    rintro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h
    rw [Subtype.mk_eq_mk] at h⊢
    exact f.inj' h

/-- Given an injective function, there is an embedding from the comapped graph into the original
graph. -/
-- porting note: @[simps] does not work here since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `comap_apply` for now.
protected def comap (f : V ↪ W) (G : SimpleGraph W) : G.comap f ↪g G :=
  { f with map_rel_iff' := by simp }

@[simp]
theorem comap_apply (f : V ↪ W) (G : SimpleGraph W) (v : V) :
  SimpleGraph.Embedding.comap f G v = f v := rfl

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
-- porting note: @[simps] does not work here since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `map_apply` for now.
protected def map (f : V ↪ W) (G : SimpleGraph V) : G ↪g G.map f :=
  { f with map_rel_iff' := by simp }

@[simp]
theorem map_apply (f : V ↪ W) (G : SimpleGraph V) (v : V) :
  SimpleGraph.Embedding.map f G v = f v := rfl

/-- Induced graphs embed in the original graph.

Note that if `G.induce s = ⊤` (i.e., if `s` is a clique) then this gives the embedding of a
complete graph. -/
@[reducible]
protected def induce (s : Set V) : G.induce s ↪g G :=
  SimpleGraph.Embedding.comap (Function.Embedding.subtype _) G

/-- Graphs on a set of vertices embed in their `spanningCoe`. -/
@[reducible]
protected def spanningCoe {s : Set V} (G : SimpleGraph s) : G ↪g G.spanningCoe :=
  SimpleGraph.Embedding.map (Function.Embedding.subtype _) G

/-- Embeddings of types induce embeddings of complete graphs on those types. -/
protected def completeGraph {α β : Type _} (f : α ↪ β) :
    (⊤ : SimpleGraph α) ↪g (⊤ : SimpleGraph β) :=
  { f with map_rel_iff' := by simp }

end Embedding

section InduceHom

variable {G G'} {G'' : SimpleGraph X} {s : Set V} {t : Set W} {r : Set X}
         (φ : G →g G') (φst : Set.MapsTo φ s t) (ψ : G' →g G'') (ψtr : Set.MapsTo ψ t r)

/-- The restriction of a morphism of graphs to induced subgraphs. -/
def InduceHom : G.induce s →g G'.induce t where
  toFun := Set.MapsTo.restrict φ s t φst
  map_rel' := φ.map_rel'

@[simp, norm_cast] lemma coe_induceHom : ⇑(InduceHom φ φst) = Set.MapsTo.restrict φ s t φst :=
  rfl

@[simp] lemma induceHom_id (G : SimpleGraph V) (s) :
    InduceHom (Hom.id : G →g G) (Set.mapsTo_id s) = Hom.id := by
  ext x
  rfl

@[simp] lemma induceHom_comp :
    (InduceHom ψ ψtr).comp (InduceHom φ φst) = InduceHom (ψ.comp φ) (ψtr.comp φst) := by
  ext x
  rfl

end InduceHom

namespace Iso

variable {G G'} (f : G ≃g G')

theorem map_mem_edgeSet_iff {e : Sym2 V} : e.map f ∈ G'.edgeSet ↔ e ∈ G.edgeSet :=
  Sym2.ind (fun _ _ => f.map_adj_iff) e

theorem apply_mem_neighborSet_iff {v w : V} : f w ∈ G'.neighborSet (f v) ↔ w ∈ G.neighborSet v :=
  Iso.map_adj_iff f

/-- An isomorphism of graphs induces an equivalence of edge sets. -/
@[simps]
def mapEdgeSet : G.edgeSet ≃ G'.edgeSet
    where
  toFun := Hom.mapEdgeSet f
  invFun := Hom.mapEdgeSet f.symm
  left_inv := by
    rintro ⟨e, h⟩
    simp [Hom.mapEdgeSet, Sym2.map_map, RelEmbedding.toRelHom]
    convert congr_fun Sym2.map_id e
    exact RelIso.symm_apply_apply _ _
  right_inv := by
    rintro ⟨e, h⟩
    simp [Hom.mapEdgeSet, Sym2.map_map, RelEmbedding.toRelHom]
    convert congr_fun Sym2.map_id e
    exact RelIso.apply_symm_apply _ _

/-- A graph isomorphism induces an equivalence of neighbor sets. -/
@[simps]
def mapNeighborSet (v : V) : G.neighborSet v ≃ G'.neighborSet (f v)
    where
  toFun w := ⟨f w, (apply_mem_neighborSet_iff f).mpr w.2⟩
  invFun w :=
    ⟨f.symm w, by
      simpa [RelIso.symm_apply_apply] using (apply_mem_neighborSet_iff f.symm).mpr w.2⟩
  left_inv w := by simp
  right_inv w := by simp

/-- Given a bijection, there is an embedding from the comapped graph into the original
graph. -/
-- porting note: `@[simps]` does not work here anymore since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `comap_apply` for now.
protected def comap (f : V ≃ W) (G : SimpleGraph W) : G.comap f.toEmbedding ≃g G :=
  { f with map_rel_iff' := by simp }

@[simp]
lemma comap_apply (f : V ≃ W) (G : SimpleGraph W) (v : V) :
  SimpleGraph.Iso.comap f G v = f v := rfl

@[simp]
lemma comap_symm_apply (f : V ≃ W) (G : SimpleGraph W) (w : W) :
  (SimpleGraph.Iso.comap f G).symm w = f.symm w := rfl

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
-- porting note: `@[simps]` does not work here anymore since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `map_apply` for now.
protected def map (f : V ≃ W) (G : SimpleGraph V) : G ≃g G.map f.toEmbedding :=
  { f with map_rel_iff' := by simp }

@[simp]
lemma map_apply (f : V ≃ W) (G : SimpleGraph V) (v : V) :
  SimpleGraph.Iso.map f G v = f v := rfl

@[simp]
lemma map_symm_apply (f : V ≃ W) (G : SimpleGraph V) (w : W) :
  (SimpleGraph.Iso.map f G).symm w = f.symm w := rfl

/-- Equivalences of types induce isomorphisms of complete graphs on those types. -/
protected def completeGraph {α β : Type _} (f : α ≃ β) :
    (⊤ : SimpleGraph α) ≃g (⊤ : SimpleGraph β) :=
  { f with map_rel_iff' := by simp }

theorem toEmbedding_completeGraph {α β : Type _} (f : α ≃ β) :
    (Iso.completeGraph f).toEmbedding = Embedding.completeGraph f.toEmbedding :=
  rfl

end Iso

end Maps

end SimpleGraph
