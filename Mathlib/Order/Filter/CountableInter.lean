/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Set.Countable

#align_import order.filter.countable_Inter from "leanprover-community/mathlib"@"b9e46fe101fc897fb2e7edaf0bf1f09ea49eb81a"

/-!
# Filters with countable intersection property

In this file we define `CountableInterFilter` to be the class of filters with the following
property: for any countable collection of sets `s ∈ l` their intersection belongs to `l` as well.

Two main examples are the `residual` filter defined in `Mathlib.Topology.GDelta` and
the `MeasureTheory.Measure.ae` filter defined in `MeasureTheory.MeasureSpace`.

We reformulate the definition in terms of indexed intersection and in terms of `Filter.Eventually`
and provide instances for some basic constructions (`⊥`, `⊤`, `Filter.principal`, `Filter.map`,
`Filter.comap`, `Inf.inf`). We also provide a custom constructor `Filter.ofCountableInter`
that deduces two axioms of a `Filter` from the countable intersection property.

## Tags
filter, countable
-/


open Set Filter

open Filter

variable {ι : Sort*} {α β : Type*}

/-- A filter `l` has the countable intersection property if for any countable collection
of sets `s ∈ l` their intersection belongs to `l` as well. -/
class CountableInterFilter (l : Filter α) : Prop where
  /-- For a countable collection of sets `s ∈ l`, their intersection belongs to `l` as well. -/
  countable_sInter_mem : ∀ S : Set (Set α), S.Countable → (∀ s ∈ S, s ∈ l) → ⋂₀ S ∈ l
#align countable_Inter_filter CountableInterFilter

variable {l : Filter α} [CountableInterFilter l]

theorem countable_sInter_mem {S : Set (Set α)} (hSc : S.Countable) : ⋂₀ S ∈ l ↔ ∀ s ∈ S, s ∈ l :=
  ⟨fun hS _s hs => mem_of_superset hS (sInter_subset_of_mem hs),
    CountableInterFilter.countable_sInter_mem _ hSc⟩
#align countable_sInter_mem countable_sInter_mem

theorem countable_iInter_mem [Countable ι] {s : ι → Set α} : (⋂ i, s i) ∈ l ↔ ∀ i, s i ∈ l :=
  sInter_range s ▸ (countable_sInter_mem (countable_range _)).trans forall_range_iff
#align countable_Inter_mem countable_iInter_mem

theorem countable_bInter_mem {ι : Type*} {S : Set ι} (hS : S.Countable) {s : ∀ i ∈ S, Set α} :
    (⋂ i, ⋂ hi : i ∈ S, s i ‹_›) ∈ l ↔ ∀ i, ∀ hi : i ∈ S, s i ‹_› ∈ l := by
  rw [biInter_eq_iInter]
  -- ⊢ ⋂ (x : ↑S), s ↑x (_ : ↑x ∈ S) ∈ l ↔ ∀ (i : ι) (hi : i ∈ S), s i hi ∈ l
  haveI := hS.toEncodable
  -- ⊢ ⋂ (x : ↑S), s ↑x (_ : ↑x ∈ S) ∈ l ↔ ∀ (i : ι) (hi : i ∈ S), s i hi ∈ l
  exact countable_iInter_mem.trans Subtype.forall
  -- 🎉 no goals
#align countable_bInter_mem countable_bInter_mem

theorem eventually_countable_forall [Countable ι] {p : α → ι → Prop} :
    (∀ᶠ x in l, ∀ i, p x i) ↔ ∀ i, ∀ᶠ x in l, p x i := by
  simpa only [Filter.Eventually, setOf_forall] using
    @countable_iInter_mem _ _ l _ _ fun i => { x | p x i }
#align eventually_countable_forall eventually_countable_forall

theorem eventually_countable_ball {ι : Type*} {S : Set ι} (hS : S.Countable)
    {p : α → ∀ i ∈ S, Prop} :
    (∀ᶠ x in l, ∀ i hi, p x i hi) ↔ ∀ i hi, ∀ᶠ x in l, p x i hi := by
  simpa only [Filter.Eventually, setOf_forall] using
    @countable_bInter_mem _ l _ _ _ hS fun i hi => { x | p x i hi }
#align eventually_countable_ball eventually_countable_ball

theorem EventuallyLE.countable_iUnion [Countable ι] {s t : ι → Set α} (h : ∀ i, s i ≤ᶠ[l] t i) :
    ⋃ i, s i ≤ᶠ[l] ⋃ i, t i :=
  (eventually_countable_forall.2 h).mono fun _ hst hs => mem_iUnion.2 <| (mem_iUnion.1 hs).imp hst
#align eventually_le.countable_Union EventuallyLE.countable_iUnion

theorem EventuallyEq.countable_iUnion [Countable ι] {s t : ι → Set α} (h : ∀ i, s i =ᶠ[l] t i) :
    ⋃ i, s i =ᶠ[l] ⋃ i, t i :=
  (EventuallyLE.countable_iUnion fun i => (h i).le).antisymm
    (EventuallyLE.countable_iUnion fun i => (h i).symm.le)
#align eventually_eq.countable_Union EventuallyEq.countable_iUnion

theorem EventuallyLE.countable_bUnion {ι : Type*} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi ≤ᶠ[l] t i hi) :
    ⋃ i ∈ S, s i ‹_› ≤ᶠ[l] ⋃ i ∈ S, t i ‹_› := by
  simp only [biUnion_eq_iUnion]
  -- ⊢ ⋃ (x : ↑S), s ↑x (_ : ↑x ∈ S) ≤ᶠ[l] ⋃ (x : ↑S), t ↑x (_ : ↑x ∈ S)
  haveI := hS.toEncodable
  -- ⊢ ⋃ (x : ↑S), s ↑x (_ : ↑x ∈ S) ≤ᶠ[l] ⋃ (x : ↑S), t ↑x (_ : ↑x ∈ S)
  exact EventuallyLE.countable_iUnion fun i => h i i.2
  -- 🎉 no goals
#align eventually_le.countable_bUnion EventuallyLE.countable_bUnion

theorem EventuallyEq.countable_bUnion {ι : Type*} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi =ᶠ[l] t i hi) :
    ⋃ i ∈ S, s i ‹_› =ᶠ[l] ⋃ i ∈ S, t i ‹_› :=
  (EventuallyLE.countable_bUnion hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.countable_bUnion hS fun i hi => (h i hi).symm.le)
#align eventually_eq.countable_bUnion EventuallyEq.countable_bUnion

theorem EventuallyLE.countable_iInter [Countable ι] {s t : ι → Set α} (h : ∀ i, s i ≤ᶠ[l] t i) :
    ⋂ i, s i ≤ᶠ[l] ⋂ i, t i :=
  (eventually_countable_forall.2 h).mono fun _ hst hs =>
    mem_iInter.2 fun i => hst _ (mem_iInter.1 hs i)
#align eventually_le.countable_Inter EventuallyLE.countable_iInter

theorem EventuallyEq.countable_iInter [Countable ι] {s t : ι → Set α} (h : ∀ i, s i =ᶠ[l] t i) :
    ⋂ i, s i =ᶠ[l] ⋂ i, t i :=
  (EventuallyLE.countable_iInter fun i => (h i).le).antisymm
    (EventuallyLE.countable_iInter fun i => (h i).symm.le)
#align eventually_eq.countable_Inter EventuallyEq.countable_iInter

theorem EventuallyLE.countable_bInter {ι : Type*} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi ≤ᶠ[l] t i hi) :
    ⋂ i ∈ S, s i ‹_› ≤ᶠ[l] ⋂ i ∈ S, t i ‹_› := by
  simp only [biInter_eq_iInter]
  -- ⊢ ⋂ (x : ↑S), s ↑x (_ : ↑x ∈ S) ≤ᶠ[l] ⋂ (x : ↑S), t ↑x (_ : ↑x ∈ S)
  haveI := hS.toEncodable
  -- ⊢ ⋂ (x : ↑S), s ↑x (_ : ↑x ∈ S) ≤ᶠ[l] ⋂ (x : ↑S), t ↑x (_ : ↑x ∈ S)
  exact EventuallyLE.countable_iInter fun i => h i i.2
  -- 🎉 no goals
#align eventually_le.countable_bInter EventuallyLE.countable_bInter

theorem EventuallyEq.countable_bInter {ι : Type*} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi =ᶠ[l] t i hi) :
    ⋂ i ∈ S, s i ‹_› =ᶠ[l] ⋂ i ∈ S, t i ‹_› :=
  (EventuallyLE.countable_bInter hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.countable_bInter hS fun i hi => (h i hi).symm.le)
#align eventually_eq.countable_bInter EventuallyEq.countable_bInter

/-- Construct a filter with countable intersection property. This constructor deduces
`Filter.univ_sets` and `Filter.inter_sets` from the countable intersection property. -/
def Filter.ofCountableInter (l : Set (Set α))
    (hp : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) : Filter α where
  sets := l
  univ_sets := @sInter_empty α ▸ hp _ countable_empty (empty_subset _)
  sets_of_superset := h_mono _ _
  inter_sets {s t} hs ht := sInter_pair s t ▸
    hp _ ((countable_singleton _).insert _) (insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩)
#align filter.of_countable_Inter Filter.ofCountableInter

instance Filter.countable_Inter_ofCountableInter (l : Set (Set α))
    (hp : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) :
    CountableInterFilter (Filter.ofCountableInter l hp h_mono) :=
  ⟨hp⟩
#align filter.countable_Inter_of_countable_Inter Filter.countable_Inter_ofCountableInter

@[simp]
theorem Filter.mem_ofCountableInter {l : Set (Set α)}
    (hp : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l) (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l)
    {s : Set α} : s ∈ Filter.ofCountableInter l hp h_mono ↔ s ∈ l :=
  Iff.rfl
#align filter.mem_of_countable_Inter Filter.mem_ofCountableInter

instance countableInterFilter_principal (s : Set α) : CountableInterFilter (𝓟 s) :=
  ⟨fun _ _ hS => subset_sInter hS⟩
#align countable_Inter_filter_principal countableInterFilter_principal

instance countableInterFilter_bot : CountableInterFilter (⊥ : Filter α) := by
  rw [← principal_empty]
  -- ⊢ CountableInterFilter (𝓟 ∅)
  apply countableInterFilter_principal
  -- 🎉 no goals
#align countable_Inter_filter_bot countableInterFilter_bot

instance countableInterFilter_top : CountableInterFilter (⊤ : Filter α) := by
  rw [← principal_univ]
  -- ⊢ CountableInterFilter (𝓟 univ)
  apply countableInterFilter_principal
  -- 🎉 no goals
#align countable_Inter_filter_top countableInterFilter_top

instance (l : Filter β) [CountableInterFilter l] (f : α → β) :
    CountableInterFilter (comap f l) := by
  refine' ⟨fun S hSc hS => _⟩
  -- ⊢ ⋂₀ S ∈ comap f l
  choose! t htl ht using hS
  -- ⊢ ⋂₀ S ∈ comap f l
  have : (⋂ s ∈ S, t s) ∈ l := (countable_bInter_mem hSc).2 htl
  -- ⊢ ⋂₀ S ∈ comap f l
  refine' ⟨_, this, _⟩
  -- ⊢ f ⁻¹' ⋂ (s : Set α) (_ : s ∈ S), t s ⊆ ⋂₀ S
  simpa [preimage_iInter] using iInter₂_mono ht
  -- 🎉 no goals

instance (l : Filter α) [CountableInterFilter l] (f : α → β) : CountableInterFilter (map f l) := by
  refine' ⟨fun S hSc hS => _⟩
  -- ⊢ ⋂₀ S ∈ map f l
  simp only [mem_map, sInter_eq_biInter, preimage_iInter₂] at hS ⊢
  -- ⊢ ⋂ (i : Set β) (_ : i ∈ S), f ⁻¹' i ∈ l
  exact (countable_bInter_mem hSc).2 hS
  -- 🎉 no goals

/-- Infimum of two `CountableInterFilter`s is a `CountableInterFilter`. This is useful, e.g.,
to automatically get an instance for `residual α ⊓ 𝓟 s`. -/
instance countableInterFilter_inf (l₁ l₂ : Filter α) [CountableInterFilter l₁]
    [CountableInterFilter l₂] : CountableInterFilter (l₁ ⊓ l₂) := by
  refine' ⟨fun S hSc hS => _⟩
  -- ⊢ ⋂₀ S ∈ l₁ ⊓ l₂
  choose s hs t ht hst using hS
  -- ⊢ ⋂₀ S ∈ l₁ ⊓ l₂
  replace hs : (⋂ i ∈ S, s i ‹_›) ∈ l₁ := (countable_bInter_mem hSc).2 hs
  -- ⊢ ⋂₀ S ∈ l₁ ⊓ l₂
  replace ht : (⋂ i ∈ S, t i ‹_›) ∈ l₂ := (countable_bInter_mem hSc).2 ht
  -- ⊢ ⋂₀ S ∈ l₁ ⊓ l₂
  refine' mem_of_superset (inter_mem_inf hs ht) (subset_sInter fun i hi => _)
  -- ⊢ (⋂ (i : Set α) (h : i ∈ S), s i h) ∩ ⋂ (i : Set α) (h : i ∈ S), t i h ⊆ i
  rw [hst i hi]
  -- ⊢ (⋂ (i : Set α) (h : i ∈ S), s i h) ∩ ⋂ (i : Set α) (h : i ∈ S), t i h ⊆ s i  …
  apply inter_subset_inter <;> exact iInter_subset_of_subset i (iInter_subset _ _)
  -- ⊢ ⋂ (i : Set α) (h : i ∈ S), s i h ⊆ s i hi
                               -- 🎉 no goals
                               -- 🎉 no goals
#align countable_Inter_filter_inf countableInterFilter_inf

/-- Supremum of two `CountableInterFilter`s is a `CountableInterFilter`. -/
instance countableInterFilter_sup (l₁ l₂ : Filter α) [CountableInterFilter l₁]
    [CountableInterFilter l₂] : CountableInterFilter (l₁ ⊔ l₂) := by
  refine' ⟨fun S hSc hS => ⟨_, _⟩⟩ <;> refine' (countable_sInter_mem hSc).2 fun s hs => _
  -- ⊢ ⋂₀ S ∈ l₁.sets
                                       -- ⊢ s ∈ l₁
                                       -- ⊢ s ∈ l₂
  exacts [(hS s hs).1, (hS s hs).2]
  -- 🎉 no goals
#align countable_Inter_filter_sup countableInterFilter_sup

namespace Filter

variable (g : Set (Set α))

/-- `Filter.CountableGenerateSets g` is the (sets of the)
greatest `countableInterFilter` containing `g`.-/
inductive CountableGenerateSets : Set α → Prop
  | basic {s : Set α} : s ∈ g → CountableGenerateSets s
  | univ : CountableGenerateSets univ
  | superset {s t : Set α} : CountableGenerateSets s → s ⊆ t → CountableGenerateSets t
  | sInter {S : Set (Set α)} :
    S.Countable → (∀ s ∈ S, CountableGenerateSets s) → CountableGenerateSets (⋂₀ S)
#align filter.countable_generate_sets Filter.CountableGenerateSets

/-- `Filter.countableGenerate g` is the greatest `countableInterFilter` containing `g`.-/
def countableGenerate : Filter α :=
  ofCountableInter (CountableGenerateSets g) (fun _ => CountableGenerateSets.sInter) fun _ _ =>
    CountableGenerateSets.superset
  --deriving CountableInterFilter
#align filter.countable_generate Filter.countableGenerate

--Porting note: could not de derived
instance : CountableInterFilter (countableGenerate g) := by
  delta countableGenerate; infer_instance
  -- ⊢ CountableInterFilter (ofCountableInter (CountableGenerateSets g) (_ : ∀ (x : …
                           -- 🎉 no goals

variable {g}

/-- A set is in the `countableInterFilter` generated by `g` if and only if
it contains a countable intersection of elements of `g`. -/
theorem mem_countableGenerate_iff {s : Set α} :
    s ∈ countableGenerate g ↔ ∃ S : Set (Set α), S ⊆ g ∧ S.Countable ∧ ⋂₀ S ⊆ s := by
  constructor <;> intro h
  -- ⊢ s ∈ countableGenerate g → ∃ S, S ⊆ g ∧ Set.Countable S ∧ ⋂₀ S ⊆ s
                  -- ⊢ ∃ S, S ⊆ g ∧ Set.Countable S ∧ ⋂₀ S ⊆ s
                  -- ⊢ s ∈ countableGenerate g
  · induction' h with s hs s t _ st ih S Sct _ ih
    · exact ⟨{s}, by simp [hs, subset_refl]⟩
      -- 🎉 no goals
    · exact ⟨∅, by simp⟩
      -- 🎉 no goals
    · refine' Exists.imp (fun S => _) ih
      -- ⊢ S ⊆ g ∧ Set.Countable S ∧ ⋂₀ S ⊆ s → S ⊆ g ∧ Set.Countable S ∧ ⋂₀ S ⊆ t
      tauto
      -- 🎉 no goals
    choose T Tg Tct hT using ih
    -- ⊢ ∃ S_1, S_1 ⊆ g ∧ Set.Countable S_1 ∧ ⋂₀ S_1 ⊆ ⋂₀ S
    refine' ⟨⋃ (s) (H : s ∈ S), T s H, by simpa, Sct.biUnion Tct, _⟩
    -- ⊢ ⋂₀ ⋃ (s : Set α) (H : s ∈ S), T s H ⊆ ⋂₀ S
    apply subset_sInter
    -- ⊢ ∀ (t' : Set α), t' ∈ S → ⋂₀ ⋃ (s : Set α) (H : s ∈ S), T s H ⊆ t'
    intro s H
    -- ⊢ ⋂₀ ⋃ (s : Set α) (H : s ∈ S), T s H ⊆ s
    refine' subset_trans (sInter_subset_sInter (subset_iUnion₂ s H)) (hT s H)
    -- 🎉 no goals
  rcases h with ⟨S, Sg, Sct, hS⟩
  -- ⊢ s ∈ countableGenerate g
  refine' mem_of_superset ((countable_sInter_mem Sct).mpr _) hS
  -- ⊢ ∀ (s : Set α), s ∈ S → s ∈ countableGenerate g
  intro s H
  -- ⊢ s ∈ countableGenerate g
  exact CountableGenerateSets.basic (Sg H)
  -- 🎉 no goals
#align filter.mem_countable_generate_iff Filter.mem_countableGenerate_iff

theorem le_countableGenerate_iff_of_countableInterFilter {f : Filter α} [CountableInterFilter f] :
    f ≤ countableGenerate g ↔ g ⊆ f.sets := by
  constructor <;> intro h
  -- ⊢ f ≤ countableGenerate g → g ⊆ f.sets
                  -- ⊢ g ⊆ f.sets
                  -- ⊢ f ≤ countableGenerate g
  · exact subset_trans (fun s => CountableGenerateSets.basic) h
    -- 🎉 no goals
  intro s hs
  -- ⊢ s ∈ f
  induction' hs with s hs s t _ st ih S Sct _ ih
  · exact h hs
    -- 🎉 no goals
  · exact univ_mem
    -- 🎉 no goals
  · exact mem_of_superset ih st
    -- 🎉 no goals
  exact (countable_sInter_mem Sct).mpr ih
  -- 🎉 no goals
#align filter.le_countable_generate_iff_of_countable_Inter_filter Filter.le_countableGenerate_iff_of_countableInterFilter

variable (g)

/-- `countableGenerate g` is the greatest `countableInterFilter` containing `g`.-/
theorem countableGenerate_isGreatest :
    IsGreatest { f : Filter α | CountableInterFilter f ∧ g ⊆ f.sets } (countableGenerate g) := by
  refine' ⟨⟨inferInstance, fun s => CountableGenerateSets.basic⟩, _⟩
  -- ⊢ countableGenerate g ∈ upperBounds {f | CountableInterFilter f ∧ g ⊆ f.sets}
  rintro f ⟨fct, hf⟩
  -- ⊢ f ≤ countableGenerate g
  rwa [@le_countableGenerate_iff_of_countableInterFilter _ _ _ fct]
  -- 🎉 no goals
#align filter.countable_generate_is_greatest Filter.countableGenerate_isGreatest

end Filter
