/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Alex Kontorovich
-/
import Mathlib.Order.Filter.Bases

#align_import order.filter.pi from "leanprover-community/mathlib"@"1f0096e6caa61e9c849ec2adbd227e960e9dff58"

/-!
# (Co)product of a family of filters

In this file we define two filters on `Π i, α i` and prove some basic properties of these filters.

* `Filter.pi (f : Π i, Filter (α i))` to be the maximal filter on `Π i, α i` such that
  `∀ i, Filter.Tendsto (Function.eval i) (Filter.pi f) (f i)`. It is defined as
  `Π i, Filter.comap (Function.eval i) (f i)`. This is a generalization of `Filter.prod` to indexed
  products.

* `Filter.coprodᵢ (f : Π i, Filter (α i))`: a generalization of `Filter.coprod`; it is the supremum
  of `comap (eval i) (f i)`.
-/


open Set Function

open Classical Filter

namespace Filter

variable {ι : Type*} {α : ι → Type*} {f f₁ f₂ : (i : ι) → Filter (α i)} {s : (i : ι) → Set (α i)}

section Pi

/-- The product of an indexed family of filters. -/
def pi (f : ∀ i, Filter (α i)) : Filter (∀ i, α i) :=
  ⨅ i, comap (eval i) (f i)
#align filter.pi Filter.pi

instance pi.isCountablyGenerated [Countable ι] [∀ i, IsCountablyGenerated (f i)] :
    IsCountablyGenerated (pi f) :=
  iInf.isCountablyGenerated _
#align filter.pi.is_countably_generated Filter.pi.isCountablyGenerated

theorem tendsto_eval_pi (f : ∀ i, Filter (α i)) (i : ι) : Tendsto (eval i) (pi f) (f i) :=
  tendsto_iInf' i tendsto_comap
#align filter.tendsto_eval_pi Filter.tendsto_eval_pi

theorem tendsto_pi {β : Type*} {m : β → ∀ i, α i} {l : Filter β} :
    Tendsto m l (pi f) ↔ ∀ i, Tendsto (fun x => m x i) l (f i) := by
  simp only [pi, tendsto_iInf, tendsto_comap_iff]; rfl
  -- ⊢ (∀ (i : ι), Tendsto (eval i ∘ m) l (f i)) ↔ ∀ (i : ι), Tendsto (fun x => m x …
                                                   -- 🎉 no goals
#align filter.tendsto_pi Filter.tendsto_pi

theorem le_pi {g : Filter (∀ i, α i)} : g ≤ pi f ↔ ∀ i, Tendsto (eval i) g (f i) :=
  tendsto_pi
#align filter.le_pi Filter.le_pi

@[mono]
theorem pi_mono (h : ∀ i, f₁ i ≤ f₂ i) : pi f₁ ≤ pi f₂ :=
  iInf_mono fun i => comap_mono <| h i
#align filter.pi_mono Filter.pi_mono

theorem mem_pi_of_mem (i : ι) {s : Set (α i)} (hs : s ∈ f i) : eval i ⁻¹' s ∈ pi f :=
  mem_iInf_of_mem i <| preimage_mem_comap hs
#align filter.mem_pi_of_mem Filter.mem_pi_of_mem

theorem pi_mem_pi {I : Set ι} (hI : I.Finite) (h : ∀ i ∈ I, s i ∈ f i) : I.pi s ∈ pi f := by
  rw [pi_def, biInter_eq_iInter]
  -- ⊢ ⋂ (x : ↑I), eval ↑x ⁻¹' s ↑x ∈ pi f
  refine' mem_iInf_of_iInter hI (fun i => _) Subset.rfl
  -- ⊢ eval ↑i ⁻¹' s ↑i ∈ comap (eval ↑i) (f ↑i)
  exact preimage_mem_comap (h i i.2)
  -- 🎉 no goals
#align filter.pi_mem_pi Filter.pi_mem_pi

theorem mem_pi {s : Set (∀ i, α i)} :
    s ∈ pi f ↔ ∃ I : Set ι, I.Finite ∧ ∃ t : ∀ i, Set (α i), (∀ i, t i ∈ f i) ∧ I.pi t ⊆ s := by
  constructor
  -- ⊢ s ∈ pi f → ∃ I, Set.Finite I ∧ ∃ t, (∀ (i : ι), t i ∈ f i) ∧ Set.pi I t ⊆ s
  · simp only [pi, mem_iInf', mem_comap, pi_def]
    -- ⊢ (∃ I, Set.Finite I ∧ ∃ V, (∀ (i : ι), ∃ t, t ∈ f i ∧ eval i ⁻¹' t ⊆ V i) ∧ ( …
    rintro ⟨I, If, V, hVf, -, rfl, -⟩
    -- ⊢ ∃ I_1, Set.Finite I_1 ∧ ∃ t, (∀ (i : ι), t i ∈ f i) ∧ ⋂ (a : ι) (_ : a ∈ I_1 …
    choose t htf htV using hVf
    -- ⊢ ∃ I_1, Set.Finite I_1 ∧ ∃ t, (∀ (i : ι), t i ∈ f i) ∧ ⋂ (a : ι) (_ : a ∈ I_1 …
    exact ⟨I, If, t, htf, iInter₂_mono fun i _ => htV i⟩
    -- 🎉 no goals
  · rintro ⟨I, If, t, htf, hts⟩
    -- ⊢ s ∈ pi f
    exact mem_of_superset (pi_mem_pi If fun i _ => htf i) hts
    -- 🎉 no goals
#align filter.mem_pi Filter.mem_pi

theorem mem_pi' {s : Set (∀ i, α i)} :
    s ∈ pi f ↔ ∃ I : Finset ι, ∃ t : ∀ i, Set (α i), (∀ i, t i ∈ f i) ∧ Set.pi (↑I) t ⊆ s :=
  mem_pi.trans exists_finite_iff_finset
#align filter.mem_pi' Filter.mem_pi'

theorem mem_of_pi_mem_pi [∀ i, NeBot (f i)] {I : Set ι} (h : I.pi s ∈ pi f) {i : ι} (hi : i ∈ I) :
    s i ∈ f i := by
  rcases mem_pi.1 h with ⟨I', -, t, htf, hts⟩
  -- ⊢ s i ∈ f i
  refine' mem_of_superset (htf i) fun x hx => _
  -- ⊢ x ∈ s i
  have : ∀ i, (t i).Nonempty := fun i => nonempty_of_mem (htf i)
  -- ⊢ x ∈ s i
  choose g hg using this
  -- ⊢ x ∈ s i
  have : update g i x ∈ I'.pi t := fun j _ => by
    rcases eq_or_ne j i with (rfl | hne) <;> simp [*]
  simpa using hts this i hi
  -- 🎉 no goals
#align filter.mem_of_pi_mem_pi Filter.mem_of_pi_mem_pi

@[simp]
theorem pi_mem_pi_iff [∀ i, NeBot (f i)] {I : Set ι} (hI : I.Finite) :
    I.pi s ∈ pi f ↔ ∀ i ∈ I, s i ∈ f i :=
  ⟨fun h _i hi => mem_of_pi_mem_pi h hi, pi_mem_pi hI⟩
#align filter.pi_mem_pi_iff Filter.pi_mem_pi_iff

theorem hasBasis_pi {ι' : ι → Type} {s : ∀ i, ι' i → Set (α i)} {p : ∀ i, ι' i → Prop}
    (h : ∀ i, (f i).HasBasis (p i) (s i)) :
    (pi f).HasBasis (fun If : Set ι × ∀ i, ι' i => If.1.Finite ∧ ∀ i ∈ If.1, p i (If.2 i))
      fun If : Set ι × ∀ i, ι' i => If.1.pi fun i => s i <| If.2 i := by
  simpa [Set.pi_def] using hasBasis_iInf' fun i => (h i).comap (eval i : (∀ j, α j) → α i)
  -- 🎉 no goals
#align filter.has_basis_pi Filter.hasBasis_pi

@[simp]
theorem pi_inf_principal_univ_pi_eq_bot :
    pi f ⊓ 𝓟 (Set.pi univ s) = ⊥ ↔ ∃ i, f i ⊓ 𝓟 (s i) = ⊥ := by
  constructor
  -- ⊢ pi f ⊓ 𝓟 (Set.pi univ s) = ⊥ → ∃ i, f i ⊓ 𝓟 (s i) = ⊥
  · simp only [inf_principal_eq_bot, mem_pi]
    -- ⊢ (∃ I, Set.Finite I ∧ ∃ t, (∀ (i : ι), t i ∈ f i) ∧ Set.pi I t ⊆ (Set.pi univ …
    contrapose!
    -- ⊢ (∀ (i : ι), ¬(s i)ᶜ ∈ f i) → ∀ (I : Set ι), Set.Finite I → ∀ (t : (i : ι) →  …
    rintro (hsf : ∀ i, ∃ᶠ x in f i, x ∈ s i) I - t htf hts
    -- ⊢ False
    have : ∀ i, (s i ∩ t i).Nonempty := fun i => ((hsf i).and_eventually (htf i)).exists
    -- ⊢ False
    choose x hxs hxt using this
    -- ⊢ False
    exact hts (fun i _ => hxt i) (mem_univ_pi.2 hxs)
    -- 🎉 no goals
  · simp only [inf_principal_eq_bot]
    -- ⊢ (∃ i, (s i)ᶜ ∈ f i) → (Set.pi univ s)ᶜ ∈ pi f
    rintro ⟨i, hi⟩
    -- ⊢ (Set.pi univ s)ᶜ ∈ pi f
    filter_upwards [mem_pi_of_mem i hi]with x using mt fun h => h i trivial
    -- 🎉 no goals
#align filter.pi_inf_principal_univ_pi_eq_bot Filter.pi_inf_principal_univ_pi_eq_bot

@[simp]
theorem pi_inf_principal_pi_eq_bot [∀ i, NeBot (f i)] {I : Set ι} :
    pi f ⊓ 𝓟 (Set.pi I s) = ⊥ ↔ ∃ i ∈ I, f i ⊓ 𝓟 (s i) = ⊥ := by
  rw [← univ_pi_piecewise_univ I, pi_inf_principal_univ_pi_eq_bot]
  -- ⊢ (∃ i, f i ⊓ 𝓟 (piecewise I s (fun x => univ) i) = ⊥) ↔ ∃ i, i ∈ I ∧ f i ⊓ 𝓟  …
  refine' exists_congr fun i => _
  -- ⊢ f i ⊓ 𝓟 (piecewise I s (fun x => univ) i) = ⊥ ↔ i ∈ I ∧ f i ⊓ 𝓟 (s i) = ⊥
  by_cases hi : i ∈ I <;> simp [hi, NeBot.ne']
  -- ⊢ f i ⊓ 𝓟 (piecewise I s (fun x => univ) i) = ⊥ ↔ i ∈ I ∧ f i ⊓ 𝓟 (s i) = ⊥
                          -- 🎉 no goals
                          -- 🎉 no goals
#align filter.pi_inf_principal_pi_eq_bot Filter.pi_inf_principal_pi_eq_bot

@[simp]
theorem pi_inf_principal_univ_pi_neBot :
    NeBot (pi f ⊓ 𝓟 (Set.pi univ s)) ↔ ∀ i, NeBot (f i ⊓ 𝓟 (s i)) := by simp [neBot_iff]
                                                                        -- 🎉 no goals
#align filter.pi_inf_principal_univ_pi_ne_bot Filter.pi_inf_principal_univ_pi_neBot

@[simp]
theorem pi_inf_principal_pi_neBot [∀ i, NeBot (f i)] {I : Set ι} :
    NeBot (pi f ⊓ 𝓟 (I.pi s)) ↔ ∀ i ∈ I, NeBot (f i ⊓ 𝓟 (s i)) := by simp [neBot_iff]
                                                                     -- 🎉 no goals
#align filter.pi_inf_principal_pi_ne_bot Filter.pi_inf_principal_pi_neBot

instance PiInfPrincipalPi.neBot [h : ∀ i, NeBot (f i ⊓ 𝓟 (s i))] {I : Set ι} :
    NeBot (pi f ⊓ 𝓟 (I.pi s)) :=
  (pi_inf_principal_univ_pi_neBot.2 ‹_›).mono <|
    inf_le_inf_left _ <| principal_mono.2 fun x hx i _ => hx i trivial
#align filter.pi_inf_principal_pi.ne_bot Filter.PiInfPrincipalPi.neBot

@[simp]
theorem pi_eq_bot : pi f = ⊥ ↔ ∃ i, f i = ⊥ := by
  simpa using @pi_inf_principal_univ_pi_eq_bot ι α f fun _ => univ
  -- 🎉 no goals
#align filter.pi_eq_bot Filter.pi_eq_bot

@[simp]
theorem pi_neBot : NeBot (pi f) ↔ ∀ i, NeBot (f i) := by simp [neBot_iff]
                                                         -- 🎉 no goals
#align filter.pi_ne_bot Filter.pi_neBot

instance [∀ i, NeBot (f i)] : NeBot (pi f) :=
  pi_neBot.2 ‹_›

@[simp]
theorem map_eval_pi (f : ∀ i, Filter (α i)) [∀ i, NeBot (f i)] (i : ι) :
    map (eval i) (pi f) = f i := by
  refine' le_antisymm (tendsto_eval_pi f i) fun s hs => _
  -- ⊢ s ∈ f i
  rcases mem_pi.1 (mem_map.1 hs) with ⟨I, hIf, t, htf, hI⟩
  -- ⊢ s ∈ f i
  rw [← image_subset_iff] at hI
  -- ⊢ s ∈ f i
  refine' mem_of_superset (htf i) ((subset_eval_image_pi _ _).trans hI)
  -- ⊢ Set.Nonempty (Set.pi I t)
  exact nonempty_of_mem (pi_mem_pi hIf fun i _ => htf i)
  -- 🎉 no goals
#align filter.map_eval_pi Filter.map_eval_pi

@[simp]
theorem pi_le_pi [∀ i, NeBot (f₁ i)] : pi f₁ ≤ pi f₂ ↔ ∀ i, f₁ i ≤ f₂ i :=
  ⟨fun h i => map_eval_pi f₁ i ▸ (tendsto_eval_pi _ _).mono_left h, pi_mono⟩
#align filter.pi_le_pi Filter.pi_le_pi

@[simp]
theorem pi_inj [∀ i, NeBot (f₁ i)] : pi f₁ = pi f₂ ↔ f₁ = f₂ := by
  refine' ⟨fun h => _, congr_arg pi⟩
  -- ⊢ f₁ = f₂
  have hle : f₁ ≤ f₂ := pi_le_pi.1 h.le
  -- ⊢ f₁ = f₂
  haveI : ∀ i, NeBot (f₂ i) := fun i => neBot_of_le (hle i)
  -- ⊢ f₁ = f₂
  exact hle.antisymm (pi_le_pi.1 h.ge)
  -- 🎉 no goals
#align filter.pi_inj Filter.pi_inj

end Pi

/-! ### `n`-ary coproducts of filters -/

section CoprodCat

-- for "Coprod"
set_option linter.uppercaseLean3 false

/-- Coproduct of filters. -/
protected def coprodᵢ (f : ∀ i, Filter (α i)) : Filter (∀ i, α i) :=
  ⨆ i : ι, comap (eval i) (f i)
#align filter.Coprod Filter.coprodᵢ

theorem mem_coprodᵢ_iff {s : Set (∀ i, α i)} :
    s ∈ Filter.coprodᵢ f ↔ ∀ i : ι, ∃ t₁ ∈ f i, eval i ⁻¹' t₁ ⊆ s := by simp [Filter.coprodᵢ]
                                                                        -- 🎉 no goals
#align filter.mem_Coprod_iff Filter.mem_coprodᵢ_iff

theorem compl_mem_coprodᵢ {s : Set (∀ i, α i)} :
    sᶜ ∈ Filter.coprodᵢ f ↔ ∀ i, (eval i '' s)ᶜ ∈ f i :=
  by simp only [Filter.coprodᵢ, mem_iSup, compl_mem_comap]
     -- 🎉 no goals
#align filter.compl_mem_Coprod Filter.compl_mem_coprodᵢ

theorem coprodᵢ_neBot_iff' :
    NeBot (Filter.coprodᵢ f) ↔ (∀ i, Nonempty (α i)) ∧ ∃ d, NeBot (f d) := by
  simp only [Filter.coprodᵢ, iSup_neBot, ← exists_and_left, ← comap_eval_neBot_iff']
  -- 🎉 no goals
#align filter.Coprod_ne_bot_iff' Filter.coprodᵢ_neBot_iff'

@[simp]
theorem coprodᵢ_neBot_iff [∀ i, Nonempty (α i)] : NeBot (Filter.coprodᵢ f) ↔ ∃ d, NeBot (f d) := by
  simp [coprodᵢ_neBot_iff', *]
  -- 🎉 no goals
#align filter.Coprod_ne_bot_iff Filter.coprodᵢ_neBot_iff

theorem coprodᵢ_eq_bot_iff' : Filter.coprodᵢ f = ⊥ ↔ (∃ i, IsEmpty (α i)) ∨ f = ⊥ := by
  simpa only [not_neBot, not_and_or, funext_iff, not_forall, not_exists, not_nonempty_iff]
    using coprodᵢ_neBot_iff'.not
#align filter.Coprod_eq_bot_iff' Filter.coprodᵢ_eq_bot_iff'

@[simp]
theorem coprodᵢ_eq_bot_iff [∀ i, Nonempty (α i)] : Filter.coprodᵢ f = ⊥ ↔ f = ⊥ := by
  simpa [funext_iff] using coprodᵢ_neBot_iff.not
  -- 🎉 no goals
#align filter.Coprod_eq_bot_iff Filter.coprodᵢ_eq_bot_iff

@[simp] theorem coprodᵢ_bot' : Filter.coprodᵢ (⊥ : ∀ i, Filter (α i)) = ⊥ :=
  coprodᵢ_eq_bot_iff'.2 (Or.inr rfl)
#align filter.Coprod_bot' Filter.coprodᵢ_bot'

@[simp]
theorem coprodᵢ_bot : Filter.coprodᵢ (fun _ => ⊥ : ∀ i, Filter (α i)) = ⊥ :=
  coprodᵢ_bot'
#align filter.Coprod_bot Filter.coprodᵢ_bot

theorem NeBot.coprodᵢ [∀ i, Nonempty (α i)] {i : ι} (h : NeBot (f i)) : NeBot (Filter.coprodᵢ f) :=
  coprodᵢ_neBot_iff.2 ⟨i, h⟩
#align filter.ne_bot.Coprod Filter.NeBot.coprodᵢ

@[instance]
theorem coprodᵢ_neBot [∀ i, Nonempty (α i)] [Nonempty ι] (f : ∀ i, Filter (α i))
    [H : ∀ i, NeBot (f i)] : NeBot (Filter.coprodᵢ f) :=
  (H (Classical.arbitrary ι)).coprodᵢ
#align filter.Coprod_ne_bot Filter.coprodᵢ_neBot

@[mono]
theorem coprodᵢ_mono (hf : ∀ i, f₁ i ≤ f₂ i) : Filter.coprodᵢ f₁ ≤ Filter.coprodᵢ f₂ :=
  iSup_mono fun i => comap_mono (hf i)
#align filter.Coprod_mono Filter.coprodᵢ_mono

variable {β : ι → Type*} {m : ∀ i, α i → β i}

theorem map_pi_map_coprodᵢ_le :
    map (fun k : ∀ i, α i => fun i => m i (k i)) (Filter.coprodᵢ f) ≤
      Filter.coprodᵢ fun i => map (m i) (f i) := by
  simp only [le_def, mem_map, mem_coprodᵢ_iff]
  -- ⊢ ∀ (x : Set ((i : ι) → β i)), (∀ (i : ι), ∃ t₁, m i ⁻¹' t₁ ∈ f i ∧ eval i ⁻¹' …
  intro s h i
  -- ⊢ ∃ t₁, t₁ ∈ f i ∧ eval i ⁻¹' t₁ ⊆ (fun k i => m i (k i)) ⁻¹' s
  obtain ⟨t, H, hH⟩ := h i
  -- ⊢ ∃ t₁, t₁ ∈ f i ∧ eval i ⁻¹' t₁ ⊆ (fun k i => m i (k i)) ⁻¹' s
  exact ⟨{ x : α i | m i x ∈ t }, H, fun x hx => hH hx⟩
  -- 🎉 no goals
#align filter.map_pi_map_Coprod_le Filter.map_pi_map_coprodᵢ_le

theorem Tendsto.pi_map_coprodᵢ {g : ∀ i, Filter (β i)} (h : ∀ i, Tendsto (m i) (f i) (g i)) :
    Tendsto (fun k : ∀ i, α i => fun i => m i (k i)) (Filter.coprodᵢ f) (Filter.coprodᵢ g) :=
  map_pi_map_coprodᵢ_le.trans (coprodᵢ_mono h)
#align filter.tendsto.pi_map_Coprod Filter.Tendsto.pi_map_coprodᵢ

end CoprodCat

end Filter
