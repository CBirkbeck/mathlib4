import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.KolmogorovExtension4.Projective
import Mathlib.KolmogorovExtension4.KolmogorovExtension
import Mathlib.Topology.Defs.Filter
-- import Mathlib.KolmogorovExtension4.section_file
import Mathlib.KolmogorovExtension4.DependsOn
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open Set MeasureTheory Filter Topology ENNReal Finset symmDiff

theorem preimage_proj {ι : Type*} {X : ι → Type*} (I J : Finset ι) [∀ i : ι, Decidable (i ∈ I)]
    (hIJ : I ⊆ J) (s : ∀ i : I, Set (X i)) :
    (fun t : (∀ j : J, X j) ↦ fun i : I ↦ t ⟨i, hIJ i.2⟩) ⁻¹' (univ.pi s) =
    (@Set.univ J).pi (fun j ↦ if h : j.1 ∈ I then s ⟨j.1, h⟩ else univ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Subtype.forall]
  refine ⟨fun h i hi ↦ ?_, fun h i i_mem ↦ by simpa [i_mem] using h i (hIJ i_mem)⟩
  split_ifs with i_mem
  · simp [i_mem, h i i_mem]
  · simp [i_mem]

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
variable (μ : (n : ℕ) → Measure (X n)) [hμ : ∀ n, IsProbabilityMeasure (μ n)]

theorem isProjectiveMeasureFamily_prod {ι : Type*} [∀ (S : Finset ι) i, Decidable (i ∈ S)]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (m : (i : ι) → Measure (α i)) [∀ i, IsProbabilityMeasure (m i)] :
    IsProjectiveMeasureFamily (fun S : Finset ι ↦ (Measure.pi (fun n : S ↦ m n))) := by
  intro T S hST
  refine Measure.pi_eq (fun s ms ↦ ?_)
  rw [Measure.map_apply (measurable_proj₂' (α := α) T S hST) (MeasurableSet.univ_pi ms),
    preimage_proj S T hST, Measure.pi_pi]
  have h1 : (@Finset.univ T _).prod (fun n ↦ (m n) (if hn : n.1 ∈ S then s ⟨n.1, hn⟩ else univ)) =
      (@Finset.univ T.toSet _).prod
      (fun n ↦ (fun k ↦ (m k) (if hk : k ∈ S then s ⟨k, hk⟩ else univ)) n) :=
    Finset.prod_congr rfl (by simp)
  have h2 : (@Finset.univ S _).prod (fun n ↦ (m n) (s n)) =
      (@Finset.univ S.toSet _).prod
      (fun n ↦ (fun k ↦ (m k) (if hk : k ∈ S then s ⟨k, hk⟩ else univ)) n) :=
    Finset.prod_congr rfl (by simp)
  rw [h1, h2, Finset.prod_set_coe
      (f := fun n ↦ (fun k ↦ (m k) (if hk : k ∈ S then s ⟨k, hk⟩ else univ)) n),
    Finset.prod_set_coe
      (f := fun n ↦ (fun k ↦ (m k) (if hk : k ∈ S then s ⟨k, hk⟩ else univ)) n),
    Finset.toFinset_coe, Finset.toFinset_coe,
    Finset.prod_subset hST (fun _ h h' ↦ by simp [h, h'])]

theorem dependsOn_cylinder_indicator {ι : Type*} {α : ι → Type*}
    (s : Finset ι) (S : Set ((i : s) → α i)) :
    DependsOn ((cylinder s S).indicator (1 : ((i : ι) → α i) → ℝ≥0∞)) s := by
  intro x y hxy
  have : x ∈ cylinder s S ↔ y ∈ cylinder s S := by simp [hxy]
  by_cases h : x ∈ cylinder s S
  · simp [h, this.1 h]
  · simp [h, this.not.1 h]

theorem cylinders_nat : cylinders X =
    ⋃ (N) (S) (_ : MeasurableSet S), {cylinder (Icc 0 N) S} := by
  ext s
  simp only [mem_cylinders, exists_prop, mem_iUnion, mem_singleton_iff]
  constructor
  · rintro ⟨t, S, mS, rfl⟩
    refine ⟨t.sup id, (fun (f : (∀ n : Finset.Icc 0 (t.sup id), X n)) (k : t) ↦
      f ⟨k.1, Finset.mem_Icc.2 ⟨Nat.zero_le k.1, Finset.le_sup (f := id) k.2⟩⟩) ⁻¹' S,
      by measurability, ?_⟩
    dsimp only [cylinder]
    rw [← preimage_comp]
    rfl
  · rintro ⟨N, S, mS, rfl⟩
    exact ⟨Finset.Icc 0 N, S, mS, rfl⟩

theorem eq {ι : Type*} [DecidableEq ι] [∀ (S : Finset ι) i, Decidable (i ∈ S)]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (ν : (i : ι) → Measure (α i)) [hν : ∀ i, IsProbabilityMeasure (ν i)]
    (I : Finset ι) {S : Set ((i : I) → α i)} (mS : MeasurableSet S) (x : (i : ι) → α i) :
    @kolContent _ _ _ _ (by have := fun i ↦ ProbabilityMeasure.nonempty ⟨ν i, hν i⟩; infer_instance)
    (isProjectiveMeasureFamily_prod ν) (cylinder I S) =
    (∫⋯∫⁻_I, (cylinder I S).indicator 1 ∂ν) x := by
  have : ∀ i, Nonempty (α i) := by
    have := fun i ↦ ProbabilityMeasure.nonempty ⟨ν i, hν i⟩;
    infer_instance
  rw [kolContent_congr (isProjectiveMeasureFamily_prod ν)
      (by rw [mem_cylinders]; exact ⟨I, S, mS, rfl⟩) rfl mS,
    ← lintegral_indicator_one₀ mS.nullMeasurableSet]
  refine lintegral_congr <| fun a ↦ ?_
  by_cases ha : a ∈ S <;> simp [ha, Function.updateFinset]

theorem Finset.Icc_eq_left_union (h : k ≤ N) : Finset.Icc k N = {k} ∪ (Finset.Icc (k + 1) N) := by
  ext x
  simp
  refine ⟨fun ⟨h1, h2⟩ ↦ ?_, ?_⟩
  · by_cases hxk : x = k
    · exact Or.inl hxk
    · exact Or.inr ⟨Nat.succ_le_of_lt <| Nat.lt_of_le_of_ne h1 (fun h ↦ hxk h.symm), h2⟩
  · rintro (h1 | ⟨h2, h3⟩)
    · exact ⟨h1 ▸ le_refl _, h1 ▸ h⟩
    · exact ⟨Nat.le_of_succ_le h2, h3⟩

theorem auxiliaire (f : ℕ → (∀ n, X n) → ℝ≥0∞) (N : ℕ → ℕ)
    (hcte : ∀ n, DependsOn (f n) (Finset.Icc 0 (N n))) (mf : ∀ n, Measurable (f n))
    (bound : ℝ≥0∞) (fin_bound : bound ≠ ∞) (le_bound : ∀ n x, f n x ≤ bound) (k : ℕ)
    (anti : ∀ x, Antitone (fun n ↦ (∫⋯∫⁻_Finset.Icc (k + 1) (N n), f n ∂μ) x))
    (l : ((n : ℕ) → X n) → ℝ≥0∞)
    (htendsto : ∀ x, Tendsto (fun n ↦ (∫⋯∫⁻_Finset.Icc (k + 1) (N n), f n ∂μ) x) atTop (𝓝 (l x)))
    (ε : ℝ≥0∞)
    (y : (n : Finset.Ico 0 k) → X n)
    (hpos : ∀ x, ∀ n,
    ε ≤ (∫⋯∫⁻_Finset.Icc k (N n), f n ∂μ) (Function.updateFinset x (Finset.Ico 0 k) y)) :
    ∃ z, ∀ x n, ε ≤ (∫⋯∫⁻_Finset.Icc (k + 1) (N n), f n ∂μ)
    (Function.update (Function.updateFinset x (Finset.Ico 0 k) y) k z) := by
  have : ∀ n, Nonempty (X n) := by
    have := fun n ↦ ProbabilityMeasure.nonempty ⟨μ n, hμ n⟩;
    infer_instance
  let F : ℕ → (∀ n, X n) → ℝ≥0∞ := fun n ↦ (∫⋯∫⁻_Finset.Icc (k + 1) (N n), f n ∂μ)
  have tendstoF x : Tendsto (F · x) atTop (𝓝 (l x)) := htendsto x
  have f_eq x n : (∫⋯∫⁻_Finset.Icc k (N n), f n ∂μ) x = (∫⋯∫⁻_{k}, F n ∂μ) x := by
    by_cases h : k ≤ N n
    · rw [Finset.Icc_eq_left_union h, lmarginal_union _ _ (mf n) (by simp)]
    · have : ¬k + 1 ≤ N n := fun h' ↦ h <| le_trans k.le_succ h'
      simp only [F]
      rw [Finset.Icc_eq_empty h, Finset.Icc_eq_empty this,
        lmarginal_eq_of_disjoint (hcte n) (by simp),
        lmarginal_eq_of_disjoint (hcte n) (by simp [h])]
  have F_le n x : F n x ≤ bound := by
    rw [← lmarginal_const (μ := μ) (s := Finset.Icc (k + 1) (N n)) bound x]
    apply lmarginal_mono <| le_bound n
  have tendsto_int x : Tendsto (fun n ↦ (∫⋯∫⁻_Finset.Icc k (N n), f n ∂μ) x) atTop
      (𝓝 ((∫⋯∫⁻_{k}, l ∂μ) x)) := by
    simp_rw [f_eq, lmarginal_singleton]
    exact tendsto_lintegral_of_dominated_convergence (fun _ ↦ bound)
      (fun n ↦ ((mf n).lmarginal μ).comp <| measurable_update ..)
      (fun n ↦ eventually_of_forall <| fun y ↦ F_le n _)
      (by simp [fin_bound])
      (eventually_of_forall (fun _ ↦ tendstoF _))
  have ε_le_lint x : ε ≤ (∫⋯∫⁻_{k}, l ∂μ) (Function.updateFinset x _ y) :=
    ge_of_tendsto (tendsto_int _) (by simp [hpos])
  have : ∀ x, ε ≤ ∫⁻ xₐ : X k,
    l (Function.update (Function.updateFinset x _ y) k xₐ) ∂μ k := by
    simpa [lmarginal_singleton] using ε_le_lint
  let x_ : ∀ n, X n := Classical.ofNonempty
  obtain ⟨x', hx'⟩ : ∃ x', ε ≤ l (Function.update (Function.updateFinset x_ _ y) k x') := by
    simp_rw [lmarginal_singleton] at ε_le_lint
    have aux : ∫⁻ (a : X k), l (Function.update (Function.updateFinset x_ _ y) k a) ∂μ k ≠ ⊤ := by
      apply ne_top_of_le_ne_top fin_bound
      rw [← mul_one bound, ← measure_univ (μ := μ k), ← lintegral_const]
      exact lintegral_mono <| fun y ↦ le_of_tendsto' (tendstoF _) <| fun _ ↦ F_le _ _
    rcases exists_lintegral_le aux with ⟨x', hx'⟩
    exact ⟨x', le_trans (this _) hx'⟩
  refine ⟨x', fun x n ↦ ?_⟩
  have := le_trans hx' ((anti _).le_of_tendsto (tendstoF _) n)
  have aux : F n (Function.update
      (Function.updateFinset x_ (Finset.Ico 0 k) y) k x') =
      F n (Function.update
      (Function.updateFinset x (Finset.Ico 0 k) y) k x') := by
    simp only [F]
    have := dependsOn_lmarginal (μ := μ) (hcte n) (Finset.Icc (k + 1) (N n))
    rw [← coe_sdiff] at this
    have := dependsOn_updateFinset (dependsOn_update this k x') (Finset.Ico 0 k) y
    have aux : (Finset.Icc 0 (N n) \ Finset.Icc (k + 1) (N n)).erase k \ Finset.Ico 0 k = ∅ := by
      ext i
      simp
      intro h1 h2 h3
      refine lt_iff_le_and_ne.2 ⟨?_, h1⟩
      by_contra!
      rw [← Nat.succ_le] at this
      linarith [h2, h3 this]
    rw [← coe_sdiff, aux, coe_empty] at this
    apply dependsOn_empty this
  simp [F] at aux
  rw [aux] at this
  exact this

def key (ind : (k : ℕ) → ((i : Finset.Ico 0 k) → X i) → X k) : (k : ℕ) → X k := fun k ↦ by
  use ind k (fun i ↦ key ind i)
  decreasing_by
  exact (Finset.mem_Ico.1 i.2).2

lemma not_mem_symmDiff {s t : Finset ℕ} {x : ℕ} :
    (x ∈ s ∧ x ∈ t) ∨ (x ∉ s ∧ x ∉ t) → x ∉ s ∆ t := by
  rw [Finset.mem_symmDiff.not]
  push_neg
  rintro (⟨hs, ht⟩ | ⟨hs, ht⟩) <;> simp [hs, ht]

theorem firstLemma (A : ℕ → Set (∀ n, X n)) (A_mem : ∀ n, A n ∈ cylinders X) (A_anti : Antitone A)
    (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n ↦ @kolContent _ _ _ _
    (by have := fun n ↦ ProbabilityMeasure.nonempty ⟨μ n, hμ n⟩; infer_instance)
    (isProjectiveMeasureFamily_prod μ) (A n)) atTop (𝓝 0) := by
  have : ∀ n, Nonempty (X n) := by
    have := fun n ↦ ProbabilityMeasure.nonempty ⟨μ n, hμ n⟩;
    infer_instance
  have A_cyl n : ∃ N S, MeasurableSet S ∧ A n = cylinder (Finset.Icc 0 N) S := by
    simpa [cylinders_nat] using A_mem n
  choose N S mS A_eq using A_cyl
  set μ_proj := isProjectiveMeasureFamily_prod μ
  let χ := fun n ↦ (A n).indicator (1 : (∀ n, X n) → ℝ≥0∞)
  have concl x n : kolContent μ_proj (A n) = (∫⋯∫⁻_Finset.Icc 0 (N n), χ n ∂μ) x := by
    simp only [χ, A_eq]
    exact eq μ (Finset.Icc 0 (N n)) (mS n) x
  have mχ n : Measurable (χ n) := by
    simp only [χ, A_eq]
    exact (measurable_indicator_const_iff 1).2 <| measurableSet_cylinder _ _ (mS n)
  have χ_dep n : DependsOn (χ n) (Finset.Icc 0 (N n)) := by
    simp only [χ, A_eq]
    exact dependsOn_cylinder_indicator _ _
  have lma_const x y n : (∫⋯∫⁻_Finset.Icc 0 (N n), χ n ∂μ) x =
      (∫⋯∫⁻_Finset.Icc 0 (N n), χ n ∂μ) y := by
    apply dependsOn_lmarginal (μ := μ) (χ_dep n) (Finset.Icc 0 (N n))
    simp
  have χ_anti : Antitone χ := by
    intro m n hmn y
    apply indicator_le
    exact fun a ha ↦ by simp [χ, A_anti hmn ha]
  have lma_inv k M n : N n ≤ M →
      ∫⋯∫⁻_Finset.Icc k M, χ n ∂μ = ∫⋯∫⁻_Finset.Icc k (N n), χ n ∂μ := by
    intro h
    apply lmarginal_eq_of_disjoint_diff (mχ n) (χ_dep n)
    · exact Finset.Icc_subset_Icc_right h
    · rw [← coe_sdiff, Finset.disjoint_coe, Finset.disjoint_iff_inter_eq_empty]
      ext i
      simp only [Finset.mem_inter, Finset.mem_Icc, zero_le, true_and, mem_sdiff, not_and, not_le,
        Finset.not_mem_empty, iff_false, Classical.not_imp, not_lt, and_imp]
      exact fun h1 h2 _ ↦ ⟨h2, h1⟩
  have anti_lma k x : Antitone fun n ↦ (∫⋯∫⁻_Finset.Icc k (N n), χ n ∂μ) x := by
    intro m n hmn
    simp only
    rw [← lma_inv k ((N n).max (N m)) n (le_max_left _ _),
      ← lma_inv k ((N n).max (N m)) m (le_max_right _ _)]
    exact lmarginal_mono (χ_anti hmn) x
  have this k x : ∃ l, Tendsto (fun n ↦ (∫⋯∫⁻_Finset.Icc k (N n), χ n ∂μ) x) atTop (𝓝 l) := by
    rcases tendsto_of_antitone <| anti_lma k x with h | h
    · rw [OrderBot.atBot_eq] at h
      exact ⟨0, h.mono_right <| pure_le_nhds 0⟩
    · exact h
  choose l hl using this
  have l_const x y : l 0 x = l 0 y := by
    have := hl 0 x
    simp_rw [lma_const x y] at this
    exact tendsto_nhds_unique this (hl 0 _)
  obtain ⟨ε, hε⟩ : ∃ ε, ∀ x, l 0 x = ε := ⟨l 0 Classical.ofNonempty, fun x ↦ l_const ..⟩
  have hpos x n : ε ≤ (∫⋯∫⁻_Finset.Icc 0 (N n), χ n ∂μ) x :=
    hε x ▸ ((anti_lma 0 _).le_of_tendsto (hl 0 _)) n
  have χ_le n x : χ n x ≤ 1 := by
    apply Set.indicator_le
    simp
  rcases auxiliaire μ χ N χ_dep mχ 1 (by norm_num) χ_le 0 (anti_lma 1) (l 1) (hl 1) ε
    Classical.ofNonempty hpos with ⟨init, hinit⟩
  simp [Function.updateFinset_def] at hinit
  choose! ind hind using
    fun k y h ↦ auxiliaire μ χ N χ_dep mχ 1 (by norm_num) χ_le k (anti_lma (k + 1))
      (l (k + 1)) (hl (k + 1)) ε y h
  -- let z := key ind
  have crucial : ∀ k x n, ε ≤ (∫⋯∫⁻_Finset.Icc k (N n), χ n ∂μ)
      (Function.updateFinset x (Finset.Ico 0 k) (fun i ↦ key ind i)) := by
    intro k
    induction k with
    | zero =>
      intro x n
      rw [Finset.Ico_self 0, Function.updateFinset_empty]
      exact hpos x n
    | succ m hm =>
      intro x n
      have : Function.updateFinset x (Finset.Ico 0 (m + 1)) (fun i ↦ key ind i) =
          Function.update (Function.updateFinset x (Finset.Ico 0 m) (fun i ↦ key ind i))
          m (key ind m) := by
        ext i
        simp [Function.updateFinset, Function.update]
        split_ifs with h1 h2 h3 h4 h5
        · aesop
        · rfl
        · rw [Nat.lt_succ] at h1
          exact (not_or.2 ⟨h2, h3⟩ <| le_iff_eq_or_lt.1 h1).elim
        · rw [h4] at h1
          exfalso
          linarith [h1]
        · exact (h1 <| lt_trans h5 m.lt_succ_self).elim
        · rfl
      rw [this]
      convert hind m (fun i ↦ key ind i) hm x n
      induction m with
      | zero => aesop
      | succ _ _ => rfl
  by_cases ε_eq : 0 < ε
  · have incr : ∀ n, key ind ∈ A n := by
      intro n
      have : χ n (key ind) = (∫⋯∫⁻_Finset.Icc (N n + 1) (N n), χ n ∂μ)
          (Function.updateFinset (key ind) (Finset.Ico 0 (N n + 1)) (fun i ↦ key ind i)) := by
        rw [Finset.Icc_eq_empty, lmarginal_empty]
        · congr
          ext i
          by_cases h : i ∈ Finset.Ico 0 (N n + 1) <;> simp [Function.updateFinset, h]
        · simp
      have : 0 < χ n (key ind) := by
        rw [this]
        exact lt_of_lt_of_le ε_eq (crucial (N n + 1) (key ind) n)
      exact mem_of_indicator_ne_zero (ne_of_lt this).symm
    exact (A_inter ▸ mem_iInter.2 incr).elim
  · have : ε = 0 := nonpos_iff_eq_zero.1 <| not_lt.1 ε_eq
    simp_rw [concl Classical.ofNonempty]
    rw [← this, ← hε Classical.ofNonempty]
    exact hl _ _

variable {ι : Type*} [DecidableEq ι] [∀ (I : Set ι) i, Decidable (i ∈ I)]
variable {α : ι → Type*} [hα : ∀ i, MeasurableSpace (α i)]
variable (ν : (i : ι) → Measure (α i)) [hν : ∀ i, IsProbabilityMeasure (ν i)]

lemma omg (s : Set ι) (x : (i : s) → α i) (i j : s) (h : i = j) (h' : α i = α j) :
    cast h' (x i) = x j := by
  aesop_subst h
  rfl

lemma omg' (a b : Type _) (h : a = b) (x : a) (t : Set a) (h' : Set a = Set b) :
    (cast h x ∈ cast h' t) = (x ∈ t) := by
  aesop_subst h
  rfl

theorem secondLemma (φ : ℕ ≃ ι)
    (A : ℕ → Set ((i : ι) → α i)) (A_mem : ∀ n, A n ∈ cylinders α) (A_anti : Antitone A)
    (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n ↦ @kolContent _ _ _ _
    (by have := fun i ↦ ProbabilityMeasure.nonempty ⟨ν i, hν i⟩; infer_instance)
    (isProjectiveMeasureFamily_prod ν) (A n)) atTop (𝓝 0) := by
  have : ∀ i, Nonempty (α i) := by
    have := fun i ↦ ProbabilityMeasure.nonempty ⟨ν i, hν i⟩;
    infer_instance
  set ν_proj := isProjectiveMeasureFamily_prod ν
  let ν_proj' := isProjectiveMeasureFamily_prod (fun k : ℕ ↦ ν (φ k))
  have A_cyl n : ∃ s S, MeasurableSet S ∧ A n = cylinder s S := by
    simpa only [mem_cylinders, exists_prop] using A_mem n
  choose s S mS A_eq using A_cyl
  let u n := (s n).preimage φ (φ.injective.injOn _)
  have h i : α (φ (φ.symm i)) = α i := by simp
  have e n i (h : i ∈ s n) : φ.symm i ∈ u n := by simpa [u] using h
  have e' n k (h : k ∈ u n) : φ k ∈ s n := by simpa [u] using h
  let f : ((k : ℕ) → α (φ k)) → (i : ι) → α i := fun x i ↦ cast (h i) (x (φ.symm i))
  let aux n : (s n ≃ u n) := {
    toFun := fun i ↦ ⟨φ.symm i, e n i.1 i.2⟩
    invFun := fun k ↦ ⟨φ k, e' n k.1 k.2⟩
    left_inv := by simp [Function.LeftInverse]
    right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  }
  let g n : ((k : u n) → α (φ k)) → (i : s n) → α i :=
    fun x i ↦ cast (h i) (x (aux n i))
  have test n : (fun (x : (i : ι) → α i) (i : s n) ↦ x i) ∘ f =
      (g n) ∘ (fun (x : (k : ℕ) → α (φ k)) (k : u n) ↦ x k) := by
    ext x
    simp [f, g, aux]
  let B n := f ⁻¹' (A n)
  let T n := (g n) ⁻¹' (S n)
  have B_eq n : B n = cylinder (u n) (T n) := by
    simp_rw [B, A_eq, cylinder, ← preimage_comp, test n]
    rfl
  have meas n : Measurable (g n) := by
    simp only [g]
    refine measurable_pi_lambda _ (fun i ↦ ?_)
    have : (fun c : (k : u n) → α (φ k) ↦ cast (h i) (c (aux n i))) =
        ((fun a ↦ cast (h i) a) ∘ (fun x ↦ x (aux n i))) := by
      ext x
      simp
    rw [this]
    apply Measurable.comp
    · have aux1 : HEq (hα i) (hα (φ (φ.symm i))) := by
        have := h i
        rw [← cast_eq_iff_heq (e := by simp [this])]
        exact @omg ι (fun i ↦ MeasurableSpace (α i)) (s n) (fun i ↦ hα i)
          i ⟨φ (φ.symm i), by simp [i.2]⟩ (by simp) _
      let f := MeasurableEquiv.cast (h i).symm aux1
      have aux2 : (fun a : α (φ (φ.symm i)) ↦ cast (h i) a) = f.symm := by
        ext a
        simp [f, MeasurableEquiv.cast]
      rw [aux2]
      exact f.measurable_invFun
    · apply @measurable_pi_apply (u n) (fun k ↦ α (φ k)) _ (aux n i)
  have imp n (t : (i : s n) → Set (α i)) : (g n) ⁻¹' (Set.univ.pi t) =
      Set.univ.pi (fun k : u n ↦ t ⟨φ k, e' n k.1 k.2⟩) := by
    ext x
    simp [g]
    constructor
    · intro h' k hk
      convert h' (φ k) (e' n k hk)
      simp [aux]
      have : (⟨φ.symm (φ k), by simp [hk]⟩ : u n) = ⟨k, hk⟩ := by simp
      rw [omg (ι := ℕ) (α := fun k ↦ α (φ k)) (u n) x ⟨φ.symm (φ k), by simp [hk]⟩ ⟨k, hk⟩]
      · simp
    · intro h' i hi
      convert h' (φ.symm i) (e n i hi)
      simp [aux]
      have : cast (congrArg Set (h i)) (t ⟨φ (φ.symm i), by simp [hi]⟩) = t ⟨i, hi⟩ := by
        have : (⟨i, hi⟩ : s n) = ⟨φ (φ.symm i), by simp [hi]⟩ := by simp
        exact @omg ι (fun i ↦ Set (α i)) (s n) t ⟨φ (φ.symm i), by simp [hi]⟩ ⟨i, hi⟩ this.symm _
      rw [← this]
      rw [omg' (α (φ (φ.symm i))) (α i) (by simp) (x ⟨φ.symm i, e n i hi⟩)
          (t ⟨φ (φ.symm i), by simp [hi]⟩) (by simp)]
  have test' n : Measure.pi (fun i : s n ↦ ν i) =
      (Measure.pi (fun k : u n ↦ ν (φ k))).map (g n) := by
    refine Measure.pi_eq (fun x mx ↦ ?_)
    rw [Measure.map_apply, imp n, Measure.pi_pi, Fintype.prod_equiv (aux n).symm
      _ (fun i ↦ (ν i) (x i))]
    · simp [aux]
    · exact meas n
    · apply MeasurableSet.pi
      · exact countable_univ
      · simp [mx]
  have mT n : MeasurableSet (T n) := (mS n).preimage (meas n)
  have crucial n : kolContent ν_proj (A n) = kolContent ν_proj' (B n) := by
    simp_rw [fun n ↦ kolContent_congr ν_proj
      (by rw [mem_cylinders]; exact ⟨s n, S n, mS n, A_eq n⟩) (A_eq n) (mS n),
      fun n ↦ kolContent_congr ν_proj'
      (by rw [mem_cylinders]; exact ⟨u n, T n, mT n, B_eq n⟩) (B_eq n) (mT n), T, test' n]
    rw [Measure.map_apply]
    · exact meas n
    · exact mS n
  have B_anti : Antitone B := by
    intro m n hmn
    exact preimage_mono <| A_anti hmn
  have B_inter : ⋂ n, B n = ∅ := by
    simp_rw [B, ← preimage_iInter, A_inter, Set.preimage_empty]
  simp_rw [crucial]
  refine firstLemma (fun k ↦ ν (φ k)) B ?_ B_anti B_inter
  exact fun n ↦ (mem_cylinders (B n)).2 ⟨u n, T n, mT n, B_eq n⟩

-- theorem secondLemma (φ : ℕ ≃ ι)
--     (A : ℕ → Set ((i : ι) → α i)) (A_mem : ∀ n, A n ∈ cylinders α) (A_anti : Antitone A)
--     (A_inter : ⋂ n, A n = ∅) :
--     Tendsto (fun n ↦ @kolContent _ _ _ _
--     (by have := fun i ↦ ProbabilityMeasure.nonempty ⟨ν i, hν i⟩; infer_instance)
--     (isProjectiveMeasureFamily_prod ν) (A n)) atTop (𝓝 0) := by
--   have : ∀ i, Nonempty (α i) := by
--     have := fun i ↦ ProbabilityMeasure.nonempty ⟨ν i, hν i⟩;
--     infer_instance
--   set ν_proj := isProjectiveMeasureFamily_prod ν
--   let ν_proj' := isProjectiveMeasureFamily_prod (fun k : ℕ ↦ ν (φ k))
--   have A_cyl n : ∃ s S, MeasurableSet S ∧ A n = cylinder s S := by
--     simpa only [mem_cylinders, exists_prop] using A_mem n
--   choose s S mS A_eq using A_cyl
--   have l' k : (fun k ↦ α (φ k)) k = α (φ k) := rfl
--   let l k : (fun k ↦ α (φ k)) k ≃ α (φ k) := Equiv.cast (l' k)
--   let u n := (s n).preimage φ (φ.injective.injOn _)
--   let b n : u n ≃ s n := {
--     toFun := fun k ↦ ⟨φ k, e' n k k.2⟩
--     invFun := fun i ↦ ⟨φ.symm i, e n i i.2⟩
--     left_inv := by simp [Function.LeftInverse]
--     right_inv := by simp [Function.RightInverse, Function.LeftInverse]
--   }
--   let a n k : (fun k : u n ↦ α (φ k)) k ≃ (fun i : s n ↦ α i) (φ k) := rfl
--   have e n i (h : i ∈ s n) : φ.symm i ∈ u n := by simpa [u] using h
--   have e' n k (h : k ∈ u n) : φ k ∈ s n := by simpa [u] using h
--   have h i : α (φ (φ.symm i)) = α i := by simp
--   let f : ((k : ℕ) → α (φ k)) ≃ ((i : ι) → α i) := φ.piCongr l
--   let g n : ((k : u n) → α (φ k)) → (i : s n) → α i := (b n).piCongr l'
--   have test n : (fun (x : (i : ι) → α i) (i : s n) ↦ x i) ∘ f =
--       (g n) ∘ (fun (x : (k : ℕ) → α (φ k)) (k : u n) ↦ x k) := by
--     ext x
--     simp [f, g, aux]
--   let B n := f ⁻¹' (A n)
--   let T n := (g n) ⁻¹' (S n)
--   have B_eq n : B n = cylinder (u n) (T n) := by
--     simp_rw [B, A_eq, cylinder, ← preimage_comp, test n]
--     rfl
--   have meas n : Measurable (g n) := by
--     simp only [g]
--     apply measurable_pi_lambda
--     exact fun a ↦ measurable_pi_apply _
--   have imp n (t : (i : s n) → Set (α i)) : (g n) ⁻¹' (Set.univ.pi t) =
--       Set.univ.pi (fun k : u n ↦ t ⟨φ k, e' n k.1 k.2⟩) := by
--     ext x
--     simp [g]
--     constructor
--     · intro h k hk
--       convert h (aux n ⟨k, hk⟩) (e' n k hk)
--       rw [← @Equiv.piCongrLeft_apply_eq_cast (s n) (u n) (fun i ↦ α i) (aux n) x,
--         @Equiv.piCongrLeft_apply_apply (s n) (u n) (fun i ↦ α i) (aux n) x]
--     · intro h i hi
--       sorry
--   have test' n : Measure.pi (fun i : s n ↦ ν i) =
--       (Measure.pi (fun k : u n ↦ ν (φ k))).map (g n) := by
--     refine Measure.pi_eq (fun x mx ↦ ?_)
--     rw [Measure.map_apply, imp n, Measure.pi_pi, Fintype.prod_equiv (aux n)
--       _ (fun i ↦ (ν i) (x i))]
--     · simp [aux]
--     · exact meas n
--     · apply MeasurableSet.pi
--       · exact countable_univ
--       · simp [mx]
--   have mT n : MeasurableSet (T n) := (mS n).preimage (meas n)
--   have crucial n : kolContent ν_proj (A n) = kolContent ν_proj' (B n) := by
--     simp_rw [fun n ↦ kolContent_congr ν_proj
--       (by rw [mem_cylinders]; exact ⟨s n, S n, mS n, A_eq n⟩) (A_eq n) (mS n),
--       fun n ↦ kolContent_congr ν_proj'
--       (by rw [mem_cylinders]; exact ⟨u n, T n, mT n, B_eq n⟩) (B_eq n) (mT n), T, test' n]
--     rw [Measure.map_apply]
--     · exact meas n
--     · exact mS n
--   have B_anti : Antitone B := by
--     intro m n hmn
--     exact preimage_mono <| A_anti hmn
--   have B_inter : ⋂ n, B n = ∅ := by
--     simp_rw [B, ← preimage_iInter, A_inter, Set.preimage_empty]
--   simp_rw [crucial]
--   refine firstLemma (fun k ↦ ν (φ k)) B ?_ B_anti B_inter
--   exact fun n ↦ (mem_cylinders (B n)).2 ⟨u n, T n, mT n, B_eq n⟩

theorem thirdLemma (A : ℕ → Set (∀ i, α i)) (A_mem : ∀ n, A n ∈ cylinders α) (A_anti : Antitone A)
    (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n ↦ @kolContent _ _ _ _
    (by have := fun i ↦ ProbabilityMeasure.nonempty ⟨ν i, hν i⟩; infer_instance)
    (isProjectiveMeasureFamily_prod ν) (A n)) atTop (𝓝 0) := by
  have : ∀ i, Nonempty (α i) := by
    have := fun i ↦ ProbabilityMeasure.nonempty ⟨ν i, hν i⟩
    infer_instance
  set ν_proj := isProjectiveMeasureFamily_prod ν
  choose s S mS A_eq using fun n ↦ (mem_cylinders (A n)).1 (A_mem n)
  let t := ⋃ n, (s n).toSet
  -- have count_t : t.Countable := Set.countable_iUnion (fun n ↦ (s n).countable_toSet)
  -- rcases count_t.exists_injective_nat' with ⟨f, hf⟩
  let u : ℕ → Finset t := fun n ↦ (s n).preimage Subtype.val (Subtype.val_injective.injOn _)
  have u_eq : ∀ n, ((u n).toSet : Set ι) = s n := by
    intro n
    rw [(s n).coe_preimage (Subtype.val_injective.injOn _)]
    ext i
    simp only [Subtype.image_preimage_coe, mem_inter_iff, mem_coe, and_iff_right_iff_imp]
    exact fun hi ↦ mem_iUnion.2 ⟨n, hi⟩
  let aux : (n : ℕ) → (s n ≃ u n) := fun n ↦ {
    toFun := by
      intro i
      have hi : i.1 ∈ t := mem_iUnion.2 ⟨n, i.2⟩
      have hi' : ⟨i.1, hi⟩ ∈ u n := by simp [u]
      exact ⟨⟨i.1, hi⟩, hi'⟩
    invFun := by
      intro i
      have : i.1.1 ∈ s n := by
        rw [← Finset.mem_coe, ← u_eq n]
        exact ⟨i.1, i.2, rfl⟩
      exact ⟨i.1.1, this⟩
    left_inv := by simp only [Function.LeftInverse, Subtype.coe_eta, implies_true]
    right_inv := by simp only [Function.RightInverse, Function.LeftInverse, Subtype.coe_eta,
      implies_true]
  }
  -- have this n i : (aux n i).1.1 = i.1 := rfl
  have et n (i : s n) : α (aux n i) = α i.1 := rfl
  have imp n (x : (i : s n) → Set (α i)) :
      Set.univ.pi (fun i : u n ↦ x ((aux n).invFun i)) =
      (fun x i ↦ cast (et n i) (x (aux n i))) ⁻¹' Set.univ.pi x
       := by
    ext y
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Subtype.forall, Set.mem_preimage]
    constructor
    · intro h i hi
      exact h i (mem_iUnion.2 ⟨n, hi⟩) (by simpa [u] using hi)
    · intro h i hi1 hi2
      have : i ∈ s n := by simpa [u] using hi2
      exact h i this
  have meas n : Measurable (fun (x : (i : u n) → α i) i ↦ cast (et n i) (x (aux n i))) := by
    apply measurable_pi_lambda
    exact fun a ↦ measurable_pi_apply _
  have crucial n : Measure.pi (fun i : s n ↦ ν i) =
      (Measure.pi (fun i : u n ↦ ν i)).map
      (fun x i ↦ cast (et n i) (x (aux n i)))
       := by
    refine Measure.pi_eq (fun x mx ↦ ?_)
    rw [Measure.map_apply, ← imp n x, Measure.pi_pi, Fintype.prod_equiv (aux n)]
    · intro i
      rfl
    · exact meas _
    · apply MeasurableSet.pi
      · exact countable_univ
      · simp only [Set.mem_univ, mx, imp_self, implies_true]
  let T : (n : ℕ) → Set ((i : u n) → α i) :=
    fun n ↦ (fun x i ↦ cast (et n i) (x (aux n i))) ⁻¹' (S n)
  have mT n : MeasurableSet (T n) := by
    apply (mS n).preimage (meas _)
  let B : ℕ → Set (∀ i : t, α i) := fun n ↦ cylinder (u n) (T n)
  have B_eq n : B n = (fun x : (i : t) → α i ↦ fun i ↦ if hi : i ∈ t
      then x ⟨i, hi⟩ else Classical.ofNonempty) ⁻¹' (A n) := by
    ext x
    simp [B, T, -cast_eq]
    have this k : (fun i : s k ↦ (fun j ↦ if hj : j ∈ t
        then x ⟨j, hj⟩
        else Classical.ofNonempty) i.1) = fun i ↦ cast (et k i) (x (aux k i)) := by
      ext i
      have : i.1 ∈ t := mem_iUnion.2 ⟨k, i.2⟩
      simp only [i.2, this, ↓reduceDite, cast_eq]
      rfl
    rw [← this, ← mem_cylinder (s n) (S n)
      (fun j ↦ if hj : j ∈ t
        then x ⟨j, hj⟩
        else Classical.ofNonempty), ← A_eq]
  have B_anti : Antitone B := by
    intro m n hmn
    simp_rw [B_eq]
    exact preimage_mono <| A_anti hmn
  have B_inter : ⋂ n, B n = ∅ := by
    simp_rw [B_eq, ← preimage_iInter, A_inter, Set.preimage_empty]
  let ν_proj' := isProjectiveMeasureFamily_prod (fun i : t ↦ ν i)
  have this n : kolContent ν_proj (A n) = kolContent ν_proj' (B n) := by
    simp_rw [fun n ↦ kolContent_congr ν_proj
      (by rw [mem_cylinders]; exact ⟨s n, S n, mS n, A_eq n⟩) (A_eq n) (mS n),
      fun n ↦ kolContent_congr ν_proj'
      (by rw [mem_cylinders]; exact ⟨u n, T n, mT n, rfl⟩) rfl (mT n), T, crucial n]
    rw [Measure.map_apply]
    · simp only [cast_eq]
      exact meas _
    · exact mS n
  simp_rw [this]
  -- have : ∀ i : t, MeasurableSpace (α i) := inferInstance
  rcases finite_or_infinite t with (t_fin | t_inf)
  · have obv : (fun _ ↦ 1 : ((i : t) → α i) → ℝ≥0∞) = 1 := rfl
    have := Fintype.ofFinite t
    have concl n : kolContent ν_proj' (B n) =
        (Measure.pi (fun i : t ↦ ν i)) (cylinder (u n) (T n)) := by
      simp_rw [B, fun n ↦ eq (fun i : t ↦ ν i) (u n) (mT n) Classical.ofNonempty]
      rw [← lmarginal_eq_of_disjoint_diff (μ := (fun i : t ↦ ν i)) _
        (dependsOn_cylinder_indicator (u n) (T n))
        (u n).subset_univ, lmarginal_univ, ← obv,
        lintegral_indicator_const]
      simp
      · exact @measurableSet_cylinder t (fun i : t ↦ α i) _ (u n) (T n) (mT n)
      · rw [Finset.coe_univ, ← compl_eq_univ_diff]
        exact disjoint_compl_right
      · rw [← obv, measurable_indicator_const_iff 1]
        exact @measurableSet_cylinder t (fun i : t ↦ α i) _ (u n) (T n) (mT n)
    simp_rw [concl, ← measure_empty (μ := Measure.pi (fun i : t ↦ ν i)), ← B_inter]
    exact tendsto_measure_iInter (fun n ↦ measurableSet_cylinder (u n) (T n) (mT n))
      B_anti ⟨0, measure_ne_top _ _⟩
  · have count_t : Countable t := Set.countable_iUnion (fun n ↦ (s n).countable_toSet)
    -- have := nonempty_equiv_of_countable N t
    obtain ⟨φ, -⟩ := Classical.exists_true_of_nonempty (α := ℕ ≃ t) nonempty_equiv_of_countable
    refine secondLemma (fun i : t ↦ ν i) φ B (fun n ↦ ?_) B_anti B_inter
    simp
    exact ⟨u n, T n, mT n, rfl⟩

-- theorem kolContent_sigma_subadditive ⦃f : ℕ → Set (∀ n, X n)⦄
--     (hf : ∀ i, f i ∈ cylinders X) (hf_Union : (⋃ i, f i) ∈ cylinders X) :
--     @kolContent _ _ _ _ (by have := fun n ↦ ProbabilityMeasure.nonempty ⟨μ n, hμ n⟩; infer_instance)
--     (isProjectiveMeasureFamily_prod μ) (⋃ i, f i) ≤
--     ∑' i, @kolContent _ _ _ _
--     (by have := fun n ↦ ProbabilityMeasure.nonempty ⟨μ n, hμ n⟩; infer_instance)
--     (isProjectiveMeasureFamily_prod μ) (f i) := by
--   have : ∀ n, Nonempty (X n) := by
--     have := fun n ↦ ProbabilityMeasure.nonempty ⟨μ n, hμ n⟩;
--     infer_instance
--   refine (kolContent (isProjectiveMeasureFamily_prod μ)).sigma_subadditive_of_sigma_additive
--     setRing_cylinders (fun f hf hf_Union hf' ↦ ?_) f hf hf_Union
--   refine sigma_additive_addContent_of_tendsto_zero setRing_cylinders
--     (kolContent (isProjectiveMeasureFamily_prod μ)) (fun hs ↦ ?_) ?_ hf hf_Union hf'
--   · rename_i s
--     rcases useful _ hs with ⟨N, S, mS, s_eq⟩
--     rw [s_eq, eq μ (mS := mS) (x := Classical.ofNonempty)]
--     refine ne_of_lt (lt_of_le_of_lt ?_ (by norm_num : (1 : ℝ≥0∞) < ⊤))
--     rw [← lmarginal_const (μ := μ) (s := Finset.Icc 0 N) 1 Classical.ofNonempty]
--     apply lmarginal_mono
--     intro x
--     apply Set.indicator_le
--     simp
--   · intro s hs anti_s inter_s
--     exact firstLemma μ s hs anti_s inter_s

-- noncomputable def measure_produit : Measure (∀ n, X n) := by
--   have : ∀ n, Nonempty (X n) := by
--     have := fun n ↦ ProbabilityMeasure.nonempty ⟨μ n, hμ n⟩;
--     infer_instance
--   exact Measure.ofAddContent setSemiringCylinders generateFrom_cylinders
--     (kolContent (isProjectiveMeasureFamily_prod μ))
--     (kolContent_sigma_subadditive μ)

-- theorem isProjectiveLimit_measure_produit :
--     IsProjectiveLimit (measure_produit μ) (fun S : Finset ℕ ↦ (Measure.pi (fun n : S ↦ μ n))) := by
--   have : ∀ n, Nonempty (X n) := by
--     have := fun n ↦ ProbabilityMeasure.nonempty ⟨μ n, hμ n⟩;
--     infer_instance
--   intro S
--   ext1 s hs
--   rw [Measure.map_apply _ hs]
--   swap; · apply measurable_proj
--   have h_mem : (fun (x : ∀ n : ℕ, (fun i : ℕ ↦ X i) n) (n : ↥S) ↦ x ↑n) ⁻¹' s ∈ cylinders X := by
--     rw [mem_cylinders]; exact ⟨S, s, hs, rfl⟩
--   rw [measure_produit, Measure.ofAddContent_eq _ _ _ _ h_mem,
--     kolContent_congr (isProjectiveMeasureFamily_prod μ) h_mem rfl hs]

-- theorem prod_meas (S : Finset ℕ) (a : ℕ) (ha : a ∈ S) (μ : (n : S) → Measure (X n))
--     [∀ n, IsProbabilityMeasure (μ n)]
--     (s : (n : S) → Set (X n)) :
--     (Measure.pi μ) (univ.pi s) = ((μ ⟨a, ha⟩) (s ⟨a, ha⟩)) *
--     ((Measure.pi (fun (n : S.erase a) ↦ μ ⟨n.1, Finset.mem_of_mem_erase n.2⟩))
--     (univ.pi (fun n : S.erase a ↦ s ⟨n.1, Finset.mem_of_mem_erase n.2⟩))) := by
--   rw [Measure.pi_pi, Measure.pi_pi, mul_comm]
--   have h1 : (@Finset.univ S _).prod (fun n ↦ (μ n) (s n)) =
--       (@Finset.univ S.toSet _).prod (fun n ↦
--       ((fun n : ℕ ↦ if hn : n ∈ S then (μ ⟨n, hn⟩) (s ⟨n, hn⟩) else 1) n)) := by
--     apply Finset.prod_congr rfl (by simp)
--   have h2 : (@Finset.univ (S.erase a) _).prod (fun n ↦ (μ ⟨n.1, Finset.mem_of_mem_erase n.2⟩)
--       (s ⟨n.1, Finset.mem_of_mem_erase n.2⟩)) =
--       (@Finset.univ (S.erase a).toSet _).prod (fun n ↦
--       ((fun n : ℕ ↦ if hn : n ∈ S then (μ ⟨n, hn⟩) (s ⟨n, hn⟩) else 1) n)) := by
--     apply Finset.prod_congr rfl (fun x _ ↦ by simp [(Finset.mem_erase.1 x.2).2])
--   rw [h1, h2,
--     Finset.prod_set_coe (f := (fun n : ℕ ↦ if hn : n ∈ S then (μ ⟨n, hn⟩) (s ⟨n, hn⟩) else 1)),
--     Finset.prod_set_coe (f := (fun n : ℕ ↦ if hn : n ∈ S then (μ ⟨n, hn⟩) (s ⟨n, hn⟩) else 1)),
--     Finset.toFinset_coe, Finset.toFinset_coe, ← Finset.prod_erase_mul S _ ha]
--   congr
--   simp [ha]


  -- have := tendsto_of_antitone anti
  -- rcases this with hlim | ⟨l, hlim⟩
  -- · rw [OrderBot.atBot_eq] at hlim
  --   exact hlim.mono_right <| pure_le_nhds 0
  -- convert hlim
  -- by_contra zero_ne_l
  -- have := fun n ↦ anti.le_of_tendsto hlim n
  -- have : ∀ n, (kolContent μ_proj) (A n) =
  --     ∫⁻ x₀ : X 0, kolContent (μ_proj'' 1) (slice x₀ (A n)) ∂(μ 0) := by
  --   intro n
  --   have : ∀ x₀ : X 0, ∀ S : Set ((n : Finset.range (NA n + 1)) → X n),
  --       slice x₀ (cylinder (Finset.range (NA n + 1)) S) =
  --       cylinder (Finset.range (NA n)) (slice_range (NA n) x₀ S) := by
  --     intro x₀ S
  --     ext x
  --     simp [slice, slice_range, produit, produit_range]
  --     congrm ?_ ∈ S
  --     ext i
  --     cases i with
  --       | mk j hj => cases j with
  --         | zero => simp [produit_range]
  --         | succ => simp [produit_range]
  --   have : ∀ x₀, kolContent (μ_proj'' 1) (slice x₀ (A n)) =
  --       Measure.pi (fun n : Finset.range (NA n) ↦ μ (n + 1)) (slice_range (NA n) x₀ (SA n)) := by
  --     intro x₀
  --     rw [A_eq n, this x₀ (SA n), kolContent_eq,
  --       kolmogorovFun_congr (μ_proj'' 1) (cylinder_mem_cylinders (Finset.range (NA n))
  --       (slice_range (NA n) x₀ (SA n)) _)]
  --     rfl
  --     apply measurable_slice_range (mSA n)
  --     apply measurable_slice_range (mSA n)

      -- constructor
      -- · rintro ⟨y, hy, rfl, rfl⟩
      --   use fun i : Finset.range (NA n + 1) ↦ y i
      -- · rintro ⟨y, hy, hy', hy''⟩
      --   refine ⟨produit x₀ x, ?_, ?_, ?_⟩
      --   · have : (fun i : Finset.range (NA n + 1) ↦ produit x₀ x i) = y := by
      --       ext i
      --       cases i with
      --       | mk j hj =>
      --         cases j with
      --         | zero => simp [produit, hy']
      --         | succ m =>
      --           have : produit x₀ x (m + 1) = x m := by
      --             simp [produit]
      --           rw [this]
      --           have : x m = (fun i : Finset.range (NA n) ↦ x i) ⟨m, ok.2 hj⟩ := by simp
      --           rw [this, ← hy'']
      --     exact this ▸ hy
      --   · simp [produit]
      --   · ext n
      --     simp [produit]

    -- let extension : (∀ n : (Finset.range (NA n + 1)).erase 0, X n) → (∀ n : {k | k ≥ 1}, X n) :=
    --   fun x k ↦ by
    --     by_cases h : k.1 < NA n + 1
    --     · use x ⟨k.1, Finset.mem_erase.2 ⟨Nat.one_le_iff_ne_zero.1 k.2, Finset.mem_range.2 h⟩⟩
    --     · use Classical.ofNonempty
    -- let e : (Finset.range (NA n + 1)).erase 0 ≃
    --     {k : {k | k ≥ 1} | k.1 ∈ (Finset.range (NA n + 1)).erase 0} :=
    --   {
    --     toFun := fun x ↦ ⟨⟨x.1, Nat.one_le_iff_ne_zero.2 (Finset.mem_erase.1 x.2).1⟩, x.2⟩
    --     invFun := fun x ↦ ⟨x.1.1, x.2⟩
    --     left_inv := by simp [Function.LeftInverse]
    --     right_inv := by simp [Function.RightInverse, Function.LeftInverse]
    --   }
    -- have : Fintype {k : {k | k ≥ 1} | k.1 ∈ (Finset.range (NA n + 1)).erase 0} := by
    --   exact Fintype.ofEquiv ((Finset.range (NA n + 1)).erase 0) e
    -- let aux : X 0 → (∀ n : {k : {k | k ≥ 1} | k.1 ∈ (Finset.range (NA n + 1)).erase 0}.toFinset, X n) →
    --     (∀ n : Finset.range (NA n + 1), X n) :=
    --   fun x₀ x ↦
    --     (fun y : ∀ n, X n ↦ fun k : Finset.range (NA n + 1) ↦ y k.1) ((produit x₀) (extension
    --     (fun k : (Finset.range (NA n + 1)).erase 0 ↦
    --     x ⟨⟨k.1, Nat.one_le_iff_ne_zero.2 (Finset.mem_erase.1 k.2).1⟩, k.2⟩)))
    --   -- if h : k = ⟨0, zero_mem_range⟩ then h ▸ x₀ else by
    --   -- rw [← ne_eq, ← Subtype.val_inj.ne] at h
    --   -- have : k.1 - 1 ∈ Finset.range (NA n) := by
    --   --   rw [Finset.mem_range, Nat.sub_lt_iff_lt_add, add_comm 1]
    --   --   exact Finset.mem_range.1 k.2
    --   --   exact Nat.one_le_iff_ne_zero.2 h
    --   -- use Nat.succ_pred_eq_of_ne_zero h ▸ x ⟨k.1 - 1, this⟩
    -- have : ∀ x₀ : X 0, ∀ S : Set ((n : Finset.range (NA n + 1)) → X n),
    --     (produit x₀) ⁻¹' (cylinder (Finset.range (NA n + 1)) S) =
    --     cylinder (α := fun k : {k | k ≥ 1} ↦ X k)
    --     {k : {k | k ≥ 1} | k.1 ∈ (Finset.range (NA n + 1)).erase 0}.toFinset ((aux x₀) ⁻¹' S) := by
    --   intro x₀ S
    --   ext x
    --   simp [produit, aux]
    --   congrm ?_ ∈ S
    --   ext k
    --   by_cases h : k = ⟨0, zero_mem_range⟩
    --   · have : k.1 = 0 := by rw [h]
    --     simp [h, this]
    --     have : k = ⟨0, zero_mem_range⟩ ↔ k.1 = 0 := by
    --       refine ⟨fun h ↦ by rw [h], fun h' ↦ ?_⟩
    --       ext
    --       exact h'

    -- have : ∀ x₀, kolContent (μ_proj' 1) ((produit x₀) ⁻¹' (A n)) =
    --     Measure.pi (fun n : (Finset.range (NA n + 1)).erase 0 ↦ μ n) ((aux x₀) ⁻¹' (SA n)) := by
    --   intro x₀
    --   simp
    --   rw [kolContent_eq (μ_proj' 1)]
    -- rw [kolContent_eq μ_proj (A_mem n), kolmogorovFun_congr μ_proj (A_mem n) (A_eq n) (mSA n)]
    -- simp [kolContent_eq (μ_proj' 1), kolmogorovFun_congr μ_proj (A_mem n) (A_eq n) (mSA n)]
