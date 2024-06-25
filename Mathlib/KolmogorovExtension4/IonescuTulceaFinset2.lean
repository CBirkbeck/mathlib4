import Mathlib.KolmogorovExtension4.compo_perso_Finset2
import Mathlib.KolmogorovExtension4.Boxes
import Mathlib.KolmogorovExtension4.Projective
import Mathlib.Probability.Kernel.MeasureCompProd
import Mathlib.KolmogorovExtension4.DependsOn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.KolmogorovExtension4.KolmogorovExtension
import Mathlib.Data.PNat.Interval
import Mathlib.KolmogorovExtension4.Annexe

open MeasureTheory ProbabilityTheory Finset ENNReal Filter Topology Function

variable {X : ℕ → Type*} [Nonempty (X 0)] [∀ n, MeasurableSpace (X n)]
variable (κ : (k : ℕ) → kernel ((i : Iic k) → X i) (X (k + 1)))
variable [∀ k, IsMarkovKernel (κ k)]

lemma mem_Iic_zero {i : ℕ} (hi : i ∈ Iic 0) : i = 0 := by simpa using hi

def zer : X 0 → (i : Iic 0) → X i := fun x₀ i ↦ (mem_Iic_zero i.2).symm ▸ x₀

theorem measurable_zer : Measurable (zer (X := X)) := by
  refine measurable_pi_lambda _ (fun i ↦ ?_)
  simp_rw [zer, eqRec_eq_cast]
  apply measurable_cast
  have : ⟨0, mem_Iic.2 <| le_refl 0⟩ = i := by simp [(mem_Iic_zero i.2).symm]
  cases this; rfl

noncomputable def family' (μ : (n : ℕ+) → Measure ((i : Ioc 0 n.1) → X i)) :
    (S : Finset ℕ+) → Measure ((k : S) → X k) :=
  fun S ↦ (μ (S.sup id)).map
    (fun x (i : S) ↦ x ⟨i.1, mem_Ioc.2 ⟨i.1.2, le_sup (f := id) i.2⟩⟩)

theorem proj_family' (μ : (n : ℕ+) → Measure ((i : Ioc 0 n.1) → X i))
    (h : ∀ a b : ℕ+, ∀ hab : a ≤ b, (μ b).map
      (fun x (i : Ioc 0 a.1) ↦ x ⟨i.1, Ioc_subset_Ioc_right ((PNat.coe_le_coe a b).2 hab) i.2⟩)
      = μ a) :
    IsProjectiveMeasureFamily (α := fun n : ℕ+ ↦ X n) (family' μ) := by
  intro I J hJI
  have sls : J.sup id ≤ I.sup id := sup_mono hJI
  have sls' : (J.sup id).1 ≤ (I.sup id).1 := (PNat.coe_le_coe _ _).2 sls
  simp only [family']
  rw [Measure.map_map]
  · conv_rhs =>
      enter [1]
      change (fun x i ↦ x ⟨i.1.1, mem_Ioc.2 ⟨i.1.2, le_sup (f := id) i.2⟩⟩ :
        ((i : Ioc 0 (J.sup id).1) → X i) → (i : J) → X i) ∘
        (fun x i ↦ x ⟨i.1, Ioc_subset_Ioc_right sls' i.2⟩ :
        ((i : Ioc 0 (I.sup id).1) → X i) → (i : Ioc 0 (J.sup id).1) → X i)
    rw [← Measure.map_map, h (J.sup id) (I.sup id) sls]
    rfl
    exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
    exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

theorem proj_family'' (x₀ : X 0) : ∀ a b : ℕ+, ∀ (hab : a ≤ b), (kerNat κ 0 b.1 (zer x₀)).map
      (fun x (i : Ioc 0 a.1) ↦ x ⟨i.1, Ioc_subset_Ioc_right ((PNat.coe_le_coe a b).2 hab) i.2⟩)
      = kerNat κ 0 a.1 (zer x₀) := by
  intro a b hab
  rw [← proj_kerNat _ _ hab, kernel.map_apply]
  exact a.pos

noncomputable def kC (x₀ : X 0) : AddContent (cylinders (fun n : ℕ+ ↦ X n)) :=
  kolContent (proj_family' _ (proj_family'' κ x₀))

def PIoc (a b : ℕ) : Finset ℕ+ := Ico (⟨a + 1, a.succ_pos⟩ : ℕ+) (⟨b + 1, b.succ_pos⟩ : ℕ+)

theorem mem_PIoc {a b : ℕ} {i : ℕ+} : i ∈ PIoc a b ↔ a < i.1 ∧ i.1 ≤ b := by
  simp [PIoc]
  rw [← PNat.coe_le_coe, ← PNat.coe_lt_coe, PNat.mk_coe, PNat.mk_coe, Nat.succ_le, Nat.lt_succ]
  rfl

theorem mem_PIoc_zero {b : ℕ} {i : ℕ+} : i ∈ PIoc 0 b ↔ i.1 ≤ b := by
  rw [mem_PIoc]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨i.pos, h⟩⟩

theorem mem_PIoc_succ {a : ℕ} {i : ℕ+} : i ∈ PIoc a (a + 1) ↔ i.1 = a + 1 := by
  rw [mem_PIoc]
  omega

theorem PIoc_diff_PIoc {a b c : ℕ} (hcb : c ≤ b) : PIoc a b \ PIoc c b = PIoc a c := by
  ext x
  rw [mem_sdiff, mem_PIoc, mem_PIoc, mem_PIoc]
  omega

def Ioc_PIoc_pi {a b : ℕ} : ((i : Ioc a b) → X i) ≃ᵐ ((i : PIoc a b) → X i) where
  toFun := fun z i ↦ z ⟨i.1.1, mem_Ioc.2 <| mem_PIoc.1 i.2⟩
  invFun := fun z i ↦ z ⟨⟨i.1, Nat.zero_lt_of_lt (mem_Ioc.1 i.2).1⟩, mem_PIoc.2 <| mem_Ioc.1 i.2⟩
  left_inv := fun z ↦ by rfl
  right_inv := fun z ↦ by rfl
  measurable_toFun := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  measurable_invFun := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

theorem Ioc_zero_pi_eq {a b : ℕ} (h : a = b) :
    ((i : Ioc 0 a) → X i) = ((i : Ioc 0 b) → X i) := by cases h; rfl

theorem sup_PIoc {N : ℕ} (hN : 0 < N) : ((PIoc 0 N).sup id).1 = N := by
  conv_rhs => change ((↑) : ℕ+ → ℕ) (⟨N, hN⟩ : ℕ+)
  conv_lhs => change ((↑) : ℕ+ → ℕ) ((PIoc 0 N).sup id)
  apply le_antisymm <;> rw [PNat.coe_le_coe]
  · refine Finset.sup_le fun i hi ↦ (PNat.coe_le_coe _ _).1 <| mem_PIoc_zero.1 hi
  · rw [← id_eq (⟨N, hN⟩ : ℕ+)]
    apply le_sup
    rw [mem_PIoc_zero]

theorem measure_cast {a b : ℕ} (h : a = b) (μ : (n : ℕ) → Measure ((i : Ioc 0 n) → X i)) :
    (μ a).map (cast (Ioc_zero_pi_eq h)) = μ b := by
  subst h
  exact Measure.map_id

lemma omg {s t : Set ℕ} {u : Set ℕ+} (h : s = t) (h' : ((i : s) → X i) = ((i : t) → X i))
    (x : (i : s) → X i) (i : u) (hi1 : i.1.1 ∈ s) (hi2 : i.1.1 ∈ t) :
    cast h' x ⟨i.1.1, hi2⟩ = x ⟨i.1.1, hi1⟩ := by
  subst h
  rfl

theorem HEq_measurableSpace_Ioc_zero_pi {a b : ℕ} (h : a = b) :
    HEq (inferInstance : MeasurableSpace ((i : Ioc 0 a) → X i))
    (inferInstance : MeasurableSpace ((i : Ioc 0 b) → X i)) := by cases h; rfl

theorem kC_cylinder (x₀ : X 0) {n : ℕ} (hn : 0 < n) {S : Set ((i : PIoc 0 n) → X i)}
    (mS : MeasurableSet S) :
    kC κ x₀ (cylinder (PIoc 0 n) S) = kerNat κ 0 n (zer x₀) (Ioc_PIoc_pi ⁻¹' S) := by
  rw [kC, kolContent_congr _ (by rw [mem_cylinders]; exact ⟨PIoc 0 n, S, mS, rfl⟩) rfl mS, family',
    Measure.map_apply _ mS, ← measure_cast (sup_PIoc hn) (fun n ↦ kerNat κ 0 n (zer x₀)),
    Measure.map_apply]
  · congrm kerNat _ _ _ _ (?_ ⁻¹' S)
    ext x i
    simp only [Ioc_PIoc_pi, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
    rw [omg _ (Ioc_zero_pi_eq (sup_PIoc hn)) x i]
    · rfl
    · rw [sup_PIoc hn]
  · apply measurable_cast
    exact HEq_measurableSpace_Ioc_zero_pi (sup_PIoc hn)
  · exact Ioc_PIoc_pi.measurable mS
  · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

def fusion {k : ℕ} (x₀ : X 0) (y : (i : PIoc 0 k) → X i) (i : Iic k) : X i :=
  if hi : i.1 = 0
    then hi ▸ x₀
    else y ⟨⟨i.1, i.1.pos_of_ne_zero hi⟩, mem_PIoc_zero.2 <| mem_Iic.1 i.2⟩

theorem measurable_fusion (k : ℕ) (x₀ : X 0) : Measurable (fusion (k := k) x₀) := by
  simp only [fusion, measurable_pi_iff]
  intro i
  by_cases h : i.1 = 0 <;> simp [h, measurable_pi_apply]

noncomputable def kerint (k N : ℕ) (f : ((n : ℕ+) → X n) → ℝ≥0∞) (x₀ : X 0)
    (x : (i : ℕ+) → X i) : ℝ≥0∞ :=
  if k < N then ∫⁻ z : (i : Ioc k N) → X i,
    f (updateFinset x _ (Ioc_PIoc_pi z)) ∂(kerNat κ k N (fusion x₀ (fun i ↦ x i.1)))
    else f x

theorem lintegral_cast_eq {α β : Type _} [hα : MeasurableSpace α] [hβ : MeasurableSpace β]
    (h : α = β) (h' : HEq hα hβ) {f : α → ℝ≥0∞} (hf : Measurable f) (μ : Measure α) :
    ∫⁻ b : β, f (cast h.symm b) ∂μ.map (cast h) = ∫⁻ a : α, f a ∂μ := by
  rw [lintegral_map]
  · exact lintegral_congr (by simp)
  · exact hf.comp <| measurable_cast _ h'.symm
  · exact measurable_cast _ h'

theorem kolContent_eq_kerint {N : ℕ} (hN : 0 < N) {S : Set ((i : PIoc 0 N) → X i)}
    (mS : MeasurableSet S)
    (x₀ : X 0) (x : (n : ℕ+) → X n) :
    kC κ x₀ (cylinder (PIoc 0 N) S) =
    kerint κ 0 N ((cylinder _ S).indicator 1) x₀ x := by
  rw [kC_cylinder _ _ hN mS, ← lintegral_indicator_one, kerint]
  · simp only [cast_eq, hN, ↓reduceIte]
    congr
    · ext i
      simp [zer, mem_Iic_zero i.2, fusion]
    · ext z
      refine Eq.trans (preimage_indicator _ _ _ _) (indicator_const_eq _ ?_)
      congrm (fun i ↦ ?_) ∈ S
      rw [updateFinset, dif_pos i.2]
  · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _) mS

theorem kerint_mono (k N : ℕ) {f g : ((n : ℕ+) → X n) → ℝ≥0∞} (hfg : f ≤ g) (x₀ : X 0)
    (x : (n : ℕ+) → X n) : kerint κ k N f x₀ x ≤ kerint κ k N g x₀ x := by
  unfold kerint
  split_ifs
  · exact lintegral_mono fun _ ↦ hfg _
  · exact hfg _

theorem measurable_kerint (k N : ℕ) {f : ((n : ℕ+) → X n) → ℝ≥0∞} (hf : Measurable f) (x₀ : X 0) :
    Measurable (kerint κ k N f x₀) := by
  unfold kerint
  split_ifs with h
  · let g : ((i : Ioc k N) → X i) × ((n : ℕ+) → X n) → ℝ≥0∞ :=
      fun c ↦ f (updateFinset c.2 _ (Ioc_PIoc_pi c.1))
    let η : kernel ((n : ℕ+) → X n) ((i : Ioc k N) → X i) :=
      { val := fun x ↦ kerNat κ k N (fusion x₀ (fun i ↦ x i.1))
        property := (kernel.measurable _).comp <| (measurable_fusion _ _).comp <|
          measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _) }
    change Measurable fun x ↦ ∫⁻ z : (i : Ioc k N) → X i, g (z, x) ∂η x
    have := isMarkovKernel_kerNat κ h
    have : IsMarkovKernel η := IsMarkovKernel.mk fun x ↦ this.isProbabilityMeasure _
    refine Measurable.lintegral_kernel_prod_left' <| hf.comp ?_
    simp only [updateFinset, measurable_pi_iff]
    intro i
    by_cases h : i ∈ PIoc k N <;> simp [h]
    · exact (measurable_pi_apply _).comp <| Ioc_PIoc_pi.measurable.comp measurable_fst
    · exact measurable_snd.eval
  · exact hf

theorem dependsOn_kerint' {a b : ℕ} (c : ℕ) {f : ((n : ℕ+) → X n) → ℝ≥0∞}
    (hf : DependsOn f (PIoc 0 a)) (hab : a ≤ b) (x₀ : X 0) : kerint κ b c f x₀ = f := by
  ext x
  rw [kerint]
  split_ifs with hkK
  · have := isMarkovKernel_kerNat κ hkK
    rw [← mul_one (f x), ← measure_univ (μ := (kerNat κ b c) (fusion x₀ (fun i ↦ x i.1))),
      ← lintegral_const]
    refine lintegral_congr fun y ↦ hf fun i hi ↦ ?_
    simp only [updateFinset, dite_eq_right_iff]
    intro h
    rw [mem_PIoc] at h
    rw [mem_coe, mem_PIoc] at hi
    omega
  · rfl

theorem dependsOn_kerint (k : ℕ) {N : ℕ} {f : ((n : ℕ+) → X n) → ℝ≥0∞} (hf : DependsOn f (PIoc 0 N))
    (x₀ : X 0) : DependsOn (kerint κ k N f x₀) (PIoc 0 k) := by
  intro x y hxy
  simp_rw [kerint]
  split_ifs with h
  · congrm ∫⁻ z : _, ?_ ∂(kerNat κ k N (fusion x₀ fun i ↦ ?_))
    · exact hxy i.1 i.2
    · refine dependsOn_updateFinset hf _ _ ?_
      rwa [← coe_sdiff, PIoc_diff_PIoc h.le]
  · refine hf fun i hi ↦ hxy i ?_
    rw [mem_coe, mem_PIoc] at hi ⊢
    omega

theorem kerint_self {k N : ℕ} (hkN : N ≤ k) (f : ((n : ℕ+) → X n) → ℝ≥0∞) (x₀ : X 0) :
    kerint κ k N f x₀ = f := by
  ext x
  rw [kerint, if_neg <| not_lt.2 hkN]

theorem updateFinset_self {ι : Type*} [DecidableEq ι] {α : ι → Type*} (x : (i : ι) → α i)
    {s : Finset ι} (y : (i : s) → α i) : (fun i : s ↦ updateFinset x s y i) = y := by
  ext i
  simp [updateFinset, i.2]

theorem kerint_eq {a b c : ℕ} (hab : a < b) (hbc : b < c) {f : ((n : ℕ+) → X n) → ℝ≥0∞}
    (hf : Measurable f) (x₀ : X 0) :
    kerint κ a c f x₀ = kerint κ a b (kerint κ b c f x₀) x₀ := by
  ext x
  simp [kerint, hab.trans hbc, hab, hbc]
  rw [← compProd_kerNat _ hab hbc, compProd_eq _ _  hab hbc, kernel.map_apply,
    lintegral_map _ (er ..).measurable, kernel.lintegral_compProd]
  · congrm ∫⁻ _ : ?_, ∫⁻ _ : ?_, f fun i ↦ ?_ ∂(?_) ∂(?_)
    · rfl
    · rfl
    · rw [split_eq_comap, kernel.comap_apply]
      congr with i
      simp only [el, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, fusion, updateFinset, PNat.mk_coe]
      split_ifs with h1 h2 h3 h4 h5
      · rfl
      · rw [mem_PIoc] at h3
        simp only at h3
        omega
      · rfl
      · omega
      · rfl
      · rw [mem_PIoc] at h5
        simp only at h5
        have := mem_Iic.1 i.2
        omega
    · rfl
    · simp only [updateFinset, Ioc_PIoc_pi, er, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
      split_ifs <;> rw [mem_PIoc] at * <;> omega
  · exact hf.comp <| measurable_updateFinset.comp <| (Ioc_PIoc_pi ..).measurable.comp
      (er ..).measurable
  · exact hf.comp <| measurable_updateFinset.comp <| (Ioc_PIoc_pi ..).measurable


theorem obv : PNat.val = Subtype.val := by rfl

theorem update_eq_updateFinset' (x : (n : ℕ+) → X n) (k : ℕ)
    (y : X (k + 1)) :
    update x k.succPNat (y) =
    updateFinset x (PIoc k (k + 1)) (Ioc_PIoc_pi (e k y)) := by
  ext i
  simp only [update, updateFinset, Ioc_PIoc_pi, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
  split_ifs with h1 h2 h3
  · cases h1; rfl
  · rw [mem_PIoc_succ] at h2
    rw [← PNat.coe_inj] at h1
    exact (h2 h1).elim
  · rw [mem_PIoc_succ] at h3
    rw [← PNat.coe_inj] at h1
    exact (h1 h3).elim
  · rfl

theorem update_updateFinset_eq (x z : (n : ℕ+) → X n) {m : ℕ} :
    update (updateFinset x (PIoc 0 m) (fun i ↦ z i)) ⟨m + 1, m.succ_pos⟩ (z ⟨m + 1, _⟩) =
    updateFinset x (PIoc 0 (m + 1)) (fun i ↦ z i) := by
  ext i
  simp only [update, updateFinset, dite_eq_ite]
  split_ifs with h1 h2 h3 h4 h5 <;> rw [mem_PIoc] at *
  · cases h1; rfl
  · have : i.1 = m + 1 := by simp [h1]
    omega
  · omega
  · rw [← PNat.coe_inj] at h1
    change ¬i.1 = m + 1 at h1
    omega

theorem auxiliaire {f : ℕ → ((n : ℕ+) → X n) → ℝ≥0∞} {N : ℕ → ℕ}
    (hcte : ∀ n, DependsOn (f n) (PIoc 0 (N n))) (mf : ∀ n, Measurable (f n))
    {bound : ℝ≥0∞} (fin_bound : bound ≠ ∞) (le_bound : ∀ n x, f n x ≤ bound) {k : ℕ}
    {x₀ : X 0}
    (anti : ∀ x, Antitone (fun n ↦ kerint κ (k + 1) (N n) (f n) x₀ x))
    {l : ((n : ℕ+) → X n) → ℝ≥0∞}
    (htendsto : ∀ x, Tendsto (fun n ↦ kerint κ (k + 1) (N n) (f n) x₀ x) atTop (𝓝 (l x)))
    (ε : ℝ≥0∞) (y : (n : PIoc 0 k) → X n)
    (hpos : ∀ x n, ε ≤ kerint κ k (N n) (f n) x₀ (updateFinset x _ y)) :
    ∃ z, ∀ x n,
    ε ≤ kerint κ (k + 1) (N n) (f n) x₀ (Function.update (updateFinset x _ y) k.succPNat z) := by
  have _ n : Nonempty (X n) := by
    refine Nat.case_strong_induction_on (p := fun n ↦ Nonempty (X n)) _ inferInstance
      fun n hind ↦ ?_
    have : Nonempty ((i : Iic n) → X i) :=
      Nonempty.intro fun i ↦ @Classical.ofNonempty _ (hind i.1 (mem_Iic.1 i.2))
    exact ProbabilityMeasure.nonempty
      ⟨κ n Classical.ofNonempty, inferInstance⟩
  -- Shorter name for integrating over all the variables except the first `k + 1`.
  let F : ℕ → ((n : ℕ+) → X n) → ℝ≥0∞ := fun n ↦ kerint κ (k + 1) (N n) (f n) x₀
  -- `Fₙ` converges to `l` by hypothesis.
  have tendstoF x : Tendsto (F · x) atTop (𝓝 (l x)) := htendsto x
  -- Integrating `fₙ` over all the variables except the first `k` is the same as integrating
  -- `Fₙ` over the `k`-th variable.
  have f_eq x n : kerint κ k (N n) (f n) x₀ x = kerint κ k (k + 1) (F n) x₀ x := by
    simp only [F]
    rcases lt_trichotomy (k + 1) (N n) with h | h | h
    · rw [kerint_eq κ k.lt_succ_self h (mf n)]
    · rw [← h, kerint_self _ (le_refl (k + 1))]
    · have : N n ≤ k := Nat.lt_succ.1 h
      rw [kerint_self _ this, dependsOn_kerint' _ _ (hcte n) (this.trans k.le_succ),
        dependsOn_kerint' _ _ (hcte n) this]
  -- `F` is also a bounded sequence.
  have F_le n x : F n x ≤ bound := by
    simp only [F, kerint]
    split_ifs with h
    · have := isMarkovKernel_kerNat κ h
      rw [← mul_one bound,
        ← measure_univ (μ := (kerNat κ (k + 1) (N n)) (fusion x₀ (fun i ↦ x i.1))),
        ← lintegral_const]
      exact lintegral_mono fun _ ↦ le_bound _ _
    · exact le_bound _ _
  -- By dominated convergence, the integral of `fₙ` with respect to all the variable except
  -- the `k` first converges to the integral of `l`.
  have tendsto_int x : Tendsto (fun n ↦ kerint κ k (N n) (f n) x₀ x) atTop
      (𝓝 (kerint κ k (k + 1) l x₀ x)) := by
    simp_rw [f_eq, kerint, if_pos k.lt_succ_self]
    refine tendsto_lintegral_of_dominated_convergence (fun _ ↦ bound)
      (fun n ↦ (measurable_kerint _ _ _ (mf n) _).comp <|
        measurable_updateFinset.comp <| (Ioc_PIoc_pi ..).measurable)
      (fun n ↦ eventually_of_forall <| fun y ↦ F_le n _)
      ?_ (eventually_of_forall (fun _ ↦ tendstoF _))
    have := isMarkovKernel_kerNat κ k.lt_succ_self
    simp [fin_bound]
  -- By hypothesis, we have `ε ≤ ∫ F(y, xₖ) ∂μₖ`, so this is also true for `l`.
  have ε_le_lint x : ε ≤ kerint κ k (k + 1) l x₀ (updateFinset x _ y) :=
    ge_of_tendsto (tendsto_int _) (by simp [hpos])
  let x_ : (n : ℕ+) → X n := Classical.ofNonempty
  -- We now have that the integral of `l` with respect to a probability measure is greater than `ε`,
  -- therefore there exists `x'` such that `ε ≤ l(y, x')`.
  obtain ⟨x', hx'⟩ : ∃ x', ε ≤ l (Function.update (updateFinset x_ _ y) k.succPNat x') := by
    have aux : ∫⁻ (a : X (k + 1)),
        l (update (updateFinset x_ _ y) k.succPNat a) ∂(κ k (fusion x₀ y)) ≠ ∞ := by
      apply ne_top_of_le_ne_top fin_bound
      rw [← mul_one bound, ← measure_univ (μ := κ k (fusion x₀ y)), ← lintegral_const]
      exact lintegral_mono <| fun y ↦ le_of_tendsto' (tendstoF _) <| fun _ ↦ F_le _ _
    rcases exists_lintegral_le aux with ⟨x', hx'⟩
    refine ⟨x', ?_⟩
    calc
      ε ≤ ∫⁻ (z : X (k + 1)),
          l (update (updateFinset x_ _ y) k.succPNat z) ∂(κ k (fusion x₀ y)) := by
          convert ε_le_lint x_
          rw [kerint, if_pos k.lt_succ_self, kerNat_succ, kernel.map_apply,
            lintegral_map_equiv]
          congrm ∫⁻ z, ?_ ∂κ k (fusion x₀ (fun i ↦ ?_))
          · simp [i.2, updateFinset]
          · rw [update_eq_updateFinset']
      _ ≤ l (update (updateFinset x_ _ y) k.succPNat x') := hx'
  refine ⟨x', fun x n ↦ ?_⟩
  -- As `F` is a non-increasing sequence, we have `ε ≤ Fₙ(y, x')` for any `n`.
  have := le_trans hx' ((anti _).le_of_tendsto (tendstoF _) n)
  -- This part below is just to say that this is true for any `x : (i : ι) → X i`,
  -- as `Fₙ` technically depends on all the variables, but really depends only on the first `k + 1`.
  convert this using 1
  refine dependsOn_kerint _ _ (hcte n) _ fun i hi ↦ ?_
  simp only [update, updateFinset]
  split_ifs with h1 h2
  · rfl
  · rfl
  · rw [mem_coe, mem_PIoc, ← PNat.coe_inj, k.succPNat_coe] at *
    change ¬i.1 = k.succ at h1
    omega

theorem cylinders_pnat :
    cylinders (fun n : ℕ+ ↦ X n) = ⋃ (N) (_ : 0 < N) (S) (_ : MeasurableSet S),
    {cylinder (PIoc 0 N) S} := by
  ext s
  simp only [mem_cylinders, exists_prop, Set.mem_iUnion, mem_singleton]
  constructor
  · rintro ⟨t, S, mS, rfl⟩
    refine ⟨(t.sup id).1, (t.sup id).pos, (fun (f : (n : PIoc 0 (t.sup id).1) → X n) (k : t) ↦
      f ⟨k.1, ?_⟩) ⁻¹' S, ?_, ?_⟩
    · rw [mem_PIoc_zero, Subtype.coe_le_coe]
      exact le_sup (α := ℕ+) (f := id) k.2
    · exact mS.preimage <| measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
    · dsimp only [cylinder]
      rw [← Set.preimage_comp]
      rfl
  · rintro ⟨N, -, S, mS, rfl⟩
    exact ⟨PIoc 0 N, S, mS, rfl⟩

def key (ind : (k : ℕ) → ((n : PIoc 0 k) → X n) → X k.succPNat) : (k : ℕ+) → X k := fun k ↦ by
  use cast (congrArg (fun k : ℕ+ ↦ X k) k.succPNat_natPred) (ind k.natPred (fun i ↦ key ind i.1))
  termination_by k => k
  decreasing_by
  have := i.2
  simp [PIoc] at this
  exact this

theorem dependsOn_cylinder_indicator {ι : Type*} {α : ι → Type*} {I : Finset ι}
    (S : Set ((i : I) → α i)) :
    DependsOn ((cylinder I S).indicator (1 : ((i : ι) → α i) → ℝ≥0∞)) I := by
  intro x y hxy
  have : x ∈ cylinder I S ↔ y ∈ cylinder I S := by simp [hxy]
  by_cases h : x ∈ cylinder I S
  · simp [h, this.1 h]
  · simp [h, this.not.1 h]

/-- This is the key theorem to prove the existence of the product measure: the `kolContent` of
a decresaing sequence of cylinders with empty intersection converges to $0$, in the case where
the measurable spaces are indexed by $\mathbb{N}$. This implies the $\sigma$-additivity of
`kolContent` (see `sigma_additive_addContent_of_tendsto_zero`),
which allows to extend it to the $\sigma$-algebra by Carathéodory's theorem. -/
theorem firstLemma (A : ℕ → Set ((n : ℕ+) → X n)) (A_mem : ∀ n, A n ∈ cylinders _)
    (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) (x₀ : X 0) :
    Tendsto (fun n ↦ kC κ x₀ (A n)) atTop (𝓝 0) := by
  have _ n : Nonempty (X n) := by
    refine Nat.case_strong_induction_on (p := fun n ↦ Nonempty (X n)) _ inferInstance
      fun n hind ↦ ?_
    have : Nonempty ((i : Iic n) → X i) :=
      Nonempty.intro fun i ↦ @Classical.ofNonempty _ (hind i.1 (mem_Iic.1 i.2))
    exact ProbabilityMeasure.nonempty
      ⟨κ n Classical.ofNonempty, inferInstance⟩
  -- `Aₙ` is a cylinder, it can be written `cylinder sₙ Sₙ`.
  have A_cyl n : ∃ N S, 0 < N ∧ MeasurableSet S ∧ A n = cylinder (PIoc 0 N) S := by
    simpa [cylinders_pnat] using A_mem n
  choose N S hN mS A_eq using A_cyl
  -- We write `χₙ` for the indicator function of `Aₙ`.
  let χ n := (A n).indicator (1 : ((n : ℕ+) → X n) → ℝ≥0∞)
  -- `χₙ` is measurable.
  have mχ n : Measurable (χ n) := by
    simp_rw [χ, A_eq]
    exact (measurable_indicator_const_iff 1).2 <| measurableSet_cylinder _ _ (mS n)
  -- `χₙ` only depends on the first coordinates.
  have χ_dep n : DependsOn (χ n) (PIoc 0 (N n)) := by
    simp_rw [χ, A_eq]
    exact dependsOn_cylinder_indicator _
  -- Therefore its integral is constant.
  have lma_const x y n : kerint κ 0 (N n) (χ n) x₀ x = kerint κ 0 (N n) (χ n) x₀ y := by
    apply dependsOn_empty
    convert dependsOn_kerint κ 0 (χ_dep n) x₀
    simp [PIoc]
  -- As `(Aₙ)` is non-increasing, so is `(χₙ)`.
  have χ_anti : Antitone χ := by
    intro m n hmn y
    apply Set.indicator_le
    exact fun a ha ↦ by simp [χ, A_anti hmn ha]
  -- Integrating `χₙ` further than the last coordinate it depends on does nothing.
  -- This is used to then show that the integral of `χₙ` over all the variables except the first
  -- `k` ones is non-increasing.
  have lma_inv k M n (h : N n ≤ M) :
      kerint κ k M (χ n) x₀ = kerint κ k (N n) (χ n) x₀ := by
    refine Nat.le_induction rfl ?_ M h
    intro K hK hind
    rw [← hind]
    rcases lt_trichotomy k K with hkK | hkK | hkK
    · rw [kerint_eq κ hkK K.lt_succ_self (mχ n), dependsOn_kerint' _ _ (χ_dep n) hK]
    · rw [hkK, dependsOn_kerint' _ _ (χ_dep n) hK, dependsOn_kerint' _ _ (χ_dep n) hK]
    · rw [kerint_self _ hkK.le, kerint_self _ (Nat.succ_le.2 hkK)]
  -- the integral of `χₙ` over all the variables except the first `k` ones is non-increasing.
  have anti_lma k x : Antitone fun n ↦ kerint κ k (N n) (χ n) x₀ x := by
    intro m n hmn
    simp only
    rw [← lma_inv k ((N n).max (N m)) n (le_max_left _ _),
      ← lma_inv k ((N n).max (N m)) m (le_max_right _ _)]
    exact kerint_mono _ _ _ (χ_anti hmn) _ _
  -- Therefore it converges to some function `lₖ`.
  have this k x : ∃ l, Tendsto (fun n ↦ kerint κ k (N n) (χ n) x₀ x) atTop (𝓝 l) := by
    rcases tendsto_of_antitone <| anti_lma k x with h | h
    · rw [OrderBot.atBot_eq] at h
      exact ⟨0, h.mono_right <| pure_le_nhds 0⟩
    · exact h
  choose l hl using this
  -- `l₀` is constant because it is the limit of constant functions: we call it `ε`.
  have l_const x y : l 0 x = l 0 y := by
    have := hl 0 x
    simp_rw [lma_const x y] at this
    exact tendsto_nhds_unique this (hl 0 _)
  obtain ⟨ε, hε⟩ : ∃ ε, ∀ x, l 0 x = ε := ⟨l 0 Classical.ofNonempty, fun x ↦ l_const ..⟩
  -- As the sequence is decreasing, `ε ≤ ∫ χₙ`.
  have hpos x n : ε ≤ kerint κ 0 (N n) (χ n) x₀ x :=
    hε x ▸ ((anti_lma 0 _).le_of_tendsto (hl 0 _)) n
  -- Also, the indicators are bounded by `1`.
  have χ_le n x : χ n x ≤ 1 := by
    apply Set.indicator_le
    simp
  -- We have all the conditions to apply àuxiliaire. This allows us to recursively
  -- build a sequence `(zₙ)` with the following crucial property: for any `k` and `n`,
  -- `ε ≤ ∫ χₙ(z₀, ..., z_{k-1}) ∂(μₖ ⊗ ... ⊗ μ_{Nₙ})`.
  choose! ind hind using
    fun k y h ↦ auxiliaire κ χ_dep mχ (by norm_num : (1 : ℝ≥0∞) ≠ ∞) χ_le (anti_lma (k + 1))
      (hl (k + 1)) ε y h
  let z := key ind
  have crucial : ∀ k x n,
      ε ≤ kerint κ k (N n) (χ n) x₀ (updateFinset x (PIoc 0 k) (fun i ↦ z i)) := by
    intro k
    induction k with
    | zero =>
      intro x n
      rw [PIoc, Ico_self, updateFinset_empty]
      exact hpos x n
    | succ m hm =>
      intro x n
      rw [← update_updateFinset_eq]
      convert hind m (fun i ↦ z i.1) hm x n
  -- We now want to prove that the integral of `χₙ` converges to `0`.
  have concl x n : kC κ x₀ (A n) = kerint κ 0 (N n) (χ n) x₀ x := by
    simp_rw [χ, A_eq]
    exact kolContent_eq_kerint _ (hN n) (mS n) x₀ x
  simp_rw [concl Classical.ofNonempty]
  convert hl 0 Classical.ofNonempty
  rw [hε]
  by_contra!
  -- Which means that we want to prove that `ε = 0`. But if `ε > 0`, then for any `n`,
  -- choosing `k > Nₙ` we get `ε ≤ χₙ(z₀, ..., z_{Nₙ})` and therefore `(z n) ∈ Aₙ`.
  -- This contradicts the fact that `(Aₙ)` has an empty intersection.
  have ε_pos : 0 < ε := this.symm.bot_lt
  have incr : ∀ n, z ∈ A n := by
    intro n
    have : χ n z = kerint κ (N n) (N n) (χ n) x₀
        (updateFinset z (PIoc 0 (N n)) (fun i ↦ z i)) := by
      rw [kerint, if_neg <| lt_irrefl (N n)]
      congr with i
      simp [updateFinset, PIoc]
    have : 0 < χ n (z) := by
      rw [this]
      exact lt_of_lt_of_le ε_pos (crucial (N n) z n)
    exact Set.mem_of_indicator_ne_zero (ne_of_lt this).symm
  exact (A_inter ▸ Set.mem_iInter.2 incr).elim

theorem kolContent_sigma_subadditive_proj (x₀ : X 0) ⦃f : ℕ → Set ((n : ℕ+) → X n)⦄
    (hf : ∀ n, f n ∈ cylinders (fun n : ℕ+ ↦ X n))
    (hf_Union : (⋃ n, f n) ∈ cylinders (fun n : ℕ+ ↦ X n)) :
    kC κ x₀ (⋃ n, f n) ≤
    ∑' n, kC κ x₀ (f n) := by
  have _ n : Nonempty (X n) := by
    refine Nat.case_strong_induction_on (p := fun n ↦ Nonempty (X n)) _ inferInstance
      fun n hind ↦ ?_
    have : Nonempty ((i : Iic n) → X i) :=
      Nonempty.intro fun i ↦ @Classical.ofNonempty _ (hind i.1 (mem_Iic.1 i.2))
    exact ProbabilityMeasure.nonempty
      ⟨κ n Classical.ofNonempty, inferInstance⟩
  refine (kC κ x₀).sigma_subadditive_of_sigma_additive
    setRing_cylinders (fun f hf hf_Union hf' ↦ ?_) f hf hf_Union
  refine sigma_additive_addContent_of_tendsto_zero setRing_cylinders
    (kC κ x₀) (fun h ↦ ?_) ?_ hf hf_Union hf'
  · rename_i s
    obtain ⟨N, S, hN, mS, s_eq⟩ : ∃ N S, 0 < N ∧ MeasurableSet S ∧ s = cylinder (PIoc 0 N) S := by
      simpa [cylinders_pnat] using h
    let x_ : (n : ℕ+) → X n := Classical.ofNonempty
    rw [s_eq, kolContent_eq_kerint κ hN mS x₀ x_]
    refine ne_of_lt (lt_of_le_of_lt ?_ (by norm_num : (1 : ℝ≥0∞) < ∞))
    rw [kerint, if_pos hN]
    have : IsMarkovKernel (kerNat κ 0 N) := isMarkovKernel_kerNat κ hN
    nth_rw 2 [← mul_one 1, ← measure_univ (μ := kerNat κ 0 N (fusion x₀ fun i ↦ x_ i.1))]
    rw [← lintegral_const]
    exact lintegral_mono <| Set.indicator_le (by simp)
  · exact fun s hs anti_s inter_s ↦ firstLemma κ s hs anti_s inter_s x₀

noncomputable def ionescu_tulcea_fun (x₀ : X 0) : Measure ((n : ℕ+) → X n) := by
  exact Measure.ofAddContent setSemiringCylinders generateFrom_cylinders
    (kC κ x₀)
    (kolContent_sigma_subadditive_proj κ x₀)

theorem proba_ionescu (x₀ : X 0) : IsProbabilityMeasure (ionescu_tulcea_fun κ x₀) := by
  constructor
  rw [← cylinder_univ ∅, ionescu_tulcea_fun, Measure.ofAddContent_eq, kC,
      kolContent_congr _ _ rfl MeasurableSet.univ]
  · simp only [family']
    rw [← kernel.map_apply _ (measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _))]
    have : IsMarkovKernel (kerNat κ 0 1) := isMarkovKernel_kerNat κ zero_lt_one
    simp
  · simp only [mem_cylinders, exists_prop, forall_const]
    exact ⟨∅, Set.univ, MeasurableSet.univ, rfl⟩
  · simp only [mem_cylinders, exists_prop, forall_const]
    exact ⟨∅, Set.univ, MeasurableSet.univ, rfl⟩


/-- The product measure is the projective limit of the partial product measures. This ensures
uniqueness and expresses the value of the product measures applied to cylinders. -/
theorem isProjectiveLimit_ionescu_tulcea_fun (x₀ : X 0) :
    IsProjectiveLimit (ionescu_tulcea_fun κ x₀) (family' (fun n ↦ kerNat κ 0 n.1 (zer x₀))) := by
  intro I
  ext1 s hs
  rw [Measure.map_apply (measurable_proj' _) hs]
  have h_mem : (fun (x : (n : ℕ+) → X n) (i : I) ↦ x i) ⁻¹' s ∈
      cylinders (fun n : ℕ+ ↦ X n) := by
    rw [mem_cylinders]; exact ⟨I, s, hs, rfl⟩
  rw [ionescu_tulcea_fun, Measure.ofAddContent_eq _ _ _ _ h_mem, kC,
    kolContent_congr _ h_mem rfl hs]

theorem measurable_ionescu : Measurable (ionescu_tulcea_fun κ) := by
  apply Measure.measurable_of_measurable_coe
  refine MeasurableSpace.induction_on_inter
    (C := fun t ↦ Measurable (fun x₀ ↦ ionescu_tulcea_fun κ x₀ t))
    (s := cylinders (fun n : ℕ+ ↦ X n)) generateFrom_cylinders.symm isPiSystem_cylinders
    (by simp) (fun t ht ↦ ?cylinder) (fun t mt ht ↦ ?compl) (fun f disf mf hf ↦ ?union)
  · obtain ⟨N, S, -, mS, t_eq⟩ : ∃ N S, 0 < N ∧ MeasurableSet S ∧ t = cylinder (PIoc 0 N) S := by
      simpa [cylinders_pnat] using ht
    simp_rw [ionescu_tulcea_fun, Measure.ofAddContent_eq _ _ _ _ ht, kC,
      kolContent_congr _ ht t_eq mS]
    simp only [family']
    refine Measure.measurable_measure.1 ?_ _ mS
    refine (Measure.measurable_map _ ?_).comp <| (kernel.measurable _).comp measurable_zer
    exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  · have this x₀ : ionescu_tulcea_fun κ x₀ tᶜ = 1 - ionescu_tulcea_fun κ x₀ t := by
      have := proba_ionescu κ
      rw [measure_compl mt (measure_ne_top _ _), measure_univ]
    simp_rw [this]
    exact Measurable.const_sub ht _
  · simp_rw [measure_iUnion disf mf]
    exact Measurable.ennreal_tsum hf

noncomputable def ionescu_tulcea_kernel : kernel (X 0) ((n : ℕ+) → X n) :=
  { val := ionescu_tulcea_fun κ
    property := measurable_ionescu κ }

theorem ionescu_tulcea_kernel_apply (x₀ : X 0) :
    ionescu_tulcea_kernel κ x₀ = ionescu_tulcea_fun κ x₀ := by
  rw [ionescu_tulcea_kernel]
  rfl

instance : IsMarkovKernel (ionescu_tulcea_kernel κ) := IsMarkovKernel.mk fun _ ↦ proba_ionescu _ _

def er' (N : ℕ) : (X 0) × ((i : Ioc 0 N) → X i) → (i : Iic N) → X i :=
  (el 0 N (zero_le N)) ∘ (Prod.map zer id)

theorem measurable_er' (N : ℕ) : Measurable (er' (X := X) N) :=
  (el ..).measurable.comp <| measurable_zer.prod_map measurable_id

def er'' : (X 0) × ((n : ℕ+) → X n) → (n : ℕ) → X n :=
  fun p n ↦ if h : n = 0 then h ▸ p.1 else p.2 ⟨n, Nat.zero_lt_of_ne_zero h⟩

theorem measurable_er'' : Measurable (er'' (X := X)) := by
  refine measurable_pi_lambda _ (fun n ↦ ?_)
  by_cases h : n = 0
  · simp only [er'', Equiv.coe_fn_mk, h, dite_true]
    simp_rw [eqRec_eq_cast]
    exact (measurable_cast _ (by cases h; rfl)).comp measurable_fst
  · simp only [er'', Equiv.coe_fn_mk, h, dite_false]
    exact measurable_snd.eval

theorem proj_zero_eq_zer_proj_zero :
    (fun (x : (n : ℕ) → X n) (i : Iic 0) ↦ x i) = zer ∘ (fun x ↦ x 0) := by
  ext x i
  simp only [zer, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply]
  have : i.1 = 0 := mem_Iic_zero i.2
  aesop

theorem proj_zero_er''_eq : (fun x ↦ x 0) ∘ (er'' (X := X)) = Prod.fst := by
  ext x
  simp [er'']

theorem proj_er''_eq_er'_prod (N : ℕ) :
    (fun (x : (n : ℕ) → X n) (i : Iic N) ↦ x i) ∘ er'' =
    (er' N) ∘ (Prod.map id (Ioc_PIoc_pi.symm ∘ (fun x (i : PIoc 0 N) ↦ x i))) := by
  ext x i
  simp [er'', er', el, zer, Ioc_PIoc_pi]

variable (κ : (n : ℕ) → kernel ((i : Iic n) → X i) (X (n + 1)))
variable [∀ n, IsMarkovKernel (κ n)]

noncomputable def ionescu_ker : kernel (X 0) ((n : ℕ) → X n) :=
  kernel.map
    ((kernel.deterministic id measurable_id) ×ₖ (ionescu_tulcea_kernel κ))
    er'' measurable_er''

instance : IsMarkovKernel (ionescu_ker κ) := kernel.IsMarkovKernel.map _ _

noncomputable def kerNat' (n : ℕ) : kernel (X 0) ((i : Ioc 0 n) → X i) :=
    kernel.comap (kerNat κ 0 n) zer measurable_zer

instance (n : ℕ) : IsFiniteKernel (kerNat' κ n) := by
  rw [kerNat']
  infer_instance

theorem isMarkovKernel_kerNat' {n : ℕ} (hn : 0 < n) : IsMarkovKernel (kerNat' κ n) := by
  have := isMarkovKernel_kerNat κ hn
  rw [kerNat']
  infer_instance

theorem proj_kerNat' (κ : (k : ℕ) → kernel ((x : Iic k) → X x) (X (k + 1)))
    [∀ i, IsMarkovKernel (κ i)]
    {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    kernel.map (kerNat' κ b)
      (fun (x : ((i : Ioc 0 b) → X i)) (i : Ioc 0 a) ↦ x ⟨i.1, Ioc_subset_Ioc_right hab i.2⟩)
      (measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)) = kerNat' κ a := by
  unfold kerNat'
  rw [← kernel.comap_map_comm]
  congr
  exact proj_kerNat _ ha hab

noncomputable def my_ker (N : ℕ) :
    kernel (X 0) ((i : Iic N) → X i) :=
  if h : N = 0
    then
      by cases h; exact kernel.map (kernel.deterministic id measurable_id) zer measurable_zer
    else kernel.map ((kernel.deterministic id measurable_id) ×ₖ
      (kerNat' κ N))
      (er' N) (measurable_er' N)

theorem ionescu_ker_proj_zero :
    kernel.map (ionescu_ker κ) (fun x ↦ x 0) (measurable_pi_apply _) =
    kernel.deterministic id measurable_id := by
  rw [ionescu_ker, kernel.map_map]
  conv_lhs => enter [2]; rw [proj_zero_er''_eq]
  exact kernel.fst_prod _ _

theorem my_ker_zero : my_ker κ 0 =
    kernel.map (kernel.deterministic id measurable_id) zer measurable_zer := rfl

theorem my_ker_pos {N : ℕ} (hN : 0 < N) :
    my_ker κ N = kernel.map ((kernel.deterministic id measurable_id) ×ₖ
      (kerNat' κ N)) (er' N) (measurable_er' N) := by
  rw [my_ker, dif_neg hN.ne.symm]

instance {N : ℕ} : IsMarkovKernel (my_ker κ N) := by
  rcases N.eq_zero_or_pos with hN | hN
  · cases hN
    rw [my_ker_zero]
    infer_instance
  · rw [my_ker_pos _ hN]
    have := isMarkovKernel_kerNat' κ hN
    infer_instance

theorem proj_my_ker {a b : ℕ} (hab : a ≤ b) :
    kernel.map (my_ker κ b)
      (fun x (i : Iic a) ↦ x ⟨i.1, Iic_subset_Iic.2 hab i.2⟩) (measurable_proj₂' ..) =
    my_ker κ a := by
  rcases eq_zero_or_pos a with ha | ha
  · cases ha
    rcases eq_zero_or_pos b with hb | hb
    · cases hb
      rw [my_ker_zero, kernel.map_map]
      congr
    · rw [my_ker_pos _ hb, my_ker_zero, kernel.map_map]
      have : (fun x (i : Iic 0) ↦ x ⟨i.1, Iic_subset_Iic.2 hab i.2⟩) ∘ (er' (X := X) b) =
          (Prod.fst ∘ (Prod.map zer id)) := by
        ext x i
        simp [er', el, zer, mem_Iic_zero i.2]
      rw [kernel.map_eq _ _ this, ← kernel.map_map, kernel.map_prod]
      · have := isMarkovKernel_kerNat' κ hb
        exact kernel.fst_prod _ _
      · exact measurable_id
  · rw [my_ker_pos _ ha, my_ker_pos _ (lt_of_lt_of_le ha hab), kernel.map_map]
    have : (fun x (i : Iic a) ↦ x ⟨i.1, Iic_subset_Iic.2 hab i.2⟩) ∘ (er' b) =
        (er' (X := X) a) ∘
        (Prod.map id (fun x (i : Ioc 0 a) ↦ x ⟨i.1, Ioc_subset_Ioc_right hab i.2⟩)) := by
      ext x i
      simp [er', el, zer]
    rw [kernel.map_eq _ _ this, ← kernel.map_map, kernel.map_prod, kernel.map_id]
    · congr
      exact proj_kerNat' _ ha hab
    repeat exact measurable_er' a

theorem proj_my_ker_Ioc {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    kernel.map (my_ker κ b)
      (fun x (i : Ioc 0 a) ↦ x ⟨i.1, mem_Iic.2 <| (mem_Ioc.1 i.2).2.trans hab⟩)
      (measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)) = kerNat' κ a := by
  have : (fun x (i : Ioc 0 a) ↦ x ⟨i.1, mem_Iic.2 <| (mem_Ioc.1 i.2).2.trans hab⟩) =
      Prod.snd ∘ (el 0 a (zero_le a)).symm ∘
      (fun (x : (i : Iic b) → X i) (i : Iic a) ↦ x ⟨i.1, Iic_subset_Iic.2 hab i.2⟩) := by
    ext x i
    simp [el]
  rw [kernel.map_eq _ _ this, ← kernel.map_map, ← kernel.map_map, proj_my_ker _ hab,
    my_ker_pos _ ha, kernel.map_map, kernel.map_map]
  have : Prod.snd ∘ (el 0 a (zero_le a)).symm ∘ (er' (X := X) a) = Prod.snd := by
    ext x i
    simp [er', el, (mem_Ioc.1 i.2).1.ne.symm]
  nth_rw 2 [← kernel.snd_prod (kernel.deterministic id measurable_id) (kerNat' κ a)]
  rw [kernel.snd]
  · congr
  · exact measurable_snd
  · exact (el ..).measurable_invFun

lemma omg' {s t : Set ℕ} (h : s = t) (h' : ((i : s) → X i) = ((i : t) → X i))
    (x : (i : t) → X i) (i : s) (hi : i.1 ∈ t) :
    x ⟨i.1, hi⟩ = cast h'.symm x i := by
  subst h
  rfl

theorem ionescu_ker_proj (N : ℕ) :
    kernel.map (ionescu_ker κ) (fun x (i : Iic N) ↦ x i) (measurable_proj _) = my_ker κ N := by
  rcases eq_zero_or_pos N with hN | hN
  · cases hN
    rw [my_ker_zero, kernel.map_eq _ _ proj_zero_eq_zer_proj_zero,
      ← kernel.map_map _ (measurable_pi_apply _) measurable_zer, ionescu_ker_proj_zero]
  · rw [ionescu_ker, kernel.map_map, my_ker_pos _ hN, kernel.map_eq _ _ (proj_er''_eq_er'_prod N),
      ← kernel.map_map _ _ (measurable_er' N), kernel.map_prod, kernel.map_id]
    congr
    ext1 x₀
    rw [kernel.map_apply, ionescu_tulcea_kernel_apply, ← Measure.map_map,
      isProjectiveLimit_ionescu_tulcea_fun, family', kerNat', kernel.comap_apply,
      ← measure_cast (sup_PIoc hN) (fun n ↦ kerNat _ 0 n (zer x₀)), Measure.map_map]
    · congr with x i
      simp only [Ioc_PIoc_pi, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
        Equiv.coe_fn_symm_mk, comp_apply, PNat.mk_coe]
      apply omg' _ _ x <;> rw [sup_PIoc hN]
    · exact Ioc_PIoc_pi.measurable_invFun
    · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
    · exact Ioc_PIoc_pi.measurable_invFun
    · exact measurable_proj _
    · exact Ioc_PIoc_pi.measurable_invFun.comp (measurable_proj _)

theorem integral_dep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (x₀ : X 0) {f : ((i : Iic N) → X i) → E} (hf : AEStronglyMeasurable f (my_ker κ N x₀)) :
    ∫ y, f ((fun x (i : Iic N) ↦ x i) y) ∂ionescu_ker κ x₀ =
    ∫ y, f y ∂my_ker κ N x₀ := by
  rw [← ionescu_ker_proj, kernel.map_apply, integral_map]
  · exact (measurable_proj _).aemeasurable
  · rwa [← kernel.map_apply, ionescu_ker_proj]
