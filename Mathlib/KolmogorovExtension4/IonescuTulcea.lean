import Mathlib.KolmogorovExtension4.compo_perso
import Mathlib.KolmogorovExtension4.Boxes
import Mathlib.KolmogorovExtension4.Projective
import Mathlib.Probability.Kernel.MeasureCompProd
import Mathlib.KolmogorovExtension4.DependsOn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.KolmogorovExtension4.KolmogorovExtension
import Mathlib.Data.PNat.Interval

open MeasureTheory ProbabilityTheory Set ENNReal Filter Topology

variable {X : ℕ → Type*} [Nonempty (X 0)] [∀ n, MeasurableSpace (X n)]
variable (κ : (k : ℕ) → kernel ((i : Iic k) → X i) ((i : Ioc k (k + 1)) → X i))
variable [∀ k, IsMarkovKernel (κ k)]

lemma mem_Iic_zero {i : ℕ} (hi : i ∈ Iic 0) : i = 0 := by simpa using hi

lemma mem_Ioc_succ {n i : ℕ} : i ∈ Ioc n (n + 1) ↔ i = n + 1 := by
  rw [mem_Ioc]
  omega

lemma lol {a b : ℕ+} : a = b + 1 ↔ a.1 = b.1 + 1 := by
  rw [← Subtype.coe_inj]
  congrm a.1 = ?_
  exact PNat.add_coe _ _

lemma Pmem_Ioc_succ {n i : ℕ+} : i ∈ Ioc n (n + 1) ↔ i = n + 1 := by
  rw [mem_Ioc, ← PNat.coe_lt_coe, ← PNat.coe_le_coe, PNat.add_coe, lol, PNat.one_coe,
    ← mem_Ioc, mem_Ioc_succ]
  rfl

def zer : (X 0) ≃ᵐ ((i : Iic 0) → X i) where
  toFun := fun x₀ i ↦ (mem_Iic_zero i.2).symm ▸ x₀
  invFun := fun x ↦ x ⟨0, mem_Iic.2 <| le_refl 0⟩
  left_inv := fun x₀ ↦ by simp
  right_inv := fun x ↦ by
    ext i
    have : ⟨0, mem_Iic.2 <| le_refl 0⟩ = i := by simp [(mem_Iic_zero i.2).symm]
    cases this; rfl
  measurable_toFun := by
    refine measurable_pi_lambda _ (fun i ↦ ?_)
    simp_rw [eqRec_eq_cast]
    apply measurable_cast
    have : ⟨0, mem_Iic.2 <| le_refl 0⟩ = i := by simp [(mem_Iic_zero i.2).symm]
    cases this; rfl
  measurable_invFun := measurable_pi_apply _

noncomputable def family (x₀ : X 0) : (S : Finset ℕ+) → Measure ((k : S) → X k) :=
  fun S ↦ (kerNat κ 0 (S.sup id).1 (zer x₀)).map
    (fun x (i : S) ↦ x ⟨i.1, ⟨i.1.2, Finset.le_sup (f := id) i.2⟩⟩)

theorem isMarkovKernel_compProd {i j k : ℕ}
    (κ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x))
    (η : kernel ((x : Iic j) → X x) ((x : Ioc j k) → X x))
    [IsMarkovKernel κ] [IsMarkovKernel η] (hij : i < j) (hjk : j < k) :
    IsMarkovKernel (κ ⊗ₖ' η) := by
  rw [compProd]
  simp only [hij, hjk, and_self, ↓reduceDite, split]
  infer_instance

theorem isMarkovKernel_castPath {i j k : ℕ}
    (κ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x)) [IsMarkovKernel κ] (hjk : j = k)  :
    IsMarkovKernel (castPath κ hjk) := by
  rw [castPath]; infer_instance

theorem isMarkovKernel_kerInterval {i j k : ℕ}
    (κ₀ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x)) [h₀ : IsMarkovKernel κ₀]
    (κ : ∀ k, kernel ((x : Iic k) → X x) ((x : Ioc k (k + 1)) → X x)) [∀ k, IsMarkovKernel (κ k)]
    (hij : i < j) (hjk : j ≤ k) :
    IsMarkovKernel (kerInterval κ₀ κ k) := by
  induction k with
  | zero => linarith
  | succ n hn =>
    rw [kerInterval_succ]
    split_ifs with h
    · exact isMarkovKernel_castPath _ _
    · have _ := hn (by omega)
      exact isMarkovKernel_compProd _ _ (by omega) n.lt_succ_self

theorem isMarkovKernel_kerNat {i j : ℕ}
    (κ : ∀ k, kernel ((x : Iic k) → X x) ((x : Ioc k (k + 1)) → X x))
    [∀ k, IsMarkovKernel (κ k)] (hij : i < j) :
    IsMarkovKernel (kerNat κ i j) := by
  simp only [kerNat, hij, ↓reduceIte]
  exact isMarkovKernel_kerInterval _ _ i.lt_succ_self (Nat.succ_le.2 hij)

theorem proj_kerNat {k l : ℕ} (hk : 0 < k) (hkl : k ≤ l) :
    kernel.map (kerNat κ 0 l)
      (fun (x : ((i : Ioc 0 l) → X i)) (i : Ioc 0 k) ↦ x ⟨i.1, Ioc_subset_Ioc_right hkl i.2⟩)
      (measurable_proj₂ ..) = kerNat κ 0 k := by
  by_cases h : k = l
  · cases h
    exact kernel.map_id _
  · have hkl : k < l := by omega
    ext x s ms
    rw [kernel.map_apply' _ _ _ ms, ← compProd_kerNat κ hk hkl,
      compProd_apply' _ _ hk hkl _ (measurable_proj₂ _ _ _ ms)]
    simp_rw [preimage_preimage]
    refine Eq.trans (b := ∫⁻ b, s.indicator 1 b ∂kerNat κ 0 k x) ?_ ?_
    · refine lintegral_congr fun b ↦ ?_
      simp only [el, nonpos_iff_eq_zero, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, er, mem_preimage,
        indicator, Pi.one_apply]
      split_ifs with hb
      · have := isMarkovKernel_kerNat κ hkl
        convert measure_univ
        · ext c
          simp only [mem_setOf_eq, mem_univ, iff_true]
          convert hb using 1
          ext i
          simp [(mem_Ioc.2 i.2).2]
        · infer_instance
      · convert measure_empty
        · ext c
          simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
          convert hb using 2
          ext i
          simp [(mem_Ioc.2 i.2).2]
        · infer_instance
    · rw [← one_mul (((kerNat κ 0 k) x) s)]
      exact lintegral_indicator_const ms _

theorem kernel.map_map {X Y Z T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace T]
    (κ : kernel X Y) {f : Y → Z} (hf : Measurable f) {g : Z → T} (hg : Measurable g) :
    kernel.map (kernel.map κ f hf) g hg = kernel.map κ (g ∘ f) (hg.comp hf) := by
  ext1 x
  rw [kernel.map_apply, kernel.map_apply, Measure.map_map hg hf, ← kernel.map_apply]

theorem proj_family (x₀ : X 0) :
    IsProjectiveMeasureFamily (α := fun k : ℕ+ ↦ X k) (family κ x₀) := by
  intro S T hTS
  have : T.sup id ≤ S.sup id := Finset.sup_mono hTS
  simp only [family]
  rw [← kernel.map_apply, ← proj_kerNat _ _ this, Measure.map_map, kernel.map_map, kernel.map_apply]
  · rfl
  · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  · exact PNat.pos _

noncomputable def updateSet {ι : Type*} {α : ι → Type*} (x : (i : ι) → α i) (s : Set ι)
    (y : (i : s) → α i) (i : ι) : α i := by
  classical
  exact if hi : i ∈ s then y ⟨i, hi⟩ else x i


theorem updateSet_empty {ι : Type*} {α : ι → Type*} (x : (i : ι) → α i) {s : Set ι} (hs : s = ∅)
    (y : (i : s) → α i) : updateSet x s y = x := by
  ext i
  simp [updateSet, hs]

theorem dependsOn_updateSet {ι β : Type*} {α : ι → Type*} {f : ((i : ι) → α i) → β} {s : Set ι}
    (hf : DependsOn f s) (t : Set ι) (y : (i : t) → α i) :
    DependsOn (fun x ↦ f (updateSet x t y)) (s \ t) := by
  refine fun x₁ x₂ h ↦ hf (fun i hi ↦ ?_)
  simp only [updateSet]
  split_ifs with h'
  · rfl
  · exact h i <| (mem_diff _).2 ⟨hi, h'⟩

theorem measurable_updateSet {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (x : (i : ι) → α i) (s : Set ι) :
    Measurable (updateSet x s) := by
  simp only [updateSet, measurable_pi_iff]
  intro i
  by_cases h : i ∈ s <;> simp [h, measurable_pi_apply]

def PIoc (a b : ℕ) := Ico (⟨a + 1, a.succ_pos⟩ : ℕ+) (⟨b + 1, b.succ_pos⟩ : ℕ+)

theorem mem_PIoc {a b : ℕ} {i : ℕ+} : i ∈ PIoc a b ↔ a < i.1 ∧ i.1 ≤ b := by
  simp [PIoc]
  rw [← PNat.coe_le_coe, ← PNat.coe_lt_coe, PNat.mk_coe, PNat.mk_coe, Nat.succ_le, Nat.lt_succ]
  rfl

theorem PIoc_diff_PIoc {a b c : ℕ} (hcb : c ≤ b) : PIoc a b \ PIoc c b = PIoc a c := by
  ext x
  rw [mem_diff, mem_PIoc, mem_PIoc, mem_PIoc]
  omega

theorem mem_PIoc_zero {b : ℕ} {i : ℕ+} : i ∈ PIoc 0 b ↔ i.1 ≤ b := by
  rw [mem_PIoc]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨i.pos, h⟩⟩

def fPIoc (a b : ℕ) : Finset ℕ+ :=
  Finset.Ico (⟨a + 1, a.succ_pos⟩ : ℕ+) (⟨b + 1, b.succ_pos⟩ : ℕ+)

theorem mem_fPIoc {a b : ℕ} {i : ℕ+} : i ∈ fPIoc a b ↔ a < i.1 ∧ i.1 ≤ b := by
  rw [fPIoc, ← Finset.mem_coe, Finset.coe_Ico]
  exact mem_PIoc

theorem mem_fPIoc_zero {b : ℕ} {i : ℕ+} : i ∈ fPIoc 0 b ↔ i.1 ≤ b := by
  rw [fPIoc, ← Finset.mem_coe, Finset.coe_Ico]
  exact mem_PIoc_zero

def Ioc_PIoc_pi {a b : ℕ} (z : (i : Ioc a b) → X i) (i : PIoc a b) : X i :=
  z ⟨i.1, mem_Ioc.2 <| mem_PIoc.1 i.2⟩

theorem measurable_Ioc_PIoc_pi (a b : ℕ) : Measurable (@Ioc_PIoc_pi X a b) :=
  measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

def Ioc_fPIoc_pi {a b : ℕ} : ((i : Ioc a b) → X i) ≃ᵐ ((i : fPIoc a b) → X i) where
  toFun := fun z i ↦ z ⟨i.1.1, mem_Ioc.2 <| mem_fPIoc.1 i.2⟩
  invFun := fun z i ↦ z ⟨⟨i.1, Nat.zero_lt_of_lt (mem_Ioc.1 i.2).1⟩, mem_fPIoc.2 <| mem_Ioc.1 i.2⟩
  left_inv := fun z ↦ by rfl
  right_inv := fun z ↦ by rfl
  measurable_toFun := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  measurable_invFun := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

theorem update_eq_updateSet {α : ℕ → Type*} (x : (n : ℕ+) → α n) (k : ℕ) (y : α (k + 1)) :
    Function.update x k.succPNat y =
    updateSet x (PIoc k (k + 1))
      (fun l ↦ cast (congrArg α (mem_Ioc_succ.1 (mem_Ioc.2 <| mem_PIoc.1 l.2)).symm) y) := by
  congr with i
  by_cases h : i = k.succPNat
  · cases h
    simp [updateSet]
    rw [if_pos]
    refine mem_PIoc.2 <| mem_Ioc.1 <| mem_Ioc_succ.2 ?_
    rw [Nat.add_one, ← Nat.succPNat_coe]
    rfl
  · simp [h, updateSet]
    rw [dif_neg]
    refine mem_PIoc.not.2 <| mem_Ioc.not.1 <| mem_Ioc_succ.not.2 ?_
    rwa [← Subtype.val_inj] at h

def fusion {k : ℕ} (x₀ : X 0) (y : (i : PIoc 0 k) → X i) (i : Iic k) : X i :=
  if hi : i.1 = 0
    then hi ▸ x₀
    else y ⟨⟨i.1, i.1.pos_of_ne_zero hi⟩, mem_PIoc_zero.2 <| mem_Iic.1 i.2⟩

theorem measurable_fusion (k : ℕ) (x₀ : X 0) : Measurable (fusion (k := k) x₀) := by
  simp only [fusion, measurable_pi_iff]
  intro i
  by_cases h : i.1 = 0 <;> simp [h, measurable_pi_apply]

noncomputable def kerint (k N : ℕ) (f : ((n : ℕ+) → X n) → ℝ≥0∞) (x₀ : X 0)
    (x : (i : ℕ+) → X i) : ℝ≥0∞ := by
  classical
  exact if k < N then ∫⁻ z : (i : Ioc k N) → X i,
    f (updateSet x _ (Ioc_PIoc_pi z)) ∂(kerNat κ k N (fusion x₀ (fun i ↦ x i.1)))
    else f x

theorem sup_fPIoc {N : ℕ} (hN : 0 < N) : ((fPIoc 0 N).sup id).1 = N := by
  conv_rhs => change ((↑) : ℕ+ → ℕ) (⟨N, hN⟩ : ℕ+)
  conv_lhs => change ((↑) : ℕ+ → ℕ) ((fPIoc 0 N).sup id)
  apply le_antisymm <;> rw [PNat.coe_le_coe]
  · refine Finset.sup_le fun i hi ↦ (PNat.coe_le_coe _ _).1 <| mem_fPIoc_zero.1 hi
  · rw [← id_eq (⟨N, hN⟩ : ℕ+)]
    apply Finset.le_sup
    rw [mem_fPIoc_zero]

theorem lintegral_cast_eq {α β : Type _} [hα : MeasurableSpace α] [hβ : MeasurableSpace β]
    (h : α = β) (h' : HEq hα hβ) {f : α → ℝ≥0∞} (hf : Measurable f) (μ : Measure α) :
    ∫⁻ b : β, f (cast h.symm b) ∂μ.map (cast h) = ∫⁻ a : α, f a ∂μ := by
  rw [lintegral_map]
  · exact lintegral_congr (by simp)
  · exact hf.comp <| measurable_cast _ h'.symm
  · exact measurable_cast _ h'

theorem Ioc_zero_pi_eq {a b : ℕ} (h : a = b) :
    ((i : Ioc 0 a) → X i) = ((i : Ioc 0 b) → X i) := by cases h; rfl

theorem HEq_measurableSpace_Ioc_zero_pi {a b : ℕ} (h : a = b) :
    HEq (inferInstance : MeasurableSpace ((i : Ioc 0 a) → X i))
    (inferInstance : MeasurableSpace ((i : Ioc 0 b) → X i)) := by cases h; rfl

theorem measure_cast {a b : ℕ} (h : a = b) (μ : (n : ℕ) → Measure ((i : Ioc 0 n) → X i)) :
    (μ a).map (cast (Ioc_zero_pi_eq h)) = μ b := by
  subst h
  exact Measure.map_id

theorem preimage_indicator {α β M : Type*} [Zero M] (f : α → β) (s : Set β) (a : α) (c : M) :
    (f ⁻¹' s).indicator (fun _ ↦ c) a = s.indicator (fun _ ↦ c) (f a) := by
  simp only [indicator, mem_preimage, Pi.one_apply]
  by_cases h : f a ∈ s <;> simp [h]

lemma omg {s t : Set ℕ} {u : Set ℕ+} (h : s = t) (h' : ((i : s) → X i) = ((i : t) → X i))
    (x : (i : s) → X i) (i : u) (hi1 : i.1.1 ∈ s) (hi2 : i.1.1 ∈ t) :
    cast h' x ⟨i.1.1, hi2⟩ = x ⟨i.1.1, hi1⟩ := by
  subst h
  rfl

theorem indicator_eq_indicator {α β M : Type*} [Zero M] {s : Set α} {t : Set β} {a : α} {b : β}
    (c : M) (h : a ∈ s ↔ b ∈ t) :
    s.indicator (fun _ ↦ c) a = t.indicator (fun _ ↦ c) b := by
  by_cases h' : a ∈ s
  · simp [indicator, h', h.1 h']
  · simp [indicator, h', h.not.1 h']

theorem kolContent_eq_kerint {N : ℕ} (hN : 0 < N) {S : Set ((i : fPIoc 0 N) → X i)}
    (mS : MeasurableSet S)
    (x₀ : X 0) (x : (n : ℕ+) → X n) :
    kolContent (α := fun n : ℕ+ ↦ X n) (proj_family κ x₀) (cylinder (fPIoc 0 N) S) =
    kerint κ 0 N ((cylinder _ S).indicator 1) x₀ x := by
  rw [kolContent_congr _ (by rw [mem_cylinders]; exact ⟨fPIoc 0 N, S, mS, rfl⟩) rfl mS, family,
    Measure.map_apply _ mS, ← lintegral_indicator_one₀, kerint]
  · simp only [cast_eq, hN, ↓reduceIte]
    rw [← lintegral_cast_eq (Ioc_zero_pi_eq <| sup_fPIoc hN)
      (HEq_measurableSpace_Ioc_zero_pi <| sup_fPIoc hN)]
    · congr
      · rw [measure_cast (sup_fPIoc hN) (fun n ↦ kerNat κ 0 n (zer x₀))]
        congr with i
        simp [zer, fusion, mem_Iic_zero i.2]
      · ext z
        refine Eq.trans (preimage_indicator _ _ _ _) (indicator_eq_indicator _ ?_)
        congrm (fun i ↦ ?_) ∈ S
        simp only [updateSet, mem_Ico, zero_add, PNat.mk_ofNat, PNat.one_le, true_and, Ioc_PIoc_pi,
          Nat.reduceAdd]
        rw [dif_pos <| mem_PIoc.2 <| mem_fPIoc.1 i.2,
          ← omg _ (Ioc_zero_pi_eq (sup_fPIoc hN)).symm z i]
        · rfl
        · rw [sup_fPIoc hN]
    · exact (measurable_indicator_const_iff 1).2 <|
        measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _) mS
  · apply MeasurableSet.nullMeasurableSet
    exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _) mS
  · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

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
      fun c ↦ f (updateSet c.2 _ (Ioc_PIoc_pi c.1))
    let η : kernel ((n : ℕ+) → X n) ((i : Ioc k N) → X i) :=
      { val := fun x ↦ kerNat κ k N (fusion x₀ (fun i ↦ x i.1))
        property := (kernel.measurable _).comp <| (measurable_fusion _ _).comp <|
          measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _) }
    change Measurable fun x ↦ ∫⁻ z : (i : Ioc k N) → X i, g (z, x) ∂η x
    have := isMarkovKernel_kerNat κ h
    have : IsMarkovKernel η := IsMarkovKernel.mk fun x ↦ this.isProbabilityMeasure _
    refine Measurable.lintegral_kernel_prod_left' <| hf.comp ?_
    simp only [updateSet, measurable_pi_iff]
    intro i
    by_cases h : i ∈ PIoc k N <;> simp [h]
    · exact (measurable_pi_apply _).comp measurable_fst
    · exact measurable_snd.eval
  · exact hf

theorem dependsOn_kerint' (k N K : ℕ) {f : ((n : ℕ+) → X n) → ℝ≥0∞} (hf : DependsOn f (PIoc 0 N))
    (hNk : N ≤ k) (x₀ : X 0) : kerint κ k K f x₀ = f := by
  ext x
  rw [kerint]
  split_ifs with hkK
  · have := isMarkovKernel_kerNat κ hkK
    rw [← mul_one (f x), ← measure_univ (μ := (kerNat κ k K) (fusion x₀ (fun i ↦ x i.1))),
      ← lintegral_const]
    refine lintegral_congr fun y ↦ hf fun i hi ↦ ?_
    simp only [updateSet, dite_eq_right_iff]
    intro h
    rw [mem_PIoc] at h hi
    omega
  · rfl

theorem dependsOn_kerint (k : ℕ) {N : ℕ} {f : ((n : ℕ+) → X n) → ℝ≥0∞} (hf : DependsOn f (PIoc 0 N))
    (x₀ : X 0) : DependsOn (kerint κ k N f x₀) (PIoc 0 k) := by
  intro x y hxy
  simp_rw [kerint]
  split_ifs with h
  · congrm ∫⁻ z : _, ?_ ∂(kerNat κ k N (fusion x₀ fun i ↦ ?_))
    · exact hxy i.1 i.2
    · refine dependsOn_updateSet hf _ _ ?_
      rwa [PIoc_diff_PIoc h.le]
  · refine hf fun i hi ↦ hxy i ?_
    rw [mem_PIoc] at hi ⊢
    omega

theorem kerint_self {k N : ℕ} (hkN : N ≤ k) (f : ((n : ℕ+) → X n) → ℝ≥0∞) (x₀ : X 0) :
    kerint κ k N f x₀ = f := by
  ext x
  rw [kerint, if_neg <| not_lt.2 hkN]

theorem updateSet_self {ι : Type*} {α : ι → Type*} (x : (i : ι) → α i) {s : Set ι}
    (y : (i : s) → α i) : (fun i : s ↦ updateSet x s y i) = y := by
  ext i
  simp [updateSet, i.2]

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
      simp only [el, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, fusion, updateSet, PNat.mk_coe]
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
    · simp only [updateSet, Ioc_PIoc_pi, er, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
      split_ifs <;> rw [mem_PIoc] at * <;> omega
  · exact hf.comp <| (measurable_updateSet _ _).comp <| (measurable_Ioc_PIoc_pi _ _).comp
      (er ..).measurable
  · exact hf.comp <| (measurable_updateSet _ _).comp <| measurable_Ioc_PIoc_pi ..

def e (n : ℕ) : (X (n + 1)) ≃ᵐ ((i : Ioc n (n + 1)) → X i) where
  toFun := fun x i ↦ (mem_Ioc_succ.1 i.2).symm ▸ x
  invFun := fun x ↦ x ⟨n + 1, mem_Ioc.2 ⟨n.lt_succ_self, le_refl (n + 1)⟩⟩
  left_inv := fun x ↦ by simp
  right_inv := fun x ↦ by
    ext i
    have : ⟨n + 1, mem_Ioc.2 ⟨n.lt_succ_self, le_refl (n + 1)⟩⟩ = i := by
      simp [(mem_Ioc_succ.1 i.2).symm]
    cases this; rfl
  measurable_toFun := by
    refine measurable_pi_lambda _ (fun i ↦ ?_)
    simp_rw [eqRec_eq_cast]
    apply measurable_cast
    have : ⟨n + 1, mem_Ioc.2 ⟨n.lt_succ_self, le_refl (n + 1)⟩⟩ = i := by
      simp [(mem_Ioc_succ.1 i.2).symm]
    cases this; rfl
  measurable_invFun := measurable_pi_apply _

theorem auxiliaire {f : ℕ → ((n : ℕ+) → X n) → ℝ≥0∞} {N : ℕ → ℕ}
    (hcte : ∀ n, DependsOn (f n) (PIoc 0 (N n))) (mf : ∀ n, Measurable (f n))
    {bound : ℝ≥0∞} (fin_bound : bound ≠ ∞) (le_bound : ∀ n x, f n x ≤ bound) {k : ℕ}
    {x₀ : X 0}
    (anti : ∀ x, Antitone (fun n ↦ kerint κ (k + 1) (N n) (f n) x₀ x))
    {l : ((n : ℕ+) → X n) → ℝ≥0∞}
    (htendsto : ∀ x, Tendsto (fun n ↦ kerint κ (k + 1) (N n) (f n) x₀ x) atTop (𝓝 (l x)))
    (ε : ℝ≥0∞) (y : (n : PIoc 0 k) → X n)
    (hpos : ∀ x n, ε ≤ kerint κ k (N n) (f n) x₀ (updateSet x _ y)) :
    ∃ z, ∀ x n,
    ε ≤ kerint κ (k + 1) (N n) (f n) x₀ (Function.update (updateSet x _ y) k.succPNat z) := by
  have _ n : Nonempty (X n) := by
    refine Nat.case_strong_induction_on (p := fun n ↦ Nonempty (X n)) _ inferInstance
      fun n hind ↦ ?_
    have : Nonempty ((i : Iic n) → X i) :=
      Nonempty.intro fun i ↦ @Classical.ofNonempty _ (hind i.1 (mem_Iic.1 i.2))
    exact ProbabilityMeasure.nonempty
      ⟨(kernel.map (κ n) (e n).symm (e n).measurable_invFun) Classical.ofNonempty, inferInstance⟩
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
      rw [kerint_self _ this, dependsOn_kerint' _ _ _ _ (hcte n) (this.trans k.le_succ),
        dependsOn_kerint' _ _ _ _ (hcte n) this]
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
        (measurable_updateSet _ _).comp <| measurable_Ioc_PIoc_pi ..)
      (fun n ↦ eventually_of_forall <| fun y ↦ F_le n _)
      ?_ (eventually_of_forall (fun _ ↦ tendstoF _))
    have := isMarkovKernel_kerNat κ k.lt_succ_self
    simp [fin_bound]
  -- By hypothesis, we have `ε ≤ ∫ F(y, xₖ) ∂μₖ`, so this is also true for `l`.
  have ε_le_lint x : ε ≤ kerint κ k (k + 1) l x₀ (updateSet x _ y) :=
    ge_of_tendsto (tendsto_int _) (by simp [hpos])
  let x_ : (n : ℕ+) → X n := Classical.ofNonempty
  -- We now have that the integral of `l` with respect to a probability measure is greater than `ε`,
  -- therefore there exists `x'` such that `ε ≤ l(y, x')`.
  obtain ⟨x', hx'⟩ : ∃ x', ε ≤ l (Function.update (updateSet x_ _ y) k.succPNat x') := by
    have aux : ∫⁻ (a : (i : Ioc k (k + 1)) → X i),
        l (updateSet (updateSet x_ _ y) _ (Ioc_PIoc_pi a)) ∂(κ k (fusion x₀ y)) ≠ ⊤ := by
      apply ne_top_of_le_ne_top fin_bound
      rw [← mul_one bound, ← measure_univ (μ := κ k (fusion x₀ y)), ← lintegral_const]
      exact lintegral_mono <| fun y ↦ le_of_tendsto' (tendstoF _) <| fun _ ↦ F_le _ _
    rcases exists_lintegral_le aux with ⟨x', hx'⟩
    refine ⟨x' ⟨k + 1, right_mem_Ioc.2 <| Nat.lt_succ_self _⟩, ?_⟩
    calc
      ε ≤ ∫⁻ (z : (i : Ioc k (k + 1)) → X i),
          l (updateSet (updateSet x_ _ y) _ (Ioc_PIoc_pi z)) ∂(κ k (fusion x₀ y)) := by
          rw [← kerNat_succ κ k]
          nth_rw 1 [← updateSet_self x_ y]
          simp only [kerint, k.lt_succ_self, ↓reduceIte] at ε_le_lint
          exact ε_le_lint _
      _ ≤ l (updateSet (updateSet x_ _ y) _ (Ioc_PIoc_pi x')) := hx'
      _ = l (Function.update (updateSet x_ _ y) k.succPNat (x' ⟨k + 1, _⟩)) := by
          rw [update_eq_updateSet]
          congr with i
          simp only [updateSet, PIoc, mem_Ico, Ioc_PIoc_pi, ioc_eq, zero_add, PNat.mk_ofNat,
            PNat.one_le, true_and, Nat.reduceAdd, Function.update]
          split_ifs with h1 h2 h3 h4 h5 h6
          · cases h2; rfl
          · exfalso; linarith [(PNat.coe_le_coe _ _).2 h1.1, (PNat.coe_lt_coe _ _).2 h3]
          · have : i.1 = k + 1 :=
              Nat.eq_of_le_of_lt_succ ((PNat.coe_le_coe _ _).2 h1.1) ((PNat.coe_lt_coe _ _).2 h1.2)
            exact (PNat.coe_inj.ne.2 h2 this).elim
          · rw [h5] at h4
            have := (PNat.coe_lt_coe _ _).2 h4
            simp at this
          · rfl
          · push_neg at h1
            rw [← PNat.coe_lt_coe, Nat.not_lt, h6] at h1
            simp [← PNat.coe_lt_coe] at h1
          · rfl
  refine ⟨x', fun x n ↦ ?_⟩
  -- As `F` is a non-increasing sequence, we have `ε ≤ Fₙ(y, x')` for any `n`.
  have := le_trans hx' ((anti _).le_of_tendsto (tendstoF _) n)
  -- This part below is just to say that this is true for any `x : (i : ι) → X i`,
  -- as `Fₙ` technically depends on all the variables, but really depends only on the first `k + 1`.
  convert this using 1
  refine dependsOn_kerint _ _ _ (hcte n) _ fun i hi ↦ ?_
  simp only [Function.update, updateSet, PIoc, zero_add, PNat.mk_ofNat, mem_Ico, PNat.one_le,
    true_and, Nat.reduceAdd]
  split_ifs with h1 h2
  · rfl
  · rfl
  · simp only [PIoc, zero_add, PNat.mk_ofNat, mem_Ico, PNat.one_le, true_and] at hi
    rw [← PNat.coe_lt_coe] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with a | b
    · rw [← PNat.coe_lt_coe] at h2
      exact (h2 a).elim
    · rw [← PNat.coe_inj] at h1
      exact (h1 b).elim

-- -- (fun (f : ((n : fPIoc 0 (t.sup id)) → X n)) (k : t) ↦
-- --       f ⟨k.1, Finset.mem_Icc.2 ⟨Nat.zero_le k.1, Finset.le_sup (f := id) k.2⟩⟩) ⁻¹' S

-- theorem cylinders_pnat :
--     cylinders (fun n : ℕ+ ↦ X n) = ⋃ (N) (_ : 0 < N) (S) (_ : MeasurableSet S),
--     {cylinder (fPIoc 0 N) S} := by
--   ext s
--   simp only [mem_cylinders, exists_prop, mem_iUnion, mem_singleton_iff]
--   constructor
--   · rintro ⟨t, S, mS, rfl⟩
--     refine ⟨(t.sup id).1, (t.sup id).pos, (fun (f : (n : fPIoc 0 (t.sup id).1) → X n) (k : t) ↦
--       f ⟨k.1, ?_⟩) ⁻¹' S, ?_, ?_⟩
--     · simp only [fPIoc, zero_add, PNat.mk_ofNat, Finset.mem_Ico]
--       refine ⟨PNat.one_le _, ?_⟩
--       have := Finset.le_sup (f := id) k.2
--       rw [← PNat.coe_lt_coe]
--       simp at this ⊢
--       rw [← PNat.coe_le_coe] at this
--       exact Nat.lt_succ_iff.2 this
--     · exact mS.preimage <| measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
--     · dsimp only [cylinder]
--       rw [← preimage_comp]
--       rfl
--   · rintro ⟨N, -, S, mS, rfl⟩
--     exact ⟨fPIoc 0 N, S, mS, rfl⟩

-- def key (ind : (k : ℕ) → ((n : PIoc 0 k) → X n) → X k.succPNat) : (k : ℕ+) → X k := fun k ↦ by
--   use cast (congrArg (fun k : ℕ+ ↦ X k) k.succPNat_natPred) (ind k.natPred (fun i ↦ key ind i.1))
--   termination_by k => k
--   decreasing_by
--   have := i.2
--   simp [PIoc] at this
--   exact this.2

-- theorem dependsOn_cylinder_indicator {ι : Type*} {α : ι → Type*} {I : Finset ι}
--     (S : Set ((i : I) → α i)) :
--     DependsOn ((cylinder I S).indicator (1 : ((i : ι) → α i) → ℝ≥0∞)) I := by
--   intro x y hxy
--   have : x ∈ cylinder I S ↔ y ∈ cylinder I S := by simp [hxy]
--   by_cases h : x ∈ cylinder I S
--   · simp [h, this.1 h]
--   · simp [h, this.not.1 h]

-- /-- This is the key theorem to prove the existence of the product measure: the `kolContent` of
-- a decresaing sequence of cylinders with empty intersection converges to $0$, in the case where
-- the measurable spaces are indexed by $\mathbb{N}$. This implies the $\sigma$-additivity of
-- `kolContent` (see `sigma_additive_addContent_of_tendsto_zero`),
-- which allows to extend it to the $\sigma$-algebra by Carathéodory's theorem. -/
-- theorem firstLemma (A : ℕ → Set ((n : ℕ+) → X n)) (A_mem : ∀ n, A n ∈ cylinders _)
--     (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) (x₀ : X 0) :
--     Tendsto (fun n ↦ kolContent (proj_family κ x₀) (A n)) atTop (𝓝 0) := by
--   -- `Aₙ` is a cylinder, it can be written `cylinder sₙ Sₙ`.
--   have A_cyl n : ∃ N S, 0 < N ∧ MeasurableSet S ∧ A n = cylinder (fPIoc 0 N) S := by
--     simpa [cylinders_pnat] using A_mem n
--   choose N S hN mS A_eq using A_cyl
--   set proj := proj_family κ x₀
--   -- We write `χₙ` for the indicator function of `Aₙ`.
--   let χ n := (A n).indicator (1 : ((n : ℕ+) → X n) → ℝ≥0∞)
--   -- `χₙ` is measurable.
--   have mχ n : Measurable (χ n) := by
--     simp_rw [χ, A_eq]
--     exact (measurable_indicator_const_iff 1).2 <| measurableSet_cylinder _ _ (mS n)
--   -- `χₙ` only depends on the first coordinates.
--   have χ_dep n : DependsOn (χ n) (PIoc 0 (N n)) := by
--     simp_rw [χ, A_eq]
--     rw [PIoc, ← Finset.coe_Ico]
--     exact dependsOn_cylinder_indicator _
--   -- Therefore its integral is constant.
--   have lma_const x y n : kerint κ 0 (N n) (χ n) x₀ x = kerint κ 0 (N n) (χ n) x₀ y := by
--     apply dependsOn_empty
--     convert dependsOn_kerint κ 0 (N n) (χ_dep n) x₀
--     simp [PIoc]
--   -- As `(Aₙ)` is non-increasing, so is `(χₙ)`.
--   have χ_anti : Antitone χ := by
--     intro m n hmn y
--     apply indicator_le
--     exact fun a ha ↦ by simp [χ, A_anti hmn ha]
--   -- Integrating `χₙ` further than the last coordinate it depends on does nothing.
--   -- This is used to then show that the integral of `χₙ` over all the variables except the first
--   -- `k` ones is non-increasing.
--   have lma_inv k M n (h : N n ≤ M) :
--       kerint κ k M (χ n) x₀ = kerint κ k (N n) (χ n) x₀ := by
--     refine Nat.le_induction rfl ?_ M h
--     intro K hK heq
--     rw [← heq]
--     ext x
--     rcases lt_trichotomy k K with hkK | hkK | hkK
--     · rw [kerint_eq' κ hkK (mχ n), dependsOn_kerint' _ _ _ _ (χ_dep n) hK]
--     · rw [hkK, dependsOn_kerint' _ _ _ _ (χ_dep n) hK, dependsOn_kerint' _ _ _ _ (χ_dep n) hK]
--     · rw [kerint_self _ (not_lt.2 <| Nat.succ_le.2 hkK), kerint_self _ (not_lt.2 hkK.le)]
--   -- the integral of `χₙ` over all the variables except the first `k` ones is non-increasing.
--   have anti_lma k x : Antitone fun n ↦ kerint κ k (N n) (χ n) x₀ x := by
--     intro m n hmn
--     simp only
--     rw [← lma_inv k ((N n).max (N m)) n (le_max_left _ _),
--       ← lma_inv k ((N n).max (N m)) m (le_max_right _ _)]
--     exact kerint_mono _ _ _ (χ_anti hmn) _ _
--   -- Therefore it converges to some function `lₖ`.
--   have this k x : ∃ l, Tendsto (fun n ↦ kerint κ k (N n) (χ n) x₀ x) atTop (𝓝 l) := by
--     rcases tendsto_of_antitone <| anti_lma k x with h | h
--     · rw [OrderBot.atBot_eq] at h
--       exact ⟨0, h.mono_right <| pure_le_nhds 0⟩
--     · exact h
--   choose l hl using this
--   -- `l₀` is constant because it is the limit of constant functions: we call it `ε`.
--   have l_const x y : l 0 x = l 0 y := by
--     have := hl 0 x
--     simp_rw [lma_const x y] at this
--     exact tendsto_nhds_unique this (hl 0 _)
--   obtain ⟨ε, hε⟩ : ∃ ε, ∀ x, l 0 x = ε := ⟨l 0 Classical.ofNonempty, fun x ↦ l_const ..⟩
--   -- As the sequence is decreasing, `ε ≤ ∫ χₙ`.
--   have hpos x n : ε ≤ kerint κ 0 (N n) (χ n) x₀ x :=
--     hε x ▸ ((anti_lma 0 _).le_of_tendsto (hl 0 _)) n
--   -- Also, the indicators are bounded by `1`.
--   have χ_le n x : χ n x ≤ 1 := by
--     apply Set.indicator_le
--     simp
--   -- We have all the conditions to apply àuxiliaire. This allows us to recursively
--   -- build a sequence `(zₙ)` with the following crucial property: for any `k` and `n`,
--   -- `ε ≤ ∫ χₙ(z₀, ..., z_{k-1}) ∂(μₖ ⊗ ... ⊗ μ_{Nₙ})`.
--   choose! ind hind using
--     fun k y h ↦ auxiliaire κ χ_dep mχ (by norm_num : (1 : ℝ≥0∞) ≠ ∞) χ_le (anti_lma (k + 1))
--       (hl (k + 1)) ε y h
--   let z := key ind
--   have crucial : ∀ k x n, ε ≤ kerint κ k (N n) (χ n) x₀ (updateSet x (PIoc 0 k) (fun i ↦ z i)) := by
--     intro k
--     induction k with
--     | zero =>
--       intro x n
--       rw [PIoc, Ico_self, updateSet_empty (hs := rfl)]
--       exact hpos x n
--     | succ m hm =>
--       intro x n
--       have : updateSet x (PIoc 0 (m + 1)) (fun i ↦ z i) =
--           Function.update (updateSet x (PIoc 0 m) (fun i ↦ z i))
--           ⟨m + 1, m.succ_pos⟩ (z ⟨m + 1, _⟩) := by
--         ext i
--         simp only [updateSet, PIoc, zero_add, PNat.mk_ofNat, mem_Ico, PNat.one_le, true_and,
--           Nat.reduceAdd, dite_eq_ite, Function.update]
--         split_ifs with h1 h2 h3 h4 h5
--         · cases h2; rfl
--         · rfl
--         · rw [← PNat.coe_lt_coe] at h1 h3
--           rw [← PNat.coe_inj] at h2
--           exact (not_or.2 ⟨h3, h2⟩ <| Nat.lt_succ_iff_lt_or_eq.1 h1).elim
--         · rw [h4, ← PNat.coe_lt_coe, PNat.mk_coe, PNat.mk_coe] at h1
--           exfalso; linarith
--         · rw [← PNat.coe_lt_coe, PNat.mk_coe] at h1 h5
--           exfalso; linarith
--         · rfl
--       rw [this]
--       convert hind m (fun i ↦ z i.1) hm x n
--   -- We now want to prove that the integral of `χₙ` converges to `0`.
--   have concl x n : kolContent proj (A n) = kerint κ 0 (N n) (χ n) x₀ x := by
--     simp_rw [χ, A_eq]
--     have : (fun s ↦ (kolContent proj).toFun s) = (kolContent proj).toFun := rfl
--     rw [← this, kolContent_eq_kerint _ (hN n) (mS n) x₀ x]
--   simp_rw [concl Classical.ofNonempty]
--   convert hl 0 Classical.ofNonempty
--   rw [hε]
--   by_contra!
--   -- Which means that we want to prove that `ε = 0`. But if `ε > 0`, then for any `n`,
--   -- choosing `k > Nₙ` we get `ε ≤ χₙ(z₀, ..., z_{Nₙ})` and therefore `(z n) ∈ Aₙ`.
--   -- This contradicts the fact that `(Aₙ)` has an empty intersection.
--   have ε_pos : 0 < ε := this.symm.bot_lt
--   have incr : ∀ n, z ∈ A n := by
--     intro n
--     have : χ n z = kerint κ (N n) (N n) (χ n) x₀
--         (updateSet z (PIoc 0 (N n)) (fun i ↦ z i)) := by
--       rw [kerint]
--       simp only [lt_self_iff_false, ↓reduceIte]
--       congr
--       ext i
--       simp [updateSet, PIoc]
--     have : 0 < χ n (z) := by
--       rw [this]
--       exact lt_of_lt_of_le ε_pos (crucial (N n) z n)
--     exact mem_of_indicator_ne_zero (ne_of_lt this).symm
--   exact (A_inter ▸ mem_iInter.2 incr).elim

-- theorem kolContent_sigma_subadditive_proj (x₀ : X 0) ⦃f : ℕ → Set ((n : ℕ+) → X n)⦄
--     (hf : ∀ n, f n ∈ cylinders (fun n : ℕ+ ↦ X n))
--     (hf_Union : (⋃ n, f n) ∈ cylinders (fun n : ℕ+ ↦ X n)) :
--     kolContent (proj_family κ x₀) (⋃ n, f n) ≤
--     ∑' n, kolContent (proj_family κ x₀) (f n) := by
--   classical
--   refine (kolContent (proj_family κ x₀)).sigma_subadditive_of_sigma_additive
--     setRing_cylinders (fun f hf hf_Union hf' ↦ ?_) f hf hf_Union
--   refine sigma_additive_addContent_of_tendsto_zero setRing_cylinders
--     (kolContent (proj_family κ x₀)) (fun h ↦ ?_) ?_ hf hf_Union hf'
--   · rename_i s
--     obtain ⟨N, S, hN, mS, s_eq⟩ : ∃ N S, 0 < N ∧ MeasurableSet S ∧ s = cylinder (fPIoc 0 N) S := by
--       simpa [cylinders_pnat] using h
--     let x_ : (n : ℕ+) → X n := Classical.ofNonempty
--     rw [s_eq, kolContent_eq_kerint κ hN mS x₀ x_]
--     refine ne_of_lt (lt_of_le_of_lt ?_ (by norm_num : (1 : ℝ≥0∞) < ⊤))
--     rw [kerint, if_pos hN]
--     have : IsMarkovKernel (kerNat κ 0 N) := isMarkovKernel_kerNat κ hN
--     nth_rw 2 [← mul_one 1, ← measure_univ (μ := kerNat κ 0 N (fusion x₀ fun i ↦ x_ i.1))]
--     rw [← lintegral_const]
--     apply lintegral_mono
--     apply Set.indicator_le
--     simp
--   · exact fun s hs anti_s inter_s ↦ firstLemma κ s hs anti_s inter_s x₀

-- noncomputable def ionescu_tulcea_fun (x₀ : X 0) : Measure ((n : ℕ+) → X n) := by
--   exact Measure.ofAddContent setSemiringCylinders generateFrom_cylinders
--     (kolContent (proj_family κ x₀))
--     (kolContent_sigma_subadditive_proj κ x₀)

-- theorem proba_ionescu (x₀ : X 0) : IsProbabilityMeasure (ionescu_tulcea_fun κ x₀) := by
--   constructor
--   rw [← cylinder_univ ∅, ionescu_tulcea_fun, Measure.ofAddContent_eq,
--       fun x₀ ↦ kolContent_congr (proj_family κ x₀) _ rfl MeasurableSet.univ]
--   · simp only [family]
--     rw [← kernel.map_apply _ (measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _))]
--     have : IsMarkovKernel (kerNat κ 0 1) := isMarkovKernel_kerNat κ zero_lt_one
--     simp
--   · simp only [mem_cylinders, exists_prop, forall_const]
--     exact ⟨∅, univ, MeasurableSet.univ, rfl⟩
--   · simp only [mem_cylinders, exists_prop, forall_const]
--     exact ⟨∅, univ, MeasurableSet.univ, rfl⟩


-- /-- The product measure is the projective limit of the partial product measures. This ensures
-- uniqueness and expresses the value of the product measures applied to cylinders. -/
-- theorem isProjectiveLimit_ionescu_tulcea_fun (x₀ : X 0) :
--     IsProjectiveLimit (ionescu_tulcea_fun κ x₀) (family κ x₀) := by
--   intro I
--   ext1 s hs
--   rw [Measure.map_apply _ hs]
--   swap; · apply measurable_proj
--   have h_mem : (fun (x : (n : ℕ+) → X n.1) (i : I) ↦ x i) ⁻¹' s ∈
--       cylinders (fun n : ℕ+ ↦ X n.1) := by
--     rw [mem_cylinders]; exact ⟨I, s, hs, rfl⟩
--   rw [ionescu_tulcea_fun, Measure.ofAddContent_eq,
--     kolContent_congr (proj_family κ x₀)]
--   · exact h_mem
--   · rfl
--   · exact hs
--   · exact h_mem

-- theorem measurable_ionescu : Measurable (ionescu_tulcea_fun κ) := by
--   apply Measure.measurable_of_measurable_coe
--   refine MeasurableSpace.induction_on_inter
--     (C := fun t ↦ Measurable (fun x₀ ↦ ionescu_tulcea_fun κ x₀ t))
--     (s := cylinders (fun n : ℕ+ ↦ X n))
--     generateFrom_cylinders.symm
--     isPiSystem_cylinders
--     ?empty
--     (fun t ht ↦ ?cylinder)
--     (fun t mt ht ↦ ?compl)
--     (fun f disf mf hf ↦ ?union)
--   · simp_rw [measure_empty]
--     exact measurable_const
--   · obtain ⟨N, S, -, mS, t_eq⟩ : ∃ N S, 0 < N ∧ MeasurableSet S ∧ t = cylinder (fPIoc 0 N) S := by
--       simpa [cylinders_pnat] using ht
--     simp_rw [ionescu_tulcea_fun, Measure.ofAddContent_eq _ _ _ _ ht,
--       fun x₀ ↦ kolContent_congr (proj_family κ x₀) ht t_eq mS]
--     simp only [family]
--     refine Measure.measurable_measure.1 ?_ _ mS
--     refine (Measure.measurable_map _ ?_).comp <| (kernel.measurable _).comp zer.measurable
--     exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
--   · have this x₀ : ionescu_tulcea_fun κ x₀ tᶜ = 1 - ionescu_tulcea_fun κ x₀ t := by
--       have := fun x₀ ↦ proba_ionescu κ x₀
--       rw [measure_compl mt (measure_ne_top _ _), measure_univ]
--     simp_rw [this]
--     exact Measurable.const_sub ht _
--   · simp_rw [measure_iUnion disf mf]
--     exact Measurable.ennreal_tsum hf

-- noncomputable def ionescu_tulcea_kernel : kernel (X 0) ((n : ℕ+) → X n) :=
--   { val := ionescu_tulcea_fun κ
--     property := measurable_ionescu κ }

-- instance : IsMarkovKernel (ionescu_tulcea_kernel κ) := IsMarkovKernel.mk fun _ ↦ proba_ionescu _ _

-- def er' (N : ℕ) : (X 0) × ((i : Ioc 0 N) → X i) ≃ᵐ ((i : Iic N) → X i) where
--   toFun := fun p n ↦ if h : n.1 = 0 then h.symm ▸ p.1 else
--     p.2 ⟨n.1, ⟨Nat.zero_lt_of_ne_zero h, n.2⟩⟩
--   invFun := fun x ↦ ⟨x ⟨0, N.zero_le⟩, fun n ↦ x ⟨n.1, Ioc_subset_Iic_self n.2⟩⟩
--   left_inv := fun p ↦ by
--     ext i
--     · simp
--     · simp only
--       split_ifs with h
--       · simpa [h] using i.2
--       · rfl
--   right_inv := fun x ↦ by
--     ext i
--     simp only
--     split_ifs with h
--     · have : i = ⟨0, N.zero_le⟩ := by rwa [← Subtype.val_inj]
--       cases this; rfl
--     · rfl
--   measurable_toFun := by
--     apply measurable_pi_lambda _ (fun n ↦ ?_)
--     by_cases h : n.1 = 0
--     · simp only [Equiv.coe_fn_mk, h, ↓reduceDite]
--       simp_rw [eqRec_eq_cast]
--       exact (measurable_cast _ (by aesop)).comp measurable_fst
--     · simp only [Equiv.coe_fn_mk, h, ↓reduceDite]
--       exact (measurable_pi_apply _).comp measurable_snd
--   measurable_invFun := (measurable_pi_apply _).prod_mk <|
--     measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

-- def er'' :
--     (X 0) × ((n : ℕ+) → X n) ≃ᵐ ((n : ℕ) → X n) where
--   toFun := fun p n ↦ if h : n = 0 then h ▸ p.1 else p.2 ⟨n, Nat.zero_lt_of_ne_zero h⟩
--   invFun := fun x ↦ ⟨x 0, fun n ↦ x n⟩
--   left_inv := fun p ↦ by
--     simp only [↓reduceDite, PNat.ne_zero]
--     rfl
--   right_inv := fun p ↦ by
--     simp only [PNat.mk_coe]
--     ext n
--     split_ifs with h
--     · cases h; rfl
--     · rfl
--   measurable_toFun := by
--     refine measurable_pi_lambda _ (fun n ↦ ?_)
--     by_cases h : n = 0
--     · simp only [Equiv.coe_fn_mk, h, dite_true]
--       simp_rw [eqRec_eq_cast]
--       exact (measurable_cast _ (by cases h; rfl)).comp measurable_fst
--     · simp only [Equiv.coe_fn_mk, h, dite_false]
--       exact measurable_snd.eval
--   measurable_invFun := (measurable_pi_apply _).prod_mk <|
--     measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

-- theorem proj_zero_eq_zer_proj_zero :
--     (fun (x : (n : ℕ) → X n) (i : Iic 0) ↦ x i) = zer ∘ (fun x ↦ x 0) := by
--   ext x i
--   simp only [zer, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply]
--   have : i.1 = 0 := mem_Iic_zero i.2
--   aesop

-- theorem proj_zero_er''_eq : (fun x ↦ x 0) ∘ (er'' (X := X)) = Prod.fst := by
--   ext x
--   simp [er'']

-- theorem proj_er''_eq_er'_prod (N : ℕ) :
--     (fun (x : (n : ℕ) → X n) (i : Iic N) ↦ x i) ∘ er'' =
--     (er' N) ∘ (Prod.map id (fun x (i : Ioc 0 N) ↦ x ⟨i.1, (mem_Ioc.1 i.2).1⟩)) := by
--   ext x i
--   simp [er'', er']

-- noncomputable def ionescu_ker : kernel (X 0) ((n : ℕ) → X n) :=
--   kernel.map
--     ((kernel.deterministic id measurable_id) ×ₖ (ionescu_tulcea_kernel κ))
--     er'' er''.measurable

-- theorem ionescu_ker_proj_zero :
--     kernel.map (ionescu_ker κ) (fun x ↦ x 0) (measurable_pi_apply _) =
--     kernel.deterministic id measurable_id := by
--   rw [ionescu_ker, kernel.map_map]
--   conv_lhs => enter [2]; rw [proj_zero_er''_eq]
--   exact kernel.fst_prod _ _

-- noncomputable def my_ker (N : ℕ) :
--     kernel (X 0) ((i : Iic N) → X i) := by
--   cases N with
--   | zero =>
--     exact kernel.map (kernel.deterministic id measurable_id) zer zer.measurable_toFun
--   | succ n =>
--     exact kernel.map ((kernel.deterministic id measurable_id) ×ₖ
--         (kernel.comap (kerNat κ 0 (n + 1)) zer zer.measurable_toFun))
--       (er' (n + 1)) (er' (n + 1)).measurable

-- theorem my_ker_zero : my_ker κ 0 =
--     kernel.map (kernel.deterministic id measurable_id) zer zer.measurable := rfl

-- theorem my_ker_pos {N : ℕ} (hN : 0 < N) :
--     my_ker κ N = kernel.map ((kernel.deterministic id measurable_id) ×ₖ
--         (kernel.comap (kerNat κ 0 N) zer zer.measurable_toFun))
--       (er' N) (er' N).measurable := by
--   rw [← N.succ_pred (ne_of_lt hN).symm]
--   rfl

-- theorem Measure.map_prod {X Y Z T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
--     [MeasurableSpace Z] [MeasurableSpace T] (μ : Measure X) [IsFiniteMeasure μ]
--     (ν : Measure Y) [IsFiniteMeasure ν] {f : X → Z} (hf : Measurable f)
--     {g : Y → T} (hg : Measurable g) :
--     (μ.prod ν).map (Prod.map f g) = (μ.map f).prod (ν.map g) := by
--   refine (Measure.prod_eq fun s t ms mt ↦ ?_).symm
--   rw [Measure.map_apply (hf.prod_map hg) (ms.prod mt)]
--   · have : Prod.map f g ⁻¹' s ×ˢ t = (f ⁻¹' s) ×ˢ (g ⁻¹' t) := prod_preimage_eq.symm
--     rw [this, Measure.prod_prod, Measure.map_apply hf ms, Measure.map_apply hg mt]

-- theorem kernel.map_prod {X Y Z T U : Type*} [MeasurableSpace X] [MeasurableSpace Y]
--     [MeasurableSpace Z] [MeasurableSpace T] [MeasurableSpace U]
--     (κ : kernel X Y) [IsFiniteKernel κ] (η : kernel X T) [IsFiniteKernel η]
--     {f : Y → Z} (hf : Measurable f) {g : T → U} (hg : Measurable g) :
--     kernel.map (κ ×ₖ η) (Prod.map f g) (hf.prod_map hg) =
--     (kernel.map κ f hf) ×ₖ (kernel.map η g hg) := by
--   ext1 x
--   rw [kernel.map_apply, kernel.prod_apply, Measure.map_prod _ _ hf hg, kernel.prod_apply,
--     kernel.map_apply, kernel.map_apply]

-- theorem ionescu_tulcea_kernel_apply (x₀ : X 0) :
--     ionescu_tulcea_kernel κ x₀ = ionescu_tulcea_fun κ x₀ := by
--   rw [ionescu_tulcea_kernel]
--   rfl

-- lemma omg' {s t : Set ℕ} (h : s = t) (h' : ((i : s) → X i) = ((i : t) → X i))
--     (x : (i : s) → X i) (i : s) (hi : i.1 ∈ t) :
--     cast h' x ⟨i.1, hi⟩ = x i := by
--   subst h
--   rfl

-- theorem kernel.map_eq {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
--     (κ : kernel X Y) {f g : Y → Z} (hf : Measurable f) (hfg : f = g) :
--     kernel.map κ f hf = kernel.map κ g (hfg ▸ hf) := by cases hfg; rfl

-- theorem ionescu_ker_proj (N : ℕ) :
--     kernel.map (ionescu_ker κ) (fun x (i : Iic N) ↦ x i) (measurable_proj _) = my_ker κ N := by
--   rcases eq_zero_or_pos N with hN | hN
--   · cases hN
--     rw [my_ker_zero, kernel.map_eq _ _ proj_zero_eq_zer_proj_zero,
--       ← kernel.map_map _ (measurable_pi_apply _) zer.measurable, ionescu_ker_proj_zero]
--   · rw [ionescu_ker, kernel.map_map, my_ker_pos _ hN, kernel.map_eq _ _ (proj_er''_eq_er'_prod N),
--       ← kernel.map_map]
--     · congr
--       rw [kernel.map_prod, kernel.map_id]
--       · congr
--         ext1 x₀
--         rw [kernel.map_apply, ionescu_tulcea_kernel_apply,
--           ← Function.id_comp
--             (fun (x : (n : ℕ+) → X n) (i : Ioc 0 N) ↦ x ⟨i.1, (mem_Ioc.1 i.2).1⟩),
--           ← (@Ioc_fPIoc_pi _ _ 0 N).symm_comp_self, Function.comp.assoc, ← Measure.map_map]
--         · have : ⇑Ioc_fPIoc_pi ∘ (fun (x : (n : ℕ+) → X n) (i : Ioc 0 N) ↦
--               x ⟨i.1, (mem_Ioc.1 i.2).1⟩) =
--               fun (x : (n : ℕ+) → X n) (i : fPIoc 0 N) ↦ x i := by ext; rfl
--           rw [this, isProjectiveLimit_ionescu_tulcea_fun, family,
--             ← measure_cast (sup_fPIoc hN).symm (fun n ↦ kerNat κ 0 n (zer x₀)),
--             Measure.map_map, Measure.map_map]
--           · rw [kernel.comap_apply]
--             nth_rw 2 [← kernel.map_id (kerNat κ 0 N)]
--             rw [kernel.map_apply]
--             congr
--             ext x i
--             simp only [Ioc_fPIoc_pi, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
--               Equiv.coe_fn_symm_mk, Function.comp_apply, PNat.mk_coe, id_eq]
--             apply omg'
--             rw [sup_fPIoc hN]
--           · exact Ioc_fPIoc_pi.measurable_invFun.comp <|
--               measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
--           · refine measurable_cast _ (heq_meas _ _ ?_)
--             rw [sup_fPIoc hN]
--           · exact Ioc_fPIoc_pi.measurable_invFun
--           · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
--         · exact Ioc_fPIoc_pi.measurable_invFun
--         · exact Ioc_fPIoc_pi.measurable_toFun.comp <|
--             measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
--         · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
--     · exact (er' N).measurable_toFun

-- theorem integral_dep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
--     {N : ℕ} (x₀ : X 0) {f : ((i : Iic N) → X i) → E} (hf : AEStronglyMeasurable f (my_ker κ N x₀)) :
--     ∫ y, f ((fun x (i : Iic N) ↦ x i) y) ∂ionescu_ker κ x₀ =
--     ∫ y, f y ∂my_ker κ N x₀ := by
--   rw [← ionescu_ker_proj, kernel.map_apply, integral_map]
--   · exact (measurable_proj _).aemeasurable
--   · rw [← kernel.map_apply, ionescu_ker_proj]
--     exact hf

-- variable (κ : (n : ℕ) → kernel ((i : Iic n) → X i) (X (n + 1)))
-- variable [∀ n, IsMarkovKernel (κ n)]

-- noncomputable def noyau : kernel (X 0) ((n : ℕ) → X n) :=
--   ionescu_ker (fun n ↦ kernel.map (κ n) (e n) (e n).measurable_toFun)

-- instance : IsMarkovKernel (noyau κ) := by
--   apply kernel.IsMarkovKernel.map
--   exact er''.measurable

-- noncomputable def noyau_partiel (N : ℕ) : kernel (X 0) ((i : Iic N) → X i) :=
--   my_ker (fun n ↦ kernel.map (κ n) (e n) (e n).measurable_toFun) N

-- theorem noyau_proj (N : ℕ) :
--     kernel.map (noyau κ) (fun x (i : Iic N) ↦ x i) (measurable_proj _) =
--     noyau_partiel κ N := ionescu_ker_proj _ _

-- theorem noyau_proj_zero : kernel.map (noyau κ) (fun x ↦ x 0) (measurable_pi_apply 0) =
--     kernel.deterministic id measurable_id := by
--   rw [noyau, ionescu_ker_proj_zero]
