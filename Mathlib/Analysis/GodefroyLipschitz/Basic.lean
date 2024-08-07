import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.LinearAlgebra.Dimension.Finrank

open Real NNReal Set Filter Topology FiniteDimensional MeasureTheory Module Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem dense_of_ae {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure]
    {p : X → Prop} (hp : ∀ᵐ x ∂μ, p x) : Dense {x | p x} := by
  rw [dense_iff_closure_eq, closure_eq_compl_interior_compl, compl_univ_iff]
  exact μ.interior_eq_empty_of_null hp

theorem basis_of_span [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (hn : finrank ℝ E = n)
    {s : Set E} (hs : span ℝ s = ⊤) :
    ∃ b : Basis (Fin n) ℝ E, range b ⊆ s := by
  let u := (linearIndependent_empty ℝ E).extend (empty_subset s)
  let v : u → E := Subtype.val
  have liv := (linearIndependent_empty ℝ E).linearIndependent_extend (empty_subset s)
  have sv : ⊤ ≤ span ℝ (range v) := by
    rw [Subtype.range_val_subtype, ← hs, span_le]
    exact (linearIndependent_empty ℝ E).subset_span_extend (empty_subset s)
  let w := Basis.mk liv sv
  use w.reindex (w.indexEquiv (finBasisOfFinrankEq ℝ E hn))
  rw [w.range_reindex, show range w = range v by simp [v, w], Subtype.range_val_subtype]
  exact (linearIndependent_empty ℝ E).extend_subset (empty_subset s)

theorem test [FiniteDimensional ℝ E] {n : ℕ} (hn : finrank ℝ (E →ₗ[ℝ] ℝ) = n)
    (h : ∀ z : E, z ≠ 0 → ∃ x : E, DifferentiableAt ℝ (‖·‖) x ∧ fderiv ℝ (‖·‖) x z ≠ 0) :
    ∃ b : Basis (Fin n) ℝ (E →ₗ[ℝ] ℝ),
      ∀ i, ∃ y : E, DifferentiableAt ℝ (‖·‖) y ∧ b i = fderiv ℝ (‖·‖) y := by
  let S := {f : E→ₗ[ℝ] ℝ | ∃ x : E, DifferentiableAt ℝ (‖·‖) x ∧ f = fderiv ℝ (‖·‖) x}
  have : span ℝ S = ⊤ := by
    by_contra! hn
    rcases exists_dual_map_eq_bot_of_lt_top hn.lt_top inferInstance with ⟨f, fne, hf⟩
    let fs := (Module.evalEquiv ℝ E).symm f
    have : ∀ x : E, DifferentiableAt ℝ (‖·‖) x → fderiv ℝ (‖·‖) x fs = 0 := by
      intro x dx
      rw [← mem_bot ℝ, ← hf, Submodule.mem_map]
      exact ⟨fderiv ℝ (‖·‖) x, Submodule.subset_span ⟨x, dx, rfl⟩,
        (apply_evalEquiv_symm_apply ℝ E (fderiv ℝ (‖·‖) x) f).symm⟩
    have fsn : fs ≠ 0 := by simp [fne, fs]
    rcases h fs fsn with ⟨x, dx, hx⟩
    exact hx <| this x dx
  rcases basis_of_span hn this with ⟨b, hb⟩
  exact ⟨b, fun i ↦ hb ⟨i, rfl⟩⟩

theorem lol (f : E → ℝ) (x y : E) (h : DifferentiableAt ℝ f x) :
    fderiv ℝ f x y = deriv (fun t : ℝ ↦ f (x + t • y)) 0 := by
  conv_rhs => enter [1]; change f ∘ (fun t ↦ x + t • y)
  rw [fderiv.comp_deriv, zero_smul, add_zero, deriv_const_add, deriv_smul_const, deriv_id'']
  · simp
  · exact differentiableAt_id
  · simpa
  · simp

theorem logique {x : E} {t : ℝ} (ht : t ≠ 0) {f : E →L[ℝ] ℝ} (hx : HasFDerivAt (‖·‖) f x) :
    HasFDerivAt (‖·‖) ((|t| / t) • f) (t • x) := by
  unfold HasFDerivAt at *
  have hx := hx.isLittleO
  constructor
  rw [Asymptotics.isLittleO_iff] at *
  intro c hc
  have := hx hc
  rw [eventually_iff, ← set_smul_mem_nhds_smul_iff ht] at this
  filter_upwards [this]
  rintro - ⟨ε, hε, rfl⟩
  simp only
  rw [norm_smul, norm_smul, ← smul_sub, _root_.map_smul, ← ContinuousLinearMap.smul_apply,
    smul_smul, mul_div_cancel₀ _ ht, ContinuousLinearMap.smul_apply, ← norm_eq_abs, smul_eq_mul,
    ← mul_sub, ← mul_sub, norm_mul, norm_norm, norm_smul, ← mul_assoc, mul_comm c, mul_assoc,
    _root_.mul_le_mul_left]
  · exact hε
  · exact norm_pos_iff.2 ht

theorem differentiableAt_norm_smul {x : E} {t : ℝ} (ht : t ≠ 0) :
    DifferentiableAt ℝ (‖·‖) x ↔ DifferentiableAt ℝ (‖·‖) (t • x) where
  mp hd := (logique ht hd.hasFDerivAt).differentiableAt
  mpr hd := by
    convert (logique (inv_ne_zero ht) hd.hasFDerivAt).differentiableAt
    rw [smul_smul, inv_mul_cancel ht, one_smul]

theorem fderiv_norm {x : E} (h : DifferentiableAt ℝ (‖·‖) x) :
    fderiv ℝ (‖·‖) x x = ‖x‖ := by
  rw [lol _ _ _ h]
  have this (t : ℝ) (ht : t ≥ -1) : ‖x + t • x‖ = (1 + t) * ‖x‖ := by
    calc
      ‖x + t • x‖ = ‖(1 + t) • x‖ := by
        rw [add_smul, one_smul]
      _ = |1 + t| * ‖x‖ := by
        rw [← norm_eq_abs, norm_smul]
      _ = (1 + t) * ‖x‖ := by
        rw [abs_eq_self.2]
        linarith
  rw [← derivWithin_of_mem_nhds (s := Ici (-1)), derivWithin_congr (f := fun t ↦ (1 + t) * ‖x‖),
    derivWithin_of_mem_nhds]
  · rw [deriv_mul_const, deriv_const_add]
    simp
    apply DifferentiableAt.const_add
    exact differentiableAt_id
  · exact Ici_mem_nhds (by norm_num)
  · intro t ht
    apply this
    simpa
  · simp
  · exact Ici_mem_nhds (by norm_num)

theorem not_differentiableAt_norm_zero (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] :
    ¬DifferentiableAt ℝ (‖·‖) (0 : E) := by
  rcases NormedSpace.exists_lt_norm ℝ E 0 with ⟨x, hx⟩
  intro h
  have : DifferentiableAt ℝ (fun t : ℝ ↦ ‖t • x‖) 0 := by
    apply DifferentiableAt.comp
    · simpa
    · simp
  have : DifferentiableAt ℝ (|·|) (0 : ℝ) := by
    simp_rw [norm_smul, norm_eq_abs] at this
    have mdr : (fun t : ℝ ↦ |t|) = fun t : ℝ ↦ (1 / ‖x‖) * |t| * ‖x‖ := by
      ext t
      rw [mul_assoc, mul_comm, mul_assoc, mul_one_div_cancel, mul_one]
      exact hx.ne.symm
    rw [mdr]
    simp_rw [mul_assoc]
    apply DifferentiableAt.const_mul
    exact this
  exact not_differentiableAt_abs_zero this

theorem fderiv_norm_smul (x : E) (t : ℝ) :
    fderiv ℝ (‖·‖) (t • x) = (|t| / t) • (fderiv ℝ (‖·‖) x) := by
  by_cases Nontrivial E
  · by_cases hd : DifferentiableAt ℝ (‖·‖) x
    · rcases eq_or_ne t 0 with rfl | ht
      · simp only [zero_smul, abs_zero, div_zero]
        rw [fderiv_zero_of_not_differentiableAt]
        exact not_differentiableAt_norm_zero E
      · rw [(logique ht hd.hasFDerivAt).fderiv]
    · rw [fderiv_zero_of_not_differentiableAt hd, smul_zero, fderiv_zero_of_not_differentiableAt]
      rcases eq_or_ne t 0 with rfl | ht
      · convert not_differentiableAt_norm_zero E
        exact zero_smul _ _
      · exact (differentiableAt_norm_smul ht).not.1 hd
  · rw [not_nontrivial_iff_subsingleton] at *
    rw [(hasFDerivAt_of_subsingleton _ _).fderiv, (hasFDerivAt_of_subsingleton _ _).fderiv]
    simp

theorem fderiv_norm_smul_pos {x : E} {t : ℝ} (ht : t > 0) :
    fderiv ℝ (‖·‖) (t • x) = fderiv ℝ (‖·‖) x := by
  rw [fderiv_norm_smul, abs_of_pos ht, div_self ht.ne.symm, one_smul]

theorem norm_fderiv_norm {x : E} (h : DifferentiableAt ℝ (‖·‖) x) :
    ‖fderiv ℝ (‖·‖) x‖ = 1 := by
  have : x ≠ 0 := by
    intro hx
    apply not_differentiableAt_norm_zero E
    convert h
    exact hx.symm
  apply le_antisymm
  · rw [show (1 : ℝ) = ↑(1 : ℝ≥0) by rfl]
    apply norm_fderiv_le_of_lipschitz
    exact lipschitzWith_one_norm
  · apply le_of_mul_le_mul_right (a := ‖x‖)
    rw [one_mul]
    calc
      ‖x‖ = fderiv ℝ (‖·‖) x x := (fderiv_norm h).symm
      _ ≤ ‖fderiv ℝ (‖·‖) x x‖ := le_norm_self _
      _ ≤ ‖fderiv ℝ (‖·‖) x‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    exact norm_pos_iff.2 this


theorem unique1 [FiniteDimensional ℝ E] {x : E} (hx : ‖x‖ = 1) (h : DifferentiableAt ℝ (‖·‖) x)
    (φ : E → ℝ) (hφ : LipschitzWith 1 φ) (φ_eq : ∀ t : ℝ, φ (t • x) = t) :
    φ = fderiv ℝ (‖·‖) x := by
  ext y
  have this t (ht : t ≠ 0) : 1 = |t * (φ y) - t * (φ (((φ y) + 1 / t) • x))| := by
    rw [φ_eq, mul_add, ← sub_sub, sub_self, mul_one_div_cancel ht]
    simp
  have this (t : ℝ) : 1 ≤ ‖x - t • (y - (φ y) • x)‖ := by
    rcases eq_or_ne t 0 with rfl | ht
    · rw [zero_smul, sub_zero, hx]
    · calc
        1 = |t * (φ y) - t * (φ (((φ y) + 1 / t) • x))| := this t ht
        _ = |t| * |φ y - φ (((φ y) + 1 / t) • x)| := by
          rw [← abs_mul]
          congr
          ring
        _ ≤ |t| * ‖y - (φ y + 1 / t) • x‖ := by
          rw [_root_.mul_le_mul_left]
          convert hφ.dist_le_mul y ((φ y + 1 / t) • x) using 1
          · simp [dist_eq_norm]
          · exact abs_pos.2 ht
        _ = ‖x - t • (y - (φ y) • x)‖ := by
          rw [← norm_eq_abs, ← norm_smul, ← norm_neg, smul_sub, smul_smul, mul_add,
            mul_one_div_cancel ht, add_smul, one_smul, mul_smul, smul_sub]
          congr 1
          abel
  have : IsLocalMin (fun t : ℝ ↦ ‖x - t • (y - (φ y) • x)‖) 0 := by
    simp [IsLocalMin, IsMinFilter, hx, this]
  have aux := this.deriv_eq_zero
  have : deriv (fun t : ℝ ↦ ‖x - t • (y - (φ y) • x)‖) 0 = - fderiv ℝ (‖·‖) x (y - (φ y) • x) := by
    conv_lhs => enter [1]; change ((‖·‖) ∘ (fun t : ℝ ↦ x - t • (y - (φ y) • x)))
    rw [fderiv.comp_deriv]
    · rw [deriv_const_sub, deriv_smul_const]
      simp
      exact differentiableAt_id
    · simpa
    · simp
  rw [aux, map_sub, _root_.map_smul, fderiv_norm h, hx] at this
  simp only [smul_eq_mul, mul_one, neg_sub] at this
  exact sub_eq_zero.1 this.symm

theorem tendsto_differentiable
    {x : ℕ → E} (hd : ∀ n, DifferentiableAt ℝ (‖·‖) (x n))
    {z : E} (ht : Tendsto x atTop (𝓝 z)) :
    Tendsto (fun n ↦ fderiv ℝ (‖·‖) (x n) z) atTop (𝓝 ‖z‖) := by
  have aux1 : Tendsto (fun n ↦ fderiv ℝ (‖·‖) (x n) (x n)) atTop (𝓝 ‖z‖) := by
    simp_rw [fun n ↦ fderiv_norm (hd n)]
    exact (continuous_norm.tendsto z).comp ht
  apply tendsto_of_tendsto_of_dist aux1
  simp_rw [dist_eq_norm, ← map_sub]
  apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ContinuousLinearMap.le_opNorm _ _)
  simp_rw [fun n ↦ norm_fderiv_norm (hd n), one_mul]
  exact tendsto_iff_norm_sub_tendsto_zero.1 ht

theorem exists_inverse (h : finrank ℝ E = 1) (φ : E → F) (hφ : Isometry φ) :
    ∃ (f : F →L[ℝ] E), ‖f‖ = 1 ∧ ∀ x : E, f (φ x) = x := by sorry

theorem norm_normalize {x : E} (hx : x ≠ 0) : ‖(1 / ‖x‖) • x‖ = 1 := by
  rw [norm_smul, norm_div, norm_one, norm_norm, one_div_mul_cancel (norm_ne_zero_iff.2 hx)]

theorem dense_seq {X : Type*} [TopologicalSpace X] [FrechetUrysohnSpace X]
    {s : Set X} (hs : Dense s) (x : X) :
    ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ Tendsto u atTop (𝓝 x) := by
  rw [← mem_closure_iff_seq_limit, dense_iff_closure_eq.1 hs]; trivial

theorem exists_inverse' [FiniteDimensional ℝ E] {n : ℕ} (hn : finrank ℝ (E →ₗ[ℝ] ℝ) = n)
    (φ : E → F) (hφ : Isometry φ) (φz : φ 0 = 0)
    (hlol : Dense (X := F) (Submodule.span ℝ (range φ))) :
    ∃ (f : F →L[ℝ] E), ‖f‖ = 1 ∧ f ∘ φ = id := by
  have main (x : E) (nx : ‖x‖ = 1) : ∃ f : F →L[ℝ] ℝ, ‖f‖ = 1 ∧ ∀ t : ℝ, f (φ (t • x)) = t := by
    apply exists_inverse
    · exact finrank_self ℝ
    · apply Isometry.of_dist_eq
      intro x₁ x₂
      rw [hφ.dist_eq, dist_eq_norm, ← sub_smul, norm_smul, nx, mul_one, dist_eq_norm]
  choose! f nf hf using main
  have aux2 : Dense {x : E | DifferentiableAt ℝ (‖·‖) x} := by
    let _ : MeasurableSpace E := borel E
    have _ : BorelSpace E := ⟨rfl⟩
    let w := FiniteDimensional.finBasis ℝ E
    exact dense_of_ae (lipschitzWith_one_norm.ae_differentiableAt (μ := w.addHaar))
  have aux3 (z : E) (hz : z ≠ 0) : ∃ x', DifferentiableAt ℝ (‖·‖) x' ∧ fderiv ℝ (‖·‖) x' z ≠ 0 := by
    obtain ⟨u, hu, htu⟩ := dense_seq aux2 z
    have := tendsto_differentiable hu htu
    have := this.eventually_ne (norm_ne_zero_iff.2 hz)
    rw [eventually_atTop] at this
    rcases this with ⟨N, hN⟩
    exact ⟨u N, hu N, hN N (le_refl N)⟩
  rcases test hn aux3 with ⟨b, hb⟩
  have hb i : ∃ y : E, ‖y‖ = 1 ∧ DifferentiableAt ℝ (‖·‖) y ∧ b i = fderiv ℝ (‖·‖) y := by
    rcases hb i with ⟨y, dy, hy⟩
    have bin := b.ne_zero i
    have yn : y ≠ 0 := by
      intro hyn
      rw [hyn, fderiv_zero_of_not_differentiableAt] at hy
      exact bin hy
      exact not_differentiableAt_norm_zero E
    refine ⟨(1 / ‖y‖) • y, norm_normalize yn,
      (differentiableAt_norm_smul (one_div_ne_zero (norm_ne_zero_iff.2 yn))).1 dy, ?_⟩
    rw [fderiv_norm_smul_pos, hy]
    exact one_div_pos.2 <| norm_pos_iff.2 yn
  choose y ny dy hy using hb
  let c := (b.dualBasis).map (Module.evalEquiv ℝ E).symm
  have mdr i j : b i (c j) = if i = j then 1 else 0 := by
    calc
      (b i) (c j)
        = Module.evalEquiv ℝ E ((Module.evalEquiv ℝ E).symm (b.dualBasis j)) (b i) := rfl
      _ = b.dualBasis j (b i) := by
        rw [(Module.evalEquiv ℝ E).apply_symm_apply]
      _ = if i = j then 1 else 0 := b.dualBasis_apply_self j i
  let T : F →L[ℝ] E :=
    { toFun := fun z ↦ ∑ i, (f (y i) z) • (c i)
      map_add' := by
        intro z w
        simp_rw [map_add, add_smul]
        rw [Finset.sum_add_distrib]
      map_smul' := by
        intro m z
        simp_rw [_root_.map_smul, smul_eq_mul, ← smul_smul]
        rw [← Finset.smul_sum]
        rfl
      cont := continuous_finset_sum (@Finset.univ (Fin n) _) fun _ ↦ by fun_prop }
  use T
  have Tφ x : T (φ x) = x := by
    have this i : LipschitzWith 1 ((f (y i)) ∘ φ) := by
      convert (f (y i)).lipschitz.comp hφ.lipschitz
      rw [← norm_toNNReal, nf _ (ny i), mul_one, toNNReal_one]
    have aux1 i x : f (y i) (φ x) = fderiv ℝ (‖·‖) (y i) x :=
      congrFun (unique1 (ny i) (dy i) ((f (y i)) ∘ φ) (this i) (hf _ (ny i))) x
    have aux2 i x : f (y i) (φ x) = b i x := by
      rw [aux1]
      exact (LinearMap.congr_fun (hy i) x).symm
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, aux2, T]
    let g : E →ₗ[ℝ] E :=
      { toFun := fun y ↦ ∑ i, (b i y) • (c i)
        map_add' := by
          intro y z
          simp_rw [map_add, add_smul]
          rw [Finset.sum_add_distrib]
        map_smul' := by
          intro m y
          simp_rw [_root_.map_smul, smul_eq_mul, ← smul_smul]
          rw [← Finset.smul_sum]
          rfl }
    have : g = LinearMap.id := by
      apply c.ext
      intro i
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe, id_eq, g]
      simp_rw [mdr, ite_smul, one_smul, zero_smul]
      rw [Fintype.sum_ite_eq']
    exact LinearMap.congr_fun this x
  constructor
  · apply le_antisymm
    · have prim : ∀ x : E, ‖x‖ = 1 → DifferentiableAt ℝ (‖·‖) x → f x = (fderiv ℝ (‖·‖) x) ∘ T := by
        intro x nx dx
        apply Continuous.ext_on hlol
        · exact (f x).continuous
        · exact (ContinuousLinearMap.continuous _).comp T.continuous
        · intro y hy
          change f x y = ((fderiv ℝ (‖·‖) x).comp T) y
          apply LinearMap.eqOn_span (R := ℝ) _ hy
          rintro - ⟨z, rfl⟩
          have : LipschitzWith 1 ((f x) ∘ φ) := by
            convert (f x).lipschitz.comp hφ.lipschitz
            rw [← norm_toNNReal, nf x nx, mul_one, toNNReal_one]
          have aux1 := unique1 nx dx ((f x) ∘ φ) this (hf x nx)
          simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
          rw [Tφ]
          exact congrFun aux1 z
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro y
      obtain ⟨u, hu, htu⟩ := dense_seq aux2 (T y)
      have := tendsto_differentiable hu htu
      have unez n : u n ≠ 0 := by
        intro h
        have := h ▸ hu n
        exact not_differentiableAt_norm_zero E this
      have obv n : 1 / ‖u n‖ > 0 := one_div_pos.2 <| norm_pos_iff.2 <| unez n
      have mdr n : fderiv ℝ (‖·‖) (u n) = fderiv ℝ (‖·‖) ((1 / ‖u n‖) • (u n)) :=
        (fderiv_norm_smul_pos (obv n)).symm
      simp_rw [mdr] at this
      apply le_of_tendsto this
      apply eventually_of_forall
      intro n
      have : fderiv ℝ (‖·‖) ((1 / ‖u n‖) • (u n)) (T y) = f ((1 / ‖u n‖) • (u n)) y := by
        have putain : DifferentiableAt ℝ (‖·‖) ((1 / ‖u n‖) • (u n)) :=
          (differentiableAt_norm_smul (obv n).ne.symm).1 (hu n)
        exact congrFun (prim _ (norm_normalize (unez n)) putain).symm y
      rw [this]
      calc
        f ((1 / ‖u n‖) • (u n)) y ≤ ‖f ((1 / ‖u n‖) • (u n)) y‖ := by
          rw [norm_eq_abs]
          exact le_abs_self _
        _ ≤ ‖f ((1 / ‖u n‖) • (u n))‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ y
        _ = 1 * ‖y‖ := by rw [nf _ (norm_normalize (unez n))]
    · have nφ := hφ.norm_map_of_map_zero φz
      rcases NormedSpace.exists_lt_norm ℝ E 0 with ⟨x, hx⟩
      apply le_of_mul_le_mul_right _ hx
      nth_rw 1 [← Tφ x]
      rw [← nφ x, one_mul]
      exact T.le_opNorm _
  · ext x
    exact Tφ x

theorem isup_fin :
    univ = ⋃ (F : Submodule ℝ E) (_ : FiniteDimensional ℝ F), (F : Set E) := by
  ext x
  simp only [mem_univ, mem_iUnion, SetLike.mem_coe, exists_prop, true_iff]
  refine ⟨span ℝ {x}, ?_, ?_⟩
  · exact Finite.span_singleton ℝ x
  apply subset_span
  exact mem_singleton _

theorem Dense.denseInducing_val {X : Type*} [TopologicalSpace X] {s : Set X} (hs : Dense s) :
    DenseInducing (@Subtype.val X s) := ⟨inducing_subtype_val, hs.denseRange_val⟩

theorem uniformInducing_val {X : Type*} [UniformSpace X] (s : Set X) :
    UniformInducing (@Subtype.val X s) := ⟨uniformity_setCoe⟩

theorem exists_inverse'' [CompleteSpace E]
    (φ : E → F) (hφ : Isometry φ) (φz : φ 0 = 0)
    (hlol : Dense (X := F) (Submodule.span ℝ (range φ))) :
    ∃ (f : F →L[ℝ] E), ‖f‖ = 1 ∧ f ∘ φ = id := by
  let A : Submodule ℝ E → Submodule ℝ F := fun p ↦ span ℝ (φ '' p)
  have mA : Monotone A := fun p q hpq ↦ span_mono (image_mono hpq)
  let ψ : (p : Submodule ℝ E) → p → A p := fun p x ↦ ⟨φ x, subset_span ⟨x.1, x.2, rfl⟩⟩
  have hψ p : Isometry (ψ p) := sorry
  have ψz p : ψ p 0 = 0 := sorry
  have fini (p : Submodule ℝ E) (hp : FiniteDimensional ℝ p) :
      ∃ T : A p →L[ℝ] p, ‖T‖ = 1 ∧ ∀ y : p, T (ψ p y) = y := by
    have : Dense (X := A p) (span ℝ (range (ψ p))) := by sorry
    have _ : Nontrivial p := sorry
    rcases exists_inverse' (n := finrank ℝ (p →ₗ[ℝ] ℝ)) rfl (ψ p) (hψ p) (ψz p) this with ⟨T, nT, hT⟩
    use T, nT
    exact fun y ↦ congrFun hT y
  choose! T nT hT using fini
  have eq {p q : Submodule ℝ E} (hp : FiniteDimensional ℝ p) (hq : FiniteDimensional ℝ q)
      (hpq : p ≤ q) :
      ∀ y : A p, (T p y).1 =
        (T q (Submodule.inclusion (mA hpq) y)).1 := by sorry
  let Q : Set F := ⋃ (p : Submodule ℝ E) (_ : FiniteDimensional ℝ p), A p
  let g : span ℝ Q → E := fun y ↦
    let n := (mem_span_set'.1 y.2).choose
    let c : Fin n → ℝ := (mem_span_set'.1 y.2).choose_spec.choose
    let x : Fin n → Q := (mem_span_set'.1 y.2).choose_spec.choose_spec.choose
    let p := fun i ↦ (mem_iUnion₂.1 (x i).2).choose
    have hx := fun i ↦ (mem_iUnion₂.1 (x i).2).choose_spec.choose_spec
    ∑ i : Fin n, c i • (T (p i) ⟨(x i).1, hx i⟩)
  have Ale (p : Submodule ℝ E) (hp : FiniteDimensional ℝ p) : A p ≤ span ℝ Q := by
    refine subset_trans ?_ subset_span
    apply subset_iUnion₂ (s := fun q hq ↦ (A q : Set F)) p hp
  let Ainc (p : Submodule ℝ E) (hp : FiniteDimensional ℝ p) : A p → span ℝ Q :=
    Submodule.inclusion (Ale p hp)
  have Teg (p : Submodule ℝ E) (hp : FiniteDimensional ℝ p) (x : span ℝ Q)
      (hx : x.1 ∈ A p) : (T p ⟨x, hx⟩).1 = g x := by
    let nx := (mem_span_set'.1 x.2).choose
    let cx : Fin nx → ℝ := (mem_span_set'.1 x.2).choose_spec.choose
    let xx : Fin nx → Q := (mem_span_set'.1 x.2).choose_spec.choose_spec.choose
    have xe : ∑ i, cx i • (xx i).1 = x :=
      (mem_span_set'.1 x.2).choose_spec.choose_spec.choose_spec
    let px := fun i ↦ (mem_iUnion₂.1 (xx i).2).choose
    have hpx i : FiniteDimensional ℝ (px i) := (mem_iUnion₂.1 (xx i).2).choose_spec.choose
    have hxx : ∀ i, (xx i).1 ∈ A (px i) :=
      fun i ↦ (mem_iUnion₂.1 (xx i).2).choose_spec.choose_spec
    change (T p ⟨x, hx⟩).1 = ∑ i, cx i • (T (px i) ⟨(xx i).1, hxx i⟩).1
    have this i : px i ≤ p ⊔ ⨆ j, px j := by
      apply le_sup_of_le_right
      apply le_iSup _ i
    simp_rw [fun i ↦ eq (hpx i) _ (this i) ⟨(xx i), hxx i⟩]
    rw [eq hp inferInstance (le_sup_left (b := ⨆ j, px j)) ⟨x, hx⟩]
    simp_rw [← coe_smul, ← Submodule.coe_sum, ← _root_.map_smul, ← map_sum]
    congr
    rw [← Subtype.val_inj]
    simp_rw [Submodule.coe_sum, Submodule.coe_inclusion, coe_smul]
    rw [xe]
  have imp {n : ℕ} {p : Fin n → Submodule ℝ E} {x : Fin n → Q} (hx : ∀ i, (x i).1 ∈ A (p i)) i :
      (x i).1 ∈ A (⨆ i, p i) := by
    have : ⨆ i, A (p i) ≤ A (⨆ i, p i) := by
      simp only [A]
      rw [iSup_span, ← image_iUnion]
      apply span_mono
      apply image_mono
      simp only [iUnion_subset_iff, SetLike.coe_subset_coe]
      exact fun i ↦ le_iSup p i
    apply this
    apply le_iSup (A ∘ p) i
    exact hx i
  have imp (x : span ℝ Q) : ∃ (p : Submodule ℝ E) (hp : FiniteDimensional ℝ p), x.1 ∈ A p := by
    let nx := (mem_span_set'.1 x.2).choose
    let cx : Fin nx → ℝ := (mem_span_set'.1 x.2).choose_spec.choose
    let xx : Fin nx → Q := (mem_span_set'.1 x.2).choose_spec.choose_spec.choose
    have xe : ∑ i, cx i • (xx i).1 = x :=
      (mem_span_set'.1 x.2).choose_spec.choose_spec.choose_spec
    let px := fun i ↦ (mem_iUnion₂.1 (xx i).2).choose
    have hpx i : FiniteDimensional ℝ (px i) := (mem_iUnion₂.1 (xx i).2).choose_spec.choose
    have hxx : ∀ i, (xx i).1 ∈ A (px i) :=
      fun i ↦ (mem_iUnion₂.1 (xx i).2).choose_spec.choose_spec
    use ⨆ i, px i, inferInstance
    rw [← xe]
    convert (∑ i, cx i • (⟨(xx i).1, imp hxx i⟩ : ( A (⨆ i, (px i)) : Submodule ℝ F))).2
    simp_rw [Submodule.coe_sum, coe_smul]
  have gadd x y : g (x + y) = g x + g y := by
    rcases imp x with ⟨p, hp, hx⟩
    rcases imp y with ⟨q, hq, hy⟩
    have : (A p) ⊔ (A q) ≤ A (p ⊔ q) := by
      apply sup_le
      · exact mA le_sup_left
      · exact mA le_sup_right
    have hx : x.1 ∈ A (p ⊔ q) := this <| le_sup_left (b := A q) hx
    have hy : y.1 ∈ A (p ⊔ q) := this <| le_sup_right (a := A p) hy
    have hxy : x.1 + y.1 ∈ A (p ⊔ q) := by
      exact ((⟨x.1, hx⟩ : A (p ⊔ q)) + ⟨y.1, hy⟩).2
    rw [← Teg (p ⊔ q) inferInstance x hx, ← Teg (p ⊔ q) inferInstance y hy,
      ← Teg (p ⊔ q) inferInstance (x + y) hxy, ← coe_add, ← map_add]
    rfl
  have gsmul (c : ℝ) x : g (c • x) = c • (g x) := by
    rcases imp x with ⟨p, hp, hx⟩
    have hcx : c • x.1 ∈ A p := (c • ⟨x.1, hx⟩ : A p).2
    rw [← Teg p hp x hx, ← Teg p hp (c • x) hcx, ← coe_smul, ← _root_.map_smul]
    rfl
  have ng x : ‖g x‖ ≤ 1 * ‖x‖ := by
    rcases imp x with ⟨p, hp, hx⟩
    rw [← Teg p hp x hx, norm_coe, ← nT p hp]
    apply (T p).le_opNorm

  have dQ : Dense (span ℝ Q : Set F) := by
    simp only [Q, A]
    rw [span_iUnion₂]
    simp_rw [span_span]
    rw [← span_iUnion₂, ← image_iUnion₂, ← isup_fin, image_univ]
    exact hlol
  have dQ := dQ.denseRange_val
  have ui := uniformInducing_val (span ℝ Q : Set F)
  have cg : UniformContinuous g := sorry
  let h := (ui.denseInducing dQ).extend g
  have ch : Continuous h :=
    (ui.denseInducing dQ).continuous_extend (uniformly_extend_exists ui dQ cg)
  have merde : ∀ x : F, ∃ u : ℕ → span ℝ Q, Tendsto (Subtype.val ∘ u) atTop (𝓝 x) := by
    intro x
    rcases dense_seq dQ x with ⟨u, hu1, hu2⟩
    let v : ℕ → span ℝ Q := fun n ↦ (hu1 n).choose
    have : u = Subtype.val ∘ v := by
      ext n
      simp only [SetLike.coe_sort_coe, Function.comp_apply, v]
      exact (hu1 n).choose_spec.symm
    use v
    rwa [← this]
  have hadd x y : h (x + y) = h x + h y := by
    rcases merde x with ⟨ux, hux⟩
    rcases merde y with ⟨uy, huy⟩
    have ptn1 : Tendsto (fun n ↦ g (ux n) + g (uy n)) atTop (𝓝 (h x + h y)) := by
      apply Tendsto.add
      · apply ((ch.tendsto x).comp hux).congr
        exact fun n ↦ (ui.denseInducing dQ).extend_eq cg.continuous (ux n)
      · apply ((ch.tendsto y).comp huy).congr
        exact fun n ↦ (ui.denseInducing dQ).extend_eq cg.continuous (uy n)
    have ptn2 : Tendsto (fun n ↦ g (ux n) + g (uy n)) atTop (𝓝 (h (x + y))) := by
      simp_rw [← gadd]
      apply ((ch.tendsto _).comp (hux.add huy)).congr
      exact fun n ↦ (ui.denseInducing dQ).extend_eq cg.continuous (ux n + uy n)
    exact tendsto_nhds_unique ptn2 ptn1
  have hsmul (c : ℝ) x : h (c • x) = c • (h x) := by
    rcases merde x with ⟨ux, hux⟩
    have ptn1 : Tendsto (fun n ↦ c • (g (ux n))) atTop (𝓝 (h (c • x))) := by
      simp_rw [← gsmul]
      apply ((ch.tendsto _).comp (hux.const_smul c)).congr
      exact fun n ↦ (ui.denseInducing dQ).extend_eq cg.continuous (c • (ux n))
    have ptn2 : Tendsto (fun n ↦ c • (g (ux n))) atTop (𝓝 (c • (h x))) := by
      apply Tendsto.const_smul
      apply ((ch.tendsto x).comp hux).congr
      exact fun n ↦ (ui.denseInducing dQ).extend_eq cg.continuous (ux n)
    exact tendsto_nhds_unique ptn1 ptn2
  have hnorm x : ‖h x‖ ≤ 1 * ‖x‖ := by
    rcases merde x with ⟨ux, hux⟩
    have ptn1 : Tendsto (fun n ↦ ‖g (ux n)‖) atTop (𝓝 (‖h x‖)) := by
      apply ((continuous_norm.tendsto _).comp <| (ch.tendsto x).comp hux).congr
      intro n
      simp only [Function.comp_apply]
      congr
      exact (ui.denseInducing dQ).extend_eq cg.continuous (ux n)
    apply le_of_tendsto_of_tendsto' ptn1 (((continuous_norm.tendsto _).comp hux).const_mul 1)
    exact fun _ ↦ ng _
  let h' : F →ₗ[ℝ] E :=
    { toFun := h
      map_add' := hadd
      map_smul' := hsmul }
  let H := h'.mkContinuous 1 hnorm
  use H
  constructor
  · apply le_antisymm
    · exact H.opNorm_le_bound (by norm_num) hnorm
    · sorry
  · ext x
    have : x ∈ ⋃ (F : Submodule ℝ E) (_ : FiniteDimensional ℝ F), (F : Set E) := by
      rw [← isup_fin]; trivial
    rcases mem_iUnion₂.1 this with ⟨p, hp, hx⟩
    have ptn : φ x ∈ Q := by
      simp only [mem_iUnion, SetLike.mem_coe, exists_prop, Q]
      exact ⟨p, hp, subset_span ⟨x, hx, rfl⟩⟩
    have ob : (T p ⟨φ x, subset_span ⟨x, hx, rfl⟩⟩).1 = g ⟨φ x, subset_span ptn⟩ := by sorry
    have merde : H (φ x) = g ⟨φ x, subset_span ptn⟩ := by
      change h (⟨φ x, subset_span ptn⟩ : span ℝ Q) = g ⟨φ x, subset_span ptn⟩
      exact (ui.denseInducing dQ).extend_eq cg.continuous _
    simp only [Function.comp_apply, id_eq]
    rw [merde, ← ob]
    exact Subtype.val_inj.2 <| hT p hp ⟨x, hx⟩
