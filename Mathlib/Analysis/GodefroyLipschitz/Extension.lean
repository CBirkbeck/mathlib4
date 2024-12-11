import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformEmbedding

open Filter Topology

theorem Dense.isDenseInducing_val {X : Type*} [TopologicalSpace X] {s : Set X} (hs : Dense s) :
    IsDenseInducing (@Subtype.val X s) := ⟨IsInducing.subtypeVal, hs.denseRange_val⟩

theorem isUniformInducing_val {X : Type*} [UniformSpace X] (s : Set X) :
    IsUniformInducing (@Subtype.val X s) := ⟨uniformity_setCoe⟩

variable {𝕜 E F : Type*} [Ring 𝕜] [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]
  [UniformSpace E] [UniformSpace F] [CompleteSpace F] [ContinuousAdd E] [ContinuousAdd F]
  [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F] [T2Space F]
  {f : E →ₗ.[𝕜] F} (hdf : Dense (f.domain : Set E)) (hf : UniformContinuous f)

noncomputable def dense_extend : E →L[𝕜] F :=
  letI g := hdf.isDenseInducing_val.extend f
  haveI cg : Continuous g := uniformContinuous_uniformly_extend (isUniformInducing_val _)
    hdf.denseRange_val hf |>.continuous
  { toFun := hdf.isDenseInducing_val.extend f
    map_add' := fun x y ↦ by
      let e : f.domain → E := Subtype.val
      have h1 : Tendsto (fun x ↦ f x.1 + f x.2)
          (comap (Prod.map e e) (𝓝 (x, y))) (𝓝 (g (x + y))) := by
        simp_rw [← LinearPMap.map_add]
        apply uniformly_extend_tendsto (e := e) (isUniformInducing_val _) hdf.denseRange_val hf
        have : e ∘ (fun x ↦ x.1 + x.2) = (fun x ↦ x.1 + x.2) ∘ (Prod.map e e) := by
          ext x; simp [e]
        rw [this, ← tendsto_map'_iff]
        exact (continuous_add.tendsto (x, y)).mono_left map_comap_le
      have h2 : Tendsto (fun x ↦ f x.1 + f x.2)
          (comap (Prod.map e e) (𝓝 (x, y))) (𝓝 (g x + g y)) := by
        apply Tendsto.add <;>
        change Tendsto (f ∘ _) _ _ <;>
        apply uniformly_extend_tendsto (e := e) (isUniformInducing_val _) hdf.denseRange_val hf
        · have : e ∘ (Prod.fst : f.domain × f.domain → _) = Prod.fst ∘ (Prod.map e e) := by
            ext x; simp
          rw [this, ← tendsto_map'_iff]
          exact (continuous_fst.tendsto (x, y)).mono_left map_comap_le
        · have : e ∘ (Prod.snd : f.domain × f.domain → _) = Prod.snd ∘ (Prod.map e e) := by
            ext x; simp
          rw [this, ← tendsto_map'_iff]
          exact (continuous_snd.tendsto (x, y)).mono_left map_comap_le
      have : (comap (Prod.map e e) (𝓝 (x, y))).NeBot := by
        rw [nhds_prod_eq, comap_prodMap_prod, Filter.prod_neBot]
        constructor <;> rw [← mem_closure_iff_comap_neBot] <;> apply hdf
      exact tendsto_nhds_unique h1 h2
    map_smul' := fun m x ↦ by
      let e : f.domain → E := Subtype.val
      simp only [RingHom.id_apply]
      have h1 : Tendsto (fun x ↦ m • f x) (comap e (𝓝 x)) (𝓝 (g (m • x))) := by
        simp_rw [← LinearPMap.map_smul]
        change Tendsto (f ∘ _) _ _
        apply uniformly_extend_tendsto (e := e) (isUniformInducing_val _) hdf.denseRange_val hf
        have : e ∘ (fun x ↦ m • x) = (fun x ↦ m • x) ∘ e := by
          ext x; simp [e]
        rw [this, ← tendsto_map'_iff]
        exact ((continuous_const_smul m).tendsto x).mono_left map_comap_le
      have h2 : Tendsto (fun x ↦ m • (f x)) (comap e (𝓝 x)) (𝓝 (m • (g x))) :=
        (uniformly_extend_spec (isUniformInducing_val _) hdf.denseRange_val hf x).const_smul m
      have : (comap e (𝓝 x)).NeBot := mem_closure_iff_comap_neBot.1 (hdf x)
      exact tendsto_nhds_unique h1 h2
    cont := cg }

theorem dense_extend_eq (x : f.domain) : dense_extend hdf hf x = f x :=
  hdf.isDenseInducing_val.extend_eq hf.continuous x

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace F]
  {f : E →ₗ.[𝕜] F} (hdf : Dense (f.domain : Set E)) (hf : UniformContinuous f)

theorem norm_dense_extend {C : ℝ} (hC : 0 ≤ C) (hfC : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖dense_extend hdf hf‖ ≤ C := by
  rw [ContinuousLinearMap.opNorm_le_iff hC]
  intro x
  obtain ⟨u, hu, lu⟩ := mem_closure_iff_seq_limit.1 (hdf x)
  have h1 : Tendsto (fun n ↦ ‖f ⟨u n, hu n⟩‖) atTop (𝓝 (‖dense_extend hdf hf x‖)) :=
    (continuous_norm.tendsto _).comp <|
      uniformly_extend_tendsto (isUniformInducing_val _) hdf.denseRange_val hf lu
  have h2 : Tendsto (fun n ↦ C * ‖u n‖) atTop (𝓝 (C * ‖x‖)) :=
    ((continuous_norm.tendsto _).comp lu).const_mul _
  exact le_of_tendsto_of_tendsto' h1 h2 fun n ↦ hfC _
