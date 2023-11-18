/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.Equiv

/-!
# Ascoli Theorem

## Main definitions
## Main statements
## Notation
## Implementation details
## References
## Tags
-/

open Set Filter Uniformity Topology TopologicalSpace Function UniformConvergence

variable {ι X Y α β : Type*} [TopologicalSpace X] [u : UniformSpace α] [UniformSpace β]
variable {F : ι → X → α} {G : ι → β → α}

theorem Equicontinuous.comap_uniformFun_eq [CompactSpace X] (hF : Equicontinuous F) :
    (UniformFun.uniformSpace X α).comap F =
    (Pi.uniformSpace _).comap F := by
  -- The `≤` inequality is trivial
  refine le_antisymm (UniformSpace.comap_mono UniformFun.uniformContinuous_toFun) ?_
  -- A bit of rewriting to get a nice intermediate statement.
  change comap _ _ ≤ comap _ _
  simp_rw [Pi.uniformity, Filter.comap_iInf, comap_comap, Function.comp]
  refine ((UniformFun.hasBasis_uniformity X α).comap (Prod.map F F)).ge_iff.mpr ?_
  -- TODO: what are the names used in Bourbaki for the sets?
  -- Core of the proof: we need to show that, for any entourage `U` in `α`,
  -- the set `𝐓(U) := {(i,j) : ι × ι | ∀ x : X, (F i x, F j x) ∈ U}` belongs to the filter
  -- `⨅ x, comap ((i,j) ↦ (F i x, F j x)) (𝓤 α)`.
  -- In other words, we have to show that it contains a finite intersection of
  -- sets of the form `𝐒(V, x) := {(i,j) : ι × ι | (F i x, F j x) ∈ V}` for some
  -- `x : X` and `V ∈ 𝓤 α`.
  intro U hU
  -- We will do an `ε/3` argument, so we start by choosing a symmetric entourage `V ∈ 𝓤 α`
  -- such that `V ○ V ○ V ⊆ U`.
  rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, Vsymm, hVU⟩
  -- Set `Ω x := {y | ∀ i, (F i x, F i y) ∈ V}`. The equicontinuity of `F` guarantees that
  -- each `Ω x` is a neighborhood of `x`.
  let Ω x : Set X := {y | ∀ i, (F i x, F i y) ∈ V}
  -- Hence, by compactness of `X`, we can find some `A ⊆ X` finite such that the `Ω a`s for `a ∈ A`
  -- still cover `X`.
  rcases CompactSpace.elim_nhds_subcover Ω (fun x ↦ hF x V hV) with ⟨A, Acover⟩
  -- We now claim that `⋂ a ∈ A, 𝐒(V, a) ⊆ 𝐓(U)`.
  have : (⋂ a ∈ A, {ij : ι × ι | (F ij.1 a, F ij.2 a) ∈ V}) ⊆
      (Prod.map F F) ⁻¹' UniformFun.gen X α U := by
    -- Given `(i, j) ∈ ⋂ a ∈ A, 𝐒(V, a)` and `x : X`, we have to prove that `(F i x, F j x) ∈ U`.
    rintro ⟨i, j⟩ hij x
    rw [mem_iInter₂] at hij
    -- We know that `x ∈ Ω a` for some `a ∈ A`, so that both `(F i x, F i a)` and `(F j a, F j x)`
    -- are in `V`.
    rcases mem_iUnion₂.mp (Acover.symm.subset <| mem_univ x) with ⟨a, ha, hax⟩
    -- Since `(i, j) ∈ 𝐒(V, a)` we also have `(F i a, F j a) ∈ V`, and finally we get
    -- `(F i x, F j x) ∈ V ○ V ○ V ⊆ U`.
    exact hVU (prod_mk_mem_compRel (prod_mk_mem_compRel
      (Vsymm.mk_mem_comm.mp (hax i)) (hij a ha)) (hax j))
  -- This completes the proof.
  exact mem_of_superset
    (A.iInter_mem_sets.mpr fun x _ ↦ mem_iInf_of_mem x <| preimage_mem_comap hV) this

lemma Equicontinuous.uniformInducing_uniformFun_iff_pi [UniformSpace ι] [CompactSpace X]
    (hF : Equicontinuous F) :
    UniformInducing (UniformFun.ofFun ∘ F) ↔ UniformInducing F := by
  rw [uniformInducing_iff_uniformSpace, uniformInducing_iff_uniformSpace, ← hF.comap_uniformFun_eq]
  rfl

lemma Equicontinuous.inducing_uniformFun_iff_pi [TopologicalSpace ι] [CompactSpace X]
    (hF : Equicontinuous F) :
    Inducing (UniformFun.ofFun ∘ F) ↔ Inducing F := by
  rw [inducing_iff, inducing_iff]
  change (_ = (UniformFun.uniformSpace X α |>.comap F |>.toTopologicalSpace)) ↔
         (_ = (Pi.uniformSpace _ |>.comap F |>.toTopologicalSpace))
  rw [hF.comap_uniformFun_eq]

theorem Equicontinuous.tendsto_uniformFun_iff_pi [CompactSpace X]
    (hF : Equicontinuous F) (ℱ : Filter ι) (f : X → α) :
    Tendsto (UniformFun.ofFun ∘ F) ℱ (𝓝 <| UniformFun.ofFun f) ↔
    Tendsto F ℱ (𝓝 f) := by
  rcases ℱ.eq_or_neBot with rfl | ℱ_ne
  · simp
  constructor <;> intro H
  · exact UniformFun.uniformContinuous_toFun.continuous.tendsto _|>.comp H
  · set S : Set (X → α) := closure (range F)
    set 𝒢 : Filter S := comap (↑) (map F ℱ)
    have hS : S.Equicontinuous := closure' (by rwa [equicontinuous_iff_range] at hF) continuous_id
    have ind : Inducing (UniformFun.ofFun ∘ (↑) : S → X →ᵤ α) :=
      hS.inducing_uniformFun_iff_pi.mpr ⟨rfl⟩
    have f_mem : f ∈ S := mem_closure_of_tendsto H range_mem_map
    have h𝒢ℱ : map (↑) 𝒢 = map F ℱ := Filter.map_comap_of_mem
      (Subtype.range_coe ▸ mem_of_superset range_mem_map subset_closure)
    have H' : Tendsto id 𝒢 (𝓝 ⟨f, f_mem⟩) := by
      rwa [tendsto_id', nhds_induced, ← map_le_iff_le_comap, h𝒢ℱ]
    rwa [ind.tendsto_nhds_iff, comp.right_id, ← tendsto_map'_iff, h𝒢ℱ] at H'

theorem Equicontinuous.comap_uniformOnFun_eq {𝔖 : Set (Set X)} (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F)) :
    (UniformOnFun.uniformSpace X α 𝔖).comap F =
    (Pi.uniformSpace _).comap ((⋃₀ 𝔖).restrict ∘ F) := by
  -- Recall that the uniform structure on `X →ᵤ[𝔖] α` is the one induced by all the maps
  -- `K.restrict : (X →ᵤ[𝔖] α) → (K →ᵤ α)` for `K ∈ 𝔖`. Its pullback along `F`, which is
  -- the LHS of our goal, is thus the uniform structure induced by the maps
  -- `K.restrict ∘ F : ι → (K →ᵤ α)` for `K ∈ 𝔖`.
  have H1 : (UniformOnFun.uniformSpace X α 𝔖).comap F =
      ⨅ (K ∈ 𝔖), (UniformFun.uniformSpace _ _).comap (K.restrict ∘ F) := by
    simp_rw [UniformOnFun.uniformSpace, UniformSpace.comap_iInf, UniformSpace.comap_comap]
  -- Now, note that a similar fact is true for the uniform structure on `X → α` induced by
  -- the map `(⋃₀ 𝔖).restrict : (X → α) → ((⋃₀ 𝔖) → α)`: it is equal to the one induced by
  -- all maps `K.restrict : (X → α) → (K → α)` for `K ∈ 𝔖`, which means that the RHS of our
  -- goal is the uniform structure induced by the maps `K.restrict ∘ F : ι → (K → α)` for `K ∈ 𝔖`.
  have H2 : (Pi.uniformSpace _).comap ((⋃₀ 𝔖).restrict ∘ F) =
      ⨅ (K ∈ 𝔖), (Pi.uniformSpace _).comap (K.restrict ∘ F) := by
    simp_rw [UniformSpace.comap_comap, Pi.uniformSpace_comap_restrict_sUnion (fun _ ↦ α) 𝔖,
      UniformSpace.comap_iInf]
  -- But, for `K ∈ 𝔖` fixed, we know that the uniform structures of `K →ᵤ α` and `K → α`
  -- induce, via the equicontinuous family `K.restrict ∘ F`, the same uniform structure on `ι`.
  have H3 : ∀ K ∈ 𝔖, (UniformFun.uniformSpace K α).comap (K.restrict ∘ F) =
      (Pi.uniformSpace _).comap (K.restrict ∘ F) := fun K hK ↦ by
    have : CompactSpace K := isCompact_iff_compactSpace.mp (h𝔖 K hK)
    exact (hF K hK).comap_uniformFun_eq
  -- Combining these three facts completes the proof.
  simp_rw [H1, H2, iInf_congr fun K ↦ iInf_congr fun hK ↦ H3 K hK]

lemma Equicontinuous.uniformInducing_uniformOnFun_iff_pi' [UniformSpace ι]
    {𝔖 : Set (Set X)} (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F)) :
    UniformInducing (UniformOnFun.ofFun 𝔖 ∘ F) ↔
    UniformInducing ((⋃₀ 𝔖).restrict ∘ F) := by
  rw [uniformInducing_iff_uniformSpace, uniformInducing_iff_uniformSpace,
      ← Equicontinuous.comap_uniformOnFun_eq h𝔖 hF]
  rfl

lemma Equicontinuous.uniformInducing_uniformOnFun_iff_pi [UniformSpace ι]
    {𝔖 : Set (Set X)} (𝔖_covers : ⋃₀ 𝔖 = univ) (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous ((K.restrict : (X → α) → (K → α)) ∘ F)) :
    UniformInducing (UniformOnFun.ofFun 𝔖 ∘ F) ↔
    UniformInducing F := by
  rw [eq_univ_iff_forall] at 𝔖_covers
  let φ : ((⋃₀ 𝔖) → α) ≃ᵤ (X → α) := UniformEquiv.piCongrLeft (β := fun _ ↦ α)
    (Equiv.subtypeUnivEquiv 𝔖_covers)
  rw [Equicontinuous.uniformInducing_uniformOnFun_iff_pi' h𝔖 hF,
      show restrict (⋃₀ 𝔖) ∘ F = φ.symm ∘ F by rfl]
  exact ⟨fun H ↦ φ.uniformInducing.comp H, fun H ↦ φ.symm.uniformInducing.comp H⟩

lemma Equicontinuous.inducing_uniformOnFun_iff_pi' [TopologicalSpace ι]
    {𝔖 : Set (Set X)} (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F)) :
    Inducing (UniformOnFun.ofFun 𝔖 ∘ F) ↔
    Inducing ((⋃₀ 𝔖).restrict ∘ F) := by
  rw [inducing_iff, inducing_iff]
  change (_ = ((UniformOnFun.uniformSpace X α 𝔖).comap F).toTopologicalSpace) ↔
    (_ = ((Pi.uniformSpace _).comap ((⋃₀ 𝔖).restrict ∘ F)).toTopologicalSpace)
  rw [← Equicontinuous.comap_uniformOnFun_eq h𝔖 hF]

lemma Equicontinuous.inducing_uniformOnFun_iff_pi [TopologicalSpace ι]
    {𝔖 : Set (Set X)} (𝔖_covers : ⋃₀ 𝔖 = univ) (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F)) :
    Inducing (UniformOnFun.ofFun 𝔖 ∘ F) ↔
    Inducing F := by
  rw [eq_univ_iff_forall] at 𝔖_covers
  let φ : ((⋃₀ 𝔖) → α) ≃ₜ (X → α) := Homeomorph.piCongrLeft (Y := fun _ ↦ α)
    (Equiv.subtypeUnivEquiv 𝔖_covers)
  rw [Equicontinuous.inducing_uniformOnFun_iff_pi' h𝔖 hF,
      show restrict (⋃₀ 𝔖) ∘ F = φ.symm ∘ F by rfl]
  exact ⟨fun H ↦ φ.inducing.comp H, fun H ↦ φ.symm.inducing.comp H⟩

-- TODO: find a way to factor common elements of this proof and the proof of
-- `Equicontinuous.comap_uniformOnFun_eq`
theorem Equicontinuous.tendsto_uniformOnFun_iff_pi'
    {𝔖 : Set (Set X)} (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F)) (ℱ : Filter ι) (f : X → α) :
    Tendsto (UniformOnFun.ofFun 𝔖 ∘ F) ℱ (𝓝 <| UniformOnFun.ofFun 𝔖 f) ↔
    Tendsto ((⋃₀ 𝔖).restrict ∘ F) ℱ (𝓝 <| (⋃₀ 𝔖).restrict f) := by
  rw [← Filter.tendsto_comap_iff (g := (⋃₀ 𝔖).restrict), ← nhds_induced]
  simp_rw [UniformOnFun.topologicalSpace_eq, Pi.induced_restrict_sUnion 𝔖 (π := fun _ ↦ α),
    nhds_iInf, nhds_induced, tendsto_iInf, tendsto_comap_iff]
  congrm ∀ K (hK : K ∈ 𝔖), ?_
  have : CompactSpace K := isCompact_iff_compactSpace.mp (h𝔖 K hK)
  rw [← (hF K hK).tendsto_uniformFun_iff_pi]
  rfl

theorem Equicontinuous.tendsto_uniformOnFun_iff_pi
    {𝔖 : Set (Set X)} (h𝔖 : ∀ K ∈ 𝔖, IsCompact K) (𝔖_covers : ⋃₀ 𝔖 = univ)
    (hF : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F)) (ℱ : Filter ι) (f : X → α) :
    Tendsto (UniformOnFun.ofFun 𝔖 ∘ F) ℱ (𝓝 <| UniformOnFun.ofFun 𝔖 f) ↔
    Tendsto F ℱ (𝓝 f) := by
  rw [eq_univ_iff_forall] at 𝔖_covers
  let φ : ((⋃₀ 𝔖) → α) ≃ₜ (X → α) := Homeomorph.piCongrLeft (Y := fun _ ↦ α)
    (Equiv.subtypeUnivEquiv 𝔖_covers)
  rw [Equicontinuous.tendsto_uniformOnFun_iff_pi' h𝔖 hF,
      show restrict (⋃₀ 𝔖) ∘ F = φ.symm ∘ F by rfl, show restrict (⋃₀ 𝔖) f = φ.symm f by rfl,
      φ.symm.inducing.tendsto_nhds_iff]

theorem Equicontinuous.isClosed_range_pi_of_uniformOnFun'
    {𝔖 : Set (Set X)} (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F))
    (H : IsClosed (range <| UniformOnFun.ofFun 𝔖 ∘ F)) :
    IsClosed (range <| (⋃₀ 𝔖).restrict ∘ F) := by
  -- Do we have no equivalent of `nontriviality`?
  rcases isEmpty_or_nonempty α with _ | _
  · simp [isClosed_discrete]
  simp_rw [isClosed_iff_clusterPt, ← Filter.map_top, ← mapClusterPt_def,
    mapClusterPt_iff_ultrafilter, range_comp, Subtype.coe_injective.surjective_comp_right.forall,
    ← restrict_eq, ← Equicontinuous.tendsto_uniformOnFun_iff_pi' h𝔖 hF]
  exact fun f ⟨u, _, hu⟩ ↦ mem_image_of_mem _ <| H.mem_of_tendsto hu <|
    eventually_of_forall mem_range_self

theorem Equicontinuous.isClosed_range_uniformOnFun_iff_pi
    {𝔖 : Set (Set X)} (h𝔖 : ∀ K ∈ 𝔖, IsCompact K) (𝔖_covers : ⋃₀ 𝔖 = univ)
    (hF : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F)) :
    IsClosed (range <| UniformOnFun.ofFun 𝔖 ∘ F) ↔
    IsClosed (range F) := by
  simp_rw [isClosed_iff_clusterPt, ← Filter.map_top, ← mapClusterPt_def,
    mapClusterPt_iff_ultrafilter, range_comp, (UniformOnFun.ofFun 𝔖).surjective.forall,
    ← Equicontinuous.tendsto_uniformOnFun_iff_pi h𝔖 𝔖_covers hF,
    (UniformOnFun.ofFun 𝔖).injective.mem_set_image]

alias ⟨Equicontinuous.isClosed_range_pi_of_uniformOnFun, _⟩ :=
  Equicontinuous.isClosed_range_uniformOnFun_iff_pi

theorem ArzelaAscoli.compactSpace_of_closed_inducing' [TopologicalSpace ι] {𝔖 : Set (Set X)}
    (h𝔖 : ∀ K ∈ 𝔖, IsCompact K) (F_ind : Inducing (UniformOnFun.ofFun 𝔖 ∘ F))
    (F_cl : IsClosed <| range <| (⋃₀ 𝔖).restrict ∘ F)
    (F_eqcont : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F))
    (F_pointwiseCompact : ∀ K ∈ 𝔖, ∀ x ∈ K, ∃ Q, IsCompact Q ∧ ∀ i, F i x ∈ Q) :
    CompactSpace ι := by
  have : Inducing (restrict (⋃₀ 𝔖) ∘ F) := by
    rwa [Equicontinuous.inducing_uniformOnFun_iff_pi' h𝔖 F_eqcont] at F_ind
  rw [← forall_sUnion] at F_pointwiseCompact
  choose! Q Q_compact F_in_Q using F_pointwiseCompact
  rw [← isCompact_univ_iff, this.isCompact_iff, image_univ]
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun x ↦ Q_compact x x.2) F_cl
    (range_subset_iff.mpr fun i x _ ↦ F_in_Q x x.2 i)

theorem ArzelaAscoli.compactSpace_of_closed_inducing [TopologicalSpace ι] {𝔖 : Set (Set X)}
    (𝔖_compact : ∀ K ∈ 𝔖, IsCompact K) (𝔖_covers : ⋃₀ 𝔖 = univ)
    (F_ind : Inducing (UniformOnFun.ofFun 𝔖 ∘ F))
    (F_cl : IsClosed (range F))
    (F_eqcont : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F))
    (F_pointwiseCompact : ∀ x, ∃ K, IsCompact K ∧ ∀ i, F i x ∈ K) :
    CompactSpace ι := by
  have : Inducing F := by
    rwa [Equicontinuous.inducing_uniformOnFun_iff_pi 𝔖_covers 𝔖_compact F_eqcont] at F_ind
  choose K K_compact F_in_K using F_pointwiseCompact
  rw [← isCompact_univ_iff, this.isCompact_iff, image_univ]
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun x ↦ K_compact x) F_cl
    (range_subset_iff.mpr fun i x _ ↦ F_in_K x i)

theorem ArzelaAscoli.compactSpace_of_closedEmbedding [TopologicalSpace ι] {𝔖 : Set (Set X)}
    (𝔖_compact : ∀ K ∈ 𝔖, IsCompact K) (F_clemb : ClosedEmbedding (UniformOnFun.ofFun 𝔖 ∘ F))
    (F_eqcont : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F))
    (F_pointwiseCompact : ∀ K ∈ 𝔖, ∀ x ∈ K, ∃ Q, IsCompact Q ∧ ∀ i, F i x ∈ Q) :
    CompactSpace ι :=
  compactSpace_of_closed_inducing' 𝔖_compact F_clemb.toInducing
    (Equicontinuous.isClosed_range_pi_of_uniformOnFun' 𝔖_compact F_eqcont F_clemb.closed_range)
    F_eqcont F_pointwiseCompact

theorem ArzelaAscoli.isCompact_closure_of_closedEmbedding [TopologicalSpace ι] [T2Space α]
    {𝔖 : Set (Set X)} (𝔖_compact : ∀ K ∈ 𝔖, IsCompact K)
    (F_clemb : ClosedEmbedding (UniformOnFun.ofFun 𝔖 ∘ F))
    {s : Set ι} (s_eqcont : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F ∘ ((↑) : s → ι)))
    (s_pointwiseCompact : ∀ K ∈ 𝔖, ∀ x ∈ K, ∃ Q, IsCompact Q ∧ ∀ i ∈ s, F i x ∈ Q) :
    IsCompact (closure s) := by
  rw [isCompact_iff_compactSpace]
  have : ∀ K ∈ 𝔖, ∀ x ∈ K, Continuous (eval x ∘ F) := fun K hK x hx ↦
    UniformOnFun.uniformContinuous_eval_of_mem _ _ hx hK |>.continuous.comp F_clemb.continuous
  have cls_eqcont : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F ∘ ((↑) : closure s → ι)) :=
    fun K hK ↦ (s_eqcont K hK).closure' <| show Continuous (K.restrict ∘ F) from
      continuous_pi fun ⟨x, hx⟩ ↦ this K hK x hx
  have cls_pointwiseCompact : ∀ K ∈ 𝔖, ∀ x ∈ K, ∃ Q, IsCompact Q ∧ ∀ i ∈ closure s, F i x ∈ Q :=
    fun K hK x hx ↦ (s_pointwiseCompact K hK x hx).imp fun Q hQ ↦ ⟨hQ.1, closure_minimal hQ.2 <|
      hQ.1.isClosed.preimage (this K hK x hx)⟩
  exact ArzelaAscoli.compactSpace_of_closedEmbedding 𝔖_compact
    (F_clemb.comp isClosed_closure.closedEmbedding_subtype_val) cls_eqcont
    fun K hK x hx ↦ (cls_pointwiseCompact K hK x hx).imp fun Q hQ ↦ ⟨hQ.1, by simpa using hQ.2⟩

---------------------------------------------------------------------------------------------------

-- Specialize ArzelaAscoli to the case 𝔖 = Set.range Set.singleton
theorem ArzelaAscoli.compactSpace_of_closed_inducing_ptwise [TopologicalSpace ι]
    (F_ind : Inducing F)
    (F_cl : IsClosed (range F))
    (F_pointwiseCompact : ∀ x, ∃ K, IsCompact K ∧ ∀ ι, F ι x ∈ K) :
    CompactSpace ι := by
  let 𝔖 : Set (Set X) := Set.range Set.singleton
  have 𝔖_compact : ∀ K ∈ 𝔖, IsCompact K := by
    rintro K ⟨x, rfl⟩
    exact isCompact_singleton
  have 𝔖_covers : ⋃₀ 𝔖 = univ := by
    rw [sUnion_range, Set.eq_univ_iff_forall]
    exact fun x ↦ mem_iUnion_of_mem x rfl
  have F_ind : Inducing (UniformOnFun.ofFun 𝔖 ∘ F) := by
    refine' (Homeomorph.mk (UniformOnFun.ofFun 𝔖) _
      (UniformOnFun.uniformContinuous_toFun 𝔖_covers).continuous).inducing.comp F_ind
    rw [continuous_iff_continuousAt]
    intro f
    rw [ContinuousAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn]
    rintro x ⟨x, rfl⟩
    rw [Set.singleton, setOf_eq_eq_singleton, tendstoUniformlyOn_singleton_iff_tendsto]
    exact (continuous_apply x).tendsto f
  have F_eqcont : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F) := by
    rintro K ⟨x, rfl⟩
    rw [equicontinuous_iff_continuous]
    exact continuous_of_discreteTopology
  exact ArzelaAscoli.compactSpace_of_closed_inducing 𝔖_compact 𝔖_covers F_ind F_cl F_eqcont F_pointwiseCompact

theorem ArzelaAscoli.ofEquicontinuous {X Y : Type*} [TopologicalSpace X] [UniformSpace Y] [CompactSpace Y]
    (S : Set C(X, Y)) (hS1 : IsClosed (ContinuousMap.toFun '' S))
    (hS2 : Equicontinuous ((↑) : S → X → Y)) :
    IsCompact S := by
  refine' isCompact_iff_compactSpace.mpr (ArzelaAscoli.compactSpace_of_closed_inducing_ptwise _
      (image_eq_range ContinuousMap.toFun S ▸ hS1) (fun x ↦ ⟨Set.univ, isCompact_univ, fun _ ↦ trivial⟩))
  change Inducing (ContinuousMap.toFun ∘ Subtype.val : S → X → Y)

  -- At this point, we need to know that S → X → Y is inducing

  rw [inducing_iff_nhds]
  rintro ⟨ϕ, hϕ⟩
  apply le_antisymm
  · rw [←Filter.map_le_iff_le_comap]
    exact (ContinuousMap.continuous_coe.comp continuous_subtype_val).continuousAt
  · rw [inducing_subtype_val.nhds_eq_comap ⟨ϕ, hϕ⟩, ← Filter.map_le_iff_le_comap]
    conv_rhs => rw [TopologicalSpace.nhds_generateFrom]
    simp only [le_iInf_iff]
    rintro - ⟨hg, K, hK, U, hU, rfl⟩
    have key : ∃ V ∈ uniformity Y, ∀ x ∈ K, ∀ y : Y, (ϕ x, y) ∈ V → y ∈ U
    · obtain ⟨V, hV, hV'⟩ := Disjoint.exists_uniform_thickening (hK.image ϕ.2) hU.isClosed_compl
        (disjoint_compl_right_iff.mpr hg)
      refine' ⟨V, hV, _⟩
      intro x hx y hy
      contrapose! hV'
      rw [Set.not_disjoint_iff]
      refine' ⟨y, _, _⟩
      · simp only [Set.mem_iUnion]
        refine' ⟨ϕ x, ⟨x, hx, rfl⟩, hy⟩
      · simp only [Set.mem_iUnion]
        refine' ⟨y, hV', _⟩
        exact UniformSpace.mem_ball_self y hV
    obtain ⟨V, hV, hVU⟩ := key
    obtain ⟨W₀, hW₀, hW₀V⟩ := comp3_mem_uniformity hV -- three epsilon trick!
    let W := symmetrizeRel W₀
    have hW : W ∈ uniformity Y := symmetrize_mem_uniformity hW₀
    have hWV : compRel W (compRel W W) ⊆ V
    · refine' Set.Subset.trans _ hW₀V
      refine' compRel_mono _ (compRel_mono _ _) <;> exact symmetrizeRel_subset_self W₀
    obtain ⟨t, _, htW⟩ := hK.elim_nhds_subcover
      (fun x => {x' | ∀ ψ : S, ((ψ : X → Y) x, (ψ : X → Y) x') ∈ W})
      (fun x _ => hS2 x W hW)
    intro F hF
    refine' ⟨⋂ x ∈ t, {ψ | (ϕ x, ψ x) ∈ W}, _, _⟩
    · rw [Filter.biInter_finset_mem]
      intro x _
      simp only
      change _ ∈ nhds ϕ.toFun
      let Z : Set Y := {y | (ϕ x, y) ∈ W}
      change {ψ | ψ x ∈ Z} ∈ nhds ϕ.toFun
      have key' := Set.singleton_pi' x (fun _ ↦ Z)
      rw [← key', set_pi_mem_nhds_iff]
      rintro - ⟨-, -⟩
      rw [mem_nhds_uniformity_iff_right]
      refine' Filter.mem_of_superset hW _
      intro a b c
      rwa [← a.eta, c] at b
      exact Set.finite_singleton x
    · rintro ⟨ψ, hψ⟩ h
      apply hF
      rintro - ⟨x, hx, rfl⟩
      refine' hVU x hx (ψ x) _
      specialize htW hx
      simp only [Set.mem_iUnion] at htW
      obtain ⟨x', hx', h'⟩ := htW
      have h1 := h' ⟨ϕ, hϕ⟩
      have h2 := h' ⟨ψ, hψ⟩
      simp only at h1 h2
      simp only [Set.mem_preimage, Set.mem_iInter] at h
      specialize h x' hx'
      change (ϕ x', ψ x') ∈ W at h
      apply hWV
      refine' ⟨ϕ x', _, ψ x', h, h2⟩
      exact (symmetric_symmetrizeRel W₀).mk_mem_comm.mp h1
