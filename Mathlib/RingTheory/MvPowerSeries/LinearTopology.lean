/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Data.Finsupp.Interval
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Nonarchimedean.Bases
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-! # Linear topology on the ring of multivariate power series

- `MvPowerSeries.basis`: the ideals of the ring of multivariate power series
all coefficients the exponent of which is smaller than some bound vanish.

## Instances :

- `MvPowerSeries.isLinearTopology` : if `α` has a linear topology,
then the product topology on `MvPowerSeries σ α` is a linear topology.
This applies in particular when `α` has a discrete topology.

-/

namespace MvPowerSeries

namespace LinearTopology

open scoped Topology

open Set SetLike

/-- The underlying family for the basis of ideals in a multivariate power series ring. -/
def basis (σ : Type*) (α : Type*) [Ring α] (Jd : TwoSidedIdeal α × (σ →₀ ℕ)) :
    TwoSidedIdeal (MvPowerSeries σ α) := by
  apply TwoSidedIdeal.mk' {f | ∀ e ≤ Jd.2, coeff α e f ∈ Jd.1}
  · simp [coeff_zero]
  · exact fun hf hg e he ↦ by rw [map_add]; exact add_mem (hf e he) (hg e he)
  · exact fun {f} hf e he ↦ by simp only [map_neg, neg_mem, hf e he]
  · exact fun {f g} hg e he ↦ by
      classical
      rw [coeff_mul]
      apply sum_mem
      rintro uv huv
      apply TwoSidedIdeal.mul_mem_left
      exact hg _ (le_trans (le_iff_exists_add'.mpr
        ⟨uv.fst, (Finset.mem_antidiagonal.mp huv).symm⟩) he)
  · exact fun {f g} hf e he ↦ by
      classical
      rw [coeff_mul]
      apply sum_mem
      rintro uv huv
      apply TwoSidedIdeal.mul_mem_right
      exact hf _ (le_trans (le_iff_exists_add.mpr ⟨uv.2, (Finset.mem_antidiagonal.mp huv).symm⟩) he)

variable {σ : Type*} {α : Type*} [Ring α]

/-- A power series `f` belongs to the twosided ideal `basis σ α ⟨J, d⟩`
if and only if `coeff α e f ∈ J` for all `e ≤ d`. -/
theorem mem_basis_iff {f : MvPowerSeries σ α} {Jd : TwoSidedIdeal α × (σ →₀ ℕ)} :
    f ∈ basis σ α Jd ↔ ∀ e ≤ Jd.2, coeff α e f ∈ Jd.1 := by
  simp [basis]

/-- If `J ≤ K` and `e ≤ d`, then we have the inclusion of twosided ideals
`basis σ α ⟨J, d⟩ ≤ basis σ α ⟨K, e,>`. -/
theorem basis_le {Jd Ke : TwoSidedIdeal α × (σ →₀ ℕ)} (hJK : Jd.1 ≤ Ke.1) (hed : Ke.2 ≤ Jd.2) :
    basis σ α Jd ≤ basis σ α Ke :=
  fun _ ↦ forall_imp (fun _ h hue ↦ hJK (h (le_trans hue hed)))

/-- `basis σ α ⟨J, d⟩ ≤ basis σ α ⟨K, e⟩` if and only if `J ≤ K` and `e ≤ d`. -/
theorem basis_le_iff {J K : TwoSidedIdeal α} {d e : σ →₀ ℕ} (hK : K ≠ ⊤) :
    basis σ α ⟨J, d⟩ ≤ basis σ α ⟨K, e⟩ ↔ J ≤ K ∧ e ≤ d := by
  constructor
  · simp only [basis, TwoSidedIdeal.le_iff, TwoSidedIdeal.coe_mk', setOf_subset_setOf]
    intro h
    by_contra h'
    simp only [not_and_or] at h'
    rcases h' with h' | h'
    · simp only [← coe_subset_coe, Set.not_subset] at h'
      obtain ⟨a, haJ, haK⟩ := h'
      apply haK
      specialize h (monomial α e a) _ e (le_refl e)
      · intro e' he'
        classical
        rw [coeff_monomial]
        split_ifs
        · exact haJ
        · apply zero_mem
      rwa [coeff_monomial_same] at h
    · simp only [← inf_eq_right] at h'
      apply hK
      rw [eq_top_iff]
      intro a _
      specialize h (monomial α e a) _
      · intro e' he'
        convert zero_mem J
        apply coeff_monomial_ne
        rintro ⟨rfl⟩
        exact h' (right_eq_inf.mpr he').symm
      · specialize h e (le_refl e)
        rwa [coeff_monomial_same] at h
  · rintro ⟨hJK, hed⟩
    exact basis_le hJK hed

variable [TopologicalSpace α]

-- We endow MvPowerSeries σ α with the product topology.
open WithPiTopology

variable (σ α) in
theorem ringSubgroupsBasis :
    RingSubgroupsBasis (fun (Jd : {J : TwoSidedIdeal α | (J : Set α) ∈ 𝓝 0} × (σ →₀ ℕ))
        ↦ (basis σ α ⟨Jd.1, Jd.2⟩).asIdeal.toAddSubgroup) where
  inter Jd Ke := ⟨⟨⟨Jd.1 ⊓ Ke.1, Filter.inter_mem Jd.1.prop Ke.1.prop⟩, Jd.2 ⊔ Ke.2⟩, by
    simp only [le_inf_iff]
    exact ⟨basis_le inf_le_left le_sup_left, basis_le inf_le_right le_sup_right⟩⟩
  mul Jd := ⟨Jd, fun f ↦ by
    simp only [Submodule.coe_toAddSubgroup, mem_mul]
    rintro ⟨x, hx, y, hy, rfl⟩
    exact Ideal.mul_mem_left _ _ hy⟩
  leftMul f Jd := ⟨Jd, fun g hg ↦ (basis σ α ⟨Jd.1, Jd.2⟩).mul_mem_left f g hg⟩
  rightMul f Jd := ⟨Jd, fun g hg ↦ by
    intro e he
    simp only [Submodule.coe_toAddSubgroup, TwoSidedIdeal.coe_asIdeal,
      mem_coe, sub_zero, mem_basis_iff] at hg ⊢
    classical
    rw [coeff_mul]
    apply sum_mem
    rintro ⟨i, j⟩ h
    apply TwoSidedIdeal.mul_mem_right
    apply hg i (le_trans ?_ he)
    simp only [← Finset.mem_antidiagonal.mp h, le_self_add]⟩

/-- If the coefficient ring `α` is endowed with the discrete topology, then for every `d : σ →₀ ℕ`,
`↑(basis σ α d) ∈ 𝓝 (0 : MvPowerSeries σ α)`. -/
theorem basis_mem_nhds_zero (Jd : {J : TwoSidedIdeal α | (J : Set α) ∈ 𝓝 0} × (σ →₀ ℕ)) :
    (basis σ α ⟨Jd.1, Jd.2⟩ : Set (MvPowerSeries σ α)) ∈ 𝓝 0 := by
  classical
  rw [nhds_pi, Filter.mem_pi]
  use Finset.Iic Jd.2, Finset.finite_toSet _, (fun e => if e ≤ Jd.2 then Jd.1 else univ)
  constructor
  · intro e
    split_ifs
    · exact Jd.1.prop
    · simp only [Filter.univ_mem]
  · intro f
    simp only [Finset.coe_Iic, mem_pi, mem_Iic, mem_ite_univ_right, mem_singleton_iff, mem_coe]
    rw [mem_basis_iff]
    exact forall_imp (fun e h he => h he he)

variable [TopologicalRing α] [IsLinearTopology α]

lemma mem_nhds_zero_iff {U : Set (MvPowerSeries σ α)} :
    U ∈ 𝓝 0 ↔ ∃ Jd, ((Jd.1 : Set α) ∈ 𝓝 0) ∧ (basis σ α Jd : Set (MvPowerSeries σ α)) ⊆ U := by
  constructor
  · rw [nhds_pi, Filter.mem_pi]
    rintro ⟨D, hD, t, ht, ht'⟩
    suffices ∃ J : TwoSidedIdeal α, (J : Set α) ∈ 𝓝 0 ∧ (J : Set α) ⊆ ⋂ i ∈ D, t i by
      obtain ⟨J, hJ, hJD⟩ := this
      use ⟨J, Finset.sup hD.toFinset id⟩
      constructor
      · exact hJ
      · apply subset_trans _ ht'
        intros f hf e he
        simp only [← coeff_apply α f e]
        apply biInter_subset_of_mem he
        apply hJD
        rw [mem_coe, mem_basis_iff] at hf
        exact hf e (Finset.le_sup (f := id) (hD.mem_toFinset.mpr he))
    set s := ⋂ i ∈ D, t i
    rw [← (IsLinearTopology.hasBasis_twoSidedIdeal (α := α)).mem_iff']
    exact (Filter.biInter_mem hD).mpr fun i a ↦ ht i
  · rintro ⟨Jd, hJd_mem_nhds, hJd⟩
    exact Filter.sets_of_superset _ (basis_mem_nhds_zero ⟨⟨Jd.1, hJd_mem_nhds⟩,Jd.2⟩) hJd

/-- If the coefficient ring `α` is endowed with a linear topology, then the pointwise
topology on `MvPowerSeries σ α)` agrees with the topology generated by `MvPowerSeries.basis`. -/
theorem topology_eq_ideals_basis_topology :
    MvPowerSeries.WithPiTopology.instTopologicalSpace α =
      (ringSubgroupsBasis σ α).toRingFilterBasis.topology := by
  rw [TopologicalAddGroup.ext_iff inferInstance inferInstance]
  ext s
  rw [mem_nhds_zero_iff]
  simp [mem_nhds_zero_iff, ((ringSubgroupsBasis σ α).hasBasis_nhds 0).mem_iff]

/-- The topology on `MvPowerSeries` is a linear topology when the ring of coefficients has
the discrete topology. -/
instance : IsLinearTopology (MvPowerSeries σ α) :=
  IsLinearTopology.mk_of_twoSidedIdeal
    (p := fun Jd ↦ (Jd.1 : Set α) ∈ 𝓝 0) (s := fun Jd ↦ basis σ α Jd)
    (Filter.HasBasis.mk fun s ↦ by simp [mem_nhds_zero_iff])

end LinearTopology

end MvPowerSeries
