import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Calculus.TangentCone

open Set

variable {𝕜 : Type*} [NormedField 𝕜] {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {E' : Type*} [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H']

/-- Given two model_with_corners `I` on `(E, H)` and `I'` on `(E', H')`, we define the model with
corners `I.prod I'` on `(E × E', H × H')`. This appears in particular for the manifold
structure on the tangent bundle to a manifold modelled on `(E, H)`: it will be modelled on
`(E × E, H × E)`. -/
@[simps]
def ModelWithCorners.prod (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') :
    ModelWithCorners 𝕜 (E × E') (H × H') :=
  { I.toPartialEquiv.prod I'.toPartialEquiv with
    toFun := fun x => (I x.1, I' x.2)
    invFun := fun x => (I.symm x.1, I'.symm x.2)
    source := { x | x.1 ∈ I.source ∧ x.2 ∈ I'.source }
    source_eq := by simp only [setOf_true, mfld_simps]
    uniqueDiffOn' := UniqueDiffOn.dense_or_prod I.uniqueDiffOn' I'.uniqueDiffOn'
    target_subset_closure_interior := by
      simp only [PartialEquiv.prod_target, target_eq, interior_prod_eq, closure_prod_eq]
      exact Set.prod_mono I.range_subset_closure_interior I'.range_subset_closure_interior
    continuous_toFun := I.continuous_toFun.prodMap I'.continuous_toFun
    continuous_invFun := I.continuous_invFun.prodMap I'.continuous_invFun }

@[simp]
lemma ModelWithCorners.range_prod (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') :
    range (I.prod I') = range I ×ˢ range I' := by
  simp [← target_eq]

/-- Given a finite family of `ModelWithCorners` `I i` on `(E i, H i)`, we define the model with
corners `pi I` on `(Π i, E i, ModelPi H)`. See note [Manifold type tags] for explanation about
`ModelPi H`. -/
@[simps!]
def ModelWithCorners.pi {𝕜 : Type*} [NormedField 𝕜] {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] {H : ι → Type*}
    [∀ i, TopologicalSpace (H i)] (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)) :
    ModelWithCorners 𝕜 (Π i, E i) (Π i, H i) where
  toPartialEquiv := PartialEquiv.pi fun i => (I i).toPartialEquiv
  source_eq := by simp only [pi_univ, mfld_simps]
  uniqueDiffOn' := UniqueDiffOn.dense_or_pi (fun i hi ↦ (I i).uniqueDiffOn')
  target_subset_closure_interior := by
    simp only [PartialEquiv.pi_target, target_eq, finite_univ, interior_pi_set, closure_pi_set]
    exact Set.pi_mono (fun i _ ↦ (I i).range_subset_closure_interior)
  continuous_toFun := continuous_pi fun i => (I i).continuous_toFun.comp (continuous_apply i)
  continuous_invFun := continuous_pi fun i => (I i).continuous_invFun.comp (continuous_apply i)

@[simp]
lemma ModelWithCorners.range_pi {𝕜 : Type*} [NormedField 𝕜] {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] {H : ι → Type*}
    [∀ i, TopologicalSpace (H i)] (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)):
    range (ModelWithCorners.pi I) = Set.pi univ (fun i ↦ range (I i)) := by
  simp [← target_eq]

/-- The product of two normed spaces is a normed space, with the sup norm. -/
instance Prod.normedSpace : NormedSpace 𝕜 (E × E') where
  norm_smul_le := fun s x => by
    simp only [norm_smul, Prod.norm_def, Prod.smul_snd, Prod.smul_fst,
      mul_max_of_nonneg, norm_nonneg, le_rfl]
  modelWithCornersSelf := (modelWithCornersSelf 𝕜 E).prod (modelWithCornersSelf 𝕜 E')
  modelWithCornersSelf_eq_id := by ext <;> simp

/-- The product of finitely many normed spaces is a normed space, with the sup norm. -/
instance Pi.normedSpace {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, SeminormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] : NormedSpace 𝕜 (∀ i, E i) where
  norm_smul_le a f := by
    simp_rw [← coe_nnnorm, ← NNReal.coe_mul, NNReal.coe_le_coe, Pi.nnnorm_def,
      NNReal.mul_finset_sup]
    exact Finset.sup_mono_fun fun _ _ => norm_smul_le a _
  modelWithCornersSelf := ModelWithCorners.pi (fun i ↦ modelWithCornersSelf 𝕜 (E i))
  modelWithCornersSelf_eq_id := by ext <;> simp

/-- The product of two normed algebras is a normed algebra, with the sup norm. -/
instance Prod.normedAlgebra {E F : Type*} [SeminormedRing E] [SeminormedRing F] [NormedAlgebra 𝕜 E]
    [NormedAlgebra 𝕜 F] : NormedAlgebra 𝕜 (E × F) :=
  { Prod.normedSpace, Prod.algebra 𝕜 E F with }

-- Porting note: Lean 3 could synth the algebra instances for Pi Pr
/-- The product of finitely many normed algebras is a normed algebra, with the sup norm. -/
instance Pi.normedAlgebra {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, SeminormedRing (E i)]
    [∀ i, NormedAlgebra 𝕜 (E i)] : NormedAlgebra 𝕜 (∀ i, E i) :=
  { Pi.normedSpace, Pi.algebra _ E with }
