import Mathlib.Algebra.Homology.ShortComplex.LeftHomology

open ZeroObject

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C D : Type _} [Category C] [Category D]
  [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

structure RightHomologyData :=
(Q H : C)
(p : S.X₂ ⟶ Q)
(ι : H ⟶ Q)
(wp : S.f ≫ p = 0)
(hp : IsColimit (CokernelCofork.ofπ p wp))
(wι : ι ≫ hp.desc (CokernelCofork.ofπ _ S.zero) = 0)
(hι : IsLimit (KernelFork.ofι ι wι))

initialize_simps_projections RightHomologyData (-hp, -hι)

namespace RightHomologyData

@[simps]
noncomputable def ofKerOfCoker [HasCokernel S.f] [HasKernel (cokernel.desc S.f S.g S.zero)] :
  S.RightHomologyData :=
{ Q := cokernel S.f,
  H := kernel (cokernel.desc S.f S.g S.zero),
  p := cokernel.π _,
  ι := kernel.ι _,
  wp := cokernel.condition _,
  hp := cokernelIsCokernel _,
  wι := kernel.condition _,
  hι := kernelIsKernel _, }

attribute [reassoc (attr := simp)] wp wι

variable {S}
variable (h : S.RightHomologyData) {A : C}

instance : Epi h.p :=
  ⟨fun _ _ => Cofork.IsColimit.hom_ext h.hp⟩

instance : Mono h.ι :=
  ⟨fun _ _ => Fork.IsLimit.hom_ext h.hι⟩

def descQ (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) : h.Q ⟶ A :=
h.hp.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]
lemma p_descQ (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) :
  h.p ≫ h.descQ k hk = k :=
h.hp.fac _ WalkingParallelPair.one

@[simp]
def descH (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) : h.H ⟶ A :=
  h.ι ≫ h.descQ k hk

/-- The morphism `h.Q ⟶ S.X₃` induced by `S.g : S.X₂ ⟶ S.X₃` and the fact that
`h.Q` is a cokernel of `S.f : S.X₁ ⟶ S.X₂`. -/
def g' : h.Q ⟶ S.X₃ := h.descQ S.g S.zero

@[reassoc (attr := simp)]
lemma p_g' : h.p ≫ h.g' = S.g :=
p_descQ _ _ _

@[reassoc (attr := simp)]
lemma ι_g' : h.ι ≫ h.g' = 0 := h.wι

@[reassoc]
lemma ι_descQ_eq_zero_of_boundary (k : S.X₂ ⟶ A) (x : S.X₃ ⟶ A) (hx : k = S.g ≫ x) :
  h.ι ≫ h.descQ k (by rw [hx, S.zero_assoc, zero_comp]) = 0 := by
  rw [show 0 = h.ι ≫ h.g' ≫ x by simp]
  congr 1
  simp only [← cancel_epi h.p, hx, p_descQ, p_g'_assoc]

/-- For `h : S.RightHomologyData`, this is a restatement of `h.hι `, saying that
`ι : h.H ⟶ h.Q` is a kernel of `h.g' : h.Q ⟶ S.X₃`. -/
def hι' : IsLimit (KernelFork.ofι h.ι h.ι_g') := h.hι

def liftH (k : A ⟶ h.Q) (hk : k ≫ h.g' = 0) :
  A ⟶ h.H :=
h.hι.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]
lemma liftH_ι (k : A ⟶ h.Q) (hk : k ≫ h.g' = 0) :
  h.liftH k hk ≫ h.ι = k :=
h.hι.fac (KernelFork.ofι k hk) WalkingParallelPair.zero

variable (S)

@[simps]
def ofIsLimitKernelFork (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c) :
  S.RightHomologyData where
  Q := S.X₂
  H := c.pt
  p := 𝟙 _
  ι := c.ι
  wp := by rw [comp_id, hf]
  hp := CokernelCofork.IsColimit.ofId _ hf
  wι := KernelFork.condition _
  hι := IsLimit.ofIsoLimit hc (Fork.ext (Iso.refl _) (by aesop_cat))

@[simp] lemma ofIsLimitKernelFork_g' (hf : S.f = 0) (c : KernelFork S.g)
    (hc : IsLimit c) : (ofIsLimitKernelFork S hf c hc).g' = S.g := by
  rw [← cancel_epi (ofIsLimitKernelFork S hf c hc).p, p_g',
    ofIsLimitKernelFork_p, id_comp]

@[simps!]
noncomputable def ofHasKernel [HasKernel S.g] (hf : S.f = 0) : S.RightHomologyData :=
ofIsLimitKernelFork S hf _ (kernelIsKernel _)

@[simps]
def ofIsColimitCokernelCofork (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c) :
  S.RightHomologyData where
  Q := c.pt
  H := c.pt
  p := c.π
  ι := 𝟙 _
  wp := CokernelCofork.condition _
  hp := IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _) (by aesop_cat))
  wι := Cofork.IsColimit.hom_ext hc (by simp [hg])
  hι := KernelFork.IsLimit.ofId _ (Cofork.IsColimit.hom_ext hc (by simp [hg]))

@[simp] lemma ofIsColimitCokernelCofork_g' (hg : S.g = 0) (c : CokernelCofork S.f)
  (hc : IsColimit c) : (ofIsColimitCokernelCofork S hg c hc).g' = 0 :=
by rw [← cancel_epi (ofIsColimitCokernelCofork S hg c hc).p, p_g', hg, comp_zero]

@[simp]
noncomputable def ofHasCokernel [HasCokernel S.f] (hg : S.g = 0) : S.RightHomologyData :=
ofIsColimitCokernelCofork S hg _ (cokernelIsCokernel _)

@[simps]
def ofZeros (hf : S.f = 0) (hg : S.g = 0) : S.RightHomologyData where
  Q := S.X₂
  H := S.X₂
  p := 𝟙 _
  ι := 𝟙 _
  wp := by rw [comp_id, hf]
  hp := CokernelCofork.IsColimit.ofId _ hf
  wι := by
    change 𝟙 _ ≫ S.g = 0
    simp only [hg, comp_zero]
  hι := KernelFork.IsLimit.ofId _ hg

@[simp]
lemma ofZeros_g' (hf : S.f = 0) (hg : S.g = 0) :
    (ofZeros S hf hg).g' = 0 := by
  rw [← cancel_epi ((ofZeros S hf hg).p), comp_zero, p_g', hg]

@[simps]
noncomputable def cokernelSequence' {X Y : C} (f : X ⟶ Y) (c : CokernelCofork f)
    (hc : IsColimit c) [HasZeroObject C] :
    RightHomologyData (ShortComplex.mk f c.π c.condition) where
  Q := c.pt
  H := 0
  p := c.π
  ι := 0
  wp := c.condition
  hp := IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _) (by simp))
  wι := Subsingleton.elim _ _
  hι := by
    refine' KernelFork.IsLimit.ofIsZeroOfMono _ _ _
    . dsimp
      convert (inferInstance : Mono (𝟙 c.pt))
      haveI := epi_of_isColimit_cofork hc
      rw [← cancel_epi c.π]
      simp only [parallelPair_obj_one, Functor.const_obj_obj, id_comp,
        Cofork.IsColimit.π_desc, Cofork.π_ofπ, comp_id]
    . apply isZero_zero

@[simps!]
noncomputable def cokernelSequence {X Y : C} (f : X ⟶ Y) [HasCokernel f] [HasZeroObject C] :
    RightHomologyData (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)) := by
  let h := cokernelSequence' f _ (cokernelIsCokernel f)
  exact h

end RightHomologyData

class HasRightHomology : Prop :=
(condition : Nonempty S.RightHomologyData)

noncomputable def rightHomologyData [HasRightHomology S] :
  S.RightHomologyData := HasRightHomology.condition.some

variable {S}

namespace HasRightHomology

lemma mk' (h : S.RightHomologyData) : HasRightHomology S :=
⟨Nonempty.intro h⟩

instance of_ker_of_coker
    [HasCokernel S.f] [HasKernel (cokernel.desc S.f S.g S.zero)] :
  S.HasRightHomology := HasRightHomology.mk' (RightHomologyData.ofKerOfCoker S)

instance of_hasKernel {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g] :
    (ShortComplex.mk (0 : X ⟶ Y) g zero_comp).HasRightHomology :=
  HasRightHomology.mk' (RightHomologyData.ofHasKernel _ rfl)

instance of_hasCokernel {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f] :
    (ShortComplex.mk f (0 : Y ⟶ Z) comp_zero).HasRightHomology :=
  HasRightHomology.mk' (RightHomologyData.ofHasCokernel _ rfl)

instance of_zeros (X Y Z : C) :
    (ShortComplex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp).HasRightHomology :=
  HasRightHomology.mk' (RightHomologyData.ofZeros _ rfl rfl)

end HasRightHomology

namespace RightHomologyData

@[simps]
def op (h : S.RightHomologyData) : S.op.LeftHomologyData where
  K := Opposite.op h.Q
  H := Opposite.op h.H
  i := h.p.op
  π := h.ι.op
  wi := Quiver.Hom.unop_inj h.wp
  hi := CokernelCofork.IsColimit.ofπOp _ _ h.hp
  wπ := Quiver.Hom.unop_inj h.wι
  hπ := KernelFork.IsLimit.ofιOp _ _ h.hι

@[simp] lemma op_f' (h : S.RightHomologyData) :
    h.op.f' = h.g'.op := rfl

@[simps]
def unop {S : ShortComplex Cᵒᵖ} (h : S.RightHomologyData) : S.unop.LeftHomologyData where
  K := Opposite.unop h.Q
  H := Opposite.unop h.H
  i := h.p.unop
  π := h.ι.unop
  wi := Quiver.Hom.op_inj h.wp
  hi := CokernelCofork.IsColimit.ofπUnop _ _ h.hp
  wπ := Quiver.Hom.op_inj h.wι
  hπ := KernelFork.IsLimit.ofιUnop _ _ h.hι

@[simp] lemma unop_f' {S : ShortComplex Cᵒᵖ} (h : S.RightHomologyData) :
    h.unop.f' = h.g'.unop := rfl

end RightHomologyData

namespace LeftHomologyData

@[simps]
def op (h : S.LeftHomologyData) : S.op.RightHomologyData where
  Q := Opposite.op h.K
  H := Opposite.op h.H
  p := h.i.op
  ι := h.π.op
  wp := Quiver.Hom.unop_inj h.wi
  hp := KernelFork.IsLimit.ofιOp _ _ h.hi
  wι := Quiver.Hom.unop_inj h.wπ
  hι := CokernelCofork.IsColimit.ofπOp _ _ h.hπ

@[simp] lemma op_g' (h : S.LeftHomologyData) :
    h.op.g' = h.f'.op := rfl

@[simps]
def unop {S : ShortComplex Cᵒᵖ} (h : S.LeftHomologyData) : S.unop.RightHomologyData where
  Q := Opposite.unop h.K
  H := Opposite.unop h.H
  p := h.i.unop
  ι := h.π.unop
  wp := Quiver.Hom.op_inj h.wi
  hp := KernelFork.IsLimit.ofιUnop _ _ h.hi
  wι := Quiver.Hom.op_inj h.wπ
  hι := CokernelCofork.IsColimit.ofπUnop _ _ h.hπ

@[simp] lemma unop_g' {S : ShortComplex Cᵒᵖ} (h : S.LeftHomologyData) :
    h.unop.g' = h.f'.unop := rfl

end LeftHomologyData

instance [S.HasLeftHomology] : HasRightHomology S.op :=
  HasRightHomology.mk' S.leftHomologyData.op

instance [S.HasRightHomology] : HasLeftHomology S.op :=
  HasLeftHomology.mk' S.rightHomologyData.op

lemma hasLeftHomology_iff_op (S : ShortComplex C) :
    S.HasLeftHomology ↔ S.op.HasRightHomology :=
  ⟨fun _ => inferInstance, fun _ => HasLeftHomology.mk' S.op.rightHomologyData.unop⟩

lemma hasRightHomology_iff_op (S : ShortComplex C) :
    S.HasRightHomology ↔ S.op.HasLeftHomology :=
  ⟨fun _ => inferInstance, fun _ => HasRightHomology.mk' S.op.leftHomologyData.unop⟩

lemma hasLeftHomology_iff_unop (S : ShortComplex Cᵒᵖ) :
    S.HasLeftHomology ↔ S.unop.HasRightHomology :=
  S.unop.hasRightHomology_iff_op.symm

lemma hasRightHomology_iff_unop (S : ShortComplex Cᵒᵖ) :
    S.HasRightHomology ↔ S.unop.HasLeftHomology :=
  S.unop.hasLeftHomology_iff_op.symm

section

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData)

structure RightHomologyMapData where
  φQ : h₁.Q ⟶ h₂.Q
  φH : h₁.H ⟶ h₂.H
  commp : h₁.p ≫ φQ = φ.τ₂ ≫ h₂.p := by aesop_cat
  commg' : φQ ≫ h₂.g' = h₁.g' ≫ φ.τ₃ := by aesop_cat
  commι : φH ≫ h₂.ι = h₁.ι ≫ φQ := by aesop_cat

namespace RightHomologyMapData

attribute [reassoc (attr := simp)] commp commg' commι
attribute [nolint simpNF] mk.injEq

@[simps]
def zero (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
  RightHomologyMapData 0 h₁ h₂ where
  φQ := 0
  φH := 0

@[simps]
def id (h : S.RightHomologyData) : RightHomologyMapData (𝟙 S) h h where
  φQ := 𝟙 _
  φH := 𝟙 _

@[simps]
def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.RightHomologyData}
  {h₂ : S₂.RightHomologyData} {h₃ : S₃.RightHomologyData}
  (ψ : RightHomologyMapData φ h₁ h₂) (ψ' : RightHomologyMapData φ' h₂ h₃) :
  RightHomologyMapData (φ ≫ φ') h₁ h₃ where
  φQ := ψ.φQ ≫ ψ'.φQ
  φH := ψ.φH ≫ ψ'.φH

instance : Subsingleton (RightHomologyMapData φ h₁ h₂) :=
  ⟨fun ψ₁ ψ₂ => by
    have hQ : ψ₁.φQ = ψ₂.φQ := by rw [← cancel_epi h₁.p, commp, commp]
    have hH : ψ₁.φH = ψ₂.φH := by rw [← cancel_mono h₂.ι, commι, commι, hQ]
    cases ψ₁
    cases ψ₂
    congr⟩

instance : Inhabited (RightHomologyMapData φ h₁ h₂) := ⟨by
  let φQ : h₁.Q ⟶ h₂.Q := h₁.descQ (φ.τ₂ ≫ h₂.p) (by rw [← φ.comm₁₂_assoc, h₂.wp, comp_zero])
  have commg' : φQ ≫ h₂.g' = h₁.g' ≫ φ.τ₃ :=
    by rw [← cancel_epi h₁.p, RightHomologyData.p_descQ_assoc, assoc,
      RightHomologyData.p_g', φ.comm₂₃, RightHomologyData.p_g'_assoc]
  let φH : h₁.H ⟶ h₂.H := h₂.liftH (h₁.ι ≫ φQ)
    (by rw [assoc, commg', RightHomologyData.ι_g'_assoc, zero_comp])
  exact ⟨φQ, φH, by simp, commg', by simp⟩⟩

instance : Unique (RightHomologyMapData φ h₁ h₂) := Unique.mk' _

def _root_.CategoryTheory.ShortComplex.rightHomologyMapData :
  RightHomologyMapData φ h₁ h₂ := default

variable {φ h₁ h₂}

lemma congr_φH {γ₁ γ₂ : RightHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φH = γ₂.φH := by rw [eq]
lemma congr_φQ {γ₁ γ₂ : RightHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φQ = γ₂.φQ := by rw [eq]

@[simps]
def ofZeros (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
  RightHomologyMapData φ (RightHomologyData.ofZeros S₁ hf₁ hg₁)
    (RightHomologyData.ofZeros S₂ hf₂ hg₂) where
  φQ := φ.τ₂
  φH := φ.τ₂

@[simps]
def ofIsLimitKernelFork (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (c₁ : KernelFork S₁.g) (hc₁ : IsLimit c₁)
    (hf₂ : S₂.f = 0) (c₂ : KernelFork S₂.g) (hc₂ : IsLimit c₂) (f : c₁.pt ⟶ c₂.pt)
    (comm : c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι) :
    RightHomologyMapData φ (RightHomologyData.ofIsLimitKernelFork S₁ hf₁ c₁ hc₁)
      (RightHomologyData.ofIsLimitKernelFork S₂ hf₂ c₂ hc₂) where
  φQ := φ.τ₂
  φH := f
  commg' := by simp only [RightHomologyData.ofIsLimitKernelFork_g', φ.comm₂₃]
  commι := comm.symm

@[simps]
def ofIsColimitCokernelCofork (φ : S₁ ⟶ S₂)
  (hg₁ : S₁.g = 0) (c₁ : CokernelCofork S₁.f) (hc₁ : IsColimit c₁)
  (hg₂ : S₂.g = 0) (c₂ : CokernelCofork S₂.f) (hc₂ : IsColimit c₂) (f : c₁.pt ⟶ c₂.pt)
  (comm : φ.τ₂ ≫ c₂.π = c₁.π ≫ f) :
  RightHomologyMapData φ (RightHomologyData.ofIsColimitCokernelCofork S₁ hg₁ c₁ hc₁)
    (RightHomologyData.ofIsColimitCokernelCofork S₂ hg₂ c₂ hc₂) where
  φQ := f
  φH := f
  commp := comm.symm

variable (S)

@[simps]
def compatibilityOfZerosOfIsLimitKernelFork (hf : S.f = 0) (hg : S.g = 0)
    (c : KernelFork S.g) (hc : IsLimit c) :
    RightHomologyMapData (𝟙 S)
      (RightHomologyData.ofIsLimitKernelFork S hf c hc)
      (RightHomologyData.ofZeros S hf hg) where
  φQ := 𝟙 _
  φH := c.ι

@[simps]
def compatibilityOfZerosOfIsColimitCokernelCofork (hf : S.f = 0) (hg : S.g = 0)
  (c : CokernelCofork S.f) (hc : IsColimit c) :
  RightHomologyMapData (𝟙 S)
    (RightHomologyData.ofZeros S hf hg)
    (RightHomologyData.ofIsColimitCokernelCofork S hg c hc) where
  φQ := c.π
  φH := c.π

end RightHomologyMapData

end

variable (S)

noncomputable def rightHomology [HasRightHomology S] : C := S.rightHomologyData.H
noncomputable def cyclesCo [HasRightHomology S] : C := S.rightHomologyData.Q
noncomputable def rightHomologyι [HasRightHomology S] : S.rightHomology ⟶ S.cyclesCo :=
  S.rightHomologyData.ι
noncomputable def pCyclesCo [HasRightHomology S] : S.X₂ ⟶ S.cyclesCo := S.rightHomologyData.p
noncomputable def fromCyclesCo [HasRightHomology S] : S.cyclesCo ⟶ S.X₃ := S.rightHomologyData.g'

@[reassoc (attr := simp)]
lemma f_pCyclesCo [HasRightHomology S] : S.f ≫ S.pCyclesCo = 0 :=
  S.rightHomologyData.wp

@[reassoc (attr := simp)]
lemma p_fromCyclesCo [HasRightHomology S] : S.pCyclesCo ≫ S.fromCyclesCo = S.g :=
  S.rightHomologyData.p_g'

instance [HasRightHomology S] : Epi S.pCyclesCo := by
  dsimp only [pCyclesCo]
  infer_instance

instance [HasRightHomology S] : Mono S.rightHomologyι := by
  dsimp only [rightHomologyι]
  infer_instance

variable {S}

def rightHomologyMap' (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
  h₁.H ⟶ h₂.H := (rightHomologyMapData φ _ _).φH

def cyclesCoMap' (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
  h₁.Q ⟶ h₂.Q := (rightHomologyMapData φ _ _).φQ

@[reassoc (attr := simp)]
lemma p_cyclesCoMap' (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    h₁.p ≫ cyclesCoMap' φ h₁ h₂ = φ.τ₂ ≫ h₂.p :=
  RightHomologyMapData.commp _

@[reassoc (attr := simp)]
lemma rightHomologyι_naturality' (φ : S₁ ⟶ S₂)
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    rightHomologyMap' φ h₁ h₂ ≫ h₂.ι = h₁.ι ≫ cyclesCoMap' φ h₁ h₂ :=
  RightHomologyMapData.commι _

noncomputable def rightHomologyMap [HasRightHomology S₁] [HasRightHomology S₂]
    (φ : S₁ ⟶ S₂) : S₁.rightHomology ⟶ S₂.rightHomology :=
  rightHomologyMap' φ _ _

noncomputable def cyclesCoMap [HasRightHomology S₁] [HasRightHomology S₂]
    (φ : S₁ ⟶ S₂) : S₁.cyclesCo ⟶ S₂.cyclesCo :=
  cyclesCoMap' φ _ _

@[reassoc (attr := simp)]
lemma p_cyclesCoMap (φ : S₁ ⟶ S₂) [S₁.HasRightHomology] [S₂.HasRightHomology] :
    S₁.pCyclesCo ≫ cyclesCoMap φ = φ.τ₂ ≫ S₂.pCyclesCo :=
  p_cyclesCoMap' _ _ _

@[reassoc (attr := simp)]
lemma fromCyclesCo_naturality (φ : S₁ ⟶ S₂) [S₁.HasRightHomology] [S₂.HasRightHomology] :
    cyclesCoMap φ ≫ S₂.fromCyclesCo = S₁.fromCyclesCo ≫ φ.τ₃ := by
  simp only [← cancel_epi S₁.pCyclesCo, p_cyclesCoMap_assoc, p_fromCyclesCo,
    p_fromCyclesCo_assoc, φ.comm₂₃]

@[reassoc (attr := simp)]
lemma rightHomologyι_naturality [HasRightHomology S₁] [HasRightHomology S₂]
    (φ : S₁ ⟶ S₂) :
    rightHomologyMap φ ≫ S₂.rightHomologyι = S₁.rightHomologyι ≫ cyclesCoMap φ :=
  rightHomologyι_naturality' _ _ _

namespace RightHomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂)

lemma rightHomologyMap'_eq : rightHomologyMap' φ h₁ h₂ = γ.φH :=
  RightHomologyMapData.congr_φH (Subsingleton.elim _ _)

lemma cyclesCoMap'_eq : cyclesCoMap' φ h₁ h₂ = γ.φQ :=
  RightHomologyMapData.congr_φQ (Subsingleton.elim _ _)

end RightHomologyMapData

@[simp]
lemma rightHomologyMap'_id (h : S.RightHomologyData) :
    rightHomologyMap' (𝟙 S) h h = 𝟙 _ :=
  (RightHomologyMapData.id h).rightHomologyMap'_eq

@[simp]
lemma cyclesCoMap'_id (h : S.RightHomologyData) :
    cyclesCoMap' (𝟙 S) h h = 𝟙 _ :=
  (RightHomologyMapData.id h).cyclesCoMap'_eq

variable (S)

@[simp]
lemma rightHomologyMap_id [HasRightHomology S] :
    rightHomologyMap (𝟙 S) = 𝟙 _ :=
  rightHomologyMap'_id _

@[simp]
lemma cyclesCoMap_id [HasRightHomology S] :
    cyclesCoMap (𝟙 S) = 𝟙 _ :=
  cyclesCoMap'_id _

@[simp]
lemma rightHomologyMap'_zero (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    rightHomologyMap' 0 h₁ h₂ = 0 :=
  (RightHomologyMapData.zero h₁ h₂).rightHomologyMap'_eq

@[simp]
lemma cyclesCoMap'_zero (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    cyclesCoMap' 0 h₁ h₂ = 0 :=
  (RightHomologyMapData.zero h₁ h₂).cyclesCoMap'_eq

variable (S₁ S₂)

@[simp]
lemma rightHomologyMap_zero [HasRightHomology S₁] [HasRightHomology S₂] :
    rightHomologyMap (0 : S₁ ⟶ S₂) = 0 :=
  rightHomologyMap'_zero _ _

@[simp]
lemma cyclesCoMap_zero [HasRightHomology S₁] [HasRightHomology S₂] :
  cyclesCoMap (0 : S₁ ⟶ S₂) = 0 :=
cyclesCoMap'_zero _ _

variable {S₁ S₂}

@[reassoc]
lemma rightHomologyMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) (h₃ : S₃.RightHomologyData) :
    rightHomologyMap' (φ₁ ≫ φ₂) h₁ h₃ = rightHomologyMap' φ₁ h₁ h₂ ≫
      rightHomologyMap' φ₂ h₂ h₃ := by
  let γ₁ := rightHomologyMapData φ₁ h₁ h₂
  let γ₂ := rightHomologyMapData φ₂ h₂ h₃
  rw [γ₁.rightHomologyMap'_eq, γ₂.rightHomologyMap'_eq, (γ₁.comp γ₂).rightHomologyMap'_eq,
    RightHomologyMapData.comp_φH]

@[reassoc]
lemma cyclesCoMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) (h₃ : S₃.RightHomologyData) :
    cyclesCoMap' (φ₁ ≫ φ₂) h₁ h₃ = cyclesCoMap' φ₁ h₁ h₂ ≫ cyclesCoMap' φ₂ h₂ h₃ := by
  let γ₁ := rightHomologyMapData φ₁ h₁ h₂
  let γ₂ := rightHomologyMapData φ₂ h₂ h₃
  rw [γ₁.cyclesCoMap'_eq, γ₂.cyclesCoMap'_eq, (γ₁.comp γ₂).cyclesCoMap'_eq,
    RightHomologyMapData.comp_φQ]

@[simp]
lemma rightHomologyMap_comp [HasRightHomology S₁] [HasRightHomology S₂] [HasRightHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    rightHomologyMap (φ₁ ≫ φ₂) = rightHomologyMap φ₁ ≫ rightHomologyMap φ₂ :=
rightHomologyMap'_comp _ _ _ _ _

@[simp]
lemma cyclesCoMap_comp [HasRightHomology S₁] [HasRightHomology S₂] [HasRightHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    cyclesCoMap (φ₁ ≫ φ₂) = cyclesCoMap φ₁ ≫ cyclesCoMap φ₂ :=
  cyclesCoMap'_comp _ _ _ _ _

attribute [simp] rightHomologyMap_comp cyclesCoMap_comp

@[simps]
def rightHomologyMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.RightHomologyData)
    (h₂ : S₂.RightHomologyData) : h₁.H ≅ h₂.H where
  hom := rightHomologyMap' e.hom h₁ h₂
  inv := rightHomologyMap' e.inv h₂ h₁
  hom_inv_id := by rw [← rightHomologyMap'_comp, e.hom_inv_id, rightHomologyMap'_id]
  inv_hom_id := by rw [← rightHomologyMap'_comp, e.inv_hom_id, rightHomologyMap'_id]

instance isIso_rightHomologyMap'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    IsIso (rightHomologyMap' φ h₁ h₂) :=
  (inferInstance : IsIso (rightHomologyMapIso' (asIso φ) h₁ h₂).hom)

@[simps]
def cyclesCoMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.RightHomologyData)
  (h₂ : S₂.RightHomologyData) : h₁.Q ≅ h₂.Q where
  hom := cyclesCoMap' e.hom h₁ h₂
  inv := cyclesCoMap' e.inv h₂ h₁
  hom_inv_id := by rw [← cyclesCoMap'_comp, e.hom_inv_id, cyclesCoMap'_id]
  inv_hom_id := by rw [← cyclesCoMap'_comp, e.inv_hom_id, cyclesCoMap'_id]

instance isIso_cyclesCoMap'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    IsIso (cyclesCoMap' φ h₁ h₂) :=
  (inferInstance : IsIso (cyclesCoMapIso' (asIso φ) h₁ h₂).hom)

@[simps]
noncomputable def rightHomologyMapIso (e : S₁ ≅ S₂) [S₁.HasRightHomology]
  [S₂.HasRightHomology] : S₁.rightHomology ≅ S₂.rightHomology where
  hom := rightHomologyMap e.hom
  inv := rightHomologyMap e.inv
  hom_inv_id := by rw [← rightHomologyMap_comp, e.hom_inv_id, rightHomologyMap_id]
  inv_hom_id := by rw [← rightHomologyMap_comp, e.inv_hom_id, rightHomologyMap_id]

instance isIso_rightHomologyMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasRightHomology]
    [S₂.HasRightHomology] :
    IsIso (rightHomologyMap φ) :=
  (inferInstance : IsIso (rightHomologyMapIso (asIso φ)).hom)

@[simps]
noncomputable def cyclesCoMapIso (e : S₁ ≅ S₂) [S₁.HasRightHomology]
    [S₂.HasRightHomology] : S₁.cyclesCo ≅ S₂.cyclesCo where
  hom := cyclesCoMap e.hom
  inv := cyclesCoMap e.inv
  hom_inv_id := by rw [← cyclesCoMap_comp, e.hom_inv_id, cyclesCoMap_id]
  inv_hom_id := by rw [← cyclesCoMap_comp, e.inv_hom_id, cyclesCoMap_id]

instance isIso_cyclesCoMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasRightHomology]
    [S₂.HasRightHomology] : IsIso (cyclesCoMap φ) :=
  (inferInstance : IsIso (cyclesCoMapIso (asIso φ)).hom)

variable {S}

noncomputable def RightHomologyData.rightHomologyIso (h : S.RightHomologyData) [S.HasRightHomology] :
  S.rightHomology ≅ h.H := rightHomologyMapIso' (Iso.refl _) _ _

noncomputable def RightHomologyData.cyclesCoIso (h : S.RightHomologyData) [S.HasRightHomology] :
  S.cyclesCo ≅ h.Q := cyclesCoMapIso' (Iso.refl _) _ _

@[reassoc (attr := simp)]
lemma RightHomologyData.p_compCyclesCoIso_inv (h : S.RightHomologyData) [S.HasRightHomology] :
    h.p ≫ h.cyclesCoIso.inv = S.pCyclesCo := by
  dsimp [pCyclesCo, RightHomologyData.cyclesCoIso]
  simp only [p_cyclesCoMap', id_τ₂, id_comp]

@[reassoc (attr := simp)]
lemma RightHomologyData.pCyclesCo_compCyclesCoIso_hom (h : S.RightHomologyData)
    [S.HasRightHomology] : S.pCyclesCo ≫ h.cyclesCoIso.hom = h.p := by
  simp only [← h.p_compCyclesCoIso_inv, assoc, Iso.inv_hom_id, comp_id]

namespace RightHomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂)

lemma rightHomologyMap_eq [S₁.HasRightHomology] [S₂.HasRightHomology] :
    rightHomologyMap φ = h₁.rightHomologyIso.hom ≫ γ.φH ≫ h₂.rightHomologyIso.inv := by
  dsimp [RightHomologyData.rightHomologyIso, rightHomologyMapIso']
  rw [← γ.rightHomologyMap'_eq, ← rightHomologyMap'_comp,
    ← rightHomologyMap'_comp, id_comp, comp_id]
  rfl

lemma cyclesCoMap_eq [S₁.HasRightHomology] [S₂.HasRightHomology] :
    cyclesCoMap φ = h₁.cyclesCoIso.hom ≫ γ.φQ ≫ h₂.cyclesCoIso.inv := by
  dsimp [RightHomologyData.cyclesCoIso, cyclesMapIso']
  rw [← γ.cyclesCoMap'_eq, ← cyclesCoMap'_comp, ← cyclesCoMap'_comp, id_comp, comp_id]
  rfl

lemma rightHomologyMap_comm [S₁.HasRightHomology] [S₂.HasRightHomology] :
    rightHomologyMap φ ≫ h₂.rightHomologyIso.hom = h₁.rightHomologyIso.hom ≫ γ.φH := by
  simp only [γ.rightHomologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

lemma cyclesCoMap_comm [S₁.HasRightHomology] [S₂.HasRightHomology] :
    cyclesCoMap φ ≫ h₂.cyclesCoIso.hom = h₁.cyclesCoIso.hom ≫ γ.φQ := by
  simp only [γ.cyclesCoMap_eq, assoc, Iso.inv_hom_id, comp_id]

end RightHomologyMapData

variable (C)

/-- We shall say that a category with right homology is a category for which
all short complexes have right homology. -/
abbrev _root_.CategoryTheory.CategoryWithRightHomology : Prop :=
  ∀ (S : ShortComplex C), S.HasRightHomology

@[simps]
noncomputable def rightHomologyFunctor [CategoryWithRightHomology C] :
    ShortComplex C ⥤ C where
  obj S := S.rightHomology
  map := rightHomologyMap

@[simps]
noncomputable def cyclesCoFunctor [CategoryWithRightHomology C] :
    ShortComplex C ⥤ C where
  obj S := S.cyclesCo
  map := cyclesCoMap

@[simps]
noncomputable def rightHomologyιNatTrans [CategoryWithRightHomology C] :
    rightHomologyFunctor C ⟶ cyclesCoFunctor C where
  app S := rightHomologyι S
  naturality := fun _ _ φ => rightHomologyι_naturality φ

@[simps]
noncomputable def pCyclesCoNatTrans [CategoryWithRightHomology C] :
    ShortComplex.π₂ ⟶ cyclesCoFunctor C where
  app S := S.pCyclesCo

@[simps]
noncomputable def fromCyclesCoNatTrans [CategoryWithRightHomology C] :
    cyclesCoFunctor C ⟶ π₃ where
  app S := S.fromCyclesCo
  naturality := fun _ _  φ => fromCyclesCo_naturality φ

variable {C}

@[simps]
def LeftHomologyMapData.op {S₁ S₂ : ShortComplex C} {φ : S₁ ⟶ S₂}
    {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
    (ψ : LeftHomologyMapData φ h₁ h₂) : RightHomologyMapData (opMap φ) h₂.op h₁.op where
  φQ := ψ.φK.op
  φH := ψ.φH.op
  commp := Quiver.Hom.unop_inj (by simp)
  commg' := Quiver.Hom.unop_inj (by simp)
  commι := Quiver.Hom.unop_inj (by simp)

@[simps]
def LeftHomologyMapData.unop {S₁ S₂ : ShortComplex Cᵒᵖ} {φ : S₁ ⟶ S₂}
    {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
    (ψ : LeftHomologyMapData φ h₁ h₂) : RightHomologyMapData (unopMap φ) h₂.unop h₁.unop where
  φQ := ψ.φK.unop
  φH := ψ.φH.unop
  commp := Quiver.Hom.op_inj (by simp)
  commg' := Quiver.Hom.op_inj (by simp)
  commι := Quiver.Hom.op_inj (by simp)

@[simps]
def RightHomologyMapData.op {S₁ S₂ : ShortComplex C} {φ : S₁ ⟶ S₂}
    {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
    (ψ : RightHomologyMapData φ h₁ h₂) : LeftHomologyMapData (opMap φ) h₂.op h₁.op where
  φK := ψ.φQ.op
  φH := ψ.φH.op
  commi := Quiver.Hom.unop_inj (by simp)
  commf' := Quiver.Hom.unop_inj (by simp)
  commπ := Quiver.Hom.unop_inj (by simp)

@[simps]
def RightHomologyMapData.unop {S₁ S₂ : ShortComplex Cᵒᵖ} {φ : S₁ ⟶ S₂}
    {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
    (ψ : RightHomologyMapData φ h₁ h₂) : LeftHomologyMapData (unopMap φ) h₂.unop h₁.unop where
  φK := ψ.φQ.unop
  φH := ψ.φH.unop
  commi := Quiver.Hom.op_inj (by simp)
  commf' := Quiver.Hom.op_inj (by simp)
  commπ := Quiver.Hom.op_inj (by simp)

variable (S)

noncomputable def rightHomologyOpIso [S.HasLeftHomology] :
    S.op.rightHomology ≅ Opposite.op S.leftHomology :=
  S.leftHomologyData.op.rightHomologyIso

noncomputable def leftHomologyOpIso [S.HasRightHomology] :
    S.op.leftHomology ≅ Opposite.op S.rightHomology :=
  S.rightHomologyData.op.leftHomologyIso

noncomputable def cyclesCoOpIso [S.HasLeftHomology] :
    S.op.cyclesCo ≅ Opposite.op S.cycles :=
  S.leftHomologyData.op.cyclesCoIso

noncomputable def cyclesOpIso [S.HasRightHomology] :
    S.op.cycles ≅ Opposite.op S.cyclesCo :=
  S.rightHomologyData.op.cyclesIso

@[simp]
lemma leftHomologyMap'_op
    (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    (leftHomologyMap' φ h₁ h₂).op = rightHomologyMap' (opMap φ) h₂.op h₁.op := by
  let γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [γ.leftHomologyMap'_eq, (γ.op).rightHomologyMap'_eq,
    LeftHomologyMapData.op_φH]

@[simp]
lemma leftHomologyMap_op (φ : S₁ ⟶ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    (leftHomologyMap φ).op = (S₂.rightHomologyOpIso).inv ≫ rightHomologyMap (opMap φ) ≫
      (S₁.rightHomologyOpIso).hom := by
  dsimp [rightHomologyOpIso, RightHomologyData.rightHomologyIso, rightHomologyMap,
    leftHomologyMap]
  simp only [← rightHomologyMap'_comp, comp_id, id_comp, leftHomologyMap'_op]

@[simp]
lemma rightHomologyMap'_op
    (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    (rightHomologyMap' φ h₁ h₂).op = leftHomologyMap' (opMap φ) h₂.op h₁.op := by
  let γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [γ.rightHomologyMap'_eq, (γ.op).leftHomologyMap'_eq,
    RightHomologyMapData.op_φH]

@[simp]
lemma rightHomologyMap_op (φ : S₁ ⟶ S₂) [S₁.HasRightHomology] [S₂.HasRightHomology] :
    (rightHomologyMap φ).op = (S₂.leftHomologyOpIso).inv ≫ leftHomologyMap
      (opMap φ) ≫ (S₁.leftHomologyOpIso).hom := by
  dsimp [leftHomologyOpIso, LeftHomologyData.leftHomologyIso, leftHomologyMap,
    rightHomologyMap]
  simp only [← leftHomologyMap'_comp, comp_id, id_comp, rightHomologyMap'_op]

namespace RightHomologyData

section

variable (φ : S₁ ⟶ S₂) (h : RightHomologyData S₁) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃]

noncomputable def ofEpiOfIsIsoOfMono : RightHomologyData S₂ := by
  haveI : Epi (opMap φ).τ₁ := by dsimp ; infer_instance
  haveI : IsIso (opMap φ).τ₂ := by dsimp ; infer_instance
  haveI : Mono (opMap φ).τ₃ := by dsimp ; infer_instance
  exact (LeftHomologyData.ofEpiOfIsIsoOfMono' (opMap φ) h.op).unop

@[simp] lemma ofEpiOfIsIsoOfMono_Q : (ofEpiOfIsIsoOfMono φ h).Q = h.Q := rfl

@[simp] lemma ofEpiOfIsIsoOfMono_H : (ofEpiOfIsIsoOfMono φ h).H = h.H := rfl

@[simp] lemma ofEpiOfIsIsoOfMono_p : (ofEpiOfIsIsoOfMono φ h).p = (inv φ.τ₂) ≫ h.p := by
  simp [ofEpiOfIsIsoOfMono, opMap]

@[simp] lemma ofEpiOfIsIsoOfMono_ι : (ofEpiOfIsIsoOfMono φ h).ι = h.ι := rfl

@[simp] lemma ofEpiOfIsIsoOfMono_g' : (ofEpiOfIsIsoOfMono φ h).g' = h.g' ≫ φ.τ₃ := by
  simp [ofEpiOfIsIsoOfMono, opMap]

end

section

variable (φ : S₁ ⟶ S₂) (h : RightHomologyData S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃]

noncomputable def ofEpiOfIsIsoOfMono' : RightHomologyData S₁ := by
  haveI : Epi (opMap φ).τ₁ := by dsimp ; infer_instance
  haveI : IsIso (opMap φ).τ₂ := by dsimp ; infer_instance
  haveI : Mono (opMap φ).τ₃ := by dsimp ; infer_instance
  exact (LeftHomologyData.ofEpiOfIsIsoOfMono (opMap φ) h.op).unop

@[simp] lemma ofEpiOfIsIsoOfMono'_Q : (ofEpiOfIsIsoOfMono' φ h).Q = h.Q := rfl

@[simp] lemma ofEpiOfIsIsoOfMono'_H : (ofEpiOfIsIsoOfMono' φ h).H = h.H := rfl

@[simp] lemma ofEpiOfIsIsoOfMono'_p : (ofEpiOfIsIsoOfMono' φ h).p = φ.τ₂ ≫ h.p := by
  simp [ofEpiOfIsIsoOfMono', opMap]

@[simp] lemma ofEpiOfIsIsoOfMono'_ι : (ofEpiOfIsIsoOfMono' φ h).ι = h.ι := rfl

@[simp] lemma ofEpiOfIsIsoOfMono'_g'_τ₃ : (ofEpiOfIsIsoOfMono' φ h).g' ≫ φ.τ₃ = h.g' := by
  rw [← cancel_epi (ofEpiOfIsIsoOfMono' φ h).p, p_g'_assoc, ofEpiOfIsIsoOfMono'_p,
    assoc, p_g', φ.comm₂₃]

end

noncomputable def ofIso (e : S₁ ≅ S₂) (h₁ : RightHomologyData S₁) : RightHomologyData S₂ :=
  h₁.ofEpiOfIsIsoOfMono e.hom

end RightHomologyData

lemma hasRightHomology_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [HasRightHomology S₁]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasRightHomology S₂ :=
  HasRightHomology.mk' (RightHomologyData.ofEpiOfIsIsoOfMono φ S₁.rightHomologyData)

lemma hasRightHomology_of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) [HasRightHomology S₂]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasRightHomology S₁ :=
HasRightHomology.mk' (RightHomologyData.ofEpiOfIsIsoOfMono' φ S₂.rightHomologyData)

lemma hasRightHomology_of_iso {S₁ S₂ : ShortComplex C}
    (e : S₁ ≅ S₂) [HasRightHomology S₁] : HasRightHomology S₂ :=
  hasRightHomology_of_epi_of_isIso_of_mono e.hom

instance _root_.CategoryTheory.CategoryWithRightHomology.op
    [CategoryWithRightHomology C] : CategoryWithLeftHomology Cᵒᵖ :=
  fun S => ShortComplex.hasLeftHomology_of_iso S.unopOp

instance _root_.CategoryTheory.CategoryWithLeftHomology.op
    [CategoryWithLeftHomology C] : CategoryWithRightHomology Cᵒᵖ :=
  fun S => ShortComplex.hasRightHomology_of_iso S.unopOp

namespace RightHomologyMapData

@[simps]
def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : RightHomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    RightHomologyMapData φ h (RightHomologyData.ofEpiOfIsIsoOfMono φ h) where
  φQ := 𝟙 _
  φH := 𝟙 _

@[simps]
noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : RightHomologyData S₂)
  [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    RightHomologyMapData φ (RightHomologyData.ofEpiOfIsIsoOfMono' φ h) h :=
{ φQ := 𝟙 _,
  φH := 𝟙 _, }

end RightHomologyMapData

instance (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (rightHomologyMap' φ h₁ h₂) := by
  let h₂' := RightHomologyData.ofEpiOfIsIsoOfMono φ h₁
  haveI : IsIso (rightHomologyMap' φ h₁ h₂') := by
    rw [(RightHomologyMapData.ofEpiOfIsIsoOfMono φ h₁).rightHomologyMap'_eq]
    dsimp
    infer_instance
  have eq := rightHomologyMap'_comp φ (𝟙 S₂) h₁ h₂' h₂
  rw [comp_id] at eq
  rw [eq]
  infer_instance

instance (φ : S₁ ⟶ S₂) [S₁.HasRightHomology] [S₂.HasRightHomology]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (rightHomologyMap φ) := by
  dsimp only [rightHomologyMap]
  infer_instance

variable (C)

@[simps!]
noncomputable def rightHomologyFunctorOpNatIso [CategoryWithRightHomology C] :
  (rightHomologyFunctor C).op ≅ opFunctor C ⋙ leftHomologyFunctor Cᵒᵖ :=
    NatIso.ofComponents (fun S => (leftHomologyOpIso S.unop).symm) (by simp)

@[simps!]
noncomputable def leftHomologyFunctorOpNatIso [CategoryWithLeftHomology C] :
  (leftHomologyFunctor C).op ≅ opFunctor C ⋙ rightHomologyFunctor Cᵒᵖ :=
    NatIso.ofComponents (fun S => (rightHomologyOpIso S.unop).symm) (by simp)

section

variable {S C}
variable (h : RightHomologyData S)
  {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [HasRightHomology S]

noncomputable def descCyclesCo : S.cyclesCo ⟶ A :=
  S.rightHomologyData.descQ k hk

@[reassoc (attr := simp)]
lemma p_descCyclesCo : S.pCyclesCo ≫ S.descCyclesCo k hk = k :=
  RightHomologyData.p_descQ _ k hk

@[reassoc]
lemma descCyclesCo_comp {A' : C} (α : A ⟶ A') :
    S.descCyclesCo k hk ≫ α = S.descCyclesCo (k ≫ α) (by rw [reassoc_of% hk, zero_comp]) := by
  simp only [← cancel_epi S.pCyclesCo, p_descCyclesCo_assoc, p_descCyclesCo]

variable (S)

noncomputable def cyclesCoIsCokernel :
    IsColimit (CokernelCofork.ofπ S.pCyclesCo S.f_pCyclesCo) :=
  S.rightHomologyData.hp

lemma isIso_pCyclesCo_of_zero (hf : S.f = 0) : IsIso (S.pCyclesCo) :=
  CokernelCofork.IsColimit.isIso_π_of_zero _ S.cyclesCoIsCokernel hf

@[simps]
noncomputable def cyclesCoIsoCokernel [HasCokernel S.f] : S.cyclesCo ≅ cokernel S.f where
  hom := S.descCyclesCo (cokernel.π S.f) (by simp)
  inv := cokernel.desc S.f S.pCyclesCo (by simp)
  hom_inv_id := by simp only [← cancel_epi S.pCyclesCo, p_descCyclesCo_assoc,
    cokernel.π_desc, comp_id]
  inv_hom_id := by simp only [← cancel_epi (cokernel.π S.f), cokernel.π_desc_assoc,
    p_descCyclesCo, comp_id]

variable {S}

@[simp]
noncomputable def descRightHomology : S.rightHomology ⟶ A :=
  S.rightHomologyι ≫ S.descCyclesCo k hk

lemma ι_descCyclesCo_π_eq_zero_of_boundary (x : S.X₃ ⟶ A) (hx : k = S.g ≫ x) :
    S.rightHomologyι ≫ S.descCyclesCo k (by rw [hx, S.zero_assoc, zero_comp]) = 0 :=
  RightHomologyData.ι_descQ_eq_zero_of_boundary _ k x hx

variable (S)

@[reassoc (attr := simp)]
lemma rightHomologyι_comp_fromCyclesCo :
    S.rightHomologyι ≫ S.fromCyclesCo = 0 :=
  S.ι_descCyclesCo_π_eq_zero_of_boundary S.g (𝟙 _) (by rw [comp_id])

noncomputable def rightHomologyIsKernel :
    IsLimit (KernelFork.ofι S.rightHomologyι S.rightHomologyι_comp_fromCyclesCo) :=
  S.rightHomologyData.hι

variable {S}

@[reassoc (attr := simp)]
lemma cyclesCoMap_comp_descCyclesCo (φ : S₁ ⟶ S) [S₁.HasRightHomology] :
    cyclesCoMap φ ≫ S.descCyclesCo k hk =
      S₁.descCyclesCo (φ.τ₂ ≫ k) (by rw [← φ.comm₁₂_assoc, hk, comp_zero]) := by
  simp only [← cancel_epi (S₁.pCyclesCo), p_cyclesCoMap_assoc, p_descCyclesCo]

@[reassoc (attr := simp)]
lemma RightHomologyData.rightHomologyIso_inv_comp_rightHomologyι :
    h.rightHomologyIso.inv ≫ S.rightHomologyι = h.ι ≫ h.cyclesCoIso.inv := by
  dsimp only [rightHomologyι, rightHomologyIso, cyclesCoIso, rightHomologyMapIso']
  simp only [Iso.refl_inv, rightHomologyι_naturality', cyclesCoMapIso'_inv]

@[reassoc (attr := simp)]
lemma RightHomologyData.rightHomologyIso_hom_comp_ι :
    h.rightHomologyIso.hom ≫ h.ι = S.rightHomologyι ≫ h.cyclesCoIso.hom := by
  simp only [← cancel_epi h.rightHomologyIso.inv, ← cancel_mono h.cyclesCoIso.inv, assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id, comp_id, rightHomologyIso_inv_comp_rightHomologyι]

@[reassoc (attr := simp)]
lemma RightHomologyData.cyclesCoIso_inv_comp_descCyclesCo :
    h.cyclesCoIso.inv ≫ S.descCyclesCo k hk = h.descQ k hk := by
  simp only [← cancel_epi h.p, p_compCyclesCoIso_inv_assoc, p_descCyclesCo, p_descQ]

@[simp]
lemma RightHomologyData.cyclesCoIso_hom_comp_descQ :
    h.cyclesCoIso.hom ≫ h.descQ k hk = S.descCyclesCo k hk := by
  rw [← h.cyclesCoIso_inv_comp_descCyclesCo, Iso.hom_inv_id_assoc]

lemma RightHomologyData.ext_iff' (f₁ f₂ : A ⟶ S.rightHomology) :
    f₁ = f₂ ↔ f₁ ≫ h.rightHomologyIso.hom ≫ h.ι = f₂ ≫ h.rightHomologyIso.hom ≫ h.ι := by
  rw [← cancel_mono h.rightHomologyIso.hom, ← cancel_mono h.ι, assoc, assoc]

end

variable {C}

namespace HasRightHomology

lemma hasCokernel [S.HasRightHomology] : HasCokernel S.f :=
⟨⟨⟨_, S.rightHomologyData.hp⟩⟩⟩

lemma hasKernel [S.HasRightHomology] [HasCokernel S.f] :
    HasKernel (cokernel.desc S.f S.g S.zero) := by
  let h := S.rightHomologyData
  haveI : HasLimit (parallelPair h.g' 0) := ⟨⟨⟨_, h.hι'⟩⟩⟩
  let e : parallelPair (cokernel.desc S.f S.g S.zero) 0 ≅ parallelPair h.g' 0 :=
    parallelPair.ext (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) h.hp)
      (Iso.refl _) (coequalizer.hom_ext (by simp)) (by aesop_cat)
  exact hasLimitOfIso e.symm

end HasRightHomology

noncomputable def rightHomologyIsoKernelDesc [S.HasRightHomology] [HasCokernel S.f]
    [HasKernel (cokernel.desc S.f S.g S.zero)] :
    S.rightHomology ≅ kernel (cokernel.desc S.f S.g S.zero) :=
  (RightHomologyData.ofKerOfCoker S).rightHomologyIso

namespace RightHomologyData

lemma isIso_p_of_zero_f (h : RightHomologyData S) (hf : S.f = 0) : IsIso h.p :=
  ⟨⟨h.descQ (𝟙 S.X₂) (by rw [hf, comp_id]), p_descQ _ _ _, by
    rw [← cancel_epi h.p, p_descQ_assoc, id_comp, comp_id]⟩⟩

end RightHomologyData

end ShortComplex

end CategoryTheory
