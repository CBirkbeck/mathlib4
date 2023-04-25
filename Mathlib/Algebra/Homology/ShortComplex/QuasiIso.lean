import Mathlib.Algebra.Homology.ShortComplex.Homology

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C : Type _} [Category C] [HasZeroMorphisms C]
  {S₁ S₂ S₃ S₄ : ShortComplex C}
  [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology] [S₄.HasHomology]

class QuasiIso (φ : S₁ ⟶ S₂) : Prop where
  isIso' : IsIso (homologyMap φ)

instance QuasiIso.isIso (φ : S₁ ⟶ S₂) [QuasiIso φ] : IsIso (homologyMap φ) := QuasiIso.isIso'

lemma quasiIso_iff (φ : S₁ ⟶ S₂) :
    QuasiIso φ ↔ IsIso (homologyMap φ) := by
  constructor
  . intro h
    infer_instance
  . intro h
    exact ⟨h⟩

instance quasiIso_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ] : QuasiIso φ :=
  ⟨IsIso.of_iso (homologyMapIso (asIso φ))⟩

lemma quasiIso_comp' (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) (hφ : QuasiIso φ) (hφ' : QuasiIso φ') :
    QuasiIso (φ ≫ φ') := by
  rw [quasiIso_iff] at hφ hφ' ⊢
  rw [homologyMap_comp]
  infer_instance

instance quasiIso_comp (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [QuasiIso φ] [QuasiIso φ'] :
    QuasiIso (φ ≫ φ') :=
  quasiIso_comp' φ φ' inferInstance inferInstance

lemma quasiIso_of_comp_left' (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃)
    (hφ : QuasiIso φ) (hφφ' : QuasiIso (φ ≫ φ')) :
    QuasiIso φ' := by
  rw [quasiIso_iff] at hφ hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_left (homologyMap φ) (homologyMap φ')

lemma quasiIso_of_comp_left (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃)
    [QuasiIso φ] [QuasiIso (φ ≫ φ')] :
    QuasiIso φ' :=
  quasiIso_of_comp_left' φ φ' inferInstance inferInstance

lemma quasiIso_iff_comp_left' (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) (hφ : QuasiIso φ) :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ' := by
  constructor
  . exact quasiIso_of_comp_left' φ φ' hφ
  . exact quasiIso_comp' φ φ' hφ

@[simp]
lemma quasiIso_iff_comp_left (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [QuasiIso φ] :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ' :=
  quasiIso_iff_comp_left' φ φ' inferInstance

lemma quasiIso_of_comp_right' (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃)
    (hφ' : QuasiIso φ') (hφφ' : QuasiIso (φ ≫ φ')) :
    QuasiIso φ := by
  rw [quasiIso_iff] at hφ' hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_right (homologyMap φ) (homologyMap φ')

lemma quasiIso_iff_comp_right' (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) (hφ' : QuasiIso φ') :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ := by
  constructor
  . exact quasiIso_of_comp_right' φ φ' hφ'
  . intro hφ
    exact quasiIso_comp' φ φ' hφ hφ'

@[simp]
lemma quasiIso_iff_comp_right (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃) [QuasiIso φ'] :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ :=
  quasiIso_iff_comp_right' φ φ' inferInstance

lemma quasiIso_of_comp_right (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃)
    [QuasiIso φ'] [QuasiIso (φ ≫ φ')] :
    QuasiIso φ :=
  quasiIso_of_comp_right' φ φ' inferInstance inferInstance

lemma quasiIso_of_arrow_mk_iso' (φ : S₁ ⟶ S₂) (φ' : S₃ ⟶ S₄) (e : Arrow.mk φ ≅ Arrow.mk φ')
    (hφ : QuasiIso φ) : QuasiIso φ' := by
  let α : S₃ ⟶ S₁ := e.inv.left
  let β : S₂ ⟶ S₄ := e.hom.right
  suffices φ' = α ≫ φ ≫ β by
    rw [this]
    infer_instance
  simp only [Arrow.w_mk_right_assoc, Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom,
    ← Arrow.comp_right, e.inv_hom_id, Arrow.id_right, comp_id]

lemma quasiIso_of_arrow_mk_iso (φ : S₁ ⟶ S₂) (φ' : S₃ ⟶ S₄) (e : Arrow.mk φ ≅ Arrow.mk φ')
    [QuasiIso φ] : QuasiIso φ' :=
  quasiIso_of_arrow_mk_iso' φ φ' e inferInstance

lemma quasiIso_iff_of_arrow_mk_iso (φ : S₁ ⟶ S₂) (φ' : S₃ ⟶ S₄) (e : Arrow.mk φ ≅ Arrow.mk φ') :
    QuasiIso φ ↔ QuasiIso φ' :=
  ⟨quasiIso_of_arrow_mk_iso' φ φ' e, quasiIso_of_arrow_mk_iso' φ' φ e.symm⟩

lemma LeftHomologyMapData.quasiIso_iff {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData}
    {h₂ : S₂.LeftHomologyData} (γ : LeftHomologyMapData φ h₁ h₂) :
    QuasiIso φ ↔ IsIso γ.φH := by
  rw [ShortComplex.quasiIso_iff, γ.homologyMap_eq]
  constructor
  . intro h
    haveI : IsIso (γ.φH ≫ (LeftHomologyData.homologyIso h₂).inv) :=
      IsIso.of_isIso_comp_left (LeftHomologyData.homologyIso h₁).hom _
    exact IsIso.of_isIso_comp_right _ (LeftHomologyData.homologyIso h₂).inv
  . intro h
    infer_instance

lemma RightHomologyMapData.quasiIso_iff {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData}
    {h₂ : S₂.RightHomologyData} (γ : RightHomologyMapData φ h₁ h₂) :
    QuasiIso φ ↔ IsIso γ.φH := by
  rw [ShortComplex.quasiIso_iff, γ.homologyMap_eq]
  constructor
  . intro h
    haveI : IsIso (γ.φH ≫ (RightHomologyData.homologyIso h₂).inv) :=
      IsIso.of_isIso_comp_left (RightHomologyData.homologyIso h₁).hom _
    exact IsIso.of_isIso_comp_right _ (RightHomologyData.homologyIso h₂).inv
  . intro h
    infer_instance

lemma HomologyMapData.quasiIso_iff' {φ : S₁ ⟶ S₂} (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)
    (γ : HomologyMapData φ h₁ h₂) :
    IsIso γ.left.φH ↔ IsIso γ.right.φH := by
  rw [← γ.left.quasiIso_iff, ← γ.right.quasiIso_iff]

lemma quasiIso_iff_isIso_leftHomologyMap' (φ : S₁ ⟶ S₂)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    QuasiIso φ ↔ IsIso (leftHomologyMap' φ h₁ h₂) := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  rw [γ.quasiIso_iff, γ.leftHomologyMap'_eq]

lemma quasiIso_iff_isIso_rightHomologyMap' (φ : S₁ ⟶ S₂)
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    QuasiIso φ ↔ IsIso (rightHomologyMap' φ h₁ h₂) := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  rw [γ.quasiIso_iff, γ.rightHomologyMap'_eq]

lemma quasiIso_iff_isIso_homologyMap' (φ : S₁ ⟶ S₂)
    (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    QuasiIso φ ↔ IsIso (homologyMap' φ h₁ h₂) :=
  quasiIso_iff_isIso_leftHomologyMap' _ _ _

lemma quasiIso_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    QuasiIso φ := by
  rw [((LeftHomologyMapData.ofEpiOfIsIsoOfMono φ) S₁.leftHomologyData).quasiIso_iff]
  dsimp
  infer_instance

lemma quasiIso_opMap_iff (φ : S₁ ⟶ S₂) :
    QuasiIso (opMap φ) ↔ QuasiIso φ := by
  have γ : HomologyMapData φ S₁.homologyData S₂.homologyData := default
  rw [γ.left.quasiIso_iff, γ.op.right.quasiIso_iff]
  dsimp
  constructor
  . intro h
    apply isIso_of_op
  . intro h
    infer_instance

lemma quasiIso_opMap (φ : S₁ ⟶ S₂) [QuasiIso φ] :
    QuasiIso (opMap φ) := by
  rw [quasiIso_opMap_iff]
  infer_instance

lemma quasiIso_unopMap {S₁ S₂ : ShortComplex Cᵒᵖ} [S₁.HasHomology] [S₂.HasHomology]
    [S₁.unop.HasHomology] [S₂.unop.HasHomology]
    (φ : S₁ ⟶ S₂) [QuasiIso φ] : QuasiIso (unopMap φ) := by
  rw [← quasiIso_opMap_iff]
  change QuasiIso φ
  infer_instance

end ShortComplex

end CategoryTheory
