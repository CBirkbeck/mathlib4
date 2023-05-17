import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.GradedType

namespace CategoryTheory

open Category Preadditive

variable {C : Type _} [Category C] (M : Type _) [AddMonoid M] [HasShift C M]

def ShiftedHom (X Y : C) : GradedType M := fun (n : M) => X ⟶ (Y⟦n⟧)

instance [Preadditive C] (X Y : C) (n : M) : AddCommGroup (ShiftedHom M X Y n) := by
  dsimp only [ShiftedHom]
  infer_instance

-- note the order of the composition (this is motivated by signs conventions)

noncomputable instance (X Y Z : C ) :
    HasGradedHSMul (ShiftedHom M Y Z) (ShiftedHom M X Y) (ShiftedHom M X Z) where
  γhsmul' p q n h α β := β ≫ α⟦q⟧' ≫ (shiftFunctorAdd' C p q n h).inv.app _

namespace ShiftedHom

variable {X Y Z : C} (f : X ⟶ Y)
variable {M}

noncomputable def mk₀ (m₀ : M) (hm₀ : m₀ = 0) :
  ShiftedHom M X Y m₀ := f ≫ (shiftFunctorZero' C m₀ hm₀).inv.app Y

noncomputable instance : One (ShiftedHom M X X 0) := ⟨mk₀ (𝟙 X) (0 : M) rfl⟩

variable (X M)

lemma one_eq : (1 : ShiftedHom M X X 0) = mk₀ (𝟙 X) 0 rfl := rfl

variable {X M}

lemma γhsmul_eq {p q : M} (α : ShiftedHom M Y Z p) (β : ShiftedHom M X Y q) (n : M)
  (hpq : p + q = n) :
  α •[hpq] β = β ≫ α⟦q⟧' ≫ (shiftFunctorAdd' C p q n hpq).inv.app _ := rfl

@[simp]
lemma mk₀_γhsmul {n : M} (g : Y ⟶ Z) (m₀ : M) (hm₀ : m₀ = 0) (β : ShiftedHom M X Y n) :
    (mk₀ g m₀ hm₀) •[show m₀ + n = n by rw [hm₀, zero_add]] β = β ≫ g⟦n⟧' := by
  subst hm₀
  simp only [mk₀, shiftFunctorZero'_eq_shiftFunctorZero, γhsmul_eq, Functor.map_comp,
    shiftFunctorAdd'_zero_add_inv_app, Functor.id_obj, assoc]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app, Functor.id_obj, comp_id]

@[simp]
lemma γhsmul_mk₀ {n : M} (α : ShiftedHom M Y Z n) (f : X ⟶ Y) (m₀ : M) (hm₀ : m₀ = 0)  :
    α •[show n + m₀ = n by rw [hm₀, add_zero]] (mk₀ f m₀ hm₀) = f ≫ α := by
  subst hm₀
  simp only [mk₀, shiftFunctorZero'_eq_shiftFunctorZero, γhsmul_eq,
    shiftFunctorAdd'_add_zero_inv_app,
    NatTrans.naturality, Functor.id_map, assoc, Iso.inv_hom_id_app_assoc]

@[simp 1100]
lemma mk₀_comp (f : X ⟶ Y) (g : Y ⟶ Z) (m m' m'' : M) (hm : m = 0) (hm' : m' = 0)
  (hm'' : m + m' = m'' ) :
    mk₀ g m hm •[hm''] mk₀ f m' hm' = mk₀ (f ≫ g) m'' (by rw [← hm'', hm, hm', zero_add]) := by
  subst hm hm'
  obtain rfl : m'' = 0 := by rw [← hm'', zero_add]
  rw [γhsmul_mk₀]
  simp [mk₀]

@[simp]
lemma mk₀_add [Preadditive C] (f₁ f₂ : X ⟶ Y) (m₀ : M) (hm₀ : m₀ = 0) :
    (mk₀ (f₁ + f₂) m₀ hm₀) = mk₀ f₁ m₀ hm₀ + mk₀ f₂ m₀ hm₀ := by
  simp [mk₀]

@[simp]
lemma one_γhsmul {n : M} (β : ShiftedHom M X Y n) :
    (1 : ShiftedHom M Y Y 0) •[zero_add n] β = β := by simp [one_eq]

@[simp 1100]
lemma one_γhsmul' {n : M} (m₀ : M) (hm₀ : m₀ = 0) (β : ShiftedHom M X Y n) :
    (mk₀ (𝟙 Y) m₀ hm₀) •[show m₀ + n = n by rw [hm₀, zero_add]] β = β := by simp

@[simp]
lemma γhsmul_one {n : M} (α : ShiftedHom M X Y n) :
    α •[add_zero n] (1 : ShiftedHom M X X 0) = α := by simp [one_eq]

@[simp 1100]
lemma γhsmul_one' {n : M} (α : ShiftedHom M X Y n) (m₀ : M) (hm₀ : m₀ = 0) :
    α  •[show n + m₀ = n by rw [hm₀, add_zero]] (mk₀ (𝟙 X) m₀ hm₀)= α := by simp

@[simp]
lemma γhsmul_add [Preadditive C] {p q n : M} (α : ShiftedHom M Y Z p) (β₁ β₂ : ShiftedHom M X Y q)
    (hpq : p + q = n) :
    α •[hpq] (β₁ + β₂) = α •[hpq] β₁ + α •[hpq] β₂ := by
  rw [γhsmul_eq, γhsmul_eq, γhsmul_eq, add_comp]

@[simp]
lemma add_γhsmul [Preadditive C] [∀ (a : M), (shiftFunctor C a).Additive]
    {p q n : M} (α₁ α₂ : ShiftedHom M Y Z p) (β : ShiftedHom M X Y q) (hpq : p + q = n) :
    (α₁ + α₂) •[hpq] β = α₁ •[hpq] β + α₂ •[hpq] β := by
  rw [γhsmul_eq, γhsmul_eq, γhsmul_eq, Functor.map_add, add_comp, comp_add]

instance {X₁ X₂ X₃ X₄ : C} : IsAssocGradedHSMul (ShiftedHom M X₃ X₄)
    (ShiftedHom M X₂ X₃) (ShiftedHom M X₁ X₂) (ShiftedHom M X₂ X₄) (ShiftedHom M X₁ X₃)
    (ShiftedHom M X₁ X₄) where
  γhsmul_assoc a b c α β γ ab bc abc hab hbc habc := by
    simp only [γhsmul_eq, assoc, Functor.map_comp,
      shiftFunctorAdd'_assoc_inv_app a b c ab bc abc hab hbc (by rw [hab, habc])]
    dsimp
    rw [← NatTrans.naturality_assoc]
    rfl

end ShiftedHom

end CategoryTheory
