/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms

#align_import number_theory.modular_forms.basic from "leanprover-community/mathlib"@"57f9349f2fe19d2de7207e99b0341808d977cdcf"

/-!
# Modular forms

This file defines modular forms and proves some basic properties about them.

We begin by defining modular forms and cusp forms as extension of `SlashInvariantForm`s then we
define the space of modular forms, cusp forms and prove that the product of two modular forms is a
modular form.
-/

open Complex UpperHalfPlane

open scoped Topology Manifold UpperHalfPlane

noncomputable section

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

section ModularForm

open ModularForm

variable (F : Type*) (Γ : Subgroup SL(2, ℤ)) (k : ℤ)

open scoped ModularForm

/-- These are `SlashInvariantForm`'s that are holomophic and bounded at infinity. -/
structure ModularForm extends SlashInvariantForm Γ k where
  holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (toSlashInvariantForm : ℍ → ℂ)
  bdd_at_infty' : ∀ A : SL(2, ℤ), IsBoundedAtImInfty (toSlashInvariantForm ∣[k] A)

/-- The `SlashInvariantForm` associated to a `ModularForm`. -/
add_decl_doc ModularForm.toSlashInvariantForm

/-- These are `SlashInvariantForm`s that are holomophic and zero at infinity. -/
structure CuspForm extends SlashInvariantForm Γ k where
  holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (toSlashInvariantForm : ℍ → ℂ)
  zero_at_infty' : ∀ A : SL(2, ℤ), IsZeroAtImInfty (toSlashInvariantForm ∣[k] A)

/-- The `SlashInvariantForm` associated to a `CuspForm`. -/
add_decl_doc CuspForm.toSlashInvariantForm

/-- `ModularFormClass F Γ k` says that `F` is a type of bundled functions that extend
`SlashInvariantFormClass` by requiring that the functions be holomorphic and bounded
at infinity. -/
class ModularFormClass (F : Type*) (Γ : outParam <| Subgroup (SL(2, ℤ))) (k : outParam ℤ)
    extends SlashInvariantFormClass F Γ k where
  holo : ∀ f : F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f : ℍ → ℂ)
  bdd_at_infty : ∀ (f : F) (A : SL(2, ℤ)), IsBoundedAtImInfty (f ∣[k] A)

/-- `CuspFormClass F Γ k` says that `F` is a type of bundled functions that extend
`SlashInvariantFormClass` by requiring that the functions be holomorphic and zero
at infinity. -/
class CuspFormClass (F : Type*) (Γ : outParam <| Subgroup (SL(2, ℤ))) (k : outParam ℤ)
    extends SlashInvariantFormClass F Γ k where
  holo : ∀ f : F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f : ℍ → ℂ)
  zero_at_infty : ∀ (f : F) (A : SL(2, ℤ)), IsZeroAtImInfty (f ∣[k] A)

instance (priority := 100) ModularFormClass.modularForm :
    ModularFormClass (ModularForm Γ k) Γ k where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr; exact FunLike.ext' h
  slash_action_eq f := f.slash_action_eq'
  holo := ModularForm.holo'
  bdd_at_infty := ModularForm.bdd_at_infty'

instance (priority := 100) CuspFormClass.cuspForm : CuspFormClass (CuspForm Γ k) Γ k where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr; exact FunLike.ext' h
  slash_action_eq f := f.slash_action_eq'
  holo := CuspForm.holo'
  zero_at_infty := CuspForm.zero_at_infty'

variable {F Γ k}

theorem ModularForm.toFun_eq_coe (f : ModularForm Γ k) : f.toFun = (f : ℍ → ℂ) :=
  rfl

@[simp]
theorem ModularForm.toSlashInvariantForm_coe (f : ModularForm Γ k) : ⇑f.1 = f :=
  rfl

theorem CuspForm.toFun_eq_coe {f : CuspForm Γ k} : f.toFun = (f : ℍ → ℂ) :=
  rfl

@[simp]
theorem CuspForm.toSlashInvariantForm_coe (f : CuspForm Γ k) : ⇑f.1 = f := rfl

@[ext]
theorem ModularForm.ext {f g : ModularForm Γ k} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h

@[ext]
theorem CuspForm.ext {f g : CuspForm Γ k} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h

/-- Copy of a `ModularForm` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def ModularForm.copy (f : ModularForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) :
    ModularForm Γ k where
  toSlashInvariantForm := f.1.copy f' h
  holo' := h.symm ▸ f.holo'
  bdd_at_infty' A := h.symm ▸ f.bdd_at_infty' A

/-- Copy of a `CuspForm` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def CuspForm.copy (f : CuspForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) : CuspForm Γ k where
  toSlashInvariantForm := f.1.copy f' h
  holo' := h.symm ▸ f.holo'
  zero_at_infty' A := h.symm ▸ f.zero_at_infty' A

end ModularForm

namespace ModularForm

open SlashInvariantForm

variable {F : Type*} {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

instance add : Add (ModularForm Γ k) :=
  ⟨fun f g =>
    { toSlashInvariantForm := f + g
      holo' := f.holo'.add g.holo'
      bdd_at_infty' := fun A => by simpa using (f.bdd_at_infty' A).add (g.bdd_at_infty' A) }⟩

@[simp]
theorem coe_add (f g : ModularForm Γ k) : ⇑(f + g) = f + g :=
  rfl

@[simp]
theorem add_apply (f g : ModularForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
  rfl

instance instZero : Zero (ModularForm Γ k) :=
  ⟨ { toSlashInvariantForm := 0
      holo' := fun _ => mdifferentiableAt_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      bdd_at_infty' := fun A => by simpa using zero_form_isBoundedAtImInfty } ⟩

@[simp]
theorem coe_zero : ⇑(0 : ModularForm Γ k) = (0 : ℍ → ℂ) :=
  rfl

@[simp]
theorem zero_apply (z : ℍ) : (0 : ModularForm Γ k) z = 0 :=
  rfl

section

variable {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ]

instance instSMul : SMul α (ModularForm Γ k) :=
  ⟨fun c f =>
    { toSlashInvariantForm := c • f.1
      holo' := by simpa using f.holo'.const_smul (c • (1 : ℂ))
      bdd_at_infty' := fun A => by simpa using (f.bdd_at_infty' A).const_smul_left (c • (1 : ℂ)) }⟩

@[simp]
theorem coe_smul (f : ModularForm Γ k) (n : α) : ⇑(n • f) = n • ⇑f :=
  rfl

@[simp]
theorem smul_apply (f : ModularForm Γ k) (n : α) (z : ℍ) : (n • f) z = n • f z :=
  rfl

end

instance instNeg : Neg (ModularForm Γ k) :=
  ⟨fun f =>
    { toSlashInvariantForm := -f.1
      holo' := f.holo'.neg
      bdd_at_infty' := fun A => by simpa using (f.bdd_at_infty' A).neg }⟩

@[simp]
theorem coe_neg (f : ModularForm Γ k) : ⇑(-f) = -f :=
  rfl

@[simp]
theorem neg_apply (f : ModularForm Γ k) (z : ℍ) : (-f) z = -f z :=
  rfl

instance instSub : Sub (ModularForm Γ k) :=
  ⟨fun f g => f + -g⟩

@[simp]
theorem coe_sub (f g : ModularForm Γ k) : ⇑(f - g) = f - g :=
  rfl

@[simp]
theorem sub_apply (f g : ModularForm Γ k) (z : ℍ) : (f - g) z = f z - g z :=
  rfl

instance : AddCommGroup (ModularForm Γ k) :=
  FunLike.coe_injective.addCommGroup _ rfl coe_add coe_neg coe_sub coe_smul coe_smul

/-- Additive coercion from `ModularForm` to `ℍ → ℂ`. -/
@[simps]
def coeHom : ModularForm Γ k →+ ℍ → ℂ where
  toFun f := f
  map_zero' := coe_zero
  map_add' _ _ := rfl

instance : Module ℂ (ModularForm Γ k) :=
  Function.Injective.module ℂ coeHom FunLike.coe_injective fun _ _ => rfl

instance : Inhabited (ModularForm Γ k) :=
  ⟨0⟩

/-- The modular form of weight `k_1 + k_2` given by the product of two modular forms of weights
`k_1` and `k_2`. -/
def mul {k_1 k_2 : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : ModularForm Γ k_1) (g : ModularForm Γ k_2) :
    ModularForm Γ (k_1 + k_2) where
  toSlashInvariantForm := f.1.mul g.1
  holo' := f.holo'.mul g.holo'
  bdd_at_infty' A := by
    -- porting note: was `by simpa using ...`
    -- `mul_slash_SL2` is no longer a `simp` and `simpa only [mul_slash_SL2] using ...` failed
    rw [SlashInvariantForm.coe_mul, mul_slash_SL2]
    exact (f.bdd_at_infty' A).mul (g.bdd_at_infty' A)

@[simp]
theorem mul_coe {k_1 k_2 : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : ModularForm Γ k_1)
    (g : ModularForm Γ k_2) : (f.mul g : ℍ → ℂ) = f * g :=
  rfl

instance : One (ModularForm Γ 0) :=
  ⟨ { toSlashInvariantForm := 1
      holo' := fun x => mdifferentiableAt_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      bdd_at_infty' := fun A => by
        simpa only [SlashInvariantForm.one_coe_eq_one,
          ModularForm.is_invariant_one] using atImInfty.const_boundedAtFilter (1 : ℂ) }⟩

@[simp]
theorem one_coe_eq_one : ((1 : ModularForm Γ 0) : ℍ → ℂ) = 1 :=
  rfl

end ModularForm

namespace CuspForm

open ModularForm

variable {F : Type*} {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

instance hasAdd : Add (CuspForm Γ k) :=
  ⟨fun f g =>
    { toSlashInvariantForm := f + g
      holo' := f.holo'.add g.holo'
      zero_at_infty' := fun A => by simpa using (f.zero_at_infty' A).add (g.zero_at_infty' A) }⟩

@[simp]
theorem coe_add (f g : CuspForm Γ k) : ⇑(f + g) = f + g :=
  rfl

@[simp]
theorem add_apply (f g : CuspForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
  rfl

instance instZero : Zero (CuspForm Γ k) :=
  ⟨ { toSlashInvariantForm := 0
      holo' := fun _ => mdifferentiableAt_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      zero_at_infty' := by simpa using Filter.zero_zeroAtFilter _ } ⟩

@[simp]
theorem coe_zero : ⇑(0 : CuspForm Γ k) = (0 : ℍ → ℂ) :=
  rfl

@[simp]
theorem zero_apply (z : ℍ) : (0 : CuspForm Γ k) z = 0 :=
  rfl

section

variable {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ]

instance instSMul : SMul α (CuspForm Γ k) :=
  ⟨fun c f =>
    { toSlashInvariantForm := c • f.1
      holo' := by simpa using f.holo'.const_smul (c • (1 : ℂ))
      zero_at_infty' := fun A => by simpa using (f.zero_at_infty' A).smul (c • (1 : ℂ)) }⟩

@[simp]
theorem coe_smul (f : CuspForm Γ k) (n : α) : ⇑(n • f) = n • ⇑f :=
  rfl

@[simp]
theorem smul_apply (f : CuspForm Γ k) (n : α) {z : ℍ} : (n • f) z = n • f z :=
  rfl

end

instance instNeg : Neg (CuspForm Γ k) :=
  ⟨fun f =>
    { toSlashInvariantForm := -f.1
      holo' := f.holo'.neg
      zero_at_infty' := fun A => by simpa using (f.zero_at_infty' A).neg }⟩

@[simp]
theorem coe_neg (f : CuspForm Γ k) : ⇑(-f) = -f :=
  rfl

@[simp]
theorem neg_apply (f : CuspForm Γ k) (z : ℍ) : (-f) z = -f z :=
  rfl

instance instSub : Sub (CuspForm Γ k) :=
  ⟨fun f g => f + -g⟩

@[simp]
theorem coe_sub (f g : CuspForm Γ k) : ⇑(f - g) = f - g :=
  rfl

@[simp]
theorem sub_apply (f g : CuspForm Γ k) (z : ℍ) : (f - g) z = f z - g z :=
  rfl

instance : AddCommGroup (CuspForm Γ k) :=
  FunLike.coe_injective.addCommGroup _ rfl coe_add coe_neg coe_sub coe_smul coe_smul

/-- Additive coercion from `CuspForm` to `ℍ → ℂ`. -/
@[simps]
def coeHom : CuspForm Γ k →+ ℍ → ℂ where
  toFun f := f
  map_zero' := CuspForm.coe_zero
  map_add' _ _ := rfl

instance : Module ℂ (CuspForm Γ k) :=
  Function.Injective.module ℂ coeHom FunLike.coe_injective fun _ _ => rfl

instance : Inhabited (CuspForm Γ k) :=
  ⟨0⟩

instance (priority := 99) [CuspFormClass F Γ k] : ModularFormClass F Γ k where
  coe := FunLike.coe
  coe_injective' := FunLike.coe_injective'
  slash_action_eq := SlashInvariantFormClass.slash_action_eq
  holo := CuspFormClass.holo
  bdd_at_infty _ _ := (CuspFormClass.zero_at_infty _ _).boundedAtFilter

end CuspForm
