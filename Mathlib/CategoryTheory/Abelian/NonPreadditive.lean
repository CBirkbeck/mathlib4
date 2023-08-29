/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Equalizers
import Mathlib.CategoryTheory.Abelian.Images
import Mathlib.CategoryTheory.Preadditive.Basic

#align_import category_theory.abelian.non_preadditive from "leanprover-community/mathlib"@"829895f162a1f29d0133f4b3538f4cd1fb5bffd3"

/-!
# Every NonPreadditiveAbelian category is preadditive

In mathlib, we define an abelian category as a preadditive category with a zero object,
kernels and cokernels, products and coproducts and in which every monomorphism and epimorphism is
normal.

While virtually every interesting abelian category has a natural preadditive structure (which is why
it is included in the definition), preadditivity is not actually needed: Every category that has
all of the other properties appearing in the definition of an abelian category admits a preadditive
structure. This is the construction we carry out in this file.

The proof proceeds in roughly five steps:
1. Prove some results (for example that all equalizers exist) that would be trivial if we already
   had the preadditive structure but are a bit of work without it.
2. Develop images and coimages to show that every monomorphism is the kernel of its cokernel.

The results of the first two steps are also useful for the "normal" development of abelian
categories, and will be used there.

3. For every object `A`, define a "subtraction" morphism `σ : A ⨯ A ⟶ A` and use it to define
   subtraction on morphisms as `f - g := prod.lift f g ≫ σ`.
4. Prove a small number of identities about this subtraction from the definition of `σ`.
5. From these identities, prove a large number of other identities that imply that defining
   `f + g := f - (0 - g)` indeed gives an abelian group structure on morphisms such that composition
   is bilinear.

The construction is non-trivial and it is quite remarkable that this abelian group structure can
be constructed purely from the existence of a few limits and colimits. Even more remarkably,
since abelian categories admit exactly one preadditive structure (see
`subsingletonPreadditiveOfHasBinaryBiproducts`), the construction manages to exactly
reconstruct any natural preadditive structure the category may have.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]

-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

section

universe v u

variable (C : Type u) [Category.{v} C]

/-- We call a category `NonPreadditiveAbelian` if it has a zero object, kernels, cokernels, binary
    products and coproducts, and every monomorphism and every epimorphism is normal. -/
class NonPreadditiveAbelian extends HasZeroMorphisms C, NormalMonoCategory C,
    NormalEpiCategory C where
  [has_zero_object : HasZeroObject C]
  [has_kernels : HasKernels C]
  [has_cokernels : HasCokernels C]
  [has_finite_products : HasFiniteProducts C]
  [has_finite_coproducts : HasFiniteCoproducts C]
#align category_theory.non_preadditive_abelian CategoryTheory.NonPreadditiveAbelian

attribute [instance] NonPreadditiveAbelian.has_zero_object

attribute [instance] NonPreadditiveAbelian.has_kernels

attribute [instance] NonPreadditiveAbelian.has_cokernels

attribute [instance] NonPreadditiveAbelian.has_finite_products

attribute [instance] NonPreadditiveAbelian.has_finite_coproducts

end

end CategoryTheory

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [NonPreadditiveAbelian C]

namespace CategoryTheory.NonPreadditiveAbelian

section Factor

variable {P Q : C} (f : P ⟶ Q)

/-- The map `p : P ⟶ image f` is an epimorphism -/
instance : Epi (Abelian.factorThruImage f) :=
  let I := Abelian.image f
  let p := Abelian.factorThruImage f
  let i := kernel.ι (cokernel.π f)
  -- It will suffice to consider some g : I ⟶ R such that p ≫ g = 0 and show that g = 0.
  NormalMonoCategory.epi_of_zero_cancel
  _ fun R (g : I ⟶ R) (hpg : p ≫ g = 0) => by
  -- Since C is abelian, u := ker g ≫ i is the kernel of some morphism h.
  let u := kernel.ι g ≫ i
  -- ⊢ g = 0
  haveI : Mono u := mono_comp _ _
  -- ⊢ g = 0
  haveI hu := normalMonoOfMono u
  -- ⊢ g = 0
  let h := hu.g
  -- ⊢ g = 0
  -- By hypothesis, p factors through the kernel of g via some t.
  obtain ⟨t, ht⟩ := kernel.lift' g p hpg
  -- ⊢ g = 0
  have fh : f ≫ h = 0
  -- ⊢ f ≫ h = 0
  calc
    f ≫ h = (p ≫ i) ≫ h := (Abelian.image.fac f).symm ▸ rfl
    _ = ((t ≫ kernel.ι g) ≫ i) ≫ h := (ht ▸ rfl)
    _ = t ≫ u ≫ h := by simp only [Category.assoc]
    _ = t ≫ 0 := (hu.w ▸ rfl)
    _ = 0 := HasZeroMorphisms.comp_zero _ _
  -- h factors through the cokernel of f via some l.
  obtain ⟨l, hl⟩ := cokernel.desc' f h fh
  -- ⊢ g = 0
  have hih : i ≫ h = 0
  -- ⊢ i ≫ h = 0
  calc
    i ≫ h = i ≫ cokernel.π f ≫ l := hl ▸ rfl
    _ = 0 ≫ l := by rw [← Category.assoc, kernel.condition]
    _ = 0 := zero_comp
  -- i factors through u = ker h via some s.
  obtain ⟨s, hs⟩ := NormalMono.lift' u i hih
  -- ⊢ g = 0
  have hs' : (s ≫ kernel.ι g) ≫ i = 𝟙 I ≫ i := by rw [Category.assoc, hs, Category.id_comp]
  -- ⊢ g = 0
  haveI : Epi (kernel.ι g) := epi_of_epi_fac ((cancel_mono _).1 hs')
  -- ⊢ g = 0
  -- ker g is an epimorphism, but ker g ≫ g = 0 = ker g ≫ 0, so g = 0 as required.
  exact zero_of_epi_comp _ (kernel.condition g)
  -- 🎉 no goals

instance isIso_factorThruImage [Mono f] : IsIso (Abelian.factorThruImage f) :=
  isIso_of_mono_of_epi <| Abelian.factorThruImage f
#align category_theory.non_preadditive_abelian.is_iso_factor_thru_image CategoryTheory.NonPreadditiveAbelian.isIso_factorThruImage

/-- The canonical morphism `i : coimage f ⟶ Q` is a monomorphism -/
instance : Mono (Abelian.factorThruCoimage f) :=
  let I := Abelian.coimage f
  let i := Abelian.factorThruCoimage f
  let p := cokernel.π (kernel.ι f)
  NormalEpiCategory.mono_of_cancel_zero _ fun R (g : R ⟶ I) (hgi : g ≫ i = 0) => by
    -- Since C is abelian, u := p ≫ coker g is the cokernel of some morphism h.
    let u := p ≫ cokernel.π g
    -- ⊢ g = 0
    haveI : Epi u := epi_comp _ _
    -- ⊢ g = 0
    haveI hu := normalEpiOfEpi u
    -- ⊢ g = 0
    let h := hu.g
    -- ⊢ g = 0
    -- By hypothesis, i factors through the cokernel of g via some t.
    obtain ⟨t, ht⟩ := cokernel.desc' g i hgi
    -- ⊢ g = 0
    have hf : h ≫ f = 0
    -- ⊢ h ≫ f = 0
    calc
      h ≫ f = h ≫ p ≫ i := (Abelian.coimage.fac f).symm ▸ rfl
      _ = h ≫ p ≫ cokernel.π g ≫ t := (ht ▸ rfl)
      _ = h ≫ u ≫ t := by simp only [Category.assoc]
      _ = 0 ≫ t := by rw [← Category.assoc, hu.w]
      _ = 0 := zero_comp
    -- h factors through the kernel of f via some l.
    obtain ⟨l, hl⟩ := kernel.lift' f h hf
    -- ⊢ g = 0
    have hhp : h ≫ p = 0
    -- ⊢ h ≫ p = 0
    calc
      h ≫ p = (l ≫ kernel.ι f) ≫ p := hl ▸ rfl
      _ = l ≫ 0 := by rw [Category.assoc, cokernel.condition]
      _ = 0 := comp_zero
    -- p factors through u = coker h via some s.
    obtain ⟨s, hs⟩ := NormalEpi.desc' u p hhp
    -- ⊢ g = 0
    have hs' : p ≫ cokernel.π g ≫ s = p ≫ 𝟙 I := by rw [← Category.assoc, hs, Category.comp_id]
    -- ⊢ g = 0
    haveI : Mono (cokernel.π g) := mono_of_mono_fac ((cancel_epi _).1 hs')
    -- ⊢ g = 0
    -- coker g is a monomorphism, but g ≫ coker g = 0 = 0 ≫ coker g, so g = 0 as required.
    exact zero_of_comp_mono _ (cokernel.condition g)
    -- 🎉 no goals

instance isIso_factorThruCoimage [Epi f] : IsIso (Abelian.factorThruCoimage f) :=
  isIso_of_mono_of_epi _
#align category_theory.non_preadditive_abelian.is_iso_factor_thru_coimage CategoryTheory.NonPreadditiveAbelian.isIso_factorThruCoimage

end Factor

section CokernelOfKernel

variable {X Y : C} {f : X ⟶ Y}

/-- In a `NonPreadditiveAbelian` category, an epi is the cokernel of its kernel. More precisely:
    If `f` is an epimorphism and `s` is some limit kernel cone on `f`, then `f` is a cokernel
    of `Fork.ι s`. -/
def epiIsCokernelOfKernel [Epi f] (s : Fork f 0) (h : IsLimit s) :
    IsColimit (CokernelCofork.ofπ f (KernelFork.condition s)) :=
  IsCokernel.cokernelIso _ _
    (cokernel.ofIsoComp _ _ (Limits.IsLimit.conePointUniqueUpToIso (limit.isLimit _) h)
      (ConeMorphism.w (Limits.IsLimit.uniqueUpToIso (limit.isLimit _) h).hom _))
    (asIso <| Abelian.factorThruCoimage f) (Abelian.coimage.fac f)
#align category_theory.non_preadditive_abelian.epi_is_cokernel_of_kernel CategoryTheory.NonPreadditiveAbelian.epiIsCokernelOfKernel

/-- In a `NonPreadditiveAbelian` category, a mono is the kernel of its cokernel. More precisely:
    If `f` is a monomorphism and `s` is some colimit cokernel cocone on `f`, then `f` is a kernel
    of `Cofork.π s`. -/
def monoIsKernelOfCokernel [Mono f] (s : Cofork f 0) (h : IsColimit s) :
    IsLimit (KernelFork.ofι f (CokernelCofork.condition s)) :=
  IsKernel.isoKernel _ _
    (kernel.ofCompIso _ _ (Limits.IsColimit.coconePointUniqueUpToIso h (colimit.isColimit _))
      (CoconeMorphism.w (Limits.IsColimit.uniqueUpToIso h <| colimit.isColimit _).hom _))
    (asIso <| Abelian.factorThruImage f) (Abelian.image.fac f)
#align category_theory.non_preadditive_abelian.mono_is_kernel_of_cokernel CategoryTheory.NonPreadditiveAbelian.monoIsKernelOfCokernel

end CokernelOfKernel

section

/-- The composite `A ⟶ A ⨯ A ⟶ cokernel (Δ A)`, where the first map is `(𝟙 A, 0)` and the second map
    is the canonical projection into the cokernel. -/
abbrev r (A : C) : A ⟶ cokernel (diag A) :=
  prod.lift (𝟙 A) 0 ≫ cokernel.π (diag A)
#align category_theory.non_preadditive_abelian.r CategoryTheory.NonPreadditiveAbelian.r

instance mono_Δ {A : C} : Mono (diag A) :=
  mono_of_mono_fac <| prod.lift_fst _ _
#align category_theory.non_preadditive_abelian.mono_Δ CategoryTheory.NonPreadditiveAbelian.mono_Δ

instance mono_r {A : C} : Mono (r A) := by
  let hl : IsLimit (KernelFork.ofι (diag A) (cokernel.condition (diag A))) :=
    monoIsKernelOfCokernel _ (colimit.isColimit _)
  apply NormalEpiCategory.mono_of_cancel_zero
  -- ⊢ ∀ (Z : C) (g : Z ⟶ A), g ≫ r A = 0 → g = 0
  intro Z x hx
  -- ⊢ x = 0
  have hxx : (x ≫ prod.lift (𝟙 A) (0 : A ⟶ A)) ≫ cokernel.π (diag A) = 0 := by
    rw [Category.assoc, hx]
  obtain ⟨y, hy⟩ := KernelFork.IsLimit.lift' hl _ hxx
  -- ⊢ x = 0
  rw [KernelFork.ι_ofι] at hy
  -- ⊢ x = 0
  have hyy : y = 0 := by
    erw [← Category.comp_id y, ← Limits.prod.lift_snd (𝟙 A) (𝟙 A), ← Category.assoc, hy,
      Category.assoc, prod.lift_snd, HasZeroMorphisms.comp_zero]
  haveI : Mono (prod.lift (𝟙 A) (0 : A ⟶ A)) := mono_of_mono_fac (prod.lift_fst _ _)
  -- ⊢ x = 0
  apply (cancel_mono (prod.lift (𝟙 A) (0 : A ⟶ A))).1
  -- ⊢ x ≫ prod.lift (𝟙 A) 0 = 0 ≫ prod.lift (𝟙 A) 0
  rw [← hy, hyy, zero_comp, zero_comp]
  -- 🎉 no goals
#align category_theory.non_preadditive_abelian.mono_r CategoryTheory.NonPreadditiveAbelian.mono_r

instance epi_r {A : C} : Epi (r A) := by
  have hlp : prod.lift (𝟙 A) (0 : A ⟶ A) ≫ Limits.prod.snd = 0 := prod.lift_snd _ _
  -- ⊢ Epi (r A)
  let hp1 : IsLimit (KernelFork.ofι (prod.lift (𝟙 A) (0 : A ⟶ A)) hlp) := by
    refine' Fork.IsLimit.mk _ (fun s => Fork.ι s ≫ Limits.prod.fst) _ _
    · intro s
      apply prod.hom_ext <;> simp
    · intro s m h
      haveI : Mono (prod.lift (𝟙 A) (0 : A ⟶ A)) := mono_of_mono_fac (prod.lift_fst _ _)
      apply (cancel_mono (prod.lift (𝟙 A) (0 : A ⟶ A))).1
      convert h
      apply prod.hom_ext <;> simp
  let hp2 : IsColimit (CokernelCofork.ofπ (Limits.prod.snd : A ⨯ A ⟶ A) hlp) :=
    epiIsCokernelOfKernel _ hp1
  apply NormalMonoCategory.epi_of_zero_cancel
  -- ⊢ ∀ (Z : C) (g : cokernel (diag A) ⟶ Z), r A ≫ g = 0 → g = 0
  intro Z z hz
  -- ⊢ z = 0
  have h : prod.lift (𝟙 A) (0 : A ⟶ A) ≫ cokernel.π (diag A) ≫ z = 0 := by rw [← Category.assoc, hz]
  -- ⊢ z = 0
  obtain ⟨t, ht⟩ := CokernelCofork.IsColimit.desc' hp2 _ h
  -- ⊢ z = 0
  rw [CokernelCofork.π_ofπ] at ht
  -- ⊢ z = 0
  have htt : t = 0 := by
    rw [← Category.id_comp t]
    change 𝟙 A ≫ t = 0
    rw [← Limits.prod.lift_snd (𝟙 A) (𝟙 A), Category.assoc, ht, ← Category.assoc,
      cokernel.condition, zero_comp]
  apply (cancel_epi (cokernel.π (diag A))).1
  -- ⊢ cokernel.π (diag A) ≫ z = cokernel.π (diag A) ≫ 0
  rw [← ht, htt, comp_zero, comp_zero]
  -- 🎉 no goals
#align category_theory.non_preadditive_abelian.epi_r CategoryTheory.NonPreadditiveAbelian.epi_r

instance isIso_r {A : C} : IsIso (r A) :=
  isIso_of_mono_of_epi _
#align category_theory.non_preadditive_abelian.is_iso_r CategoryTheory.NonPreadditiveAbelian.isIso_r

/-- The composite `A ⨯ A ⟶ cokernel (diag A) ⟶ A` given by the natural projection into the cokernel
    followed by the inverse of `r`. In the category of modules, using the normal kernels and
    cokernels, this map is equal to the map `(a, b) ↦ a - b`, hence the name `σ` for
    "subtraction". -/
abbrev σ {A : C} : A ⨯ A ⟶ A :=
  cokernel.π (diag A) ≫ inv (r A)
#align category_theory.non_preadditive_abelian.σ CategoryTheory.NonPreadditiveAbelian.σ

end

-- Porting note: simp can prove these
@[reassoc]
theorem diag_σ {X : C} : diag X ≫ σ = 0 := by rw [cokernel.condition_assoc, zero_comp]
                                              -- 🎉 no goals
#align category_theory.non_preadditive_abelian.diag_σ CategoryTheory.NonPreadditiveAbelian.diag_σ

@[reassoc (attr := simp)]
theorem lift_σ {X : C} : prod.lift (𝟙 X) 0 ≫ σ = 𝟙 X := by rw [← Category.assoc, IsIso.hom_inv_id]
                                                           -- 🎉 no goals
#align category_theory.non_preadditive_abelian.lift_σ CategoryTheory.NonPreadditiveAbelian.lift_σ

@[reassoc]
theorem lift_map {X Y : C} (f : X ⟶ Y) :
    prod.lift (𝟙 X) 0 ≫ Limits.prod.map f f = f ≫ prod.lift (𝟙 Y) 0 := by simp
                                                                          -- 🎉 no goals
#align category_theory.non_preadditive_abelian.lift_map CategoryTheory.NonPreadditiveAbelian.lift_map

/-- σ is a cokernel of Δ X. -/
def isColimitσ {X : C} : IsColimit (CokernelCofork.ofπ (σ : X ⨯ X ⟶ X) diag_σ) :=
  cokernel.cokernelIso _ σ (asIso (r X)).symm (by rw [Iso.symm_hom, asIso_inv])
                                                  -- 🎉 no goals
#align category_theory.non_preadditive_abelian.is_colimit_σ CategoryTheory.NonPreadditiveAbelian.isColimitσ

/-- This is the key identity satisfied by `σ`. -/
theorem σ_comp {X Y : C} (f : X ⟶ Y) : σ ≫ f = Limits.prod.map f f ≫ σ := by
  obtain ⟨g, hg⟩ :=
    CokernelCofork.IsColimit.desc' isColimitσ (Limits.prod.map f f ≫ σ) (by
      rw [prod.diag_map_assoc, diag_σ, comp_zero])
  suffices hfg : f = g
  -- ⊢ σ ≫ f = prod.map f f ≫ σ
  · rw [← hg, Cofork.π_ofπ, hfg]
    -- 🎉 no goals
  calc
    f = f ≫ prod.lift (𝟙 Y) 0 ≫ σ := by rw [lift_σ, Category.comp_id]
    _ = prod.lift (𝟙 X) 0 ≫ Limits.prod.map f f ≫ σ := by rw [lift_map_assoc]
    _ = prod.lift (𝟙 X) 0 ≫ σ ≫ g := by rw [← hg, CokernelCofork.π_ofπ]
    _ = g := by rw [← Category.assoc, lift_σ, Category.id_comp]
#align category_theory.non_preadditive_abelian.σ_comp CategoryTheory.NonPreadditiveAbelian.σ_comp

section

-- We write `f - g` for `prod.lift f g ≫ σ`.
/-- Subtraction of morphisms in a `NonPreadditiveAbelian` category. -/
def hasSub {X Y : C} : Sub (X ⟶ Y) :=
  ⟨fun f g => prod.lift f g ≫ σ⟩
#align category_theory.non_preadditive_abelian.has_sub CategoryTheory.NonPreadditiveAbelian.hasSub

attribute [local instance] hasSub

-- We write `-f` for `0 - f`.
/-- Negation of morphisms in a `NonPreadditiveAbelian` category. -/
def hasNeg {X Y : C} : Neg (X ⟶ Y) where
  neg := fun f => 0 - f
#align category_theory.non_preadditive_abelian.has_neg CategoryTheory.NonPreadditiveAbelian.hasNeg

attribute [local instance] hasNeg

-- We write `f + g` for `f - (-g)`.
/-- Addition of morphisms in a `NonPreadditiveAbelian` category. -/
def hasAdd {X Y : C} : Add (X ⟶ Y) :=
  ⟨fun f g => f - -g⟩
#align category_theory.non_preadditive_abelian.has_add CategoryTheory.NonPreadditiveAbelian.hasAdd

attribute [local instance] hasAdd

theorem sub_def {X Y : C} (a b : X ⟶ Y) : a - b = prod.lift a b ≫ σ := rfl
#align category_theory.non_preadditive_abelian.sub_def CategoryTheory.NonPreadditiveAbelian.sub_def

theorem add_def {X Y : C} (a b : X ⟶ Y) : a + b = a - -b := rfl
#align category_theory.non_preadditive_abelian.add_def CategoryTheory.NonPreadditiveAbelian.add_def

theorem neg_def {X Y : C} (a : X ⟶ Y) : -a = 0 - a := rfl
#align category_theory.non_preadditive_abelian.neg_def CategoryTheory.NonPreadditiveAbelian.neg_def

theorem sub_zero {X Y : C} (a : X ⟶ Y) : a - 0 = a := by
  rw [sub_def]
  -- ⊢ prod.lift a 0 ≫ σ = a
  conv_lhs =>
    congr; congr; rw [← Category.comp_id a]
    case a.g => rw [show 0 = a ≫ (0 : Y ⟶ Y) by simp]
  rw [← prod.comp_lift, Category.assoc, lift_σ, Category.comp_id]
  -- 🎉 no goals
#align category_theory.non_preadditive_abelian.sub_zero CategoryTheory.NonPreadditiveAbelian.sub_zero

theorem sub_self {X Y : C} (a : X ⟶ Y) : a - a = 0 := by
  rw [sub_def, ← Category.comp_id a, ← prod.comp_lift, Category.assoc, diag_σ, comp_zero]
  -- 🎉 no goals
#align category_theory.non_preadditive_abelian.sub_self CategoryTheory.NonPreadditiveAbelian.sub_self

theorem lift_sub_lift {X Y : C} (a b c d : X ⟶ Y) :
    prod.lift a b - prod.lift c d = prod.lift (a - c) (b - d) := by
  simp only [sub_def]
  -- ⊢ prod.lift (prod.lift a b) (prod.lift c d) ≫ σ = prod.lift (prod.lift a c ≫ σ …
  ext
  -- ⊢ (prod.lift (prod.lift a b) (prod.lift c d) ≫ σ) ≫ prod.fst = prod.lift (prod …
  · rw [Category.assoc, σ_comp, prod.lift_map_assoc, prod.lift_fst, prod.lift_fst, prod.lift_fst]
    -- 🎉 no goals
  · rw [Category.assoc, σ_comp, prod.lift_map_assoc, prod.lift_snd, prod.lift_snd, prod.lift_snd]
    -- 🎉 no goals
#align category_theory.non_preadditive_abelian.lift_sub_lift CategoryTheory.NonPreadditiveAbelian.lift_sub_lift

theorem sub_sub_sub {X Y : C} (a b c d : X ⟶ Y) : a - c - (b - d) = a - b - (c - d) := by
  rw [sub_def, ← lift_sub_lift, sub_def, Category.assoc, σ_comp, prod.lift_map_assoc]; rfl
  -- ⊢ prod.lift (prod.lift a b ≫ σ) (prod.lift c d ≫ σ) ≫ σ = a - b - (c - d)
                                                                                       -- 🎉 no goals
#align category_theory.non_preadditive_abelian.sub_sub_sub CategoryTheory.NonPreadditiveAbelian.sub_sub_sub

theorem neg_sub {X Y : C} (a b : X ⟶ Y) : -a - b = -b - a := by
  conv_lhs => rw [neg_def, ← sub_zero b, sub_sub_sub, sub_zero, ← neg_def]
  -- 🎉 no goals
#align category_theory.non_preadditive_abelian.neg_sub CategoryTheory.NonPreadditiveAbelian.neg_sub

theorem neg_neg {X Y : C} (a : X ⟶ Y) : - -a = a := by
  rw [neg_def, neg_def]
  -- ⊢ 0 - (0 - a) = a
  conv_lhs =>
    congr; rw [← sub_self a]
  rw [sub_sub_sub, sub_zero, sub_self, sub_zero]
  -- 🎉 no goals
#align category_theory.non_preadditive_abelian.neg_neg CategoryTheory.NonPreadditiveAbelian.neg_neg

theorem add_comm {X Y : C} (a b : X ⟶ Y) : a + b = b + a := by
  rw [add_def]
  -- ⊢ a - -b = b + a
  conv_lhs => rw [← neg_neg a]
  -- ⊢ - -a - -b = b + a
  rw [neg_def, neg_def, neg_def, sub_sub_sub]
  -- ⊢ 0 - 0 - (0 - a - b) = b + a
  conv_lhs =>
    congr
    next => skip
    rw [← neg_def, neg_sub]
  rw [sub_sub_sub, add_def, ← neg_def, neg_neg b, neg_def]
  -- 🎉 no goals
#align category_theory.non_preadditive_abelian.add_comm CategoryTheory.NonPreadditiveAbelian.add_comm

theorem add_neg {X Y : C} (a b : X ⟶ Y) : a + -b = a - b := by rw [add_def, neg_neg]
                                                               -- 🎉 no goals
#align category_theory.non_preadditive_abelian.add_neg CategoryTheory.NonPreadditiveAbelian.add_neg

theorem add_neg_self {X Y : C} (a : X ⟶ Y) : a + -a = 0 := by rw [add_neg, sub_self]
                                                              -- 🎉 no goals
#align category_theory.non_preadditive_abelian.add_neg_self CategoryTheory.NonPreadditiveAbelian.add_neg_self

theorem neg_add_self {X Y : C} (a : X ⟶ Y) : -a + a = 0 := by rw [add_comm, add_neg_self]
                                                              -- 🎉 no goals
#align category_theory.non_preadditive_abelian.neg_add_self CategoryTheory.NonPreadditiveAbelian.neg_add_self

theorem neg_sub' {X Y : C} (a b : X ⟶ Y) : -(a - b) = -a + b := by
  rw [neg_def, neg_def]
  -- ⊢ 0 - (a - b) = 0 - a + b
  conv_lhs => rw [← sub_self (0 : X ⟶ Y)]
  -- ⊢ 0 - 0 - (a - b) = 0 - a + b
  rw [sub_sub_sub, add_def, neg_def]
  -- 🎉 no goals
#align category_theory.non_preadditive_abelian.neg_sub' CategoryTheory.NonPreadditiveAbelian.neg_sub'

theorem neg_add {X Y : C} (a b : X ⟶ Y) : -(a + b) = -a - b := by rw [add_def, neg_sub', add_neg]
                                                                  -- 🎉 no goals
#align category_theory.non_preadditive_abelian.neg_add CategoryTheory.NonPreadditiveAbelian.neg_add

theorem sub_add {X Y : C} (a b c : X ⟶ Y) : a - b + c = a - (b - c) := by
  rw [add_def, neg_def, sub_sub_sub, sub_zero]
  -- 🎉 no goals
#align category_theory.non_preadditive_abelian.sub_add CategoryTheory.NonPreadditiveAbelian.sub_add

theorem add_assoc {X Y : C} (a b c : X ⟶ Y) : a + b + c = a + (b + c) := by
  conv_lhs =>
    congr; rw [add_def]
  rw [sub_add, ← add_neg, neg_sub', neg_neg]
  -- 🎉 no goals
#align category_theory.non_preadditive_abelian.add_assoc CategoryTheory.NonPreadditiveAbelian.add_assoc

theorem add_zero {X Y : C} (a : X ⟶ Y) : a + 0 = a := by rw [add_def, neg_def, sub_self, sub_zero]
                                                         -- 🎉 no goals
#align category_theory.non_preadditive_abelian.add_zero CategoryTheory.NonPreadditiveAbelian.add_zero

theorem comp_sub {X Y Z : C} (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g - h) = f ≫ g - f ≫ h := by
  rw [sub_def, ← Category.assoc, prod.comp_lift, sub_def]
  -- 🎉 no goals
#align category_theory.non_preadditive_abelian.comp_sub CategoryTheory.NonPreadditiveAbelian.comp_sub

theorem sub_comp {X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z) : (f - g) ≫ h = f ≫ h - g ≫ h := by
  rw [sub_def, Category.assoc, σ_comp, ← Category.assoc, prod.lift_map, sub_def]
  -- 🎉 no goals
#align category_theory.non_preadditive_abelian.sub_comp CategoryTheory.NonPreadditiveAbelian.sub_comp

theorem comp_add (X Y Z : C) (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g + h) = f ≫ g + f ≫ h := by
  rw [add_def, comp_sub, neg_def, comp_sub, comp_zero, add_def, neg_def]
  -- 🎉 no goals
#align category_theory.non_preadditive_abelian.comp_add CategoryTheory.NonPreadditiveAbelian.comp_add

theorem add_comp (X Y Z : C) (f g : X ⟶ Y) (h : Y ⟶ Z) : (f + g) ≫ h = f ≫ h + g ≫ h := by
  rw [add_def, sub_comp, neg_def, sub_comp, zero_comp, add_def, neg_def]
  -- 🎉 no goals
#align category_theory.non_preadditive_abelian.add_comp CategoryTheory.NonPreadditiveAbelian.add_comp

/-- Every `NonPreadditiveAbelian` category is preadditive. -/
def preadditive : Preadditive C where
  homGroup X Y :=
    { add := (· + ·)
      add_assoc := add_assoc
      zero := 0
      zero_add := neg_neg
      add_zero := add_zero
      neg := fun f => -f
      add_left_neg := neg_add_self
      sub_eq_add_neg  := fun f g => (add_neg f g).symm -- Porting note: autoParam failed
      add_comm := add_comm }
  add_comp := add_comp
  comp_add := comp_add
#align category_theory.non_preadditive_abelian.preadditive CategoryTheory.NonPreadditiveAbelian.preadditive

end

end CategoryTheory.NonPreadditiveAbelian
