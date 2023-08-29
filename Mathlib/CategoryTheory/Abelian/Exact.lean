/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Adam Topaz, Johan Commelin, Jakob von Raumer
-/
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.Exact
import Mathlib.Tactic.TFAE

#align_import category_theory.abelian.exact from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Exact sequences in abelian categories

In an abelian category, we get several interesting results related to exactness which are not
true in more general settings.

## Main results
* `(f, g)` is exact if and only if `f ≫ g = 0` and `kernel.ι g ≫ cokernel.π f = 0`. This
  characterisation tends to be less cumbersome to work with than the original definition involving
  the comparison map `image f ⟶ kernel g`.
* If `(f, g)` is exact, then `image.ι f` has the universal property of the kernel of `g`.
* `f` is a monomorphism iff `kernel.ι f = 0` iff `Exact 0 f`, and `f` is an epimorphism iff
  `cokernel.π = 0` iff `Exact f 0`.
* A faithful functor between abelian categories that preserves zero morphisms reflects exact
  sequences.
* `X ⟶ Y ⟶ Z ⟶ 0` is exact if and only if the second map is a cokernel of the first, and
  `0 ⟶ X ⟶ Y ⟶ Z` is exact if and only if the first map is a kernel of the second.
* An exact functor preserves exactness, more specifically, `F` preserves finite colimits and
  finite limits, if and only if `Exact f g` implies `Exact (F.map f) (F.map g)`.
-/


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory Limits Preadditive

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

namespace CategoryTheory

namespace Abelian

variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

attribute [local instance] hasEqualizers_of_hasKernels

/-- In an abelian category, a pair of morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` is exact
iff `imageSubobject f = kernelSubobject g`.
-/
theorem exact_iff_image_eq_kernel : Exact f g ↔ imageSubobject f = kernelSubobject g := by
  constructor
  -- ⊢ Exact f g → imageSubobject f = kernelSubobject g
  · intro h
    -- ⊢ imageSubobject f = kernelSubobject g
    have : IsIso (imageToKernel f g h.w) := have := h.epi; isIso_of_mono_of_epi _
    -- ⊢ imageSubobject f = kernelSubobject g
    refine Subobject.eq_of_comm (asIso (imageToKernel _ _ h.w)) ?_
    -- ⊢ (asIso (imageToKernel f g (_ : f ≫ g = 0))).hom ≫ Subobject.arrow (kernelSub …
    simp
    -- 🎉 no goals
  · apply exact_of_image_eq_kernel
    -- 🎉 no goals
#align category_theory.abelian.exact_iff_image_eq_kernel CategoryTheory.Abelian.exact_iff_image_eq_kernel

theorem exact_iff : Exact f g ↔ f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0 := by
  constructor
  -- ⊢ Exact f g → f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0
  · exact fun h ↦ ⟨h.1, kernel_comp_cokernel f g h⟩
    -- 🎉 no goals
  · refine fun h ↦ ⟨h.1, ?_⟩
    -- ⊢ Epi (imageToKernel f g (_ : f ≫ g = 0))
    suffices hl :
      IsLimit (KernelFork.ofι (imageSubobject f).arrow (imageSubobject_arrow_comp_eq_zero h.1))
    · have : imageToKernel f g h.1 = (hl.conePointUniqueUpToIso (limit.isLimit _)).hom ≫
          (kernelSubobjectIso _).inv := by ext; simp
      rw [this]
      -- ⊢ Epi ((IsLimit.conePointUniqueUpToIso hl (limit.isLimit (parallelPair g 0))). …
      infer_instance
      -- 🎉 no goals
    refine KernelFork.IsLimit.ofι _ _ (fun u hu ↦ ?_) ?_ (fun _ _ _ h ↦ ?_)
    · refine kernel.lift (cokernel.π f) u ?_ ≫ (imageIsoImage f).hom ≫ (imageSubobjectIso _).inv
      -- ⊢ u ≫ cokernel.π f = 0
      rw [← kernel.lift_ι g u hu, Category.assoc, h.2, comp_zero]
      -- 🎉 no goals
    · aesop_cat
      -- 🎉 no goals
    · intros
      -- ⊢ x✝ = (fun {W'} u hu => kernel.lift (cokernel.π f) u (_ : u ≫ cokernel.π f =  …
      rw [← cancel_mono (imageSubobject f).arrow, h]
      -- ⊢ x✝² = (fun {W'} u hu => kernel.lift (cokernel.π f) u (_ : u ≫ cokernel.π f = …
      simp
      -- 🎉 no goals
#align category_theory.abelian.exact_iff CategoryTheory.Abelian.exact_iff

theorem exact_iff' {cg : KernelFork g} (hg : IsLimit cg) {cf : CokernelCofork f}
    (hf : IsColimit cf) : Exact f g ↔ f ≫ g = 0 ∧ cg.ι ≫ cf.π = 0 := by
  constructor
  -- ⊢ Exact f g → f ≫ g = 0 ∧ Fork.ι cg ≫ Cofork.π cf = 0
  · intro h
    -- ⊢ f ≫ g = 0 ∧ Fork.ι cg ≫ Cofork.π cf = 0
    exact ⟨h.1, fork_ι_comp_cofork_π f g h cg cf⟩
    -- 🎉 no goals
  · rw [exact_iff]
    -- ⊢ f ≫ g = 0 ∧ Fork.ι cg ≫ Cofork.π cf = 0 → f ≫ g = 0 ∧ kernel.ι g ≫ cokernel. …
    refine fun h => ⟨h.1, ?_⟩
    -- ⊢ kernel.ι g ≫ cokernel.π f = 0
    apply zero_of_epi_comp (IsLimit.conePointUniqueUpToIso hg (limit.isLimit _)).hom
    -- ⊢ (IsLimit.conePointUniqueUpToIso hg (limit.isLimit (parallelPair g 0))).hom ≫ …
    apply zero_of_comp_mono (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hf).hom
    -- ⊢ ((IsLimit.conePointUniqueUpToIso hg (limit.isLimit (parallelPair g 0))).hom  …
    simp [h.2]
    -- 🎉 no goals
#align category_theory.abelian.exact_iff' CategoryTheory.Abelian.exact_iff'

open List in
theorem exact_tfae :
    TFAE [Exact f g, f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0,
      imageSubobject f = kernelSubobject g] := by
  tfae_have 1 ↔ 2; · apply exact_iff
  -- ⊢ Exact f g ↔ f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0
                     -- 🎉 no goals
  tfae_have 1 ↔ 3; · apply exact_iff_image_eq_kernel
  -- ⊢ Exact f g ↔ imageSubobject f = kernelSubobject g
                     -- 🎉 no goals
  tfae_finish
  -- 🎉 no goals
#align category_theory.abelian.exact_tfae CategoryTheory.Abelian.exact_tfae

nonrec theorem IsEquivalence.exact_iff {D : Type u₁} [Category.{v₁} D] [Abelian D] (F : C ⥤ D)
    [IsEquivalence F] : Exact (F.map f) (F.map g) ↔ Exact f g := by
  simp only [exact_iff, ← F.map_eq_zero_iff, F.map_comp, Category.assoc, ←
    kernelComparison_comp_ι g F, ← π_comp_cokernelComparison f F]
  rw [IsIso.comp_left_eq_zero (kernelComparison g F), ← Category.assoc,
    IsIso.comp_right_eq_zero _ (cokernelComparison f F)]
#align category_theory.abelian.is_equivalence.exact_iff CategoryTheory.Abelian.IsEquivalence.exact_iff

/-- The dual result is true even in non-abelian categories, see
    `CategoryTheory.exact_comp_mono_iff`. -/
theorem exact_epi_comp_iff {W : C} (h : W ⟶ X) [Epi h] : Exact (h ≫ f) g ↔ Exact f g := by
  refine' ⟨fun hfg => _, fun h => exact_epi_comp h⟩
  -- ⊢ Exact f g
  let hc := isCokernelOfComp _ _ (colimit.isColimit (parallelPair (h ≫ f) 0))
    (by rw [← cancel_epi h, ← Category.assoc, CokernelCofork.condition, comp_zero]) rfl
  refine' (exact_iff' _ _ (limit.isLimit _) hc).2 ⟨_, ((exact_iff _ _).1 hfg).2⟩
  -- ⊢ f ≫ g = 0
  exact zero_of_epi_comp h (by rw [← hfg.1, Category.assoc])
  -- 🎉 no goals
#align category_theory.abelian.exact_epi_comp_iff CategoryTheory.Abelian.exact_epi_comp_iff

/-- If `(f, g)` is exact, then `Abelian.image.ι f` is a kernel of `g`. -/
def isLimitImage (h : Exact f g) :
    IsLimit (KernelFork.ofι (Abelian.image.ι f) (image_ι_comp_eq_zero h.1) : KernelFork g) := by
  rw [exact_iff] at h
  -- ⊢ IsLimit (KernelFork.ofι (image.ι f) (_ : image.ι f ≫ g = 0))
  exact KernelFork.IsLimit.ofι _ _
    (fun u hu ↦ kernel.lift (cokernel.π f) u
      (by rw [← kernel.lift_ι g u hu, Category.assoc, h.2, comp_zero])) (by aesop_cat)
    (fun _ _ _ hm => by
      rw [← cancel_mono (image.ι f), hm, kernel.lift_ι])
#align category_theory.abelian.is_limit_image CategoryTheory.Abelian.isLimitImage

/-- If `(f, g)` is exact, then `image.ι f` is a kernel of `g`. -/
def isLimitImage' (h : Exact f g) :
    IsLimit (KernelFork.ofι (Limits.image.ι f) (Limits.image_ι_comp_eq_zero h.1)) :=
  IsKernel.isoKernel _ _ (isLimitImage f g h) (imageIsoImage f).symm <| IsImage.lift_fac _ _
#align category_theory.abelian.is_limit_image' CategoryTheory.Abelian.isLimitImage'

/-- If `(f, g)` is exact, then `Abelian.coimage.π g` is a cokernel of `f`. -/
def isColimitCoimage (h : Exact f g) :
    IsColimit
      (CokernelCofork.ofπ (Abelian.coimage.π g) (Abelian.comp_coimage_π_eq_zero h.1) :
        CokernelCofork f) := by
  rw [exact_iff] at h
  -- ⊢ IsColimit (CokernelCofork.ofπ (coimage.π g) (_ : f ≫ coimage.π g = 0))
  refine' CokernelCofork.IsColimit.ofπ _ _
    (fun u hu => cokernel.desc (kernel.ι g) u
      (by rw [← cokernel.π_desc f u hu, ← Category.assoc, h.2, zero_comp]))
    (by aesop_cat) _
  intros _ _ _ _ hm
  -- ⊢ m✝ = (fun {Z'} u hu => cokernel.desc (kernel.ι g) u (_ : kernel.ι g ≫ u = 0) …
  ext
  -- ⊢ coequalizer.π (kernel.ι g) 0 ≫ m✝ = coequalizer.π (kernel.ι g) 0 ≫ (fun {Z'} …
  rw [hm, cokernel.π_desc]
  -- 🎉 no goals
#align category_theory.abelian.is_colimit_coimage CategoryTheory.Abelian.isColimitCoimage

/-- If `(f, g)` is exact, then `factorThruImage g` is a cokernel of `f`. -/
def isColimitImage (h : Exact f g) :
    IsColimit (CokernelCofork.ofπ (Limits.factorThruImage g) (comp_factorThruImage_eq_zero h.1)) :=
  IsCokernel.cokernelIso _ _ (isColimitCoimage f g h) (coimageIsoImage' g) <|
    (cancel_mono (Limits.image.ι g)).1 <| by simp
                                             -- 🎉 no goals
#align category_theory.abelian.is_colimit_image CategoryTheory.Abelian.isColimitImage

theorem exact_cokernel : Exact f (cokernel.π f) := by
  rw [exact_iff]
  -- ⊢ f ≫ cokernel.π f = 0 ∧ kernel.ι (cokernel.π f) ≫ cokernel.π f = 0
  aesop_cat
  -- 🎉 no goals
#align category_theory.abelian.exact_cokernel CategoryTheory.Abelian.exact_cokernel

-- porting note: this can no longer be an instance in Lean4
lemma mono_cokernel_desc_of_exact (h : Exact f g) : Mono (cokernel.desc f g h.w) :=
  suffices h : cokernel.desc f g h.w =
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitImage f g h)).hom ≫
        Limits.image.ι g
    from h.symm ▸ mono_comp _ _
  (cancel_epi (cokernel.π f)).1 <| by simp
                                      -- 🎉 no goals

-- porting note: this can no longer be an instance in Lean4
/-- If `ex : Exact f g` and `epi g`, then `cokernel.desc _ _ ex.w` is an isomorphism. -/
lemma isIso_cokernel_desc_of_exact_of_epi (ex : Exact f g) [Epi g] :
    IsIso (cokernel.desc f g ex.w) :=
  have := mono_cokernel_desc_of_exact _ _ ex
  isIso_of_mono_of_epi (Limits.cokernel.desc f g ex.w)

-- porting note: removed the simp attribute because the lemma may never apply automatically
@[reassoc (attr := nolint unusedHavesSuffices)]
theorem cokernel.desc.inv [Epi g] (ex : Exact f g) :
    have := isIso_cokernel_desc_of_exact_of_epi _ _ ex
    g ≫ inv (cokernel.desc _ _ ex.w) = cokernel.π _ := by
  have := isIso_cokernel_desc_of_exact_of_epi _ _ ex
  -- ⊢ let_fun this := (_ : IsIso (cokernel.desc f g (_ : f ≫ g = 0)));
  simp
  -- 🎉 no goals
#align category_theory.abelian.cokernel.desc.inv CategoryTheory.Abelian.cokernel.desc.inv

-- porting note: this can no longer be an instance in Lean4
lemma isIso_kernel_lift_of_exact_of_mono (ex : Exact f g) [Mono f] : IsIso (kernel.lift g f ex.w) :=
  have := ex.epi_kernel_lift
  isIso_of_mono_of_epi (Limits.kernel.lift g f ex.w)

-- porting note: removed the simp attribute because the lemma may never apply automatically
@[reassoc (attr := nolint unusedHavesSuffices)]
theorem kernel.lift.inv [Mono f] (ex : Exact f g) :
    have := isIso_kernel_lift_of_exact_of_mono _ _ ex
    inv (kernel.lift _ _ ex.w) ≫ f = kernel.ι g := by
  have := isIso_kernel_lift_of_exact_of_mono _ _ ex
  -- ⊢ let_fun this := (_ : IsIso (kernel.lift g f (_ : f ≫ g = 0)));
  simp
  -- 🎉 no goals
#align category_theory.abelian.kernel.lift.inv CategoryTheory.Abelian.kernel.lift.inv

/-- If `X ⟶ Y ⟶ Z ⟶ 0` is exact, then the second map is a cokernel of the first. -/
def isColimitOfExactOfEpi [Epi g] (h : Exact f g) : IsColimit (CokernelCofork.ofπ _ h.w) :=
  IsColimit.ofIsoColimit (colimit.isColimit _) <|
    Cocones.ext
      ⟨cokernel.desc _ _ h.w, epiDesc g (cokernel.π f) ((exact_iff _ _).1 h).2,
        (cancel_epi (cokernel.π f)).1 (by aesop_cat), (cancel_epi g).1 (by aesop_cat)⟩
                                          -- 🎉 no goals
                                                                           -- 🎉 no goals
          (by rintro (_|_) <;> simp [h.w])
              -- ⊢ NatTrans.app (colimit.cocone (parallelPair f 0)).ι WalkingParallelPair.zero  …
                               -- 🎉 no goals
                               -- 🎉 no goals
#align category_theory.abelian.is_colimit_of_exact_of_epi CategoryTheory.Abelian.isColimitOfExactOfEpi

/-- If `0 ⟶ X ⟶ Y ⟶ Z` is exact, then the first map is a kernel of the second. -/
def isLimitOfExactOfMono [Mono f] (h : Exact f g) : IsLimit (KernelFork.ofι _ h.w) :=
  IsLimit.ofIsoLimit (limit.isLimit _) <|
    Cones.ext
      ⟨monoLift f (kernel.ι g) ((exact_iff _ _).1 h).2, kernel.lift _ _ h.w,
        (cancel_mono (kernel.ι g)).1 (by aesop_cat), (cancel_mono f).1 (by aesop_cat)⟩
                                         -- 🎉 no goals
                                                                           -- 🎉 no goals
      fun j => by cases j <;> simp
                  -- ⊢ NatTrans.app (limit.cone (parallelPair g 0)).π WalkingParallelPair.zero = (I …
                              -- 🎉 no goals
                              -- 🎉 no goals
#align category_theory.abelian.is_limit_of_exact_of_mono CategoryTheory.Abelian.isLimitOfExactOfMono

theorem exact_of_is_cokernel (w : f ≫ g = 0)
    (h : IsColimit (CokernelCofork.ofπ _ w)) : Exact f g := by
  refine' (exact_iff _ _).2 ⟨w, _⟩
  -- ⊢ kernel.ι g ≫ cokernel.π f = 0
  have := h.fac (CokernelCofork.ofπ _ (cokernel.condition f)) WalkingParallelPair.one
  -- ⊢ kernel.ι g ≫ cokernel.π f = 0
  simp only [Cofork.ofπ_ι_app] at this
  -- ⊢ kernel.ι g ≫ cokernel.π f = 0
  rw [← this, ← Category.assoc, kernel.condition, zero_comp]
  -- 🎉 no goals
#align category_theory.abelian.exact_of_is_cokernel CategoryTheory.Abelian.exact_of_is_cokernel

theorem exact_of_is_kernel (w : f ≫ g = 0) (h : IsLimit (KernelFork.ofι _ w)) : Exact f g := by
  refine' (exact_iff _ _).2 ⟨w, _⟩
  -- ⊢ kernel.ι g ≫ cokernel.π f = 0
  have := h.fac (KernelFork.ofι _ (kernel.condition g)) WalkingParallelPair.zero
  -- ⊢ kernel.ι g ≫ cokernel.π f = 0
  simp only [Fork.ofι_π_app] at this
  -- ⊢ kernel.ι g ≫ cokernel.π f = 0
  rw [← this, Category.assoc, cokernel.condition, comp_zero]
  -- 🎉 no goals
#align category_theory.abelian.exact_of_is_kernel CategoryTheory.Abelian.exact_of_is_kernel

theorem exact_iff_exact_image_ι : Exact f g ↔ Exact (Abelian.image.ι f) g := by
  conv_lhs => rw [← Abelian.image.fac f]
  -- ⊢ Exact (Abelian.factorThruImage f ≫ image.ι f) g ↔ Exact (image.ι f) g
  rw [exact_epi_comp_iff]
  -- 🎉 no goals
#align category_theory.abelian.exact_iff_exact_image_ι CategoryTheory.Abelian.exact_iff_exact_image_ι

theorem exact_iff_exact_coimage_π : Exact f g ↔ Exact f (coimage.π g) := by
  conv_lhs => rw [← Abelian.coimage.fac g]
  -- ⊢ Exact f (coimage.π g ≫ Abelian.factorThruCoimage g) ↔ Exact f (coimage.π g)
  rw [exact_comp_mono_iff]
  -- 🎉 no goals
#align category_theory.abelian.exact_iff_exact_coimage_π CategoryTheory.Abelian.exact_iff_exact_coimage_π

section

variable (Z)

open List in
theorem tfae_mono : TFAE [Mono f, kernel.ι f = 0, Exact (0 : Z ⟶ X) f] := by
  tfae_have 3 → 2
  -- ⊢ Exact 0 f → kernel.ι f = 0
  · exact kernel_ι_eq_zero_of_exact_zero_left Z
    -- 🎉 no goals
  tfae_have 1 → 3
  -- ⊢ Mono f → Exact 0 f
  · intros
    -- ⊢ Exact 0 f
    exact exact_zero_left_of_mono Z
    -- 🎉 no goals
  tfae_have 2 → 1
  -- ⊢ kernel.ι f = 0 → Mono f
  · exact mono_of_kernel_ι_eq_zero _
    -- 🎉 no goals
  tfae_finish
  -- 🎉 no goals
#align category_theory.abelian.tfae_mono CategoryTheory.Abelian.tfae_mono

-- Note we've already proved `mono_iff_exact_zero_left : mono f ↔ Exact (0 : Z ⟶ X) f`
-- in any preadditive category with kernels and images.
theorem mono_iff_kernel_ι_eq_zero : Mono f ↔ kernel.ι f = 0 :=
  (tfae_mono X f).out 0 1
#align category_theory.abelian.mono_iff_kernel_ι_eq_zero CategoryTheory.Abelian.mono_iff_kernel_ι_eq_zero

open List in
theorem tfae_epi : TFAE [Epi f, cokernel.π f = 0, Exact f (0 : Y ⟶ Z)] := by
  tfae_have 3 → 2
  -- ⊢ Exact f 0 → cokernel.π f = 0
  · rw [exact_iff]
    -- ⊢ f ≫ 0 = 0 ∧ kernel.ι 0 ≫ cokernel.π f = 0 → cokernel.π f = 0
    rintro ⟨-, h⟩
    -- ⊢ cokernel.π f = 0
    exact zero_of_epi_comp _ h
    -- 🎉 no goals
  tfae_have 1 → 3
  -- ⊢ Epi f → Exact f 0
  · rw [exact_iff]
    -- ⊢ Epi f → f ≫ 0 = 0 ∧ kernel.ι 0 ≫ cokernel.π f = 0
    intro
    -- ⊢ f ≫ 0 = 0 ∧ kernel.ι 0 ≫ cokernel.π f = 0
    exact ⟨by simp, by simp [cokernel.π_of_epi]⟩
    -- 🎉 no goals
  tfae_have 2 → 1
  -- ⊢ cokernel.π f = 0 → Epi f
  · exact epi_of_cokernel_π_eq_zero _
    -- 🎉 no goals
  tfae_finish
  -- 🎉 no goals
#align category_theory.abelian.tfae_epi CategoryTheory.Abelian.tfae_epi

-- Note we've already proved `epi_iff_exact_zero_right : epi f ↔ exact f (0 : Y ⟶ Z)`
-- in any preadditive category with equalizers and images.
theorem epi_iff_cokernel_π_eq_zero : Epi f ↔ cokernel.π f = 0 :=
  (tfae_epi X f).out 0 1
#align category_theory.abelian.epi_iff_cokernel_π_eq_zero CategoryTheory.Abelian.epi_iff_cokernel_π_eq_zero

end

section Opposite

theorem Exact.op (h : Exact f g) : Exact g.op f.op := by
  rw [exact_iff]
  -- ⊢ g.op ≫ f.op = 0 ∧ kernel.ι f.op ≫ cokernel.π g.op = 0
  refine' ⟨by simp [← op_comp, h.w], Quiver.Hom.unop_inj _⟩
  -- ⊢ (kernel.ι f.op ≫ cokernel.π g.op).unop = 0.unop
  simp only [unop_comp, cokernel.π_op, eqToHom_refl, kernel.ι_op, Category.id_comp,
    Category.assoc, kernel_comp_cokernel_assoc _ _ h, zero_comp, comp_zero, unop_zero]
#align category_theory.abelian.exact.op CategoryTheory.Abelian.Exact.op

theorem Exact.op_iff : Exact g.op f.op ↔ Exact f g :=
  ⟨fun e => by
    rw [← IsEquivalence.exact_iff _ _ (opOpEquivalence C).inverse]
    -- ⊢ Exact ((opOpEquivalence C).inverse.map f) ((opOpEquivalence C).inverse.map g)
    exact Exact.op _ _ e, Exact.op _ _⟩
    -- 🎉 no goals
#align category_theory.abelian.exact.op_iff CategoryTheory.Abelian.Exact.op_iff

theorem Exact.unop {X Y Z : Cᵒᵖ} (g : X ⟶ Y) (f : Y ⟶ Z) (h : Exact g f) : Exact f.unop g.unop := by
  rw [← f.op_unop, ← g.op_unop] at h
  -- ⊢ Exact f.unop g.unop
  rwa [← Exact.op_iff]
  -- 🎉 no goals
#align category_theory.abelian.exact.unop CategoryTheory.Abelian.Exact.unop

theorem Exact.unop_iff {X Y Z : Cᵒᵖ} (g : X ⟶ Y) (f : Y ⟶ Z) : Exact f.unop g.unop ↔ Exact g f :=
  ⟨fun e => by rwa [← f.op_unop, ← g.op_unop, ← Exact.op_iff] at e, fun e => by
               -- 🎉 no goals
    rw [← Exact.op_iff]
    -- ⊢ Exact g.unop.op f.unop.op
    exact e⟩
    -- 🎉 no goals
#align category_theory.abelian.exact.unop_iff CategoryTheory.Abelian.Exact.unop_iff

end Opposite

end Abelian

namespace Functor

section

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

variable (F : C ⥤ D) [PreservesZeroMorphisms F]

instance (priority := 100) reflectsExactSequencesOfPreservesZeroMorphismsOfFaithful [Faithful F] :
    ReflectsExactSequences F where
  reflects {X Y Z} f g hfg := by
    rw [Abelian.exact_iff, ← F.map_comp, F.map_eq_zero_iff] at hfg
    -- ⊢ Exact f g
    refine' (Abelian.exact_iff _ _).2 ⟨hfg.1, F.zero_of_map_zero _ _⟩
    -- ⊢ F.map (kernel.ι g ≫ cokernel.π f) = 0
    obtain ⟨k, hk⟩ :=
      kernel.lift' (F.map g) (F.map (kernel.ι g))
        (by simp only [← F.map_comp, kernel.condition, CategoryTheory.Functor.map_zero])
    obtain ⟨l, hl⟩ :=
      cokernel.desc' (F.map f) (F.map (cokernel.π f))
        (by simp only [← F.map_comp, cokernel.condition, CategoryTheory.Functor.map_zero])
    rw [F.map_comp, ← hk, ← hl, Category.assoc, reassoc_of% hfg.2, zero_comp, comp_zero]
    -- 🎉 no goals
#align category_theory.functor.reflects_exact_sequences_of_preserves_zero_morphisms_of_faithful CategoryTheory.Functor.reflectsExactSequencesOfPreservesZeroMorphismsOfFaithful

end

end Functor

namespace Functor

open Limits Abelian

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]

variable [Abelian A] [Abelian B]

variable (L : A ⥤ B)

section

variable [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- A functor preserving finite limits and finite colimits preserves exactness. The converse
result is also true, see `Functor.preservesFiniteLimitsOfMapExact` and
`Functor.preservesFiniteColimitsOfMapExact`. -/
theorem map_exact {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (e1 : Exact f g) :
    Exact (L.map f) (L.map g) := by
  let hcoker := isColimitOfHasCokernelOfPreservesColimit L f
  -- ⊢ Exact (L.map f) (L.map g)
  let hker := isLimitOfHasKernelOfPreservesLimit L g
  -- ⊢ Exact (L.map f) (L.map g)
  refine' (exact_iff' _ _ hker hcoker).2 ⟨by simp [← L.map_comp, e1.1], _⟩
  -- ⊢ Fork.ι (Fork.ofι (L.map (kernel.ι g)) (_ : L.map (kernel.ι g) ≫ L.map g = L. …
  simp only [Fork.ι_ofι, Cofork.π_ofπ, ← L.map_comp, kernel_comp_cokernel _ _ e1, L.map_zero]
  -- 🎉 no goals
#align category_theory.functor.map_exact CategoryTheory.Functor.map_exact

end

section

variable (h : ∀ ⦃X Y Z : A⦄ {f : X ⟶ Y} {g : Y ⟶ Z}, Exact f g → Exact (L.map f) (L.map g))

open ZeroObject

/-- A functor which preserves exactness preserves zero morphisms. -/
theorem preservesZeroMorphisms_of_map_exact : L.PreservesZeroMorphisms := by
  replace h := (h (exact_of_zero (𝟙 0) (𝟙 0))).w
  -- ⊢ PreservesZeroMorphisms L
  rw [L.map_id, Category.comp_id] at h
  -- ⊢ PreservesZeroMorphisms L
  exact preservesZeroMorphisms_of_map_zero_object (idZeroEquivIsoZero _ h)
  -- 🎉 no goals
#align category_theory.functor.preserves_zero_morphisms_of_map_exact CategoryTheory.Functor.preservesZeroMorphisms_of_map_exact

/-- A functor which preserves exactness preserves monomorphisms. -/
theorem preservesMonomorphisms_of_map_exact : L.PreservesMonomorphisms where
  preserves f hf := by
    letI := preservesZeroMorphisms_of_map_exact L h
    -- ⊢ Mono (L.map f)
    apply ((tfae_mono (L.obj 0) (L.map f)).out 2 0).mp
    -- ⊢ Exact 0 (L.map f)
    rw [← L.map_zero]
    -- ⊢ Exact (L.map 0) (L.map f)
    exact h (((tfae_mono 0 f).out 0 2).mp hf)
    -- 🎉 no goals
#align category_theory.functor.preserves_monomorphisms_of_map_exact CategoryTheory.Functor.preservesMonomorphisms_of_map_exact

/-- A functor which preserves exactness preserves epimorphisms. -/
theorem preservesEpimorphisms_of_map_exact : L.PreservesEpimorphisms where
  preserves f hf := by
    letI := preservesZeroMorphisms_of_map_exact L h
    -- ⊢ Epi (L.map f)
    apply ((tfae_epi (L.obj 0) (L.map f)).out 2 0).mp
    -- ⊢ Exact (L.map f) 0
    rw [← L.map_zero]
    -- ⊢ Exact (L.map f) (L.map 0)
    exact h (((tfae_epi 0 f).out 0 2).mp hf)
    -- 🎉 no goals
#align category_theory.functor.preserves_epimorphisms_of_map_exact CategoryTheory.Functor.preservesEpimorphisms_of_map_exact

/-- A functor which preserves exactness preserves kernels. -/
def preservesKernelsOfMapExact (X Y : A) (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) L where
  preserves {c} ic := by
    letI := preservesZeroMorphisms_of_map_exact L h
    -- ⊢ IsLimit (L.mapCone c)
    letI := preservesMonomorphisms_of_map_exact L h
    -- ⊢ IsLimit (L.mapCone c)
    letI := mono_of_isLimit_fork ic
    -- ⊢ IsLimit (L.mapCone c)
    have hf :=
      (isLimitMapConeForkEquiv' L (KernelFork.condition c)).symm
        (isLimitOfExactOfMono (L.map (Fork.ι c)) (L.map f)
          (h (exact_of_is_kernel (Fork.ι c) f (KernelFork.condition c)
              (ic.ofIsoLimit (isoOfι _)))))
    exact hf.ofIsoLimit ((Cones.functoriality _ L).mapIso (isoOfι _).symm)
    -- 🎉 no goals
#align category_theory.functor.preserves_kernels_of_map_exact CategoryTheory.Functor.preservesKernelsOfMapExact

/-- A functor which preserves exactness preserves zero cokernels. -/
def preservesCokernelsOfMapExact (X Y : A) (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) L where
  preserves {c} ic := by
    letI := preservesZeroMorphisms_of_map_exact L h
    -- ⊢ IsColimit (L.mapCocone c)
    letI := preservesEpimorphisms_of_map_exact L h
    -- ⊢ IsColimit (L.mapCocone c)
    letI := epi_of_isColimit_cofork ic
    -- ⊢ IsColimit (L.mapCocone c)
    have hf :=
      (isColimitMapCoconeCoforkEquiv' L (CokernelCofork.condition c)).symm
        (isColimitOfExactOfEpi (L.map f) (L.map (Cofork.π c))
          (h (exact_of_is_cokernel f (Cofork.π c) (CokernelCofork.condition c)
              (ic.ofIsoColimit (isoOfπ _)))))
    exact hf.ofIsoColimit ((Cocones.functoriality _ L).mapIso (isoOfπ _).symm)
    -- 🎉 no goals
#align category_theory.functor.preserves_cokernels_of_map_exact CategoryTheory.Functor.preservesCokernelsOfMapExact

/-- A functor which preserves exactness is left exact, i.e. preserves finite limits.
This is part of the inverse implication to `Functor.map_exact`. -/
def preservesFiniteLimitsOfMapExact : PreservesFiniteLimits L := by
  letI := preservesZeroMorphisms_of_map_exact L h
  -- ⊢ PreservesFiniteLimits L
  letI := preservesKernelsOfMapExact L h
  -- ⊢ PreservesFiniteLimits L
  apply preservesFiniteLimitsOfPreservesKernels
  -- 🎉 no goals
#align category_theory.functor.preserves_finite_limits_of_map_exact CategoryTheory.Functor.preservesFiniteLimitsOfMapExact

/-- A functor which preserves exactness is right exact, i.e. preserves finite colimits.
This is part of the inverse implication to `Functor.map_exact`. -/
def preservesFiniteColimitsOfMapExact : PreservesFiniteColimits L := by
  letI := preservesZeroMorphisms_of_map_exact L h
  -- ⊢ PreservesFiniteColimits L
  letI := preservesCokernelsOfMapExact L h
  -- ⊢ PreservesFiniteColimits L
  apply preservesFiniteColimitsOfPreservesCokernels
  -- 🎉 no goals
#align category_theory.functor.preserves_finite_colimits_of_map_exact CategoryTheory.Functor.preservesFiniteColimitsOfMapExact

end

section

/-- A functor preserving zero morphisms, monos, and cokernels preserves finite limits. -/
def preservesFiniteLimitsOfPreservesMonosAndCokernels [PreservesZeroMorphisms L]
    [PreservesMonomorphisms L] [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) L] :
    PreservesFiniteLimits L := by
  apply preservesFiniteLimitsOfMapExact
  -- ⊢ ∀ ⦃X Y Z : A⦄ {f : X ⟶ Y} {g : Y ⟶ Z}, Exact f g → Exact (L.map f) (L.map g)
  intro X Y Z f g h
  -- ⊢ Exact (L.map f) (L.map g)
  rw [← Abelian.coimage.fac g, L.map_comp, exact_comp_mono_iff]
  -- ⊢ Exact (L.map f) (L.map (coimage.π g))
  exact
    exact_of_is_cokernel _ _ _ (isColimitCoforkMapOfIsColimit' L _ (isColimitCoimage f g h))
#align category_theory.functor.preserves_finite_limits_of_preserves_monos_and_cokernels CategoryTheory.Functor.preservesFiniteLimitsOfPreservesMonosAndCokernels

/-- A functor preserving zero morphisms, epis, and kernels preserves finite colimits. -/
def preservesFiniteColimitsOfPreservesEpisAndKernels [PreservesZeroMorphisms L]
    [PreservesEpimorphisms L] [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) L] :
    PreservesFiniteColimits L := by
  apply preservesFiniteColimitsOfMapExact
  -- ⊢ ∀ ⦃X Y Z : A⦄ {f : X ⟶ Y} {g : Y ⟶ Z}, Exact f g → Exact (L.map f) (L.map g)
  intro X Y Z f g h
  -- ⊢ Exact (L.map f) (L.map g)
  rw [← Abelian.image.fac f, L.map_comp, exact_epi_comp_iff]
  -- ⊢ Exact (L.map (Abelian.image.ι f)) (L.map g)
  exact exact_of_is_kernel _ _ _ (isLimitForkMapOfIsLimit' L _ (isLimitImage f g h))
  -- 🎉 no goals
#align category_theory.functor.preserves_finite_colimits_of_preserves_epis_and_kernels CategoryTheory.Functor.preservesFiniteColimitsOfPreservesEpisAndKernels

end

end Functor

end CategoryTheory
