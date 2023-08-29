/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber

#align_import category_theory.preadditive.hom_orthogonal from "leanprover-community/mathlib"@"829895f162a1f29d0133f4b3538f4cd1fb5bffd3"

/-!
# Hom orthogonal families.

A family of objects in a category with zero morphisms is "hom orthogonal" if the only
morphism between distinct objects is the zero morphism.

We show that in any category with zero morphisms and finite biproducts,
a morphism between biproducts drawn from a hom orthogonal family `s : ι → C`
can be decomposed into a block diagonal matrix with entries in the endomorphism rings of the `s i`.

When the category is preadditive, this decomposition is an additive equivalence,
and intertwines composition and matrix multiplication.
When the category is `R`-linear, the decomposition is an `R`-linear equivalence.

If every object in the hom orthogonal family has an endomorphism ring with invariant basis number
(e.g. if each object in the family is simple, so its endomorphism ring is a division ring,
or otherwise if each endomorphism ring is commutative),
then decompositions of an object as a biproduct of the family have uniquely defined multiplicities.
We state this as:
```
theorem HomOrthogonal.equiv_of_iso (o : HomOrthogonal s) {f : α → ι} {g : β → ι}
  (i : (⨁ fun a => s (f a)) ≅ ⨁ fun b => s (g b)) : ∃ e : α ≃ β, ∀ a, g (e a) = f a
```

This is preliminary to defining semisimple categories.
-/


open Classical Matrix CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A family of objects is "hom orthogonal" if
there is at most one morphism between distinct objects.

(In a category with zero morphisms, that must be the zero morphism.) -/
def HomOrthogonal {ι : Type*} (s : ι → C) : Prop :=
  ∀ i j, i ≠ j → Subsingleton (s i ⟶ s j)
#align category_theory.hom_orthogonal CategoryTheory.HomOrthogonal

namespace HomOrthogonal

variable {ι : Type*} {s : ι → C}

theorem eq_zero [HasZeroMorphisms C] (o : HomOrthogonal s) {i j : ι} (w : i ≠ j) (f : s i ⟶ s j) :
    f = 0 := by
  haveI := o i j w
  -- ⊢ f = 0
  apply Subsingleton.elim
  -- 🎉 no goals
#align category_theory.hom_orthogonal.eq_zero CategoryTheory.HomOrthogonal.eq_zero

section

variable [HasZeroMorphisms C] [HasFiniteBiproducts C]

/-- Morphisms between two direct sums over a hom orthogonal family `s : ι → C`
are equivalent to block diagonal matrices,
with blocks indexed by `ι`,
and matrix entries in `i`-th block living in the endomorphisms of `s i`. -/
@[simps]
noncomputable def matrixDecomposition (o : HomOrthogonal s) {α β : Type} [Fintype α] [Fintype β]
    {f : α → ι} {g : β → ι} :
    ((⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b)) ≃
      ∀ i : ι, Matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i)) where
  toFun z i j k :=
    eqToHom
        (by
          rcases k with ⟨k, ⟨⟩⟩
          -- ⊢ s (f k) = s (f ↑{ val := k, property := (_ : f k = f k) })
          simp) ≫
          -- 🎉 no goals
      biproduct.components z k j ≫
        eqToHom
          (by
            rcases j with ⟨j, ⟨⟩⟩
            -- ⊢ s (g ↑{ val := j, property := (_ : g j = g j) }) = s (g j)
            simp)
            -- 🎉 no goals
  invFun z :=
    biproduct.matrix fun j k =>
      if h : f j = g k then z (f j) ⟨k, by simp [h]⟩ ⟨j, by simp⟩ ≫ eqToHom (by simp [h]) else 0
                                           -- 🎉 no goals
                                                            -- 🎉 no goals
                                                                                -- 🎉 no goals
  left_inv z := by
    ext j k
    -- ⊢ biproduct.ι (fun a => s (f a)) k ≫ (fun z => biproduct.matrix fun j k => if  …
    simp only [biproduct.matrix_π, biproduct.ι_desc]
    -- ⊢ (if h : f k = g j then (eqToHom (_ : s (f k) = s (f ↑{ val := k, property := …
    split_ifs with h
    -- ⊢ (eqToHom (_ : s (f k) = s (f ↑{ val := k, property := (_ : k ∈ f ⁻¹' {f k})  …
    · simp
      -- ⊢ biproduct.components z k j = biproduct.ι (fun a => s (f a)) k ≫ z ≫ biproduc …
      rfl
      -- 🎉 no goals
    · symm
      -- ⊢ biproduct.ι (fun a => s (f a)) k ≫ z ≫ biproduct.π (fun b => s (g b)) j = 0
      apply o.eq_zero h
      -- 🎉 no goals
  right_inv z := by
    ext i ⟨j, w⟩ ⟨k, ⟨⟩⟩
    -- ⊢ (fun z i j k => eqToHom (_ : s i = s (f ↑k)) ≫ biproduct.components z ↑k ↑j  …
    simp only [eqToHom_refl, biproduct.matrix_components, Category.id_comp]
    -- ⊢ (if h : f k = g j then z (f k) { val := j, property := (_ : j ∈ g ⁻¹' {f k}) …
    split_ifs with h
    -- ⊢ (z (f k) { val := j, property := (_ : j ∈ g ⁻¹' {f k}) } { val := k, propert …
    · simp
      -- 🎉 no goals
    · exfalso
      -- ⊢ False
      exact h w.symm
      -- 🎉 no goals
#align category_theory.hom_orthogonal.matrix_decomposition CategoryTheory.HomOrthogonal.matrixDecomposition

end

section

variable [Preadditive C] [HasFiniteBiproducts C]

/-- `HomOrthogonal.matrixDecomposition` as an additive equivalence. -/
@[simps]
noncomputable def matrixDecompositionAddEquiv (o : HomOrthogonal s) {α β : Type} [Fintype α]
    [Fintype β] {f : α → ι} {g : β → ι} :
    ((⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b)) ≃+
      ∀ i : ι, Matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i)) :=
  { o.matrixDecomposition with
    map_add' := fun w z => by
      ext
      -- ⊢ Equiv.toFun { toFun := src✝.toFun, invFun := src✝.invFun, left_inv := (_ : F …
      dsimp [biproduct.components]
      -- ⊢ eqToHom (_ : s x✝¹ = s (f ↑x✝)) ≫ (biproduct.ι (fun a => s (f a)) ↑x✝ ≫ (w + …
      simp }
      -- 🎉 no goals
#align category_theory.hom_orthogonal.matrix_decomposition_add_equiv CategoryTheory.HomOrthogonal.matrixDecompositionAddEquiv

@[simp]
theorem matrixDecomposition_id (o : HomOrthogonal s) {α : Type} [Fintype α] {f : α → ι} (i : ι) :
    o.matrixDecomposition (𝟙 (⨁ fun a => s (f a))) i = 1 := by
  ext ⟨b, ⟨⟩⟩ ⟨a, j_property⟩
  -- ⊢ ↑(matrixDecomposition o) (𝟙 (⨁ fun a => s (f a))) ((fun b => f b) b) { val : …
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at j_property
  -- ⊢ ↑(matrixDecomposition o) (𝟙 (⨁ fun a => s (f a))) ((fun b => f b) b) { val : …
  simp only [Category.comp_id, Category.id_comp, Category.assoc, End.one_def, eqToHom_refl,
    Matrix.one_apply, HomOrthogonal.matrixDecomposition_apply, biproduct.components]
  split_ifs with h
  -- ⊢ eqToHom (_ : s (f b) = s (f ↑{ val := a, property := j_property✝ })) ≫ bipro …
  · cases h
    -- ⊢ eqToHom (_ : s (f b) = s (f ↑{ val := b, property := j_property✝ })) ≫ bipro …
    simp
    -- 🎉 no goals
  · simp at h
    -- ⊢ eqToHom (_ : s (f b) = s (f ↑{ val := a, property := j_property✝ })) ≫ bipro …
    -- porting note: used to be `convert comp_zero`, but that does not work anymore
    have : biproduct.ι (fun a ↦ s (f a)) a ≫ biproduct.π (fun b ↦ s (f b)) b = 0 := by
      simpa using biproduct.ι_π_ne _ (Ne.symm h)
    rw [this, comp_zero]
    -- 🎉 no goals
#align category_theory.hom_orthogonal.matrix_decomposition_id CategoryTheory.HomOrthogonal.matrixDecomposition_id

theorem matrixDecomposition_comp (o : HomOrthogonal s) {α β γ : Type} [Fintype α] [Fintype β]
    [Fintype γ] {f : α → ι} {g : β → ι} {h : γ → ι} (z : (⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b))
    (w : (⨁ fun b => s (g b)) ⟶ ⨁ fun c => s (h c)) (i : ι) :
    o.matrixDecomposition (z ≫ w) i = o.matrixDecomposition w i * o.matrixDecomposition z i := by
  ext ⟨c, ⟨⟩⟩ ⟨a, j_property⟩
  -- ⊢ ↑(matrixDecomposition o) (z ≫ w) ((fun b => h b) c) { val := c, property :=  …
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at j_property
  -- ⊢ ↑(matrixDecomposition o) (z ≫ w) ((fun b => h b) c) { val := c, property :=  …
  simp only [Matrix.mul_apply, Limits.biproduct.components,
    HomOrthogonal.matrixDecomposition_apply, Category.comp_id, Category.id_comp, Category.assoc,
    End.mul_def, eqToHom_refl, eqToHom_trans_assoc, Finset.sum_congr]
  conv_lhs => rw [← Category.id_comp w, ← biproduct.total]
  -- ⊢ eqToHom (_ : s (h c) = s (f ↑{ val := a, property := j_property✝ })) ≫ bipro …
  simp only [Preadditive.sum_comp, Preadditive.comp_sum]
  -- ⊢ (Finset.sum Finset.univ fun j => eqToHom (_ : s (h c) = s (f ↑{ val := a, pr …
  apply Finset.sum_congr_set
  -- ⊢ ∀ (x : β) (h_1 : x ∈ (fun a => g a) ⁻¹' {h c}), eqToHom (_ : s (h c) = s (f  …
  · intros
    -- ⊢ eqToHom (_ : s (h c) = s (f ↑{ val := a, property := j_property✝ })) ≫ bipro …
    simp
    -- 🎉 no goals
  · intro b nm
    -- ⊢ eqToHom (_ : s (h c) = s (f ↑{ val := a, property := j_property✝ })) ≫ bipro …
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at nm
    -- ⊢ eqToHom (_ : s (h c) = s (f ↑{ val := a, property := j_property✝ })) ≫ bipro …
    simp only [Category.assoc]
    -- ⊢ eqToHom (_ : s (h c) = s (f ↑{ val := a, property := j_property✝ })) ≫ bipro …
    -- porting note: this used to be 4 times `convert comp_zero`
    have : biproduct.ι (fun b ↦ s (g b)) b ≫ w ≫ biproduct.π (fun b ↦ s (h b)) c = 0 := by
      apply o.eq_zero nm
    simp only [this, comp_zero]
    -- 🎉 no goals
#align category_theory.hom_orthogonal.matrix_decomposition_comp CategoryTheory.HomOrthogonal.matrixDecomposition_comp

section

variable {R : Type*} [Semiring R] [Linear R C]

/-- `HomOrthogonal.MatrixDecomposition` as an `R`-linear equivalence. -/
@[simps]
noncomputable def matrixDecompositionLinearEquiv (o : HomOrthogonal s) {α β : Type} [Fintype α]
    [Fintype β] {f : α → ι} {g : β → ι} :
    ((⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b)) ≃ₗ[R]
      ∀ i : ι, Matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i)) :=
  { o.matrixDecompositionAddEquiv with
    map_smul' := fun w z => by
      ext
      -- ⊢ AddHom.toFun { toFun := src✝.toFun, map_add' := (_ : ∀ (x y : (⨁ fun a => s  …
      dsimp [biproduct.components]
      -- ⊢ eqToHom (_ : s x✝¹ = s (f ↑x✝)) ≫ (biproduct.ι (fun a => s (f a)) ↑x✝ ≫ (w • …
      simp }
      -- 🎉 no goals
#align category_theory.hom_orthogonal.matrix_decomposition_linear_equiv CategoryTheory.HomOrthogonal.matrixDecompositionLinearEquiv

end

/-!
The hypothesis that `End (s i)` has invariant basis number is automatically satisfied
if `s i` is simple (as then `End (s i)` is a division ring).
-/


variable [∀ i, InvariantBasisNumber (End (s i))]

/-- Given a hom orthogonal family `s : ι → C`
for which each `End (s i)` is a ring with invariant basis number (e.g. if each `s i` is simple),
if two direct sums over `s` are isomorphic, then they have the same multiplicities.
-/
theorem equiv_of_iso (o : HomOrthogonal s) {α β : Type} [Fintype α] [Fintype β] {f : α → ι}
    {g : β → ι} (i : (⨁ fun a => s (f a)) ≅ ⨁ fun b => s (g b)) :
    ∃ e : α ≃ β, ∀ a, g (e a) = f a := by
  refine' ⟨Equiv.ofPreimageEquiv _, fun a => Equiv.ofPreimageEquiv_map _ _⟩
  -- ⊢ (c : ι) → ↑((fun a => f a) ⁻¹' {c}) ≃ ↑(g ⁻¹' {c})
  intro c
  -- ⊢ ↑((fun a => f a) ⁻¹' {c}) ≃ ↑(g ⁻¹' {c})
  apply Nonempty.some
  -- ⊢ Nonempty (↑((fun a => f a) ⁻¹' {c}) ≃ ↑(g ⁻¹' {c}))
  apply Cardinal.eq.1
  -- ⊢ Cardinal.mk ↑((fun a => f a) ⁻¹' {c}) = Cardinal.mk ↑(g ⁻¹' {c})
  simp only [Cardinal.mk_fintype, Nat.cast_inj]
  -- ⊢ Fintype.card ↑((fun a => f a) ⁻¹' {c}) = Fintype.card ↑(g ⁻¹' {c})
  exact
    Matrix.square_of_invertible (o.matrixDecomposition i.inv c) (o.matrixDecomposition i.hom c)
      (by
        rw [← o.matrixDecomposition_comp]
        simp)
      (by
        rw [← o.matrixDecomposition_comp]
        simp)
#align category_theory.hom_orthogonal.equiv_of_iso CategoryTheory.HomOrthogonal.equiv_of_iso

end

end HomOrthogonal

end CategoryTheory
