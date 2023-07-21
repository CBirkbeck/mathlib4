
import Mathlib.LinearAlgebra.Matrix.SVD.ColumnRowBlocks
import Mathlib.LinearAlgebra.Matrix.SVD.HermitianMatricesRank
import Mathlib.LinearAlgebra.Matrix.SVD.IsROrCStarOrderedRing
import Mathlib.LinearAlgebra.Matrix.SVD.HermitianMulSelfPosSemiDef
import Mathlib.LinearAlgebra.Matrix.SVD.KernelConjTransposeMul
import Mathlib.LinearAlgebra.Matrix.SVD.svdReindex
import Mathlib.LinearAlgebra.Matrix.SVD.RankMulIsUnit


variable {𝕂: Type}[IsROrC 𝕂][DecidableEq 𝕂]
variable {M N: ℕ}

open Matrix BigOperators

namespace Matrix

noncomputable def svdV₁ (A: Matrix (Fin M) (Fin N) 𝕂): Matrix (Fin N) (Fin (A.rank)) 𝕂 :=
  ((reindex (Equiv.refl (Fin N)) (enz A))
    (isHermitian_transpose_mul_self A).eigenvectorMatrix).toColumns₁

noncomputable def svdV₂ (A: Matrix (Fin M) (Fin N) 𝕂): Matrix (Fin N) (Fin (N - A.rank)) 𝕂 :=
  ((reindex (Equiv.refl (Fin N)) (enz A))
    (isHermitian_transpose_mul_self A).eigenvectorMatrix).toColumns₂

noncomputable def svdμ (A: Matrix (Fin M) (Fin N) 𝕂): Matrix (Fin A.rank) (Fin A.rank) ℝ :=
  (reindex (er A) (er A))
  (diagonal (fun (i : {a // (isHermitian_transpose_mul_self A).eigenvalues a ≠ 0}) =>
      (isHermitian_transpose_mul_self A).eigenvalues i))

noncomputable def svdμ' (A: Matrix (Fin M) (Fin N) 𝕂): Matrix (Fin A.rank) (Fin A.rank) ℝ :=
  (reindex (er' A) (er' A))
  (diagonal (fun (i : {a // (isHermitian_mul_conjTranspose_self A).eigenvalues a ≠ 0}) =>
      (isHermitian_mul_conjTranspose_self A).eigenvalues i))

noncomputable def svdσ (A: Matrix (Fin M) (Fin N) 𝕂): Matrix (Fin A.rank) (Fin A.rank) ℝ :=
  (reindex (er A) (er A))
  (diagonal (fun (i : {a // (isHermitian_transpose_mul_self A).eigenvalues a ≠ 0}) =>
      Real.sqrt ((isHermitian_transpose_mul_self A).eigenvalues i)))

noncomputable def svdU₁ (A: Matrix (Fin M) (Fin N) 𝕂): Matrix (Fin M) (Fin A.rank) 𝕂 :=
  A ⬝ A.svdV₁ ⬝ (A.svdσ.map (algebraMap ℝ 𝕂))⁻¹

noncomputable def svdU₁' (A: Matrix (Fin M) (Fin N) 𝕂): Matrix (Fin M) (Fin (A.rank)) 𝕂 :=
  ((reindex (Equiv.refl (Fin M)) (emz A))
    (isHermitian_mul_conjTranspose_self A).eigenvectorMatrix).toColumns₁

noncomputable def svdU₂ (A: Matrix (Fin M) (Fin N) 𝕂): Matrix (Fin M) (Fin (M - A.rank)) 𝕂 :=
  ((reindex (Equiv.refl (Fin M)) (emz A))
    (isHermitian_mul_conjTranspose_self A).eigenvectorMatrix).toColumns₂

lemma U_columns' (A: Matrix (Fin M) (Fin N) 𝕂) :
  ((reindex (Equiv.refl (Fin M)) (emz A))
    (isHermitian_mul_conjTranspose_self A).eigenvectorMatrix) = fromColumns A.svdU₁' A.svdU₂ :=
  fromColumns_toColumns _

lemma V_conjTranspose_mul_V (A: Matrix (Fin M) (Fin N) 𝕂):
  (A.svdV₁ᴴ ⬝ A.svdV₁ = 1 ∧ A.svdV₂ᴴ ⬝ A.svdV₂ = 1) ∧
  (A.svdV₂ᴴ ⬝ A.svdV₁ = 0 ∧ A.svdV₁ᴴ ⬝ A.svdV₂ = 0) := by
  simp_rw [svdV₁, toColumns₁, svdV₂, toColumns₂, reindex_apply, Equiv.refl_symm, Equiv.coe_refl,
    submatrix_apply, id_eq, Matrix.mul, dotProduct, conjTranspose_apply, of_apply,
    ← conjTranspose_apply, IsHermitian.conjTranspose_eigenvectorMatrix, ← mul_apply,
    eigenvector_matrix_inv_mul_self]
  constructor
  swap
  simp only [ne_eq, Equiv.symm_trans_apply, Equiv.symm_symm, EmbeddingLike.apply_eq_iff_eq,
   not_false_eq_true, one_apply_ne, zero_apply]
  exact ⟨rfl, rfl⟩
  constructor
  all_goals (
    funext i j
    by_cases i = j
    simp_rw [h, one_apply_eq, one_apply_ne h]
    rw [one_apply_ne]
    simp_rw [ne_eq, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, Sum.inl.injEq, h]
  )

lemma V₁_conjTranspose_mul_V₁ (A: Matrix (Fin M) (Fin N) 𝕂): A.svdV₁ᴴ ⬝ A.svdV₁ = 1 :=
  (V_conjTranspose_mul_V A).1.1

lemma V₂_conjTranspose_mul_V₂ (A: Matrix (Fin M) (Fin N) 𝕂): A.svdV₂ᴴ ⬝ A.svdV₂ = 1 :=
  (V_conjTranspose_mul_V A).1.2

lemma V₂_conjTranspose_mul_V₁ (A: Matrix (Fin M) (Fin N) 𝕂): A.svdV₂ᴴ ⬝ A.svdV₁ = 0 :=
  (V_conjTranspose_mul_V A).2.1

lemma V₁_conjTranspose_mul_V₂ (A: Matrix (Fin M) (Fin N) 𝕂): A.svdV₁ᴴ ⬝ A.svdV₂ = 0 :=
  (V_conjTranspose_mul_V A).2.2

lemma V_inv (A: Matrix (Fin M) (Fin N) 𝕂) :
  (fromColumns A.svdV₁ A.svdV₂)ᴴ⬝(fromColumns A.svdV₁ A.svdV₂) = 1 := by
  rw [conjTranspose_fromColumns_eq_fromRows_conjTranspose, fromRows_mul_fromColumns,
    V₁_conjTranspose_mul_V₂, V₁_conjTranspose_mul_V₁, V₂_conjTranspose_mul_V₂,
    V₂_conjTranspose_mul_V₁, fromBlocks_one]


-- First we should prove the 12 21 22 blocks are zero
noncomputable def svdS (A: Matrix (Fin M) (Fin N) 𝕂) :
  Matrix ((Fin A.rank) ⊕ (Fin (N - A.rank))) ((Fin A.rank) ⊕ (Fin (N - A.rank))) ℝ :=
  (reindex (enz A) (enz A))
    (diagonal (isHermitian_transpose_mul_self A).eigenvalues)

noncomputable def svdS' (A: Matrix (Fin M) (Fin N) 𝕂) :
  Matrix ((Fin A.rank) ⊕ (Fin (M - A.rank))) ((Fin A.rank) ⊕ (Fin (M - A.rank))) ℝ :=
  (reindex (emz A) (emz A))
    (diagonal (isHermitian_mul_conjTranspose_self A).eigenvalues)

lemma S_zero_blocks (A: Matrix (Fin M) (Fin N) 𝕂) :
  A.svdS.toBlocks₁₂ = 0 ∧ A.svdS.toBlocks₂₁ = 0 ∧ A.svdS.toBlocks₂₂ = 0 := by
  unfold toBlocks₁₂ toBlocks₂₁ toBlocks₂₂ svdS
  simp only [reindex_apply, submatrix_apply, ne_eq, EmbeddingLike.apply_eq_iff_eq,
    not_false_eq_true, diagonal_apply_ne]
  simp_rw [← Matrix.ext_iff, of_apply, zero_apply, ge_iff_le, implies_true, true_and ]
  intro i j
  by_cases i = j
  unfold enz equiv_sum_trans
  simp only [ne_eq, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_symm_mk, Sum.elim_inr,
    Equiv.sumCompl_apply_inr]
  simp_rw [h, diagonal_apply_eq]
  apply enz_nr_zero
  rw [diagonal_apply_ne]
  exact enz_inj _ _ _ h

lemma S'_zero_blocks (A: Matrix (Fin M) (Fin N) 𝕂) :
  A.svdS'.toBlocks₁₂ = 0 ∧ A.svdS'.toBlocks₂₁ = 0 ∧ A.svdS'.toBlocks₂₂ = 0 := by
  unfold toBlocks₁₂ toBlocks₂₁ toBlocks₂₂ svdS'
  simp only [reindex_apply, submatrix_apply, ne_eq, EmbeddingLike.apply_eq_iff_eq,
    not_false_eq_true, diagonal_apply_ne]
  simp_rw [← Matrix.ext_iff, of_apply, zero_apply, ge_iff_le, implies_true, true_and ]
  intro i j
  by_cases i = j
  unfold emz equiv_sum_trans
  simp only [ne_eq, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_symm_mk, Sum.elim_inr,
    Equiv.sumCompl_apply_inr]
  simp_rw [h, diagonal_apply_eq]
  apply emz_mr_zero
  rw [diagonal_apply_ne]
  exact emz_inj _ _ _ h

lemma S_σpos_block (A: Matrix (Fin M) (Fin N) 𝕂) :
  A.svdS.toBlocks₁₁ = A.svdμ := by
  unfold toBlocks₁₁ svdμ svdS
  simp only [reindex_apply, submatrix_apply, ne_eq, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq,
    submatrix_diagonal_equiv]
  funext i j
  by_cases h: i=j
  simp_rw [h]
  unfold enz er equiv_sum_trans
  simp only [ne_eq, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_symm_mk,
    Sum.elim_inl, Equiv.sumCompl_apply_inl, of_apply,
    diagonal_apply_eq, Function.comp_apply]
  rw [diagonal_apply_ne, of_apply, diagonal_apply_ne]
  rw [ne_eq, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq]
  assumption'

lemma S'_σpos_block (A: Matrix (Fin M) (Fin N) 𝕂) :
  A.svdS'.toBlocks₁₁ = A.svdμ' := by
  unfold toBlocks₁₁ svdμ' svdS'
  simp only [reindex_apply, submatrix_apply, ne_eq, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq,
    submatrix_diagonal_equiv]
  funext i j
  by_cases h: i=j
  simp_rw [h]
  unfold emz er' equiv_sum_trans
  simp only [ne_eq, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_symm_mk,
    Sum.elim_inl, Equiv.sumCompl_apply_inl, of_apply,
    diagonal_apply_eq, Function.comp_apply]
  rw [diagonal_apply_ne, of_apply, diagonal_apply_ne]
  rw [ne_eq, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq]
  assumption'

lemma S_block (A: Matrix (Fin M) (Fin N) 𝕂) :
  (reindex (enz A) (enz A))
    ( diagonal ( (isHermitian_transpose_mul_self A).eigenvalues))=
      fromBlocks A.svdμ 0 0 0 := by
  let hz := S_zero_blocks A
  rw [← svdS, ← fromBlocks_toBlocks (A.svdS), ← S_σpos_block]
  rw [hz.1, hz.2.1, hz.2.2]

lemma S'_block (A: Matrix (Fin M) (Fin N) 𝕂) :
  (reindex (emz A) (emz A))
    ( diagonal ( (isHermitian_mul_conjTranspose_self A).eigenvalues)) =
      fromBlocks A.svdμ' 0 0 0 := by
  let hz := S'_zero_blocks A
  rw [← svdS', ← fromBlocks_toBlocks (A.svdS'), ← S'_σpos_block]
  rw [hz.1, hz.2.1, hz.2.2]

lemma V_columns (A: Matrix (Fin M) (Fin N) 𝕂) :
  (reindex (Equiv.refl (Fin N)) (enz A))
      (isHermitian_transpose_mul_self A).eigenvectorMatrix = fromColumns A.svdV₁ A.svdV₂ := by
  rw [reindex_apply]
  unfold fromColumns svdV₁ svdV₂ toColumns₁ toColumns₂
  funext i j
  cases' j with j j
  -- Column 1
  simp only [Equiv.refl_symm, Equiv.coe_refl, submatrix_apply, id_eq,
    reindex_apply, of_apply, Sum.elim_inl]
  -- Column 2
  simp only [Equiv.refl_symm, Equiv.coe_refl, submatrix_apply, id_eq,
    reindex_apply, of_apply, Sum.elim_inr]

lemma reduced_spectral_theorem (A: Matrix (Fin M) (Fin N) 𝕂):
  Aᴴ⬝A = A.svdV₁ ⬝ (A.svdμ.map (algebraMap ℝ 𝕂))⬝ A.svdV₁ᴴ := by
  let hAHA := isHermitian_transpose_mul_self A

  rw [← submatrix_id_id (Aᴴ⬝A), modified_spectral_theorem hAHA,
    ← IsHermitian.conjTranspose_eigenvectorMatrix]
  rw [← submatrix_mul_equiv
    hAHA.eigenvectorMatrix
    (diagonal (IsROrC.ofReal ∘ hAHA.eigenvalues) ⬝ (hAHA.eigenvectorMatrixᴴ)) _ (enz A).symm _]
  rw [← submatrix_mul_equiv
    (diagonal (IsROrC.ofReal ∘ hAHA.eigenvalues))
    (hAHA.eigenvectorMatrixᴴ) _ (enz A).symm _]
  rw [← @IsROrC.algebraMap_eq_ofReal 𝕂]
  simp_rw [Function.comp]
  rw [← diagonal_map, submatrix_map,
    ← reindex_apply, ← Equiv.coe_refl, ← Equiv.refl_symm, ← reindex_apply,
    ← conjTranspose_submatrix, ← reindex_apply, S_block, V_columns,
    conjTranspose_fromColumns_eq_fromRows_conjTranspose, fromBlocks_map,
    fromBlocks_mul_fromRows, fromColumns_mul_fromRows]
  simp only [map_zero, Matrix.map_zero, Matrix.zero_mul, add_zero, Matrix.mul_zero]
  rw [Matrix.mul_assoc]
  rw [map_zero]

lemma reduced_spectral_theorem' (A: Matrix (Fin M) (Fin N) 𝕂):
  A⬝Aᴴ = A.svdU₁' ⬝ (A.svdμ'.map (algebraMap ℝ 𝕂))⬝ A.svdU₁'ᴴ := by
  let hAAH := isHermitian_mul_conjTranspose_self A
  rw [← submatrix_id_id (A⬝Aᴴ), modified_spectral_theorem hAAH,
    ← IsHermitian.conjTranspose_eigenvectorMatrix]
  rw [← submatrix_mul_equiv
    hAAH.eigenvectorMatrix
    (diagonal (IsROrC.ofReal ∘ hAAH.eigenvalues) ⬝ (hAAH.eigenvectorMatrixᴴ)) _ (emz A).symm _]
  rw [← submatrix_mul_equiv
    (diagonal (IsROrC.ofReal ∘ hAAH.eigenvalues))
    (hAAH.eigenvectorMatrixᴴ) _ (emz A).symm _]
  rw [← @IsROrC.algebraMap_eq_ofReal 𝕂]
  simp_rw [Function.comp]
  rw [← diagonal_map, submatrix_map,
    ← reindex_apply, ← Equiv.coe_refl, ← Equiv.refl_symm, ← reindex_apply,
    ← conjTranspose_submatrix, ← reindex_apply, S'_block, U_columns',
    conjTranspose_fromColumns_eq_fromRows_conjTranspose, fromBlocks_map,
    fromBlocks_mul_fromRows, fromColumns_mul_fromRows]
  simp only [map_zero, Matrix.map_zero, Matrix.zero_mul, add_zero, Matrix.mul_zero]
  rw [Matrix.mul_assoc]
  rw [map_zero]

lemma svdσ_inv (A: Matrix (Fin M) (Fin N) 𝕂): A.svdσ⁻¹ =
  (reindex (er A) (er A))
  (diagonal (fun (i : {a // (isHermitian_transpose_mul_self A).eigenvalues a ≠ 0}) =>
      1 / Real.sqrt ((isHermitian_transpose_mul_self A).eigenvalues i))) := by
  rw [inv_eq_right_inv]
  rw [svdσ]
  simp only [ne_eq, reindex_apply, submatrix_diagonal_equiv, diagonal_mul_diagonal,
    Function.comp_apply]
  rw [← diagonal_one, diagonal_eq_diagonal_iff]
  intros i
  rw [mul_one_div_cancel]
  apply ne_of_gt
  apply sing_vals_ne_zero_pos

lemma σ_inv_μ_σ_inv_eq_one (A: Matrix (Fin M) (Fin N) 𝕂):
  (A.svdσ⁻¹)ᴴ⬝A.svdμ⬝A.svdσ⁻¹ = 1 := by
  rw [svdσ_inv, svdμ]
  simp only [ne_eq, one_div, reindex_apply, submatrix_diagonal_equiv, diagonal_conjTranspose, star_trivial,
    diagonal_mul_diagonal, Function.comp_apply]
  rw [← diagonal_one]
  rw [diagonal_eq_diagonal_iff]
  intro i
  rw [mul_comm, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt]
  -- Why does ? rw [inv_mul_self] not work
  -- rw [inv_mul_self]
  rw [inv_mul_cancel]
  apply ne_of_gt (eig_vals_ne_zero_pos A _)
  apply le_of_lt (eig_vals_ne_zero_pos A _)

lemma IsUnit_det_svdσ (A: Matrix (Fin M) (Fin N) 𝕂): IsUnit (A.svdσ.det) := by
  unfold svdσ
  rw [reindex_apply]
  simp only [ne_eq, submatrix_diagonal_equiv, det_diagonal, Function.comp_apply]
  apply Ne.isUnit
  apply Finset.prod_ne_zero_iff.2
  intros i _
  apply (ne_of_gt)
  apply sing_vals_ne_zero_pos

lemma IsUnit_det_svdσ_mapK (A: Matrix (Fin M) (Fin N) 𝕂):
  IsUnit (det (map A.svdσ (algebraMap ℝ 𝕂))) := by
  unfold svdσ
  simp only [ne_eq, reindex_apply, submatrix_diagonal_equiv, map_zero,
    diagonal_map, Function.comp_apply, det_diagonal]
  rw [isUnit_iff_ne_zero]
  rw [Finset.prod_ne_zero_iff]
  intro i
  simp only [Finset.mem_univ, ne_eq, map_eq_zero, forall_true_left]
  apply ne_of_gt
  apply sing_vals_ne_zero_pos

lemma xw (A: Matrix (Fin M) (Fin N) 𝕂):
  (map (A.svdσ) (algebraMap ℝ 𝕂))⁻¹ = (map (A.svdσ)⁻¹ (algebraMap ℝ 𝕂)) := by
  rw [inv_eq_left_inv]
  rw [← map_mul, nonsing_inv_mul]
  simp only [map_zero, _root_.map_one, map_one]
  apply IsUnit_det_svdσ

lemma U₁_conjTranspose_mul_U₁ (A: Matrix (Fin M) (Fin N) 𝕂):
  A.svdU₁ᴴ ⬝ A.svdU₁ = 1 := by
  rw [svdU₁, conjTranspose_mul, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, reduced_spectral_theorem, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ A.svdV₁, V₁_conjTranspose_mul_V₁, Matrix.one_mul,
    Matrix.mul_assoc A.svdV₁, ← Matrix.mul_assoc _ A.svdV₁, V₁_conjTranspose_mul_V₁,
    Matrix.one_mul, xw, ← conjTranspose_map, ← Matrix.map_mul, ← Matrix.map_mul,
    ← Matrix.mul_assoc, σ_inv_μ_σ_inv_eq_one]
  simp only [map_zero, _root_.map_one, map_one]
  unfold Function.Semiconj
  intros x
  rw [IsROrC.star_def, IsROrC.algebraMap_eq_ofReal, starRingEnd_apply,
    star_trivial, IsROrC.star_def, IsROrC.conj_ofReal]

lemma U₂_conjTranspose_mul_U₂ (A: Matrix (Fin M) (Fin N) 𝕂):
  A.svdU₂ᴴ ⬝ A.svdU₂ = 1 := by
  rw [svdU₂, toColumns₂]
  simp only [reindex_apply, Equiv.refl_symm, Equiv.coe_refl, submatrix_apply, id_eq]
  funext i j
  simp_rw [Matrix.mul_apply, conjTranspose_apply, of_apply,
    ← conjTranspose_apply, IsHermitian.conjTranspose_eigenvectorMatrix,
    ← Matrix.mul_apply, eigenvector_matrix_inv_mul_self]
  by_cases hij: i = j
  simp_rw [hij]
  simp only [one_apply_eq]
  rw [one_apply_ne hij]
  rw [one_apply_ne]
  simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq]
  exact hij

lemma U₁'_conjTranspose_mul_U₂ (A: Matrix (Fin M) (Fin N) 𝕂):
  A.svdU₁'ᴴ ⬝ A.svdU₂ = 0 := by
  simp_rw [svdU₁', svdU₂, toColumns₁, toColumns₂, reindex_apply, Equiv.refl_symm, Equiv.coe_refl,
    submatrix_apply, id_eq, Matrix.mul, dotProduct, conjTranspose_apply, of_apply,
    ← conjTranspose_apply, IsHermitian.conjTranspose_eigenvectorMatrix, ← mul_apply,
    eigenvector_matrix_inv_mul_self]
  funext i j
  simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, not_false_eq_true, one_apply_ne, zero_apply]

lemma mul_V₂_eq_zero (A: Matrix (Fin M) (Fin N) 𝕂):
  A ⬝ A.svdV₂ = 0 := by
  suffices h : Aᴴ⬝A⬝A.svdV₂ = 0
  · exact (ker_conj_transpose_mul_self_eq_ker _ _).1 h
  rw [reduced_spectral_theorem, Matrix.mul_assoc, V₁_conjTranspose_mul_V₂, Matrix.mul_zero]

-- lemma Matrix.left_mul_inj_of_invertible
--   {m n: Type}[Fintype m][DecidableEq m][Fintype n][DecidableEq n]
--   {R: Type}[CommRing R]
--   (P : Matrix m m R) [Invertible P] :
--   Function.Injective (fun (x : Matrix m n R) => P ⬝ x) := by
--   rintro x a hax
--   replace hax := congr_arg (fun (x : Matrix m n R) => P⁻¹ ⬝ x) hax
--   simp only [inv_mul_cancel_left_of_invertible] at hax
--   exact hax

-- lemma Matrix.right_mul_inj_of_invertible
--   {m n: Type}[Fintype m][DecidableEq m][Fintype n][DecidableEq n]
--   {R: Type}[CommRing R]
--   (P : Matrix m m R) [Invertible P] :
--   Function.Injective (fun (x : Matrix n m R) => x ⬝ P) := by
--   rintro x a hax
--   replace hax := congr_arg (fun (x : Matrix n m R) => x ⬝ P⁻¹) hax
--   simp only [mul_inv_cancel_right_of_invertible] at hax
--   exact hax

lemma conjTranspose_mul_U₂_eq_zero (A: Matrix (Fin M) (Fin N) 𝕂):
  Aᴴ ⬝ A.svdU₂ = 0 := by
  suffices h : A⬝Aᴴ⬝A.svdU₂ = 0
  · exact (ker_self_mul_conj_transpose_eq_ker_conj_transpose _ _).1 h
  rw [reduced_spectral_theorem', Matrix.mul_assoc, U₁'_conjTranspose_mul_U₂]
  simp only [Matrix.mul_zero]

lemma U₁_conjTranspose_mul_U₂ (A: Matrix (Fin M) (Fin N) 𝕂): A.svdU₁ᴴ ⬝ A.svdU₂ = 0 := by
  unfold svdU₁
  simp_rw [conjTranspose_mul, Matrix.mul_assoc, conjTranspose_mul_U₂_eq_zero, Matrix.mul_zero]

lemma U₂_conjTranspose_mul_U₁ (A: Matrix (Fin M) (Fin N) 𝕂): A.svdU₂ᴴ ⬝ A.svdU₁ = 0 := by
  rw [← conjTranspose_conjTranspose (A.svdU₁), ← conjTranspose_mul, U₁_conjTranspose_mul_U₂,
    conjTranspose_zero]

lemma U_inv (A: Matrix (Fin M) (Fin N) 𝕂):
  (fromColumns A.svdU₁ A.svdU₂)ᴴ⬝(fromColumns A.svdU₁ A.svdU₂) = 1 := by
  rw [conjTranspose_fromColumns_eq_fromRows_conjTranspose, fromRows_mul_fromColumns,
    U₁_conjTranspose_mul_U₂, U₁_conjTranspose_mul_U₁, U₂_conjTranspose_mul_U₂,
    U₂_conjTranspose_mul_U₁, fromBlocks_one]

lemma V_conjTranspose_mul_inj (A: Matrix (Fin M) (Fin N) 𝕂)
  {m: Type}[Fintype m]:
  Function.Injective (fun x : Matrix m (Fin N) 𝕂 => x ⬝ (fromColumns A.svdV₁ A.svdV₂)) := by
  intro X Y h
  replace h := congr_arg (fun x => x⬝(fromColumns A.svdV₁ A.svdV₂)ᴴ) h
  dsimp at h
  have V_inv' := V_inv A
  rw [conjTranspose_fromColumns_eq_fromRows_conjTranspose,
    ← fromColumns_mul_fromRows_eq_one_comm,
    ← conjTranspose_fromColumns_eq_fromRows_conjTranspose] at V_inv'
  rw [Matrix.mul_assoc, Matrix.mul_assoc, V_inv', Matrix.mul_one, Matrix.mul_one] at h
  exact h
  apply enz

/-- # Main SVD Theorem
Any matrix A (M × N) with rank r = A.rank and  with elements in ℝ or ℂ fields can be decompsed
into three matrices:
  U: an M × M matrix containing the left eigenvectors of the matrix
  S: an M × N matrix with an r × r block in the upper left corner with nonzero singular values
  V: an N × N matrix containing the right eigenvectors of the matrix
  Note that
  S is a block matrix S = [S₁₁, S₁₂; S₂₁, S₂₂] with
  - S₁₁: a diagonal r × r matrix and
  - S₁₂: r × (N - r) zero matrix, S₂₁ : (M - r) × r zero matrix and
  - S₂₂: (M - r) × (N - r) zero matrix
  U is a block column matrix U = [U₁ U₂] with
  - U₁ : a M × r containing left eigenvectors with nonzero singular values.
  - U₂ : a M × (M - r) containing left eigenvectors with zero singular values.
  V is a block column matrix V = [V₁ V₂] with
  - V₁ : a N × r containing right eigenvectors with nonzero singular values.
  - V₂ : a M × (M - r) containing right eigenvectors with zero singular values.

Further UUᴴ = UᴴU = 1 and VVᴴ=VᴴV = 1 as can be seen in lemmas `U_inv` and `V_inv` together with
`fromColumns_mul_fromRows_eq_one_comm` and `conjTranspose_fromColumns_eq_fromRows_conjTranspose` -/
theorem svd_theorem (A: Matrix (Fin M) (Fin N) 𝕂):
  A =
    (fromColumns A.svdU₁ A.svdU₂) ⬝
    (fromBlocks (map A.svdσ (algebraMap ℝ 𝕂)) 0 0 0) ⬝
    (fromColumns A.svdV₁ A.svdV₂)ᴴ := by
  apply_fun (fun x => x⬝(fromColumns A.svdV₁ A.svdV₂))
  dsimp
  rw [Matrix.mul_assoc, V_inv, Matrix.mul_one, fromColumns_mul_fromBlocks, mul_fromColumns,
    mul_V₂_eq_zero]
  simp only [Matrix.mul_zero, add_zero]
  rw [fromColumns_ext_iff, eq_self, and_true, svdU₁, Matrix.mul_assoc,
    nonsing_inv_mul, Matrix.mul_one]
  exact (IsUnit_det_svdσ_mapK _)
  exact (V_conjTranspose_mul_inj _)

end Matrix
