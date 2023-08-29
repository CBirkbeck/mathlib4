/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.DoldKan.FunctorGamma
import Mathlib.CategoryTheory.Idempotents.HomologicalComplex

#align_import algebraic_topology.dold_kan.gamma_comp_n from "leanprover-community/mathlib"@"32a7e535287f9c73f2e4d2aef306a39190f0b504"

/-! The counit isomorphism of the Dold-Kan equivalence

The purpose of this file is to construct natural isomorphisms
`N₁Γ₀ : Γ₀ ⋙ N₁ ≅ toKaroubi (ChainComplex C ℕ)`
and `N₂Γ₂ : Γ₂ ⋙ N₂ ≅ 𝟭 (Karoubi (ChainComplex C ℕ))`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Idempotents Opposite SimplicialObject Simplicial

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category C] [Preadditive C] [HasFiniteCoproducts C]

/-- The isomorphism `(Γ₀.splitting K).nondegComplex ≅ K` for all `K : ChainComplex C ℕ`. -/
@[simps!]
def Γ₀NondegComplexIso (K : ChainComplex C ℕ) : (Γ₀.splitting K).nondegComplex ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun n => Iso.refl _)
    (by
      rintro _ n (rfl : n + 1 = _)
      -- ⊢ ((fun n => Iso.refl (HomologicalComplex.X (Splitting.nondegComplex (Γ₀.split …
      dsimp
      -- ⊢ 𝟙 (Splitting.N (Γ₀.splitting K) (n + 1)) ≫ HomologicalComplex.d K (n + 1) n  …
      simp only [id_comp, comp_id, AlternatingFaceMapComplex.obj_d_eq, Preadditive.sum_comp,
        Preadditive.comp_sum]
      rw [Fintype.sum_eq_single (0 : Fin (n + 2))]
      -- ⊢ HomologicalComplex.d K (n + 1) n = Splitting.ιSummand (Γ₀.splitting K) (Spli …
      · simp only [Fin.val_zero, pow_zero, one_zsmul]
        -- ⊢ HomologicalComplex.d K (n + 1) n = Splitting.ιSummand (Γ₀.splitting K) (Spli …
        erw [Γ₀.Obj.mapMono_on_summand_id_assoc, Γ₀.Obj.Termwise.mapMono_δ₀,
          Splitting.ι_πSummand_eq_id, comp_id]
      · intro i hi
        -- ⊢ Splitting.ιSummand (Γ₀.splitting K) (Splitting.IndexSet.id (op [n + 1])) ≫ ( …
        dsimp
        -- ⊢ Splitting.ιSummand (Γ₀.splitting K) (Splitting.IndexSet.id (op [n + 1])) ≫ ( …
        simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, assoc]
        -- ⊢ (-1) ^ ↑i • Splitting.ιSummand (Γ₀.splitting K) (Splitting.IndexSet.id (op [ …
        erw [Γ₀.Obj.mapMono_on_summand_id_assoc, Γ₀.Obj.Termwise.mapMono_eq_zero, zero_comp,
          zsmul_zero]
        · intro h
          -- ⊢ False
          replace h := congr_arg SimplexCategory.len h
          -- ⊢ False
          change n + 1 = n at h
          -- ⊢ False
          linarith
          -- 🎉 no goals
        · simpa only [Isδ₀.iff] using hi)
          -- 🎉 no goals
#align algebraic_topology.dold_kan.Γ₀_nondeg_complex_iso AlgebraicTopology.DoldKan.Γ₀NondegComplexIso

/-- The natural isomorphism `(Γ₀.splitting K).nondegComplex ≅ K` for `K : ChainComplex C ℕ`. -/
def Γ₀'CompNondegComplexFunctor : Γ₀' ⋙ Split.nondegComplexFunctor ≅ 𝟭 (ChainComplex C ℕ) :=
  NatIso.ofComponents Γ₀NondegComplexIso
#align algebraic_topology.dold_kan.Γ₀'_comp_nondeg_complex_functor AlgebraicTopology.DoldKan.Γ₀'CompNondegComplexFunctor

/-- The natural isomorphism `Γ₀ ⋙ N₁ ≅ toKaroubi (ChainComplex C ℕ)`. -/
def N₁Γ₀ : Γ₀ ⋙ N₁ ≅ toKaroubi (ChainComplex C ℕ) :=
  calc
    Γ₀ ⋙ N₁ ≅ Γ₀' ⋙ Split.forget C ⋙ N₁ := Functor.associator _ _ _
    _ ≅ Γ₀' ⋙ Split.nondegComplexFunctor ⋙ toKaroubi _ :=
      (isoWhiskerLeft Γ₀' Split.toKaroubiNondegComplexFunctorIsoN₁.symm)
    _ ≅ (Γ₀' ⋙ Split.nondegComplexFunctor) ⋙ toKaroubi _ := (Functor.associator _ _ _).symm
    _ ≅ 𝟭 _ ⋙ toKaroubi (ChainComplex C ℕ) := (isoWhiskerRight Γ₀'CompNondegComplexFunctor _)
    _ ≅ toKaroubi (ChainComplex C ℕ) := Functor.leftUnitor _
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.N₁Γ₀ AlgebraicTopology.DoldKan.N₁Γ₀

theorem N₁Γ₀_app (K : ChainComplex C ℕ) :
    N₁Γ₀.app K = (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.symm ≪≫
      (toKaroubi _).mapIso (Γ₀NondegComplexIso K) := by
  ext1
  -- ⊢ (N₁Γ₀.app K).hom = ((Splitting.toKaroubiNondegComplexIsoN₁ (Γ₀.splitting K)) …
  dsimp [N₁Γ₀]
  -- ⊢ (((Karoubi.Hom.mk PInfty ≫ NatTrans.app Split.toKaroubiNondegComplexFunctorI …
  erw [id_comp, comp_id, comp_id]
  -- ⊢ NatTrans.app Split.toKaroubiNondegComplexFunctorIsoN₁.inv (Split.mk' (Γ₀.spl …
  rfl
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.N₁Γ₀_app AlgebraicTopology.DoldKan.N₁Γ₀_app

theorem N₁Γ₀_hom_app (K : ChainComplex C ℕ) :
    N₁Γ₀.hom.app K = (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.inv ≫
        (toKaroubi _).map (Γ₀NondegComplexIso K).hom := by
  change (N₁Γ₀.app K).hom = _
  -- ⊢ (N₁Γ₀.app K).hom = (Splitting.toKaroubiNondegComplexIsoN₁ (Γ₀.splitting K)). …
  simp only [N₁Γ₀_app]
  -- ⊢ ((Splitting.toKaroubiNondegComplexIsoN₁ (Γ₀.splitting K)).symm ≪≫ (toKaroubi …
  rfl
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.N₁Γ₀_hom_app AlgebraicTopology.DoldKan.N₁Γ₀_hom_app

theorem N₁Γ₀_inv_app (K : ChainComplex C ℕ) :
    N₁Γ₀.inv.app K = (toKaroubi _).map (Γ₀NondegComplexIso K).inv ≫
        (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.hom := by
  change (N₁Γ₀.app K).inv = _
  -- ⊢ (N₁Γ₀.app K).inv = (toKaroubi (ChainComplex C ℕ)).map (Γ₀NondegComplexIso K) …
  simp only [N₁Γ₀_app]
  -- ⊢ ((Splitting.toKaroubiNondegComplexIsoN₁ (Γ₀.splitting K)).symm ≪≫ (toKaroubi …
  rfl
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.N₁Γ₀_inv_app AlgebraicTopology.DoldKan.N₁Γ₀_inv_app

@[simp]
theorem N₁Γ₀_hom_app_f_f (K : ChainComplex C ℕ) (n : ℕ) :
    (N₁Γ₀.hom.app K).f.f n = (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.inv.f.f n := by
  rw [N₁Γ₀_hom_app]
  -- ⊢ HomologicalComplex.Hom.f ((Splitting.toKaroubiNondegComplexIsoN₁ (Γ₀.splitti …
  apply comp_id
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.N₁Γ₀_hom_app_f_f AlgebraicTopology.DoldKan.N₁Γ₀_hom_app_f_f

@[simp]
theorem N₁Γ₀_inv_app_f_f (K : ChainComplex C ℕ) (n : ℕ) :
    (N₁Γ₀.inv.app K).f.f n = (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.hom.f.f n := by
  rw [N₁Γ₀_inv_app]
  -- ⊢ HomologicalComplex.Hom.f ((toKaroubi (ChainComplex C ℕ)).map (Γ₀NondegComple …
  apply id_comp
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.N₁Γ₀_inv_app_f_f AlgebraicTopology.DoldKan.N₁Γ₀_inv_app_f_f

-- Porting note: added to speed up elaboration
attribute [irreducible] N₁Γ₀

theorem N₂Γ₂_toKaroubi : toKaroubi (ChainComplex C ℕ) ⋙ Γ₂ ⋙ N₂ = Γ₀ ⋙ N₁ := by
  have h := Functor.congr_obj (functorExtension₂_comp_whiskeringLeft_toKaroubi
    (ChainComplex C ℕ) (SimplicialObject C)) Γ₀
  have h' := Functor.congr_obj (functorExtension₁_comp_whiskeringLeft_toKaroubi
    (SimplicialObject C) (ChainComplex C ℕ)) N₁
  dsimp [N₂, Γ₂, functorExtension₁] at h h' ⊢
  -- ⊢ toKaroubi (ChainComplex C ℕ) ⋙ (functorExtension₂ (ChainComplex C ℕ) (Simpli …
  rw [← Functor.assoc, h, Functor.assoc, h']
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.N₂Γ₂_to_karoubi AlgebraicTopology.DoldKan.N₂Γ₂_toKaroubi

/-- Compatibility isomorphism between `toKaroubi _ ⋙ Γ₂ ⋙ N₂` and `Γ₀ ⋙ N₁` which
are functors `ChainComplex C ℕ ⥤ Karoubi (ChainComplex C ℕ)`. -/
@[simps!]
def N₂Γ₂ToKaroubiIso : toKaroubi (ChainComplex C ℕ) ⋙ Γ₂ ⋙ N₂ ≅ Γ₀ ⋙ N₁ :=
  eqToIso N₂Γ₂_toKaroubi
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.N₂Γ₂_to_karoubi_iso AlgebraicTopology.DoldKan.N₂Γ₂ToKaroubiIso

-- Porting note: added to speed up elaboration
attribute [irreducible] N₂Γ₂ToKaroubiIso

/-- The counit isomorphism of the Dold-Kan equivalence for additive categories. -/
def N₂Γ₂ : Γ₂ ⋙ N₂ ≅ 𝟭 (Karoubi (ChainComplex C ℕ)) :=
  ((whiskeringLeft _ _ _).obj (toKaroubi (ChainComplex C ℕ))).preimageIso
      (N₂Γ₂ToKaroubiIso ≪≫ N₁Γ₀)
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.N₂Γ₂ AlgebraicTopology.DoldKan.N₂Γ₂

@[simp]
theorem N₂Γ₂_inv_app_f_f (X : Karoubi (ChainComplex C ℕ)) (n : ℕ) :
    (N₂Γ₂.inv.app X).f.f n =
      X.p.f n ≫ (Γ₀.splitting X.X).ιSummand (Splitting.IndexSet.id (op [n])) := by
  simp only [N₂Γ₂, Functor.preimageIso, Iso.trans,
    whiskeringLeft_obj_preimage_app, N₂Γ₂ToKaroubiIso_inv, assoc,
    Functor.id_map, NatTrans.comp_app, eqToHom_app, Karoubi.comp_f,
    Karoubi.eqToHom_f, Karoubi.decompId_p_f, HomologicalComplex.comp_f,
    N₁Γ₀_inv_app_f_f, Splitting.toKaroubiNondegComplexIsoN₁_hom_f_f,
    Functor.comp_map, Functor.comp_obj, Karoubi.decompId_i_f,
    eqToHom_refl, comp_id, N₂_map_f_f, Γ₂_map_f_app, N₁_obj_p,
    PInfty_on_Γ₀_splitting_summand_eq_self_assoc, toKaroubi_obj_X,
    Splitting.ι_desc, Splitting.IndexSet.id_fst, SimplexCategory.len_mk, unop_op,
    Karoubi.HomologicalComplex.p_idem_assoc]
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.N₂Γ₂_inv_app_f_f AlgebraicTopology.DoldKan.N₂Γ₂_inv_app_f_f

-- porting note: added to ease the proof of `N₂Γ₂_compatible_with_N₁Γ₀`
lemma whiskerLeft_toKaroubi_N₂Γ₂_hom :
    whiskerLeft (toKaroubi (ChainComplex C ℕ)) N₂Γ₂.hom = N₂Γ₂ToKaroubiIso.hom ≫ N₁Γ₀.hom := by
  let e : _ ≅ toKaroubi (ChainComplex C ℕ) ⋙ 𝟭 _ := N₂Γ₂ToKaroubiIso ≪≫ N₁Γ₀
  -- ⊢ whiskerLeft (toKaroubi (ChainComplex C ℕ)) N₂Γ₂.hom = N₂Γ₂ToKaroubiIso.hom ≫ …
  have h := ((whiskeringLeft _ _ (Karoubi (ChainComplex C ℕ))).obj
    (toKaroubi (ChainComplex C ℕ))).image_preimage e.hom
  dsimp only [whiskeringLeft, N₂Γ₂, Functor.preimageIso] at h ⊢
  -- ⊢ whiskerLeft (toKaroubi (ChainComplex C ℕ)) ((CategoryTheory.Functor.mk { obj …
  exact h
  -- 🎉 no goals

-- Porting note: added to speed up elaboration
attribute [irreducible] N₂Γ₂

theorem N₂Γ₂_compatible_with_N₁Γ₀ (K : ChainComplex C ℕ) :
    N₂Γ₂.hom.app ((toKaroubi _).obj K) = N₂Γ₂ToKaroubiIso.hom.app K ≫ N₁Γ₀.hom.app K :=
  congr_app whiskerLeft_toKaroubi_N₂Γ₂_hom K
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.N₂Γ₂_compatible_with_N₁Γ₀ AlgebraicTopology.DoldKan.N₂Γ₂_compatible_with_N₁Γ₀

end DoldKan

end AlgebraicTopology
