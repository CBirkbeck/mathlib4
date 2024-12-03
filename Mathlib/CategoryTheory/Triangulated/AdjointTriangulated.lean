import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Triangulated.AdjointCommShift
import Mathlib.CategoryTheory.Triangulated.UliftLemmas

noncomputable section

namespace CategoryTheory

open Category Functor CategoryTheory Opposite Pretriangulated

namespace Adjunction

universe u₁ u₂ v₁ v₂ u

variable {C : Type u₁} {D : Type u₂} [Category.{v₁,u₁} C] [Category.{v₂,u₂} D]
  [HasShift C ℤ] [HasShift D ℤ] [Limits.HasZeroObject C]
  [Limits.HasZeroObject D] [Preadditive C] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] {F : C ⥤ D} {G : D ⥤ C} [F.CommShift ℤ] [G.CommShift ℤ]

variable (X : C)

open ComposableArrows in
lemma isTriangulated_of_left_adjoint_triangulated_aux (adj : F ⊣ G)
    [CommShift.adjunction_compat ℤ adj] [F.IsTriangulated] (T : Triangle D)
    (dT : T ∈ distinguishedTriangles) (X : C) :
    (homologySequenceComposableArrows₅ (preadditiveCoyoneda.obj (op X))
    (G.mapTriangle.obj T) 0 1 (by simp)).Exact := by
  apply Exact.exact_of_comp_exact (AddCommGrp.uliftFunctor.{v₁, max v₁ v₂})
  set e : homologySequenceComposableArrows₅ (preadditiveCoyoneda.obj (op (F.obj X))) T 0 1 (by simp)
      ⋙ AddCommGrp.uliftFunctor.{v₂, max v₁ v₂} ≅ homologySequenceComposableArrows₅
      (preadditiveCoyoneda.obj (op X)) (G.mapTriangle.obj T) 0 1 (by simp) ⋙
      AddCommGrp.uliftFunctor.{v₁, max v₁ v₂} := by
    refine ?_ ≪≫ isoWhiskerRight (homologySequenceComposableArrows₅_mapTriangle_iso _ 0 1
      (by simp) G T).symm _
    refine homologySequenceComposableArrows₅_comp_iso _ T 0 1 (by simp) _ ≪≫ ?_
    refine ?_ ≪≫ (@homologySequenceComposableArrows₅_comp_iso _ _ _ _ _
      (G ⋙ preadditiveCoyoneda.obj (op X)) (ShiftSequence.comp_left _ ℤ G)
      T 0 1 (by simp) _ _ _).symm
    apply @homologySequenceComposableArrows₅_iso_of_natIso _ _ _ _ _
      (preadditiveCoyoneda.obj (op (F.obj X)) ⋙ AddCommGrp.uliftFunctor)
      (ShiftSequence.comp_right _ _ _) T 0 1 (by simp) ((G ⋙ preadditiveCoyoneda.obj (op X)) ⋙
      AddCommGrp.uliftFunctor)  (@ShiftSequence.comp_right _ _ _ _ (G ⋙ preadditiveCoyoneda.obj
      (op X)) ℤ _ _ (ShiftSequence.comp_left _ _ _) _ _ _)
    sorry
  rw [exact_iff_of_iso e.symm]
  exact (homologySequenceComposableArrows₅_exact (preadditiveCoyoneda.obj (op (F.obj X))) _ dT 0 1
    (by simp)).comp_exact _

open ComposableArrows in
def isTriangulated_of_left_adjoint_triangulated (adj : F ⊣ G) [CommShift.adjunction_compat ℤ adj]
    [F.IsTriangulated] : G.IsTriangulated := by
  apply Functor.IsTriangulated.mk
  intro T dT
  obtain ⟨Z, g', h', dT'⟩ := distinguished_cocone_triangle (G.map T.mor₁)
  obtain ⟨θ, hθ₁, hθ₂⟩ := complete_distinguished_triangle_morphism
    (F.mapTriangle.obj (Triangle.mk (G.map T.mor₁) g' h')) T (F.map_distinguished _ dT') dT
    (adj.counit.app _) (adj.counit.app _) (adj.counit.naturality _)
  simp at hθ₁ hθ₂
  set φ : Z ⟶ G.obj T.obj₃ := adj.homEquiv _ _ θ with φdef
  have hφ₁ : g' ≫ φ = G.map T.mor₂ := by
    rw [φdef, ← homEquiv_naturality_left, hθ₁]
    simp [homEquiv_apply]
  have hφ₂ : h' = φ ≫ G.map T.mor₃ ≫ (G.commShiftIso 1).hom.app T.obj₁ := by
    rw [φdef, ← assoc, ← homEquiv_naturality_right, ← hθ₂]
    simp only [comp_obj, homEquiv_apply, map_comp, unit_naturality_assoc, assoc,
      commShiftIso_hom_naturality]
    erw [CommShift.compat_right_triangle, comp_id]
  have hφ : IsIso φ := by
    rw [isIso_iff_isIso_yoneda_map]
    intro X
    suffices h' : IsIso ((preadditiveCoyoneda.obj (op X)).map φ) by
      have : ((yoneda.map φ).app (op X)) = (coyoneda.obj (op X)).map φ := by
        simp [yoneda, coyoneda]
      rw [this]
      have : (coyoneda.obj (op X)).map φ = (forget AddCommGrp).map
        ((preadditiveCoyoneda.obj (op X)).map φ) := by aesop
      rw [this]
      apply Functor.map_isIso
    suffices h'' : IsIso (((preadditiveCoyoneda.obj (op X)).shift (0 : ℤ)).map φ) by
      have : (preadditiveCoyoneda.obj (op X)).map φ =
          ((preadditiveCoyoneda.obj (op X)).isoShiftZero ℤ).inv.app _ ≫
          ((preadditiveCoyoneda.obj (op X)).shift (0 : ℤ)).map φ ≫
          ((preadditiveCoyoneda.obj (op X)).isoShiftZero ℤ).hom.app _ := by
        rw [((preadditiveCoyoneda.obj (op X)).isoShiftZero ℤ).hom.naturality, ← assoc,
          Iso.inv_hom_id_app, id_comp]
      rw [this]
      apply IsIso.comp_isIso
    set R₁ : ComposableArrows AddCommGrp 4 :=
      Monotone.functor (f := Fin.castLE (n := 4 + 1) (m := 5 + 1) (by simp)) (fun ⦃a b⦄ h ↦ h) ⋙
      homologySequenceComposableArrows₅ (preadditiveCoyoneda.obj (op X))
      (Triangle.mk (G.map T.mor₁) g' h') 0 1 (by simp)
    have hR₁ : R₁.Exact := (homologySequenceComposableArrows₅_exact
      (preadditiveCoyoneda.obj (op X)) _ dT' 0 1 (by simp)).exact_truncation 4 (by linarith)
    set R₂ : ComposableArrows AddCommGrp 4 :=
      Monotone.functor (f := Fin.castLE (n := 4 + 1) (m := 5 + 1) (by simp)) (fun ⦃a b⦄ h ↦ h) ⋙
      homologySequenceComposableArrows₅ (preadditiveCoyoneda.obj (op X))
      (G.mapTriangle.obj T) 0 1 (by simp)
    have hR₂ : R₂.Exact := by
      apply Exact.exact_truncation (i := 4) (h := by linarith)
      exact isTriangulated_of_left_adjoint_triangulated_aux adj T dT X
    set Φ : R₁ ⟶ R₂ := by
      refine whiskerLeft (Monotone.functor (f := Fin.castLE (n := 4 + 1) (m := 5 + 1) (by simp))
        (fun ⦃a b⦄ h ↦ h)) ((preadditiveCoyoneda.obj
        (op X)).homologySequenceComposableArrows₅_map_of_triangle_map ?_ 0 1 (by simp))
      exact Triangle.homMk _ _ (𝟙 _) (𝟙 _) φ (by simp) (by simp; exact hφ₁) (by simp; exact hφ₂)
    refine Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hR₁ hR₂ Φ ?_ ?_ ?_ ?_
    · simp only [id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int, Nat.cast_ofNat, Int.reduceAdd,
      Int.reduceSub, obj', Nat.reduceAdd, Fin.zero_eta, Fin.isValue, app', preadditiveCoyoneda_obj,
      homologySequenceComposableArrows₅.eq_1, Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃,
      Triangle.mk_mor₁, Triangle.mk_mor₂, mk₅.eq_1, mk₄.eq_1, mk₃.eq_1, mk₂.eq_1, mapTriangle_obj,
      homologySequenceComposableArrows₅_map_of_triangle_map, Triangle.homMk_hom₁, map_id,
      Triangle.homMk_hom₂, Triangle.homMk_hom₃, whiskerLeft_app, Monotone.functor_obj, Φ]
      change Epi (𝟙 _)
      infer_instance
    · simp only [id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int, Nat.cast_ofNat, Int.reduceAdd,
      Int.reduceSub, obj', Nat.reduceAdd, Fin.mk_one, Fin.isValue, app', preadditiveCoyoneda_obj,
      homologySequenceComposableArrows₅.eq_1, Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃,
      Triangle.mk_mor₁, Triangle.mk_mor₂, mk₅.eq_1, mk₄.eq_1, mk₃.eq_1, mk₂.eq_1, mapTriangle_obj,
      homologySequenceComposableArrows₅_map_of_triangle_map, Triangle.homMk_hom₁, map_id,
      Triangle.homMk_hom₂, Triangle.homMk_hom₃, whiskerLeft_app, Monotone.functor_obj, Φ]
      change IsIso (𝟙 _)
      infer_instance
    · simp only [id_eq, Int.reduceNeg, Nat.cast_ofNat, Int.reduceAdd, Int.reduceSub, obj',
      Nat.reduceAdd, Fin.reduceFinMk, app', preadditiveCoyoneda_obj,
      homologySequenceComposableArrows₅.eq_1, Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃,
      Triangle.mk_mor₁, Triangle.mk_mor₂, mk₅.eq_1, mk₄.eq_1, mk₃.eq_1, mk₂.eq_1, mapTriangle_obj,
      homologySequenceComposableArrows₅_map_of_triangle_map, Triangle.homMk_hom₁, map_id,
      Triangle.homMk_hom₂, Triangle.homMk_hom₃, whiskerLeft_app, Fin.isValue, Monotone.functor_obj,
      Φ]
      change IsIso (𝟙 _)
      infer_instance
    · simp only [obj', Nat.reduceAdd, Fin.reduceFinMk, app', preadditiveCoyoneda_obj,
      Int.reduceAdd, homologySequenceComposableArrows₅.eq_1, Triangle.mk_obj₁, Triangle.mk_obj₂,
      Triangle.mk_obj₃, Triangle.mk_mor₁, Triangle.mk_mor₂, mk₅.eq_1, mk₄.eq_1, mk₃.eq_1, mk₂.eq_1,
      mapTriangle_obj, homologySequenceComposableArrows₅_map_of_triangle_map, Triangle.homMk_hom₁,
      map_id, Triangle.homMk_hom₂, Triangle.homMk_hom₃, whiskerLeft_app, Fin.isValue,
      Monotone.functor_obj, Φ]
      change Mono (𝟙 _)
      infer_instance
  exact isomorphic_distinguished _ dT' _ (Triangle.isoMk (Triangle.mk (G.map T.mor₁) g' h')
    (G.mapTriangle.obj T) (Iso.refl _) (Iso.refl _) (asIso φ) (by simp) (by simp [hφ₁])
    (by simp [hφ₂])).symm

end Adjunction

end CategoryTheory
