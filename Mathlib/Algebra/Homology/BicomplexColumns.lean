import Mathlib.Algebra.Homology.Embedding.StupidFiltration
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.TotalComplexShift

open CategoryTheory Category Limits ComplexShape

instance {C ι : Type*} [Category C] [HasZeroMorphisms C]
    {c : ComplexShape ι} (i : ι) :
    (HomologicalComplex.eval C c i).PreservesZeroMorphisms where

namespace CategoryTheory

variable {C : Type*} [Category C]

namespace Limits

lemma IsZero.obj' {X : C} (hX : IsZero X) {D : Type*} [Category D]
    (F : C ⥤ D) [HasZeroMorphisms C] [HasZeroMorphisms D]
    [F.PreservesZeroMorphisms] : IsZero (F.obj X) := by
  rw [IsZero.iff_id_eq_zero, ← F.map_id, hX.eq_of_src (𝟙 _) 0, F.map_zero]

section

variable [IsIdempotentComplete C] {I : Type*}
  {X : I → C} (Y : I → C)
  (hX : ∀ (i : I), DirectFactor (X i) (Y i))

lemma hasCoproduct_of_direct_factor [HasCoproduct Y] : HasCoproduct X := by
  let p : ∐ Y ⟶ ∐ Y := Sigma.map (fun i => (hX i).r ≫ (hX i).s)
  obtain ⟨S, h, fac⟩ := directFactor_of_isIdempotentComplete _ p (by aesop_cat)
  refine ⟨Cofan.mk S (fun i => (hX i).s ≫ Sigma.ι Y i ≫ h.r),
    mkCofanColimit _ (fun c => h.s ≫ Sigma.desc (fun i => (hX i).r ≫ c.inj i))
      (fun c i => by simp [p, reassoc_of% fac])
      (fun c m hm => ?_)⟩
  dsimp at m ⊢
  rw [← cancel_epi h.r]
  ext i
  simp [← hm, reassoc_of% fac, p]
  simp only [← assoc]
  congr 1
  rw [← cancel_mono h.s]
  simp [fac, p]

end

section

variable {I : Type*} (X : I → C) (i : I)
    (hX : ∀ j, j ≠ i → IsZero (X j))

open Classical in
@[simp]
noncomputable def cofanOfIsZeroButOne : Cofan X := Cofan.mk (X i)
  (fun j => if h : j = i then eqToHom (by rw [h]) else (hX _ h).to_ _)

@[simp]
lemma cofanOfIsZeroButOne_ι_self :
    (cofanOfIsZeroButOne X i hX).inj i = 𝟙 _ :=
  dif_pos rfl

def isColimitCofanOfIsZeroButOne :
    IsColimit (cofanOfIsZeroButOne X i hX) :=
  mkCofanColimit _ (fun s => s.inj i) (fun s j => by
    by_cases hj : j = i
    · subst hj
      simp
    · apply (hX _ hj).eq_of_src) (fun s m hm => by
      dsimp
      simpa using hm i)

lemma hasCoproduct_of_isZero_but_one : HasCoproduct X :=
  ⟨⟨_, isColimitCofanOfIsZeroButOne X i hX⟩⟩

end

end Limits

end CategoryTheory

namespace HomologicalComplex₂

variable {C : Type*} [Category C] [Preadditive C] [IsIdempotentComplete C]
  {ι₁ ι₂ ι : Type*} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}
  {K : HomologicalComplex₂ C c₁ c₂} (L : HomologicalComplex₂ C c₁ c₂)
  (c : ComplexShape ι) [TotalComplexShape c₁ c₂ c]
  (h : ∀ i₁ i₂, DirectFactor ((K.X i₁).X i₂) ((L.X i₁).X i₂))

lemma hasTotal_of_directFactor [L.HasTotal c] : K.HasTotal c :=
  fun i => hasCoproduct_of_direct_factor
    (GradedObject.mapObjFun L.toGradedObject (π c₁ c₂ c) i) (fun _ => h _ _)

variable {ι₁' : Type*} {c₁' : ComplexShape ι₁'} (e : c₁'.Embedding c₁) [e.IsRelIff]
  [HasZeroObject C]

instance [K.HasTotal c] : HomologicalComplex₂.HasTotal (K.stupidTrunc e) c :=
  hasTotal_of_directFactor K c
    (fun i₁ i₂ => (K.stupidTruncDirectFactor e i₁).map (HomologicalComplex.eval _ _ i₂))

end HomologicalComplex₂

namespace ComplexShape

open Embedding

lemma embeddingUpIntGE_monotone (a a' : ℤ) (h : a' ≤ a):
    (embeddingUpIntGE a).Subset (embeddingUpIntGE a') where
  subset := by
    obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le h
    rintro _ ⟨l, rfl⟩
    exact ⟨k + l, by dsimp; omega⟩

end ComplexShape

namespace CochainComplex

variable (C : Type*) [Category C] [HasZeroMorphisms C] [HasZeroObject C]

noncomputable abbrev stupidFiltrationGEFunctor :
    ℤᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  ComplexShape.Embedding.stupidTruncGEFiltration
    (fun n => ComplexShape.embeddingUpIntGE n.unop)
      (fun _ _ φ => ComplexShape.embeddingUpIntGE_monotone _ _ (leOfHom φ.unop)) C

variable {C}
variable (K L : CochainComplex C ℤ)

noncomputable abbrev stupidFiltrationGE : ℤᵒᵖ ⥤ CochainComplex C ℤ :=
  stupidFiltrationGEFunctor C ⋙ ((evaluation _ _).obj K)

end CochainComplex

namespace HomologicalComplex₂

section

variable (C : Type*) [Category C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι₁ ι₂ : Type*} [DecidableEq ι₁] (c₁ : ComplexShape ι₁) (c₂ : ComplexShape ι₂)

noncomputable def singleColumn (i₁ : ι₁) :
    HomologicalComplex C c₂ ⥤ HomologicalComplex₂ C c₁ c₂ :=
  HomologicalComplex.single (HomologicalComplex C c₂) c₁ i₁

variable {C c₂}

lemma isZero_singleColumn_X (K : HomologicalComplex C c₂)
    (i₁ i₁' : ι₁) (h : i₁' ≠ i₁) :
    IsZero (((singleColumn C c₁ c₂ i₁).obj K).X i₁') :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ h

lemma isZero_singleColumn_X_X (K : HomologicalComplex C c₂)
    (i₁ i₁' : ι₁) (h : i₁' ≠ i₁) (i₂ : ι₂) :
    IsZero ((((singleColumn C c₁ c₂ i₁).obj K).X i₁').X i₂) :=
  (isZero_singleColumn_X c₁ K i₁ i₁' h).obj' (HomologicalComplex.eval C c₂ i₂)

noncomputable def singleColumnXIso (K : HomologicalComplex C c₂) (i₁ : ι₁) :
    ((singleColumn C c₁ c₂ i₁).obj K).X i₁ ≅ K := by
  apply HomologicalComplex.singleObjXSelf

noncomputable def singleColumnXXIso (K : HomologicalComplex C c₂) (i₁ : ι₁) (i₂ : ι₂) :
    (((singleColumn C c₁ c₂ i₁).obj K).X i₁).X i₂ ≅ K.X i₂ :=
  (HomologicalComplex.eval C c₂ i₂).mapIso (singleColumnXIso c₁ K i₁)

@[reassoc]
lemma singleColumn_obj_X_d (K : HomologicalComplex C c₂) (i₁ : ι₁) (i₂ i₂' : ι₂) :
    (((singleColumn C c₁ c₂ i₁).obj K).X i₁).d i₂ i₂' =
      (singleColumnXXIso c₁ K i₁ i₂).hom ≫ K.d i₂ i₂' ≫
        (singleColumnXXIso c₁ K i₁ i₂').inv := by
  dsimp only [singleColumn, singleColumnXXIso]
  simp only [Functor.mapIso_hom, HomologicalComplex.eval_map,
    Functor.mapIso_inv, HomologicalComplex.Hom.comm_assoc]
  rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f,
    comp_id]

end

section

variable (C : Type*) [Category C] [Preadditive C] [HasZeroObject C]
  {ι₁ ι₂ ι : Type*} [DecidableEq ι₁] [DecidableEq ι] (c₁ : ComplexShape ι₁) (c₂ : ComplexShape ι₂)
  (K : HomologicalComplex C c₂) (i₁ : ι₁) (c : ComplexShape ι)
  [TotalComplexShape c₁ c₂ c]
  [((singleColumn C c₁ c₂ i₁).obj K).HasTotal  c]

@[simp]
lemma singleColumn_d₁ (x : ι₁) (y : ι₂) (n : ι) :
    ((singleColumn C c₁ c₂ i₁).obj K).d₁ c x y n = 0 := by
  by_cases hx : c₁.Rel x (c₁.next x)
  · by_cases hx' : π c₁ c₂ c (next c₁ x, y) = n
    · rw [d₁_eq _ _ hx _ _ hx']
      simp [singleColumn]
    · rw [d₁_eq_zero' _ _ hx _ _ hx']
  · rw [d₁_eq_zero _ _ _ _ _ hx]

@[simp]
lemma singleColumn_d₂ (y y' : ι₂) (hy : c₂.Rel y y') (n : ι)
    (hn : π c₁ c₂ c (i₁, y') = n) :
    ((singleColumn C c₁ c₂ i₁).obj K).d₂ c i₁ y n =
      ε₂ c₁ c₂ c (i₁, y) • (singleColumnXXIso c₁ K i₁ y).hom ≫ K.d y y' ≫
        (singleColumnXXIso c₁ K i₁ y').inv ≫
        ((singleColumn C c₁ c₂ i₁).obj K).ιTotal c i₁ y' n hn := by
  simp [d₂_eq _ _ _ hy _ hn, singleColumn_obj_X_d]

end

end HomologicalComplex₂

namespace HomologicalComplex₂

variable (C : Type*) [Category C] [Abelian C] {ι : Type*} (c : ComplexShape ι)

noncomputable abbrev rowFiltrationGEFunctor :
    ℤᵒᵖ ⥤ HomologicalComplex₂ C (up ℤ) c ⥤ HomologicalComplex₂ C (up ℤ) c :=
  CochainComplex.stupidFiltrationGEFunctor _

instance (n : ℤᵒᵖ) {ι' : Type*} {c' : ComplexShape ι'}
    (K : HomologicalComplex₂ C (up ℤ) c) [TotalComplexShape (up ℤ) c c'] [K.HasTotal c']:
    (((rowFiltrationGEFunctor C _).obj n).obj K).HasTotal c' := by
  dsimp [rowFiltrationGEFunctor]
  infer_instance

variable {C c}

noncomputable def rowFiltration (K : HomologicalComplex₂ C (up ℤ) c) :
    ℤᵒᵖ ⥤ HomologicalComplex₂ C (up ℤ) c :=
  rowFiltrationGEFunctor C c ⋙ ((evaluation _ _).obj K)

noncomputable def rowFiltrationMap {K L : HomologicalComplex₂ C (up ℤ) c} (φ : K ⟶ L) :
    K.rowFiltration ⟶ L.rowFiltration :=
  whiskerLeft _ ((evaluation _ _).map φ)

variable (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
variable [K.HasTotal (up ℤ)]

instance (n : ℤᵒᵖ) : (K.rowFiltration.obj n).HasTotal (up ℤ) := by
  dsimp [rowFiltration]
  infer_instance

instance (L : CochainComplex C ℤ) (i₂ : ℤ) :
    ((singleColumn C (up ℤ) (up ℤ) i₂).obj L).HasTotal (up ℤ) :=
  fun n => hasCoproduct_of_isZero_but_one _ ⟨⟨i₂, n - i₂⟩, by simp⟩ (by
    rintro ⟨⟨x, y⟩, hxy⟩ h
    apply isZero_singleColumn_X_X
    simp at hxy h
    omega)

@[simp]
noncomputable def cofanSingleColumnObjTotal (L : CochainComplex C ℤ) (x y n : ℤ) (h : x + y = n):
  GradedObject.CofanMapObjFun (((singleColumn C (up ℤ) (up ℤ) x).obj L).toGradedObject)
    (π (up ℤ) (up ℤ) (up ℤ)) n :=
  cofanOfIsZeroButOne  _ ⟨⟨x, y⟩, h⟩ (by
    rintro ⟨⟨x', y'⟩, hxy⟩ h'
    apply isZero_singleColumn_X_X
    simp at hxy h'
    omega)

noncomputable def isColimitCofanSingleColumnObjTotal
    (L : CochainComplex C ℤ) (x y n : ℤ) (h : x + y = n) :
    IsColimit (cofanSingleColumnObjTotal L x y n h) := by
  apply isColimitCofanOfIsZeroButOne

noncomputable def singleColumnObjTotalXIso
    (L : CochainComplex C ℤ) (x y n : ℤ) (h : x + y = n) :
    (((singleColumn C (up ℤ) (up ℤ) x).obj L).total (up ℤ)).X n ≅ L.X y :=
  ((cofanSingleColumnObjTotal L x y n h).iso
    (isColimitCofanSingleColumnObjTotal L x y n h)).symm ≪≫ (singleColumnXXIso (up ℤ) L x y)

lemma singleColumnObjTotalXIso_inv
    (L : CochainComplex C ℤ) (x y n : ℤ) (h : x + y = n) :
    (singleColumnObjTotalXIso L x y n h).inv =
      (singleColumnXXIso (up ℤ) L x y).inv ≫
        ((singleColumn C (up ℤ) (up ℤ) x).obj L).ιTotal (up ℤ) x y n h := by
  rfl

noncomputable def singleColumnObjTotal (L : CochainComplex C ℤ) (x x' : ℤ) (h : x + x' = 0) :
    ((singleColumn C (up ℤ) (up ℤ) x).obj L).total (up ℤ) ≅ L⟦x'⟧ :=
  Iso.symm (HomologicalComplex.Hom.isoOfComponents
    (fun n => (singleColumnObjTotalXIso L _ _ _ (by dsimp; omega)).symm) (by
      intro y y' h
      dsimp at h ⊢
      simp [singleColumnObjTotalXIso_inv]
      rw [singleColumn_d₂ _ _ _ _ _ _ _ (y' + x')
        (by dsimp; omega) _ (by dsimp; omega)]
      obtain rfl : x' = -x := by omega
      simp))

end HomologicalComplex₂
