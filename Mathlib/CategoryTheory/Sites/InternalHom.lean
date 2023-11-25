import Mathlib.CategoryTheory.Sites.Over

namespace CategoryTheory

open Category Limits

lemma Over.exists_eq_mk {C : Type*} [Category C] {X : C} (Y : Over X) :
    ∃ (Z : C) (f : Z ⟶ X), Y = Over.mk f :=
  ⟨_, Y.hom, rfl⟩

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {A : Type*} [Category A]

section

variable {I : Type*} {X : C} (Y : I → C) (f : ∀ i, Y i ⟶ X)

abbrev Sieve.ofArrows : Sieve X :=
    Sieve.generate (Presieve.ofArrows Y f)

lemma Sieve.mem_ofArrows_iff {W : C} (g : W ⟶ X) :
    Sieve.ofArrows Y f g ↔ ∃ (i : I) (a : W ⟶ Y i), g = a ≫ f i := by
  dsimp [Sieve.ofArrows]
  constructor
  · rintro ⟨T, a, b, ⟨i⟩, rfl⟩
    exact ⟨i, a, rfl⟩
  · rintro ⟨i, a, rfl⟩
    exact ⟨_, a, f i, ⟨i⟩, rfl⟩

end

section

variable {I : Type*} (Y : I → C)

def Sieve.ofObjects (X : C) : Sieve X where
  arrows Z _ := ∃ (i : I), Nonempty (Z ⟶ Y i)
  downward_closed := by
    rintro Z₁ Z₂ p ⟨i, ⟨f⟩⟩ g
    exact ⟨i, ⟨g ≫ f⟩⟩

end

namespace GrothendieckTopology

def ObjectsCoverTop {I : Type*} (Y : I → C) : Prop :=
  ∀ (X : C), Sieve.ofObjects Y X ∈ J X

lemma sieve_ofArrows_sub_sieve_ofObjects {X : C}
    {I : Type*} (Y : I → C) (f : ∀ i, Y i ⟶ X) :
    Sieve.ofArrows Y f ≤ Sieve.ofObjects Y X := by
  rintro W _ ⟨T, b, c, hc, rfl⟩
  obtain ⟨i⟩ := hc
  exact ⟨i, ⟨b⟩⟩

lemma sieve_ofArrows_eq_sieve_ofObjects {X : C} (hX : IsTerminal X)
    {I : Type*} (Y : I → C) (f : ∀ i, Y i ⟶ X) :
    Sieve.ofArrows Y f = Sieve.ofObjects Y X := by
  apply le_antisymm
  · exact sieve_ofArrows_sub_sieve_ofObjects Y f
  · rintro W a ⟨i, ⟨b⟩⟩
    rw [Sieve.mem_ofArrows_iff]
    exact ⟨i, b, hX.hom_ext _ _⟩

lemma objectsCoverTop_iff_of_isTerminal {X : C} (hX : IsTerminal X)
    {I : Type*} (Y : I → C) (f : ∀ i, Y i ⟶ X) :
    Sieve.ofArrows Y f ∈ J X ↔ J.ObjectsCoverTop Y := by
  simp only [sieve_ofArrows_eq_sieve_ofObjects hX]
  constructor
  · intro h W
    apply J.superset_covering _ (J.pullback_stable (hX.from W) h)
    rintro T a ⟨i, ⟨b⟩⟩
    exact ⟨i, ⟨b⟩⟩
  · intro hY
    exact hY X

end GrothendieckTopology


namespace Presheaf

section

variable (F : Cᵒᵖ ⥤ Type*) {I : Type*} (Y : I → C)

abbrev FamilyOfElementsOnObjects := ∀ (i : I), F.obj (Opposite.op (Y i))

def FamilyOfElementsOnObjects.IsCompatible
    (x : FamilyOfElementsOnObjects F Y) : Prop :=
  ∀ (Z : C) (i j : I) (f : Z ⟶ Y i) (g : Z ⟶ Y j),
    F.map f.op (x i) = F.map g.op (x j)

end

/-lemma IsSheaf.ext_of_arrows {F : Cᵒᵖ ⥤ A} (hF : IsSheaf J F) {I : Type*} {X : C}
    (Y : I → C) (f : ∀ i, Y i ⟶ X)
    (hf : Sieve.ofArrows Y f ∈ J X)
    {W : A} {a b : W ⟶ F.obj (Opposite.op X)}
    (h : ∀ (i : I), a ≫ F.map (f i).op = b ≫ F.map (f i).op) :
    a = b := by
  apply hF.hom_ext ⟨_, hf⟩
  rintro ⟨W, g, T, p, q, ⟨i⟩, rfl⟩
  dsimp
  simp only [Functor.map_comp, reassoc_of% (h i)]-/

variable (F G : Cᵒᵖ ⥤ A)

@[simps obj]
def internalHom : Cᵒᵖ ⥤ Type _ where
  obj X := (Over.forget X.unop).op ⋙ F ⟶ (Over.forget X.unop).op ⋙ G
  map f := whiskerLeft (Over.map f.unop).op
  map_id := by
    rintro ⟨X⟩
    dsimp
    ext φ ⟨Y⟩
    simpa [Over.mapId] using φ.naturality ((@Over.mapId _ _ X).hom.app Y).op
  map_comp := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f : Y ⟶ X⟩ ⟨g : Z ⟶ Y⟩
    dsimp
    ext φ ⟨W⟩
    simpa [Over.mapComp] using φ.naturality ((Over.mapComp g f).hom.app W).op

lemma InternalHom.isAmalgamation_iff {X : C} (S : Sieve X)
    (x : Presieve.FamilyOfElements (internalHom F G) S)
    (hx : x.Compatible) (y : (internalHom F G).obj ⟨X⟩) :
    x.IsAmalgamation y ↔ ∀ (Y : C) (g : Y ⟶ X) (hg : S g),
      y.app ⟨Over.mk g⟩ = (x g hg).app  ⟨Over.mk (𝟙 Y)⟩ := by
  constructor
  · intro h Y g hg
    rw [← h g hg]
    dsimp [internalHom]
    congr
    simp
  · intro h Y g hg
    dsimp [internalHom] at y ⊢
    ext ⟨W⟩
    dsimp
    refine' (h W.left (W.hom ≫ g) (S.downward_closed hg _)).trans _
    dsimp
    have H := hx (𝟙 _) W.hom (S.downward_closed hg W.hom) hg (by simp)
    dsimp at H
    simp only [FunctorToTypes.map_id_apply] at H
    rw [H]
    dsimp [internalHom, Over.map, Comma.mapRight]
    congr
    cases W
    simp

lemma internalHom_isSheaf (hG : IsSheaf J G) : IsSheaf J (internalHom F G) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro X S hS x hx
  apply exists_unique_of_exists_of_unique
  · have Φ : ∀ {Y : C} (g : Y ⟶ X), ∃ (φ : F.obj ⟨Y⟩ ⟶ G.obj ⟨Y⟩),
      ∀ {Z : C} (p : Z ⟶ Y) (hp : S (p ≫ g)), φ ≫ G.map p.op =
        F.map p.op ≫ (x (p ≫ g) hp).app ⟨Over.mk (𝟙 _)⟩ := by
          intro Y g
          let y : Presieve.FamilyOfElements (G ⋙ coyoneda.obj (Opposite.op (F.obj ⟨Y⟩))) (S.pullback g).arrows :=
              fun Z f hf => F.map f.op ≫ (x (f ≫ g) hf).app ⟨Over.mk (𝟙 Z)⟩
          have hy' : y.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac => by
            dsimp
            rw [assoc, assoc]
            erw [← (x (f₁ ≫ g) h₁).naturality (Over.homMk g₁ : Over.mk g₁ ⟶ Over.mk (𝟙 _)).op,
              ← (x (f₂ ≫ g) h₂).naturality (Over.homMk g₂ : Over.mk g₂ ⟶ Over.mk (𝟙 _)).op]
            dsimp
            rw [← F.map_comp_assoc, ← F.map_comp_assoc, ← op_comp, ← op_comp]
            simp only [fac]
            congr 1
            refine' Eq.trans _ ((congr_app (hx g₁ g₂ h₁ h₂ (by rw [reassoc_of% fac]))
              ⟨Over.mk (𝟙 Z)⟩).trans _)
            all_goals
              dsimp [internalHom, Over.map, Comma.mapRight]
              congr
              simp
          exact ⟨(hG (F.obj ⟨Y⟩) (S.pullback g) (J.pullback_stable g hS)).amalgamate _ hy',
            fun p hp => Presieve.IsSheafFor.valid_glue _ hy' _ _⟩
    let app : ∀ {Y : C} (_ : Y ⟶ X), F.obj ⟨Y⟩ ⟶ G.obj ⟨Y⟩ := fun {Y} g => (Φ g).choose
    have happ : ∀ {Y : C} (g : Y ⟶ X) {Z : C} (p : Z ⟶ Y) (hp : S (p ≫ g)),
      app g ≫ G.map p.op = F.map p.op ≫ (x (p ≫ g) hp).app ⟨Over.mk (𝟙 _)⟩ :=
        fun {Y} g => (Φ g).choose_spec
    have happ' : ∀ {Y₁ Y₂ : C} (φ : Y₂ ⟶ Y₁) (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X) (_ : φ ≫ p₁ = p₂)
        (_ : S p₂), app p₁ ≫ G.map φ.op = F.map φ.op ≫ app (φ ≫ p₁) := by
      rintro Y₁ Y₂ φ p₁ _ rfl hp₂
      rw [happ p₁ φ hp₂]
      congr 1
      have H := happ (φ ≫ p₁) (𝟙 _) (by simpa using hp₂)
      erw [op_id, F.map_id, id_comp, G.map_id, comp_id] at H
      rw [H]
      congr 2
      simp
    refine' ⟨
      { app := fun Y => app Y.unop.hom
        naturality := by
          rintro ⟨Y₁ : Over X⟩ ⟨Y₂ : Over X⟩ ⟨f : Y₂ ⟶ Y₁⟩
          dsimp
          change F.map f.left.op ≫ app Y₂.hom = app Y₁.hom ≫ G.map f.left.op
          apply hG.hom_ext ⟨S.pullback Y₂.hom, J.pullback_stable _ hS⟩
          rintro ⟨T, (v : T ⟶ Y₂.left), hv : S (v ≫ Y₂.hom)⟩
          rw [assoc, assoc]
          change _ ≫ _ ≫ G.map v.op = _ ≫ _ ≫ G.map v.op
          rw [← G.map_comp, ← op_comp,
            happ' (v ≫ f.left) Y₁.hom (v ≫ Y₂.hom) (by rw [assoc, Over.w f]) hv,
            happ' v Y₂.hom _ rfl hv, op_comp, F.map_comp, assoc, assoc, ← Over.w f]}, _⟩
    rw [InternalHom.isAmalgamation_iff _ _ _ _ hx]
    intro Y g hg
    change app _ = _
    have H := happ g (𝟙 _) (by simpa using hg)
    erw [op_id, G.map_id, comp_id, F.map_id, id_comp] at H
    refine' H.trans _
    congr
    simp
  · intro y₁ y₂ hy₁ hy₂
    dsimp
    ext ⟨W⟩
    dsimp
    rw [InternalHom.isAmalgamation_iff _ _ _ _ hx] at hy₁ hy₂
    obtain ⟨Y, u, rfl⟩ : ∃ (Y : C) (u : Y ⟶ X), W = Over.mk u := ⟨_, W.hom, rfl⟩
    refine' hG.hom_ext ⟨S.pullback u, J.pullback_stable _ hS⟩ _ _ _
    rintro ⟨T, v, hv⟩
    dsimp
    let φ : Over.mk (v ≫ u) ⟶ Over.mk u := Over.homMk v
    erw [← y₁.naturality φ.op, ← y₂.naturality φ.op]
    congr 1
    exact (hy₁ _ (v ≫ u) hv).trans (hy₂ _ (v ≫ u) hv).symm

def internalHomSectionsEquiv : (internalHom F G).sections ≃ (F ⟶ G) where
  toFun s :=
    { app := fun X => (s.1 X).app ⟨Over.mk (𝟙 _)⟩
      naturality := by
        rintro ⟨X₁⟩ ⟨X₂⟩ ⟨f : X₂ ⟶ X₁⟩
        dsimp
        erw [← s.2 f.op]
        dsimp [internalHom]
        refine' Eq.trans _ ((s.1 ⟨X₁⟩).naturality (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 X₁)).op)
        dsimp [Over.map, Comma.mapRight]
        congr 4
        simp }
  invFun f := ⟨fun X => whiskerLeft _ f, by rintro ⟨X₁⟩ ⟨X₂⟩ ⟨g : X₂ ⟶ X₁⟩; rfl⟩
  left_inv s := by
    ext ⟨X⟩
    dsimp
    ext ⟨Y⟩
    obtain ⟨Y, f, rfl⟩ := Y.exists_eq_mk
    dsimp
    rw [← s.2 f.op]
    dsimp [internalHom, Over.map, Comma.mapRight]
    congr 3
    simp
  right_inv f := rfl

end Presheaf

namespace Sheaf

def internalHom' (F G : Sheaf J A) : Cᵒᵖ ⥤ Type _ where
  obj X := (J.overPullback A X.unop).obj F ⟶ (J.overPullback A X.unop).obj G
  map f := fun φ => (J.overMapPullback A f.unop).map φ
  map_id X := by
    ext φ
    exact Sheaf.Hom.ext _ _ (congr_fun ((Presheaf.internalHom F.1 G.1).map_id X) φ.1)
  map_comp f g := by
    ext φ
    exact Sheaf.Hom.ext _ _ (congr_fun ((Presheaf.internalHom F.1 G.1).map_comp f g) φ.1)

def internalHom'Iso (F G : Sheaf J A) :
    internalHom' F G ≅ Presheaf.internalHom F.1 G.1 :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun φ => φ.1
      invFun := fun φ => ⟨φ⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) (fun _ => rfl)

def internalHom (F G : Sheaf J A) : Sheaf J (Type _) where
  val := internalHom' F G
  cond := (Presheaf.isSheaf_of_iso_iff (internalHom'Iso F G)).2
    (Presheaf.internalHom_isSheaf F.1 G.1 G.2)

def internalHomSectionsEquiv (F G : Sheaf J A) :
    (internalHom F G).1.sections ≃ (F ⟶ G) :=
  ((Functor.sectionsFunctor Cᵒᵖ).mapIso (internalHom'Iso F G)).toEquiv.trans
    ((Presheaf.internalHomSectionsEquiv F.1 G.1).trans
      { toFun := fun f => (sheafToPresheaf J A).preimage f
        invFun := fun f => (sheafToPresheaf J A).map f
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })

@[reassoc (attr := simp)]
lemma internalHomSectionsEquiv_symm_apply_comp_coe_apply {F G H : Sheaf J A}
    (α : F ⟶ G) (β : G ⟶ H) (X : Cᵒᵖ) :
      ((internalHomSectionsEquiv F H).symm (α ≫ β)).1 X =
        ((internalHomSectionsEquiv F G).symm (α)).1 X ≫
          ((internalHomSectionsEquiv G H).symm (β)).1 X := rfl

end Sheaf

namespace Presheaf

namespace FamilyOfElementsOnObjects

variable {F : Cᵒᵖ ⥤ Type _} {I : Type*} {Y : I → C}
    (x : FamilyOfElementsOnObjects F Y)

noncomputable def familyOfElements (X : C) :
    Presieve.FamilyOfElements F (Sieve.ofObjects Y X).arrows :=
  fun _ _ hf => F.map hf.choose_spec.some.op (x _)

namespace IsCompatible

variable {x} (hx : x.IsCompatible)

lemma familyOfElements_apply {X Z : C} (f : Z ⟶ X) (i : I) (φ : Z ⟶ Y i) :
    familyOfElements x X f ⟨i, ⟨φ⟩⟩ = F.map φ.op (x i) := by
  apply hx

lemma familyOfElements_isCompatible (X : C) :
    (familyOfElements x X).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ ⟨i₁, ⟨φ₁⟩⟩ ⟨i₂, ⟨φ₂⟩⟩ _
  simpa [hx.familyOfElements_apply f₁ i₁ φ₁,
    hx.familyOfElements_apply f₂ i₂ φ₂] using hx Z i₁ i₂ (g₁ ≫ φ₁) (g₂ ≫ φ₂)

variable (hY : J.ObjectsCoverTop Y) (hF : IsSheaf J F)

lemma _root_.CategoryTheory.GrothendieckTopology.ObjectsCoverTop.ext {f g : F.sections}
    (h : ∀ i, f.1 (Opposite.op (Y i)) = g.1 (Opposite.op (Y i))) : f = g := by
  ext ⟨X⟩
  apply (Presieve.isSeparated_of_isSheaf J F
    ((isSheaf_iff_isSheaf_of_type _ _).1 hF) _ (hY X)).ext
  rintro W a ⟨i, ⟨b⟩⟩
  erw [f.2 a.op, ← f.2 b.op, h, g.2 b.op, g.2 a.op]

lemma exists_unique_section :
    ∃! (s : F.sections), ∀ (i : I), s.1 (Opposite.op (Y i)) = x i := by
  have H := (isSheaf_iff_isSheaf_of_type _ _).1 hF
  apply exists_unique_of_exists_of_unique
  · let s := fun (X : C) => (H _ (hY X)).amalgamate _
      (hx.familyOfElements_isCompatible X)
    have hs : ∀ {X : C} (i : I) (f : X ⟶ Y i), s X = F.map f.op (x i) := fun {X} i f => by
      have h := Presieve.IsSheafFor.valid_glue (H _ (hY X))
          (hx.familyOfElements_isCompatible _) (𝟙 _) ⟨i, ⟨f⟩⟩
      dsimp at h
      rw [F.map_id] at h
      exact h.trans (hx.familyOfElements_apply _ _ _)
    have hs' : ∀ {W X : C} (a : W ⟶ X) (i : I) (_ : W ⟶ Y i), F.map a.op (s X) = s W := by
      intro W X a i b
      rw [hs i b]
      exact (Presieve.IsSheafFor.valid_glue (H _ (hY X))
        (hx.familyOfElements_isCompatible _) a ⟨i, ⟨b⟩⟩).trans (familyOfElements_apply hx _ _ _)
    refine' ⟨⟨fun X => s X.unop, _⟩, fun i => (hs i (𝟙 (Y i))).trans (by simp)⟩
    rintro ⟨Y₁⟩ ⟨Y₂⟩ ⟨f : Y₂ ⟶ Y₁⟩
    change F.map f.op (s Y₁) = s Y₂
    apply (Presieve.isSeparated_of_isSheaf J F H _ (hY Y₂)).ext
    rintro Z φ ⟨i, ⟨g⟩⟩
    rw [hs' φ i g, ← hs' (φ ≫ f) i g, op_comp, F.map_comp]
    rfl
  · intro y₁ y₂ h₁ h₂
    apply hY.ext hF
    intro i
    rw [h₁, h₂]

noncomputable def section_ : F.sections := (hx.exists_unique_section hY hF).choose

@[simp]
lemma section_apply (i : I) : (hx.section_ hY hF).1 (Opposite.op (Y i)) = x i :=
  (hx.exists_unique_section hY hF).choose_spec.1 i

end IsCompatible

end FamilyOfElementsOnObjects

end Presheaf

namespace Sheaf

variable {F G : Sheaf J A} (φ : F ⟶ G) {I : Type*} (Y : I → C)

lemma isIso_of_isIso_pullback (hY : J.ObjectsCoverTop Y)
    (hφ : ∀ (i : I), IsIso ((J.overPullback A (Y i)).map φ)) :
    IsIso φ := by
  let e : ∀ (i : I), ((J.overPullback A (Y i)).obj F) ≅
    ((J.overPullback A (Y i)).obj G) := fun i =>
      asIso ((J.overPullback A (Y i)).map φ)
  have hφ : ∀ {Z : C} {i : I} (_ : Z ⟶ Y i), IsIso ((J.overPullback A Z).map φ) := by
    intro Z i g
    rw [← J.overMapPullback_map_overPullback_map g φ]
    infer_instance
  let f : Presheaf.FamilyOfElementsOnObjects (internalHom G F).1 Y :=
    fun i => (e i).inv
  have hf : f.IsCompatible := fun Z i j a b => by
    have := hφ a
    rw [← cancel_mono ((J.overPullback A Z).map φ)]
    simp [internalHom, internalHom']
  refine' ⟨(internalHomSectionsEquiv G F).1 (hf.section_ hY (Sheaf.cond _)), _, _⟩
  · refine' (internalHomSectionsEquiv F F).symm.injective
      (hY.ext (Sheaf.cond _) (fun i => Eq.trans _ (e i).hom_inv_id))
    dsimp
    simp only [Equiv.symm_apply_apply, IsIso.hom_inv_id,
      Presheaf.FamilyOfElementsOnObjects.IsCompatible.section_apply]
    exact IsIso.hom_inv_id ((GrothendieckTopology.overPullback J A (Y i)).map φ)
  · refine' (internalHomSectionsEquiv G G).symm.injective
      (hY.ext (Sheaf.cond _) (fun i => Eq.trans _ (e i).inv_hom_id))
    dsimp
    simp only [Equiv.symm_apply_apply, IsIso.inv_hom_id,
      Presheaf.FamilyOfElementsOnObjects.IsCompatible.section_apply]
    exact IsIso.inv_hom_id ((GrothendieckTopology.overPullback J A (Y i)).map φ)

end Sheaf

end CategoryTheory
