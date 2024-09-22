import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Triangulated.Basic
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Filtered.Final

universe u v

namespace CategoryTheory

section LimitOnZ

open Limits

variable {C : Type u} [CategoryTheory.Category.{v, u} C] (F F' : ℤ ⥤ C)

lemma HasLimit_of_transition_iso {a : ℤ} (G : Set.Iic a ⥤ C) (hG : ∀ (b c : Set.Iic a)
    (u : b ⟶ c), IsIso (G.map u)) : HasLimit G := by
  refine HasLimit.mk {cone := ?_, isLimit := ?_}
  · refine {pt := G.obj ⟨a, by simp only [Set.mem_Iic, le_refl]⟩, π := ?_}
    refine {app := ?_, naturality := ?_}
    · intro b
      simp only [Functor.const_obj_obj]
      have := hG b ⟨a, by simp only [Set.mem_Iic, le_refl]⟩ (homOfLE (Set.mem_Iic.mp b.2))
      exact inv (G.map (homOfLE (Set.mem_Iic.mp b.2)))
    · intro b c u
      simp only [Functor.const_obj_obj, Functor.const_obj_map, id_eq, Category.id_comp,
        IsIso.eq_inv_comp, IsIso.comp_inv_eq]
      rw [← Functor.map_comp]
      congr 1
  · exact {lift := fun s ↦ s.π.app ⟨a, by simp only [Set.mem_Iic, le_refl]⟩,
           fac := by simp, uniq := by simp}

abbrev Inclusion_Iic (a : ℤ) : Set.Iic a ⥤ ℤ :=
  Monotone.functor (f := fun b ↦ b.1) (fun _ _ h ↦ h)

lemma Initial_inclusion_Iic (a : ℤ) : Functor.Initial (Inclusion_Iic a) := by
  have : (Inclusion_Iic a).Full :=
      {map_surjective := fun u ↦ by existsi homOfLE (Subtype.mk_le_mk.mpr (leOfHom u)); rfl}
  apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  intro d
  existsi ⟨min a d, by simp only [Set.mem_Iic, min_le_iff, le_refl, true_or]⟩
  exact Nonempty.intro (homOfLE (min_le_right a d))

lemma HasLimit_inclusion_of_transition_eventually_iso {a : ℤ}
    (hF : ∀ (b c : Set.Iic a) (u : b.1 ⟶ c.1), IsIso (F.map u)) :
    HasLimit (Inclusion_Iic a ⋙ F) := by
  apply HasLimit_of_transition_iso
  intro b c u
  simp only [Functor.comp_obj, Functor.comp_map]
  exact hF b c u

lemma HasLimit_of_transition_eventually_iso {a : ℤ} (hF : ∀ (b c : Set.Iic a) (u : b.1 ⟶ c.1),
    IsIso (F.map u)) : HasLimit F := by
  have : (Inclusion_Iic a).Initial := Initial_inclusion_Iic a
  have : HasLimit (Inclusion_Iic a ⋙ F) := HasLimit_inclusion_of_transition_eventually_iso F hF
  exact Functor.Initial.hasLimit_of_comp (Inclusion_Iic a)

noncomputable def Hom_of_almost_NatTrans_aux [HasLimit F] [HasLimit F']
    (α : (n : ℤ) → (F.obj n ⟶ F'.obj n)) (a : ℤ)
    (nat : ∀ (b c : Set.Iic a) (u : b.1 ⟶ c.1), F.map u ≫ α c.1 = α b.1 ≫ F'.map u) :
    Limits.limit F ⟶ Limits.limit F' := by
  have := Initial_inclusion_Iic a
  refine (Functor.Initial.limitIso (Inclusion_Iic a) F).inv ≫ ?_ ≫
    (Functor.Initial.limitIso (Inclusion_Iic a) F').hom
  exact limMap {app := fun b ↦ α b.1, naturality := nat}

lemma Hom_of_almost_NatTrans_indep [HasLimit F] [HasLimit F']
    (α : (n : ℤ) → (F.obj n ⟶ F'.obj n)) {a₁ a₂ : ℤ} (h : a₁ ≤ a₂)
    (nat : ∀ (b c : Set.Iic a₂) (u : b.1 ⟶ c.1), F.map u ≫ α c.1 = α b.1 ≫ F'.map u) :
    Hom_of_almost_NatTrans_aux F F' α a₁
    (fun b c u ↦ nat ⟨b.1, le_trans (Set.mem_Iic.mp b.2) h⟩
                 ⟨c.1, le_trans (Set.mem_Iic.mp c.2) h⟩ u) =
    Hom_of_almost_NatTrans_aux F F' α a₂ nat := by
  have := Initial_inclusion_Iic a₁
  have := Initial_inclusion_Iic a₂
  set e₂ := Functor.Initial.limitIso (Inclusion_Iic a₂) F
  set e'₂ := Functor.Initial.limitIso (Inclusion_Iic a₂) F'
  set e₁ := Functor.Initial.limitIso (Inclusion_Iic a₁) F
  set e'₁ := Functor.Initial.limitIso (Inclusion_Iic a₁) F'
  set f₂ : limit (Inclusion_Iic a₂ ⋙ F) ⟶ limit (Inclusion_Iic a₂ ⋙ F') :=
    limMap {app := fun b ↦ α b.1, naturality := nat}
  set f₁ : limit (Inclusion_Iic a₁ ⋙ F) ⟶ limit (Inclusion_Iic a₁ ⋙ F') :=
    limMap {app := fun b ↦ α b.1, naturality := fun b c u ↦ nat ⟨b.1, le_trans (Set.mem_Iic.mp b.2) h⟩
                 ⟨c.1, le_trans (Set.mem_Iic.mp c.2) h⟩ u}
  change e₁.inv ≫ f₁ ≫ e'₁.hom = e₂.inv ≫ f₂ ≫ e'₂.hom
  set I : Set.Iic a₁ ⥤ Set.Iic a₂ := Monotone.functor
    (f := fun b ↦ ⟨b.1, le_trans (Set.mem_Iic.mp b.2) h⟩) (fun _ _ h ↦ h)
  sorry



/-
lemma Hom_of_almost_NatTrans_indep [HasLimit F] [HasLimit F']
    (α : (n : ℤ) → (F.obj n ⟶ F'.obj n)) {a₁ a₂ : ℤ}
    (nat : ∀ (b c : Set.Iic (max a₁ a₂)) (u : b.1 ⟶ c.1), F.map u ≫ α c.1 = α b.1 ≫ F'.map u) :
    Hom_of_almost_NatTrans_aux F F' α a₁
    (fun b c u ↦ by refine nat ⟨b.1, le_trans (Set.mem_Iic.mp b.2) (le_max_left a₁ a₂)⟩
                      ⟨c.1, le_trans (Set.mem_Iic.mp c.2) (le_max_left a₁ a₂)⟩ u) =
    Hom_of_almost_NatTrans_aux F F' α a₂
    (fun b c u ↦ by refine nat ⟨b.1, le_trans (Set.mem_Iic.mp b.2) (le_max_right a₁ a₂)⟩
                      ⟨c.1, le_trans (Set.mem_Iic.mp c.2) (le_max_right a₁ a₂)⟩ u) := by sorry
-/

end LimitOnZ

section Shift

variable {C : Type u} {A : Type*} [CategoryTheory.Category.{v, u} C] [AddCommMonoid A]
  [CategoryTheory.HasShift C A]

attribute [local instance] endofunctorMonoidalCategory

open Category

@[reassoc]
lemma shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd'_hom_app (m₁ m₂ m₃ m : A)
    (hm : m₂ + m₃ = m) (X : C) :
    (shiftFunctorComm C m₁ m).hom.app X ≫
    ((shiftFunctorAdd' C m₂ m₃ m hm).hom.app X)⟦m₁⟧' =
  (shiftFunctorAdd' C m₂ m₃ m hm).hom.app (X⟦m₁⟧) ≫
    ((shiftFunctorComm C m₁ m₂).hom.app X)⟦m₃⟧' ≫
    (shiftFunctorComm C m₁ m₃).hom.app (X⟦m₂⟧) := by
  rw [← cancel_mono ((shiftFunctorComm C m₁ m₃).inv.app (X⟦m₂⟧)),
    ← cancel_mono (((shiftFunctorComm C m₁ m₂).inv.app X)⟦m₃⟧')]
  simp only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  simp only [shiftFunctorComm_eq C _ _ _ rfl]
  dsimp
  simp only [Functor.map_comp, Category.assoc]
  slice_rhs 3 4 => rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  rw [Category.id_comp]
  conv_rhs => rw [← Functor.map_comp, Iso.inv_hom_id_app]; erw [Functor.map_id, Category.comp_id]
  slice_lhs 2 3 => rw [shiftFunctorAdd'_assoc_hom_app m₂ m₃ m₁ m (m₁ + m₃) (m₁ + m) hm
    (add_comm _ _) (by rw [hm]; exact add_comm _ _)]
  simp only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  slice_lhs 2 3 => rw [← shiftFunctorAdd'_assoc_hom_app m₂ m₁ m₃ (m₁ + m₂) (m₁ + m₃) (m₁ + m)
    (add_comm _ _) rfl (by rw [add_comm m₂, add_assoc, hm])]
  slice_lhs 3 4 => rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  erw [Category.id_comp]
  rw [shiftFunctorAdd'_assoc_hom_app m₁ m₂ m₃ (m₁ + m₂) m (m₁ + m) rfl hm (by rw [add_assoc, hm])]
  simp only [Functor.comp_obj, Iso.inv_hom_id_app_assoc]

lemma shiftFunctorAdd_symm_eqToIso (i j i' j' : A) (hi : i = i') (hj : j = j') :
    (shiftFunctorAdd C i j).symm = eqToIso (by rw [hi, hj]) ≪≫
    (shiftFunctorAdd C i' j').symm ≪≫ eqToIso (by rw [hi, hj]) := by
  ext X
  simp only [Functor.comp_obj, Iso.symm_hom, Iso.trans_hom, eqToIso.hom, NatTrans.comp_app,
    eqToHom_app]
  have := (shiftMonoidalFunctor C A).μ_natural_left (X := {as := i})
    (Y := {as := i'}) (eqToHom (by rw [hi])) {as := j}
  apply_fun (fun T ↦ T.app X) at this
  simp only [endofunctorMonoidalCategory_tensorObj_obj, MonoidalCategory.eqToHom_whiskerRight,
    NatTrans.comp_app] at this
  change _ ≫ (shiftFunctorAdd C i' j).inv.app X = (shiftFunctorAdd C i j).inv.app X ≫ _ at this
  simp only [Functor.comp_obj, endofunctorMonoidalCategory_whiskerRight_app] at this
  set f : ((shiftMonoidalFunctor C A).obj (MonoidalCategory.tensorObj { as := i' }
    { as := j })).obj X ⟶ ((shiftMonoidalFunctor C A).obj
    (MonoidalCategory.tensorObj { as := i } { as := j })).obj X := eqToHom (by rw [hi])
  rw [← cancel_mono f] at this
  simp only [eqToHom_map, eqToHom_app, assoc, eqToHom_trans, eqToHom_refl, comp_id, f] at this
  rw [← this]
  have := (shiftMonoidalFunctor C A).μ_natural_right (X := {as := j})
    (Y := {as := j'}) {as := i'} (eqToHom (by rw [hj]))
  apply_fun (fun T ↦ T.app X) at this
  simp only [endofunctorMonoidalCategory_tensorObj_obj, MonoidalCategory.eqToHom_whiskerRight,
    NatTrans.comp_app] at this
  change _ ≫ (shiftFunctorAdd C i' j').inv.app X = (shiftFunctorAdd C i' j).inv.app X ≫ _ at this
  simp only [Functor.comp_obj, MonoidalCategory.whiskerLeft_eqToHom, eqToHom_app,
    endofunctorMonoidalCategory_tensorObj_obj, eqToHom_map, eqToHom_app] at this
  set f : ((shiftMonoidalFunctor C A).obj (MonoidalCategory.tensorObj { as := i' }
    { as := j' })).obj X ⟶ ((shiftMonoidalFunctor C A).obj
    (MonoidalCategory.tensorObj { as := i' } { as := j })).obj X := eqToHom (by rw [hj])
  rw [← cancel_mono f] at this
  simp only [assoc, eqToHom_trans, eqToHom_refl, comp_id, f] at this
  rw [← this]
  simp

lemma shiftFunctorAdd_eqToIso (i j i' j' : A) (hi : i = i') (hj : j = j') :
    shiftFunctorAdd C i j = eqToIso (by rw [hi, hj]) ≪≫
    shiftFunctorAdd C i' j' ≪≫ eqToIso (by rw [hi, hj]) := by
  conv_lhs => rw [← Iso.symm_symm_eq (shiftFunctorAdd C i j),
                shiftFunctorAdd_symm_eqToIso i j i' j' hi hj]
  ext X
  simp

lemma shiftFunctorAdd'_symm_eqToIso (i j k i' j' k' : A) (h : i + j = k) (h' : i' + j' = k')
    (hi : i = i') (hj : j = j') :
    (shiftFunctorAdd' C i j k h).symm = eqToIso (by rw [hi, hj]) ≪≫
    (shiftFunctorAdd' C i' j' k' h').symm ≪≫ eqToIso (by rw [← h, ← h', hi, hj])
    := by
  dsimp [shiftFunctorAdd']
  rw [shiftFunctorAdd_symm_eqToIso i j i' j' hi hj]
  ext X
  simp only [Functor.comp_obj, Iso.trans_assoc, Iso.trans_hom, eqToIso.hom, Iso.symm_hom,
    eqToIso.inv, eqToHom_trans, NatTrans.comp_app, eqToHom_app]

lemma shiftFunctorAdd'_eqToIso (i j k i' j' k' : A) (h : i + j = k) (h' : i' + j' = k')
    (hi : i = i') (hj : j = j') :
    shiftFunctorAdd' C i j k h = eqToIso (by rw [← h, ← h', hi, hj]) ≪≫
    shiftFunctorAdd' C i' j' k' h' ≪≫ eqToIso (by rw [hi, hj]) := by
  dsimp [shiftFunctorAdd']
  rw [shiftFunctorAdd_eqToIso i j i' j' hi hj]
  ext X
  simp only [Functor.comp_obj, Iso.trans_hom, eqToIso.hom, eqToHom_trans_assoc, NatTrans.comp_app,
    eqToHom_app, Iso.trans_assoc]

end Shift

section

variable {C : Type u} [Category.{v,u} C]

lemma IsIso.comp_left_bijective {X Y Z : C} (f : X ⟶ Y) [IsIso f] :
    Function.Bijective (fun (g : Y ⟶ Z) ↦ f ≫ g) := by
  constructor
  · exact Epi.left_cancellation
  · intro g; existsi inv f ≫ g; simp only [hom_inv_id_assoc]

lemma IsIso.comp_right_bijective {X Y Z : C} (f : X ⟶ Y) [IsIso f] :
    Function.Bijective (fun (g : Z ⟶ X) ↦ g ≫ f) := by
  constructor
  · exact Mono.right_cancellation
  · intro g; existsi g ≫ inv f; simp only [Category.assoc, inv_hom_id, Category.comp_id]

end

open Limits Category Functor Pretriangulated

namespace Triangulated

variable {C : Type u} [Category.{v,u} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

abbrev IsTriangleMorphism (T T' : Triangle C) (u : T.obj₁ ⟶ T'.obj₁) (v : T.obj₂ ⟶ T'.obj₂)
    (w : T.obj₃ ⟶ T'.obj₃) :=
  (T.mor₁ ≫ v = u ≫ T'.mor₁) ∧ (T.mor₂ ≫ w = v ≫ T'.mor₂) ∧
  (T.mor₃ ≫ (shiftFunctor C 1).map u = w ≫ T'.mor₃)

lemma NineGrid' {T_X T_Y : Triangle C} (dT_X : T_X ∈ distinguishedTriangles)
    (dT_Y : T_Y ∈ distinguishedTriangles) (u₁ : T_X.obj₁ ⟶ T_Y.obj₁) (u₂ : T_X.obj₂ ⟶ T_Y.obj₂)
    (comm : T_X.mor₁ ≫ u₂ = u₁ ≫ T_Y.mor₁) {Z₂ : C} (v₂ : T_Y.obj₂ ⟶ Z₂) (w₂ : Z₂ ⟶ T_X.obj₂⟦1⟧)
    (dT₂ : Triangle.mk u₂ v₂ w₂ ∈ distinguishedTriangles) :
    ∃ (Z₁ Z₃ : C) (f : Z₁ ⟶ Z₂) (g : Z₂ ⟶ Z₃) (h : Z₃ ⟶ Z₁⟦1⟧) (v₁ : T_Y.obj₁ ⟶ Z₁)
    (w₁ : Z₁ ⟶ T_X.obj₁⟦1⟧) (u₃ : T_X.obj₃ ⟶ T_Y.obj₃) (v₃ : T_Y.obj₃ ⟶ Z₃)
    (w₃ : Z₃ ⟶ T_X.obj₃⟦1⟧),
    Triangle.mk f g h ∈ distinguishedTriangles ∧
    Triangle.mk u₁ v₁ w₁ ∈ distinguishedTriangles ∧
    Triangle.mk u₃ v₃ w₃ ∈ distinguishedTriangles ∧
    IsTriangleMorphism T_X T_Y u₁ u₂ u₃ ∧
    IsTriangleMorphism T_Y (Triangle.mk f g h) v₁ v₂ v₃ ∧
    w₁ ≫ T_X.mor₁⟦1⟧' = f ≫ w₂ ∧ w₂ ≫ T_X.mor₂⟦1⟧' = g ≫ w₃ ∧
    w₃ ≫ T_X.mor₃⟦1⟧' = - h ≫ w₁⟦1⟧' := by
  obtain ⟨Z₁, v₁, w₁, dT₁⟩ := distinguished_cocone_triangle u₁
  obtain ⟨A, a, b, dTdiag⟩ := distinguished_cocone_triangle (T_X.mor₁ ≫ u₂)
  set oct₁ := someOctahedron (u₁₂ := T_X.mor₁) (u₂₃ := u₂) (u₁₃ := T_X.mor₁ ≫ u₂) rfl dT_X
    dT₂ dTdiag
  set oct₂ := someOctahedron (u₁₂ := u₁) (u₂₃ := T_Y.mor₁) (u₁₃ := T_X.mor₁ ≫ u₂)
    comm.symm dT₁ dT_Y dTdiag
  obtain ⟨Z₃, g, h, dT_Z⟩ := distinguished_cocone_triangle (oct₂.m₁ ≫ oct₁.m₃)
  set oct₃ := someOctahedron (u₁₂ := oct₂.m₁) (u₂₃ := oct₁.m₃) (u₁₃ := oct₂.m₁ ≫ oct₁.m₃) rfl
    oct₂.mem ((rotate_distinguished_triangle _).mp oct₁.mem) dT_Z
  existsi Z₁, Z₃, (oct₂.m₁ ≫ oct₁.m₃), g, h, v₁, w₁, oct₁.m₁ ≫ oct₂.m₃, oct₃.m₁, oct₃.m₃
  constructor
  . exact dT_Z
  · constructor
    · exact dT₁
    · constructor
      · have := inv_rot_of_distTriang _ oct₃.mem
        refine isomorphic_distinguished _ this _ (Triangle.isoMk _ _ ?_ ?_ ?_ ?_ ?_ ?_)
        · have := (shiftFunctorCompIsoId C 1 (-1)
              (by simp only [Int.reduceNeg, add_right_neg])).app T_X.obj₃
          simp only [Int.reduceNeg, Functor.comp_obj, Functor.id_obj] at this
          exact this.symm
        · exact Iso.refl _
        · exact Iso.refl _
        · simp only [Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
          Triangle.invRotate_obj₂, Iso.refl_hom, comp_id, Triangle.invRotate_obj₁, Int.reduceNeg,
          Triangle.mk_obj₃, Iso.symm_hom, Iso.app_inv, Triangle.invRotate_mor₁,
          Preadditive.neg_comp, Functor.map_neg, Functor.map_comp, assoc, neg_neg]
          rw [← cancel_epi ((shiftFunctorCompIsoId C 1 (-1) (by simp only [Int.reduceNeg,
            add_right_neg])).hom.app T_X.obj₃)]
          rw [← cancel_mono ((shiftFunctorCompIsoId C 1 (-1) (by simp only [Int.reduceNeg,
            add_right_neg])).inv.app T_Y.obj₃)]
          rw [assoc]; conv_lhs => erw [← shift_shift_neg']
          simp only [Int.reduceNeg, Functor.comp_obj, Functor.id_obj, Iso.hom_inv_id_app_assoc,
            assoc, Iso.hom_inv_id_app, comp_id]
          simp only [Int.reduceNeg, Functor.map_comp]
        · simp only [Triangle.mk_obj₂, Triangle.invRotate_obj₃, Triangle.mk_obj₃,
          Triangle.mk_mor₂, Iso.refl_hom, comp_id, Triangle.invRotate_obj₂, Triangle.mk_obj₁,
          Triangle.invRotate_mor₂, Triangle.mk_mor₁, id_comp]
        · simp only [Triangle.mk_obj₃, Triangle.invRotate_obj₁, Int.reduceNeg, Triangle.mk_obj₁,
           Triangle.mk_mor₃, id_eq, Iso.symm_hom, Iso.app_inv, Triangle.invRotate_obj₃,
           Triangle.mk_obj₂, Iso.refl_hom, Triangle.invRotate_mor₃, Triangle.mk_mor₂, id_comp]
          rw [shift_shiftFunctorCompIsoId_inv_app]
      · constructor
        · constructor
          · exact comm
          · constructor
            · rw [← assoc, oct₁.comm₁, assoc, oct₂.comm₃]
            · conv_rhs => rw [assoc, ← oct₂.comm₄, ← assoc, oct₁.comm₂]
        · constructor
          · constructor
            · simp only [Triangle.mk_obj₂, Triangle.mk_obj₁, Triangle.mk_mor₁]
              conv_rhs => rw [← assoc, oct₂.comm₁, assoc, oct₁.comm₃]
            · constructor
              · simp only [Triangle.mk_obj₃, Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂,
                Triangle.mk_mor₁, Triangle.mk_mor₂]
                conv_lhs => congr; rw [← oct₂.comm₃]
                rw [assoc, oct₃.comm₁, ← assoc, oct₁.comm₃]
              · exact oct₃.comm₂.symm
          · constructor
            · simp only [Triangle.mk_obj₁, Triangle.shiftFunctor_obj, Int.negOnePow_one,
              Functor.comp_obj, Triangle.mk_obj₂, Triangle.mk_mor₁, assoc, Units.neg_smul, one_smul,
              Preadditive.comp_neg]
              rw [← oct₁.comm₄, ← assoc, oct₂.comm₂]
            · constructor
              · rw [oct₃.comm₃]; simp only [Triangle.mk_mor₃]
              · conv_rhs => congr; rw [← oct₂.comm₂]
                simp only [Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
                  Functor.map_comp]
                conv_lhs => congr; rfl; rw [← oct₁.comm₂]
                have := oct₃.comm₄
                simp only [Triangle.mk_obj₁, Triangle.mk_mor₃, Triangle.mk_obj₂, Triangle.mk_mor₁,
                  Preadditive.comp_neg] at this
                rw [← assoc, this]
                simp only [Functor.map_comp, Preadditive.neg_comp, assoc, neg_neg]

/-- Proposition 1.1.11 of of [BBD].
-/
lemma NineGrid {X₁ X₂ Y₁ Y₂ : C} (u₁ : X₁ ⟶ Y₁) (u₂ : X₂ ⟶ Y₂) (f_X : X₁ ⟶ X₂) (f_Y : Y₁ ⟶ Y₂)
    (comm : f_X ≫ u₂ = u₁ ≫ f_Y) :
    ∃ (X₃ Y₃ Z₁ Z₂ Z₃ : C) (g_X : X₂ ⟶ X₃) (h_X : X₃ ⟶ X₁⟦1⟧) (g_Y : Y₂ ⟶ Y₃)
    (h_Y : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧) (f : Z₁ ⟶ Z₂) (g : Z₂ ⟶ Z₃) (h : Z₃ ⟶ Z₁⟦(1 : ℤ)⟧) (u₃ : X₃ ⟶ Y₃)
    (v₁ : Y₁ ⟶ Z₁) (v₂ : Y₂ ⟶ Z₂) (v₃ : Y₃ ⟶ Z₃) (w₁ : Z₁ ⟶ X₁⟦(1 : ℤ)⟧) (w₂ : Z₂ ⟶ X₂⟦(1 : ℤ)⟧)
    (w₃ : Z₃ ⟶ X₃⟦(1 : ℤ)⟧),
    Triangle.mk f_X g_X h_X ∈ distinguishedTriangles ∧
    Triangle.mk f_Y g_Y h_Y ∈ distinguishedTriangles ∧
    Triangle.mk f g h ∈ distinguishedTriangles ∧
    Triangle.mk u₁ v₁ w₁ ∈ distinguishedTriangles ∧
    Triangle.mk u₂ v₂ w₂ ∈ distinguishedTriangles ∧
    Triangle.mk u₃ v₃ w₃ ∈ distinguishedTriangles ∧
    IsTriangleMorphism (Triangle.mk f_X g_X h_X) (Triangle.mk f_Y g_Y h_Y) u₁ u₂ u₃ ∧
    IsTriangleMorphism (Triangle.mk f_Y g_Y h_Y) (Triangle.mk f g h) v₁ v₂ v₃ ∧
    w₁ ≫ f_X⟦1⟧' = f ≫ w₂ ∧ w₂ ≫ g_X⟦1⟧' = g ≫ w₃ ∧ w₃ ≫ h_X⟦1⟧' = - h ≫ w₁⟦1⟧' := by
  obtain ⟨X₃, g_X, h_X, dT_X⟩ := Pretriangulated.distinguished_cocone_triangle f_X
  obtain ⟨Y₃, g_Y, h_Y, dT_Y⟩ := Pretriangulated.distinguished_cocone_triangle f_Y
  obtain ⟨Z₂, v₂, w₂, dT₂⟩ := Pretriangulated.distinguished_cocone_triangle u₂
  obtain ⟨Z₁, Z₃, f, g, h, v₁, w₁, u₃, v₃, w₃, dT_Z, dT₁, dT₃, comm_XY, comm_YZ, comm₁, comm₂,
    comm₃⟩ := NineGrid' dT_X dT_Y u₁ u₂ comm v₂ w₂ dT₂
  existsi X₃, Y₃, Z₁, Z₂, Z₃, g_X, h_X, g_Y, h_Y, f, g, h, u₃, v₁, v₂, v₃, w₁, w₂, w₃
  exact ⟨dT_X, dT_Y, dT_Z, dT₁, dT₂, dT₃, comm_XY, comm_YZ, comm₁, comm₂, comm₃⟩

end Triangulated

namespace Pretriangulated

variable {C : Type u} [Category.{v,u} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

noncomputable instance : (Triangle.π₁ (C := C)).CommShift ℤ where
  iso n := by
    refine NatIso.ofComponents (fun X ↦ Iso.refl _) ?_
    intro _ _ _
    simp only [Triangle.shiftFunctor_eq, comp_obj, Triangle.shiftFunctor_obj, Triangle.π₁_obj,
      Triangle.mk_obj₁, Functor.comp_map, Triangle.π₁_map, Triangle.shiftFunctor_map_hom₁,
      Iso.refl_hom, comp_id, id_comp]
  zero := by aesop_cat
  add n m := by
    apply Iso.ext; apply NatTrans.ext; ext T
    simp only [Triangle.shiftFunctor_eq, comp_obj, Triangle.shiftFunctor_obj, Triangle.π₁_obj,
      Triangle.mk_obj₁, NatIso.ofComponents_hom_app, Iso.refl_hom, CommShift.isoAdd_hom_app,
      Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃,
      Triangle.shiftFunctorAdd_eq, Triangle.π₁_map, Triangle.shiftFunctorAdd'_hom_app_hom₁, map_id,
      id_comp]
    rw [shiftFunctorAdd'_eq_shiftFunctorAdd, Iso.hom_inv_id_app]

lemma Triangle_π₁_commShiftIso (a : ℤ) (T : Triangle C) :
    ((Triangle.π₁ (C := C)).commShiftIso a).app T = Iso.refl _ := rfl

lemma Triangle_π₁_commShiftIso_hom (a : ℤ) (T : Triangle C) :
    ((Triangle.π₁ (C := C)).commShiftIso a).hom.app T = 𝟙 _ := rfl

noncomputable instance : (Triangle.π₂ (C := C)).CommShift ℤ where
  iso n := by
    refine NatIso.ofComponents (fun X ↦ Iso.refl _) ?_
    intro _ _ _
    simp only [Triangle.shiftFunctor_eq, comp_obj, Triangle.shiftFunctor_obj, Triangle.π₂_obj,
      Triangle.mk_obj₂, Functor.comp_map, Triangle.π₂_map, Triangle.shiftFunctor_map_hom₂,
      Iso.refl_hom, comp_id, id_comp]
  zero := by aesop_cat
  add n m := by
    apply Iso.ext; apply NatTrans.ext; ext T
    simp only [Triangle.shiftFunctor_eq, comp_obj, Triangle.shiftFunctor_obj, Triangle.π₂_obj,
      Triangle.mk_obj₂, NatIso.ofComponents_hom_app, Iso.refl_hom, CommShift.isoAdd_hom_app,
      Triangle.mk_obj₁, Triangle.mk_obj₃, Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃,
      Triangle.shiftFunctorAdd_eq, Triangle.π₂_map, Triangle.shiftFunctorAdd'_hom_app_hom₂, map_id,
      id_comp]
    rw [shiftFunctorAdd'_eq_shiftFunctorAdd, Iso.hom_inv_id_app]

lemma Triangle_π₂_commShiftIso (a : ℤ) (T : Triangle C) :
    ((Triangle.π₂ (C := C)).commShiftIso a).app T = Iso.refl _ := rfl

lemma Triangle_π₂_commShiftIso_hom (a : ℤ) (T : Triangle C) :
    ((Triangle.π₂ (C := C)).commShiftIso a).hom.app T = 𝟙 _ := rfl

noncomputable instance : (Triangle.π₃ (C := C)).CommShift ℤ where
  iso n := by
    refine NatIso.ofComponents (fun X ↦ Iso.refl _) ?_
    intro _ _ _
    simp only [Triangle.shiftFunctor_eq, comp_obj, Triangle.shiftFunctor_obj, Triangle.π₃_obj,
      Triangle.mk_obj₃, Functor.comp_map, Triangle.π₃_map, Triangle.shiftFunctor_map_hom₃,
      Iso.refl_hom, comp_id, id_comp]
  zero := by aesop_cat
  add n m := by
    apply Iso.ext; apply NatTrans.ext; ext T
    simp only [Triangle.shiftFunctor_eq, comp_obj, Triangle.shiftFunctor_obj, Triangle.π₃_obj,
      Triangle.mk_obj₃, NatIso.ofComponents_hom_app, Iso.refl_hom, CommShift.isoAdd_hom_app,
      Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃,
      Triangle.shiftFunctorAdd_eq, Triangle.π₃_map, Triangle.shiftFunctorAdd'_hom_app_hom₃, map_id,
      id_comp]
    rw [shiftFunctorAdd'_eq_shiftFunctorAdd, Iso.hom_inv_id_app]

lemma Triangle_π₃_commShiftIso (a : ℤ) (T : Triangle C) :
    ((Triangle.π₃ (C := C)).commShiftIso a).app T = Iso.refl _ := rfl

lemma Triangle_π₃_commShiftIso_hom (a : ℤ) (T : Triangle C) :
    ((Triangle.π₃ (C := C)).commShiftIso a).hom.app T = 𝟙 _ := rfl

end Pretriangulated

namespace Pretriangulated.TriangleMorphism

variable {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]

@[simp]
theorem smul_iso_hom {T₁ T₂ : CategoryTheory.Pretriangulated.Triangle C} (f : T₁ ≅ T₂) (n : ℤˣ) :
    (n • f).hom = n.1 • f.hom := sorry

@[simp]
theorem smul_hom₁ {T₁ T₂ : CategoryTheory.Pretriangulated.Triangle C} (f : T₁ ⟶ T₂) (n : ℤ) :
    (n • f).hom₁ = n • f.hom₁ := sorry

@[simp]
theorem smul_hom₂ {T₁ T₂ : CategoryTheory.Pretriangulated.Triangle C} (f : T₁ ⟶ T₂) (n : ℤ) :
    (n • f).hom₂ = n • f.hom₂ := sorry

@[simp]
theorem smul_hom₃ {T₁ T₂ : CategoryTheory.Pretriangulated.Triangle C} (f : T₁ ⟶ T₂) (n : ℤ) :
    (n • f).hom₃ = n • f.hom₃ := sorry

end Pretriangulated.TriangleMorphism

end CategoryTheory
