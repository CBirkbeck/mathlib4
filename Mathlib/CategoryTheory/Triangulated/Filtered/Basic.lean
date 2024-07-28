/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw, Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Shift.Predicate
import Mathlib.CategoryTheory.Triangulated.Lemmas

/-!
# Filtered Triangulated Categories

-/

--set_option diagnostics true

noncomputable section

open CategoryTheory Preadditive Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory

open Category Pretriangulated ZeroObject

/-
We work in a preadditive category `C` equipped with an additive shift.
-/
variable {C : Type u} [Category.{v, u} C] [HasZeroObject C] [HasShift C (ℤ × ℤ)] [Preadditive C]

attribute [local instance] endofunctorMonoidalCategory

instance Shift₁ : HasShift C ℤ where
  shift := (Discrete.addMonoidalFunctor (AddMonoidHom.inl ℤ ℤ)).comp HasShift.shift

def Shift₂ : HasShift C ℤ where
  shift := (Discrete.addMonoidalFunctor (AddMonoidHom.inr ℤ ℤ)).comp HasShift.shift

instance AdditiveShift₁ [∀ (p : ℤ × ℤ), Functor.Additive (shiftFunctor C p)] :
    ∀ (n : ℤ), Functor.Additive (shiftFunctor C n) := by
  intro n
  change Functor.Additive (shiftFunctor C (n, (0 : ℤ)))
  exact inferInstance

instance AdditiveShift₂ [∀ (p : ℤ × ℤ), Functor.Additive (shiftFunctor C p)] :
    ∀ (n : ℤ), Functor.Additive (@shiftFunctor C _ _ _ Shift₂ n) := by
  intro n
  change Functor.Additive (shiftFunctor C ((0 : ℤ), n))
  exact inferInstance

/-
lemma shiftFunctorComm_eq_shift₁FunctorComm (n m : ℤ) :
    shiftFunctorComm C (n, (0 : ℤ)) (m, (0 : ℤ)) = shiftFunctorComm C n m := sorry

lemma shiftFunctorComm_eq_shift₂FunctorComm (n m : ℤ) :
    shiftFunctorComm C ((0 : ℤ), n) ((0 : ℤ), m) = @shiftFunctorComm C _ _ _ Shift₂ n m := sorry
-/

lemma shift₁FunctorZero_eq_shiftFunctorZero :
    shiftFunctorZero C ℤ = shiftFunctorZero C (ℤ × ℤ) := by
  rw [shiftFunctorZero, shiftFunctorZero, Iso.symm_eq_iff]
  apply Iso.ext
  rw [MonoidalFunctor.εIso_hom, MonoidalFunctor.εIso_hom]
  erw [LaxMonoidalFunctor.comp_ε]
  simp only [Functor.comp_obj, Discrete.addMonoidalFunctor_toLaxMonoidalFunctor_ε,
    AddMonoidHom.inl_apply, Discrete.addMonoidal_tensorUnit_as, eqToHom_refl,
    Discrete.functor_map_id, comp_id]
  rfl

lemma shift₁FunctorAdd_eq_shiftFunctorAdd (a b : ℤ) :
    shiftFunctorAdd C a b = shiftFunctorAdd C (a, (0 : ℤ)) (b, (0 : ℤ)) := by sorry

instance Shift₂CommShift₁ (n : ℤ) : (@shiftFunctor C _ _ _ Shift₂ n).CommShift ℤ where
iso := fun m ↦ (shiftFunctorAdd' C (m, (0 : ℤ)) ((0 : ℤ), n) (m, n) (by simp only [Prod.mk_add_mk,
    add_zero, zero_add])).symm.trans (shiftFunctorAdd' C ((0 : ℤ), n) (m, (0 : ℤ)) (m, n)
    (by simp only [Prod.mk_add_mk, add_zero, zero_add]))
zero := by
  simp only
  rw [← shiftFunctorComm_eq]
  ext X
  rw [Functor.CommShift.isoZero_hom_app, shift₁FunctorZero_eq_shiftFunctorZero]
  change _ =  (shiftFunctor C ((0 : ℤ), n)).map ((shiftFunctorZero C (ℤ × ℤ)).hom.app X) ≫
    (shiftFunctorZero C (ℤ × ℤ)).inv.app ((shiftFunctor C ((0 : ℤ), n)).obj X)
  rw [shiftFunctorZero_inv_app_shift]
  slice_rhs 1 2 => rw [← Functor.map_comp]
  simp only [Functor.id_obj, Iso.hom_inv_id_app, Functor.map_id, id_comp]
  rw [← Iso.symm_hom, shiftFunctorComm_symm]
  rfl
add := by
  intro a b
  simp only
  ext A
  simp only [Functor.comp_obj, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.CommShift.isoAdd_hom_app, Functor.map_comp, assoc]
  rw [shift₁FunctorAdd_eq_shiftFunctorAdd]
  sorry

/-
  rw [← shiftFunctorComm_eq, ← shiftFunctorComm_eq, ← shiftFunctorComm_eq]
  ext A
  simp only [Functor.CommShift.isoAdd_hom_app]
  rw [shift₁FunctorAdd_eq_shiftFunctorAdd]
-/

set_option quotPrecheck false in
/-- shifting an object `X` by `(0, n)` is obtained by the notation `X⟪n⟫` -/
notation -- Any better notational suggestions?
X "⟪" n "⟫" => (@shiftFunctor C _ _ _ Shift₂ n).obj X

set_option quotPrecheck false in
/-- shifting a morphism `f` by `(0, n)` is obtained by the notation `f⟪n⟫'` -/
notation f "⟪" n "⟫'" => (@shiftFunctor C _ _ _ Shift₂ n).map f

namespace Triangulated

variable (C)

/-- Definition of a filtered pretriangulated category.
-/
class FilteredTriangulated [∀ p : ℤ × ℤ, Functor.Additive (shiftFunctor C p)]
  [hC : Pretriangulated C]
where
  /-- the second shift acts by triangulated functors -/
  shift₂_triangle : ∀ (n : ℤ), (@shiftFunctor C _ _ _ Shift₂ n).IsTriangulated
  /-- morphism into the object with shifted filtration -/
  α : 𝟭 C ⟶ @shiftFunctor C _ _ _ Shift₂ 1
  /-- objets with filtration concentrated in degree `≤ n` -/
  LE : ℤ → Triangulated.Subcategory C
  /-- objets with filtration concentrated in degree `≥ n` -/
  GE : ℤ → Triangulated.Subcategory C
  LE_closedUnderIsomorphisms : ∀ (n : ℤ), ClosedUnderIsomorphisms (LE n).P := by infer_instance
  GE_closedUnderIsomorphisms : ∀ (n : ℤ), ClosedUnderIsomorphisms (GE n).P := by infer_instance
  LE_zero_le : (LE 0).P ≤ (LE 1).P
  GE_one_le : (GE 1).P ≤ (GE 0).P
  LE_shift : ∀ (n a n' : ℤ), a + n = n' → ∀ (X : C), (LE n).P X → (LE n').P (X⟪a⟫)
  GE_shift : ∀ (n a n' : ℤ), a + n = n' → ∀ (X : C), (GE n).P X → (GE n').P (X⟪a⟫)
  zero' : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (GE 1).P X → (LE 0).P Y → f = 0
  adj_left : ∀ ⦃X Y : C⦄, (GE 1).P X → (LE 0).P Y → Function.Bijective
    (fun (f : Y⟪1⟫ ⟶ X) ↦ (α.app Y ≫ f : Y ⟶ X))
  adj_right : ∀ ⦃X Y : C⦄, (GE 1).P X → (LE 0).P Y → Function.Bijective
    (fun (f : Y ⟶ X) ↦ (f ≫ α.app X : Y ⟶ (X⟪1⟫)))
  LE_exhaustive : ∀ (X : C), ∃ (n : ℤ), (LE n).P X
  GE_exhaustive : ∀ (X : C), ∃ (n : ℤ), (GE n).P X
  α_s : ∀ (X : C), (α.app X)⟪1⟫' = α.app (X⟪1⟫)
  exists_triangle_one_zero : ∀ (X : C), ∃ (A : C) (B : C) (_ : (GE 1).P A) (_ : (LE 0).P B)
    (f : A ⟶ X) (g : X ⟶ B) (h : B ⟶ A⟦1⟧),
    Triangle.mk f g h ∈ distinguishedTriangles

namespace FilteredTriangulated

attribute [instance] LE_closedUnderIsomorphisms GE_closedUnderIsomorphisms

variable {C}

variable [∀ p : ℤ × ℤ, Functor.Additive (CategoryTheory.shiftFunctor C p)]
  [hC : Pretriangulated C] [hP : FilteredTriangulated C]

lemma exists_triangle (A : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    ∃ (X Y : C) (_ : (GE n₁).P X) (_ : (LE n₀).P Y) (f : X ⟶ A) (g : A ⟶ Y)
      (h : Y ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨X, Y, hX, hY, f, g, h, mem⟩ := exists_triangle_one_zero (A⟪-n₀⟫)
  let T := (@Functor.mapTriangle _ _ _ _ _ _ (@shiftFunctor C _ _ _ Shift₂ n₀)
    (Shift₂CommShift₁ n₀)).obj (Triangle.mk f g h)
  let e := (@shiftEquiv' C _ _ _ Shift₂ (-n₀) n₀ (by rw [add_left_neg])).unitIso.symm.app A
  have hT' : Triangle.mk (T.mor₁ ≫ e.hom) (e.inv ≫ T.mor₂) T.mor₃ ∈ distTriang C := by
    refine isomorphic_distinguished _ (@Functor.IsTriangulated.map_distinguished _ _ _ _ _ _
      (@shiftFunctor C _ _ _ Shift₂ n₀) (Shift₂CommShift₁ n₀) _ _ _ _ _ _ _ _
      (shift₂_triangle n₀) _ mem) _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_
    all_goals dsimp; simp [T]
  exact ⟨_, _, GE_shift _ _ _ (by omega) _ hX, LE_shift _ _ _ (by omega) _ hY, _, _, _, hT'⟩

/- Are the following two lemmas even useful?-/
lemma predicateShift_LE (n n' a : ℤ) (hn' : n = n') :
    (PredicateShift (LE n).P a) = (hP.LE n').P := by
  ext X; sorry
--  simp only [PredicateShift, Triangulated.Subcategory.shift_iff, hn']
-- might need to add lemmas from jriou_lozalization

lemma predicateShift_GE (a n n' : ℤ) (hn' : n = n') :
    (PredicateShift (GE n).P a) = (hP.GE n').P := by
  ext X; sorry
--  simp only [PredicateShift, hn', Triangulated.Subcategory.shift_iff]
-- might need to add lemmas from jriou_lozalization

lemma LE_monotone : Monotone (fun n ↦ (hP.LE n).P) := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), (LE n).P ≤ (hP.LE (n + a)).P
  suffices ∀ (a : ℕ), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by omega
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX =>
    (LE_closedUnderIsomorphisms (n + 1)).of_iso ((@shiftEquiv' C _ _ _ Shift₂
    (-n) n (by rw [add_left_neg])).unitIso.symm.app X) (LE_shift 1 n (n + 1) rfl _
    (LE_zero_le _ (LE_shift n (-n) 0 (by rw [add_left_neg]) X hX)))
  have H_add : ∀ (a b c : ℕ) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h, Nat.cast_add, ← add_assoc]
    exact (ha n).trans (hb (n+a))
  intro a
  induction' a with a ha
  · exact H_zero
  · exact H_add a 1 _ rfl ha H_one

lemma GE_antitone : Antitone (fun n ↦ (hP.GE n).P) := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), (GE (n + a)).P ≤ (hP.GE n).P
  suffices ∀ (a : ℕ), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by omega
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX =>
    (GE_closedUnderIsomorphisms n).of_iso ((@shiftEquiv' C _ _ _ Shift₂
    (-n) n (by rw [add_left_neg])).unitIso.symm.app X) (GE_shift 0 n n (by rw [add_zero]) _
    (GE_one_le _ (GE_shift (n + 1) (-n) 1 (by rw [neg_add_cancel_left]) X hX)))
  have H_add : ∀ (a b c : ℕ) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h, Nat.cast_add, ← add_assoc ]
    exact (hb (n + a)).trans (ha n)
  intro a
  induction' a with a ha
  · exact H_zero
  · exact H_add a 1 _ rfl ha H_one

/-- Given a filtration `F` on a pretriangulated category `C`, the property `IsLE X n`
holds if `X : C` is `≤ n` for the filtration. -/
class IsLE (X : C) (n : ℤ) : Prop where
  le : (hP.LE n).P X

/-- Given a filtration `F` on a pretriangulated category `C`, the property `IsGE X n`
holds if `X : C` is `≥ n` for the filtration. -/
class IsGE (X : C) (n : ℤ) : Prop where
  ge : (hP.GE n).P X

lemma mem_of_isLE (X : C) (n : ℤ) [IsLE X n] : (LE n).P X := IsLE.le

lemma mem_of_isGE (X : C) (n : ℤ) [IsGE X n] : (GE n).P X := IsGE.ge

-- Should the following be instances or lemmas? Let's make them instances and see what happens.
instance zero_isLE (n : ℤ) : IsLE (0 : C) n := {le := (LE n).zero}

instance zero_isGE (n : ℤ) : IsGE (0 : C) n := {ge := (GE n).zero}

instance shift_isLE_of_isLE (X : C) (n a : ℤ) [IsLE X n] : IsLE (X⟦a⟧) n :=
  {le := (LE n).shift X a (mem_of_isLE X n)}

instance shift_isGE_of_isGE (X : C) (n a : ℤ) [IsGE X n] : IsGE (X⟦a⟧) n :=
  {ge := (GE n).shift X a (mem_of_isGE X n)}

instance LE_ext₁ (T : Triangle C) (hT : T ∈ distinguishedTriangles) (n : ℤ) [IsLE T.obj₂ n]
    [IsLE T.obj₃ n] : IsLE T.obj₁ n :=
  {le := (LE n).ext₁ T hT (mem_of_isLE T.obj₂ n) (mem_of_isLE T.obj₃ n)}

instance LE_ext₂ (T : Triangle C) (hT : T ∈ distinguishedTriangles) (n : ℤ) [IsLE T.obj₁ n]
    [IsLE T.obj₃ n] : IsLE T.obj₂ n :=
  {le := (LE n).ext₂ T hT (mem_of_isLE T.obj₁ n) (mem_of_isLE T.obj₃ n)}

instance LE_ext₃ (T : Triangle C) (hT : T ∈ distinguishedTriangles) (n : ℤ) [IsLE T.obj₁ n]
    [IsLE T.obj₂ n] : IsLE T.obj₃ n :=
  {le := (LE n).ext₃ T hT (mem_of_isLE T.obj₁ n) (mem_of_isLE T.obj₂ n)}

instance GE_ext₁ (T : Triangle C) (hT : T ∈ distinguishedTriangles) (n : ℤ) [IsGE T.obj₂ n]
    [IsGE T.obj₃ n] : IsGE T.obj₁ n :=
  {ge := (GE n).ext₁ T hT (mem_of_isGE T.obj₂ n) (mem_of_isGE T.obj₃ n)}

instance GE_ext₂ (T : Triangle C) (hT : T ∈ distinguishedTriangles) (n : ℤ) [IsGE T.obj₁ n]
    [IsGE T.obj₃ n] : IsGE T.obj₂ n :=
  {ge := (GE n).ext₂ T hT (mem_of_isGE T.obj₁ n) (mem_of_isGE T.obj₃ n)}

instance GE_ext₃ (T : Triangle C) (hT : T ∈ distinguishedTriangles) (n : ℤ) [IsGE T.obj₁ n]
    [IsGE T.obj₂ n] : IsGE T.obj₃ n :=
  {ge := (GE n).ext₃ T hT (mem_of_isGE T.obj₁ n) (mem_of_isGE T.obj₂ n)}

lemma isLE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [IsLE X n] : IsLE Y n where
  le := mem_of_iso (LE n).P e (mem_of_isLE X n)

lemma isGE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [IsGE X n] : IsGE Y n where
  ge := mem_of_iso (GE n).P e (mem_of_isGE X n)

lemma isLE_of_LE (X : C) (p q : ℤ) (hpq : p ≤ q) [IsLE X p] : IsLE X q where
  le := LE_monotone hpq _ (mem_of_isLE X p)

lemma isGE_of_GE (X : C) (p q : ℤ) (hpq : p ≤ q) [IsGE X q] : IsGE X p where
  ge := GE_antitone hpq _ (mem_of_isGE X q)

lemma isLE_shift (X : C) (n a n' : ℤ) (hn' : a + n = n') [IsLE X n] :
    IsLE (X⟪a⟫) n' :=
  ⟨LE_shift n a n' hn' X (mem_of_isLE X n)⟩

lemma isGE_shift (X : C) (n a n' : ℤ) (hn' : a + n = n') [IsGE X n] :
    IsGE (X⟪a⟫) n' :=
  ⟨GE_shift n a n' hn' X (mem_of_isGE X n)⟩

lemma isLE_of_shift (X : C) (n a n' : ℤ) (hn' : a + n = n') [IsLE (X⟪a⟫) n'] :
    IsLE X n := by
  have h := isLE_shift (X⟪a⟫) n' (-a) n (by linarith)
  exact isLE_of_iso (show ((X⟪a⟫)⟪-a⟫) ≅ X from
  (@shiftEquiv C _ _ _ Shift₂ a).unitIso.symm.app X) n

lemma isGE_of_shift (X : C) (n a n' : ℤ) (hn' : a + n = n') [IsGE (X⟪a⟫) n'] :
    IsGE X n := by
  have h := isGE_shift (X⟪a⟫) n' (-a) n (by linarith)
  exact isGE_of_iso (show ((X⟪a⟫)⟪-a⟫) ≅ X from
  (@shiftEquiv C _ _ _ Shift₂ a).unitIso.symm.app X) n

lemma isLE_shift_iff (X : C) (n a n' : ℤ) (hn' : a + n = n') :
    IsLE (X⟪a⟫) n' ↔ IsLE X n := by
  constructor
  · intro
    exact isLE_of_shift X n a n' hn'
  · intro
    exact isLE_shift X n a n' hn'

lemma isGE_shift_iff (X : C) (n a n' : ℤ) (hn' : a + n = n') :
    IsGE (X⟪a⟫) n' ↔ IsGE X n := by
  constructor
  · intro
    exact isGE_of_shift X n a n' hn'
  · intro
    exact isGE_shift X n a n' hn'

lemma zero {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    [IsGE X n₁] [IsLE Y n₀] : f = 0 := by
  have := isLE_shift Y n₀ (-n₀) 0 (by simp only [add_left_neg])
  have := isGE_shift X n₁ (-n₀) (n₁-n₀) (by linarith)
  have := isGE_of_GE (X⟪-n₀⟫) 1 (n₁-n₀) (by linarith)
  apply (@shiftFunctor C _ _ _ Shift₂ (-n₀)).map_injective
  simp only [Functor.map_zero]
  apply zero'
  · apply mem_of_isGE
  · apply mem_of_isLE

lemma zero_of_isGE_of_isLE {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    (_ : IsGE X n₁) (_ : IsLE Y n₀) : f = 0 :=
  zero f n₀ n₁ h

lemma isZero (X : C) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    [IsGE X n₁] [IsLE X n₀] : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  exact zero _ n₀ n₁ h

def core (X : C) : Prop := (LE 0).P X ∧ (GE 0).P X

lemma mem_core_iff (X : C) :
    core X ↔ IsLE X 0 ∧ IsGE X 0 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨h₁⟩, ⟨h₂⟩⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨mem_of_isLE _ _, mem_of_isGE _ _⟩

def tCore : Triangulated.Subcategory C where
  P := core
  zero' := by
    existsi 0, isZero_zero C
    rw [mem_core_iff]
    exact ⟨inferInstance, inferInstance⟩
  shift X n hX := by
    rw [mem_core_iff] at hX ⊢
    have := hX.1; have := hX.2
    exact ⟨inferInstance, inferInstance⟩
  ext₂' T dT hT₁ hT₃ := by
    apply le_isoClosure
    rw [mem_core_iff] at hT₁ hT₃ ⊢
    constructor
    · have := hT₁.1; have := hT₃.1
      exact LE_ext₂ T dT 0
    · have := hT₁.2; have := hT₃.2
      exact GE_ext₂  T dT 0

lemma mem_tCore_iff (X : C) :
    tCore.P X ↔ IsLE X 0 ∧ IsGE X 0 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨h₁⟩, ⟨h₂⟩⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨mem_of_isLE _ _, mem_of_isGE _ _⟩

instance : ClosedUnderIsomorphisms (tCore (C := C)).P where
  of_iso {X Y} e hX := by
    rw [mem_tCore_iff] at hX ⊢
    have := hX.1
    have := hX.2
    constructor
    · exact isLE_of_iso e 0
    · exact isGE_of_iso e 0

abbrev Core' := (tCore (C := C)).category

abbrev ιCore' : Core' (C := C) ⥤ C := fullSubcategoryInclusion _

instance : Functor.Additive (ιCore' (C := C)) := sorry

instance : Functor.Full (ιCore' (C := C)) := sorry

instance : Functor.Faithful (ιCore' (C := C)) := sorry


instance (X : Core') : IsLE (C := C) (ιCore'.obj X) 0 := ⟨X.2.1⟩
instance (X : Core') : IsGE (C := C) (ιCore'.obj X) 0 := ⟨X.2.2⟩
instance (X : Core') : IsLE X.1 0 (C := C) := ⟨X.2.1⟩
instance (X : Core') : IsGE X.1 0 (C := C) := ⟨X.2.2⟩

lemma ιCore_obj_mem_core (X : Core') : core (C := C) (ιCore'.obj X) := X.2

/-
def ιHeartDegree (n : ℤ) : t.Heart' ⥤ C :=
  t.ιHeart' ⋙ shiftFunctor C (-n)

noncomputable def ιHeartDegreeCompShiftIso (n : ℤ) : t.ιHeartDegree n ⋙ shiftFunctor C n ≅ t.ιHeart' :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (shiftFunctorCompIsoId C (-n) n (add_left_neg n)) ≪≫
    Functor.rightUnitor _
-/

variable (C)

class HasCore where
  H : Type*
  [cat : Category H]
  [preadditive : Preadditive H]
  ι : H ⥤ C
  additive_ι : ι.Additive := by infer_instance
  fullι : ι.Full := by infer_instance
  faithful_ι : ι.Faithful := by infer_instance
  hι : ι.essImage = setOf tCore.P := by simp

variable {C}

def hasCoreFullSubcategory : HasCore C where
  H := Core'
  ι := ιCore'
  hι := by
    ext X
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      refine ClosedUnderIsomorphisms.of_iso (Functor.essImage.getIso h ) ?_
      exact (Functor.essImage.witness h).2
    · intro h
      change (fullSubcategoryInclusion core).obj ⟨X, h⟩ ∈ _
      exact Functor.obj_mem_essImage _ _

variable [ht : HasCore C]

def Core := ht.H

instance : Category (Core (C := C)) := ht.cat

def ιCore : Core (C := C) ⥤ C := ht.ι

instance : Preadditive (Core (C := C)) := ht.preadditive
instance : (ιCore (C := C)).Full := ht.fullι
instance : (ιCore (C := C)).Faithful := ht.faithful_ι
instance : (ιCore (C := C)).Additive := ht.additive_ι

-- Add instances saying that the core is triangulated and the inclusion is a triangulated functor.

lemma ιCore_obj_mem (X : Core (C := C)) : tCore.P (ιCore.obj X) := by
  change (ιCore.obj X) ∈ setOf tCore.P
  rw [← ht.hι]
  exact ιCore.obj_mem_essImage X

instance (X : Core) : IsLE (C := C) (ιCore.obj X) 0 :=
  ⟨(ιCore_obj_mem X).1⟩

instance (X : Core) : IsGE (C := C) (ιCore.obj X) 0 :=
  ⟨(ιCore_obj_mem X).2⟩

lemma mem_essImage_ιCore_iff (X : C) :
    X ∈ ιCore.essImage ↔ tCore.P X := by
  dsimp [ιCore]
  rw [ht.hι, Set.mem_setOf_eq]

noncomputable def coreMk (X : C) (hX : tCore.P X) : Core (C := C) :=
  Functor.essImage.witness ((mem_essImage_ιCore_iff X).2 hX)

noncomputable def ιCoreObjCoreMkIso (X : C) (hX : tCore.P X) :
    ιCore.obj (coreMk X hX) ≅ X :=
  Functor.essImage.getIso ((mem_essImage_ιCore_iff X).2 hX)

@[simps obj]
noncomputable def liftCore {D : Type*} [Category D]
    (G : D ⥤ C) (hF : ∀ (X : D), tCore.P (G.obj X)) :
    D ⥤ Core (C := C) where
  obj X := coreMk (G.obj X) (hF X)
  map {X Y} f := ιCore.preimage ((ιCoreObjCoreMkIso _ (hF X)).hom ≫ G.map f ≫
      (ιCoreObjCoreMkIso _ (hF Y)).inv)
  map_id X := ιCore.map_injective (by simp)
  map_comp f g := ιCore.map_injective (by simp)

@[simp, reassoc]
lemma ιCore_map_liftCore_map {D : Type*} [Category D]
    (G : D ⥤ C) (hF : ∀ (X : D), tCore.P (G.obj X)) {X Y : D} (f : X ⟶ Y) :
    ιCore.map ((liftCore G hF).map f) =
      (ιCoreObjCoreMkIso _ (hF X)).hom ≫ G.map f ≫
        (ιCoreObjCoreMkIso _ (hF Y)).inv := by
  simp [liftCore]

noncomputable def liftCoreιCore {D : Type*} [Category D]
    (G : D ⥤ C) (hF : ∀ (X : D), tCore.P (G.obj X)) :
    liftCore G hF ⋙ ιCore ≅ G :=
  NatIso.ofComponents (fun X => ιCoreObjCoreMkIso _ (hF X)) (by aesop_cat)

end FilteredTriangulated

end Triangulated

#exit

namespace Subcategory

variable {C}
variable (S : Subcategory C) (t : TStructure C)

class HasInducedTStructure : Prop :=
  exists_triangle_zero_one (A : C) (hA : S.P A) :
    ∃ (X Y : C) (_ : t.LE 0 X) (_ : t.GE 1 Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧) (_ : Triangle.mk f g h ∈ distTriang C),
    X ∈ S.ι.essImage ∧ Y ∈ S.ι.essImage

variable [h : S.HasInducedTStructure t]

def tStructure : TStructure S.category where
  LE n X := t.LE n (S.ι.obj X)
  GE n X := t.GE n (S.ι.obj X)
  LE_closedUnderIsomorphisms n := ⟨fun {X Y} e hX => mem_of_iso (t.LE n) (S.ι.mapIso e) hX⟩
  GE_closedUnderIsomorphisms n := ⟨fun {X Y} e hX => mem_of_iso (t.GE n) (S.ι.mapIso e) hX⟩
  LE_shift n a n' h X hX := mem_of_iso (t.LE n') ((S.ι.commShiftIso a).symm.app X)
    (t.LE_shift n a n' h (S.ι.obj X) hX)
  GE_shift n a n' h X hX := mem_of_iso (t.GE n') ((S.ι.commShiftIso a).symm.app X)
    (t.GE_shift n a n' h (S.ι.obj X) hX)
  zero' {X Y} f hX hY := S.ι.map_injective (by
    rw [Functor.map_zero]
    exact t.zero' (S.ι.map f) hX hY)
  LE_zero_le X hX := t.LE_zero_le _ hX
  GE_one_le X hX := t.GE_one_le _ hX
  exists_triangle_zero_one A := by
    obtain ⟨X, Y, hX, hY, f, g, h, hT, ⟨X', ⟨e⟩⟩, ⟨Y', ⟨e'⟩⟩⟩ :=
      h.exists_triangle_zero_one A.1 A.2
    refine' ⟨X', Y', mem_of_iso (t.LE 0) e.symm hX, mem_of_iso (t.GE 1) e'.symm hY,
      S.ι.preimage (e.hom ≫ f), S.ι.preimage (g ≫ e'.inv),
      S.ι.preimage (e'.hom ≫ h ≫ e.inv⟦(1 : ℤ)⟧' ≫ (S.ι.commShiftIso (1 : ℤ)).inv.app X'),
      isomorphic_distinguished _ hT _ _⟩
    refine' Triangle.isoMk _ _ e (Iso.refl _) e' _ _ _
    · dsimp
      simp
    · dsimp
      simp
    · dsimp
      simp only [Functor.map_preimage, Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj,
        Category.comp_id, Iso.cancel_iso_hom_left, ← Functor.map_comp, Iso.inv_hom_id,
        Functor.map_id]

@[simp]
lemma mem_tStructure_heart_iff (X : S.category) :
    (S.tStructure t).heart X ↔ t.heart X.1 := by
  rfl

lemma tStructure_isLE_iff (X : S.category) (n : ℤ) :
    (S.tStructure t).IsLE X n ↔ t.IsLE (S.ι.obj X) n :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

lemma tStructure_isGE_iff (X : S.category) (n : ℤ) :
    (S.tStructure t).IsGE X n ↔ t.IsGE (S.ι.obj X) n :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

end Subcategory

end Triangulated

end CategoryTheory


end FilteredTriangulated
