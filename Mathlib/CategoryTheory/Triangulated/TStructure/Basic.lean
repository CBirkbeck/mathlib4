import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.RespectsIso
import Mathlib.Tactic.Linarith

open CategoryTheory Category Limits

namespace Set

variable {C : Type _} [Category C] (S : Set C)

variable {A : Type _} [AddMonoid A] [HasShift C A]

def shift (a : A) : Set C := fun X => (X⟦a⟧ ∈ S)

lemma mem_shift_iff (a : A) (X : C) : X ∈ S.shift a ↔ X⟦a⟧ ∈ S := by rfl

lemma shift_respectsIso (a : A) [S.RespectsIso] : (S.shift a).RespectsIso where
  condition {X Y} e hX := by
    simp only [mem_shift_iff] at hX ⊢
    exact mem_of_iso S ((shiftFunctor C a).mapIso e) hX

variable (A)

@[simp]
lemma shift_zero [S.RespectsIso] : S.shift (0 : A) = S := by
  ext X
  simp only [mem_shift_iff]
  exact mem_iff_of_iso S ((shiftFunctorZero C A).app X)

variable {A}

lemma shift_shift (a b c : A) (h : a + b = c) [S.RespectsIso] :
    (S.shift b).shift a = S.shift c := by
  ext X
  simp only [mem_shift_iff]
  exact mem_iff_of_iso _ ((shiftFunctorAdd' C a b c h).symm.app X)

end Set

namespace CategoryTheory

@[simp]
lemma essImageFullSubcategoryInclusion {C : Type*} [Category C] (S : Set C) [S.RespectsIso] :
    (fullSubcategoryInclusion S).essImage = S := by
  ext X
  constructor
  · rintro ⟨Y, ⟨e⟩⟩
    rw [← S.mem_iff_of_iso e]
    exact Y.2
  · intro hX
    exact ⟨⟨X, hX⟩, ⟨Iso.refl _⟩⟩

variable (C : Type _) [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

open Pretriangulated

namespace Triangulated

structure TStructure where
  setLE (n : ℤ) : Set C
  setGE (n : ℤ) : Set C
  setLE_respectsIso (n : ℤ) : (setLE n).RespectsIso
  setGE_respectsIso (n : ℤ) : (setGE n).RespectsIso
  shift_mem_setLE (n a n' : ℤ) (h : a + n' = n) (X : C) (hX : X ∈ setLE n) : X⟦a⟧ ∈ setLE n'
  shift_mem_setGE (n a n' : ℤ) (h : a + n' = n) (X : C) (hX : X ∈ setGE n) : X⟦a⟧ ∈ setGE n'
  zero' ⦃X Y : C⦄ (f : X ⟶ Y) (hX : X ∈ setLE 0) (hY : Y ∈ setGE 1) : f = 0
  setLE_zero_subset : setLE 0 ⊆ setLE 1
  setGE_one_subset : setGE 1 ⊆ setGE 0
  exists_triangle_zero_one (A : C) : ∃ (X Y : C) (_ : X ∈ setLE 0) (_ : Y ∈ setGE 1)
    (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C

namespace TStructure

attribute [instance] setLE_respectsIso setGE_respectsIso

noncomputable def mk' (setLEZero : Set C) (setGEZero : Set C)
    [setLEZero.RespectsIso] [setGEZero.RespectsIso]
    (zero : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), X ∈ setLEZero → Y⟦(1 : ℤ)⟧ ∈ setGEZero → f = 0)
    (setLE_zero_subset' : setLEZero ⊆ setLEZero.shift (1 : ℤ))
    (setGE_zero_subset' : setGEZero.shift (1 : ℤ) ⊆ setGEZero)
    (exists_triangle_zero_one' : ∀ (A : C), ∃ (X Y : C) (_ : X ∈ setLEZero)
      (_ : Y⟦(1 : ℤ)⟧ ∈ setGEZero) (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C) :
    TStructure C where
  setLE n := setLEZero.shift n
  setGE n := setGEZero.shift n
  setLE_respectsIso n := Set.shift_respectsIso _ _
  setGE_respectsIso n := Set.shift_respectsIso _ _
  shift_mem_setLE := by
    rintro n a n' h X hX
    simpa only [← setLEZero.shift_shift _ _ _ h] using hX
  shift_mem_setGE := by
    rintro n a n' h X hX
    simpa only [← setGEZero.shift_shift _ _ _ h] using hX
  zero' := fun X Y f hX hY => zero f (by simpa only [Set.shift_zero] using hX) hY
  setLE_zero_subset := by simpa only [Set.shift_zero] using setLE_zero_subset'
  setGE_one_subset := by simpa only [Set.shift_zero] using setGE_zero_subset'
  exists_triangle_zero_one := by simpa only [Set.shift_zero] using exists_triangle_zero_one'

variable {C}
variable (t : TStructure C)

lemma exists_triangle (A : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    ∃ (X Y : C) (_ : X ∈ t.setLE n₀) (_ : Y ∈ t.setGE n₁) (f : X ⟶ A) (g : A ⟶ Y)
      (h : Y ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨X, Y, hX, hY, f, g, h, mem⟩ := t.exists_triangle_zero_one (A⟦n₀⟧)
  let T := (Triangle.shiftFunctor C (-n₀)).obj (Triangle.mk f g h)
  have e := (shiftEquiv C n₀).unitIso.symm.app A
  have hT' : Triangle.mk (T.mor₁ ≫ e.hom) (e.inv ≫ T.mor₂) T.mor₃ ∈ distTriang C := by
    refine' isomorphic_distinguished _ (Triangle.shift_distinguished _ mem (-n₀)) _ _
    refine' Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) _ _ _
    all_goals dsimp ; simp [T]
  exact ⟨_, _, t.shift_mem_setLE _ _ _ (neg_add_self n₀) _ hX,
    t.shift_mem_setGE _ _ _ (by linarith) _ hY, _, _, _, hT'⟩

lemma shift_setLE (a n n' : ℤ) (hn' : a + n = n'): ((t.setLE n).shift a) = t.setLE n' := by
  ext X
  constructor
  · intro hX
    rw [Set.mem_shift_iff] at hX
    apply ((setLE t n').mem_iff_of_iso ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.shift_mem_setLE n (-a) n' (by linarith) _ hX)
  · intro hX
    exact t.shift_mem_setLE _ _ _ hn' X hX

lemma shift_setGE (a n n' : ℤ) (hn' : a + n = n'): ((t.setGE n).shift a) = t.setGE n' := by
  ext X
  constructor
  · intro hX
    rw [Set.mem_shift_iff] at hX
    apply ((setGE t n').mem_iff_of_iso ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.shift_mem_setGE n (-a) n' (by linarith) _ hX)
  · intro hX
    exact t.shift_mem_setGE _ _ _ hn' X hX

lemma setLE_monotone (n₀ n₁ : ℤ) (h : n₀ ≤ n₁) : t.setLE n₀ ⊆ t.setLE n₁ := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), t.setLE n ⊆ t.setLE (n + a)
  suffices ∀ (a : ℕ), H a by
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by linarith
    apply this
  clear n₀ n₁ h
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX => by
    rw [← t.shift_setLE n 1 (n+(1 : ℕ)) rfl, Set.mem_shift_iff]
    rw [← t.shift_setLE n 0 n (add_zero n), Set.mem_shift_iff] at hX
    exact t.setLE_zero_subset hX
  have H_add : ∀ (a b c : ℕ) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h, Nat.cast_add, ← add_assoc]
    exact (ha n).trans (hb (n+a))
  intro a
  induction' a with a ha
  · exact H_zero
  · exact H_add a 1 _ rfl ha H_one

lemma setGE_antitone (n₀ n₁ : ℤ) (h : n₀ ≤ n₁) : t.setGE n₁ ⊆ t.setGE n₀ := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), t.setGE (n + a) ⊆ t.setGE n
  suffices ∀ (a : ℕ), H a by
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by linarith
    apply this
  clear n₀ n₁ h
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX => by
    rw [← t.shift_setGE n 1 (n + (1 : ℕ)) (by simp), Set.mem_shift_iff] at hX
    rw [← t.shift_setGE n 0 n (add_zero n)]
    exact t.setGE_one_subset hX
  have H_add : ∀ (a b c : ℕ) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h, Nat.cast_add, ← add_assoc ]
    exact (hb (n + a)).trans (ha n)
  intro a
  induction' a with a ha
  · exact H_zero
  · exact H_add a 1 _ rfl ha H_one

class IsLE (X : C) (n : ℤ) : Prop where
  mem : X ∈ t.setLE n

lemma mem_of_isLE (X : C) (n : ℤ) [t.IsLE X n] : X ∈ t.setLE n := IsLE.mem

class IsGE (X : C) (n : ℤ) : Prop where
  mem : X ∈ t.setGE n

lemma mem_of_isGE (X : C) (n : ℤ) [t.IsGE X n] : X ∈ t.setGE n := IsGE.mem

lemma isLE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [t.IsLE X n] : t.IsLE Y n where
  mem := (t.setLE n).mem_of_iso e (t.mem_of_isLE X n)

lemma isGE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [t.IsGE X n] : t.IsGE Y n where
  mem := (t.setGE n).mem_of_iso e (t.mem_of_isGE X n)

lemma isLE_of_LE (X : C) (p q : ℤ) (hpq : p ≤ q) [t.IsLE X p] : t.IsLE X q where
  mem := setLE_monotone t p q hpq (t.mem_of_isLE X p)

lemma isGE_of_GE (X : C) (p q : ℤ) (hpq : p ≤ q) [t.IsGE X q] : t.IsGE X p where
  mem := setGE_antitone t p q hpq (t.mem_of_isGE X q)

lemma isLE_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n) [t.IsLE X n] :
    t.IsLE (X⟦a⟧) n' :=
  ⟨t.shift_mem_setLE n a n' hn' X (t.mem_of_isLE X n)⟩

lemma isGE_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n) [t.IsGE X n] :
    t.IsGE (X⟦a⟧) n' :=
  ⟨t.shift_mem_setGE n a n' hn' X (t.mem_of_isGE X n)⟩

lemma isLE_of_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n) [t.IsLE (X⟦a⟧) n'] :
    t.IsLE X n := by
  have h := t.isLE_shift (X⟦a⟧) n' (-a) n (by linarith)
  exact t.isLE_of_iso (show X⟦a⟧⟦-a⟧ ≅ X from (shiftEquiv C a).unitIso.symm.app X) n

lemma isGE_of_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n) [t.IsGE (X⟦a⟧) n'] :
    t.IsGE X n := by
  have h := t.isGE_shift (X⟦a⟧) n' (-a) n (by linarith)
  exact t.isGE_of_iso (show X⟦a⟧⟦-a⟧ ≅ X from (shiftEquiv C a).unitIso.symm.app X) n

lemma isLE_shift_iff (X : C) (n a n' : ℤ) (hn' : a + n' = n) :
    t.IsLE (X⟦a⟧) n' ↔ t.IsLE X n := by
  constructor
  · intro
    exact t.isLE_of_shift X n a n' hn'
  · intro
    exact t.isLE_shift X n a n' hn'

lemma isGE_shift_iff (X : C) (n a n' : ℤ) (hn' : a + n' = n) :
    t.IsGE (X⟦a⟧) n' ↔ t.IsGE X n := by
  constructor
  · intro
    exact t.isGE_of_shift X n a n' hn'
  · intro
    exact t.isGE_shift X n a n' hn'

lemma zero {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    [t.IsLE X n₀] [t.IsGE Y n₁] : f = 0 := by
  have := t.isLE_shift X n₀ n₀ 0 (add_zero n₀)
  have := t.isGE_shift Y n₁ n₀ (n₁-n₀) (by linarith)
  have := t.isGE_of_GE (Y⟦n₀⟧) 1 (n₁-n₀) (by linarith)
  apply (shiftFunctor C n₀).map_injective
  simp only [Functor.map_zero]
  apply t.zero'
  · apply t.mem_of_isLE
  · apply t.mem_of_isGE

lemma zero_of_isLE_of_isGE {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    (_ : t.IsLE X n₀) (_ : t.IsGE Y n₁) : f = 0 :=
  t.zero f n₀ n₁ h

lemma isZero (X : C) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    [t.IsLE X n₀] [t.IsGE X n₁] : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  exact t.zero _ n₀ n₁ h

def heart : Set C := t.setLE 0 ∩ t.setGE 0

lemma mem_heart_iff (X : C) :
    X ∈ t.heart ↔ t.IsLE X 0 ∧ t.IsGE X 0 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨h₁⟩, ⟨h₂⟩⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨t.mem_of_isLE _ _, t.mem_of_isGE _ _⟩

instance : t.heart.RespectsIso where
  condition X Y e hX := by
    rw [mem_heart_iff] at hX ⊢
    have := hX.1
    have := hX.2
    constructor
    · exact t.isLE_of_iso e 0
    · exact t.isGE_of_iso e 0

-- this should be refactored by requiring a type class [t.HasHeart]
-- which would involve a fully faithful functor `H ⥤ C` whose essential image is `t.heart`

abbrev Heart' := FullSubcategory t.heart

abbrev ιHeart' : t.Heart' ⥤ C := fullSubcategoryInclusion _


instance (X : t.Heart') : t.IsLE (t.ιHeart'.obj X) 0 := ⟨X.2.1⟩
instance (X : t.Heart') : t.IsGE (t.ιHeart'.obj X) 0 := ⟨X.2.2⟩
instance (X : t.Heart') : t.IsLE X.1 0 := ⟨X.2.1⟩
instance (X : t.Heart') : t.IsGE X.1 0 := ⟨X.2.2⟩


lemma ιHeart_obj_mem_heart (X : t.Heart') : t.ιHeart'.obj X ∈ t.heart := X.2

def ιHeartDegree (n : ℤ) : t.Heart' ⥤ C :=
  t.ιHeart' ⋙ shiftFunctor C (-n)

noncomputable def ιHeartDegreeCompShiftIso (n : ℤ) : t.ιHeartDegree n ⋙ shiftFunctor C n ≅ t.ιHeart' :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (shiftFunctorCompIsoId C (-n) n (add_left_neg n)) ≪≫
    Functor.rightUnitor _

class HasHeart where
  H : Type*
  [cat : Category H]
  [preadditive : Preadditive H]
  ι : H ⥤ C
  additive_ι : ι.Additive := by infer_instance
  fullι : Full ι := by infer_instance
  faithful_ι : Faithful ι := by infer_instance
  hι : ι.essImage = t.heart := by simp

def hasHeartFullSubcategory : t.HasHeart where
  H := FullSubcategory t.heart
  ι := fullSubcategoryInclusion t.heart

variable [ht : t.HasHeart]

def Heart := ht.H

instance : Category t.Heart := ht.cat

def ιHeart : t.Heart ⥤ C := ht.ι

instance : Preadditive t.Heart := ht.preadditive
instance : Full t.ιHeart := ht.fullι
instance : Faithful t.ιHeart := ht.faithful_ι
instance : t.ιHeart.Additive := ht.additive_ι

lemma ιHeart_obj_mem (X : t.Heart) : t.ιHeart.obj X ∈ t.heart := by
  rw [← ht.hι]
  exact t.ιHeart.obj_mem_essImage X

instance (X : t.Heart) : t.IsLE (t.ιHeart.obj X) 0 :=
  ⟨(t.ιHeart_obj_mem X).1⟩

instance (X : t.Heart) : t.IsGE (t.ιHeart.obj X) 0 :=
  ⟨(t.ιHeart_obj_mem X).2⟩

lemma mem_essImage_ιHeart_iff (X : C) :
    X ∈ t.ιHeart.essImage ↔ X ∈ t.heart := by
  dsimp [ιHeart]
  rw [ht.hι]

noncomputable def heartMk (X : C) (hX : X ∈ t.heart) : t.Heart :=
  Functor.essImage.witness ((t.mem_essImage_ιHeart_iff X).2 hX)

noncomputable def ιHeartObjHeartMkIso (X : C) (hX : X ∈ t.heart) :
    t.ιHeart.obj (t.heartMk X hX) ≅ X :=
  Functor.essImage.getIso ((t.mem_essImage_ιHeart_iff X).2 hX)

@[simps obj]
noncomputable def liftHeart {D : Type*} [Category D]
    (F : D ⥤ C) (hF : ∀ (X : D), F.obj X ∈ t.heart) :
    D ⥤ t.Heart where
  obj X := t.heartMk (F.obj X) (hF X)
  map {X Y} f := t.ιHeart.preimage ((t.ιHeartObjHeartMkIso _ (hF X)).hom ≫ F.map f ≫
      (t.ιHeartObjHeartMkIso _ (hF Y)).inv)
  map_id X := t.ιHeart.map_injective (by simp)
  map_comp f g := t.ιHeart.map_injective (by simp)

@[simp, reassoc]
lemma ιHeart_map_liftHeart_map {D : Type*} [Category D]
    (F : D ⥤ C) (hF : ∀ (X : D), F.obj X ∈ t.heart) {X Y : D} (f : X ⟶ Y) :
    t.ιHeart.map ((t.liftHeart F hF).map f) =
      (t.ιHeartObjHeartMkIso _ (hF X)).hom ≫ F.map f ≫
        (t.ιHeartObjHeartMkIso _ (hF Y)).inv := by
  simp [liftHeart]

noncomputable def liftHeartιHeart {D : Type*} [Category D]
    (F : D ⥤ C) (hF : ∀ (X : D), F.obj X ∈ t.heart) :
    t.liftHeart F hF ⋙ t.ιHeart ≅ F :=
  NatIso.ofComponents (fun X => t.ιHeartObjHeartMkIso _ (hF X)) (by aesop_cat)

end TStructure

namespace Subcategory

variable {C}
variable (S : Subcategory C) (t : TStructure C)

class HasInducedTStructure : Prop :=
  exists_triangle_zero_one (A : C) (hA : A ∈ S.set) :
    ∃ (X Y : C) (_ : X ∈ t.setLE 0) (_ : Y ∈ t.setGE 1)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧) (_ : Triangle.mk f g h ∈ distTriang C),
    X ∈ S.ι.essImage ∧ Y ∈ S.ι.essImage

variable [h : S.HasInducedTStructure t]

def tStructure : TStructure S.category where
  setLE n X := t.setLE n (S.ι.obj X)
  setGE n X := t.setGE n (S.ι.obj X)
  setLE_respectsIso n := ⟨fun X Y e hX => (t.setLE n).mem_of_iso (S.ι.mapIso e) hX⟩
  setGE_respectsIso n := ⟨fun X Y e hX => (t.setGE n).mem_of_iso (S.ι.mapIso e) hX⟩
  shift_mem_setLE n a n' h X hX := (t.setLE n').mem_of_iso ((S.ι.commShiftIso a).symm.app X)
    (t.shift_mem_setLE n a n' h (S.ι.obj X) hX)
  shift_mem_setGE n a n' h X hX := (t.setGE n').mem_of_iso ((S.ι.commShiftIso a).symm.app X)
    (t.shift_mem_setGE n a n' h (S.ι.obj X) hX)
  zero' {X Y} f hX hY := S.ι.map_injective (by
    rw [Functor.map_zero]
    exact t.zero' (S.ι.map f) hX hY)
  setLE_zero_subset X hX := t.setLE_zero_subset hX
  setGE_one_subset X hX := t.setGE_one_subset hX
  exists_triangle_zero_one A := by
    obtain ⟨X, Y, hX, hY, f, g, h, hT, ⟨X', ⟨e⟩⟩, ⟨Y', ⟨e'⟩⟩⟩ :=
      h.exists_triangle_zero_one A.1 A.2
    refine' ⟨X', Y', (t.setLE 0).mem_of_iso e.symm hX, (t.setGE 1).mem_of_iso e'.symm hY,
      S.ι.preimage (e.hom ≫ f), S.ι.preimage (g ≫ e'.inv),
      S.ι.preimage (e'.hom ≫ h ≫ e.inv⟦(1 : ℤ)⟧' ≫ (S.ι.commShiftIso (1 : ℤ)).inv.app X'),
      isomorphic_distinguished _ hT _ _⟩
    refine' Triangle.isoMk _ _ e (Iso.refl _) e' _ _ _
    · dsimp
      simp
    · dsimp
      simp
    · dsimp
      simp only [Functor.image_preimage, assoc, Iso.inv_hom_id_app, Functor.comp_obj,
        comp_id, Iso.cancel_iso_hom_left, ← Functor.map_comp, Iso.inv_hom_id,
        Functor.map_id]

@[simp]
lemma mem_tStructure_heart_iff (X : S.category) :
    X ∈ (S.tStructure t).heart ↔ X.1 ∈ t.heart := by
  rfl

end Subcategory

end Triangulated

end CategoryTheory
