import Mathlib.CategoryTheory.Arrow
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.Data.Set.Image

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

lemma Arrow.eq_iff (φ φ' : Arrow C) : φ = φ' ↔ ∃ (h : φ.left = φ'.left)
        (h' : φ.right = φ'.right), φ.hom = eqToHom h ≫ φ'.hom ≫ eqToHom h'.symm := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, by simp⟩
  · cases φ
    cases φ'
    dsimp
    rintro ⟨rfl, rfl, h⟩
    simp only [h, eqToHom_refl, Category.comp_id, Category.id_comp]

lemma Arrow.mk_eq_iff {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    Arrow.mk f = Arrow.mk g ↔ ∃ (h : X = X') (h' : Y = Y'),
      f = eqToHom h ≫ g ≫ eqToHom h'.symm :=
  Arrow.eq_iff _ _

variable (C)

structure Subcategory where
  J : Type w
  s : J → Arrow C
  id₁ : ∀ (i : J), Arrow.mk (𝟙 (s i).left) ∈ Set.range s
  id₂ : ∀ (i : J), Arrow.mk (𝟙 (s i).right) ∈ Set.range s
  comp' : ∀ (i j : J) (hij : (s i).right = (s j).left),
    Arrow.mk ((s i).hom ≫ eqToHom hij ≫ (s j).hom) ∈ Set.range s

namespace Subcategory

variable {C}

variable (S : Subcategory C)

@[pp_dot]
def objSet : Set C :=
  fun X => ∃ (i : S.J), X = (S.s i).left

@[pp_dot]
def obj : Type u := S.objSet

@[pp_dot]
def homSet (X Y : S.obj) : Set (X.1 ⟶ Y.1) := fun f => ∃ (i : S.J), S.s i = Arrow.mk f

@[simp]
lemma mem_homSet_iff {X Y : S.obj} (f : X.1 ⟶ Y.1) :
    f ∈ S.homSet X Y ↔ ∃ (i : S.J), S.s i = Arrow.mk f := by rfl

@[pp_dot]
def hom (X Y : S.obj) : Type v := S.homSet X Y

lemma hom_ext {X Y : S.obj} (f g : S.hom X Y) (h : f.1 = g.1) : f = g :=
  Subtype.ext h

@[simps, pp_dot]
def id (X : S.obj) : S.hom X X := ⟨𝟙 _, by
  obtain ⟨i, hi⟩ := X.2
  · simp only [mem_homSet_iff]
    obtain ⟨j, hj⟩ := S.id₁ i
    exact ⟨j, by convert hj⟩⟩

@[simps, pp_dot]
def comp {X Y Z : S.obj} (f : S.hom X Y) (g : S.hom Y Z) : S.hom X Z := ⟨f.1 ≫ g.1, by
  obtain ⟨i, hi⟩ := f.2
  obtain ⟨j, hj⟩ := g.2
  obtain ⟨k, hk⟩ := S.comp' i j (by rw [hi, hj]; rfl)
  simp only [mem_homSet_iff]
  refine' ⟨k, _⟩
  rw [hk]
  simp [Arrow.eq_iff] at hi hj ⊢
  obtain ⟨h₁, h₂, hi⟩ := hi
  obtain ⟨h₃, h₄, hj⟩ := hj
  exact ⟨h₁, h₄, by simp [hi, hj]⟩⟩

instance : Category S.obj where
  Hom X Y := S.hom X Y
  id := S.id
  comp := S.comp
  id_comp _ := S.hom_ext _ _ (by aesop_cat)
  comp_id _ := S.hom_ext _ _ (by aesop_cat)
  assoc _ _ _ := S.hom_ext _ _ (by aesop_cat)

def S.ι : S.obj ⥤ C where
  obj X := X.1
  map φ := φ.1

instance : Small.{w} S.obj := by
  let π : S.J → S.obj := fun i => ⟨(S.s i).left, ⟨i, rfl⟩⟩
  have : Function.Surjective π := fun X => by
    obtain ⟨i, hi⟩ := X.2
    exact ⟨i, Subtype.ext hi.symm⟩
  exact small_of_surjective this

instance : Small.{w} (Skeleton S.obj) := by
  have : Function.Injective (fromSkeleton S.obj).obj := fun _ _ h => by simpa using h
  exact small_of_injective this

instance : LocallySmall.{w} S.obj := ⟨fun X Y => by
  let Z : Set S.J := fun i => X.1 = (S.s i).left ∧ Y.1 = (S.s i).right
  let π : Z → S.hom X Y := fun i => by
    refine' ⟨eqToHom i.2.1 ≫ (S.s i).hom ≫ eqToHom i.2.2.symm, ⟨i, _⟩ ⟩
    rw [Arrow.eq_iff]
    exact ⟨i.2.1.symm, i.2.2.symm, by simp⟩
  have : Function.Surjective π := fun f => by
    obtain ⟨i, hi⟩ := f.2
    rw [Arrow.eq_iff] at hi
    obtain ⟨h₁, h₂, hi⟩ := hi
    dsimp at h₁ h₂
    exact ⟨⟨i, ⟨h₁.symm, h₂.symm⟩⟩, Subtype.ext (by simp [hi])⟩
  exact small_of_surjective this⟩

instance : EssentiallySmall.{w} S.obj := by
  rw [essentiallySmall_iff]
  constructor <;> infer_instance

end Subcategory

end CategoryTheory
