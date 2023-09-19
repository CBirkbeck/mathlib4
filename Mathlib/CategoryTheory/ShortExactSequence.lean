import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Homology.Exact
import Mathlib.CategoryTheory.Functor.Fin

-- modified from LTE with some names that I think more mnemonic

universe u v

open CategoryTheory Category CategoryTheory.Limits ZeroObject

variable (C D : Type u)
variable [Category.{v} C] [Category.{v} D]
variable [HasImages C] [HasZeroMorphisms C] [HasKernels C] [HasZeroObject C]
variable [HasImages D] [HasZeroMorphisms D] [HasKernels D] [HasZeroObject D]

namespace CategoryTheory

@[ext] structure SES :=
(l m r : C)
(lm : l ⟶ m)
(mr : m ⟶ r)
(mono : Mono lm := by aesop_cat)
(exact : Exact lm mr := by aesop_cat)
(epi : Epi mr := by aesop_cat)

attribute [instance] SES.mono SES.epi

@[ext] structure SES.morphism (s t : SES C) :=
(l : s.l ⟶ t.l)
(m : s.m ⟶ t.m)
(r : s.r ⟶ t.r)
(comm1 : s.lm ≫ m = l ≫ t.lm := by aesop_cat)
(comm2 : s.mr ≫ r = m ≫ t.mr := by aesop_cat)

attribute [reassoc] SES.morphism.comm1
attribute [reassoc] SES.morphism.comm2

instance SES.instCategory : Category.{v} (SES.{u, v} C) where
  Hom := SES.morphism C
  id s :=
  { l := 𝟙 _
    m := 𝟙 _
    r := 𝟙 _ }
  comp {a b c} m n :=
  { l := m.l ≫ n.l
    m := m.m ≫ n.m
    r := m.r ≫ n.r
    comm1 := by rw [m.comm1_assoc, Category.assoc, ← n.comm1]
    comm2 := by rw [m.comm2_assoc, Category.assoc, ← n.comm2] }

namespace SES

@[simps]
def lFunctor : SES C ⥤ C where
  obj s := s.l
  map f := f.l

@[simps]
def mFunctor : SES C ⥤ C where
  obj s := s.m
  map f := f.m

@[simps]
def rFunctor : SES C ⥤ C where
  obj s := s.r
  map f := f.r

@[simps]
def lmNatTrans : NatTrans (lFunctor C) (mFunctor C) where
  app A := A.lm
  naturality _ _ f := f.comm1.symm

@[simps]
def mrNatTrans : NatTrans (mFunctor C) (rFunctor C) where
  app A := A.mr
  naturality _ _ f := f.comm2.symm

instance : HasZeroMorphisms (SES C) where
  Zero A B :=
  { zero :=
    { l := 0
      m := 0
      r := 0 } }
  comp_zero f s := by
    refine SES.morphism.ext _ _ ?_ ?_ ?_ <;>
    · change _ ≫ 0 = 0
      aesop_cat
  zero_comp := by
    intros
    refine SES.morphism.ext _ _ ?_ ?_ ?_ <;>
    · change 0 ≫ _ = 0
      aesop_cat

variable {C}

@[simp] lemma zero_l (s t : SES C) : (0 : s ⟶ t).l = 0 := rfl
@[simp] lemma zero_m (s t : SES C) : (0 : s ⟶ t).m = 0 := rfl
@[simp] lemma zero_r (s t : SES C) : (0 : s ⟶ t).r = 0 := rfl

def asFunctor (s : SES C) : Fin 3 ⥤ C :=
  fin3FunctorMk ![s.l, s.m, s.r] s.lm s.mr

def asFunctorMap {s t : SES C} (f : s ⟶ t) :
  ∀ i, s.asFunctor.obj i ⟶ t.asFunctor.obj i
| ⟨0, _⟩ => f.l
| ⟨1, _⟩ => f.m
| ⟨2, _⟩ => f.r

lemma asFunctorMap_natural {s t : SES C} (f : s ⟶ t) :
  ∀ (i j : Fin 3) (hij : i ≤ j),
    asFunctorMap f i ≫ t.asFunctor.map hij.hom = s.asFunctor.map hij.hom ≫ asFunctorMap f j
| ⟨0,_⟩, ⟨0,_⟩, _ => by aesop_cat
| ⟨1,_⟩, ⟨1,_⟩, _ => by aesop_cat
| ⟨2,hi⟩, ⟨2,hj⟩, _ => by aesop_cat
| ⟨0,_⟩, ⟨1,_⟩, _ => f.comm1.symm
| ⟨1,_⟩, ⟨2,_⟩, _ => f.comm2.symm
| ⟨i+3,hi⟩, _, _      => by exfalso; linarith
| _, ⟨j+3,hj⟩, _      => by exfalso; linarith
| ⟨i+1,hi⟩, ⟨0,hj⟩, (H : _ ≤ 0) => by exfalso; linarith
| ⟨i+2,hi⟩, ⟨1,hj⟩, (H : _ ≤ 1) => by exfalso; linarith
| ⟨0,hi⟩, ⟨2,hj⟩, hij => by
  have h01 : (0 : Fin 3) ⟶ 1 := homOfLE <| by decide
  have h12 : (1 : Fin 3) ⟶ 2 := homOfLE <| by decide
  calc  asFunctorMap f ⟨0, hi⟩ ≫ t.asFunctor.map hij.hom
    _ = asFunctorMap f ⟨0, hi⟩ ≫ t.asFunctor.map h01 ≫ t.asFunctor.map h12 := ?_
    _ = (asFunctorMap f ⟨0, hi⟩ ≫ t.asFunctor.map h01) ≫ t.asFunctor.map h12 :=
      by rw [Category.assoc]
    _ = (s.asFunctor.map h01 ≫ asFunctorMap f _) ≫ t.asFunctor.map h12 := ?_
    _ = s.asFunctor.map h01 ≫ asFunctorMap f _ ≫ t.asFunctor.map h12 := Category.assoc _ _ _
    _ = s.asFunctor.map h01 ≫ s.asFunctor.map h12 ≫ asFunctorMap f _ := ?_
    _ = s.asFunctor.map hij.hom ≫ asFunctorMap f ⟨2, hj⟩ := ?_
  · rw [← Functor.map_comp]; congr
  · congr 1; exact f.comm1.symm
  · congr 1; exact f.comm2.symm
  · rw [← Functor.map_comp_assoc]; congr 1

@[simps]
protected def functor : SES C ⥤ (Fin 3 ⥤ C) where
  obj := asFunctor
  map f :=
  { app := asFunctorMap f
    naturality := fun _ _ hij => (asFunctorMap_natural f _ _ hij.le).symm }
  map_id _ := by ext i; fin_cases i <;> rfl
  map_comp _ _ := by ext i; fin_cases i <;> rfl

end SES

end CategoryTheory
