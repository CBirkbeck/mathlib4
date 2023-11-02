import Mathlib.CategoryTheory.Functor.Hom
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.RepresentationTheory.Action
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Category.Preorder

universe u v w v₁ u₁ u₂

open CategoryTheory Limits Functor

section Stacks

namespace Galois

class ConnectedObject (C : Type u₁) [Category.{v₁} C] (X : C) where
  notInitial : IsInitial X → False
  noTrivialComponent (Y : C) (i : Y ⟶ X) [Mono i] : ¬ IsIso i → IsInitial Y

/- Stacks Project Definition 0BMY -/
class GaloisCategory (C : Type u₁) [Category.{v₁} C] (F : C ⥤ Type v₁) where
  -- properties of C
  hasFiniteLimits : HasFiniteLimits C
  hasFiniteColimits : HasFiniteColimits C
  asFiniteCoproductOfConnected (X : C) :
    ∃ (ι : Type w) (_ : Fintype ι) (f : ι → C) (_ : ∀ i, ConnectedObject C (f i)),
    IsIsomorphic X (∐ f)

  -- properties of F
  imageFinite (X : C) : Fintype (F.obj X)
  reflectsIsos : ReflectsIsomorphisms F
  leftExact : PreservesFiniteLimits F
  rightExact : PreservesFiniteColimits F

variable {C : Type v₁} [Category.{v₁} C] (F : C ⥤ Type v₁) [GaloisCategory C F] 

instance (X : C) : Fintype (F.obj X) := GaloisCategory.imageFinite X

def fundamentalGroup (F : C ⥤ Type v₁) : Type (max v₁ v₁) := Aut F

-- inherit group instance from automorphism group
instance : Group (fundamentalGroup F) := by
  show Group (Aut F)
  exact inferInstance

-- the fundamental group is a profinite group
instance : TopologicalSpace (fundamentalGroup F) := sorry
instance : TopologicalGroup (fundamentalGroup F) := sorry
instance : CompactSpace (fundamentalGroup F) := sorry
instance : TotallyDisconnectedSpace (fundamentalGroup F) := sorry
instance : T2Space (fundamentalGroup F) := sorry

abbrev πTypes := Action (FintypeCat.{v₁}) (MonCat.of (fundamentalGroup F))

def fibreFunctor : C ⥤ πTypes F where
  obj X := {
    V := FintypeCat.of (F.obj X)
    ρ := MonCat.ofHom {
      toFun := fun (g : fundamentalGroup F) ↦ g.hom.app X
      map_one' := rfl
      map_mul' := by aesop
    }
  }
  map f := {
    hom := F.map f
    comm := by
      intro g
      exact symm <| g.hom.naturality f
  }

example : fibreFunctor F ⋙ forget (πTypes F) = F := rfl

theorem fundamental : IsEquivalence (fibreFunctor F) := sorry

end Galois

end Stacks

section SGA

namespace Galois2

section Def

/- Lenstra (G1)-(G3) -/
class PreGaloisCategory (C : Type u) [Category.{v, u} C] : Prop where
  -- (G1)
  hasTerminalObject : HasTerminal C
  hasPullbacks : HasPullbacks C
  -- (G2)
  hasFiniteCoproducts : HasFiniteCoproducts C
  hasQuotientsByFiniteGroups (G : Type w) [Group G] [Finite G] : HasColimitsOfShape C (SingleObj G ⥤ C)
  -- (G3)
  epiMonoFactorisation {X Z : C} (f : X ⟶ Z) : ∃ (Y : C) (p : X ⟶ Y) (i : Y ⟶ Z),
    Epi p ∧ Mono i ∧ p ≫ i = f
  monoInducesIsoOnDirectSummand {X Y : C} (i : X ⟶ Y) [Mono i] : ∃ (Z : C) (u : Z ⟶ Y)
    (_ : IsColimit (BinaryCofan.mk i u)), True

/- Lenstra (G4)-(G6) -/
class FundamentalFunctor {C : Type u} [Category.{v, u} C] [PreGaloisCategory C] (F : C ⥤ Type w) where
  -- (G0)
  imageFinite (X : C) : Fintype (F.obj X)
  -- (G4)
  preservesTerminalObjects : PreservesLimitsOfShape (CategoryTheory.Discrete PEmpty.{1}) F
  --preservesTerminalObjects : IsIsomorphic (F.obj (⊤_ C)) PUnit
  preservesPullbacks : PreservesLimitsOfShape WalkingCospan F
  -- (G5)
  preservesFiniteCoproducts : PreservesFiniteCoproducts F
  preservesEpis : Functor.PreservesEpimorphisms F
  preservesQuotientsByFiniteGroups (G : Type w) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) F
 -- (G6)
  reflectsIsos : ReflectsIsomorphisms F

class ConnectedObject {C : Type u} [Category.{v, u} C] (X : C) : Prop where
  notInitial : IsInitial X → False
  noTrivialComponent (Y : C) (i : Y ⟶ X) [Mono i] : (IsInitial Y → False) → IsIso i

variable {C : Type u} [Category.{v, u} C] [PreGaloisCategory C]

instance : HasTerminal C := PreGaloisCategory.hasTerminalObject
instance : HasPullbacks C := PreGaloisCategory.hasPullbacks
instance : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
instance : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
instance : HasEqualizers C := hasEqualizers_of_hasPullbacks_and_binary_products
instance : HasFiniteCoproducts C := PreGaloisCategory.hasFiniteCoproducts
instance (ι : Type*) [Finite ι] : HasColimitsOfShape (Discrete ι) C :=
  hasColimitsOfShape_discrete C ι
instance : HasInitial C := inferInstance

variable {C : Type u} [Category.{v, u} C] {F : C ⥤ Type w} [PreGaloisCategory C] [FundamentalFunctor F]

instance (X : C) : Fintype (F.obj X) := FundamentalFunctor.imageFinite X

instance : PreservesLimitsOfShape (CategoryTheory.Discrete PEmpty.{1}) F :=
  FundamentalFunctor.preservesTerminalObjects
instance : PreservesLimitsOfShape WalkingCospan F :=
  FundamentalFunctor.preservesPullbacks
instance : PreservesFiniteCoproducts F :=
  FundamentalFunctor.preservesFiniteCoproducts
instance : PreservesColimitsOfShape (Discrete PEmpty.{1}) F :=
  FundamentalFunctor.preservesFiniteCoproducts.preserves PEmpty
instance : ReflectsIsomorphisms F :=
  FundamentalFunctor.reflectsIsos
noncomputable instance : ReflectsColimitsOfShape (Discrete PEmpty.{1}) F :=
  reflectsColimitsOfShapeOfReflectsIsomorphisms

noncomputable instance preservesFiniteLimits : PreservesFiniteLimits F :=
  preservesFiniteLimitsOfPreservesTerminalAndPullbacks F

def preservesInitialObject (O : C) : IsInitial O → IsInitial (F.obj O) :=
  IsInitial.isInitialObj F O

instance preservesMonomorphisms : PreservesMonomorphisms F :=
  preservesMonomorphisms_of_preservesLimitsOfShape F

lemma monoFromPullbackIso {X Y : C} (f : X ⟶ Y) [HasPullback f f]
    [Mono (pullback.fst : pullback f f ⟶ X)] : Mono f where
  right_cancellation g h heq := by
    let u : _ ⟶ pullback f f := pullback.lift g h heq
    let u' : _ ⟶ pullback f f := pullback.lift g g rfl
    trans
    show g = u' ≫ pullback.snd
    exact (pullback.lift_snd g g rfl).symm
    have h2 : u = u' := (cancel_mono pullback.fst).mp (by simp only [limit.lift_π, PullbackCone.mk_π_app])
    rw [←h2]
    simp only [limit.lift_π, PullbackCone.mk_π_app]

lemma monomorphismIffInducesInjective {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective (F.map f) := by
  constructor
  intro hfmono
  have : Mono (F.map f) := preservesMonomorphisms.preserves f
  exact injective_of_mono (F.map f)
  intro hfinj
  have : Mono (F.map f) := (mono_iff_injective (F.map f)).mpr hfinj
  have h2 : IsIso (pullback.fst : pullback (F.map f) (F.map f) ⟶ F.obj X) := fst_iso_of_mono_eq (F.map f)
  let ϕ : F.obj (pullback f f) ≅ pullback (F.map f) (F.map f) := PreservesPullback.iso F f f

  have : ϕ.hom ≫ pullback.fst = F.map pullback.fst := PreservesPullback.iso_hom_fst F f f
  have : IsIso (F.map (pullback.fst : pullback f f ⟶ X)) := by
    rw [←this]
    exact IsIso.comp_isIso
  have : IsIso (pullback.fst : pullback f f ⟶ X) := isIso_of_reflects_iso pullback.fst F
  have : Mono f := monoFromPullbackIso f
  assumption

example (X : C) : ConnectedObject X ↔ ∃ (Y : C) (i : Y ⟶ X), Mono i ∧ ¬ IsIso i ∧ (IsInitial Y → False) := by
  constructor
  intro h
  by_contra h2
  simp at h2

example (X : C) [ConnectedObject X] : ∃ (ι : Type) (D : Discrete ι ⥤ C) (t : Cocone D) (_ : IsColimit t),
    Finite ι ∧ (∀ i, ConnectedObject (D.obj i)) ∧ t.pt = X := by
  use PUnit
  use fromPUnit X
  let t : Cocone (fromPUnit X) := {
    pt := X
    ι := {
      app := by
        intro y
        simp
        exact (𝟙 X)
    }
  }
  have : t.pt = X := rfl
  have : IsColimit t := sorry
  use t
  use this
  simp
  constructor
  exact Finite.of_fintype PUnit.{1}
  assumption

lemma sumOfConnectedComponents (X : C) : ∃ (ι : Type) (D : Discrete ι ⥤ C) (t : Cocone D) (_ : IsColimit t),
    Finite ι ∧ (∀ i, ConnectedObject (D.obj i)) ∧ t.pt = X := by
  simp
  induction' Nat.card (F.obj X) using Nat.strong_induction_on with n hi
  by_cases ConnectedObject X
  . use PUnit
    simp
  . by_cases (IsInitial X → False)
    . have : ¬ (∀ (Y : C) (i : Y ⟶ X) [Mono i], (IsInitial Y → False) → IsIso i) := sorry
      simp at this
      obtain ⟨Y, hnotinitial, i, himono, hinoiso⟩ := this
      have : Function.Injective (F.map i) := (monomorphismIffInducesInjective i).mp himono
      have : Nat.card (F.obj Y) ≠ 0 := sorry
      have : Nat.card (F.obj Y) < Nat.card (F.obj X) := sorry
      obtain ⟨Z, u, x, _⟩ := PreGaloisCategory.monoInducesIsoOnDirectSummand i
      have : Nat.card (F.obj Z) < Nat.card (F.obj Z) := sorry
    . simp at h
      obtain ⟨y, _⟩ := h
      admit

def evaluation (A X : C) (a : F.obj A) (f : A ⟶ X) : F.obj X := F.map f a

/- The evaluation map is injective for connected objects. -/
lemma evaluationInjectiveOfConnected (A X : C) [ConnectedObject A] (a : F.obj A) :
    Function.Injective (evaluation A X a) := by
  intro f g (h : F.map f a = F.map g a)
  let E := equalizer f g
  have : IsIso (equalizer.ι f g) := by
    apply ConnectedObject.noTrivialComponent E (equalizer.ι f g)
    intro hEinitial
    have hFEinitial : IsInitial (F.obj E) := preservesInitialObject E hEinitial
    have h2 : F.obj E ≃ { x : F.obj A // F.map f x = F.map g x } := by
      apply Iso.toEquiv
      trans
      exact PreservesEqualizer.iso F f g
      exact Types.equalizerIso (F.map f) (F.map g)
    have h3 : F.obj E ≃ PEmpty := (IsInitial.uniqueUpToIso hFEinitial (Types.isInitialPunit)).toEquiv
    apply not_nonempty_pempty
    apply (Equiv.nonempty_congr h3).mp
    apply (Equiv.nonempty_congr h2).mpr
    use a
  exact eq_of_epi_equalizer

def ConnectedObjects := { A : C | ConnectedObject A }

def I := (A : @ConnectedObjects C _) × F.obj (A : C)

def r : Setoid (@I C _ F) where
  r := by
    intro ⟨A, a⟩ ⟨B, b⟩
    exact ∃ f : (A : C) ⟶ B, IsIso f ∧ F.map f a = b
  iseqv := {
      refl := by
        intro ⟨A, a⟩
        use (𝟙 (A : C))
        constructor
        exact IsIso.id (A : C)
        simp only [FunctorToTypes.map_id_apply]
      symm := by
        intro ⟨A, a⟩ ⟨B, b⟩ ⟨f, ⟨_, hf⟩⟩
        use inv f
        constructor
        exact IsIso.inv_isIso
        rw [←hf]
        show (F.map f ≫ F.map (inv f) ) a = a
        rw [Functor.map_hom_inv]
        simp only [types_id_apply]
      trans := by
        intro ⟨A, a⟩ ⟨B, b⟩ ⟨C, c⟩ ⟨f, ⟨fiso, hf⟩⟩ ⟨g, ⟨giso, hg⟩⟩
        use f ≫ g
        constructor
        exact IsIso.comp_isIso
        simp only [FunctorToTypes.map_comp_apply, hf, hg]
    }

def J := Quotient (r F)

instance partOrder : PartialOrder (J F) where
  le x y := by
    exact ∃ (p q : I F) (f : (p.1 : C) ⟶ q.1), Quotient.mk (r F) p = x ∧ Quotient.mk (r F) q = y ∧ F.map f p.2 = q.2
  le_refl x := by
    refine Quotient.inductionOn x (fun x' ↦ ?_)
    obtain ⟨A, a⟩ := x'
    use ⟨A, a⟩
    use ⟨A, a⟩
    use 𝟙 (A : C)
    simp only [FunctorToTypes.map_id_apply, and_self]
  le_trans x y z := by
    refine Quotient.inductionOn x (fun x' ↦ ?_)
    refine Quotient.inductionOn y (fun y' ↦ ?_)
    refine Quotient.inductionOn z (fun z' ↦ ?_)
    intro ⟨⟨A, a⟩, ⟨B, b⟩, f, hf1, hf2, hf3⟩
    intro ⟨⟨B', b'⟩, ⟨C, c⟩, g, hg1, hg2, hg3⟩
    have ⟨u, _, hu⟩ : (r F).r ⟨B, b⟩ ⟨B', b'⟩ := Quotient.exact (Eq.trans hf2 hg1.symm)
    use ⟨A, a⟩
    use ⟨C, c⟩
    use f ≫ u ≫ g
    simp [hf1, hg2]
    rw [hf3, hu, hg3]
  le_antisymm x y := by
    refine Quotient.inductionOn x (fun x' ↦ ?_)
    refine Quotient.inductionOn y (fun y' ↦ ?_)
    intro ⟨⟨A, a⟩, ⟨B, b⟩, f, hf1, hf2, hf3⟩
    intro ⟨⟨B', b'⟩, ⟨A', a'⟩, g, hg1, hg2, hg3⟩
    have ⟨u, _, hu⟩ : (r F).r ⟨B, b⟩ ⟨B', b'⟩ := Quotient.exact (Eq.trans hf2 hg1.symm)
    have ⟨v, _, hv⟩ : (r F).r ⟨A', a'⟩ ⟨A, a⟩ := Quotient.exact (Eq.trans hg2 hf1.symm)
    let i : (A : C) ⟶ A := (f ≫ u) ≫ (g ≫ v)
    let j : (B' : C) ⟶ B' := (g ≫ v) ≫ (f ≫ u)
    have h1 : F.map i a = F.map (𝟙 (A : C)) a := by
      simp only [FunctorToTypes.map_comp_apply, FunctorToTypes.map_id_apply]
      rw [hf3, hu, hg3, hv]
    have h2 : F.map j b' = F.map (𝟙 (B' : C)) b' := by
      simp only [FunctorToTypes.map_comp_apply, FunctorToTypes.map_id_apply]
      rw [hg3, hv, hf3, hu]
    have : ConnectedObject (A : C) := A.prop
    have : ConnectedObject (B' : C) := B'.prop
    have : i = 𝟙 (A : C) := evaluationInjectiveOfConnected F inst A A a h1
    have : j = 𝟙 (B' : C) := evaluationInjectiveOfConnected F inst B' B' b' h2
    have : IsIso (f ≫ u) := by use g ≫ v
    rw [←hf1, ←hg1]
    apply Quotient.sound
    use f ≫ u
    constructor
    assumption
    simp only [FunctorToTypes.map_comp_apply]
    rw [hf3, hu]

--example : IsDirected (J F) (fun a b ↦ (partOrder F inst).le a b) where
--  directed x y := by
--    refine Quotient.inductionOn x (fun x' ↦ ?_)
--    refine Quotient.inductionOn y (fun y' ↦ ?_)

instance preOrder : Preorder (J F) := @PartialOrder.toPreorder (J F) (partOrder F inst)

instance : SmallCategory (J F) := @Preorder.smallCategory (J F) (preOrder F inst)

def diagram : (J F) ⥤ Type w := sorry

end Def

section FundamentalGroup

variable {C : Type u} [Category.{v, u} C] (F : C ⥤ Type u) [GaloisCategory C F] 

instance (X : C) : Fintype (F.obj X) := GaloisCategory.imageFinite X

def fundamentalGroup (F : C ⥤ Type u) : Type (max u u) := Aut F

-- inherit group instance from automorphism group
instance : Group (fundamentalGroup F) := by
  show Group (Aut F)
  exact inferInstance

-- the fundamental group is a profinite group
instance : TopologicalSpace (fundamentalGroup F) := sorry
instance : TopologicalGroup (fundamentalGroup F) := sorry
instance : CompactSpace (fundamentalGroup F) := sorry
instance : TotallyDisconnectedSpace (fundamentalGroup F) := sorry
instance : T2Space (fundamentalGroup F) := sorry

abbrev πTypes := Action (FintypeCat.{u}) (MonCat.of (fundamentalGroup F))

def fibreFunctor : C ⥤ πTypes F where
  obj X := {
    V := FintypeCat.of (F.obj X)
    ρ := MonCat.ofHom {
      toFun := fun (g : fundamentalGroup F) ↦ g.hom.app X
      map_one' := rfl
      map_mul' := by aesop
    }
  }
  map f := {
    hom := F.map f
    comm := by
      intro g
      exact symm <| g.hom.naturality f
  }

example : fibreFunctor F ⋙ forget (πTypes F) = F := rfl

theorem fundamental : IsEquivalence (fibreFunctor F) := sorry

end FundamentalGroup

end Galois2

end SGA
