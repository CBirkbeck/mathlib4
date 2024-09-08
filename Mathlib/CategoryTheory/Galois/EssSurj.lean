/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Galois.Full
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Category.FinTopCat
import Mathlib.RepresentationTheory.Action.Continuous

/-!

# Essential surjectivity of fiber functors

Let `F : C ⥤ FintypeCat` be a fiber functor of a Galois category `C` and denote by
`H` the induced functor `C ⥤ Action FintypeCat (Aut F)`.

In this file we show that the essential image of `H` are the finite `Aut F`-sets where
the `Aut F` action is continuous.

## Main results

- `exists_lift_of_quotient_openSubgroup`: If `U` is an open subgroup of `Aut F`, then
  there exists an object `X` such that `F.obj X` is isomorphic to `Aut F ⧸ U` as
  `Aut F`-sets.
- `exists_lift_of_continuous`: If `X` is a finite, discrete `Aut F`-set, then
  there exists an object `A` such that `F.obj A` is isomorphic to `X` as
  `Aut F`-sets.

## Strategy

We first show that every finite, discrete `Aut F`-set `Y` has a decomposition into connected
components and each connected component is of the form `Aut F ⧸ U` for an open subgroup `U`.
Since `H` preserves finite coproducts, it hence suffices to treat the case `Y = Aut F ⧸ U`.
For the case `Y = Aut F ⧸ U` we closely follow the second part of Stacks Project Tag 0BN4.

-/

universe u v

namespace CategoryTheory

open Functor

class Functor.PreservesForget₂ {V W : Type*}
    [Category V] [ConcreteCategory V] [Category W] [ConcreteCategory W]
    (F : V ⥤ W) (D : Type*) [Category D] [ConcreteCategory D]
    [HasForget₂ V D] [HasForget₂ W D] : Prop where
  comp_forget₂ : F ⋙ forget₂ W D = forget₂ V D := by aesop_cat

def Functor.mapContAction {V W : Type (u + 1)} [LargeCategory V]
    [ConcreteCategory V] [LargeCategory W] [ConcreteCategory W]
    [HasForget₂ V TopCat] [HasForget₂ W TopCat] (F : Functor V W)
    [F.PreservesForget₂ TopCat]
    (G : MonCat) [TopologicalSpace G] :
    ContAction V G ⥤ ContAction W G :=
  FullSubcategory.lift _ (fullSubcategoryInclusion _ ⋙ F.mapAction G) <| fun X ↦ by
  simp only [comp_obj, fullSubcategoryInclusion.obj]
  constructor
  let q : G × (F ⋙ forget₂ _ TopCat).obj X.obj.V →
      (F ⋙ forget₂ _ TopCat).obj X.obj.V := fun ⟨g, x⟩ ↦
    (F ⋙ forget₂ _ TopCat).map (X.obj.ρ g) x
  show Continuous q
  simp only [q]
  rw [PreservesForget₂.comp_forget₂]
  exact X.property.1

namespace PreGaloisCategory

variable {C : Type u} [Category.{v} C] {F : C ⥤ FintypeCat.{u}}

open Limits Functor

/-- Given an object of `FintypeCat`, we make an object of `FinTopCat` by equipping
it with the discrete topology. -/
private def mkDiscrete (X : FintypeCat) : TopCat :=
  ⟨X, ⊥⟩

/-- We may consider a finite type as a topological space by endowing it with the discrete
topology. -/
instance : HasForget₂ FintypeCat TopCat where
  forget₂ := {
    obj := fun X ↦ mkDiscrete X
    map := fun {X Y} f ↦ ⟨f, ⟨fun _ ↦ id⟩⟩
  }

instance : TopologicalSpace (MonCat.of (Aut F)) :=
  inferInstanceAs <| TopologicalSpace (Aut F)

---

/-- An object of `FinTopCat` is discrete if its topology is discrete. -/
abbrev FinTopCat.IsDiscrete (X : FinTopCat) : Prop :=
  DiscreteTopology X

/-- The category of discrete finite topological spaces. -/
abbrev DiscreteFinTopCat := FullSubcategory FinTopCat.IsDiscrete

instance : HasForget₂ DiscreteFinTopCat TopCat where
  forget₂ := fullSubcategoryInclusion _ ⋙ forget₂ FinTopCat TopCat

def fintypeToDiscreteFinTopCat : FintypeCat ⥤ DiscreteFinTopCat where
  obj X := ⟨⟨X, ⊥⟩, ⟨rfl⟩⟩
  map f := ⟨f, ⟨fun _ ↦ id⟩⟩

instance : (fullSubcategoryInclusion FinTopCat.IsDiscrete).PreservesForget₂ TopCat where

instance (G : MonCat) [TopologicalSpace G] :
    HasForget₂ (ContAction DiscreteFinTopCat G) (Action FintypeCat G) where
  forget₂ := (fullSubcategoryInclusion FinTopCat.IsDiscrete).mapContAction _ ⋙
      fullSubcategoryInclusion _ ⋙ (forget₂ FinTopCat FintypeCat).mapAction _

variable (F)

/-- The action of `Aut F` on `F.obj X` is continuous for every `X : C`, hence
`functorToAction F` factors via the inclusion of the full subcategory of finite,
discrete `Aut F`-sets. -/
def functorToContAction : C ⥤ ContAction FintypeCat (MonCat.of (Aut F)) :=
  FullSubcategory.lift _ (functorToAction F) <| fun X ↦ continuousSMul_aut_fiber F X

lemma functorToContAction_comp_inclusion_eq :
    functorToContAction F ⋙ fullSubcategoryInclusion _ = functorToAction F :=
  rfl

def functorToContAction' : C ⥤ ContAction DiscreteFinTopCat (MonCat.of (Aut F)) :=
  let G : C ⥤ Action DiscreteFinTopCat (MonCat.of (Aut F)) :=
    functorToAction F ⋙ fintypeToDiscreteFinTopCat.mapAction _
  FullSubcategory.lift _ G <| fun X ↦ continuousSMul_aut_fiber F X

lemma functorToContAction'_comp_inclusion_eq :
    functorToContAction' F ⋙ forget₂ _ _  = functorToAction F :=
  rfl

instance {V W : Type (u + 1)} [LargeCategory V] [ConcreteCategory V] [LargeCategory W]
    [ConcreteCategory W] [HasForget₂ V W]
    (G : MonCat.{u}) :
    HasForget₂ (Action V G) (Action W G) where
  forget₂ := (forget₂ V W).mapAction G
  forget_comp := by
    show forget₂ (Action V G) V ⋙ forget₂ V W ⋙ forget W = _
    rw [HasForget₂.forget_comp]
    rfl

instance (G : MonCat.{u}) [TopologicalSpace G] :
    HasForget₂ (DiscreteContAction FinTopCat G) (Action FintypeCat G) :=
  letI := HasForget₂.trans (ContAction FinTopCat G)
    (Action FinTopCat G)
    (Action FintypeCat G)
  HasForget₂.trans _ (ContAction FinTopCat G) _

def functorToContAction'' : C ⥤ DiscreteContAction FinTopCat (MonCat.of (Aut F)) :=
  let G : FintypeCat.{u} ⥤ FinTopCat :=
    { obj := fun X ↦ ⟨X, ⊥⟩, map := fun f ↦ ⟨f, ⟨fun _ ↦ id⟩⟩ }
  FullSubcategory.lift _
    (FullSubcategory.lift _ (functorToAction F ⋙ G.mapAction _) <| fun X ↦
      continuousSMul_aut_fiber F X)
    (fun X ↦ ⟨rfl⟩)

lemma functorToContAction''_comp_inclusion_eq :
    functorToContAction'' F ⋙ forget₂ _ _ = functorToAction F :=
  rfl

variable [GaloisCategory C] [FiberFunctor F]

instance : (functorToContAction F).Faithful :=
  Functor.Faithful.of_comp_eq (functorToContAction_comp_inclusion_eq F)

instance : (functorToContAction F).Full :=
  haveI : (functorToContAction F ⋙ fullSubcategoryInclusion _).Full :=
    inferInstanceAs <| (functorToAction F).Full
  haveI := CategoryTheory.FullSubcategory.faithful
    (Action.IsContinuous (V := FintypeCat) (G := MonCat.of (Aut F)))
  Functor.Full.of_comp_faithful (functorToContAction F)
    (fullSubcategoryInclusion _)

variable {F} {G : Type*} [Group G] [TopologicalSpace G] [TopologicalGroup G] [CompactSpace G]

private noncomputable local instance fintypeQuotient (H : OpenSubgroup (G)) :
    Fintype (G ⧸ (H : Subgroup (G))) :=
  have : Finite (G ⧸ H.toSubgroup) := H.toSubgroup.quotient_finite_of_isOpen H.isOpen'
  Fintype.ofFinite _

private noncomputable local instance fintypeQuotientStabilizer {X : Type*} [MulAction G X]
    [TopologicalSpace X] [ContinuousSMul G X] [DiscreteTopology X] (x : X) :
    Fintype (G ⧸ (MulAction.stabilizer (G) x)) :=
  fintypeQuotient ⟨MulAction.stabilizer (G) x, stabilizer_isOpen (G) x⟩

/-- If `X` is a finite discrete `G`-set, it can be written as the finite disjoint union
of quotients of the form `G ⧸ Uᵢ` for open subgroups `(Uᵢ)`. Note that this
is simply the decomposition into orbits. -/
lemma has_decomp_quotients (X : Action FintypeCat (MonCat.of G))
    [TopologicalSpace X.V] [DiscreteTopology X.V] [ContinuousSMul G X.V] :
    ∃ (ι : Type) (_ : Finite ι) (f : ι → OpenSubgroup (G)),
      Nonempty ((∐ fun i ↦ G ⧸ₐ (f i).toSubgroup) ≅ X) := by
  obtain ⟨ι, hf, f, u, hc⟩ := has_decomp_connected_components' X
  letI (i : ι) : TopologicalSpace (f i).V := ⊥
  haveI (i : ι) : DiscreteTopology (f i).V := ⟨rfl⟩
  have (i : ι) : ContinuousSMul G (f i).V := ContinuousSMul.mk <| by
    let r : f i ⟶ X := Sigma.ι f i ≫ u.hom
    let r'' (p : G × (f i).V) : G × X.V := (p.1, r.hom p.2)
    let q (p : G × X.V) : X.V := X.ρ p.1 p.2
    let q' (p : G × (f i).V) : (f i).V := (f i).ρ p.1 p.2
    have heq : q ∘ r'' = r.hom ∘ q' := by
      ext (p : G × (f i).V)
      exact (congr_fun (r.comm p.1) p.2).symm
    have hrinj : Function.Injective r.hom :=
      (ConcreteCategory.mono_iff_injective_of_preservesPullback r).mp <| mono_comp _ _
    let t₁ : TopologicalSpace (G × (f i).V) := inferInstance
    show @Continuous _ _ _ ⊥ q'
    have : TopologicalSpace.induced r.hom inferInstance = ⊥ := by
      rw [← le_bot_iff]
      exact fun s _ ↦ ⟨r.hom '' s, ⟨isOpen_discrete (r.hom '' s), Set.preimage_image_eq s hrinj⟩⟩
    rw [← this, continuous_induced_rng, ← heq]
    exact Continuous.comp continuous_smul (by fun_prop)
  have (i : ι) : ∃ (U : OpenSubgroup (G)), (Nonempty ((f i) ≅ G ⧸ₐ U.toSubgroup)) := by
    obtain ⟨(x : (f i).V)⟩ := nonempty_fiber_of_isConnected (forget₂ _ _) (f i)
    let U : OpenSubgroup (G) := ⟨MulAction.stabilizer (G) x, stabilizer_isOpen (G) x⟩
    letI : Fintype (G ⧸ MulAction.stabilizer (G) x) := fintypeQuotient U
    exact ⟨U, ⟨FintypeCat.isoQuotientStabilizerOfIsConnected (f i) x⟩⟩
  choose g ui using this
  exact ⟨ι, hf, g, ⟨(Sigma.mapIso (fun i ↦ (ui i).some)).symm ≪≫ u⟩⟩

/-- If `X` is connected and `x` is in the fiber of `X`, `F.obj X` is isomorphic
to the quotient of `Aut F` by the stabilizer of `x` as `Aut F`-sets. -/
noncomputable def fiberIsoQuotientStabilizer (X : C) [IsConnected X] (x : F.obj X) :
    (functorToAction F).obj X ≅ Aut F ⧸ₐ MulAction.stabilizer (Aut F) x :=
  haveI : IsConnected ((functorToAction F).obj X) := PreservesIsConnected.preserves
  letI : Fintype (Aut F ⧸ MulAction.stabilizer (Aut F) x) := fintypeQuotientStabilizer x
  FintypeCat.isoQuotientStabilizerOfIsConnected ((functorToAction F).obj X) x

section

open Action.FintypeCat

variable (V : OpenSubgroup (Aut F)) {U : OpenSubgroup (Aut F)}
  (h : Subgroup.Normal U.toSubgroup) {A : C} (u : (functorToAction F).obj A ≅ Aut F ⧸ₐ U.toSubgroup)

/-

### Strategy outline

Let `A` be object of `C` with fiber `Aut F`-isomorphic to `Aut F ⧸ U` for an open normal
subgroup `U`. Then for any open subgroup `V` of `Aut F`, `V ⧸ (U ⊓ V)` acts on `A`. This
induces the diagram `quotientDiag`. Now assume `U ≤ V`. Then we can also postcompose
the diagram `quotientDiag` with `F`. The goal of this section is to compute that the colimit
of this composed diagram is `Aut F ⧸ V`. Finally, we obtain `F.obj (A ⧸ V) ≅ Aut F ⧸ V` as
`Aut F`-sets.
-/

private noncomputable def quotientToEndObjectHom :
    V.toSubgroup ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup →* End A :=
  let ff : (functorToAction F).FullyFaithful := FullyFaithful.ofFullyFaithful (functorToAction F)
  let e : End A ≃* End (Aut F ⧸ₐ U.toSubgroup) := (ff.mulEquivEnd A).trans (Iso.conj u)
  e.symm.toMonoidHom.comp (quotientToEndHom V.toSubgroup U.toSubgroup)

private lemma functorToAction_map_quotientToEndObjectHom
    (m : SingleObj.star (V ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup) ⟶
      SingleObj.star (V ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup)) :
    (functorToAction F).map (quotientToEndObjectHom V h u m) =
      u.hom ≫ quotientToEndHom V.toSubgroup U.toSubgroup m ≫ u.inv := by
  simp [← cancel_epi u.inv, ← cancel_mono u.hom, ← Iso.conj_apply, quotientToEndObjectHom]

@[simps!]
private noncomputable def quotientDiag : SingleObj (V.toSubgroup ⧸ Subgroup.subgroupOf U V) ⥤ C :=
  SingleObj.functor (quotientToEndObjectHom V h u)

variable {V} (hUinV : U ≤ V)

@[simps]
private noncomputable def coconeQuotientDiag :
    Cocone (quotientDiag V h u ⋙ functorToAction F) where
  pt := Aut F ⧸ₐ V.toSubgroup
  ι := SingleObj.natTrans (u.hom ≫ quotientToQuotientOfLE V.toSubgroup U.toSubgroup hUinV) <| by
    intro (m : V ⧸ Subgroup.subgroupOf U V)
    simp only [const_obj_obj, Functor.comp_map, const_obj_map, Category.comp_id]
    rw [← cancel_epi (u.inv), Iso.inv_hom_id_assoc]
    apply Action.hom_ext
    ext (x : Aut F ⧸ U.toSubgroup)
    induction' m, x using Quotient.inductionOn₂ with σ μ
    suffices h : ⟦μ * σ⁻¹⟧ = ⟦μ⟧ by
      simp only [quotientToQuotientOfLE_hom_mk, quotientDiag_map,
        functorToAction_map_quotientToEndObjectHom V _ u]
      simpa
    apply Quotient.sound
    apply (QuotientGroup.leftRel_apply).mpr
    simp

@[simps]
private noncomputable def coconeQuotientDiagDesc
    (s : Cocone (quotientDiag V h u ⋙ functorToAction F)) :
      (coconeQuotientDiag h u hUinV).pt ⟶ s.pt where
  hom := Quotient.lift (fun σ ↦ (u.inv ≫ s.ι.app (SingleObj.star _)).hom ⟦σ⟧) <| fun σ τ hst ↦ by
    let J' := quotientDiag V h u ⋙ functorToAction F
    let m : End (SingleObj.star (V.toSubgroup ⧸ Subgroup.subgroupOf U V)) :=
      ⟦⟨σ⁻¹ * τ, (QuotientGroup.leftRel_apply).mp hst⟩⟧
    have h1 : J'.map m ≫ s.ι.app (SingleObj.star _) = s.ι.app (SingleObj.star _) := s.ι.naturality m
    conv_rhs => rw [← h1]
    have h2 : (J'.map m).hom (u.inv.hom ⟦τ⟧) = u.inv.hom ⟦σ⟧ := by
      simp only [comp_obj, quotientDiag_obj, Functor.comp_map, quotientDiag_map, J',
        functorToAction_map_quotientToEndObjectHom V h u m]
      show (u.inv ≫ u.hom ≫ _ ≫ u.inv).hom ⟦τ⟧ = u.inv.hom ⟦σ⟧
      simp [m]
    simp only [← h2, const_obj_obj, Action.comp_hom, FintypeCat.comp_apply]
  comm g := by
    ext (x : Aut F ⧸ V.toSubgroup)
    induction' x using Quotient.inductionOn with σ
    simp only [const_obj_obj]
    show (((Aut F ⧸ₐ U.toSubgroup).ρ g ≫ u.inv.hom) ≫ (s.ι.app (SingleObj.star _)).hom) ⟦σ⟧ =
      ((s.ι.app (SingleObj.star _)).hom ≫ s.pt.ρ g) (u.inv.hom ⟦σ⟧)
    have : ((functorToAction F).obj A).ρ g ≫ (s.ι.app (SingleObj.star _)).hom =
        (s.ι.app (SingleObj.star _)).hom ≫ s.pt.ρ g :=
      (s.ι.app (SingleObj.star _)).comm g
    rw [← this, u.inv.comm g]
    rfl

/-- The constructed cocone `coconeQuotientDiag` on the diagram `quotientDiag` is colimiting. -/
private noncomputable def coconeQuotientDiagIsColimit :
    IsColimit (coconeQuotientDiag h u hUinV) where
  desc := coconeQuotientDiagDesc h u hUinV
  fac s j := by
    apply (cancel_epi u.inv).mp
    apply Action.hom_ext
    ext (x : Aut F ⧸ U.toSubgroup)
    induction' x using Quotient.inductionOn with σ
    simp
    rfl
  uniq s f hf := by
    apply Action.hom_ext
    ext (x : Aut F ⧸ V.toSubgroup)
    induction' x using Quotient.inductionOn with σ
    simp [← hf (SingleObj.star _)]

end

/-- For every open subgroup `V` of `Aut F`, there exists an `X : C` such that
`F.obj X ≅ Aut F ⧸ V` as `Aut F`-sets. -/
lemma exists_lift_of_quotient_openSubgroup (V : OpenSubgroup (Aut F)) :
    ∃ (X : C), Nonempty ((functorToAction F).obj X ≅ Aut F ⧸ₐ V.toSubgroup) := by
  obtain ⟨I, hf, hc, hi⟩ := exists_set_ker_evaluation_subset_of_isOpen F (one_mem V) V.isOpen'
  haveI (X : I) : IsConnected X.val := hc X X.property
  haveI (X : I) : Nonempty (F.obj X.val) := nonempty_fiber_of_isConnected F X
  have hn : Nonempty (F.obj <| (∏ᶜ fun X : I => X)) := nonempty_fiber_pi_of_nonempty_of_finite F _
  obtain ⟨A, f, hgal⟩ := exists_hom_from_galois_of_fiber_nonempty F (∏ᶜ fun X : I => X) hn
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  let U : OpenSubgroup (Aut F) := ⟨MulAction.stabilizer (Aut F) a, stabilizer_isOpen (Aut F) a⟩
  let u := fiberIsoQuotientStabilizer A a
  have hUnormal : U.toSubgroup.Normal := stabilizer_normal_of_isGalois F A a
  have h1 (σ : Aut F) (σinU : σ ∈ U) : σ.hom.app A = 𝟙 (F.obj A) := by
    have hi : (Aut F ⧸ₐ MulAction.stabilizer (Aut F) a).ρ σ = 𝟙 _ := by
      refine FintypeCat.hom_ext _ _ (fun x ↦ ?_)
      induction' x using Quotient.inductionOn with τ
      show ⟦σ * τ⟧ = ⟦τ⟧
      apply Quotient.sound
      apply (QuotientGroup.leftRel_apply).mpr
      simp only [mul_inv_rev]
      exact Subgroup.Normal.conj_mem hUnormal _ (Subgroup.inv_mem U.toSubgroup σinU) _
    simp [← cancel_mono u.hom.hom, show σ.hom.app A ≫ u.hom.hom = _ from u.hom.comm σ, hi]
  have h2 (σ : Aut F) (σinU : σ ∈ U) : ∀ X : I, σ.hom.app X = 𝟙 (F.obj X) := by
    intro ⟨X, hX⟩
    ext (x : F.obj X)
    let p : A ⟶ X := f ≫ Pi.π (fun Z : I => (Z : C)) ⟨X, hX⟩
    have : IsConnected X := hc X hX
    obtain ⟨a, rfl⟩ := surjective_of_nonempty_fiber_of_isConnected F p x
    simp only [FintypeCat.id_apply, FunctorToFintypeCat.naturality, h1 σ σinU]
  have hUinV : (U : Set (Aut F)) ≤ V := fun u uinU ↦ hi u (h2 u uinU)
  have := V.quotient_finite_of_isOpen' U V.isOpen' U.isOpen'
  exact ⟨colimit (quotientDiag V hUnormal u),
    ⟨preservesColimitIso (functorToAction F) (quotientDiag V hUnormal u) ≪≫
    colimit.isoColimitCocone ⟨coconeQuotientDiag hUnormal u hUinV,
    coconeQuotientDiagIsColimit hUnormal u hUinV⟩⟩⟩

/--
If `X` is a finite, discrete `Aut F`-set with continuous `Aut F`-action, then
there exists `A : C` such that `F.obj A ≅ X` as `Aut F`-sets.
-/
theorem exists_lift_of_continuous (X : Action FintypeCat (MonCat.of (Aut F)))
    [TopologicalSpace X.V] [DiscreteTopology X.V] [ContinuousSMul (Aut F) X.V] :
    ∃ A, Nonempty ((functorToAction F).obj A ≅ X) := by
  obtain ⟨ι, hfin, f, ⟨u⟩⟩ := has_decomp_quotients X
  choose g gu using (fun i ↦ exists_lift_of_quotient_openSubgroup (f i))
  exact ⟨∐ g, ⟨PreservesCoproduct.iso (functorToAction F) g ≪≫
    Sigma.mapIso (fun i ↦ (gu i).some) ≪≫ u⟩⟩

/-- The by `F` induced functor `C ⥤ ContAction FintypeCat (MonCat.of (Aut F))`
is essentially surjective. -/
instance : (functorToContAction F).EssSurj where
  mem_essImage Y := by
    let Y' : Action FintypeCat (MonCat.of (Aut F)) :=
      (fullSubcategoryInclusion _).obj Y
    letI : TopologicalSpace Y'.V := ⊥
    haveI : DiscreteTopology Y'.V := ⟨rfl⟩
    haveI : ContinuousSMul (Aut F) Y'.V := Y.property
    obtain ⟨A, ⟨u⟩⟩ := exists_lift_of_continuous Y'
    exact ⟨A, ⟨(fullSubcategoryInclusion _).preimageIso u⟩⟩

/-- The by `F` induced functor `C ⥤ ContAction FintypeCat (MonCat.of (Aut F))`
is an equivalence. -/
instance isequiv : (functorToContAction F).IsEquivalence where

end PreGaloisCategory

end CategoryTheory
