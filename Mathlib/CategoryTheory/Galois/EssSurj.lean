/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Galois.Full
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.CategoryTheory.Endomorphism

/-!

# Essential surjectivity of fiber functors

-/

universe u₁ u₂ w u v₁

section Profinite

--open TopologicalSpace

variable {G : Type*} [Group G]

open Function Set

lemma QuotientGroup.preimage_mk_singleton_mk (H : Subgroup G) (g : G) :
    mk (s := H) ⁻¹' {mk g} = (g * ·) '' H := by
  ext g'
  simp only [mem_preimage, mem_singleton_iff, QuotientGroup.eq, image_mul_left, SetLike.mem_coe]
  rw [← H.inv_mem_iff]
  simp

variable [TopologicalSpace G] [TopologicalGroup G]

instance (X : Type*) [MulAction G X] [Fintype X] : MulAction G (FintypeCat.of X) :=
  inferInstanceAs <| MulAction G X

lemma closed_of_open (U : Subgroup G) (h : IsOpen (U : Set G)) : IsClosed (U : Set G) :=
  OpenSubgroup.isClosed ⟨U, h⟩

lemma Subgroup.discreteTopology (U : Subgroup G) (U_open : IsOpen (U : Set G)) :
    DiscreteTopology (G ⧸ U) := by
  apply singletons_open_iff_discrete.mp
  rintro ⟨g⟩
  erw [isOpen_mk, QuotientGroup.preimage_mk_singleton_mk]
  exact Homeomorph.mulLeft g |>.isOpen_image|>.mpr U_open

def finiteQuotientOfOpen [CompactSpace G] (U : Subgroup G) (h : IsOpen (U : Set G)) :
    Finite (G ⧸ U) :=
  have : CompactSpace (G ⧸ U) := Quotient.compactSpace
  have : DiscreteTopology (G ⧸ U) := U.discreteTopology h
  finite_of_compact_of_discrete

def finiteQuotientSubgroups [CompactSpace G] (U K : Subgroup G) (hUopen : IsOpen (U : Set G))
    (hKpoen : IsOpen (K : Set G)) : Finite (U ⧸ Subgroup.subgroupOf K U) := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp <| IsClosed.isCompact
    <| closed_of_open U hUopen
  apply finiteQuotientOfOpen (Subgroup.subgroupOf K U)
  show IsOpen (((Subgroup.subtype U) ⁻¹' K) : Set U)
  apply Continuous.isOpen_preimage
  continuity
  assumption

end Profinite

namespace CategoryTheory

namespace PreGaloisCategory

variable {C : Type u} [Category.{u} C] (F : C ⥤ FintypeCat.{u})

open Limits Functor

lemma stabilizer_open (X : C) (x : ((functorToAction F).obj X).V) :
    IsOpen (MulAction.stabilizer (Aut F) x : Set (Aut F)) := by
  let q (g : Aut F) : Aut F × F.obj X := (g, x)
  have : Continuous q := by
    continuity
  let h (p : Aut F × F.obj X) : F.obj X := p.1.hom.app X p.2
  have : Continuous h := continuous_smul
  let p (g : Aut F) : F.obj X := g.hom.app X x
  have : p ⁻¹' {x} = MulAction.stabilizer (Aut F) x := rfl
  rw [←this]
  apply IsOpen.preimage
  show Continuous (h ∘ q)
  apply Continuous.comp
  assumption
  assumption
  trivial

variable [GaloisCategory C] [FiberFunctor F]

noncomputable instance (G : Type u) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) (functorToAction F) := by
  apply Action.preservesColimitsOfShapeOfPreserves
  show PreservesColimitsOfShape (SingleObj G) F
  infer_instance

section

noncomputable instance fintypeQuotient (H : OpenSubgroup (Aut F)) :
    Fintype (Aut F ⧸ (H : Subgroup (Aut F))) := by
  have : Finite (Aut F ⧸ H.toSubgroup) := finiteQuotientOfOpen H.toSubgroup H.isOpen'
  apply Fintype.ofFinite

instance (H : Subgroup (Aut F)) : MulAction (Aut F) (Aut F ⧸ H) := inferInstance

end

private lemma help0 (X : C) [IsGalois X] :
    ∃ (U : OpenSubgroup (Aut F))
      (_ : (functorToAction F).obj X ≅ Action.FintypeCat.ofMulAction (Aut F)
        (FintypeCat.of <| Aut F ⧸ U.toSubgroup)),
    Subgroup.Normal U.toSubgroup := by
  have hc : IsConnected ((functorToAction F).obj X) := PreservesIsConnected.preserves
  have : Nonempty (F.obj X) := nonempty_fiber_of_isConnected F X
  obtain ⟨x : ((functorToAction F).obj X).V⟩ := this
  have : MulAction (Aut F) (F.obj X) := by
    show MulAction (Aut F) ((functorToAction F).obj X).V
    infer_instance
  have : MulAction.IsPretransitive (Aut F) ((functorToAction F).obj X).V :=
    FintypeCat.Action.pretransitive_of_isConnected (Aut F) ((functorToAction F).obj X)
  have : MulAction.orbit (Aut F) x ≃ Aut F ⧸ MulAction.stabilizer (Aut F) x :=
    MulAction.orbitEquivQuotientStabilizer (Aut F) x
  have : MulAction.orbit (Aut F) x = Set.univ := MulAction.orbit_eq_univ (Aut F) x
  have : MulAction.orbit (Aut F) x ≃ Set.univ := Equiv.setCongr this
  let e : ((functorToAction F).obj X).V ≃ Aut F ⧸ MulAction.stabilizer (Aut F) x := by
    trans
    exact (Equiv.Set.univ ↑(F.obj X)).symm
    trans
    apply Equiv.setCongr
    exact (MulAction.orbit_eq_univ (Aut F) x).symm
    exact MulAction.orbitEquivQuotientStabilizer (Aut F) x
  let U : OpenSubgroup (Aut F) := ⟨MulAction.stabilizer (Aut F) x, stabilizer_open F X x⟩
  use U
  let inst : Fintype (Aut F ⧸ U.toSubgroup) := fintypeQuotient F U
  let u : Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ U.toSubgroup) ≅
      (functorToAction F).obj X := by
    apply Action.mkIso
    swap
    exact (FintypeCat.equivEquivIso e.symm)
    intro (σ : Aut F)
    ext (a : Aut F ⧸ MulAction.stabilizer (Aut F) x)
    obtain ⟨τ, hτ⟩ := Quotient.exists_rep a
    rw [←hτ]
    rfl
  use u.symm
  constructor
  intro n ninstab g
  simp
  show g • n • (g⁻¹ • x) = x
  have : MulAction.IsPretransitive (Aut X) (F.obj X) := inferInstance
  let inst : SMul (Aut X) ((functorToAction F).obj X).V :=
    inferInstanceAs <| SMul (Aut X) (F.obj X)
  have : MulAction.IsPretransitive (Aut X) ((functorToAction F).obj X).V :=
    isPretransitive_of_isGalois F X
  have : ∃ (φ : Aut X), F.map φ.hom x = g⁻¹ • x :=
    MulAction.IsPretransitive.exists_smul_eq x (g⁻¹ • x)
  obtain ⟨φ, h⟩ := this
  rw [← h]
  show g • n • _ = x
  --show g • n • (F.map φ.hom x) = x
  show g • (((functorToAction F).map φ.hom).hom ≫ ((functorToAction F).obj X).ρ n) x = x
  rw [← ((functorToAction F).map φ.hom).comm]
  simp only [FintypeCat.comp_apply]
  show g • ((functorToAction F).map φ.hom).hom (n • x) = x
  have : ((functorToAction F).map φ.hom).hom = F.map φ.hom := rfl
  rw [this]
  --show g • F.map φ.hom (n • x) = x
  rw [ninstab, h]
  show (g * g⁻¹) • x = x
  simp

lemma FintypeCat.jointly_surjective {J : Type} [SmallCategory J] [FinCategory J]
    (F : J ⥤ FintypeCat.{u}) (t : Cocone F) (h : IsColimit t) (x : t.pt) :
    ∃ j y, t.ι.app j y = x := by
  let s : Cocone (F ⋙ FintypeCat.incl) := FintypeCat.incl.mapCocone t
  let hs : IsColimit s := isColimitOfPreserves FintypeCat.incl.{u} h
  exact Types.jointly_surjective (F ⋙ FintypeCat.incl) hs x

private lemma help1 (H : Subgroup (Aut F)) (h : IsOpen (H : Set (Aut F))) : ∃ (I : Set C)
    (_ : Fintype I), (∀ X ∈ I, IsConnected X) ∧
    ((σ : Aut F) → (∀ X : I, σ.hom.app X = 𝟙 (F.obj X)) → σ ∈ H) := by
  obtain ⟨U, hUopen, hU⟩ := isOpen_induced_iff.mp h
  have h1inU : 1 ∈ U := by
    show 1 ∈ autEmbedding F ⁻¹' U
    rw [hU]
    exact Subgroup.one_mem H
  obtain ⟨I, u, ho, ha⟩ := isOpen_pi_iff.mp hUopen 1 h1inU
  choose fι ff fc h4 h5 h6 using (fun X : I => has_decomp_connected_components X.val)
  let J : Set C := ⋃ X, Set.range (ff X)
  use J
  use Fintype.ofFinite J
  constructor
  intro X ⟨A, ⟨Y, hY⟩, hA2⟩
  have : X ∈ Set.range (ff Y) := by simpa [hY]
  obtain ⟨i, hi⟩ := this
  rw [← hi]
  exact h5 Y i
  intro σ h
  have (X : I) : σ.hom.app X = 𝟙 (F.obj X) := by
    --have is : ∐ ff X ≅ X := h3 X
    let t : ColimitCocone (Discrete.functor (ff X)) := ⟨Cofan.mk X (fc X), h4 X⟩
    let s : Cocone (Discrete.functor (ff X) ⋙ F) := F.mapCocone t.cocone
    have : Fintype (fι X) := Fintype.ofFinite _
    let hs : IsColimit s := isColimitOfPreserves F t.isColimit
    --rw [h6]
    ext (x : F.obj t.cocone.pt)
    obtain ⟨⟨j⟩, a, ha : F.map (t.cocone.ι.app ⟨j⟩) a = x⟩ :=
      FintypeCat.jointly_surjective (Discrete.functor (ff X) ⋙ F) s hs x
    show σ.hom.app X x = x
    rw [← ha]
    show (F.map (t.cocone.ι.app ⟨j⟩) ≫ σ.hom.app X) a = F.map (t.cocone.ι.app ⟨j⟩) a
    erw [σ.hom.naturality]
    simp
    have : σ.hom.app ((ff X) j) = 𝟙 (F.obj ((ff X) j)) := by
      have : (ff X) j ∈ J := by aesop
      exact h ⟨(ff X) j, this⟩
    rw [this]
    rfl
  have (X : I) : autEmbedding F σ X = 1 := by
    apply Iso.ext
    exact this X
  have (X : I) : autEmbedding F σ X ∈ u X := by
    rw [this X]
    exact (ho X.val X.property).right
  have : autEmbedding F σ ∈ Set.pi I u := by
    intro X XinI
    exact this ⟨X, XinI⟩
  have : σ ∈ autEmbedding F ⁻¹' U := by
    apply ha
    exact this
  rw [hU] at this
  exact this

private lemma help2 (I : Set C) [Fintype I] (h : ∀ X ∈ I, IsConnected X) :
    Nonempty (F.obj (∏ᶜ fun X : I ↦ X)) := by
  let P : FintypeCat := ∏ᶜ fun X : I => F.obj X
  have i1 : F.obj (∏ᶜ fun X : I => X) ≅ P := PreservesProduct.iso F _
  let f (X : I) : Type u := F.obj X
  have i2 : FintypeCat.incl.obj P ≅ ∏ᶜ f := PreservesProduct.iso FintypeCat.incl _
  have (X : I) : Nonempty (F.obj X) := by
    have : IsConnected (X : C) := h X.val X.property
    exact nonempty_fiber_of_isConnected F (X : C)
  have : Nonempty (∀ X : I, F.obj X) := inferInstance
  obtain ⟨x⟩ := this
  have i3 : ∏ᶜ f ≅ Shrink.{u, u} (∀ X : I, f X) := Types.Small.productIso f
  let y : ∏ᶜ f := i3.inv ((equivShrink _) x)
  let y' : P := i2.inv y
  use i1.inv y'

variable (H N : OpenSubgroup (Aut F)) [Subgroup.Normal N.toSubgroup]

private noncomputable def help3 (H N : OpenSubgroup (Aut F)) (hn : Subgroup.Normal N.toSubgroup) :
    H.toSubgroup ⧸ Subgroup.subgroupOf N H →*
      End (Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ N.toSubgroup)) := by
  let φ' : H →* End (Action.FintypeCat.ofMulAction (Aut F)
      (FintypeCat.of <| Aut F ⧸ N.toSubgroup)) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    intro ⟨v, _⟩
    show Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ N.toSubgroup) ⟶
      Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ N.toSubgroup)
    let fh : (Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ N.toSubgroup)).V
        ⟶ (Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ N.toSubgroup)).V := by
      show Aut F ⧸ N.toSubgroup → Aut F ⧸ N.toSubgroup
      apply Quotient.lift
      swap
      intro σ
      exact ⟦σ * v⁻¹⟧
      intro σ τ hst
      apply Quotient.sound
      apply (QuotientGroup.leftRel_apply).mpr
      simp
      show v * (σ⁻¹ * τ) * v⁻¹ ∈ N
      apply Subgroup.Normal.conj_mem hn
      exact QuotientGroup.leftRel_apply.mp hst
    constructor
    swap
    exact fh
    intro (σ : Aut F)
    ext (x : Aut F ⧸ N.toSubgroup)
    obtain ⟨τ, hτ⟩ := Quotient.exists_rep x
    rw [←hτ]
    rfl
    apply Action.hom_ext
    ext (x : Aut F ⧸ N.toSubgroup)
    obtain ⟨τ, hτ⟩ := Quotient.exists_rep x
    rw [←hτ]
    rfl
    intro σ τ
    apply Action.hom_ext
    ext (x : Aut F ⧸ N.toSubgroup)
    obtain ⟨μ, hμ⟩ := Quotient.exists_rep x
    rw [←hμ]
    show ⟦μ * (σ * τ)⁻¹⟧ = ⟦μ * τ⁻¹ * σ⁻¹⟧
    group
    rfl
  apply QuotientGroup.lift (Subgroup.subgroupOf N.toSubgroup H.toSubgroup) φ'
  intro u uinU'
  show φ' u = 1
  apply Action.hom_ext
  ext (x : Aut F ⧸ N.toSubgroup)
  obtain ⟨μ, hμ⟩ := Quotient.exists_rep x
  rw [←hμ]
  show ⟦μ * u⁻¹⟧ = ⟦μ⟧
  apply Quotient.sound
  apply (QuotientGroup.leftRel_apply).mpr
  simpa

--private def help411 {G M : Type*} [Group G] [Group M]
--    (J : SingleObj M ⥤ Action FintypeCat (MonCat.of G)) :
--    Action FintypeCat (MonCat.of G) where
--  V := (J.obj (SingleObj.star M)).V ⧸ M

--private def help41 {G M : Type*} [Group G] [Group M]
--    (J : SingleObj M ⥤ Action FintypeCat (MonCat.of G)) :
--    Cocone J where
--  pt := J.obj (SingleObj.star M) ⧸ M
--  ι := {
--    app := fun _ => 𝟙 (J.obj _)
--    --naturality := 
--  }

--private def help42 {G M : Type*} [Group G] [Group M] (H N : Subgroup G) (h : Subgroup.Normal N)
--  (J : SingleObj M ⥤ Action FintypeCat (MonCat.of G))

--private lemma help4 {G M : Type*} [Group G] [Group M] [Finite M]
--    (J : SingleObj M ⥤ Action FintypeCat (MonCat.of G)) :
--  colimit J ≅ Action.ofMulAction' G (G ⧸ H) := sorry

def help43 {G : Type*} [Group G] (H N : Subgroup G) [Fintype (G ⧸ N)]
    [Fintype (G ⧸ H)] (h : N ≤ H) :
    Action.FintypeCat.ofMulAction G (FintypeCat.of <| G ⧸ N) ⟶
      Action.FintypeCat.ofMulAction G (FintypeCat.of <| G ⧸ H) := by
  constructor
  swap
  apply Quotient.lift
  intro a b hab
  apply Quotient.sound
  apply (QuotientGroup.leftRel_apply).mpr
  apply h
  exact (QuotientGroup.leftRel_apply).mp hab
  intro (g : G)
  ext (x : G ⧸ N)
  obtain ⟨μ, hμ⟩ := Quotient.exists_rep x
  rw [←hμ]
  rfl

noncomputable def help44 (V U : OpenSubgroup (Aut F)) (h : Subgroup.Normal U.toSubgroup) (A : C)
    (u : (functorToAction F).obj A ≅ Action.FintypeCat.ofMulAction
      (Aut F) (FintypeCat.of <| Aut F ⧸ U.toSubgroup)) :
    V.toSubgroup ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup →* End A := by
  let φ : V.toSubgroup ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup →*
      End (Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ U.toSubgroup)) :=
    help3 F V U h
  let ff : (functorToAction F).FullyFaithful := FullyFaithful.ofFullyFaithful (functorToAction F)
  let e1 : End A ≃* End ((functorToAction F).obj A) := ff.mulEquivEnd A
  let e2 : End ((functorToAction F).obj A) ≃*
      End (Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ U.toSubgroup)) :=
    Iso.conj u
  let e : End A ≃* End (Action.FintypeCat.ofMulAction (Aut F)
    (FintypeCat.of <| Aut F ⧸ U.toSubgroup)) := e1.trans e2
  exact MonoidHom.comp e.symm.toMonoidHom φ

lemma help441 (V U : OpenSubgroup (Aut F)) (h : Subgroup.Normal U.toSubgroup) (A : C)
    (u : (functorToAction F).obj A ≅
      Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ U.toSubgroup))
    (m : SingleObj.star (V ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup) ⟶
      SingleObj.star (V ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup)) :
    (functorToAction F).map (help44 F V U h A u m) = u.hom ≫ help3 F V U h m ≫ u.inv := by
  apply (cancel_epi (u.inv)).mp
  apply (cancel_mono (u.hom)).mp
  simp [←Iso.conj_apply, MulEquiv.apply_symm_apply, help44]

noncomputable def help45 (V U : OpenSubgroup (Aut F)) (h : Subgroup.Normal U.toSubgroup) (A : C)
    (u : (functorToAction F).obj A ≅
      Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ U.toSubgroup)) :
    SingleObj (V.toSubgroup ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup) ⥤ C :=
  SingleObj.functor (help44 F V U h A u)

noncomputable def help46 (V U : OpenSubgroup (Aut F)) (h : Subgroup.Normal U.toSubgroup) (A : C)
    (hUinV : U ≤ V)
    (u : (functorToAction F).obj A ≅
      Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ U.toSubgroup)) :
    Cocone (help45 F V U h A u ⋙ functorToAction F) where
  pt := Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ V.toSubgroup)
  ι := by
    apply SingleObj.natTrans
    swap
    show (functorToAction F).obj A ⟶ Action.FintypeCat.ofMulAction (Aut F)
      (FintypeCat.of <| Aut F ⧸ V.toSubgroup)
    exact (u.hom ≫ help43 V.toSubgroup U.toSubgroup hUinV)
    intro (m : V ⧸ Subgroup.subgroupOf U V)
    show (functorToAction F).map (help44 F V U h A u m) ≫ u.hom ≫
      help43 V.toSubgroup U.toSubgroup hUinV = u.hom ≫ help43 V.toSubgroup U.toSubgroup hUinV
    apply (cancel_epi (u.inv)).mp
    rw [Iso.inv_hom_id_assoc]
    apply Action.hom_ext
    ext (x : Aut F ⧸ U.toSubgroup)
    obtain ⟨μ, hμ⟩ := Quotient.exists_rep x
    rw [←hμ]
    let φ : V.toSubgroup ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup →*
        End (Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ U.toSubgroup)) :=
      help3 F V U h
    have : u.inv ≫ (functorToAction F).map (help44 F V U h A u m) ≫ u.hom = φ m := by
      simp [← Iso.conj_apply, MulEquiv.apply_symm_apply, help44]
    show Action.Hom.hom ((u.inv ≫ (functorToAction F).map (help44 F V U h A u m) ≫ u.hom) ≫
      help43 V.toSubgroup U.toSubgroup hUinV) ⟦μ⟧
      = ⟦μ⟧
    rw [this]
    show ((φ m).hom ≫ (help43 V.toSubgroup U.toSubgroup hUinV).hom) ⟦μ⟧ = ⟦μ⟧
    obtain ⟨σ, hσ⟩ := Quotient.exists_rep m
    rw [←hσ]
    show ⟦μ * σ⁻¹⟧ = ⟦μ⟧
    apply Quotient.sound
    apply (QuotientGroup.leftRel_apply).mpr
    simp only [InvMemClass.coe_inv, mul_inv_rev, _root_.inv_inv, inv_mul_cancel_right,
      SetLike.coe_mem]

noncomputable def help461 (V U : OpenSubgroup (Aut F)) (h : Subgroup.Normal U.toSubgroup) (A : C)
    (hUinV : U ≤ V)
    (u : (functorToAction F).obj A ≅
      Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ U.toSubgroup)) :
    (s : Cocone (help45 F V U h A u ⋙ functorToAction F)) →
      (help46 F V U h A hUinV u).pt ⟶ s.pt := by
  let M := V.toSubgroup ⧸ Subgroup.subgroupOf U V
  let J : SingleObj M ⥤ C := help45 F V U h A u
  let J' : SingleObj M ⥤ Action FintypeCat (MonCat.of (Aut F)) := J ⋙ functorToAction F
  let φ : M →* End (Action.FintypeCat.ofMulAction (Aut F)
      (FintypeCat.of <| Aut F ⧸ U.toSubgroup)) :=
    help3 F V U h
  intro s
  constructor
  swap
  show Aut F ⧸ V.toSubgroup ⟶ s.pt.V
  apply Quotient.lift
  swap
  intro (σ : Aut F)
  let f : (functorToAction F).obj A ⟶ s.pt := s.ι.app (SingleObj.star M)
  exact (u.inv ≫ f).hom ⟦σ⟧
  intro σ τ hst
  have : σ⁻¹ * τ ∈ V := (QuotientGroup.leftRel_apply).mp hst
  let m : (SingleObj.star M ⟶ SingleObj.star M) := ⟦⟨σ⁻¹ * τ, this⟩⟧
  have h1 : J'.map m ≫ s.ι.app (SingleObj.star M) = s.ι.app (SingleObj.star M) :=
    s.ι.naturality m
  have h2 : (J'.map m).hom (u.inv.hom ⟦τ⟧) = u.inv.hom ⟦σ⟧ := by
    erw [(help441 F V U h A u m : J'.map m = u.hom ≫ φ m ≫ u.inv)]
    show Action.Hom.hom (u.inv ≫ u.hom ≫ φ m ≫ u.inv) ⟦τ⟧ = Action.Hom.hom u.inv ⟦σ⟧
    simp only [Iso.inv_hom_id_assoc, Action.comp_hom, FintypeCat.comp_apply]
    apply congrArg
    show ⟦τ * (σ⁻¹ * τ)⁻¹⟧ = ⟦σ⟧
    simp only [mul_inv_rev, _root_.inv_inv, mul_inv_cancel_left]
  have h3 : (u.inv ≫ s.ι.app (SingleObj.star M)).hom ⟦σ⟧
      = (u.inv ≫ J'.map m ≫ s.ι.app (SingleObj.star M)).hom ⟦τ⟧ := by
    show (u.inv ≫ s.ι.app (SingleObj.star M)).hom ⟦σ⟧
      = (s.ι.app (SingleObj.star M)).hom ((J'.map m).hom (u.inv.hom ⟦τ⟧))
    rw [h2]
    rfl
  rw [h1] at h3
  exact h3
  intro (g : Aut F)
  ext (x : Aut F ⧸ V.toSubgroup)
  obtain ⟨σ, hσ⟩ := Quotient.exists_rep x
  rw [←hσ]
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.symm_trans_apply, id_eq, Action.comp_hom, FintypeCat.comp_apply,
    InvMemClass.coe_inv, eq_mpr_eq_cast]
  have : ((functorToAction F).obj A).ρ g ≫ (s.ι.app (SingleObj.star M)).hom
    = (s.ι.app (SingleObj.star M)).hom ≫ s.pt.ρ g := (s.ι.app (SingleObj.star M)).comm g
  show (((Action.FintypeCat.ofMulAction (Aut F)
    (FintypeCat.of <| Aut F ⧸ U.toSubgroup)).ρ g ≫ u.inv.hom) ≫
      (s.ι.app (SingleObj.star M)).hom) ⟦σ⟧ =
    ((s.ι.app (SingleObj.star M)).hom ≫ s.pt.ρ g) (u.inv.hom ⟦σ⟧)
  rw [←this, u.inv.comm g]
  rfl

noncomputable def help47 (V U : OpenSubgroup (Aut F)) (h : Subgroup.Normal U.toSubgroup) (A : C)
    (hUinV : U ≤ V)
    (u : (functorToAction F).obj A ≅
        Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ U.toSubgroup)) :
    IsColimit (help46 F V U h A hUinV u) where
  desc := help461 F V U h A hUinV u
  fac s j := by
    apply (cancel_epi u.inv).mp
    apply Action.hom_ext
    ext (x : Aut F ⧸ U.toSubgroup)
    obtain ⟨σ, hσ⟩ := Quotient.exists_rep x
    rw [←hσ]
    show Action.Hom.hom (help461 F V U h A hUinV u s)
      (Action.Hom.hom (u.inv ≫ u.hom ≫ help43 V.toSubgroup U.toSubgroup hUinV) ⟦σ⟧) =
      Action.Hom.hom (s.ι.app j) (Action.Hom.hom u.inv ⟦σ⟧)
    simp only [Iso.inv_hom_id_assoc, comp_obj, const_obj_obj]
    rfl
  uniq s := by
    let M := V ⧸ Subgroup.subgroupOf U V
    intro f hf
    apply Action.hom_ext
    ext (x : Aut F ⧸ V.toSubgroup)
    obtain ⟨σ, hσ⟩ := Quotient.exists_rep x
    rw [←hσ]
    let y : F.obj A := u.inv.hom ⟦σ⟧
    have h1 : ⟦σ⟧ = ((help46 F V U h A hUinV u).ι.app (SingleObj.star M)).hom y := by
      show ⟦σ⟧ = (u.inv ≫ u.hom ≫ help43 V.toSubgroup U.toSubgroup hUinV).hom ⟦σ⟧
      simp only [Iso.inv_hom_id_assoc]
      rfl
    show Action.Hom.hom f ⟦σ⟧ = (s.ι.app (SingleObj.star M)).hom y
    rw [←hf (SingleObj.star M), h1]
    rfl

lemma ess_surj_of_quotient_by_open (V : OpenSubgroup (Aut F)) :
    ∃ (X : C), Nonempty ((functorToAction F).obj X ≅
      Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ V.toSubgroup)) := by
  obtain ⟨I, hf, hc, hi⟩ := help1 F V.toSubgroup V.isOpen'
  have : Fintype I := inferInstance
  let Y : C := ∏ᶜ fun X : I => X
  have hn : Nonempty (F.obj Y) := help2 F I hc
  obtain ⟨A, f, hgal⟩ := exists_hom_from_galois_of_fiber_nonempty F Y hn
  obtain ⟨U, u, hUnormal⟩ := help0 F A
  have h1 : ∀ σ ∈ U, σ.hom.app A = 𝟙 (F.obj A) := by
    intro σ σinU
    have hi : (Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ U.toSubgroup)).ρ σ =
        𝟙 (Aut F ⧸ U.toSubgroup) := by
      apply FintypeCat.hom_ext
      intro (x : Aut F ⧸ U.toSubgroup)
      obtain ⟨τ, hτ⟩ := Quotient.exists_rep x
      rw [←hτ]
      show ⟦σ * τ⟧ = ⟦τ⟧
      apply Quotient.sound
      apply (QuotientGroup.leftRel_apply).mpr
      simp only [mul_inv_rev]
      apply Subgroup.Normal.conj_mem hUnormal
      exact Subgroup.inv_mem U.toSubgroup σinU
    have : Mono u.hom.hom := by
      show Mono ((forget₂ _ FintypeCat).map u.hom)
      infer_instance
    apply (cancel_mono u.hom.hom).mp
    erw [u.hom.comm σ, hi]
    rfl
  have h2 : ∀ σ ∈ U, ∀ X : I, σ.hom.app X = 𝟙 (F.obj X) := by
    intro σ σinU ⟨X, hX⟩
    ext (x : F.obj X)
    have hne : Nonempty (F.obj A) := nonempty_fiber_of_isConnected F A
    let p : A ⟶ X := f ≫ Pi.π (fun Z : I => (Z : C)) ⟨X, hX⟩
    have : IsConnected X := hc X hX
    have : Function.Surjective (F.map p) := surjective_of_nonempty_fiber_of_isConnected F p
    obtain ⟨a, ha⟩ := this x
    simp only [FintypeCat.id_apply, ←ha]
    show (F.map p ≫ σ.hom.app X) a = F.map p a
    rw [σ.hom.naturality, h1 σ σinU]
    rfl
  have hUinV : (U : Set (Aut F)) ≤ V := by
    intro u uinU
    exact hi u (h2 u uinU)
  let U' : Subgroup V := Subgroup.subgroupOf U.toSubgroup V
  have hU'normal : Subgroup.Normal U' := Subgroup.Normal.subgroupOf hUnormal V
  let M := V ⧸ U'
  have : Finite M := finiteQuotientSubgroups V U V.isOpen' U.isOpen'
  let J : SingleObj M ⥤ C := help45 F V U hUnormal A u
  let i1 : (functorToAction F).obj (colimit J) ≅
    colimit (J ⋙ functorToAction F) := preservesColimitIso (functorToAction F) J
  let c : Cocone (J ⋙ functorToAction F) := help46 F V U hUnormal A hUinV u
  let ci : IsColimit c := help47 F V U hUnormal A hUinV u
  let i2 : colimit (J ⋙ functorToAction F) ≅
      Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ V.toSubgroup) :=
    colimit.isoColimitCocone ⟨c, ci⟩
  let i3 : (functorToAction F).obj (colimit J) ≅
    Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ V.toSubgroup) := i1 ≪≫ i2
  let X : C := colimit J
  use X
  exact ⟨i3⟩

end PreGaloisCategory

end CategoryTheory
