import Mathlib.CategoryTheory.GaloisCategories.Basic
import Mathlib.CategoryTheory.GaloisCategories.Prorepresantability
import Mathlib.Data.Rel

universe u v w

open CategoryTheory Limits Functor

namespace Galois

section Graph

abbrev graph {X Y : Type u} (f : X → Y) : Type u := { p : X × Y | p.2 = f p.1 }

--instance {X Y : Type u} [Finite X] [Finite Y] (f : X → Y) : Finite (graph f) := by
--  show Finite ({ p : X × Y | p.2 = f p.1 })
--  infer_instance

def graphEquivDomain {X Y : Type u} (f : X → Y) : graph f ≃ X where
  toFun := fun ⟨p, _⟩ => p.1
  invFun x := ⟨⟨x, f x⟩, rfl⟩
  left_inv := fun ⟨p, hp⟩ => by
    apply Subtype.ext
    apply Prod.ext
    rfl
    exact hp.symm
  right_inv x := rfl

end Graph

section Topology

variable {C : Type u} [Category.{v, u} C] (F : C ⥤ FintypeCat.{w})
  [PreGaloisCategory C] [FibreFunctor F]

def fundamentalGroup : Type (max u w) := Aut F

def autEmbedding (σ : Aut F) : (X : C) → Aut (F.obj X) := fun X => σ.app X

lemma autEmbedding_injective : Function.Injective (autEmbedding F) := by
  intro σ τ h
  apply Iso.ext
  apply NatTrans.ext σ.hom τ.hom
  ext X x
  have : σ.app X = τ.app X := congrFun h X
  rw [←Iso.app_hom, ←Iso.app_hom, this]

instance (X : C) : TopologicalSpace (F.obj X) := ⊥
instance (X : C) : DiscreteTopology (F.obj X) := ⟨rfl⟩
instance (X : C) : TopologicalSpace (Aut (F.obj X)) := ⊥
instance (X : C) : DiscreteTopology (Aut (F.obj X)) := ⟨rfl⟩
instance : TopologicalSpace (Aut F) := TopologicalSpace.induced (autEmbedding F) inferInstance

lemma autEmbedding_range :
    Set.range (autEmbedding F) =
    { a | ∀ (X Y : C) (f : X ⟶ Y), F.map f ≫ (a Y).hom = (a X).hom ≫ F.map f } := by
  ext a
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  intro ⟨σ, h⟩
  rw [←h]
  exact σ.hom.naturality
  intro h
  use NatIso.ofComponents (fun X => (a X))
  aesop

lemma fundamentalGroup_closed : IsClosed (Set.range (autEmbedding F)) := by
  rw [autEmbedding_range]
  constructor
  apply isOpen_iff_forall_mem_open.mpr
  intro a h
  simp at h
  obtain ⟨X, Y, f, (h : (a Y).hom ∘ F.map f ≠ F.map f ∘ (a X).hom)⟩ := h
  rw [Function.ne_iff] at h
  obtain ⟨x, hx⟩ := h
  simp at hx
  let U : Set (Aut (F.obj X)) := { γ | γ.hom x = (a X).hom x }
  let V : Set (Aut (F.obj Y)) := { γ | γ.hom (F.map f x) = (a Y).hom (F.map f x) }
  have : IsOpen U := trivial
  have : IsOpen V := trivial
  let sx (A : C) : Set (Aut (F.obj A)) :=
    { γ | ∀ (h : X ⟶ A), γ.hom (F.map h x) = (a A).hom (F.map h x) }
  let sy (A : C) : Set (Aut (F.obj A)) :=
    { γ | ∀ (h : Y ⟶ A), γ.hom (F.map h (F.map f x)) = (a A).hom (F.map h (F.map f x)) }
  let Ix : Set C := {X}
  let Iy : Set C := {Y}
  let tx : Set (∀ A, Aut (F.obj A)) := Set.pi Ix sx
  let ty : Set (∀ A, Aut (F.obj A)) := Set.pi Iy sy
  have hx : IsOpen tx := isOpen_set_pi (Set.toFinite Ix) (fun _ _ => trivial)
  have hy : IsOpen ty := isOpen_set_pi (Set.toFinite Iy) (fun _ _ => trivial)
  let t : Set (∀ A, Aut (F.obj A)) := tx ∩ ty
  have : IsOpen t := IsOpen.inter hx hy
  use t
  refine ⟨?_, ?_, ?_⟩
  intro γ hγ
  simp at hγ
  simp
  use X
  use Y
  use f
  show (γ Y).hom ∘ F.map f ≠ F.map f ∘ (γ X).hom
  rw [Function.ne_iff]
  use x
  simp
  have hty : (γ Y).hom (F.map f x) = (a Y).hom (F.map f x) := by
    have := hγ.2 (𝟙 Y)
    simp at this
    assumption
  have htx : (γ X).hom x = (a X).hom x := by
    have := hγ.1 (𝟙 X)
    simp at this
    assumption
  rw [htx, hty]
  assumption
  assumption
  simp

def autEmbedding_embedding : ClosedEmbedding (autEmbedding F) where
  induced := rfl
  inj := autEmbedding_injective F
  closed_range := fundamentalGroup_closed F

instance (X Y : C) : Finite (F.obj X ⟶ F.obj Y) := by
  show Finite (F.obj X → F.obj Y)
  infer_instance

instance (X : C) : Finite (Aut (F.obj X)) := by
  have : Function.Injective (fun σ : Aut (F.obj X) ↦ σ.hom) := by
    intro σ τ h
    exact Iso.ext h
  exact Finite.of_injective _ this

instance : CompactSpace (∀ X, Aut (F.obj X)) := by
  have (X : C) : CompactSpace (Aut (F.obj X)) := Finite.compactSpace
  exact Pi.compactSpace

instance : CompactSpace (Aut F) := ClosedEmbedding.compactSpace (autEmbedding_embedding F)

instance (X : C) : T2Space (Aut (F.obj X)) := DiscreteTopology.toT2Space

instance : T2Space (∀ X, Aut (F.obj X)) := Pi.t2Space

instance (X : C) : TotallyDisconnectedSpace (Aut (F.obj X)) := inferInstance
instance : TotallyDisconnectedSpace (∀ X, Aut (F.obj X)) := inferInstance

instance : T2Space (Aut F) :=
  T2Space.of_injective_continuous (autEmbedding_injective F) continuous_induced_dom

instance : TotallyDisconnectedSpace (Aut F) := by
  apply (Embedding.isTotallyDisconnected_range (autEmbedding_embedding F).embedding).mp
  exact isTotallyDisconnected_of_totallyDisconnectedSpace _

instance : Group (∀ X, Aut (F.obj X)) := inferInstance

instance : ContinuousMul (∀ X, Aut (F.obj X)) := inferInstance
instance : ContinuousInv (∀ X, Aut (F.obj X)) := inferInstance

def autEmbeddingMonoidHom : Aut F →* (∀ X, Aut (F.obj X)) := by
  apply MonoidHom.mk' (autEmbedding F)
  intro σ τ
  rfl

instance : ContinuousMul (Aut F) :=
  Inducing.continuousMul (autEmbeddingMonoidHom F)
    (autEmbedding_embedding F).toInducing

instance : ContinuousInv (Aut F) := by
  apply Inducing.continuousInv (autEmbedding_embedding F).toInducing
  intro σ
  rfl

instance : TopologicalGroup (Aut F) := ⟨⟩

instance (X : C) : SMul (Aut F) (F.obj X) := ⟨fun σ a => (σ.app X).hom a⟩
instance (X : C) : SMul (Aut (F.obj X)) (F.obj X) := ⟨fun σ a => σ.hom a⟩

instance (X : C) : ContinuousSMul (Aut (F.obj X)) (F.obj X) := by
  constructor
  continuity

instance (X : C) : ContinuousSMul (Aut F) (F.obj X) := by
  constructor
  let f : Aut F × F.obj X → F.obj X := fun ⟨σ, x⟩ => (σ.app X).hom x
  show Continuous f
  admit

end Topology

section Action

variable {C : Type u} [Category.{v, u} C] (F : C ⥤ FintypeCat.{u})
  [PreGaloisCategory C] [FibreFunctor F]

def H : C ⥤ Action FintypeCat (MonCat.of (Aut F)) where
  obj X := {
    V := F.obj X
    ρ := MonCat.ofHom {
      toFun := fun (g : Aut F) => g.hom.app X
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

instance : PreservesMonomorphisms (H F) := sorry

instance : PreservesConnectedObjects (H F) := sorry

lemma lift_transitive_subobjects (X : C) (Y : FintypeCat.{u}) (i : Y ⟶ F.obj X)
    [Mono i] [MulAction (Aut F) Y] [MulAction.IsPretransitive (Aut F) Y]
    [Nonempty Y]
    (h : ∀ (σ : Aut F) (y : Y), i (σ • y) = σ • i y) :
    ∃ (Z : C) (f : Z ⟶ X) (u : Y ≅ F.obj Z),
    ConnectedObject Z ∧ Mono f ∧ i = u.hom ≫ F.map f := by
  have : Nonempty Y := inferInstance
  obtain ⟨y⟩ := this
  let x : F.obj X := i y
  obtain ⟨Z, f, z, hz, hc, hm⟩ := fibre_in_connected_component F X x
  use Z
  use f
  let X' : Action FintypeCat (MonCat.of (Aut F)) := (H F).obj X
  let Z' : Action FintypeCat (MonCat.of (Aut F)) := (H F).obj Z
  let Y' : Action FintypeCat (MonCat.of (Aut F)) := Action.ofMulAction (Aut F) Y
  let i' : Y' ⟶ X' := { hom := i }
  let j' : Z' ⟶ X' := (H F).map f
  have : ReflectsMonomorphisms
      (forget₂ (Action FintypeCat.{u} (MonCat.of (Aut F))) FintypeCat.{u}) :=
    reflectsMonomorphisms_of_faithful _
  have : Mono i' := by
    apply Functor.mono_of_mono_map (forget₂ _ FintypeCat.{u})
    show Mono i
    infer_instance
  have : Mono j' := Functor.map_mono (H F) f
  have : ConnectedObject Z' := PreservesConnectedObjects.preserves
  have : ConnectedObject Y' := connected_of_transitive (Aut F) Y
  have h : (forget₂ (Action FintypeCat (MonCat.of (Aut F))) FintypeCat).map i' y
      = (forget₂ (Action FintypeCat (MonCat.of (Aut F))) FintypeCat).map j' z :=
    hz.symm
  obtain ⟨u', hu'⟩ :=
    @connected_component_unique.{u+1, u, u, u}
    (Action FintypeCat (MonCat.of (Aut F))) _
    (forget₂ (Action FintypeCat (MonCat.of (Aut F))) FintypeCat)
    _ _ X' Y' Z'
    _ _
    y z i' j' h _ _
  let u : Y ≅ F.obj Z :=
    (forget₂ (Action FintypeCat (MonCat.of (Aut F))) FintypeCat).mapIso u'
  use u
  refine ⟨?_, ?_, ?_⟩
  exact hc
  exact hm
  have h2 : i' = u'.hom ≫ (H F).map f := by
    apply @evaluationInjectiveOfConnected.{_, _, _, w} _ _
      (forget₂ (Action FintypeCat (MonCat.of (Aut F))) FintypeCat) _ _ Y' X' _ y
    show (forget₂ (Action FintypeCat (MonCat.of (Aut F))) FintypeCat).map i' y
      = (forget₂ (Action FintypeCat (MonCat.of (Aut F))) FintypeCat).map (u'.hom ≫ (H F).map f) y
    simp only [End.one_def, id_eq, eq_mpr_eq_cast, OneHom.toFun_eq_coe, OneHom.coe_mk, map_comp,
      FintypeCat.comp_apply, hu']
    exact hz.symm
  have h3 :
    (forget₂ (Action FintypeCat (MonCat.of (Aut F))) FintypeCat).map ((H F).map f)
    = F.map f := rfl
  have h4 :
    (forget₂ (Action FintypeCat (MonCat.of (Aut F))) FintypeCat).map i' = i := rfl
  simp
  rw [←h3, ←h4]
  simp
  show
    (forget₂ (Action FintypeCat (MonCat.of (Aut F))) FintypeCat).map
    (i') =
    (forget₂ (Action FintypeCat (MonCat.of (Aut F))) FintypeCat).map
    (u'.hom ≫ (H F).map f)
  congr

lemma lift_subobjects (X : C) (Y : FintypeCat.{u}) (i : Y ⟶ F.obj X)
      [Mono i] [MulAction (Aut F) Y]
      (h : ∀ (σ : Aut F) (y : Y), i (σ • y) = σ • i y)
    : ∃ (Z : C) (f : Z ⟶ X) (u : F.obj Z ≅ Y),
    Mono f ∧ u.hom ≫ i = F.map f := by
  let Y' : Action FintypeCat.{u} (MonCat.of (Aut F)) := Action.ofMulAction (Aut F) Y
  obtain ⟨ι, hf, f, t, hc⟩ := hasDecompConnectedComponents'.{u, _, _, u}
    (forget₂ _ FintypeCat.{u}) Y'
  let f' (i : ι) : FintypeCat.{u} := (f i).V
  have (i : ι) : MulAction (Aut F) (f' i) := sorry
  have (i : ι) : MulAction.IsPretransitive (Aut F) (f' i) := sorry
  have (i : ι) : Nonempty (f' i) := sorry
  have : Fintype ι := Fintype.ofFinite ι
  have inst0 : HasCoproduct.{_, _, _} f := sorry
  have inst1 : HasCoproduct fun j => (f j).V := sorry
  have inst2 : PreservesColimit.{_, _, _, u} (Discrete.functor f)
    (forget₂ (Action FintypeCat.{u} (MonCat.of (Aut F))) FintypeCat.{u}) := sorry
  let is1 : (∐ f).V ≅ ∐ f' :=
    @PreservesCoproduct.iso.{0, u, u, u+1, u+1}
    _ _ _ _
    (forget₂ _ FintypeCat.{u}) _ f inst0 inst1 inst2
  let i' (j : ι) : f' j ⟶ F.obj X := Sigma.ι f' j ≫ is1.inv ≫ (forget₂ _ FintypeCat).map t.hom ≫ i
  have (i : ι) : Mono (i' i) := sorry
  have h' (i : ι) : ∀ (σ : Aut F) (y : f' i), (i' i) (σ • y) = σ • (i' i) y := sorry
  have (i : ι) : ∃ (Z : C) (f : Z ⟶ X) (u : (f' i) ≅ F.obj Z), ConnectedObject Z ∧ Mono f ∧ i' i = u.hom ≫ F.map f :=
    lift_transitive_subobjects.{u, v, u, u} F X (f' i) (i' i) (h' i)
  choose gZ gf gu h3 h4 h5 using this
  use ∐ gZ
  use Sigma.desc gf
  let t' : (∐ f).V ≅ Y := (forget₂ _ FintypeCat).mapIso t
  let is2 : F.obj (∐ gZ) ≅ ∐ fun i => F.obj (gZ i) := PreservesCoproduct.iso F gZ
  let u' : ∐ f' ≅ ∐ fun i => F.obj (gZ i) := Sigma.mapIso gu
  use is2 ≪≫ u'.symm ≪≫ is1.symm ≪≫ t'
  constructor
  admit
  apply (cancel_epi is2.inv).mp
  show is2.inv ≫ (is2 ≪≫ u'.symm ≪≫ is1.symm ≪≫ t').hom ≫ i = is2.inv ≫ F.map (Sigma.desc gf)
  simp
  apply Sigma.hom_ext
  intro j
  simp
  rw [←ι_comp_sigmaComparison, ←PreservesCoproduct.inv_hom]
  show Sigma.ι (fun b ↦ F.obj (gZ b)) j
    ≫ ((PreservesCoproduct.iso F fun b ↦ gZ b).inv ≫
    (PreservesCoproduct.iso F gZ).hom) ≫
      colimMap _ ≫
        sigmaComparison (forget₂ (Action FintypeCat (MonCat.of (Aut F))) FintypeCat) f ≫
          (forget₂ (Action FintypeCat (MonCat.of (Aut F))) FintypeCat).map t.hom ≫ i =
    F.map (gf j)
  rw [Iso.inv_hom_id, Category.id_comp]
  simp
  have : (forget₂ _ FintypeCat).map (Sigma.ι (fun b ↦ f b) j) = Sigma.ι f' j ≫ is1.inv := by
    rw [PreservesCoproduct.inv_hom]
    show (forget₂ _ FintypeCat).map (Sigma.ι (fun b ↦ f b) j) =
      Sigma.ι (fun i => (forget₂ _ FintypeCat).obj (f i)) j
      ≫ sigmaComparison (forget₂ _ FintypeCat) f
    simp
  have : (forget₂ _ FintypeCat).map (Sigma.ι (fun b ↦ f b) j) ≫
      (forget₂ _ FintypeCat).map t.hom ≫ i = i' j := by
    show (forget₂ _ FintypeCat).map (Sigma.ι (fun b ↦ f b) j) ≫
      (forget₂ _ FintypeCat).map t.hom ≫ i =
      Sigma.ι f' j ≫ is1.inv ≫ (forget₂ _ FintypeCat).map t.hom ≫ i
    rw [this, Category.assoc]
  rw [this, h5]
  simp

noncomputable instance H_full : Full (H F) := by
  apply Functor.fullOfExists
  intro X Y ⟨(f : F.obj X ⟶ F.obj Y), hf⟩
  --let Γ_s'' := Function.graph f
  let Γ_s' := graph f
  let p1 : Γ_s' → F.obj X := (graphEquivDomain f).toFun
  let p2 : Γ_s' → F.obj Y := fun ⟨q, _⟩ => q.2
  have hpq : ∀ q : Γ_s', p2 q = f (p1 q) := by
    intro ⟨_, hq⟩ 
    exact hq
  have : Finite Γ_s' := inferInstance
  have : Fintype Γ_s' := Fintype.ofFinite Γ_s'
  let Γ_s : FintypeCat := FintypeCat.of Γ_s'
  let inst : MulAction (Aut F) Γ_s := {
    smul := by
      intro g ⟨q, hq⟩
      constructor
      swap
      exact (g • q.1, g • q.2)
      rw [hq]
      show ((H F).obj Y).ρ g (f q.1) = f (((H F).obj X).ρ g q.1)
      show (f ≫ ((H F).obj Y).ρ g) q.1 = (((H F).obj X).ρ g ≫ f) q.1
      rw [hf g]
    one_smul := by
      intro ⟨q, hq⟩
      rfl
    mul_smul := by
      intro g h ⟨q, hq⟩
      rfl
  }
  let u : Γ_s ⟶ F.obj X ⨯ F.obj Y := prod.lift p1 p2
  let is1 : F.obj (X ⨯ Y) ≅ F.obj X ⨯ F.obj Y := PreservesLimitPair.iso F X Y
  let i : Γ_s ⟶ F.obj (X ⨯ Y) := u ≫ is1.inv
  have : Mono u := by
    apply ConcreteCategory.mono_of_injective
    intro q₁ q₂ hq
    let pr1 : F.obj X ⨯ F.obj Y ⟶ F.obj X := prod.fst
    have hp1 : (u ≫ pr1) q₁ = (u ≫ pr1) q₂ := congrArg pr1 hq
    rw [prod.lift_fst] at hp1
    let pr2 : F.obj X ⨯ F.obj Y ⟶ F.obj Y := prod.snd
    have hp2 : (u ≫ pr2) q₁ = (u ≫ pr2) q₂ := congrArg pr2 hq
    rw [prod.lift_snd] at hp2
    apply Subtype.ext
    apply Prod.ext
    exact hp1
    exact hp2
  have : Mono i := mono_comp u is1.inv
  have h (σ : Aut F) : ∀ y : Γ_s, i (σ • y) = σ • i y := by
    let sf : Γ_s ⟶ Γ_s := fun y => σ • y
    have : sf ≫ i = i ≫ ((H F).obj (X ⨯ Y)).ρ σ := by
      apply (cancel_mono is1.hom).mp
      show sf ≫ u ≫ is1.inv ≫ is1.hom = u ≫ is1.inv ≫ ((H F).obj (X ⨯ Y)).ρ σ ≫ is1.hom
      rw [Iso.inv_hom_id, Category.comp_id]
      apply prod.hom_ext
      show sf ≫ prod.lift p1 p2 ≫ prod.fst = u ≫ is1.inv ≫ ((H F).obj (X ⨯ Y)).ρ σ ≫ is1.hom ≫ prod.fst
      rw [prod.lift_fst, PreservesLimitPair.iso_hom, prodComparison_fst]
      show sf ≫ p1 = u ≫ is1.inv ≫ σ.hom.app (X ⨯ Y) ≫ F.map prod.fst
      rw [←σ.hom.naturality, ←prodComparison_fst, ←PreservesLimitPair.iso_hom]
      show sf ≫ p1 = u ≫ (is1.inv ≫ (PreservesLimitPair.iso F X Y).hom) ≫ prod.fst ≫ σ.hom.app X
      rw [Iso.inv_hom_id, Category.id_comp]
      show sf ≫ p1 = (prod.lift _ _ ≫ prod.fst) ≫ σ.hom.app X
      rw [prod.lift_fst]
      rfl
      show sf ≫ prod.lift p1 p2 ≫ prod.snd = u ≫ is1.inv ≫ ((H F).obj (X ⨯ Y)).ρ σ ≫ is1.hom ≫ prod.snd
      rw [prod.lift_snd, PreservesLimitPair.iso_hom, prodComparison_snd]
      show sf ≫ p2 = u ≫ is1.inv ≫ σ.hom.app (X ⨯ Y) ≫ F.map prod.snd
      rw [←σ.hom.naturality, ←prodComparison_snd, ←PreservesLimitPair.iso_hom]
      show sf ≫ p2 = u ≫ (is1.inv ≫ (PreservesLimitPair.iso F X Y).hom) ≫ prod.snd ≫ σ.hom.app Y
      rw [Iso.inv_hom_id, Category.id_comp]
      show sf ≫ p2 = (prod.lift _ _ ≫ prod.snd) ≫ σ.hom.app Y
      rw [prod.lift_snd]
      rfl
    intro ⟨q, hq⟩
    exact congrFun this _
  obtain ⟨Z, f', u', _, h2⟩ := lift_subobjects F (prod X Y) Γ_s i h
  let ψ : Z ⟶ X := f' ≫ prod.fst
  have : IsIso (F.map ψ) := by
    rw [F.map_comp, ←h2, Category.assoc]
    show IsIso (u'.hom ≫ (i ≫ F.map prod.fst))
    have : IsIso (i ≫ F.map prod.fst) := by
      show IsIso (u ≫ is1.inv ≫ F.map prod.fst)
      rw [←prodComparison_fst, ←PreservesLimitPair.iso_hom]
      show IsIso (u ≫ (is1.inv ≫ (PreservesLimitPair.iso F X Y).hom) ≫ prod.fst)
      rw [Iso.inv_hom_id, Category.id_comp, prod.lift_fst]
      have : Function.Bijective p1 := Equiv.bijective _
      let p1' : Γ_s ⟶ F.obj X := p1
      exact (FintypeCat.isIso_iff_bijective p1').mpr this
    apply IsIso.comp_isIso
  have : IsIso ψ := isIso_of_reflects_iso ψ F
  let φ : X ⟶ Y := inv ψ ≫ f' ≫ prod.snd
  use φ
  ext (x : F.obj X)
  let z : F.obj Z := F.map (inv ψ) x
  have : F.map ψ z = x := by
    show (F.map (inv ψ) ≫ F.map ψ) x = x
    rw [←F.map_comp (inv ψ) ψ]
    simp
  show F.map φ x = f x
  show F.map (inv ψ ≫ f' ≫ prod.snd) x = f x
  rw [←this]
  show (F.map ψ ≫ F.map (CategoryTheory.inv ψ ≫ f' ≫ prod.snd)) z = f (F.map ψ z)
  rw [←F.map_comp, IsIso.hom_inv_id_assoc]
  rw [F.map_comp, ←h2, Category.assoc]
  show (u'.hom ≫ (u ≫ is1.inv) ≫ F.map prod.snd) z = f (F.map ψ z)
  rw [Category.assoc, ←prodComparison_snd, ←PreservesLimitPair.iso_hom]
  show (u'.hom ≫ u ≫ (is1.inv ≫ (PreservesLimitPair.iso F X Y).hom) ≫ prod.snd) z = f (F.map ψ z)
  rw [Iso.inv_hom_id, Category.id_comp, prod.lift_snd]
  show p2 (u'.hom z) = f (F.map ψ z)
  rw [hpq (u'.hom z)]
  apply congrArg
  show p1 (u'.hom z) = F.map (f' ≫ prod.fst) z
  rw [F.map_comp, ←h2, Category.assoc]
  show p1 (u'.hom z) = (u'.hom ≫ u ≫ is1.inv ≫ F.map prod.fst) z
  rw [←prodComparison_fst, ←PreservesLimitPair.iso_hom]
  show p1 (u'.hom z) = (u'.hom ≫ u ≫ (is1.inv ≫ (PreservesLimitPair.iso F X Y).hom) ≫ prod.fst) z
  rw [Iso.inv_hom_id, Category.id_comp, prod.lift_fst]
  rfl

end Action

end Galois
