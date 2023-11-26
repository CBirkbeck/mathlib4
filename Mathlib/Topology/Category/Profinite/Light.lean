import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Category.Profinite.Limits
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Sites.RegularExtensive
import Mathlib.CategoryTheory.Sites.Sheafification

universe u

section GeneralTopology

variable {X Y : Type*}
  [TopologicalSpace X]
  [TopologicalSpace Y] [CompactSpace Y] (W : Set (X × Y))
  (hW : IsClopen W) (a : X) (b : Y) (h : (a, b) ∈ W)

theorem exists_clopen_box : ∃ (U : Set X) (V : Set Y) (_ : IsClopen U) (_ : IsClopen V),
    a ∈ U ∧ b ∈ V ∧ (U ×ˢ V : Set (X × Y)) ⊆ W := by
  let V : Set Y := {y | (a, y) ∈ W}
  let p : Y → X × Y := fun y ↦ (a, y)
  have hp : Continuous p := Continuous.Prod.mk _
  have hVC : IsClosed V := hW.2.preimage hp
  have hVC' : IsCompact V := hVC.isCompact
  have hVO : IsOpen V := hW.1.preimage hp
  let U : Set X := {x | ({x} : Set X) ×ˢ V ⊆ W}
  have hUV : U ×ˢ V ⊆ W := by
    intro ⟨w₁, w₂⟩ hw
    rw [Set.prod_mk_mem_set_prod_eq] at hw
    simp only [Set.mem_setOf_eq] at hw
    apply hw.1
    simp only [Set.singleton_prod, Set.mem_image, Set.mem_setOf_eq, Prod.mk.injEq, true_and,
      exists_eq_right]
    exact hw.2
  refine ⟨U, V, ⟨?_, ?_⟩, ⟨hVO, hVC⟩, ?_, h, hUV⟩
  · rw [isOpen_iff_mem_nhds]
    intro x hx
    rw [mem_nhds_iff]
    have := hW.1
    rw [isOpen_prod_iff] at this
    rw [isCompact_iff_finite_subcover] at hVC'
    specialize @hVC' V
      (fun (v : V) ↦ (this x v.val (hUV (Set.mk_mem_prod hx v.prop))).choose_spec.choose) ?_ ?_
    · intro v
      exact (this x v.val (hUV (Set.mk_mem_prod hx v.prop))).choose_spec.choose_spec.2.1
    · intro v hv
      rw [Set.mem_iUnion]
      exact ⟨⟨v, hv⟩, (this x v (hUV (Set.mk_mem_prod hx hv))).choose_spec.choose_spec.2.2.2.1⟩
    · obtain ⟨I, hI⟩ := hVC'
      let t := ⋂ i ∈ I, (fun v ↦ (this x v.val (hUV (Set.mk_mem_prod hx v.prop))).choose) i
      refine ⟨t, ?_, ?_, ?_⟩
      · intro x' hx'
        have hxt : {x'} ×ˢ V ⊆ t ×ˢ V := by
          rw [Set.prod_subset_prod_iff]
          left
          exact ⟨Set.singleton_subset_iff.mpr hx' , subset_refl _⟩
        refine subset_trans hxt ?_
        intro ⟨z, w⟩ hz
        rw [Set.mem_prod] at hz
        have hz' := hI hz.2
        rw [Set.mem_iUnion] at hz'
        obtain ⟨i, hi⟩ := hz'
        rw [Set.mem_iUnion] at hi
        obtain ⟨hhi, hi⟩ := hi
        apply (this x i.val (hUV (Set.mk_mem_prod hx i.prop))).choose_spec.choose_spec.2.2.2.2
        rw [Set.mem_prod]
        refine ⟨?_, hi⟩
        rw [Set.mem_iInter] at hz
        have hhz := hz.1 i
        rw [Set.mem_iInter] at hhz
        exact hhz hhi
      · apply Set.Finite.isOpen_biInter (Set.Finite.ofFinset I (fun _ ↦ Iff.rfl))
        intro v _
        exact (this x v.val (hUV (Set.mk_mem_prod hx v.prop))).choose_spec.choose_spec.1
      · rw [Set.mem_iInter]
        intro v
        rw [Set.mem_iInter]
        intro
        exact (this x v.val (hUV (Set.mk_mem_prod hx v.prop))).choose_spec.choose_spec.2.2.1
  · apply isClosed_of_closure_subset
    intro x hx
    have hhx : {x} ×ˢ V ⊆ (closure U) ×ˢ V := by
      rw [Set.prod_subset_prod_iff]
      left
      exact ⟨Set.singleton_subset_iff.mpr hx , subset_refl _⟩
    refine subset_trans hhx ?_
    have hU : (closure U) ×ˢ V ⊆ closure (U ×ˢ V) := by
      rw [closure_prod_eq, Set.prod_subset_prod_iff]
      left
      exact ⟨subset_refl _, subset_closure⟩
    refine subset_trans hU ?_
    refine subset_trans ?_ hW.2.closure_subset
    exact closure_mono hUV
  · intro ⟨w₁, w₂⟩ hw
    rw [Set.prod_mk_mem_set_prod_eq] at hw
    simp only [Set.mem_singleton_iff, Set.mem_setOf_eq] at hw
    rw [hw.1]
    exact hw.2

variable [CompactSpace X] [T2Space (X × Y)]

open Classical in
theorem exists_finset_clopen_box :
    ∃ (I : Finset ({s : Set X // IsClopen s} × {t : Set Y // IsClopen t})),
    W = ⋃ (i ∈ I), i.1.val ×ˢ i.2.val := by
  have hW' := hW.2.isCompact
  rw [isCompact_iff_finite_subcover] at hW'
  specialize hW' (fun (⟨⟨a, b⟩, hab⟩ : W) ↦ (exists_clopen_box W hW a b hab).choose ×ˢ
    (exists_clopen_box W hW a b hab).choose_spec.choose) ?_ ?_
  · intro ⟨⟨a, b⟩, hab⟩
    exact IsOpen.prod (exists_clopen_box W hW a b hab).choose_spec.choose_spec.1.1
      (exists_clopen_box W hW a b hab).choose_spec.choose_spec.2.1.1
  · intro ⟨a, b⟩ hab
    rw [Set.mem_iUnion]
    use ⟨⟨a, b⟩, hab⟩
    rw [Set.mem_prod]
    exact ⟨(exists_clopen_box W hW a b hab).choose_spec.choose_spec.2.2.1,
      (exists_clopen_box W hW a b hab).choose_spec.choose_spec.2.2.2.1⟩
  · obtain ⟨I, hI⟩ := hW'
    let fI : W → {s : Set X // IsClopen s} × {t : Set Y // IsClopen t} :=
      fun (⟨⟨a, b⟩, hab⟩ : W) ↦ (⟨(exists_clopen_box W hW a b hab).choose,
        (exists_clopen_box W hW a b hab).choose_spec.choose_spec.1⟩,
        ⟨(exists_clopen_box W hW a b hab).choose_spec.choose,
        (exists_clopen_box W hW a b hab).choose_spec.choose_spec.2.1⟩)
    use (fI '' I).toFinset
    ext x
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · replace h := hI h
      rw [Set.mem_iUnion] at h ⊢
      obtain ⟨i, hi⟩ := h
      use fI i
      rw [Set.mem_iUnion] at hi ⊢
      obtain ⟨hi, hi'⟩ := hi
      have hfi : fI i ∈ (fI '' I).toFinset := by
        rw [Set.mem_toFinset]
        exact Set.mem_image_of_mem fI hi
      use hfi
    · rw [Set.mem_iUnion] at h
      obtain ⟨i, hi⟩ := h
      rw [Set.mem_iUnion] at hi
      obtain ⟨hi, h⟩ := hi
      rw [Set.mem_toFinset] at hi
      obtain ⟨w, hw⟩ := hi
      apply (exists_clopen_box W hW w.val.1 w.val.2 w.prop).choose_spec.choose_spec.2.2.2.2
      rw [← hw.2] at h
      exact h

instance countable_clopens_prod [Countable {s : Set X // IsClopen s}]
    [Countable {t : Set Y // IsClopen t}] : Countable {w : Set (X × Y) // IsClopen w} := by
  refine @Function.Surjective.countable
    (Finset ({s : Set X // IsClopen s} × {t : Set Y // IsClopen t})) _ _
    (fun I ↦ ⟨⋃ (i ∈ I), i.1.val ×ˢ i.2.val, ?_⟩) ?_
  · apply Set.Finite.isClopen_biUnion (Set.Finite.ofFinset I (fun _ ↦ Iff.rfl))
    intro i _
    exact IsClopen.prod i.1.2 i.2.2
  · intro ⟨W, hW⟩
    simp only [Subtype.mk.injEq]
    have := exists_finset_clopen_box W hW
    obtain ⟨I, hI⟩ := this
    exact ⟨I, hI.symm⟩

end GeneralTopology

open CategoryTheory Limits FintypeCat Opposite

structure LightProfinite : Type (u+1) where
  diagram : ℕᵒᵖ ⥤ FintypeCat
  cone : Cone (diagram ⋙ toProfinite.{u})
  isLimit : IsLimit cone

@[ext]
theorem LightProfinite.ext {Y : LightProfinite} {a b : Y.cone.pt}
    (h : ∀ n, Y.cone.π.app n a = Y.cone.π.app n b) : a = b := by
  have : PreservesLimitsOfSize.{0, 0} (forget Profinite) := preservesLimitsOfSizeShrink _
  exact Concrete.isLimit_ext _ Y.isLimit _ _ h

def FintypeCat.toLightProfinite (X : FintypeCat) : LightProfinite where
  diagram := (Functor.const _).obj X
  cone := {
    pt := toProfinite.obj X
    π := eqToHom rfl }
  isLimit := {
    lift := fun s ↦ s.π.app ⟨0⟩
    fac := fun s j ↦ (s.π.naturality (homOfLE (zero_le (unop j))).op)
    uniq := fun _ _ h ↦  h ⟨0⟩ }

noncomputable
def LightProfinite.of (F : ℕᵒᵖ ⥤ FintypeCat) : LightProfinite where
  diagram := F
  isLimit := limit.isLimit (F ⋙ FintypeCat.toProfinite)

class Profinite.IsLight (S : Profinite) : Prop where
  countable_clopens : Countable {s : Set S // IsClopen s}

attribute [instance] Profinite.IsLight.countable_clopens

instance (X Y : Profinite) [X.IsLight] [Y.IsLight] : (Profinite.of (X × Y)).IsLight where
  countable_clopens := countable_clopens_prod

open Classical in
noncomputable
def clopensEquiv (S : Profinite) : {s : Set S // IsClopen s} ≃ LocallyConstant S Bool where
  toFun s := {
    toFun := fun x ↦ decide (x ∈ s.val)
    isLocallyConstant := by
      rw [IsLocallyConstant.iff_isOpen_fiber]
      intro y
      cases y with
      | false => convert s.prop.compl.1; ext; simp
      | true => convert s.prop.1; ext; simp }
  invFun f := {
    val := f ⁻¹' {true}
    property := f.2.isClopen_fiber _ }
  left_inv s := by ext; simp
  right_inv f := by ext; simp

open Classical in
instance (S : Profinite) [S.IsLight] : Countable (DiscreteQuotient S) := by
  have : ∀ d : DiscreteQuotient S, Fintype d := fun d ↦ Fintype.ofFinite _
  refine @Function.Surjective.countable ({t : Finset {s : Set S // IsClopen s} //
    (∀ (i j : {s : Set S // IsClopen s}), i ∈ t → j ∈ t → i ≠ j → i.val ∩ j.val = ∅) ∧
    ∀ (x : S), ∃ i, i ∈ t ∧ x ∈ i.val}) _ _ ?_ ?_
  · intro t
    refine ⟨⟨fun x y ↦ ∃ i, i ∈ t.val ∧ x ∈ i.val ∧ y ∈ i.val, ⟨by simpa using t.prop.2,
      fun ⟨i, h⟩ ↦ ⟨i, ⟨h.1, h.2.2, h.2.1⟩⟩, ?_⟩⟩, ?_⟩
    · intro x y z ⟨ixy, hxy⟩ ⟨iyz, hyz⟩
      refine ⟨ixy, hxy.1, hxy.2.1, ?_⟩
      convert hyz.2.2
      by_contra h
      have hh := t.prop.1 ixy iyz hxy.1 hyz.1 h
      apply Set.not_mem_empty y
      rw [← hh]
      exact ⟨hxy.2.2, hyz.2.1⟩
    · intro x
      simp only [setOf, Setoid.Rel]
      obtain ⟨i, h⟩ := t.prop.2 x
      convert i.prop.1 with z
      refine ⟨fun ⟨j, hh⟩ ↦ ?_, fun hh ↦ ?_⟩
      · suffices i = j by rw [this]; exact hh.2.2
        by_contra hhh
        have hhhh := t.prop.1 i j h.1 hh.1 hhh
        apply Set.not_mem_empty x
        rw [← hhhh]
        exact ⟨h.2, hh.2.1⟩
      · exact ⟨i, h.1, h.2, hh⟩
  · intro d
    refine ⟨⟨(Set.range (fun x ↦ ⟨d.proj ⁻¹' {x}, d.isClopen_preimage _⟩)).toFinset, ?_, ?_⟩, ?_⟩
    · intro i j hi hj hij
      simp only [Set.toFinset_range, Finset.mem_image, Finset.mem_univ, true_and] at hi hj
      obtain ⟨ai, hi⟩ := hi
      obtain ⟨aj, hj⟩ := hj
      rw [← hi, ← hj]
      dsimp
      ext x
      refine ⟨fun ⟨hhi, hhj⟩ ↦ ?_, fun h ↦ by simp at h⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hhi hhj
      exfalso
      apply hij
      rw [← hi, ← hj, ← hhi, ← hhj]
    · intro x
      refine ⟨⟨d.proj ⁻¹' {d.proj x}, d.isClopen_preimage _⟩, ?_⟩
      simp
    · ext x y
      simp only [DiscreteQuotient.proj, Set.toFinset_range, Finset.mem_image, Finset.mem_univ,
        true_and, exists_exists_eq_and, Set.mem_preimage, Set.mem_singleton_iff, exists_eq_left',
        Quotient.eq'']
      exact ⟨d.iseqv.symm , d.iseqv.symm⟩

instance (S : Profinite) : IsCofiltered (DiscreteQuotient S) := inferInstance

noncomputable
def cofinal_sequence (S : Profinite) [S.IsLight] : ℕ → DiscreteQuotient S := fun
  | .zero => (exists_surjective_nat _).choose 0
  | .succ n => (IsCofiltered.toIsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (cofinal_sequence S n)).choose

noncomputable
def cofinal_sequence' (S : Profinite) [S.IsLight] : ℕ → DiscreteQuotient S := fun n ↦ by
  induction n with
  | zero => exact (exists_surjective_nat _).choose 0
  | succ n D => exact
      (IsCofiltered.toIsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n) D).choose

theorem antitone_cofinal_sequence (S : Profinite) [S.IsLight] : Antitone (cofinal_sequence S) :=
  antitone_nat_of_succ_le fun n ↦
    leOfHom (IsCofiltered.toIsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (cofinal_sequence S n)).choose_spec.choose_spec.choose

theorem cofinal_cofinal_sequence (S : Profinite) [S.IsLight] :
    ∀ d, ∃ n, cofinal_sequence S n ≤ d := by
  intro d
  obtain ⟨m, h⟩ := (exists_surjective_nat _).choose_spec d
  refine ⟨m + 1, ?_⟩
  rw [← h]
  exact leOfHom (IsCofiltered.toIsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose m)
      (cofinal_sequence S m)).choose_spec.choose

@[simps]
noncomputable def initial_functor (S : Profinite) [S.IsLight] : ℕᵒᵖ ⥤ DiscreteQuotient S where
  obj n := cofinal_sequence S (unop n)
  map h := homOfLE (antitone_cofinal_sequence S (leOfHom h.unop))

instance initial_functor_initial (S : Profinite) [S.IsLight] : (initial_functor S).Initial where
  out d := by
    obtain ⟨n, h⟩ := cofinal_cofinal_sequence S d
    let g : (initial_functor S).obj ⟨n⟩ ⟶ d := eqToHom (by simp) ≫ homOfLE h
    have : Nonempty (CostructuredArrow (initial_functor S) d) := ⟨CostructuredArrow.mk g⟩
    apply isConnected_of_zigzag
    intro i j
    refine ⟨[i, j], ?_⟩
    simp only [List.chain_cons, Zag, or_self, List.Chain.nil, and_true, ne_eq, not_false_eq_true,
      List.getLast_cons, not_true_eq_false, List.getLast_singleton']
    refine ⟨⟨𝟙 _⟩, ?_⟩
    by_cases hnm : unop i.1 ≤ unop j.1
    · right
      refine ⟨CostructuredArrow.homMk (homOfLE hnm).op rfl⟩
    · left
      simp only [not_le] at hnm
      refine ⟨CostructuredArrow.homMk (homOfLE (le_of_lt hnm)).op rfl⟩

namespace LightProfinite

def toProfinite (S : LightProfinite) : Profinite := S.cone.pt

noncomputable
def ofIsLight (S : Profinite.{u}) [S.IsLight] : LightProfinite.{u} where
  diagram := initial_functor S ⋙ S.fintypeDiagram
  cone := (Functor.Initial.limitConeComp (initial_functor S) S.lim).cone
  isLimit := (Functor.Initial.limitConeComp (initial_functor S) S.lim).isLimit

instance (S : LightProfinite.{u}) : S.toProfinite.IsLight where
  countable_clopens := by
    refine @Countable.of_equiv _ _ ?_ (clopensEquiv S.toProfinite).symm
    refine @Function.Surjective.countable
      (Σ (n : ℕ), LocallyConstant ((S.diagram ⋙ FintypeCat.toProfinite).obj ⟨n⟩) Bool) _ ?_ ?_ ?_
    · apply @instCountableSigma _ _ _ ?_
      intro n
      refine @Finite.to_countable _ ?_
      refine @Finite.of_injective _ ((S.diagram ⋙ FintypeCat.toProfinite).obj ⟨n⟩ → Bool) ?_ _
        LocallyConstant.coe_injective
      refine @Pi.finite _ _ ?_ _
      simp only [Functor.comp_obj, toProfinite_obj_toCompHaus_toTop_α]
      infer_instance
    · exact fun a ↦ a.snd.comap (S.cone.π.app ⟨a.fst⟩).1
    · intro a
      obtain ⟨n, g, h⟩ := Profinite.exists_locallyConstant S.cone S.isLimit a
      exact ⟨⟨unop n, g⟩, h.symm⟩

open Classical in
noncomputable def monoLight_diagram {X : Profinite} {Y : LightProfinite} (f : X ⟶ Y.toProfinite) :
    ℕᵒᵖ ⥤ FintypeCat where
  obj := fun n ↦ FintypeCat.of (Set.range (f ≫ Y.cone.π.app n) : Set (Y.diagram.obj n))
  map := fun h ⟨x, hx⟩ ↦ ⟨Y.diagram.map h x, (by
    obtain ⟨y, hx⟩ := hx
    rw [← hx]
    use y
    have := Y.cone.π.naturality h
    simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map, Category.id_comp,
      Functor.comp_map] at this
    rw [this]
    rfl )⟩
  map_id := by -- `aesop` can handle it but is a bit slow
    intro
    simp only [Functor.comp_obj, id_eq, Functor.const_obj_obj, Functor.const_obj_map,
      Functor.comp_map, eq_mp_eq_cast, cast_eq, eq_mpr_eq_cast, CategoryTheory.Functor.map_id,
      FintypeCat.id_apply]
    rfl
  map_comp := by -- `aesop` can handle it but is a bit slow
    intros
    simp only [Functor.comp_obj, id_eq, Functor.const_obj_obj, Functor.const_obj_map,
      Functor.comp_map, eq_mp_eq_cast, cast_eq, eq_mpr_eq_cast, Functor.map_comp,
      FintypeCat.comp_apply]
    rfl

attribute [local instance] FintypeCat.discreteTopology

def monoLight_cone_π_app' (n : ℕᵒᵖ) {X : Profinite} {Y : LightProfinite} (f : X ⟶ Y.toProfinite) :
    C(X, Set.range (f ≫ Y.cone.π.app n)) where
  toFun := fun x ↦ ⟨Y.cone.π.app n (f x), ⟨x, rfl⟩⟩
  continuous_toFun := Continuous.subtype_mk ((Y.cone.π.app n).continuous.comp f.continuous) _

def monoLight_cone_π_app (n : ℕᵒᵖ) {X : Profinite} {Y : LightProfinite} (f : X ⟶ Y.toProfinite) :
    X ⟶ (monoLight_diagram f ⋙ FintypeCat.toProfinite).obj n where
  toFun x := ⟨Y.cone.π.app n (f x), ⟨x, rfl⟩⟩
  continuous_toFun := by
    convert (monoLight_cone_π_app' n f).continuous_toFun
    change ⊥ = _
    ext U
    rw [isOpen_induced_iff]
    have := discreteTopology_bot
    refine ⟨fun _ ↦ ⟨Subtype.val '' U, isOpen_discrete _,
      Function.Injective.preimage_image Subtype.val_injective _⟩, fun _ ↦ isOpen_discrete U⟩
    -- This is annoying

def monoLight_cone {X : Profinite} {Y : LightProfinite.{u}} (f : X ⟶ Y.toProfinite) :
    Cone ((monoLight_diagram f) ⋙ FintypeCat.toProfinite) where
  pt := X
  π := {
    app := fun n ↦ monoLight_cone_π_app n f
    naturality := by
      intro n m h
      have := Y.cone.π.naturality h
      simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map, Category.id_comp,
        Functor.comp_map] at this
      simp only [Functor.comp_obj, toProfinite_obj_toCompHaus_toTop_α, Functor.const_obj_obj,
        Functor.const_obj_map, monoLight_cone_π_app, this, CategoryTheory.comp_apply,
        Category.id_comp, Functor.comp_map]
      rfl }

instance isIso_indexCone_lift {X : Profinite} {Y : LightProfinite.{u}} (f : X ⟶ Y.toProfinite)
    [Mono f] : IsIso ((Profinite.limitConeIsLimit ((monoLight_diagram f) ⋙
    FintypeCat.toProfinite)).lift (monoLight_cone f)) := by
  apply Profinite.isIso_of_bijective
  refine ⟨fun a b h ↦ ?_, fun a ↦ ?_⟩
  · have hf : Function.Injective f := by rwa [← Profinite.mono_iff_injective]
    suffices f a = f b by exact hf this
    apply LightProfinite.ext
    intro n
    apply_fun fun f : (Profinite.limitCone ((monoLight_diagram f) ⋙ FintypeCat.toProfinite)).pt =>
      f.val n at h
    erw [ContinuousMap.coe_mk, Subtype.ext_iff] at h
    exact h
  · suffices : ∃ x, ∀ n, monoLight_cone_π_app (op n) f x = a.val (op n)
    · obtain ⟨x, h⟩ := this
      use x
      apply Subtype.ext
      apply funext
      intro n
      exact h (unop n)
    have : Set.Nonempty (⋂ (n : ℕ), (monoLight_cone_π_app (op n) f) ⁻¹' {a.val (op n)})
    · refine IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed
        (fun n ↦ (monoLight_cone_π_app (op n) f) ⁻¹' {a.val (op n)}) (directed_of_isDirected_le ?_)
        (fun _ ↦ (Set.singleton_nonempty _).preimage fun ⟨a, ⟨b, hb⟩⟩ ↦ ⟨b, Subtype.ext hb⟩)
        (fun _ ↦ (IsClosed.preimage (monoLight_cone_π_app _ _).continuous (T1Space.t1 _)).isCompact)
        (fun _ ↦ IsClosed.preimage (monoLight_cone_π_app _ _).continuous (T1Space.t1 _))
      intro i j h x hx
      simp only [Functor.comp_obj, profiniteToCompHaus_obj, compHausToTop_obj,
        toProfinite_obj_toCompHaus_toTop_α, Functor.comp_map, profiniteToCompHaus_map,
        compHausToTop_map, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
      have := (monoLight_cone f).π.naturality (homOfLE h).op
      simp only [monoLight_cone, Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map,
        Category.id_comp, Functor.comp_map] at this
      rw [this]
      simp only [CategoryTheory.comp_apply]
      rw [hx, ← a.prop (homOfLE h).op]
      rfl
    obtain ⟨x, hx⟩ := this
    exact ⟨x, Set.mem_iInter.1 hx⟩


noncomputable
def monoLight_isLimit {X : Profinite} {Y : LightProfinite} (f : X ⟶ Y.toProfinite) [Mono f] :
    IsLimit (monoLight_cone f) := Limits.IsLimit.ofIsoLimit (Profinite.limitConeIsLimit _)
    (Limits.Cones.ext (asIso ((Profinite.limitConeIsLimit ((monoLight_diagram f) ⋙
    FintypeCat.toProfinite)).lift (monoLight_cone f))) fun _ => rfl).symm

noncomputable
def mono_lightProfinite {X : Profinite} {Y : LightProfinite} (f : X ⟶ Y.toProfinite) [Mono f] :
    LightProfinite := ⟨monoLight_diagram f, monoLight_cone f, monoLight_isLimit f⟩

theorem mono_light {X Y : Profinite} [Y.IsLight] (f : X ⟶ Y) [Mono f] : X.IsLight := by
  let Y' : LightProfinite := ofIsLight Y
  change (mono_lightProfinite (Y := Y') f).toProfinite.IsLight
  infer_instance

instance {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) [X.IsLight] [Y.IsLight] :
    (Profinite.pullback f g).IsLight := by
  let i : Profinite.pullback f g ⟶ Profinite.of (X × Y) := ⟨fun x ↦ x.val, continuous_induced_dom⟩
  have : Mono i := by
    rw [Profinite.mono_iff_injective]
    exact Subtype.val_injective
  exact mono_light i

instance {α : Type} [Fintype α] (X : α → Profinite.{u}) [∀ a, (X a).IsLight] :
    (Profinite.finiteCoproduct X).IsLight where
  countable_clopens := by
    refine @Function.Surjective.countable ((a : α) → {s : Set (X a) // IsClopen s}) _ inferInstance
      (fun f ↦ ⟨⋃ (a : α), Sigma.mk a '' (f a).val, ?_⟩) ?_
    · apply isClopen_iUnion_of_finite
      intro i
      exact ⟨isOpenMap_sigmaMk _ (f i).prop.1, isClosedMap_sigmaMk _ (f i).prop.2⟩
    · intro ⟨s, ⟨hso, hsc⟩⟩
      rw [isOpen_sigma_iff] at hso
      rw [isClosed_sigma_iff] at hsc
      refine ⟨fun i ↦ ⟨_, ⟨hso i, hsc i⟩⟩, ?_⟩
      simp only [Subtype.mk.injEq]
      ext ⟨i, xi⟩
      refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
      · rw [Set.mem_iUnion] at hx
        obtain ⟨_, _, hj, hxj⟩ := hx
        simpa [hxj] using hj
      · rw [Set.mem_iUnion]
        refine ⟨i, xi, (by simpa using hx), rfl⟩

@[simps!]
instance : Category LightProfinite := InducedCategory.category toProfinite

@[simps!]
instance concreteCategory : ConcreteCategory LightProfinite := InducedCategory.concreteCategory _

@[simps!]
def lightToProfinite : LightProfinite.{u} ⥤ Profinite.{u} := inducedFunctor _

instance : Faithful lightToProfinite := show Faithful <| inducedFunctor _ from inferInstance

instance : Full lightToProfinite := show Full <| inducedFunctor _ from inferInstance

instance : lightToProfinite.ReflectsEpimorphisms := inferInstance

instance {X : LightProfinite} : TopologicalSpace ((forget LightProfinite).obj X) :=
  (inferInstance : TopologicalSpace X.cone.pt)

instance {X : LightProfinite} : TotallyDisconnectedSpace ((forget LightProfinite).obj X) :=
  (inferInstance : TotallyDisconnectedSpace X.cone.pt)

instance {X : LightProfinite} : CompactSpace ((forget LightProfinite).obj X) :=
  (inferInstance : CompactSpace X.cone.pt )

instance {X : LightProfinite} : T2Space ((forget LightProfinite).obj X) :=
  (inferInstance : T2Space X.cone.pt )

instance {X : LightProfinite.{u}} : (lightToProfinite.obj X).IsLight :=
  (inferInstance : X.toProfinite.IsLight)

section Pullback

-- TODO: is there a way to avoid this code duplication from `Profinite`?

variable {X Y B : LightProfinite.{u}} (f : X ⟶ B) (g : Y ⟶ B)

noncomputable
def pullback : LightProfinite.{u} :=
  ofIsLight.{u} (Profinite.pullback.{u} (lightToProfinite.{u}.map f) (lightToProfinite.{u}.map g))

/-- The projection from the pullback to the first component. -/
def pullback.fst : pullback f g ⟶ X where
  toFun := fun ⟨⟨x, _⟩, _⟩ => x
  continuous_toFun := Continuous.comp continuous_fst continuous_subtype_val

/-- The projection from the pullback to the second component. -/
def pullback.snd : pullback f g ⟶ Y where
  toFun := fun ⟨⟨_, y⟩, _⟩ => y
  continuous_toFun := Continuous.comp continuous_snd continuous_subtype_val

@[reassoc]
lemma pullback.condition : pullback.fst f g ≫ f = pullback.snd f g ≫ g := by
  ext ⟨_, h⟩
  exact h

/--
Construct a morphism to the explicit pullback given morphisms to the factors
which are compatible with the maps to the base.
This is essentially the universal property of the pullback.
-/
def pullback.lift {Z : LightProfinite.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    Z ⟶ pullback f g where
  toFun := fun z => ⟨⟨a z, b z⟩, by apply_fun (· z) at w; exact w⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_prod_mk]
    exact ⟨a.continuous, b.continuous⟩

@[reassoc (attr := simp)]
lemma pullback.lift_fst {Z : LightProfinite.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    pullback.lift f g a b w ≫ pullback.fst f g = a := rfl

@[reassoc (attr := simp)]
lemma pullback.lift_snd {Z : LightProfinite.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    pullback.lift f g a b w ≫ pullback.snd f g = b := rfl

lemma pullback.hom_ext {Z : LightProfinite.{u}} (a b : Z ⟶ pullback f g)
    (hfst : a ≫ pullback.fst f g = b ≫ pullback.fst f g)
    (hsnd : a ≫ pullback.snd f g = b ≫ pullback.snd f g) : a = b := by
  ext z
  apply_fun (· z) at hfst hsnd
  apply Subtype.ext
  apply Prod.ext
  · exact hfst
  · exact hsnd

/-- The pullback cone whose cone point is the explicit pullback. -/
@[simps! pt π]
noncomputable def pullback.cone : Limits.PullbackCone f g :=
  Limits.PullbackCone.mk (pullback.fst f g) (pullback.snd f g) (pullback.condition f g)

/-- The explicit pullback cone is a limit cone. -/
@[simps! lift]
def pullback.isLimit : Limits.IsLimit (pullback.cone f g) :=
  Limits.PullbackCone.isLimitAux _
    (fun s => pullback.lift f g s.fst s.snd s.condition)
    (fun _ => pullback.lift_fst _ _ _ _ _)
    (fun _ => pullback.lift_snd _ _ _ _ _)
    (fun _ _ hm => pullback.hom_ext _ _ _ _ (hm .left) (hm .right))

end Pullback

section FiniteCoproduct

variable {α : Type} [Fintype α] (X : α → LightProfinite.{u})

/--
The coproduct of a finite family of objects in `LightProfinite`, constructed as the disjoint
union with its usual topology.
-/
noncomputable
def finiteCoproduct : LightProfinite :=
  ofIsLight (Profinite.finiteCoproduct fun a ↦ (X a).toProfinite)

/-- The inclusion of one of the factors into the explicit finite coproduct. -/
def finiteCoproduct.ι (a : α) : X a ⟶ finiteCoproduct X where
  toFun := (⟨a, ·⟩)
  continuous_toFun := continuous_sigmaMk (σ := fun a => (X a).toProfinite)

/--
To construct a morphism from the explicit finite coproduct, it suffices to
specify a morphism from each of its factors.
This is essentially the universal property of the coproduct.
-/
def finiteCoproduct.desc {B : LightProfinite.{u}} (e : (a : α) → (X a ⟶ B)) :
    finiteCoproduct X ⟶ B where
  toFun := fun ⟨a, x⟩ => e a x
  continuous_toFun := by
    apply continuous_sigma
    intro a
    exact (e a).continuous

@[reassoc (attr := simp)]
lemma finiteCoproduct.ι_desc {B : LightProfinite.{u}} (e : (a : α) → (X a ⟶ B)) (a : α) :
    finiteCoproduct.ι X a ≫ finiteCoproduct.desc X e = e a := rfl

lemma finiteCoproduct.hom_ext {B : LightProfinite.{u}} (f g : finiteCoproduct X ⟶ B)
    (h : ∀ a : α, finiteCoproduct.ι X a ≫ f = finiteCoproduct.ι X a ≫ g) : f = g := by
  ext ⟨a, x⟩
  specialize h a
  apply_fun (· x) at h
  exact h

/-- The coproduct cocone associated to the explicit finite coproduct. -/
@[simps]
noncomputable def finiteCoproduct.cocone : Limits.Cocone (Discrete.functor X) where
  pt := finiteCoproduct X
  ι := Discrete.natTrans fun ⟨a⟩ => finiteCoproduct.ι X a

/-- The explicit finite coproduct cocone is a colimit cocone. -/
@[simps]
def finiteCoproduct.isColimit : Limits.IsColimit (finiteCoproduct.cocone X) where
  desc := fun s => finiteCoproduct.desc _ fun a => s.ι.app ⟨a⟩
  fac := fun s ⟨a⟩ => finiteCoproduct.ι_desc _ _ _
  uniq := fun s m hm => finiteCoproduct.hom_ext _ _ _ fun a => by
    specialize hm ⟨a⟩
    ext t
    apply_fun (· t) at hm
    exact hm

end FiniteCoproduct

def fintypeCatToLightProfinite : FintypeCat ⥤ LightProfinite where
  obj X := X.toLightProfinite
  map f := FintypeCat.toProfinite.map f

noncomputable
def EffectiveEpi.struct {B X : LightProfinite.{u}} (π : X ⟶ B) (hπ : Function.Surjective π) :
    EffectiveEpiStruct π where
  desc e h := (QuotientMap.of_surjective_continuous hπ π.continuous).lift e fun a b hab ↦
    FunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
    (by ext; exact hab)) a
  fac e h := ((QuotientMap.of_surjective_continuous hπ π.continuous).lift_comp e
    fun a b hab ↦ FunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
    (by ext; exact hab)) a)
  uniq e h g hm := by
    suffices g = (QuotientMap.of_surjective_continuous hπ π.continuous).liftEquiv ⟨e,
      fun a b hab ↦ FunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
      (by ext; exact hab)) a⟩ by assumption
    rw [← Equiv.symm_apply_eq (QuotientMap.of_surjective_continuous hπ π.continuous).liftEquiv]
    ext
    simp only [QuotientMap.liftEquiv_symm_apply_coe, ContinuousMap.comp_apply, ← hm]
    rfl

theorem epi_iff_surjective {X Y : LightProfinite.{u}} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  constructor
  · dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.continuous).isClosed
    let U := Cᶜ
    have hyU : y ∈ U := by
      refine' Set.mem_compl _
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have hUy : U ∈ nhds y := hC.compl_mem_nhds hyU
    obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_clopen.mem_nhds_iff.mp hUy
    classical
      let Z := (FintypeCat.of (ULift.{u} <| Fin 2)).toLightProfinite
      let g : Y ⟶ Z := ⟨(LocallyConstant.ofClopen hV).map ULift.up, LocallyConstant.continuous _⟩
      let h : Y ⟶ Z := ⟨fun _ => ⟨1⟩, continuous_const⟩
      have H : h = g := by
        rw [← cancel_epi f]
        ext x
        apply ULift.ext
        dsimp [LocallyConstant.ofClopen]
        erw [LightProfinite.instCategoryLightProfinite_comp_apply, ContinuousMap.coe_mk,
          LightProfinite.instCategoryLightProfinite_comp_apply, ContinuousMap.coe_mk,
          Function.comp_apply, if_neg]
        refine' mt (fun α => hVU α) _
        simp only [concreteCategory_forget_obj, Set.mem_compl_iff, Set.mem_range, not_exists,
          not_forall, not_not]
        exact ⟨x, rfl⟩
      apply_fun fun e => (e y).down at H
      dsimp [LocallyConstant.ofClopen] at H
      erw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, Function.comp_apply, if_pos hyV] at H
      exact top_ne_bot H
  · rw [← CategoryTheory.epi_iff_surjective]
    apply (forget LightProfinite).epi_of_epi_map

theorem effectiveEpi_iff_surjective {X Y : LightProfinite.{u}} (f : X ⟶ Y) :
    EffectiveEpi f ↔ Function.Surjective f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨⟨EffectiveEpi.struct f h⟩⟩⟩
  rw [← epi_iff_surjective]
  infer_instance

instance : Preregular LightProfinite where
  exists_fac := by
    intro X Y Z f π hπ
    refine ⟨pullback f π, pullback.fst f π, ?_, pullback.snd f π, (pullback.condition _ _).symm⟩
    rw [LightProfinite.effectiveEpi_iff_surjective] at hπ ⊢
    intro y
    obtain ⟨z,hz⟩ := hπ (f y)
    exact ⟨⟨(y, z), hz.symm⟩, rfl⟩

instance (n : ℕ) (F : Discrete (Fin n) ⥤ LightProfinite) :
    HasColimit (Discrete.functor (F.obj ∘ Discrete.mk) : Discrete (Fin n) ⥤ LightProfinite) where
  exists_colimit := ⟨⟨finiteCoproduct.cocone _, finiteCoproduct.isColimit _⟩⟩

instance : HasFiniteCoproducts LightProfinite where
  out _ := {
    has_colimit := fun _ ↦ hasColimitOfIso Discrete.natIsoFunctor
  }

instance {X Y B : LightProfinite} (f : X ⟶ B) (g : Y ⟶ B) : HasLimit (cospan f g) where
  exists_limit := ⟨⟨pullback.cone f g, pullback.isLimit f g⟩⟩

instance : HasPullbacks LightProfinite where
  has_limit F := hasLimitOfIso (diagramIsoCospan F).symm

noncomputable
instance : PreservesFiniteCoproducts lightToProfinite := by
  refine ⟨fun J hJ ↦ ⟨fun {F} ↦ ?_⟩⟩
  suffices : PreservesColimit (Discrete.functor (F.obj ∘ Discrete.mk)) lightToProfinite
  · exact preservesColimitOfIsoDiagram _ Discrete.natIsoFunctor.symm
  apply preservesColimitOfPreservesColimitCocone (finiteCoproduct.isColimit _)
  exact Profinite.finiteCoproduct.isColimit _

noncomputable
instance : PreservesLimitsOfShape WalkingCospan lightToProfinite := by
  refine ⟨fun {F} ↦ ?_⟩
  suffices : ∀ {X Y B} (f : X ⟶ B) (g : Y ⟶ B), PreservesLimit (cospan f g) lightToProfinite
  · exact preservesLimitOfIsoDiagram _ (diagramIsoCospan F).symm
  intro _ _ _ f g
  apply preservesLimitOfPreservesLimitCone (pullback.isLimit f g)
  exact (isLimitMapConePullbackConeEquiv lightToProfinite (pullback.condition f g)).symm
    (Profinite.pullback.isLimit _ _)

instance : FinitaryExtensive LightProfinite :=
  finitaryExtensive_of_preserves_and_reflects lightToProfinite

instance : Precoherent LightProfinite := sorry -- see #8399

end LightProfinite

structure LightProfinite' : Type u where
  diagram : ℕᵒᵖ ⥤ FintypeCat.Skeleton.{u}

namespace LightProfinite'

noncomputable section

def toProfinite (S : LightProfinite') : Profinite :=
  limit (S.diagram  ⋙ FintypeCat.Skeleton.equivalence.functor ⋙ FintypeCat.toProfinite.{u})

instance : Category LightProfinite' := InducedCategory.category toProfinite

instance : SmallCategory LightProfinite' := inferInstance

instance concreteCategory : ConcreteCategory LightProfinite' := InducedCategory.concreteCategory _

@[simps!]
def lightToProfinite' : LightProfinite' ⥤ Profinite := inducedFunctor _

instance : Faithful lightToProfinite' := show Faithful <| inducedFunctor _ from inferInstance

instance : Full lightToProfinite' := show Full <| inducedFunctor _ from inferInstance

end

end LightProfinite'

noncomputable section Equivalence

def smallToLight : LightProfinite' ⥤ LightProfinite where
  obj X := ⟨X.diagram ⋙ Skeleton.equivalence.functor, _, limit.isLimit _⟩
  map f := f

instance : Faithful smallToLight := ⟨id⟩

instance : Full smallToLight := ⟨id, fun _ ↦ rfl⟩

instance : EssSurj smallToLight := by
  constructor
  intro Y
  let i : limit (((Y.diagram ⋙ Skeleton.equivalence.inverse) ⋙ Skeleton.equivalence.functor) ⋙
    toProfinite) ≅ Y.cone.pt := (Limits.lim.mapIso (isoWhiskerRight ((Functor.associator _ _ _) ≪≫
    (isoWhiskerLeft Y.diagram Skeleton.equivalence.counitIso)) toProfinite)) ≪≫
    IsLimit.conePointUniqueUpToIso (limit.isLimit _) Y.isLimit
  exact ⟨⟨Y.diagram ⋙ Skeleton.equivalence.inverse⟩, ⟨⟨i.hom, i.inv, i.hom_inv_id, i.inv_hom_id⟩⟩⟩
  -- why can't I just write `i`?

instance : IsEquivalence smallToLight := Equivalence.ofFullyFaithfullyEssSurj _

def LightProfinite.equivSmall : LightProfinite ≌ LightProfinite' := smallToLight.asEquivalence.symm

instance : EssentiallySmall LightProfinite where
  equiv_smallCategory := ⟨LightProfinite', inferInstance, ⟨LightProfinite.equivSmall⟩⟩

end Equivalence


variable (P : LightProfinite.{0}ᵒᵖ ⥤ Type)

-- #check (coherentTopology LightProfinite.{0}).sheafify P (D := Type)
-- Doesn't work, need a universe bump because `LightProfinite` is large.

instance : Preregular LightProfinite' := sorry

instance : FinitaryExtensive LightProfinite' := sorry

variable (P : LightProfinite'.{0}ᵒᵖ ⥤ Type)

-- #check (coherentTopology LightProfinite'.{0}).sheafify P (D := Type)
-- Works because `LightProfinite'` is actually small.

-- TODO: provide API to sheafify over essentially small categories
