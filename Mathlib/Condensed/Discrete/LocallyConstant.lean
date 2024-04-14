import Mathlib.Condensed.TopComparison
import Mathlib.Condensed.Discrete.ConstantSheaf

universe u

noncomputable section

open CategoryTheory Limits Condensed LocallyConstant Opposite

@[simps]
def LC : Type (u+1) ⥤ (CompHaus.{u}ᵒᵖ ⥤ Type (u+1)) where
  obj X := {
    obj := fun ⟨S⟩ ↦ LocallyConstant S X
    map := fun f g ↦ g.comap f.unop
    map_id := fun _ ↦ comap_id
    map_comp := fun f g ↦ comap_comp g.unop f.unop }
  map f := {
    app := fun S t ↦ t.map f }

@[simps]
def LC_iso_aux (Y X : Type*) [TopologicalSpace Y] :
    LocallyConstant Y X ≅ C(Y, TopCat.discrete.obj X) :=
  letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  { hom := fun f ↦ (f : C(Y, X))
    inv := fun f ↦ ⟨f, (IsLocallyConstant.iff_continuous f).mpr f.2⟩ }

def LC_iso (X : Type (u+1)) : LC.obj X ≅ (topCatToCondensed.obj (TopCat.discrete.obj X)).val :=
  NatIso.ofComponents (fun S ↦ LC_iso_aux _ _) (fun f ↦ by aesop)

@[simps]
def LC' : Type (u+1) ⥤ CondensedSet.{u} where
  obj X := {
    val := LC.obj X
    cond := by
      rw [Presheaf.isSheaf_of_iso_iff (LC_iso X)]
      exact (topCatToCondensed.obj _).cond
  }
  map f := ⟨LC.map f⟩
  map_id X := by simp only [LC.map_id]; rfl
  map_comp f g := by simp only [LC.map_comp]; rfl

namespace Condensed.locallyConstantDiscrete

section

open CompHaus

variable (X : CondensedSet.{u}) {α : Type u} [Finite α] (σ : α → Type u)
  [∀ a, TopologicalSpace (σ a)] [∀ a, CompactSpace (σ a)] [∀ a, T2Space (σ a)]

def sigmaComparison : X.val.obj ⟨(of ((a : α) × σ a))⟩ ⟶ ((a : α) → X.val.obj ⟨of (σ a)⟩) :=
  fun x a ↦ X.val.map ⟨Sigma.mk a, continuous_sigmaMk⟩ x

noncomputable instance : PreservesLimitsOfShape (Discrete α) X.val :=
  let α' := (Countable.toSmall α).equiv_small.choose
  let e : α ≃ α' := (Countable.toSmall α).equiv_small.choose_spec.some
  have : Fintype α := Fintype.ofFinite _
  have : Fintype α' := Fintype.ofEquiv α e
  have : PreservesFiniteProducts X.val := inferInstance
  have := this.preserves α'
  preservesLimitsOfShapeOfEquiv (Discrete.equivalence e.symm) X.val

theorem sigmaComparison_eq_comp_isos : sigmaComparison X σ =
    (X.val.mapIso (opCoproductIsoProduct' (finiteCoproduct.isColimit.{u, u} fun a ↦ of (σ a))
      (productIsProduct fun x ↦ Opposite.op (of (σ x))))).hom ≫
    (PreservesProduct.iso X.val fun a ↦ ⟨of (σ a)⟩).hom ≫
    (Types.productIso.{u, u + 1} fun a ↦ X.val.obj ⟨of (σ a)⟩).hom := by
  ext x a
  simp only [finiteCoproduct.cocone_pt, Fan.mk_pt, Functor.mapIso_hom,
    PreservesProduct.iso_hom, types_comp_apply, Types.productIso_hom_comp_eval_apply]
  have := congrFun (piComparison_comp_π X.val (fun a ↦ ⟨of (σ a)⟩) a)
  simp only [types_comp_apply] at this
  rw [this, ← FunctorToTypes.map_comp_apply]
  simp only [sigmaComparison]
  apply congrFun
  congr 2
  erw [← opCoproductIsoProduct_inv_comp_ι]
  simp only [coe_of, Opposite.unop_op, unop_comp, Quiver.Hom.unop_op, Category.assoc]
  change finiteCoproduct.ι.{u, u} (fun a ↦ of (σ a)) _ = _
  rw [← Sigma.ι_comp_toFiniteCoproduct]
  congr
  simp only [opCoproductIsoProduct, ← unop_comp, coproductIsoCoproduct,
    opCoproductIsoProduct'_comp_self]
  rfl

instance : IsIso <| sigmaComparison X σ := by
  rw [sigmaComparison_eq_comp_isos]
  infer_instance

end

variable {S : CompHaus.{u}} {Y : Type (u+1)} (f : S → Y) (f' : LocallyConstant S Y)

def α : Type u := Set.range (fun (x : Set.range f) ↦ f ⁻¹' {x.val})

def σ : α f → Type u := fun x ↦ x.val

instance (x : α f) : TopologicalSpace (σ f x) := (inferInstance : TopologicalSpace <| Subtype _)

instance (x : α f) : T2Space (σ f x) := (inferInstance : T2Space <| Subtype _)

instance compactSpaceOfLocallyConstant (x : α f') : CompactSpace x.val := by
  obtain ⟨y, hy⟩ := x.prop
  erw [← isCompact_iff_compactSpace, ← hy]
  exact (f'.2.isClosed_fiber _).isCompact

instance (x : α f') : CompactSpace (σ f' x) := compactSpaceOfLocallyConstant _ _

def α.image (a : α f) : Y := a.2.choose.1

lemma α.eq_fiber_image (a : α f) : a.1 = f ⁻¹' {a.image} := a.2.choose_spec.symm

def α.mk (s : S) : α f := ⟨f ⁻¹' {f s}, by simp⟩

def α.mkSelf (s : S) : (mk f s).val := ⟨s, rfl⟩

lemma α.map_eq_image (a : α f) (x : a.1) : f x = a.image := by
  have := a.2.choose_spec
  rw [← Set.mem_singleton_iff, ← Set.mem_preimage]
  convert x.prop

lemma α.mk_image (s : S) : (α.mk f s).image = f s :=
  (map_eq_image (x := mkSelf f s)).symm

lemma α.mem_iff_eq_image (s : S) (a : α f) : s ∈ a.val ↔ f s = a.image := by
  constructor
  · intro h
    exact a.map_eq_image _ ⟨s, h⟩
  · intro h
    rw [a.eq_fiber_image]
    exact h

def α.preimage (a : α f) : S := a.2.choose.2.choose

lemma α.map_preimage_eq_image (a : α f) : f a.preimage = a.image := a.2.choose.2.choose_spec

instance : Finite (α f') :=
  have : Finite (Set.range f') := range_finite f'
  Finite.Set.finite_range _

lemma α.map_preimage_eq_image_map {X : Type (u+1)} (g : Y → X) (a : α (g ∘ f)) :
    g (f a.preimage) = a.image := by
  rw [← map_preimage_eq_image]
  rfl

variable {T : CompHaus.{u}} (g : T ⟶ S)

lemma α.map_eq_image_comap (a : α (f'.comap g)) (x : a.1) : f' (g x.val) = a.image := by
  rw [← map_eq_image (f'.comap g) a x]
  rfl

lemma α.map_preimage_eq_image_comap (a : α (f'.comap g)) : f' (g a.preimage) = a.image := by
  rw [← map_preimage_eq_image]
  rfl

lemma α.image_eq_image_mk (a : α (f'.comap g)) : a.image = (α.mk f' (g (a.preimage _))).image := by
  rw [← map_preimage_eq_image_comap, mk_image]

def component_hom (a : α (f'.comap g)) :
    CompHaus.of a.val ⟶ CompHaus.of (α.mk f' (g a.preimage)).val where
  toFun x := ⟨g x.val, by
    simp only [α.mk, Set.mem_preimage, Set.mem_singleton_iff]
    rw [α.map_eq_image_comap, α.map_preimage_eq_image_comap]
    ⟩
  continuous_toFun := Continuous.subtype_mk (Continuous.comp g.continuous continuous_subtype_val) _

@[simps]
def sigmaToFun : C((x : α f) × x.val, S) where
  toFun := fun ⟨a, x⟩ ↦ x.val

lemma sigmaToFun_inj : Function.Injective (sigmaToFun f) := by
  rintro ⟨⟨_, _, rfl⟩, ⟨_, hx⟩⟩ ⟨⟨_, _, rfl⟩, ⟨_, hy⟩⟩ h
  refine Sigma.subtype_ext ?_ h
  simp only [sigmaToFun_apply] at h
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx hy
  simp [← hx, ← hy, h]

lemma sigmaToFun_surj : Function.Surjective (sigmaToFun f) :=
  fun _ ↦ ⟨⟨⟨_, ⟨⟨_, Set.mem_range_self _⟩, rfl⟩⟩, ⟨_, rfl⟩⟩, rfl⟩

@[simps!]
def sigmaIso : (CompHaus.of <| (x : α f') × x.val) ≅ S :=
  CompHaus.isoOfBijective (sigmaToFun f') ⟨sigmaToFun_inj f', sigmaToFun_surj f'⟩

@[simps]
def sigmaIncl' (a : α f) : C(a.val, S) where
  toFun := fun x ↦ x.val

@[simps!]
def sigmaIncl (a : α f') : CompHaus.of a.val ⟶ S := sigmaIncl' _ _

section

variable {X : Type (u+1)} (g : Y → X)

def extracted_map (a : α (f'.map g)) (b : α (f'.comap (sigmaIncl (map g f') a))) :
    CompHaus.of b.val ⟶ CompHaus.of (α.mk f' (b.preimage).val).val where
  toFun x := ⟨x.val.val, by
    rw [α.mem_iff_eq_image, α.mk_image]
    simp only [map_apply, CompHaus.coe_of, sigmaIncl, sigmaIncl', coe_comap,
      ContinuousMap.coe_mk]
    have := x.prop
    rw [α.mem_iff_eq_image] at this
    simp only [map_apply, CompHaus.coe_of, sigmaIncl, sigmaIncl', coe_comap,
      ContinuousMap.coe_mk, Function.comp_apply] at this
    rw [this]
    exact (α.map_preimage_eq_image _ _).symm⟩
  continuous_toFun := Continuous.subtype_mk (continuous_induced_dom.comp continuous_induced_dom) _

lemma sigmaIncl_comp_sigmaIncl (a : α (f'.map g)) (b : α (f'.comap (sigmaIncl (f'.map g) a))) :
    sigmaIncl (f'.comap (sigmaIncl (f'.map g) a)) b ≫ sigmaIncl (f'.map g) a =
      (extracted_map _ _ a b) ≫ sigmaIncl f' (α.mk f' (b.preimage).val) := rfl

end

variable {Y : CondensedSet.{u}} (f : LocallyConstant S (Y.val.obj (op (⊤_ _))))

@[elementwise (attr := simp), reassoc]
lemma sigmaComparison_comp_sigmaIso' (X : CondensedSet.{u}) (a : α f):
    (X.val.mapIso (sigmaIso f).op).hom ≫ sigmaComparison X (σ f) ≫ (fun g ↦ g a) =
      X.val.map (sigmaIncl f a).op := by
  ext
  simp only [Functor.mapIso_hom, Iso.op_hom, types_comp_apply, sigmaComparison,
    CompHaus.coe_of]
  rw [← FunctorToTypes.map_comp_apply]
  congr

-- @[elementwise (attr := simp), reassoc]
lemma sigmaComparison_comp_sigmaIso (a : α f):
    (Y.val.mapIso (sigmaIso f).op).hom ≫ sigmaComparison Y (σ f) ≫ (fun g ↦ g a) =
      Y.val.map (sigmaIncl f a).op := sigmaComparison_comp_sigmaIso' f Y a

def counit_app_app_image : (a : α f) → Y.val.obj ⟨CompHaus.of <| a.val⟩ :=
  fun a ↦ Y.val.map (terminal.from _).op a.image

def counit_app_app (S : CompHaus.{u}) (Y : CondensedSet.{u}) :
    LocallyConstant S (Y.val.obj (op (⊤_ _))) ⟶ Y.val.obj ⟨S⟩ :=
  fun f ↦ ((inv (sigmaComparison Y (σ f))) ≫ (Y.val.mapIso (sigmaIso f).op).inv)
    (counit_app_app_image f)

lemma locallyConstantCondensed_ext' (X : CondensedSet.{u}) (x y : X.val.obj ⟨S⟩)
    (h : ∀ (a : α f), X.val.map (sigmaIncl f a).op x = X.val.map (sigmaIncl f a).op y) : x = y := by
  apply_fun (X.val.mapIso (sigmaIso f).op).hom using injective_of_mono _
  apply_fun sigmaComparison X (σ f) using injective_of_mono _
  ext a
  specialize h a
  rw [← sigmaComparison_comp_sigmaIso'] at h
  exact h

lemma locallyConstantCondensed_ext (x y : Y.val.obj ⟨S⟩)
    (h : ∀ (a : α f), Y.val.map (sigmaIncl f a).op x = Y.val.map (sigmaIncl f a).op y) : x = y :=
  locallyConstantCondensed_ext' f Y x y h

lemma _root_.CategoryTheory.types_iso_inv_comp_apply {X Y : Type _} (i : X ⟶ Y) (y : Y) [IsIso i] :
    i (inv i y) = y :=
  inv_hom_id_apply (asIso i) _

lemma incl_of_counit_app_app (a : α f) :
    Y.val.map (sigmaIncl f a).op (counit_app_app S Y f) = counit_app_app_image f a := by
  simp only [← sigmaComparison_comp_sigmaIso, Functor.mapIso_hom, Iso.op_hom, types_comp_apply]
  simp only [counit_app_app, Functor.mapIso_inv, ← Iso.op_hom, types_comp_apply,
    ← FunctorToTypes.map_comp_apply, Iso.inv_hom_id, FunctorToTypes.map_id_apply,
    types_iso_inv_comp_apply (i := sigmaComparison _ _)]

lemma incl_comap (a : α (f.comap g)) : sigmaIncl (f.comap g) a ≫ g =
    (component_hom f g a) ≫ sigmaIncl f _ := rfl

lemma incl_comap_op {S T : CompHausᵒᵖ} (f : LocallyConstant S.unop (Y.val.obj (op (⊤_ _))))
    (g : S ⟶ T) (a : α (f.comap g.unop)) : g ≫ (sigmaIncl (f.comap g.unop) a).op =
    (sigmaIncl f _).op ≫ (component_hom f g.unop a).op := by
  rw [← op_comp, ← incl_comap]
  simp

@[simps!]
def counitApp (Y : CondensedSet.{u}) : LC'.obj (Y.val.obj (op (⊤_ _))) ⟶ Y where
  val := {
    app := fun ⟨S⟩ ↦ counit_app_app S Y
    naturality := by
      intro S T g
      simp only [LC', LC]
      ext f
      apply locallyConstantCondensed_ext (f.comap g.unop)
      intro a
      simp only [op_unop, types_comp_apply]
      rw [incl_of_counit_app_app, ← FunctorToTypes.map_comp_apply, incl_comap_op]
      simp only [op_unop, FunctorToTypes.map_comp_apply]
      rw [incl_of_counit_app_app]
      simp only [counit_app_app_image, ← FunctorToTypes.map_comp_apply, ← op_comp,
        terminal.comp_from, α.image_eq_image_mk]
  }

theorem hom_apply_counit_app_app {X : CondensedSet.{u}} (g : Y ⟶ X)
    (a : α (f.map (g.val.app (op (⊤_ CompHaus))))) :
    X.val.map (sigmaIncl (map (g.val.app (op (⊤_ CompHaus))) f) a).op
      (g.val.app ⟨S⟩ (counit_app_app S Y f)) =
        counit_app_app_image (map (g.val.app (op (⊤_ CompHaus))) f) a := by
  apply locallyConstantCondensed_ext' (f.comap (sigmaIncl _ _))
  intro b
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
  simp only [counit_app_app_image]
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
  simp only [CompHaus.coe_of, map_apply, terminal.comp_from]
  rw [← α.map_preimage_eq_image_map]
  change (_ ≫ X.val.map _) _ = (_ ≫ X.val.map _) _
  simp only [← g.val.naturality]
  rw [sigmaIncl_comp_sigmaIncl]
  simp only [coe_comap, map_apply, CompHaus.coe_of, op_comp, Functor.map_comp, types_comp_apply]
  rw [incl_of_counit_app_app]
  simp only [counit_app_app_image, ← FunctorToTypes.map_comp_apply, ← op_comp,
    terminal.comp_from]
  erw [α.mk_image]
  change (Y.val.map _ ≫ _) _ = (Y.val.map _ ≫ _) _
  simp only [g.val.naturality]
  simp only [types_comp_apply]
  have := α.map_preimage_eq_image (f := g.val.app _ ∘ f) (a := a)
  simp only [Function.comp_apply] at this
  rw [this]
  apply congrArg
  erw [← α.mem_iff_eq_image (f := g.val.app _ ∘ f)]
  exact (b.preimage).prop

@[simps]
def counit : underlying (Type (u+1)) ⋙ LC' ⟶ 𝟭 _ where
  app := counitApp
  naturality X Y g := by
    apply Sheaf.hom_ext
    simp only [underlying, LC', id_eq, eq_mpr_eq_cast, Functor.comp_obj, Functor.flip_obj_obj,
      sheafToPresheaf_obj, Functor.id_obj, Functor.comp_map, Functor.flip_obj_map,
      sheafToPresheaf_map, Functor.id_map]
    rw [Sheaf.instCategorySheaf_comp_val, Sheaf.instCategorySheaf_comp_val]
    ext S (f : LocallyConstant _ _)
    simp only [FunctorToTypes.comp, counitApp_val_app]
    apply locallyConstantCondensed_ext (f.map (g.val.app (op (⊤_ _))))
    intro a
    simp only [map_apply, op_unop]
    erw [incl_of_counit_app_app]
    exact (hom_apply_counit_app_app _ _ _).symm

@[simps]
def unit : 𝟭 _ ⟶ LC' ⋙ underlying _ where
  app X x := LocallyConstant.const _ x

theorem locallyConstantAdjunction_left_triangle (X : Type (u + 1)) :
    LC.map (unit.app X) ≫ (counit.app (LC'.obj X)).val = 𝟙 (LC.obj X) := by
  ext ⟨S⟩ (f : LocallyConstant _ X)
  simp only [Functor.id_obj, Functor.comp_obj, underlying_obj, FunctorToTypes.comp, NatTrans.id_app,
    LC_obj_obj, types_id_apply]
  simp only [counit, counitApp_val_app]
  apply locallyConstantCondensed_ext' (X := LC'.obj X) (Y := LC'.obj X) (f.map (unit.app X))
  intro a
  erw [incl_of_counit_app_app]
  simp only [LC'_obj_val, LC_obj_obj, unop_op, Functor.id_obj, map_apply, CompHaus.coe_of,
    counit_app_app_image, LC_obj_map, Quiver.Hom.unop_op]
  ext x
  erw [← α.map_eq_image _ a x]
  rfl

def _root_.CompHaus.isTerminalPUnit : IsTerminal (CompHaus.of PUnit.{u + 1}) :=
  haveI : ∀ X, Unique (X ⟶ CompHaus.of PUnit.{u + 1}) := fun X =>
    ⟨⟨⟨fun _ => PUnit.unit, continuous_const⟩⟩, fun f => by ext; aesop⟩
  Limits.IsTerminal.ofUnique _

def _root_.CompHaus.terminalIsoPUnit : ⊤_ CompHaus.{u} ≅ CompHaus.of PUnit :=
  terminalIsTerminal.uniqueUpToIso CompHaus.isTerminalPUnit

@[simps]
def unitInv : LC' ⋙ underlying _ ⟶ 𝟭 (Type (u+1)) where
  app X f := f.toFun (CompHaus.terminalIsoPUnit.inv PUnit.unit)

def unitIso : 𝟭 (Type (u+1)) ≅ LC' ⋙ underlying _ where
  hom := unit
  inv := unitInv
  inv_hom_id := by
    ext
    simp only [Functor.comp_obj, underlying_obj, LC'_obj_val, LC_obj_obj, FunctorToTypes.comp,
      unitInv_app, toFun_eq_coe, unit_app, const, NatTrans.id_app, types_id_apply]
    apply DFunLike.ext
    intro _
    simp only [coe_mk, Function.const_apply]
    congr
    apply_fun CompHaus.terminalIsoPUnit.hom
    · rfl
    · intro _ _ h
      convert congrArg CompHaus.terminalIsoPUnit.inv h
      all_goals simp

instance : IsIso unit := (inferInstance : IsIso unitIso.hom)

@[simps]
def adjunction' : Adjunction.CoreUnitCounit LC' (underlying (Type (u+1))) where
  unit := unit
  counit := counit
  left_triangle := by
    ext X
    simp only [id_eq, eq_mpr_eq_cast, Functor.comp_obj, Functor.id_obj, NatTrans.comp_app,
      underlying_obj, LC_obj_obj, whiskerRight_app, Functor.associator_hom_app, whiskerLeft_app,
      Category.id_comp, NatTrans.id_app']
    apply Sheaf.hom_ext
    rw [Sheaf.instCategorySheaf_comp_val, Sheaf.instCategorySheaf_id_val]
    exact locallyConstantAdjunction_left_triangle X
  right_triangle := by
    ext X (x : X.val.obj _)
    simp only [Functor.comp_obj, Functor.id_obj, underlying_obj, counit, FunctorToTypes.comp,
      whiskerLeft_app, Functor.associator_inv_app, LC'_obj_val, LC_obj_obj, types_id_apply,
      whiskerRight_app, underlying_map, counitApp_val_app, NatTrans.id_app']
    apply locallyConstantCondensed_ext (unit.app _ x)
    intro a
    erw [incl_of_counit_app_app]
    simp only [unit, Functor.id_obj, coe_const, counit_app_app_image]
    let y : ⊤_ CompHaus := CompHaus.terminalIsoPUnit.inv PUnit.unit
    have := α.map_eq_image _ a ⟨y, by simp [α.mem_iff_eq_image, ← α.map_preimage_eq_image, unit]⟩
    erw [← this]
    simp only [unit, Functor.id_obj, coe_const, Function.const_apply]
    have hh : sigmaIncl (const _ x) a = terminal.from _ := Unique.uniq _ _
    rw [hh]

@[simps!]
def adjunction : LC' ⊣ underlying _ :=
  Adjunction.mkOfUnitCounit adjunction'

def iso : LC' ≅ discrete _ := adjunction.leftAdjointUniq (discrete_underlying_adj _)

end Condensed.locallyConstantDiscrete
