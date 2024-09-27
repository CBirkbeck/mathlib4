import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
universe v u
variable (n : ℕ)

open CategoryTheory

lemma Fin.comp_contractNth {G H : Type*} [MulOneClass G] [MulOneClass H] (f : G →* H)
    (j : Fin (n + 1)) (g : Fin (n + 1) → G) :
    f ∘ Fin.contractNth j (· * ·) g = Fin.contractNth j (· * ·) (f ∘ g) := by
  ext x
  rcases lt_trichotomy (x : ℕ) j with (h|h|h)
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_lt, h]
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_eq, h, f.map_mul]
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_gt, h]

namespace Finsupp

def submodule {R M α : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (S : α → Submodule R M) : Submodule R (α →₀ M) where
  carrier := { x | ∀ i, x i ∈ S i }
  add_mem' hx hy i := (S i).add_mem (hx i) (hy i)
  zero_mem' i := (S i).zero_mem
  smul_mem' r _ hx i := (S i).smul_mem r (hx i)

@[simp]
lemma mem_submodule {R M α : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (S : α → Submodule R M) (x : α →₀ M) :
    x ∈ Finsupp.submodule S ↔ ∀ i, x i ∈ S i := by
  rfl

theorem ker_mapRange {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (I : Type*) [DecidableEq I] :
    LinearMap.ker (Finsupp.mapRange.linearMap (α := I) f)
      = Finsupp.submodule (fun _ => LinearMap.ker f) := by
  ext x
  simp [Finsupp.ext_iff]

theorem mapRange_linearMap_comp_lsingle
    {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) {I : Type*} [DecidableEq I] (i : I) :
    Finsupp.mapRange.linearMap f ∘ₗ Finsupp.lsingle i = Finsupp.lsingle i ∘ₗ f := by
  ext x y
  simp

theorem mapRange_injective_iff {α M N : Type*} [Zero M] [Zero N]
    [Nonempty α] (f : M → N) (hf : f 0 = 0) :
    (mapRange (α := α) f hf).Injective ↔ Function.Injective f :=
  ⟨fun h x y hxy => Nonempty.elim (α := α) inferInstance fun a => by
    simpa using congr($(@h (Finsupp.single a x) (Finsupp.single a y)
      (by simp only [hxy, mapRange_single])) a),
  fun h x y hxy => Finsupp.ext fun i => h <| by simpa using congr($hxy i)⟩

theorem range_mapRange {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (hf : LinearMap.ker f = ⊥)
    (I : Type*) [DecidableEq I] :
    LinearMap.range (Finsupp.mapRange.linearMap (α := I) f)
      = Finsupp.submodule (fun _ => LinearMap.range f) := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    rw [← hy]
    simp
  · intro hx
    choose y hy using hx
    refine ⟨⟨x.support, y, fun i => ?_⟩, by ext; simp_all⟩
    constructor
    <;> contrapose!
    <;> simp_all (config := {contextual := true}) [← hy, map_zero,
      LinearMap.ker_eq_bot'.1 hf]

end Finsupp

namespace ModuleCat

variable (R : Type u) [Ring R]

lemma ofHom_comp {M N P : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    ofHom (g ∘ₗ f) = ofHom f ≫ ofHom g := rfl

@[ext]
lemma finsupp_lhom_ext {M N : ModuleCat R} {α : Type*} (f g : ModuleCat.of R (α →₀ M) ⟶ N)
    (h : ∀ x, ModuleCat.ofHom (Finsupp.lsingle x) ≫ f = ModuleCat.ofHom (Finsupp.lsingle x) ≫ g) :
    f = g :=
  Finsupp.lhom_ext' h

end ModuleCat

namespace groupHomology
open Rep

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  (A : Rep k G) (B : Rep k H) (f : G →* H) (φ : A →ₗ[k] B) (n : ℕ)

class IsPairMap : Prop where
  compatible : ∀ (g : G), B.ρ (f g) ∘ₗ φ = φ ∘ₗ A.ρ g

namespace IsPairMap
open Representation

variable {A B f φ} (S : Subgroup G)

lemma compatible_apply [IsPairMap A B f φ] (g : G) (x : A) :
    B.ρ (f g) (φ x) = φ (A.ρ g x) :=
  congr($(compatible g) x)

instance comp {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    (A : Rep k G) (B : Rep k H) (C : Rep k K) (f : G →* H) (g : H →* K) (φ : A →ₗ[k] B)
    (ψ : B →ₗ[k] C) [IsPairMap A B f φ] [IsPairMap B C g ψ] :
    IsPairMap A C (g.comp f) (ψ ∘ₗ φ) where
  compatible x := by
    ext y
    have := congr($(compatible (A := A) (B := B) (f := f) (φ := φ) x) y)
    have := congr($(compatible (A := B) (B := C) (f := g) (φ := ψ) (f x)) (φ y))
    simp_all

instance instCoinf [S.Normal] : IsPairMap A (coinf A S) (QuotientGroup.mk' S)
    (coinvariantsKer (A.ρ.comp S.subtype)).mkQ where
  compatible := by intros; rfl

instance instRes : IsPairMap ((Action.res _ f).obj B) B f LinearMap.id where
  compatible := by intros; rfl

instance instHom {A B : Rep k G} (f : A ⟶ B) : IsPairMap A B (MonoidHom.id G) f.hom where
  compatible g := (f.comm g).symm

variable [IsPairMap A B f φ] [DecidableEq G] [DecidableEq H]

variable (A B f φ) in
@[simps (config := .lemmasOnly)]
noncomputable def chainsMap :
    inhomogeneousChains A ⟶ inhomogeneousChains B where
  f i := ModuleCat.ofHom <| Finsupp.mapRange.linearMap φ ∘ₗ Finsupp.lmapDomain A k (f ∘ ·)
  comm' i j (hij : _ = _) := by
    subst hij
    refine Finsupp.lhom_ext ?_
    intro g a
    simpa [ChainComplex.of_x, ModuleCat.coe_of, ModuleCat.ofHom, ModuleCat.comp_def, map_add,
      map_sum, Fin.comp_contractNth] using congr(Finsupp.single (fun (k : Fin j) => f (g k.succ))
        $(compatible_apply (f := f) (g 0)⁻¹ _))

@[reassoc (attr := simp)]
lemma lsingle_comp_chainsMap (n : ℕ) (x : Fin n → G) :
    ModuleCat.ofHom (Finsupp.lsingle x) ≫ (chainsMap A B f φ).f n
      = ModuleCat.ofHom φ ≫ ModuleCat.ofHom (Finsupp.lsingle (f ∘ x)) := by
  ext
  simp [chainsMap_f]

@[simp]
lemma chainsMap_f_single (n : ℕ) (x : Fin n → G) (a : A) :
    (chainsMap A B f φ).f n (Finsupp.single x a) = Finsupp.single (f ∘ x) (φ a) := by
  simp [chainsMap_f]

@[simp]
lemma chainsMap_id :
    chainsMap A A (MonoidHom.id G) (Action.Hom.hom (𝟙 A)) = 𝟙 (inhomogeneousChains A) := by
  ext : 1
  apply ModuleCat.finsupp_lhom_ext
  exact lsingle_comp_chainsMap _

lemma chainsMap_comp {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    [DecidableEq G] [DecidableEq H] [DecidableEq K]
    (A : Rep k G) (B : Rep k H) (C : Rep k K) (f : G →* H) (g : H →* K) (φ : A →ₗ[k] B)
    (ψ : B →ₗ[k] C) [IsPairMap A B f φ] [IsPairMap B C g ψ] :
    chainsMap A C (g.comp f) (ψ ∘ₗ φ) = (chainsMap A B f φ) ≫ (chainsMap B C g ψ) := by
  ext : 1
  apply ModuleCat.finsupp_lhom_ext
  intro x
  simp [Rep.coe_def, ModuleCat.ofHom_comp, Function.comp.assoc]

lemma chainsMap_eq_mapRange {A B : Rep k G} (i : ℕ) (φ : A ⟶ B) :
    (chainsMap A B (MonoidHom.id G) φ.hom).f i = Finsupp.mapRange.linearMap φ.hom := by
  ext x
  have : (fun (x : Fin i → G) => MonoidHom.id G ∘ x) = id := by ext; rfl
  simp [chainsMap_f, ModuleCat.ofHom, ModuleCat.coe_of, ModuleCat.hom_def, ModuleCat.comp_def,
    this, -Finsupp.mapRange.linearMap_apply, -id_eq]

instance chainsMap_f_map_mono {A B : Rep k G} (φ : A ⟶ B) [Mono φ] (i : ℕ) :
    Mono ((chainsMap A B (MonoidHom.id G) φ.hom).f i) := by
  rw [chainsMap_eq_mapRange]
  exact (ModuleCat.mono_iff_injective _).2 <|
    (Finsupp.mapRange_injective_iff φ.hom (map_zero _)).2 <|
    (ModuleCat.mono_iff_injective φ.hom).1 <| (forget₂ (Rep k G) (ModuleCat k)).map_mono φ

instance chainsMap_f_map_epi {A B : Rep k G} (φ : A ⟶ B) [Epi φ] (i : ℕ) :
    Epi ((chainsMap A B (MonoidHom.id G) φ.hom).f i) where
  left_cancellation f g h := ModuleCat.finsupp_lhom_ext (R := k) _ _ fun x => by
    have h1 : ModuleCat.ofHom (Finsupp.lsingle x) ≫ Finsupp.mapRange.linearMap φ.hom
      = φ.hom ≫ ModuleCat.ofHom (Finsupp.lsingle x) :=
      Finsupp.mapRange_linearMap_comp_lsingle φ.hom x
    letI : Epi φ.hom := (forget₂ (Rep k G) (ModuleCat k)).map_epi φ
    simpa only [← cancel_epi φ.hom, ← Category.assoc, ← h1,
      ← chainsMap_eq_mapRange] using ModuleCat.finsupp_lhom_ext_iff.1 h x

variable (A B f φ)
noncomputable abbrev cyclesMap (n : ℕ) :
    groupHomology.cycles A n ⟶ groupHomology.cycles B n :=
  HomologicalComplex.cyclesMap (chainsMap A B f φ) n

noncomputable abbrev homologyMap (n : ℕ) :
  groupHomology A n ⟶ groupHomology B n :=
HomologicalComplex.homologyMap (chainsMap A B f φ) n

noncomputable abbrev fOne := Finsupp.mapRange.linearMap φ ∘ₗ Finsupp.lmapDomain A k f
noncomputable abbrev fTwo := Finsupp.mapRange.linearMap φ ∘ₗ Finsupp.lmapDomain A k (Prod.map f f)
noncomputable abbrev fThree := Finsupp.mapRange.linearMap φ
  ∘ₗ Finsupp.lmapDomain A k (Prod.map f (Prod.map f f))

@[reassoc (attr := simp)]
lemma chainsMap_f_0_comp_zeroChainsLEquiv :
    (chainsMap A B f φ).f 0 ≫ (zeroChainsLEquiv B : (inhomogeneousChains B).X 0 →ₗ[k] B)
      = (zeroChainsLEquiv A : (inhomogeneousChains A).X 0 →ₗ[k] A) ≫ ModuleCat.ofHom φ := by
  apply ModuleCat.finsupp_lhom_ext
  intro x
  ext y
  rw [lsingle_comp_chainsMap_assoc]
  simp [ModuleCat.ofHom, ModuleCat.coe_of, ModuleCat.hom_def, Function.comp_apply,
    ModuleCat.comp_def, zeroChainsLEquiv, coe_def, Unique.eq_default]

@[reassoc (attr := simp)]
lemma chainsMap_f_1_comp_oneChainsLEquiv :
    (chainsMap A B f φ).f 1 ≫ (oneChainsLEquiv B : (inhomogeneousChains B).X 1 →ₗ[k] (H →₀ B))
      = (oneChainsLEquiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fOne A B f φ) := by
  apply ModuleCat.finsupp_lhom_ext
  intro x
  ext y
  rw [lsingle_comp_chainsMap_assoc]
  simp [ModuleCat.ofHom, ModuleCat.coe_of, ModuleCat.hom_def, Function.comp_apply,
    ModuleCat.comp_def, oneChainsLEquiv, coe_def]

@[reassoc (attr := simp)]
lemma chainsMap_f_2_comp_twoChainsLEquiv :
    (chainsMap A B f φ).f 2
      ≫ (twoChainsLEquiv B : (inhomogeneousChains B).X 2 →ₗ[k] H × H →₀ B)
      = (twoChainsLEquiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fTwo A B f φ) := by
  apply ModuleCat.finsupp_lhom_ext
  intro x
  ext y
  rw [lsingle_comp_chainsMap_assoc]
  simp [ModuleCat.ofHom, ModuleCat.coe_of, ModuleCat.hom_def, Function.comp_apply,
    ModuleCat.comp_def, twoChainsLEquiv, coe_def]

@[reassoc (attr := simp)]
lemma chainsMap_f_3_comp_threeChainsLEquiv :
    (chainsMap A B f φ).f 3
      ≫ (threeChainsLEquiv B : (inhomogeneousChains B).X 3 →ₗ[k] H × H × H →₀ B)
      = (threeChainsLEquiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fThree A B f φ) := by
  apply ModuleCat.finsupp_lhom_ext
  intro x
  ext y
  rw [lsingle_comp_chainsMap_assoc]
  simp [ModuleCat.ofHom, ModuleCat.coe_of, ModuleCat.hom_def, Function.comp_apply,
    ModuleCat.comp_def, threeChainsLEquiv, coe_def, ← Fin.comp_tail]

open ShortComplex

noncomputable def mapH0 : H0 A →ₗ[k] H0 B :=
  Submodule.mapQ _ _ φ <| Submodule.span_le.2 <| fun x ⟨⟨g, y⟩, hy⟩ =>
    mem_coinvariantsKer B.ρ (f g) (φ y) _ <| by simp [compatible_apply, ← hy]

@[simps]
noncomputable def mapShortComplexH1 :
    shortComplexH1 A ⟶ shortComplexH1 B where
  τ₁ := ModuleCat.ofHom (fTwo A B f φ)
  τ₂ := ModuleCat.ofHom (fOne A B f φ)
  τ₃ := ModuleCat.ofHom φ
  comm₁₂ := Finsupp.lhom_ext fun a b => by
    simp [ModuleCat.coe_of, ModuleCat.comp_def, ModuleCat.ofHom, shortComplexH1,
      ← compatible_apply (f := f), map_add, map_sub]
  comm₂₃ := Finsupp.lhom_ext fun a b => by
    simp [ModuleCat.coe_of, ModuleCat.comp_def, ModuleCat.ofHom, shortComplexH1,
      ← compatible_apply (f := f)]

noncomputable abbrev mapOneCycles :
    oneCycles A →ₗ[k] oneCycles B :=
  ShortComplex.cyclesMap' (mapShortComplexH1 A B f φ) (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

noncomputable abbrev mapH1 : H1 A →ₗ[k] H1 B :=
  ShortComplex.leftHomologyMap' (mapShortComplexH1 A B f φ)
    (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

@[simp]
lemma subtype_comp_mapOneCycles :
    (oneCycles B).subtype ∘ₗ mapOneCycles A B f φ = fOne A B f φ ∘ₗ (oneCycles A).subtype :=
  ShortComplex.cyclesMap'_i (mapShortComplexH1 A B f φ) (moduleCatLeftHomologyData _)
    (moduleCatLeftHomologyData _)

@[simp]
lemma H1π_comp_mapH1 :
    mapH1 A B f φ ∘ₗ H1π A = H1π B ∘ₗ mapOneCycles A B f φ :=
  leftHomologyπ_naturality' (mapShortComplexH1 A B f φ) _ _

@[reassoc (attr := simp)]
lemma cyclesMap_comp_isoOneCycles_hom :
    cyclesMap A B f φ 1 ≫ (isoOneCycles B).hom
      = (isoOneCycles A).hom ≫ mapOneCycles A B f φ := by
  simp_rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i, mapOneCycles,
      Category.assoc, cyclesMap'_i, isoOneCycles, ← Category.assoc]
  simp

@[reassoc (attr := simp)]
lemma homologyMap_comp_isoH1_hom :
    homologyMap A B f φ 1 ≫ (isoH1 B).hom = (isoH1 A).hom ≫ mapH1 A B f φ := by
  simpa [← cancel_epi (groupHomologyπ _ _), mapH1, Category.assoc]
    using (leftHomologyπ_naturality' (mapShortComplexH1 A B f φ)
    (moduleCatLeftHomologyData _) (moduleCatLeftHomologyData _)).symm

@[simps]
noncomputable def mapShortComplexH2 :
    shortComplexH2 A ⟶ shortComplexH2 B where
  τ₁ := ModuleCat.ofHom (fThree A B f φ)
  τ₂ := ModuleCat.ofHom (fTwo A B f φ)
  τ₃ := ModuleCat.ofHom (fOne A B f φ)
  comm₁₂ := Finsupp.lhom_ext fun a b => by
    simp [ModuleCat.coe_of, ModuleCat.comp_def, ModuleCat.ofHom, shortComplexH2,
      map_add, map_sub, ← compatible_apply (f := f)]
  comm₂₃ := Finsupp.lhom_ext fun a b => by
    simp [ModuleCat.coe_of, ModuleCat.comp_def, ModuleCat.ofHom, shortComplexH2,
      map_add, map_sub, ← compatible_apply (f := f)]

noncomputable abbrev mapTwoCycles :
    twoCycles A →ₗ[k] twoCycles B :=
  ShortComplex.cyclesMap' (mapShortComplexH2 A B f φ) (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

noncomputable abbrev mapH2 : H2 A →ₗ[k] H2 B :=
  ShortComplex.leftHomologyMap' (mapShortComplexH2 A B f φ)
    (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

@[simp]
lemma subtype_comp_mapTwoCycles :
    (twoCycles B).subtype ∘ₗ mapTwoCycles A B f φ
      = fTwo A B f φ ∘ₗ (twoCycles A).subtype :=
  ShortComplex.cyclesMap'_i (mapShortComplexH2 A B f φ) (moduleCatLeftHomologyData _)
    (moduleCatLeftHomologyData _)

@[simp]
lemma H2π_comp_mapH2 :
    mapH2 A B f φ ∘ₗ H2π A = H2π B ∘ₗ mapTwoCycles A B f φ :=
  leftHomologyπ_naturality' (mapShortComplexH2 A B f φ) _ _

@[reassoc (attr := simp)]
lemma cyclesMap_comp_isoTwoCycles_hom :
    cyclesMap A B f φ 2 ≫ (isoTwoCycles B).hom
      = (isoTwoCycles A).hom ≫ mapTwoCycles A B f φ := by
  simp_rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 B)).i, mapTwoCycles,
      Category.assoc, cyclesMap'_i, isoTwoCycles, ← Category.assoc]
  simp

@[reassoc (attr := simp)]
lemma homologyMap_comp_isoH2_hom :
    homologyMap A B f φ 2 ≫ (isoH2 B).hom = (isoH2 A).hom ≫ mapH2 A B f φ := by
  simpa [← cancel_epi (groupHomologyπ _ _), mapH2, Category.assoc]
    using (leftHomologyπ_naturality' (mapShortComplexH2 A B f φ)
    (moduleCatLeftHomologyData _) (moduleCatLeftHomologyData _)).symm

end IsPairMap
open IsPairMap

variable [DecidableEq G]

variable (k G) in
@[simps]
noncomputable def chainsFunctor : Rep k G ⥤ ChainComplex (ModuleCat k) ℕ where
  obj A := inhomogeneousChains A
  map f := chainsMap _ _ (MonoidHom.id _) f.hom
  map_id _ := chainsMap_id
  map_comp {X Y Z} φ ψ := chainsMap_comp X Y Z (MonoidHom.id G) (MonoidHom.id G) φ.hom ψ.hom

instance : (chainsFunctor k G).PreservesZeroMorphisms where
  map_zero X Y := by
    ext i : 1
    apply Finsupp.lhom_ext
    intro x y
    simp only [chainsFunctor_obj, ChainComplex.of_x, ModuleCat.coe_of, chainsFunctor_map,
      Action.zero_hom, chainsMap_f, ModuleCat.ofHom, LinearMap.coe_comp, Function.comp_apply,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single, HomologicalComplex.zero_f]
    exact Finsupp.single_zero _ -- :/

variable (k G) in

@[simps]
noncomputable def functor (n : ℕ) : Rep k G ⥤ ModuleCat k where
  obj A := groupHomology A n
  map {A B} φ :=
    letI : IsPairMap A B (MonoidHom.id _) φ.hom := instHom φ
    homologyMap A B (MonoidHom.id _) φ.hom n
  map_id A := by
    simp only [homologyMap, chainsMap_id,
      HomologicalComplex.homologyMap_id (inhomogeneousChains A) n]
    rfl
  map_comp f g := by
    simp only [← HomologicalComplex.homologyMap_comp, ← chainsMap_comp]
    rfl

open ShortComplex

def mapShortExact (X : ShortComplex (Rep k G)) (H : ShortExact X) :
    ShortExact ((chainsFunctor k G).mapShortComplex.obj X) :=
  letI := H.2
  letI := H.3
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
      have : LinearMap.range X.f.hom = LinearMap.ker X.g.hom :=
        (H.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      show LinearMap.range ((chainsMap X.X₁ X.X₂ (MonoidHom.id G) X.f.hom).f i)
        = LinearMap.ker ((chainsMap X.X₂ X.X₃ (MonoidHom.id G) X.g.hom).f i)
      rw [chainsMap_eq_mapRange, chainsMap_eq_mapRange, Finsupp.ker_mapRange,
        Finsupp.range_mapRange, this]
      · exact LinearMap.ker_eq_bot.2 ((ModuleCat.mono_iff_injective _).1 <|
          (forget₂ (Rep k G) (ModuleCat k)).map_mono X.f)
    mono_f := chainsMap_f_map_mono X.f i
    epi_g := chainsMap_f_map_epi X.g i }

end groupHomology
