/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.QuasiIso

#align_import category_theory.preadditive.projective_resolution from "leanprover-community/mathlib"@"324a7502510e835cdbd3de1519b6c66b51fb2467"

/-!
# Projective resolutions

A projective resolution `P : ProjectiveResolution Z` of an object `Z : C` consists of
an `ℕ`-indexed chain complex `P.complex` of projective objects,
along with a chain map `P.π` from `C` to the chain complex consisting just of `Z` in degree zero,
so that the augmented chain complex is exact.

When `C` is abelian, this exactness condition is equivalent to `π` being a quasi-isomorphism.
It turns out that this formulation allows us to set up the basic theory of derived functors
without even assuming `C` is abelian.

(Typically, however, to show `HasProjectiveResolutions C`
one will assume `EnoughProjectives C` and `Abelian C`.
This construction appears in `CategoryTheory.Abelian.Projective`.)

We show that given `P : ProjectiveResolution X` and `Q : ProjectiveResolution Y`,
any morphism `X ⟶ Y` admits a lift to a chain map `P.complex ⟶ Q.complex`.
(It is a lift in the sense that
the projection maps `P.π` and `Q.π` intertwine the lift and the original morphism.)

Moreover, we show that any two such lifts are homotopic.

As a consequence, if every object admits a projective resolution,
we can construct a functor `projectiveResolutions C : C ⥤ HomotopyCategory C`.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace ShortComplex

variable [Abelian C] {S : ShortComplex C}

def Exact.liftFromProjective (hS : S.Exact) {P : C} (f : P ⟶ S.X₂) [Projective P] (hf : f ≫ S.g = 0) :
    P ⟶ S.X₁ := by
  have := hS.epi_toCycles
  exact Projective.factorThru (S.liftCycles f hf) S.toCycles

@[reassoc (attr := simp)]
lemma Exact.liftFromProjective_comp
    (hS : S.Exact) {P : C} (f : P ⟶ S.X₂) [Projective P] (hf : f ≫ S.g = 0) :
    hS.liftFromProjective f hf ≫ S.f = f := by
  have := hS.epi_toCycles
  dsimp [liftFromProjective]
  simp only [← toCycles_i, Projective.factorThru_comp_assoc, liftCycles_i]

end ShortComplex


open Projective

section

variable [Abelian C]

-- porting note: removed @[nolint has_nonempty_instance]
/--
A `ProjectiveResolution Z` consists of a bundled `ℕ`-indexed chain complex of projective objects,
along with a quasi-isomorphism to the complex consisting of just `Z` supported in degree `0`.

(We don't actually ask here that the chain map is a quasi-iso, just exactness everywhere:
that `π` is a quasi-iso is a lemma when the category is abelian.
Should we just ask for it here?)

Except in situations where you want to provide a particular projective resolution
(for example to compute a derived functor),
you will not typically need to use this bundled object, and will instead use
* `ProjectiveResolution Z`: the `ℕ`-indexed chain complex
  (equipped with `Projective` and `Exact` instances)
* `ProjectiveResolution.π Z`: the chain map from `ProjectiveResolution Z` to
  `(ChainComplex.single₀ C).obj Z` (all the components are equipped with `Epi` instances,
  and when the category is `Abelian` we will show `π` is a quasi-iso).
-/
structure ProjectiveResolution (Z : C) where
  complex : ChainComplex C ℕ
  [hasHomology : ∀ i, complex.HasHomology i]
  π : complex ⟶ ((ChainComplex.single₀ C).obj Z)
  projective : ∀ n, Projective (complex.X n) := by infer_instance
  hπ : QuasiIso π := by infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution CategoryTheory.ProjectiveResolution

attribute [instance] ProjectiveResolution.projective ProjectiveResolution.hasHomology
  ProjectiveResolution.hπ

/-- An object admits a projective resolution.
-/
class HasProjectiveResolution (Z : C) : Prop where
  out : Nonempty (ProjectiveResolution Z)
#align category_theory.has_projective_resolution CategoryTheory.HasProjectiveResolution

section

variable (C)

/-- You will rarely use this typeclass directly: it is implied by the combination
`[EnoughProjectives C]` and `[Abelian C]`.
By itself it's enough to set up the basic theory of derived functors.
-/
class HasProjectiveResolutions : Prop where
  out : ∀ Z : C, HasProjectiveResolution Z
#align category_theory.has_projective_resolutions CategoryTheory.HasProjectiveResolutions

attribute [instance 100] HasProjectiveResolutions.out

end

namespace ProjectiveResolution

lemma complex_exactAt_succ {Z : C} (P : ProjectiveResolution Z) (n : ℕ) :
    P.complex.ExactAt n.succ := by
  rw [← quasiIsoAt_iff_exactAt' P.π n.succ (ChainComplex.single₀_exactAt _ _)]
  · infer_instance

@[simp]
theorem π_f_succ {Z : C} (P : ProjectiveResolution Z) (n : ℕ) : P.π.f (n + 1) = 0 := by
  apply zero_of_target_iso_zero
  dsimp; rfl
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.π_f_succ CategoryTheory.ProjectiveResolution.π_f_succ

@[simp]
theorem complex_d_comp_π_f_zero {Z : C} (P : ProjectiveResolution Z) :
    P.complex.d 1 0 ≫ P.π.f 0 = 0 := by
  rw [← HomologicalComplex.Hom.comm, π_f_succ, zero_comp]
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.complex_d_comp_π_f_zero CategoryTheory.ProjectiveResolution.complex_d_comp_π_f_zero

@[simp 1100]
theorem complex_d_succ_comp {Z : C} (P : ProjectiveResolution Z) (n : ℕ) :
    P.complex.d (n + 2) (n + 1) ≫ P.complex.d (n + 1) n = 0 := by simp
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.complex_d_succ_comp CategoryTheory.ProjectiveResolution.complex_d_succ_comp

@[simps!]
def cofork {Z : C} (P : ProjectiveResolution Z) : CokernelCofork (P.complex.d 1 0) :=
  CokernelCofork.ofπ _ P.complex_d_comp_π_f_zero

def isColimitCofork {Z : C} (P : ProjectiveResolution Z) : IsColimit P.cofork := by
  refine' IsColimit.ofIsoColimit (P.complex.opcyclesIsCokernel 1 0 (by simp)) _
  refine' Cofork.ext (P.complex.isoHomologyι₀.symm ≪≫ isoOfQuasiIsoAt P.π 0 ≪≫
    ChainComplex.single₀Homology₀Iso Z) _
  dsimp [cofork]
  rw [ChainComplex.isoHomologyι₀_inv_naturality_assoc]
  simp only [HomologicalComplex.p_opcyclesMap_assoc, ChainComplex.single₀_obj_X_0,
    ← cancel_mono (ChainComplex.single₀Homology₀Iso Z).inv, Category.assoc,
    Iso.hom_inv_id, Category.comp_id,
    ← cancel_mono (((ChainComplex.single₀ C).obj Z).homologyι 0),
    ChainComplex.isoHomologyι₀_inv_hom_id]
  simp only [← cancel_mono (ChainComplex.single₀Opcycles₀Iso Z).hom,
    Category.assoc, ChainComplex.pOpcycles_comp_single₀OpcyclesIso_hom,
    ChainComplex.single₀Homology₀Iso_inv_comp_single₀_homologyι_assoc,
    Category.comp_id, Iso.inv_hom_id, Category.comp_id, ChainComplex.single₀_obj_X_0]

instance {Z : C} (P : ProjectiveResolution Z) (n : ℕ) : CategoryTheory.Epi (P.π.f n) := by
  cases n
  · exact epi_of_isColimit_cofork P.isColimitCofork
  · rw [π_f_succ]; infer_instance

/-- A projective object admits a trivial projective resolution: itself in degree 0. -/
def self (Z : C) [CategoryTheory.Projective Z] : ProjectiveResolution Z where
  complex := (ChainComplex.single₀ C).obj Z
  π := 𝟙 ((ChainComplex.single₀ C).obj Z)
  projective n := by
    cases n
    · dsimp
      infer_instance
    · dsimp
      infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.self CategoryTheory.ProjectiveResolution.self

lemma exact₀ {Z : C} (P : ProjectiveResolution Z) :
    (ShortComplex.mk _ _ P.complex_d_comp_π_f_zero).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ P.isColimitCofork

lemma exact_succ {Z : C} (P : ProjectiveResolution Z) (n : ℕ):
    (ShortComplex.mk _ _ (P.complex.d_comp_d (n+2) (n+1) n)).Exact :=
  (HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp; linarith)
    (by simp)).1 (P.complex_exactAt_succ n)

/-- Auxiliary construction for `lift`. -/
def liftZero {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex.X 0 ⟶ Q.complex.X 0 :=
  factorThru (P.π.f 0 ≫ f) (Q.π.f 0)
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_f_zero CategoryTheory.ProjectiveResolution.liftZero

@[reassoc (attr := simp)]
lemma liftZero_comp
    {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    liftZero f P Q ≫ Q.π.f 0 = P.π.f 0 ≫ f := by
  simp [liftZero]

/-- Auxiliary construction for `lift`. -/
def liftOne {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex.X 1 ⟶ Q.complex.X 1 :=
  ShortComplex.Exact.liftFromProjective Q.exact₀ (P.complex.d 1 0 ≫ liftZero f P Q) (by
    rw [Category.assoc, liftZero_comp, ← HomologicalComplex.Hom.comm_assoc,
      ChainComplex.single₀_obj_X_d, zero_comp, comp_zero])
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_f_one CategoryTheory.ProjectiveResolution.liftOne

/-- Auxiliary lemma for `lift`. -/
@[simp]
theorem liftOne_zero_comm {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y)
    (Q : ProjectiveResolution Z) :
    liftOne f P Q ≫ Q.complex.d 1 0 = P.complex.d 1 0 ≫ liftZero f P Q := by
  apply ShortComplex.Exact.liftFromProjective_comp
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_f_one_zero_comm CategoryTheory.ProjectiveResolution.liftOne_zero_comm

/-- Auxiliary construction for `lift`. -/
def liftSucc {Y Z : C} (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) (n : ℕ)
    (g : P.complex.X n ⟶ Q.complex.X n) (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 1))
    (w : g' ≫ Q.complex.d (n + 1) n = P.complex.d (n + 1) n ≫ g) :
    Σ' g'' : P.complex.X (n + 2) ⟶ Q.complex.X (n + 2),
      g'' ≫ Q.complex.d (n + 2) (n + 1) = P.complex.d (n + 2) (n + 1) ≫ g' :=
  ⟨ShortComplex.Exact.liftFromProjective (Q.exact_succ n)
    (P.complex.d (n + 2) (n + 1) ≫ g') (by simp [w]), by
      apply ShortComplex.Exact.liftFromProjective_comp⟩
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_f_succ CategoryTheory.ProjectiveResolution.liftSucc

/-- A morphism in `C` lifts to a chain map between projective resolutions. -/
def lift {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex ⟶ Q.complex :=
  ChainComplex.mkHom _ _ (liftZero f _ _) (liftOne f _ _) (liftOne_zero_comm f _ _)
    fun n ⟨g, g', w⟩ => liftSucc P Q n g g' w
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift CategoryTheory.ProjectiveResolution.lift

/-- The resolution maps intertwine the lift of a morphism and that morphism. -/
@[reassoc (attr := simp)]
theorem lift_commutes {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y)
    (Q : ProjectiveResolution Z) : lift f P Q ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f := by
  ext; simp [lift, liftZero]
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_commutes CategoryTheory.ProjectiveResolution.lift_commutes

-- Now that we've checked this property of the lift,
-- we can seal away the actual definition.
end ProjectiveResolution

end

namespace ProjectiveResolution

variable [Abelian C]

/-- An auxiliary definition for `liftHomotopyZero`. -/
def liftHomotopyZeroZero {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : P.complex.X 0 ⟶ Q.complex.X 1 :=
  ShortComplex.Exact.liftFromProjective Q.exact₀ (f.f 0)
    (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_homotopy_zero_zero CategoryTheory.ProjectiveResolution.liftHomotopyZeroZero

@[reassoc (attr := simp)]
lemma liftHomotopyZeroZero_comp {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    liftHomotopyZeroZero f comm ≫ Q.complex.d 1 0 = f.f 0 := by
  apply ShortComplex.Exact.liftFromProjective_comp

/-- An auxiliary definition for `liftHomotopyZero`. -/
def liftHomotopyZeroOne {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : P.complex.X 1 ⟶ Q.complex.X 2 :=
  ShortComplex.Exact.liftFromProjective (Q.exact_succ 0)
    (f.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZero f comm) (by
      simp only [Preadditive.sub_comp, HomologicalComplex.Hom.comm,
        Category.assoc]
      erw [liftHomotopyZeroZero_comp]
      rw [sub_self])
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_homotopy_zero_one CategoryTheory.ProjectiveResolution.liftHomotopyZeroOne

@[reassoc (attr := simp)]
lemma liftHomotopyZeroOne_comp {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    liftHomotopyZeroOne f comm ≫ Q.complex.d 2 1 =
      f.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZero f comm := by
  apply ShortComplex.Exact.liftFromProjective_comp

/-- An auxiliary definition for `liftHomotopyZero`. -/
def liftHomotopyZeroSucc {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (n : ℕ) (g : P.complex.X n ⟶ Q.complex.X (n + 1))
    (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 2))
    (w : f.f (n + 1) = P.complex.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
    P.complex.X (n + 2) ⟶ Q.complex.X (n + 3) :=
  ShortComplex.Exact.liftFromProjective (Q.exact_succ (n+1))
    (f.f (n + 2) - P.complex.d (n + 2) (n + 1) ≫ g') (by simp [w])
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_homotopy_zero_succ CategoryTheory.ProjectiveResolution.liftHomotopyZeroSucc

@[reassoc (attr := simp)]
def liftHomotopyZeroSucc_comp {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (n : ℕ) (g : P.complex.X n ⟶ Q.complex.X (n + 1))
    (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 2))
    (w : f.f (n + 1) = P.complex.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
    liftHomotopyZeroSucc f n g g' w ≫ Q.complex.d (n+3) (n+2) =
      f.f (n + 2) - P.complex.d (n + 2) (n + 1) ≫ g' := by
  apply ShortComplex.Exact.liftFromProjective_comp


/-- Any lift of the zero morphism is homotopic to zero. -/
def liftHomotopyZero {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : Homotopy f 0 :=
  Homotopy.mkInductive _ (liftHomotopyZeroZero f comm) (by simp )
    (liftHomotopyZeroOne f comm) (by simp) fun n ⟨g, g', w⟩ =>
    ⟨liftHomotopyZeroSucc f n g g' w, by simp⟩
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_homotopy_zero CategoryTheory.ProjectiveResolution.liftHomotopyZero

/-- Two lifts of the same morphism are homotopic. -/
def liftHomotopy {Y Z : C} (f : Y ⟶ Z) {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (g h : P.complex ⟶ Q.complex) (g_comm : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f)
    (h_comm : h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) : Homotopy g h :=
  Homotopy.equivSubZero.invFun (liftHomotopyZero _ (by simp [g_comm, h_comm]))
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_homotopy CategoryTheory.ProjectiveResolution.liftHomotopy

/-- The lift of the identity morphism is homotopic to the identity chain map. -/
def liftIdHomotopy (X : C) (P : ProjectiveResolution X) : Homotopy (lift (𝟙 X) P P) (𝟙 P.complex) :=
  by apply liftHomotopy (𝟙 X) <;> simp
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_id_homotopy CategoryTheory.ProjectiveResolution.liftIdHomotopy

/-- The lift of a composition is homotopic to the composition of the lifts. -/
def liftCompHomotopy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (P : ProjectiveResolution X)
    (Q : ProjectiveResolution Y) (R : ProjectiveResolution Z) :
    Homotopy (lift (f ≫ g) P R) (lift f P Q ≫ lift g Q R) := by
  apply liftHomotopy (f ≫ g) <;> simp
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.lift_comp_homotopy CategoryTheory.ProjectiveResolution.liftCompHomotopy

-- We don't care about the actual definitions of these homotopies.
/-- Any two projective resolutions are homotopy equivalent. -/
def homotopyEquiv {X : C} (P Q : ProjectiveResolution X) : HomotopyEquiv P.complex Q.complex where
  hom := lift (𝟙 X) P Q
  inv := lift (𝟙 X) Q P
  homotopyHomInvId := by
    refine' (liftCompHomotopy (𝟙 X) (𝟙 X) P Q P).symm.trans _
    simp only [Category.id_comp]
    apply liftIdHomotopy
  homotopyInvHomId := by
    refine' (liftCompHomotopy (𝟙 X) (𝟙 X) Q P Q).symm.trans _
    simp only [Category.id_comp]
    apply liftIdHomotopy
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.homotopy_equiv CategoryTheory.ProjectiveResolution.homotopyEquiv

@[reassoc (attr := simp)]
theorem homotopyEquiv_hom_π {X : C} (P Q : ProjectiveResolution X) :
    (homotopyEquiv P Q).hom ≫ Q.π = P.π := by simp [homotopyEquiv]
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.homotopy_equiv_hom_π CategoryTheory.ProjectiveResolution.homotopyEquiv_hom_π

@[reassoc (attr := simp)]
theorem homotopyEquiv_inv_π {X : C} (P Q : ProjectiveResolution X) :
    (homotopyEquiv P Q).inv ≫ P.π = Q.π := by simp [homotopyEquiv]
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.homotopy_equiv_inv_π CategoryTheory.ProjectiveResolution.homotopyEquiv_inv_π

end ProjectiveResolution

section

variable [Abelian C]

def projectiveResolution (Z : C) [HasProjectiveResolution Z] : ProjectiveResolution Z :=
  HasProjectiveResolution.out.some

-- porting note: this was named `projective_resolution` in mathlib 3. As there was also a need
-- for a definition of `ProjectiveResolution Z` given `(Z : projectiveResolution Z)`, it
-- seemed more consistent to have `projectiveResolution Z : ProjectiveResolution Z`
-- and `projectiveResolution.complex Z : ChainComplex C ℕ`
/-- An arbitrarily chosen projective resolution of an object. -/
abbrev projectiveResolution.complex (Z : C) [HasProjectiveResolution Z] : ChainComplex C ℕ :=
  (projectiveResolution Z).complex
#align category_theory.projective_resolution CategoryTheory.projectiveResolution.complex

/-- The chain map from the arbitrarily chosen projective resolution
`projectiveResolution.complex Z` back to the chain complex consisting
of `Z` supported in degree `0`. -/
abbrev projectiveResolution.π (Z : C) [HasProjectiveResolution Z] :
    projectiveResolution.complex Z ⟶ (ChainComplex.single₀ C).obj Z :=
  (projectiveResolution Z).π
#align category_theory.projective_resolution.π CategoryTheory.projectiveResolution.π

/-- The lift of a morphism to a chain map between the arbitrarily chosen projective resolutions. -/
abbrev projectiveResolution.lift {X Y : C} (f : X ⟶ Y) [HasProjectiveResolution X]
    [HasProjectiveResolution Y] :
    projectiveResolution.complex X ⟶ projectiveResolution.complex Y :=
  ProjectiveResolution.lift f _ _
#align category_theory.projective_resolution.lift CategoryTheory.projectiveResolution.lift

@[reassoc (attr := simp)]
lemma projectiveResolution.lift_comm {X Y : C} (f : X ⟶ Y) [HasProjectiveResolution X]
    [HasProjectiveResolution Y] :
    (projectiveResolution.lift f).f 0 ≫ (projectiveResolution.π Y).f 0 =
      (projectiveResolution.π X).f 0 ≫ f := by
  rw [← HomologicalComplex.comp_f, ProjectiveResolution.lift_commutes,
    HomologicalComplex.comp_f, ChainComplex.single₀_map_f_0]

end

variable (C)
variable [Abelian C] [HasProjectiveResolutions C]

/-- Taking projective resolutions is functorial,
if considered with target the homotopy category
(`ℕ`-indexed chain complexes and chain maps up to homotopy).
-/
def projectiveResolutions : C ⥤ HomotopyCategory C (ComplexShape.down ℕ) where
  obj X := (HomotopyCategory.quotient _ _).obj (projectiveResolution.complex X)
  map f := (HomotopyCategory.quotient _ _).map (projectiveResolution.lift f)
  map_id X := by
    rw [← (HomotopyCategory.quotient _ _).map_id]
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.liftIdHomotopy
  map_comp f g := by
    rw [← (HomotopyCategory.quotient _ _).map_comp]
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.liftCompHomotopy
#align category_theory.projective_resolutions CategoryTheory.projectiveResolutions

variable {C}

def ProjectiveResolution.iso {X : C} (P : ProjectiveResolution X) :
    (projectiveResolutions C).obj X ≅
      (HomotopyCategory.quotient _ _).obj P.complex :=
  HomotopyCategory.isoOfHomotopyEquiv (homotopyEquiv _ _)

@[reassoc]
lemma ProjectiveResolution.iso_inv_naturality {X Y : C} (f : X ⟶ Y)
    (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f) :
    P.iso.inv ≫ (projectiveResolutions C).map f =
      (HomotopyCategory.quotient _ _).map φ ≫ Q.iso.inv  := by
  apply HomotopyCategory.eq_of_homotopy
  apply liftHomotopy f
  all_goals aesop_cat

@[reassoc]
lemma ProjectiveResolution.iso_hom_naturality {X Y : C} (f : X ⟶ Y)
    (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f) :
    (projectiveResolutions C).map f ≫ Q.iso.hom =
      P.iso.hom ≫ (HomotopyCategory.quotient _ _).map φ := by
  rw [← cancel_epi P.iso.inv,
    ProjectiveResolution.iso_inv_naturality_assoc f P Q φ comm,
    Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

end CategoryTheory
