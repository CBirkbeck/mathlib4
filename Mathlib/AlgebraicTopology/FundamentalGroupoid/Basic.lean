/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import Mathlib.CategoryTheory.Category.Grpd
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Path

#align_import algebraic_topology.fundamental_groupoid.basic from "leanprover-community/mathlib"@"3d7987cda72abc473c7cdbbb075170e9ac620042"

/-!
# Fundamental groupoid of a space

Given a topological space `X`, we can define the fundamental groupoid of `X` to be the category with
objects being points of `X`, and morphisms `x ⟶ y` being paths from `x` to `y`, quotiented by
homotopy equivalence. With this, the fundamental group of `X` based at `x` is just the automorphism
group of `x`.
-/

open CategoryTheory

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

variable {x₀ x₁ : X}

noncomputable section

open unitInterval

namespace Path

namespace Homotopy

section

/-- Auxiliary function for `reflTransSymm`. -/
def reflTransSymmAux (x : I × I) : ℝ :=
  if (x.2 : ℝ) ≤ 1 / 2 then x.1 * 2 * x.2 else x.1 * (2 - 2 * x.2)
#align path.homotopy.refl_trans_symm_aux Path.Homotopy.reflTransSymmAux

@[continuity]
theorem continuous_reflTransSymmAux : Continuous reflTransSymmAux := by
  refine' continuous_if_le _ _ (Continuous.continuousOn _) (Continuous.continuousOn _) _
  · continuity
    -- 🎉 no goals
  · continuity
    -- 🎉 no goals
  · continuity
    -- 🎉 no goals
  · continuity
    -- 🎉 no goals
  intro x hx
  -- ⊢ ↑x.fst * 2 * ↑x.snd = ↑x.fst * (2 - 2 * ↑x.snd)
  norm_num [hx, mul_assoc]
  -- 🎉 no goals
#align path.homotopy.continuous_refl_trans_symm_aux Path.Homotopy.continuous_reflTransSymmAux

theorem reflTransSymmAux_mem_I (x : I × I) : reflTransSymmAux x ∈ I := by
  dsimp only [reflTransSymmAux]
  -- ⊢ (if ↑x.snd ≤ 1 / 2 then ↑x.fst * 2 * ↑x.snd else ↑x.fst * (2 - 2 * ↑x.snd))  …
  split_ifs
  -- ⊢ ↑x.fst * 2 * ↑x.snd ∈ I
  · constructor
    -- ⊢ 0 ≤ ↑x.fst * 2 * ↑x.snd
    · apply mul_nonneg
      -- ⊢ 0 ≤ ↑x.fst * 2
      · apply mul_nonneg
        -- ⊢ 0 ≤ ↑x.fst
        · unit_interval
          -- 🎉 no goals
        · norm_num
          -- 🎉 no goals
      · unit_interval
        -- 🎉 no goals
    · rw [mul_assoc]
      -- ⊢ ↑x.fst * (2 * ↑x.snd) ≤ 1
      apply mul_le_one
      · unit_interval
        -- 🎉 no goals
      · apply mul_nonneg
        -- ⊢ 0 ≤ 2
        · norm_num
          -- 🎉 no goals
        · unit_interval
          -- 🎉 no goals
      · linarith
        -- 🎉 no goals
  · constructor
    -- ⊢ 0 ≤ ↑x.fst * (2 - 2 * ↑x.snd)
    · apply mul_nonneg
      -- ⊢ 0 ≤ ↑x.fst
      · unit_interval
        -- 🎉 no goals
      linarith [unitInterval.nonneg x.2, unitInterval.le_one x.2]
      -- 🎉 no goals
    · apply mul_le_one
      · unit_interval
        -- 🎉 no goals
      · linarith [unitInterval.nonneg x.2, unitInterval.le_one x.2]
        -- 🎉 no goals
      · linarith [unitInterval.nonneg x.2, unitInterval.le_one x.2]
        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align path.homotopy.refl_trans_symm_aux_mem_I Path.Homotopy.reflTransSymmAux_mem_I

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from the constant path based at `x₀` to
  `p.trans p.symm`. -/
def reflTransSymm (p : Path x₀ x₁) : Homotopy (Path.refl x₀) (p.trans p.symm) where
  toFun x := p ⟨reflTransSymmAux x, reflTransSymmAux_mem_I x⟩
  continuous_toFun := by continuity
                         -- 🎉 no goals
  map_zero_left := by simp [reflTransSymmAux]
                      -- 🎉 no goals
  map_one_left x := by
    dsimp only [reflTransSymmAux, Path.coe_toContinuousMap, Path.trans]
    -- ⊢ ↑p { val := if ↑x ≤ 1 / 2 then ↑1 * 2 * ↑x else ↑1 * (2 - 2 * ↑x), property  …
    change _ = ite _ _ _
    -- ⊢ ↑p { val := if ↑x ≤ 1 / 2 then ↑1 * 2 * ↑x else ↑1 * (2 - 2 * ↑x), property  …
    split_ifs with h
    -- ⊢ ↑p { val := ↑1 * 2 * ↑x, property := (_ : (fun x => x ∈ I) (↑1 * 2 * ↑x)) }  …
    · rw [Path.extend, Set.IccExtend_of_mem]
      -- ⊢ ↑p { val := ↑1 * 2 * ↑x, property := (_ : (fun x => x ∈ I) (↑1 * 2 * ↑x)) }  …
      · norm_num
        -- 🎉 no goals
      · rw [unitInterval.mul_pos_mem_iff zero_lt_two]
        -- ⊢ ↑x ∈ Set.Icc 0 (1 / 2)
        exact ⟨unitInterval.nonneg x, h⟩
        -- 🎉 no goals
    · rw [Path.symm, Path.extend, Set.IccExtend_of_mem]
      -- ⊢ ↑p { val := ↑1 * (2 - 2 * ↑x), property := (_ : (fun x => x ∈ I) (↑1 * (2 -  …
      · simp only [Set.Icc.coe_one, one_mul, coe_mk_mk, Function.comp_apply]
        -- ⊢ ↑p { val := 2 - 2 * ↑x, property := (_ : (fun x => x ∈ I) (2 - 2 * ↑x)) } =  …
        congr 1
        -- ⊢ { val := 2 - 2 * ↑x, property := (_ : (fun x => x ∈ I) (2 - 2 * ↑x)) } = σ { …
        ext
        -- ⊢ ↑{ val := 2 - 2 * ↑x, property := (_ : (fun x => x ∈ I) (2 - 2 * ↑x)) } = ↑( …
        norm_num [sub_sub_eq_add_sub]
        -- 🎉 no goals
      · rw [unitInterval.two_mul_sub_one_mem_iff]
        -- ⊢ ↑x ∈ Set.Icc (1 / 2) 1
        exact ⟨(not_le.1 h).le, unitInterval.le_one x⟩
        -- 🎉 no goals
  prop' t x hx := by
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff] at hx
    -- ⊢ ↑(ContinuousMap.mk fun x => ContinuousMap.toFun { toContinuousMap := Continu …
    simp only [ContinuousMap.coe_mk, coe_toContinuousMap, Path.refl_apply]
    -- ⊢ ↑p { val := reflTransSymmAux (t, x), property := (_ : reflTransSymmAux (t, x …
    cases hx with
    | inl hx
    | inr hx =>
      rw [hx]
      norm_num [reflTransSymmAux]
#align path.homotopy.refl_trans_symm Path.Homotopy.reflTransSymm

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from the constant path based at `x₁` to
  `p.symm.trans p`. -/
def reflSymmTrans (p : Path x₀ x₁) : Homotopy (Path.refl x₁) (p.symm.trans p) :=
  (reflTransSymm p.symm).cast rfl <| congr_arg _ Path.symm_symm
#align path.homotopy.refl_symm_trans Path.Homotopy.reflSymmTrans

end

section TransRefl

/-- Auxiliary function for `trans_refl_reparam`. -/
def transReflReparamAux (t : I) : ℝ :=
  if (t : ℝ) ≤ 1 / 2 then 2 * t else 1
#align path.homotopy.trans_refl_reparam_aux Path.Homotopy.transReflReparamAux

@[continuity]
theorem continuous_transReflReparamAux : Continuous transReflReparamAux := by
  refine' continuous_if_le _ _ (Continuous.continuousOn _) (Continuous.continuousOn _) _ <;>
    [continuity; continuity; continuity; continuity; skip]
  intro x hx
  -- ⊢ 2 * ↑x = 1
  simp [hx]
  -- 🎉 no goals
#align path.homotopy.continuous_trans_refl_reparam_aux Path.Homotopy.continuous_transReflReparamAux

theorem transReflReparamAux_mem_I (t : I) : transReflReparamAux t ∈ I := by
  unfold transReflReparamAux
  -- ⊢ (if ↑t ≤ 1 / 2 then 2 * ↑t else 1) ∈ I
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]
  -- ⊢ 2 * ↑t ∈ I
                -- ⊢ 0 ≤ 2 * ↑t
                -- ⊢ 0 ≤ 1
                                -- 🎉 no goals
                                -- 🎉 no goals
                                -- 🎉 no goals
                                -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align path.homotopy.trans_refl_reparam_aux_mem_I Path.Homotopy.transReflReparamAux_mem_I

theorem transReflReparamAux_zero : transReflReparamAux 0 = 0 := by
  norm_num [transReflReparamAux]
  -- 🎉 no goals
#align path.homotopy.trans_refl_reparam_aux_zero Path.Homotopy.transReflReparamAux_zero

theorem transReflReparamAux_one : transReflReparamAux 1 = 1 := by
  norm_num [transReflReparamAux]
  -- 🎉 no goals
#align path.homotopy.trans_refl_reparam_aux_one Path.Homotopy.transReflReparamAux_one

theorem trans_refl_reparam (p : Path x₀ x₁) :
    p.trans (Path.refl x₁) =
      p.reparam (fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩) (by continuity)
                                                                                    -- 🎉 no goals
        (Subtype.ext transReflReparamAux_zero) (Subtype.ext transReflReparamAux_one) := by
  ext
  -- ⊢ ↑(Path.trans p (Path.refl x₁)) x✝ = ↑(Path.reparam p (fun t => { val := tran …
  unfold transReflReparamAux
  -- ⊢ ↑(Path.trans p (Path.refl x₁)) x✝ = ↑(Path.reparam p (fun t => { val := if ↑ …
  simp only [Path.trans_apply, not_le, coe_reparam, Function.comp_apply, one_div, Path.refl_apply]
  -- ⊢ (if h : ↑x✝ ≤ 2⁻¹ then ↑p { val := 2 * ↑x✝, property := (_ : 2 * ↑x✝ ∈ I) }  …
  split_ifs
  · rfl
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align path.homotopy.trans_refl_reparam Path.Homotopy.trans_refl_reparam

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from `p.trans (Path.refl x₁)` to `p`. -/
def transRefl (p : Path x₀ x₁) : Homotopy (p.trans (Path.refl x₁)) p :=
  ((Homotopy.reparam p (fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩)
          (by continuity) (Subtype.ext transReflReparamAux_zero)
              -- 🎉 no goals
          (Subtype.ext transReflReparamAux_one)).cast
      rfl (trans_refl_reparam p).symm).symm
#align path.homotopy.trans_refl Path.Homotopy.transRefl

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from `(Path.refl x₀).trans p` to `p`. -/
def reflTrans (p : Path x₀ x₁) : Homotopy ((Path.refl x₀).trans p) p :=
  (transRefl p.symm).symm₂.cast (by simp) (by simp)
                                    -- 🎉 no goals
                                              -- 🎉 no goals
#align path.homotopy.refl_trans Path.Homotopy.reflTrans

end TransRefl

section Assoc

/-- Auxiliary function for `trans_assoc_reparam`. -/
def transAssocReparamAux (t : I) : ℝ :=
  if (t : ℝ) ≤ 1 / 4 then 2 * t else if (t : ℝ) ≤ 1 / 2 then t + 1 / 4 else 1 / 2 * (t + 1)
#align path.homotopy.trans_assoc_reparam_aux Path.Homotopy.transAssocReparamAux

@[continuity]
theorem continuous_transAssocReparamAux : Continuous transAssocReparamAux := by
  refine' continuous_if_le _ _ (Continuous.continuousOn _)
      (continuous_if_le _ _ (Continuous.continuousOn _) (Continuous.continuousOn _) _).continuousOn
      _ <;>
    [continuity; continuity; continuity; continuity; continuity; continuity; continuity; skip;
      skip] <;>
    · intro x hx
      -- ⊢ ↑x + 1 / 4 = 1 / 2 * (↑x + 1)
      -- ⊢ 2 * ↑x = if ↑x ≤ 1 / 2 then ↑x + 1 / 4 else 1 / 2 * (↑x + 1)
      -- 🎉 no goals
      norm_num [hx]
      -- 🎉 no goals
#align path.homotopy.continuous_trans_assoc_reparam_aux Path.Homotopy.continuous_transAssocReparamAux

theorem transAssocReparamAux_mem_I (t : I) : transAssocReparamAux t ∈ I := by
  unfold transAssocReparamAux
  -- ⊢ (if ↑t ≤ 1 / 4 then 2 * ↑t else if ↑t ≤ 1 / 2 then ↑t + 1 / 4 else 1 / 2 * ( …
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]
                -- ⊢ 0 ≤ 2 * ↑t
                -- ⊢ 0 ≤ ↑t + 1 / 4
                -- ⊢ 0 ≤ 1 / 2 * (↑t + 1)
                                -- 🎉 no goals
                                -- 🎉 no goals
                                -- 🎉 no goals
                                -- 🎉 no goals
                                -- 🎉 no goals
                                -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align path.homotopy.trans_assoc_reparam_aux_mem_I Path.Homotopy.transAssocReparamAux_mem_I

theorem transAssocReparamAux_zero : transAssocReparamAux 0 = 0 := by
  norm_num [transAssocReparamAux]
  -- 🎉 no goals
#align path.homotopy.trans_assoc_reparam_aux_zero Path.Homotopy.transAssocReparamAux_zero

theorem transAssocReparamAux_one : transAssocReparamAux 1 = 1 := by
  norm_num [transAssocReparamAux]
  -- 🎉 no goals
#align path.homotopy.trans_assoc_reparam_aux_one Path.Homotopy.transAssocReparamAux_one

theorem trans_assoc_reparam {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    (p.trans q).trans r =
      (p.trans (q.trans r)).reparam
        (fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩) (by continuity)
                                                                              -- 🎉 no goals
        (Subtype.ext transAssocReparamAux_zero) (Subtype.ext transAssocReparamAux_one) := by
  ext x
  -- ⊢ ↑(Path.trans (Path.trans p q) r) x = ↑(Path.reparam (Path.trans p (Path.tran …
  simp only [transAssocReparamAux, Path.trans_apply, mul_inv_cancel_left₀, not_le,
    Function.comp_apply, Ne.def, not_false_iff, bit0_eq_zero, one_ne_zero, mul_ite, Subtype.coe_mk,
    Path.coe_reparam]
  -- TODO: why does split_ifs not reduce the ifs??????
  split_ifs with h₁ h₂ h₃ h₄ h₅
  · rfl
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    linarith
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    linarith
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    linarith
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    linarith
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    linarith
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    linarith
    -- 🎉 no goals
  · have h : 2 * (2 * (x : ℝ)) - 1 = 2 * (2 * (↑x + 1 / 4) - 1) := by linarith
    -- ⊢ ↑q { val := 2 * (2 * ↑x) - 1, property := (_ : 2 * ↑{ val := 2 * ↑x, propert …
    simp [h₂, h₁, h, dif_neg (show ¬False from id), dif_pos True.intro, if_false, if_true]
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    linarith
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    linarith
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    linarith
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    linarith
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    linarith
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    linarith
    -- 🎉 no goals
  · congr
    -- ⊢ ↑x = 2 * (1 / 2 * (↑x + 1)) - 1
    ring
    -- 🎉 no goals
#align path.homotopy.trans_assoc_reparam Path.Homotopy.trans_assoc_reparam

/-- For paths `p q r`, we have a homotopy from `(p.trans q).trans r` to `p.trans (q.trans r)`. -/
def transAssoc {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    Homotopy ((p.trans q).trans r) (p.trans (q.trans r)) :=
  ((Homotopy.reparam (p.trans (q.trans r))
          (fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩) (by continuity)
                                                                                -- 🎉 no goals
          (Subtype.ext transAssocReparamAux_zero) (Subtype.ext transAssocReparamAux_one)).cast
      rfl (trans_assoc_reparam p q r).symm).symm
#align path.homotopy.trans_assoc Path.Homotopy.transAssoc

end Assoc

end Homotopy

end Path

/-- The fundamental groupoid of a space `X` is defined to be a type synonym for `X`, and we
subsequently put a `CategoryTheory.Groupoid` structure on it. -/
def FundamentalGroupoid (X : Type u) := X
#align fundamental_groupoid FundamentalGroupoid

namespace FundamentalGroupoid

instance {X : Type u} [h : Inhabited X] : Inhabited (FundamentalGroupoid X) := h

attribute [reducible] FundamentalGroupoid

attribute [local instance] Path.Homotopic.setoid

instance : CategoryTheory.Groupoid (FundamentalGroupoid X) where
  Hom x y := Path.Homotopic.Quotient x y
  id x := ⟦Path.refl x⟧
  comp {x y z} := Path.Homotopic.Quotient.comp
  id_comp {x y} f :=
    Quotient.inductionOn f fun a =>
      show ⟦(Path.refl x).trans a⟧ = ⟦a⟧ from Quotient.sound ⟨Path.Homotopy.reflTrans a⟩
  comp_id {x y} f :=
    Quotient.inductionOn f fun a =>
      show ⟦a.trans (Path.refl y)⟧ = ⟦a⟧ from Quotient.sound ⟨Path.Homotopy.transRefl a⟩
  assoc {w x y z} f g h :=
    Quotient.inductionOn₃ f g h fun p q r =>
      show ⟦(p.trans q).trans r⟧ = ⟦p.trans (q.trans r)⟧ from
        Quotient.sound ⟨Path.Homotopy.transAssoc p q r⟩
  inv {x y} p :=
    Quotient.lift (fun l : Path x y => ⟦l.symm⟧)
      (by
        rintro a b ⟨h⟩
        -- ⊢ (fun l => Quotient.mk (Path.Homotopic.setoid y x) (Path.symm l)) a = (fun l  …
        simp only
        -- ⊢ Quotient.mk (Path.Homotopic.setoid y x) (Path.symm a) = Quotient.mk (Path.Ho …
        rw [Quotient.eq]
        -- ⊢ Path.symm a ≈ Path.symm b
        exact ⟨h.symm₂⟩)
        -- 🎉 no goals
      p
  inv_comp {x y} f :=
    Quotient.inductionOn f fun a =>
      show ⟦a.symm.trans a⟧ = ⟦Path.refl y⟧ from
        Quotient.sound ⟨(Path.Homotopy.reflSymmTrans a).symm⟩
  comp_inv {x y} f :=
    Quotient.inductionOn f fun a =>
      show ⟦a.trans a.symm⟧ = ⟦Path.refl x⟧ from
        Quotient.sound ⟨(Path.Homotopy.reflTransSymm a).symm⟩

theorem comp_eq (x y z : FundamentalGroupoid X) (p : x ⟶ y) (q : y ⟶ z) : p ≫ q = p.comp q := rfl
#align fundamental_groupoid.comp_eq FundamentalGroupoid.comp_eq

theorem id_eq_path_refl (x : FundamentalGroupoid X) : 𝟙 x = ⟦Path.refl x⟧ := rfl
#align fundamental_groupoid.id_eq_path_refl FundamentalGroupoid.id_eq_path_refl

/-- The functor sending a topological space `X` to its fundamental groupoid. -/
def fundamentalGroupoidFunctor : TopCat ⥤ CategoryTheory.Grpd where
  obj X := { α := FundamentalGroupoid X }
  map f :=
    { obj := f
      map := fun {X Y} p => by exact Path.Homotopic.Quotient.mapFn p f
                               -- 🎉 no goals
      map_id := fun X => rfl
      map_comp := fun {x y z} p q => by
        refine' Quotient.inductionOn₂ p q fun a b => _
        -- ⊢ { obj := ↑f, map := fun {X Y} p => Path.Homotopic.Quotient.mapFn p f }.map ( …
        simp only [comp_eq, ← Path.Homotopic.map_lift, ← Path.Homotopic.comp_lift, Path.map_trans] }
        -- 🎉 no goals
  map_id X := by
    simp only
    -- ⊢ CategoryTheory.Functor.mk { obj := ↑(𝟙 X), map := fun {X_1 Y} p => Path.Homo …
    change _ = (⟨_, _, _⟩ : FundamentalGroupoid X ⥤ FundamentalGroupoid X)
    -- ⊢ CategoryTheory.Functor.mk { obj := ↑(𝟙 X), map := fun {X_1 Y} p => Path.Homo …
    congr
    -- ⊢ (fun {X_1 Y} p => Path.Homotopic.Quotient.mapFn p (𝟙 X)) = fun {X_1 Y} f => f
    ext x y p
    -- ⊢ Path.Homotopic.Quotient.mapFn p (𝟙 X) = p
    refine' Quotient.inductionOn p fun q => _
    -- ⊢ Path.Homotopic.Quotient.mapFn (Quotient.mk (Path.Homotopic.setoid x y) q) (𝟙 …
    rw [← Path.Homotopic.map_lift]
    -- ⊢ Quotient.mk (Path.Homotopic.setoid (↑(𝟙 X) x) (↑(𝟙 X) y)) (Path.map q (_ : C …
    conv_rhs => rw [← q.map_id]
    -- 🎉 no goals
  map_comp f g := by
    simp only
    -- ⊢ CategoryTheory.Functor.mk { obj := ↑(f ≫ g), map := fun {X Y} p => Path.Homo …
    congr
    -- ⊢ (fun {X Y} p => Path.Homotopic.Quotient.mapFn p (f ≫ g)) = fun {X Y} f_1 =>  …
    ext x y p
    -- ⊢ Path.Homotopic.Quotient.mapFn p (f ≫ g) = (CategoryTheory.Functor.mk { obj : …
    refine' Quotient.inductionOn p fun q => _
    -- ⊢ Path.Homotopic.Quotient.mapFn (Quotient.mk (Path.Homotopic.setoid x y) q) (f …
    simp only [Quotient.map_mk, Path.map_map, Quotient.eq']
    -- ⊢ Path.Homotopic.Quotient.mapFn (Quotient.mk (Path.Homotopic.setoid x y) q) (f …
    rfl
    -- 🎉 no goals
#align fundamental_groupoid.fundamental_groupoid_functor FundamentalGroupoid.fundamentalGroupoidFunctor

scoped notation "π" => FundamentalGroupoid.fundamentalGroupoidFunctor
scoped notation "πₓ" => FundamentalGroupoid.fundamentalGroupoidFunctor.obj
scoped notation "πₘ" => FundamentalGroupoid.fundamentalGroupoidFunctor.map

theorem map_eq {X Y : TopCat} {x₀ x₁ : X} (f : C(X, Y)) (p : Path.Homotopic.Quotient x₀ x₁) :
    (πₘ f).map p = p.mapFn f := rfl
#align fundamental_groupoid.map_eq FundamentalGroupoid.map_eq

/-- Help the typechecker by converting a point in a groupoid back to a point in
the underlying topological space. -/
@[reducible]
def toTop {X : TopCat} (x : πₓ X) : X := x
#align fundamental_groupoid.to_top FundamentalGroupoid.toTop

/-- Help the typechecker by converting a point in a topological space to a
point in the fundamental groupoid of that space. -/
@[reducible]
def fromTop {X : TopCat} (x : X) : πₓ X := x
#align fundamental_groupoid.from_top FundamentalGroupoid.fromTop

/-- Help the typechecker by converting an arrow in the fundamental groupoid of
a topological space back to a path in that space (i.e., `Path.Homotopic.Quotient`). -/
-- Porting note: Added `(X := X)` to the type.
@[reducible]
def toPath {X : TopCat} {x₀ x₁ : πₓ X} (p : x₀ ⟶ x₁) : Path.Homotopic.Quotient (X := X) x₀ x₁ := p
#align fundamental_groupoid.to_path FundamentalGroupoid.toPath

/-- Help the typechecker by converting a path in a topological space to an arrow in the
fundamental groupoid of that space. -/
@[reducible]
def fromPath {X : TopCat} {x₀ x₁ : X} (p : Path.Homotopic.Quotient x₀ x₁) : x₀ ⟶ x₁ := p
#align fundamental_groupoid.from_path FundamentalGroupoid.fromPath

end FundamentalGroupoid
