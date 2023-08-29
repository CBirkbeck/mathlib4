/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Winston Yin
-/
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Topology.MetricSpace.Contracting

#align_import analysis.ODE.picard_lindelof from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Picard-Lindelöf (Cauchy-Lipschitz) Theorem

In this file we prove that an ordinary differential equation $\dot x=v(t, x)$ such that $v$ is
Lipschitz continuous in $x$ and continuous in $t$ has a local solution, see
`IsPicardLindelof.exists_forall_hasDerivWithinAt_Icc_eq`.

As a corollary, we prove that a time-independent locally continuously differentiable ODE has a
local solution.

## Implementation notes

In order to split the proof into small lemmas, we introduce a structure `PicardLindelof` that holds
all assumptions of the main theorem. This structure and lemmas in the `PicardLindelof` namespace
should be treated as private implementation details. This is not to be confused with the `Prop`-
valued structure `IsPicardLindelof`, which holds the long hypotheses of the Picard-Lindelöf
theorem for actual use as part of the public API.

We only prove existence of a solution in this file. For uniqueness see `ODE_solution_unique` and
related theorems in `Mathlib/Analysis/ODE/Gronwall.lean`.

## Tags

differential equation
-/

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

open Filter Function Set Metric TopologicalSpace intervalIntegral MeasureTheory
open MeasureTheory.MeasureSpace (volume)
open scoped Filter Topology NNReal ENNReal Nat Interval

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `Prop` structure holding the hypotheses of the Picard-Lindelöf theorem.

The similarly named `PicardLindelof` structure is part of the internal API for convenience, so as
not to constantly invoke choice, but is not intended for public use. -/
structure IsPicardLindelof {E : Type*} [NormedAddCommGroup E] (v : ℝ → E → E) (tMin t₀ tMax : ℝ)
    (x₀ : E) (L : ℝ≥0) (R C : ℝ) : Prop where
  ht₀ : t₀ ∈ Icc tMin tMax
  hR : 0 ≤ R
  lipschitz : ∀ t ∈ Icc tMin tMax, LipschitzOnWith L (v t) (closedBall x₀ R)
  cont : ∀ x ∈ closedBall x₀ R, ContinuousOn (fun t : ℝ => v t x) (Icc tMin tMax)
  norm_le : ∀ t ∈ Icc tMin tMax, ∀ x ∈ closedBall x₀ R, ‖v t x‖ ≤ C
  C_mul_le_R : (C : ℝ) * max (tMax - t₀) (t₀ - tMin) ≤ R
#align is_picard_lindelof IsPicardLindelof

/-- This structure holds arguments of the Picard-Lipschitz (Cauchy-Lipschitz) theorem. It is part of
the internal API for convenience, so as not to constantly invoke choice. Unless you want to use one
of the auxiliary lemmas, use `IsPicardLindelof.exists_forall_hasDerivWithinAt_Icc_eq` instead
of using this structure.

The similarly named `IsPicardLindelof` is a bundled `Prop` holding the long hypotheses of the
Picard-Lindelöf theorem as named arguments. It is used as part of the public API.
-/
structure PicardLindelof (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E → E
  (tMin tMax : ℝ)
  t₀ : Icc tMin tMax
  x₀ : E
  (C R L : ℝ≥0)
  isPicardLindelof : IsPicardLindelof toFun tMin t₀ tMax x₀ L R C
#align picard_lindelof PicardLindelof

namespace PicardLindelof

variable (v : PicardLindelof E)

instance : CoeFun (PicardLindelof E) fun _ => ℝ → E → E :=
  ⟨toFun⟩

instance : Inhabited (PicardLindelof E) :=
  ⟨⟨0, 0, 0, ⟨0, le_rfl, le_rfl⟩, 0, 0, 0, 0,
      { ht₀ := by rw [Subtype.coe_mk, Icc_self]; exact mem_singleton _
                  -- ⊢ 0 ∈ {0}
                                                 -- 🎉 no goals
        hR := le_rfl
        lipschitz := fun t _ => (LipschitzWith.const 0).lipschitzOnWith _
        cont := fun _ _ => by simpa only [Pi.zero_apply] using continuousOn_const
                              -- 🎉 no goals
        norm_le := fun t _ x _ => norm_zero.le
        C_mul_le_R := (zero_mul _).le }⟩⟩

theorem tMin_le_tMax : v.tMin ≤ v.tMax :=
  v.t₀.2.1.trans v.t₀.2.2
#align picard_lindelof.t_min_le_t_max PicardLindelof.tMin_le_tMax

protected theorem nonempty_Icc : (Icc v.tMin v.tMax).Nonempty :=
  nonempty_Icc.2 v.tMin_le_tMax
#align picard_lindelof.nonempty_Icc PicardLindelof.nonempty_Icc

protected theorem lipschitzOnWith {t} (ht : t ∈ Icc v.tMin v.tMax) :
    LipschitzOnWith v.L (v t) (closedBall v.x₀ v.R) :=
  v.isPicardLindelof.lipschitz t ht
#align picard_lindelof.lipschitz_on_with PicardLindelof.lipschitzOnWith

protected theorem continuousOn :
    ContinuousOn (uncurry v) (Icc v.tMin v.tMax ×ˢ closedBall v.x₀ v.R) :=
  have : ContinuousOn (uncurry (flip v)) (closedBall v.x₀ v.R ×ˢ Icc v.tMin v.tMax) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith _ v.L v.isPicardLindelof.cont
      v.isPicardLindelof.lipschitz
  this.comp continuous_swap.continuousOn (preimage_swap_prod _ _).symm.subset
#align picard_lindelof.continuous_on PicardLindelof.continuousOn

theorem norm_le {t : ℝ} (ht : t ∈ Icc v.tMin v.tMax) {x : E} (hx : x ∈ closedBall v.x₀ v.R) :
    ‖v t x‖ ≤ v.C :=
  v.isPicardLindelof.norm_le _ ht _ hx
#align picard_lindelof.norm_le PicardLindelof.norm_le

/-- The maximum of distances from `t₀` to the endpoints of `[tMin, tMax]`. -/
def tDist : ℝ :=
  max (v.tMax - v.t₀) (v.t₀ - v.tMin)
#align picard_lindelof.t_dist PicardLindelof.tDist

theorem tDist_nonneg : 0 ≤ v.tDist :=
  le_max_iff.2 <| Or.inl <| sub_nonneg.2 v.t₀.2.2
#align picard_lindelof.t_dist_nonneg PicardLindelof.tDist_nonneg

theorem dist_t₀_le (t : Icc v.tMin v.tMax) : dist t v.t₀ ≤ v.tDist := by
  rw [Subtype.dist_eq, Real.dist_eq]
  -- ⊢ |↑t - ↑v.t₀| ≤ tDist v
  cases' le_total t v.t₀ with ht ht
  -- ⊢ |↑t - ↑v.t₀| ≤ tDist v
  · rw [abs_of_nonpos (sub_nonpos.2 <| Subtype.coe_le_coe.2 ht), neg_sub]
    -- ⊢ ↑v.t₀ - ↑t ≤ tDist v
    exact (sub_le_sub_left t.2.1 _).trans (le_max_right _ _)
    -- 🎉 no goals
  · rw [abs_of_nonneg (sub_nonneg.2 <| Subtype.coe_le_coe.2 ht)]
    -- ⊢ ↑t - ↑v.t₀ ≤ tDist v
    exact (sub_le_sub_right t.2.2 _).trans (le_max_left _ _)
    -- 🎉 no goals
#align picard_lindelof.dist_t₀_le PicardLindelof.dist_t₀_le

/-- Projection $ℝ → [t_{\min}, t_{\max}]$ sending $(-∞, t_{\min}]$ to $t_{\min}$ and $[t_{\max}, ∞)$
to $t_{\max}$. -/
def proj : ℝ → Icc v.tMin v.tMax :=
  projIcc v.tMin v.tMax v.tMin_le_tMax
#align picard_lindelof.proj PicardLindelof.proj

theorem proj_coe (t : Icc v.tMin v.tMax) : v.proj t = t :=
  projIcc_val _ _
#align picard_lindelof.proj_coe PicardLindelof.proj_coe

theorem proj_of_mem {t : ℝ} (ht : t ∈ Icc v.tMin v.tMax) : ↑(v.proj t) = t := by
  simp only [proj, projIcc_of_mem v.tMin_le_tMax ht]
  -- 🎉 no goals
#align picard_lindelof.proj_of_mem PicardLindelof.proj_of_mem

@[continuity]
theorem continuous_proj : Continuous v.proj :=
  continuous_projIcc
#align picard_lindelof.continuous_proj PicardLindelof.continuous_proj

/-- The space of curves $γ \colon [t_{\min}, t_{\max}] \to E$ such that $γ(t₀) = x₀$ and $γ$ is
Lipschitz continuous with constant $C$. The map sending $γ$ to
$\mathbf Pγ(t)=x₀ + ∫_{t₀}^{t} v(τ, γ(τ))\,dτ$ is a contracting map on this space, and its fixed
point is a solution of the ODE $\dot x=v(t, x)$. -/
structure FunSpace where
  toFun : Icc v.tMin v.tMax → E
  map_t₀' : toFun v.t₀ = v.x₀
  lipschitz' : LipschitzWith v.C toFun
#align picard_lindelof.fun_space PicardLindelof.FunSpace

namespace FunSpace

variable {v} (f : FunSpace v)

instance : CoeFun (FunSpace v) fun _ => Icc v.tMin v.tMax → E :=
  ⟨toFun⟩

instance : Inhabited v.FunSpace :=
  ⟨⟨fun _ => v.x₀, rfl, (LipschitzWith.const _).weaken (zero_le _)⟩⟩

protected theorem lipschitz : LipschitzWith v.C f :=
  f.lipschitz'
#align picard_lindelof.fun_space.lipschitz PicardLindelof.FunSpace.lipschitz

protected theorem continuous : Continuous f :=
  f.lipschitz.continuous
#align picard_lindelof.fun_space.continuous PicardLindelof.FunSpace.continuous

/-- Each curve in `PicardLindelof.FunSpace` is continuous. -/
def toContinuousMap : v.FunSpace ↪ C(Icc v.tMin v.tMax, E) :=
  ⟨fun f => ⟨f, f.continuous⟩, fun f g h => by cases f; cases g; simpa using h⟩
                                               -- ⊢ { toFun := toFun✝, map_t₀' := map_t₀'✝, lipschitz' := lipschitz'✝ } = g
                                                        -- ⊢ { toFun := toFun✝¹, map_t₀' := map_t₀'✝¹, lipschitz' := lipschitz'✝¹ } = { t …
                                                                 -- 🎉 no goals
#align picard_lindelof.fun_space.to_continuous_map PicardLindelof.FunSpace.toContinuousMap

instance : MetricSpace v.FunSpace :=
  MetricSpace.induced toContinuousMap toContinuousMap.injective inferInstance

theorem uniformInducing_toContinuousMap : UniformInducing (@toContinuousMap _ _ _ v) :=
  ⟨rfl⟩
#align picard_lindelof.fun_space.uniform_inducing_to_continuous_map PicardLindelof.FunSpace.uniformInducing_toContinuousMap

theorem range_toContinuousMap :
    range toContinuousMap =
      {f : C(Icc v.tMin v.tMax, E) | f v.t₀ = v.x₀ ∧ LipschitzWith v.C f} := by
  ext f; constructor
  -- ⊢ f ∈ range ↑toContinuousMap ↔ f ∈ {f | ↑f v.t₀ = v.x₀ ∧ LipschitzWith v.C ↑f}
         -- ⊢ f ∈ range ↑toContinuousMap → f ∈ {f | ↑f v.t₀ = v.x₀ ∧ LipschitzWith v.C ↑f}
  · rintro ⟨⟨f, hf₀, hf_lip⟩, rfl⟩; exact ⟨hf₀, hf_lip⟩
    -- ⊢ ↑toContinuousMap { toFun := f, map_t₀' := hf₀, lipschitz' := hf_lip } ∈ {f | …
                                    -- 🎉 no goals
  · rcases f with ⟨f, hf⟩; rintro ⟨hf₀, hf_lip⟩; exact ⟨⟨f, hf₀, hf_lip⟩, rfl⟩
    -- ⊢ ContinuousMap.mk f ∈ {f | ↑f v.t₀ = v.x₀ ∧ LipschitzWith v.C ↑f} → Continuou …
                           -- ⊢ ContinuousMap.mk f ∈ range ↑toContinuousMap
                                                 -- 🎉 no goals
#align picard_lindelof.fun_space.range_to_continuous_map PicardLindelof.FunSpace.range_toContinuousMap

theorem map_t₀ : f v.t₀ = v.x₀ :=
  f.map_t₀'
#align picard_lindelof.fun_space.map_t₀ PicardLindelof.FunSpace.map_t₀

protected theorem mem_closedBall (t : Icc v.tMin v.tMax) : f t ∈ closedBall v.x₀ v.R :=
  calc
    dist (f t) v.x₀ = dist (f t) (f.toFun v.t₀) := by rw [f.map_t₀']
                                                      -- 🎉 no goals
    _ ≤ v.C * dist t v.t₀ := (f.lipschitz.dist_le_mul _ _)
    _ ≤ v.C * v.tDist := (mul_le_mul_of_nonneg_left (v.dist_t₀_le _) v.C.2)
    _ ≤ v.R := v.isPicardLindelof.C_mul_le_R
#align picard_lindelof.fun_space.mem_closed_ball PicardLindelof.FunSpace.mem_closedBall

/-- Given a curve $γ \colon [t_{\min}, t_{\max}] → E$, `PicardLindelof.vComp` is the function
$F(t)=v(π t, γ(π t))$, where `π` is the projection $ℝ → [t_{\min}, t_{\max}]$. The integral of this
function is the image of `γ` under the contracting map we are going to define below. -/
def vComp (t : ℝ) : E :=
  v (v.proj t) (f (v.proj t))
#align picard_lindelof.fun_space.v_comp PicardLindelof.FunSpace.vComp

theorem vComp_apply_coe (t : Icc v.tMin v.tMax) : f.vComp t = v t (f t) := by
  simp only [vComp, proj_coe]
  -- 🎉 no goals
#align picard_lindelof.fun_space.v_comp_apply_coe PicardLindelof.FunSpace.vComp_apply_coe

theorem continuous_vComp : Continuous f.vComp := by
  have := (continuous_subtype_val.prod_mk f.continuous).comp v.continuous_proj
  -- ⊢ Continuous (vComp f)
  refine' ContinuousOn.comp_continuous v.continuousOn this fun x => _
  -- ⊢ ((fun x => (↑x, toFun f x)) ∘ proj v) x ∈ Icc v.tMin v.tMax ×ˢ closedBall v. …
  exact ⟨(v.proj x).2, f.mem_closedBall _⟩
  -- 🎉 no goals
#align picard_lindelof.fun_space.continuous_v_comp PicardLindelof.FunSpace.continuous_vComp

theorem norm_vComp_le (t : ℝ) : ‖f.vComp t‖ ≤ v.C :=
  v.norm_le (v.proj t).2 <| f.mem_closedBall _
#align picard_lindelof.fun_space.norm_v_comp_le PicardLindelof.FunSpace.norm_vComp_le

theorem dist_apply_le_dist (f₁ f₂ : FunSpace v) (t : Icc v.tMin v.tMax) :
    dist (f₁ t) (f₂ t) ≤ dist f₁ f₂ :=
  @ContinuousMap.dist_apply_le_dist _ _ _ _ _ (toContinuousMap f₁) (toContinuousMap f₂) _
#align picard_lindelof.fun_space.dist_apply_le_dist PicardLindelof.FunSpace.dist_apply_le_dist

theorem dist_le_of_forall {f₁ f₂ : FunSpace v} {d : ℝ} (h : ∀ t, dist (f₁ t) (f₂ t) ≤ d) :
    dist f₁ f₂ ≤ d :=
  (@ContinuousMap.dist_le_iff_of_nonempty _ _ _ _ _ (toContinuousMap f₁) (toContinuousMap f₂) _
    v.nonempty_Icc.to_subtype).2 h
#align picard_lindelof.fun_space.dist_le_of_forall PicardLindelof.FunSpace.dist_le_of_forall

instance [CompleteSpace E] : CompleteSpace v.FunSpace := by
  refine' (completeSpace_iff_isComplete_range uniformInducing_toContinuousMap).2
      (IsClosed.isComplete _)
  rw [range_toContinuousMap, setOf_and]
  -- ⊢ IsClosed ({a | ↑a v.t₀ = v.x₀} ∩ {a | LipschitzWith v.C ↑a})
  refine' (isClosed_eq (ContinuousMap.continuous_eval_const _) continuous_const).inter _
  -- ⊢ IsClosed {a | LipschitzWith v.C ↑a}
  have : IsClosed {f : Icc v.tMin v.tMax → E | LipschitzWith v.C f} :=
    isClosed_setOf_lipschitzWith v.C
  exact this.preimage ContinuousMap.continuous_coe
  -- 🎉 no goals

theorem intervalIntegrable_vComp (t₁ t₂ : ℝ) : IntervalIntegrable f.vComp volume t₁ t₂ :=
  f.continuous_vComp.intervalIntegrable _ _
#align picard_lindelof.fun_space.interval_integrable_v_comp PicardLindelof.FunSpace.intervalIntegrable_vComp

variable [CompleteSpace E]

/-- The Picard-Lindelöf operator. This is a contracting map on `PicardLindelof.FunSpace v` such
that the fixed point of this map is the solution of the corresponding ODE.

More precisely, some iteration of this map is a contracting map. -/
def next (f : FunSpace v) : FunSpace v where
  toFun t := v.x₀ + ∫ τ : ℝ in v.t₀..t, f.vComp τ
  map_t₀' := by simp only [integral_same, add_zero]
                -- 🎉 no goals
  lipschitz' := LipschitzWith.of_dist_le_mul fun t₁ t₂ => by
    rw [dist_add_left, dist_eq_norm,
      integral_interval_sub_left (f.intervalIntegrable_vComp _ _) (f.intervalIntegrable_vComp _ _)]
    exact norm_integral_le_of_norm_le_const fun t _ => f.norm_vComp_le _
    -- 🎉 no goals
#align picard_lindelof.fun_space.next PicardLindelof.FunSpace.next

theorem next_apply (t : Icc v.tMin v.tMax) : f.next t = v.x₀ + ∫ τ : ℝ in v.t₀..t, f.vComp τ :=
  rfl
#align picard_lindelof.fun_space.next_apply PicardLindelof.FunSpace.next_apply

theorem hasDerivWithinAt_next (t : Icc v.tMin v.tMax) :
    HasDerivWithinAt (f.next ∘ v.proj) (v t (f t)) (Icc v.tMin v.tMax) t := by
  haveI : Fact ((t : ℝ) ∈ Icc v.tMin v.tMax) := ⟨t.2⟩
  -- ⊢ HasDerivWithinAt ((next f).toFun ∘ proj v) (PicardLindelof.toFun v (↑t) (toF …
  simp only [(· ∘ ·), next_apply]
  -- ⊢ HasDerivWithinAt (fun x => v.x₀ + ∫ (τ : ℝ) in ↑v.t₀..↑(proj v x), vComp f τ …
  refine' HasDerivWithinAt.const_add _ _
  -- ⊢ HasDerivWithinAt (fun x => ∫ (τ : ℝ) in ↑v.t₀..↑(proj v x), vComp f τ) (Pica …
  have : HasDerivWithinAt (∫ τ in v.t₀..·, f.vComp τ) (f.vComp t) (Icc v.tMin v.tMax) t :=
    integral_hasDerivWithinAt_right (f.intervalIntegrable_vComp _ _)
      (f.continuous_vComp.stronglyMeasurableAtFilter _ _)
      f.continuous_vComp.continuousWithinAt
  rw [vComp_apply_coe] at this
  -- ⊢ HasDerivWithinAt (fun x => ∫ (τ : ℝ) in ↑v.t₀..↑(proj v x), vComp f τ) (Pica …
  refine' this.congr_of_eventuallyEq_of_mem _ t.coe_prop
  -- ⊢ (fun x => ∫ (τ : ℝ) in ↑v.t₀..↑(proj v x), vComp f τ) =ᶠ[𝓝[Icc v.tMin v.tMax …
  filter_upwards [self_mem_nhdsWithin] with _ ht'
  -- ⊢ ∫ (τ : ℝ) in ↑v.t₀..↑(proj v a✝), vComp f τ = ∫ (τ : ℝ) in ↑v.t₀..a✝, vComp  …
  rw [v.proj_of_mem ht']
  -- 🎉 no goals
#align picard_lindelof.fun_space.has_deriv_within_at_next PicardLindelof.FunSpace.hasDerivWithinAt_next

theorem dist_next_apply_le_of_le {f₁ f₂ : FunSpace v} {n : ℕ} {d : ℝ}
    (h : ∀ t, dist (f₁ t) (f₂ t) ≤ (v.L * |t.1 - v.t₀|) ^ n / n ! * d) (t : Icc v.tMin v.tMax) :
    dist (next f₁ t) (next f₂ t) ≤ (v.L * |t.1 - v.t₀|) ^ (n + 1) / (n + 1)! * d := by
  simp only [dist_eq_norm, next_apply, add_sub_add_left_eq_sub, ←
    intervalIntegral.integral_sub (intervalIntegrable_vComp _ _ _)
      (intervalIntegrable_vComp _ _ _),
    norm_integral_eq_norm_integral_Ioc] at *
  calc
    ‖∫ τ in Ι (v.t₀ : ℝ) t, f₁.vComp τ - f₂.vComp τ‖ ≤
        ∫ τ in Ι (v.t₀ : ℝ) t, v.L * ((v.L * |τ - v.t₀|) ^ n / n ! * d) := by
      refine' norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc _) _
      · -- porting note: was `continuity`
        refine .mul continuous_const <| .mul (.div_const ?_ _) continuous_const
        refine .pow (.mul continuous_const <| .abs <| ?_) _
        exact .sub continuous_id continuous_const
      · refine' (ae_restrict_mem measurableSet_Ioc).mono fun τ hτ => _
        refine' (v.lipschitzOnWith (v.proj τ).2).norm_sub_le_of_le (f₁.mem_closedBall _)
            (f₂.mem_closedBall _) ((h _).trans_eq _)
        rw [v.proj_of_mem]
        exact uIcc_subset_Icc v.t₀.2 t.2 <| Ioc_subset_Icc_self hτ
    _ = (v.L * |t.1 - v.t₀|) ^ (n + 1) / (n + 1)! * d := by
      simp_rw [mul_pow, div_eq_mul_inv, mul_assoc, MeasureTheory.integral_mul_left,
        MeasureTheory.integral_mul_right, integral_pow_abs_sub_uIoc, div_eq_mul_inv,
        pow_succ (v.L : ℝ), Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, mul_inv, mul_assoc]
#align picard_lindelof.fun_space.dist_next_apply_le_of_le PicardLindelof.FunSpace.dist_next_apply_le_of_le

theorem dist_iterate_next_apply_le (f₁ f₂ : FunSpace v) (n : ℕ) (t : Icc v.tMin v.tMax) :
    dist (next^[n] f₁ t) (next^[n] f₂ t) ≤ (v.L * |t.1 - v.t₀|) ^ n / n ! * dist f₁ f₂ := by
  induction' n with n ihn generalizing t
  -- ⊢ dist (toFun (next^[Nat.zero] f₁) t) (toFun (next^[Nat.zero] f₂) t) ≤ (↑v.L * …
  · rw [Nat.zero_eq, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
    -- ⊢ dist (toFun (next^[0] f₁) t) (toFun (next^[0] f₂) t) ≤ dist f₁ f₂
    exact dist_apply_le_dist f₁ f₂ t
    -- 🎉 no goals
  · rw [iterate_succ_apply', iterate_succ_apply']
    -- ⊢ dist (toFun (next (next^[n] f₁)) t) (toFun (next (next^[n] f₂)) t) ≤ (↑v.L * …
    exact dist_next_apply_le_of_le ihn _
    -- 🎉 no goals
#align picard_lindelof.fun_space.dist_iterate_next_apply_le PicardLindelof.FunSpace.dist_iterate_next_apply_le

theorem dist_iterate_next_le (f₁ f₂ : FunSpace v) (n : ℕ) :
    dist (next^[n] f₁) (next^[n] f₂) ≤ (v.L * v.tDist) ^ n / n ! * dist f₁ f₂ := by
  refine' dist_le_of_forall fun t => (dist_iterate_next_apply_le _ _ _ _).trans _
  -- ⊢ (↑v.L * |↑t - ↑v.t₀|) ^ n / ↑n ! * dist f₁ f₂ ≤ (↑v.L * tDist v) ^ n / ↑n !  …
  have : |(t - v.t₀ : ℝ)| ≤ v.tDist := v.dist_t₀_le t
  -- ⊢ (↑v.L * |↑t - ↑v.t₀|) ^ n / ↑n ! * dist f₁ f₂ ≤ (↑v.L * tDist v) ^ n / ↑n !  …
  gcongr
  -- 🎉 no goals
#align picard_lindelof.fun_space.dist_iterate_next_le PicardLindelof.FunSpace.dist_iterate_next_le

end FunSpace

variable [CompleteSpace E]

section

theorem exists_contracting_iterate :
    ∃ (N : ℕ) (K : _), ContractingWith K (FunSpace.next : v.FunSpace → v.FunSpace)^[N] := by
  rcases ((Real.tendsto_pow_div_factorial_atTop (v.L * v.tDist)).eventually
    (gt_mem_nhds zero_lt_one)).exists with ⟨N, hN⟩
  have : (0 : ℝ) ≤ (v.L * v.tDist) ^ N / N ! :=
    div_nonneg (pow_nonneg (mul_nonneg v.L.2 v.tDist_nonneg) _) (Nat.cast_nonneg _)
  exact ⟨N, ⟨_, this⟩, hN, LipschitzWith.of_dist_le_mul fun f g =>
    FunSpace.dist_iterate_next_le f g N⟩
#align picard_lindelof.exists_contracting_iterate PicardLindelof.exists_contracting_iterate

theorem exists_fixed : ∃ f : v.FunSpace, f.next = f :=
  let ⟨_N, _K, hK⟩ := exists_contracting_iterate v
  ⟨_, hK.isFixedPt_fixedPoint_iterate⟩
#align picard_lindelof.exists_fixed PicardLindelof.exists_fixed

end

/-- Picard-Lindelöf (Cauchy-Lipschitz) theorem. Use
`IsPicardLindelof.exists_forall_hasDerivWithinAt_Icc_eq` instead for the public API. -/
theorem exists_solution :
    ∃ f : ℝ → E, f v.t₀ = v.x₀ ∧ ∀ t ∈ Icc v.tMin v.tMax,
      HasDerivWithinAt f (v t (f t)) (Icc v.tMin v.tMax) t := by
  rcases v.exists_fixed with ⟨f, hf⟩
  -- ⊢ ∃ f, f ↑v.t₀ = v.x₀ ∧ ∀ (t : ℝ), t ∈ Icc v.tMin v.tMax → HasDerivWithinAt f  …
  refine' ⟨f ∘ v.proj, _, fun t ht => _⟩
  -- ⊢ (f.toFun ∘ proj v) ↑v.t₀ = v.x₀
  · simp only [(· ∘ ·), proj_coe, f.map_t₀]
    -- 🎉 no goals
  · simp only [(· ∘ ·), v.proj_of_mem ht]
    -- ⊢ HasDerivWithinAt (fun x => FunSpace.toFun f (proj v x)) (toFun v t (FunSpace …
    lift t to Icc v.tMin v.tMax using ht
    -- ⊢ HasDerivWithinAt (fun x => FunSpace.toFun f (proj v x)) (toFun v (↑t) (FunSp …
    simpa only [hf, v.proj_coe] using f.hasDerivWithinAt_next t
    -- 🎉 no goals
#align picard_lindelof.exists_solution PicardLindelof.exists_solution

end PicardLindelof

theorem IsPicardLindelof.norm_le₀ {E : Type*} [NormedAddCommGroup E] {v : ℝ → E → E}
    {tMin t₀ tMax : ℝ} {x₀ : E} {C R : ℝ} {L : ℝ≥0}
    (hpl : IsPicardLindelof v tMin t₀ tMax x₀ L R C) : ‖v t₀ x₀‖ ≤ C :=
  hpl.norm_le t₀ hpl.ht₀ x₀ <| mem_closedBall_self hpl.hR
#align is_picard_lindelof.norm_le₀ IsPicardLindelof.norm_le₀

/-- Picard-Lindelöf (Cauchy-Lipschitz) theorem. -/
theorem IsPicardLindelof.exists_forall_hasDerivWithinAt_Icc_eq [CompleteSpace E] {v : ℝ → E → E}
    {tMin t₀ tMax : ℝ} (x₀ : E) {C R : ℝ} {L : ℝ≥0}
    (hpl : IsPicardLindelof v tMin t₀ tMax x₀ L R C) :
    ∃ f : ℝ → E, f t₀ = x₀ ∧
      ∀ t ∈ Icc tMin tMax, HasDerivWithinAt f (v t (f t)) (Icc tMin tMax) t := by
  lift C to ℝ≥0 using (norm_nonneg _).trans hpl.norm_le₀
  -- ⊢ ∃ f, f t₀ = x₀ ∧ ∀ (t : ℝ), t ∈ Icc tMin tMax → HasDerivWithinAt f (v t (f t …
  lift t₀ to Icc tMin tMax using hpl.ht₀
  -- ⊢ ∃ f, f ↑t₀ = x₀ ∧ ∀ (t : ℝ), t ∈ Icc tMin tMax → HasDerivWithinAt f (v t (f  …
  exact PicardLindelof.exists_solution
    ⟨v, tMin, tMax, t₀, x₀, C, ⟨R, hpl.hR⟩, L, { hpl with ht₀ := t₀.property }⟩
#align exists_forall_deriv_within_Icc_eq_of_is_picard_lindelof IsPicardLindelof.exists_forall_hasDerivWithinAt_Icc_eq

variable [ProperSpace E] {v : E → E} (t₀ : ℝ) (x₀ : E)

/-- A time-independent, locally continuously differentiable ODE satisfies the hypotheses of the
  Picard-Lindelöf theorem. -/
theorem exists_isPicardLindelof_const_of_contDiffOn_nhds {s : Set E} (hv : ContDiffOn ℝ 1 v s)
    (hs : s ∈ 𝓝 x₀) :
    ∃ ε > (0 : ℝ), ∃ L R C, IsPicardLindelof (fun _ => v) (t₀ - ε) t₀ (t₀ + ε) x₀ L R C := by
  -- extract Lipschitz constant
  obtain ⟨L, s', hs', hlip⟩ :=
    ContDiffAt.exists_lipschitzOnWith ((hv.contDiffWithinAt (mem_of_mem_nhds hs)).contDiffAt hs)
  -- radius of closed ball in which v is bounded
  obtain ⟨r, hr : 0 < r, hball⟩ := Metric.mem_nhds_iff.mp (inter_sets (𝓝 x₀) hs hs')
  -- ⊢ ∃ ε, ε > 0 ∧ ∃ L R C, IsPicardLindelof (fun x => v) (t₀ - ε) t₀ (t₀ + ε) x₀  …
  have hr' := (half_pos hr).le
  -- ⊢ ∃ ε, ε > 0 ∧ ∃ L R C, IsPicardLindelof (fun x => v) (t₀ - ε) t₀ (t₀ + ε) x₀  …
  -- uses [ProperSpace E] for `isCompact_closedBall`
  obtain ⟨C, hC⟩ := (isCompact_closedBall x₀ (r / 2)).bddAbove_image <| hv.continuousOn.norm.mono
    (subset_inter_iff.mp ((closedBall_subset_ball (half_lt_self hr)).trans hball)).left
  have hC' : 0 ≤ C := by
    apply (norm_nonneg (v x₀)).trans
    apply hC
    exact ⟨x₀, ⟨mem_closedBall_self hr', rfl⟩⟩
  set ε := if C = 0 then 1 else r / 2 / C with hε
  -- ⊢ ∃ ε, ε > 0 ∧ ∃ L R C, IsPicardLindelof (fun x => v) (t₀ - ε) t₀ (t₀ + ε) x₀  …
  have hε0 : 0 < ε := by
    rw [hε]
    split_ifs with h
    · exact zero_lt_one
    · exact div_pos (half_pos hr) (lt_of_le_of_ne hC' (Ne.symm h))
  refine' ⟨ε, hε0, L, r / 2, C, _⟩
  -- ⊢ IsPicardLindelof (fun x => v) (t₀ - ε) t₀ (t₀ + ε) x₀ L (r / 2) C
  exact
    { ht₀ := by rw [← Real.closedBall_eq_Icc]; exact mem_closedBall_self hε0.le
      hR := (half_pos hr).le
      lipschitz := fun t _ => hlip.mono
        (subset_inter_iff.mp (Subset.trans (closedBall_subset_ball (half_lt_self hr)) hball)).2
      cont := fun x _ => continuousOn_const
      norm_le := fun t _ x hx => hC ⟨x, hx, rfl⟩
      C_mul_le_R := by
        rw [add_sub_cancel', sub_sub_cancel, max_self, mul_ite, mul_one]
        split_ifs with h
        · rwa [← h] at hr'
        · exact (mul_div_cancel' (r / 2) h).le }
#align exists_is_picard_lindelof_const_of_cont_diff_on_nhds exists_isPicardLindelof_const_of_contDiffOn_nhds

/-- A time-independent, locally continuously differentiable ODE admits a solution in some open
interval. -/
theorem exists_forall_deriv_at_Ioo_eq_of_contDiffOn_nhds {s : Set E} (hv : ContDiffOn ℝ 1 v s)
    (hs : s ∈ 𝓝 x₀) :
    ∃ ε > (0 : ℝ),
      ∃ f : ℝ → E, f t₀ = x₀ ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), f t ∈ s ∧ HasDerivAt f (v (f t)) t := by
  obtain ⟨ε, hε, L, R, C, hpl⟩ := exists_isPicardLindelof_const_of_contDiffOn_nhds t₀ x₀ hv hs
  -- ⊢ ∃ ε, ε > 0 ∧ ∃ f, f t₀ = x₀ ∧ ∀ (t : ℝ), t ∈ Ioo (t₀ - ε) (t₀ + ε) → f t ∈ s …
  obtain ⟨f, hf1, hf2⟩ := hpl.exists_forall_hasDerivWithinAt_Icc_eq x₀
  -- ⊢ ∃ ε, ε > 0 ∧ ∃ f, f t₀ = x₀ ∧ ∀ (t : ℝ), t ∈ Ioo (t₀ - ε) (t₀ + ε) → f t ∈ s …
  have hf2' : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt f (v (f t)) t := fun t ht =>
    (hf2 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have h : f ⁻¹' s ∈ 𝓝 t₀ := by
    have := hf2' t₀ (mem_Ioo.mpr ⟨sub_lt_self _ hε, lt_add_of_pos_right _ hε⟩)
    apply ContinuousAt.preimage_mem_nhds this.continuousAt
    rw [hf1]
    exact hs
  rw [Metric.mem_nhds_iff] at h
  -- ⊢ ∃ ε, ε > 0 ∧ ∃ f, f t₀ = x₀ ∧ ∀ (t : ℝ), t ∈ Ioo (t₀ - ε) (t₀ + ε) → f t ∈ s …
  obtain ⟨r, hr1, hr2⟩ := h
  -- ⊢ ∃ ε, ε > 0 ∧ ∃ f, f t₀ = x₀ ∧ ∀ (t : ℝ), t ∈ Ioo (t₀ - ε) (t₀ + ε) → f t ∈ s …
  refine ⟨min r ε, lt_min hr1 hε, f, hf1, fun t ht => ⟨?_,
    hf2' t (mem_of_mem_of_subset ht (Ioo_subset_Ioo (sub_le_sub_left (min_le_right _ _) _)
      (add_le_add_left (min_le_right _ _) _)))⟩⟩
  rw [← Set.mem_preimage]
  -- ⊢ t ∈ f ⁻¹' s
  apply Set.mem_of_mem_of_subset _ hr2
  -- ⊢ t ∈ ball t₀ r
  apply Set.mem_of_mem_of_subset ht
  -- ⊢ Ioo (t₀ - min r ε) (t₀ + min r ε) ⊆ ball t₀ r
  rw [← Real.ball_eq_Ioo]
  -- ⊢ ball t₀ (min r ε) ⊆ ball t₀ r
  exact Metric.ball_subset_ball (min_le_left _ _)
  -- 🎉 no goals
#align exists_forall_deriv_at_Ioo_eq_of_cont_diff_on_nhds exists_forall_deriv_at_Ioo_eq_of_contDiffOn_nhds

/-- A time-independent, continuously differentiable ODE admits a solution in some open interval. -/
theorem exists_forall_hasDerivAt_Ioo_eq_of_contDiff (hv : ContDiff ℝ 1 v) :
    ∃ ε > (0 : ℝ), ∃ f : ℝ → E, f t₀ = x₀ ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt f (v (f t)) t :=
  let ⟨ε, hε, f, hf1, hf2⟩ :=
    exists_forall_deriv_at_Ioo_eq_of_contDiffOn_nhds t₀ x₀ hv.contDiffOn
      (IsOpen.mem_nhds isOpen_univ (mem_univ _))
  ⟨ε, hε, f, hf1, fun t ht => (hf2 t ht).2⟩
#align exists_forall_deriv_at_Ioo_eq_of_cont_diff exists_forall_hasDerivAt_Ioo_eq_of_contDiff
