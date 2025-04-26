/-
Copyright (c) 2025 Hanliu Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang, Hanliu Jiang
-/
import Mathlib.NumberTheory.Padics.PSAC

set_option maxHeartbeats 10000000000000
set_option synthInstance.maxHeartbeats 10000000000000


open Finset IsUltrametricDist NNReal Filter  CauSeq  zero_atBot
open scoped fwdDiff ZeroAtInfty Topology  LaurentSeries PowerSeries
variable {p : ℕ} [hp : Fact p.Prime]

namespace PadicInt
lemma Tends_to_Zero'(f:(AdicCompletion (Ideal.span {(p:ℤ_[p]⸨X⸩)}) (ℤ_[p]⸨X⸩)))
:Tendsto (fun n ↦ (p_sequence_coeff (p:=p) n) f) atBot (𝓝 0):=by
  have:=by
   exact AdicCompletion.mk_surjective (Ideal.span {(p:ℤ_[p]⸨X⸩)}) ℤ_[p]⸨X⸩
  unfold Function.Surjective at this
  rcases (this f) with ⟨r,rs⟩
  have :(fun n ↦  p_sequence_coeff (p:=p) n f)=
    (fun n  ↦  cauchy_sequence_coeff (p:=p) n r) :=by
      ext n
      rw[esg n f r rs]
  rw[this]
  exact cauchy_sequence_coeff_tends_to_zero' r
lemma Tends_to_Zero_0(f:(AdicCompletion (Ideal.span {(p:ℤ_[p]⸨X⸩)}) (ℤ_[p]⸨X⸩)))
:Tendsto (fun n:ℕ ↦  p_sequence_coeff (p:=p) (-n:ℤ ) f) atTop
(𝓝 0):=by
 have:=Tends_to_Zero' f
 rw[NormedAddCommGroup.tendsto_atBot] at this
 refine NormedAddCommGroup.tendsto_atTop.mpr ?_
 intro s rs
 choose m sm using (this s rs)
 use (-m).natAbs
 intro e de
 have: m ≥  (-↑e):=by
   simp
   have:-(e:ℤ) ≤ -↑(-m).natAbs :=by
     simp only [ neg_le_neg_iff, sup_le_iff, Nat.cast_nonneg, and_true]
     exact Int.ofNat_le.mpr de
   have: -↑(-m).natAbs ≤ m :=by
     simp
     exact neg_abs_le m
   (expose_names; exact Int.le_trans this_2 this)
 exact (sm (-(e:ℤ)) this)
lemma Tends_to_Zero_1(f:(AdicCompletion (Ideal.span {(p:ℤ_[p]⸨X⸩)}) (ℤ_[p]⸨X⸩)))
:Tendsto (fun n:ℕ ↦  p_sequence_coeff (p:=p) (-(n+1):ℤ ) f) atTop
(𝓝 0):=by
  have:=Tends_to_Zero_0  (p:=p) f
  rw[NormedAddCommGroup.tendsto_atTop] at this
  refine NormedAddCommGroup.tendsto_atTop.mpr ?_
  intro h sh
  simp only [sub_zero]
  choose e se using (this h sh)
  use e
  intro r sf
  have:=se (r+1) (Nat.le_add_right_of_le sf)
  simp only [sub_zero] at this
  exact this
lemma Tends_to_Zero(a:(AdicCompletion (Ideal.span {(p:ℤ_[p]⸨X⸩)}) (ℤ_[p]⸨X⸩)))
:Tendsto (fun n:ℕ ↦  (p_sequence_coeff (p:=p) (-(n+1):ℤ ) a
-p_sequence_coeff (p:=p) (-(n+2):ℤ ) a)) atTop
(𝓝 0):=by
  have:=Tends_to_Zero_0  (p:=p) a
  rw[NormedAddCommGroup.tendsto_atTop] at this
  refine NormedAddCommGroup.tendsto_atTop.mpr ?_
  intro h sh
  simp only [sub_zero]
  choose e se using (this h sh)
  use e
  intro r sf
  rw[sub_eq_add_neg]
  have  := nonarchimedean ((p_sequence_coeff (p:=p) (-↑(r+ 1))) a)  (-(p_sequence_coeff
  (p:=p) (-↑(r+ 2))) a)
  have m : ‖(p_sequence_coeff (p:=p) (-↑(r+ 1))) a‖ ⊔ ‖-(p_sequence_coeff
  (p:=p) (-↑(r+ 2))) a‖ <h :=by
    refine max_lt ?_ ?_
    · have:=se (r+1) (Nat.le_add_right_of_le sf)
      simp only [sub_zero] at this
      exact this
    · have:=se (r+2) (Nat.le_add_right_of_le sf)
      simp only [sub_zero] at this
      simp only [norm_neg]
      exact this
  exact lt_of_le_of_lt this m

noncomputable def FunctionTrans_2: (AdicCompletion (Ideal.span {(p:ℤ_[p]⸨X⸩)})
 (ℤ_[p]⸨X⸩)) →ₗ[ℤ_[p]]
 C₀(ℕ, ℤ_[p]) where
   toFun a :=⟨⟨(fun n:ℕ => p_sequence_coeff (p:=p) (-((n+1):ℕ ):ℤ ) a-
   p_sequence_coeff (p:=p) (-((n+2):ℕ ):ℤ ) a)
    ,continuous_of_discreteTopology⟩, cocompact_eq_atTop (α := ℕ) ▸ Tends_to_Zero a⟩
   map_add'  a b:=by
     ext n
     simp
     ring
   map_smul' a b:=by
     ext s
     simp
     ring

noncomputable def asd (a:C_₀(ℤ,ℤ_[p]))(t:ℕ): BddBelow (Function.support
 (fun (n : ℤ) => if ‖a n‖≤(p:ℝ)^(-t:ℤ) then 0 else (a n))) :=by

  have e:= zero_atBot a
  rw[NormedAddCommGroup.tendsto_atBot] at e
  have:(p:ℝ )^(-t:ℤ) >0 :=by
    simp
    refine pow_pos ?_ t
    simp
    exact Nat.pos_of_neZero p
  have:=e ((p:ℝ )^(-t:ℤ)) this
  choose m fs using this
  refine HahnSeries.forallLTEqZero_supp_BddBelow _  m ?_
  intro s js
  have:‖a s‖≤(p:ℝ)^(-t:ℤ) :=by
    refine le_of_lt ?_
    have:=fs s (Int.le_of_lt js)
    simp only [sub_zero] at this
    exact this
  exact if_pos this

noncomputable def Adic_Complection_tofun : C_₀(ℤ,ℤ_[p]) →
 (AdicCompletion.AdicCauchySequence (Ideal.span {(p:ℤ_[p]⸨X⸩)})
 (ℤ_[p]⸨X⸩)) :=fun
   | a => {
     val t :=HahnSeries.ofSuppBddBelow (fun (n : ℤ) => if ‖a n‖≤(p:ℝ)^(-t:ℤ) then 0 else (a n))
       (asd a t)
     property :=by
       intro m n  sn
       simp only
       refine powerseries_equiv_2 m _ _ ?_
       intro s
       unfold HahnSeries.coeff_map_0
       simp only [LinearMap.coe_mk, AddHom.coe_mk,
         HahnSeries.ofSuppBddBelow_coeff]
       rcases Decidable.em (‖a s‖ ≤ (p:ℝ)^(-m:ℤ)) with r1|r2
       · rcases Decidable.em (‖a s‖ ≤ (p:ℝ)^(-n:ℤ)) with r3|r4
         · simp only [r1, r3]
           simp
         · simp only[r1 ,r4]
           simp only [↓reduceIte, zero_sub, neg_mem_iff,
           Ideal.span_singleton_pow]
           rw[norm_le_pow_iff_mem_span_pow] at r1
           exact r1
       · rcases Decidable.em (‖a s‖ ≤ (p:ℝ)^(-n:ℤ)) with r3|r4
         · simp only[r2,r3]
           simp
           rw[norm_le_pow_iff_mem_span_pow,← Ideal.span_singleton_pow] at r3
           exact (Ideal.pow_le_pow_right sn) r3
         · simp only[r2,r4]
           simp





   }


lemma help1 (r:
 AdicCompletion.AdicCauchySequence (Ideal.span {(p:ℤ_[p]⸨X⸩)}) ℤ_[p]⸨X⸩)(s:ℤ):
 IsCauSeq norm ( fun n ↦ (r n).coeff s ) :=by
    have: ( fun n ↦ (r n).coeff s ) =
     Cauchy_p_adic  (((AdicCompletion.mapAlg (IsLocalRing.maximalIdeal ℤ_[p])
    (Ideal.span {(p:ℤ_[p]⸨X⸩)}) (HahnSeries.coeff_map_0 (p:=p) s) (CauchyHanser s))) r):=by
      unfold  HahnSeries.coeff_map_0 Cauchy_p_adic
      ext n
      simp
      rfl
    rw[this]
    rcases (Cauchy_p_adic (((AdicCompletion.mapAlg (IsLocalRing.maximalIdeal ℤ_[p])
    (Ideal.span {(p:ℤ_[p]⸨X⸩)}) (HahnSeries.coeff_map_0 (p:=p) s) (CauchyHanser s))) r))
     with ⟨l1,l2⟩
    simp
    exact l2

lemma help2 (r:
 AdicCompletion.AdicCauchySequence (Ideal.span {(p:ℤ_[p]⸨X⸩)}) ℤ_[p]⸨X⸩):
∀ ε >0 , ∃ N ,∀ n≥ N ,∀  (s:ℤ),‖(r n).coeff s-
 CauSeq.lim ⟨fun n ↦ (r n).coeff s, help1 r s⟩‖ <  ε  :=by
  intro ε hε
  obtain ⟨m, hm⟩ := exists_pow_neg_lt p hε
  use m
  intro s hs s_1
  have: (r s).coeff s_1-
   CauSeq.lim ⟨fun n ↦ (r n).coeff s_1, help1 r s_1⟩=
   CauSeq.lim (const norm ((r s).coeff s_1)-⟨ fun n ↦ (r n).coeff s_1, help1 r s_1⟩) :=by
     nth_rw  2 [← Mathlib.Tactic.RingNF.add_neg]
     rw[← lim_add,lim_neg,lim_const ]
     ring
  rw[this]
  refine  lt_of_le_of_lt ?_ hm
  refine CauchyL _ _ ?_
  use m
  intro g3 sr3
  simp only [sub_apply, const_apply]
  have:=powerseries_equiv (p:=p)  m s_1
  unfold HahnSeries.coeff_map_0 at this
  simp at this
  rw[norm_le_pow_iff_mem_span_pow,←Ideal.span_singleton_pow]
  refine this (r s) (r g3) ?_
  rcases r with ⟨l1,l2⟩
  simp
  unfold AdicCompletion.IsAdicCauchy at l2
  simp at l2
  exact SModEq.trans (id (SModEq.symm (l2 hs))) (l2 sr3)
theorem zpow_adds ( x : ℝ)(hx : ¬ x=0)(y z:ℤ)  : x ^ (y + z) = x ^ y * x ^ z := by
  have:∃ r:ℝˣ, x= r :=by
    refine Units.exists_iff_ne_zero.mpr ?_
    use x
  choose r hr using this
  rw[hr]
  have(m:ℤ ): (r:ℝ)^m =Units.val (r^m) :=by
    simp
  rw[this]
  rw[zpow_add r y z]
  simp

lemma ds3(a:AdicCompletion (Ideal.span {(p:ℤ_[p]⸨X⸩)})
 (ℤ_[p]⸨X⸩)) :AdicCompletion.mk (Ideal.span {(p:ℤ_[p]⸨X⸩)}) ℤ_[p]⸨X⸩
    (Adic_Complection_tofun ⟨⟨(fun n => (p_sequence_coeff (p:=p) n a)),
     continuous_of_discreteTopology⟩,Tends_to_Zero' a⟩) = a :=by
  have:=by
   exact AdicCompletion.mk_surjective (Ideal.span {(p:ℤ_[p]⸨X⸩)}) ℤ_[p]⸨X⸩
  unfold Function.Surjective at this
  rcases (this a) with ⟨r,rs⟩
  rw[← sub_eq_zero,← rs,← LinearMap.map_sub]
  refine AdicCompletion.mk_zero_of (Ideal.span {(p:ℤ_[p]⸨X⸩)}) ℤ_[p]⸨X⸩ _ ?_
  rw[rs]
  simp only [
    AdicCompletion.AdicCauchySequence.sub_apply,← SModEq.sub_mem]
  use 0
  intro g sefg
  have: (p:ℝ)^(-g:ℤ)>0 :=by
     simp
     refine pow_pos ?_ g
     simp
     exact Nat.pos_of_neZero p
  choose seg theg  using (help2 r ((p:ℝ)^(-g:ℤ)) this)
  use (max g seg)
  constructor
  · exact Nat.le_max_left g seg
  · use g
    constructor
    · exact Nat.le_refl g
    · refine powerseries_equiv_2 g  _ _ ?_
      intro s
      unfold HahnSeries.coeff_map_0 Adic_Complection_tofun
      simp only [
        ZeroAtBotContinuousMap.coe_mk,  LinearMap.coe_mk, AddHom.coe_mk,
        HahnSeries.ofSuppBddBelow_coeff]
      have:=esg s a r rs
      rcases Decidable.em (‖(p_sequence_coeff (p:=p) s) a‖≤ (p:ℝ)^(-(max g seg):ℤ)) with r3|r4
      · simp only [r3]
        simp only [↓reduceIte, zero_sub, neg_mem_iff]
        rw[this] at r3
        unfold cauchy_sequence_coeff Cauchy.seq_map Cauchy_p_adic HahnSeries.coeff_map_0
         AdicCompletion.mapAlg at r3
        simp only[Ideal.span_singleton_pow, ← norm_le_pow_iff_mem_span_pow,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply] at r3
        simp only[Ideal.span_singleton_pow, ← norm_le_pow_iff_mem_span_pow]
        have ln:=theg (max g seg) (Nat.le_max_right g seg) s
        have :=norm_add_le  ((r (g ⊔ seg)).coeff s -
         CauSeq.lim ⟨fun n ↦ (r n).coeff s,  help1 r s⟩)
          (CauSeq.lim ⟨fun n ↦ (r n).coeff s,  help1 r s⟩)
        rw[sub_add_cancel] at this
        have ln2:=add_lt_add_of_lt_of_le ln r3
        have:=lt_of_le_of_lt this ln2
        have gf:(p:ℝ) ^ (-g:ℤ) + (p:ℝ)^ (-(g ⊔ seg):ℤ) ≤ (p:ℝ) ^ (-(g:ℤ)+ 1) :=by
          have: (p:ℝ)^ (-(g ⊔ seg):ℤ) ≤ (p:ℝ)^ (-g:ℤ) :=by
             refine (zpow_le_zpow_iff_right₀ ?_).mpr ?_
             simp
             refine Nat.Prime.one_lt (hp.1)
             simp
          have:=add_le_add (Preorder.le_refl ((p:ℝ)^ (-g:ℤ))) this
          refine le_trans this ?_
          rw[← (two_mul)]
          have:(p:ℝ) ^ (-(g:ℤ)+ 1)=p *(p:ℝ)^ (-g:ℤ) :=by
                have:¬ (p:ℝ)=0 :=by
                    simp
                    exact NeZero.ne p
                rw[(zpow_adds (p:ℝ) this (-(g:ℤ))  1 )]
                simp
                ring
          rw[this]
          refine (mul_le_mul_iff_of_pos_right ?_).mpr ?_
          simp
          refine pow_pos ?_ g
          simp
          exact Nat.pos_of_neZero p
          simp
          exact Nat.Prime.two_le hp.1
        exact (norm_le_pow_iff_norm_lt_pow_add_one ((r (g ⊔ seg)).coeff s) (-g:ℤ)).mpr
          (gt_of_ge_of_gt gf this)
      · simp only [r4,↓reduceIte]
        rw[esg s a r rs]
        unfold cauchy_sequence_coeff Cauchy.seq_map Cauchy_p_adic HahnSeries.coeff_map_0
         AdicCompletion.mapAlg
        simp only[Ideal.span_singleton_pow, ← norm_le_pow_iff_mem_span_pow,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply]
        have ln:=theg (max g seg) (Nat.le_max_right g seg) s
        rw[← (neg_sub),norm_neg] at ln
        exact le_of_lt ln

lemma helper3 (a:CauSeq ℤ_[p] norm)(b:ℤ_[p])(hs :CauSeq.LimZero (a-const norm b)):
 a.lim =b:=by
  rw[← lim_eq_zero_iff ,← Mathlib.Tactic.RingNF.add_neg,← lim_add,lim_neg,lim_const ] at hs
  calc
  _=(a.lim+ (-b))+b :=by ring
  _=_:=by
    rw[hs]
    simp





end PadicInt
