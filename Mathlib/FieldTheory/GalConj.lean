/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/

import Mathlib.FieldTheory.Normal

/-!
TODO
-/

open Polynomial

open scoped Polynomial BigOperators IntermediateField

namespace AlgEquiv

variable {R : Type*} [CommSemiring R] {A₁ A₂ : Type*}

variable [Semiring A₁] [Semiring A₂]

variable [Algebra R A₁] [Algebra R A₂]

variable (e : A₁ ≃ₐ[R] A₂)

theorem symm_apply_eq {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq
#align alg_equiv.symm_apply_eq AlgEquiv.symm_apply_eq

end AlgEquiv

namespace IntermediateField

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] {α : E}

theorem adjoinRootEquivAdjoin_symm_apply_gen (h : IsIntegral F α) :
    (adjoinRootEquivAdjoin F h).symm (AdjoinSimple.gen F α) = AdjoinRoot.root (minpoly F α) := by
  rw [AlgEquiv.symm_apply_eq, adjoinRootEquivAdjoin_apply_root]
#align intermediate_field.adjoin_root_equiv_adjoin_symm_apply_gen IntermediateField.adjoinRootEquivAdjoin_symm_apply_gen

end IntermediateField

section GalConjClasses

variable (F : Type*) [Field F] (E : Type*) [Field E] [Algebra F E]

def IsGalConj.setoid :=
  MulAction.orbitRel (E ≃ₐ[F] E) E
#align is_gal_conj.setoid IsGalConj.setoid

def GalConjClasses :=
  MulAction.orbitRel.Quotient (E ≃ₐ[F] E) E
#align gal_conj_classes GalConjClasses

variable {E}

def IsGalConj (x y : E) : Prop :=
  (IsGalConj.setoid F E).r x y
#align is_gal_conj IsGalConj

scoped[IsGalConj] notation:50 -- need to fix the precedence
  x " ≈g[" F "] " y => IsGalConj F x y

open scoped IsGalConj

namespace IsGalConj

instance decidable [DecidableEq E] [Fintype (E ≃ₐ[F] E)] (x y : E) :
    Decidable (x ≈g[F] y) :=
  Fintype.decidableExistsFintype

instance [DecidableEq E] [Fintype (E ≃ₐ[F] E)] : DecidableEq (GalConjClasses F E) :=
  @Quotient.decidableEq _ (IsGalConj.setoid F E) (IsGalConj.decidable F)

instance : IsEquiv E (IsGalConj F) :=
  letI := IsGalConj.setoid F E
  inferInstanceAs <| IsEquiv E (· ≈ ·)

@[refl]
nonrec theorem refl (x : E) : x ≈g[F] x :=
  refl x
#align is_gal_conj.refl IsGalConj.refl

@[symm]
nonrec theorem symm {x y : E} : (x ≈g[F] y) → y ≈g[F] x :=
  symm
#align is_gal_conj.symm IsGalConj.symm

@[trans]
nonrec theorem trans {x y z : E} : (x ≈g[F] y) → (y ≈g[F] z) → x ≈g[F] z :=
  _root_.trans
#align is_gal_conj.trans IsGalConj.trans

end IsGalConj

namespace GalConjClasses

def mk (x : E) : GalConjClasses F E :=
  ⟦x⟧
#align gal_conj_classes.mk GalConjClasses.mk

instance : Zero (GalConjClasses F E) :=
  ⟨mk F 0⟩

theorem zero_def : (0 : GalConjClasses F E) = mk F 0 :=
  rfl
#align gal_conj_classes.zero_def GalConjClasses.zero_def

@[elab_as_elim]
lemma ind {motive : GalConjClasses F E → Prop} (h : ∀ x : E, motive (mk F x))
    (c : GalConjClasses F E) : motive c :=
  Quotient.ind h c

variable {F}

noncomputable def out (c : GalConjClasses F E) : E :=
  letI := IsGalConj.setoid F E
  Quotient.out c
#align gal_conj_classes.out GalConjClasses.out

@[simp]
theorem eq {x y : E} : mk F x = mk F y ↔ x ≈g[F] y :=
  letI := IsGalConj.setoid F E
  Quotient.eq'
#align gal_conj_classes.eq GalConjClasses.eq

@[simp]
nonrec theorem out_eq (q : GalConjClasses F E) : mk F q.out = q :=
  letI := IsGalConj.setoid F E
  q.out_eq
#align gal_conj_classes.out_eq GalConjClasses.out_eq

theorem mk_out (x : E) :
    letI := IsGalConj.setoid F E
    (mk F x).out ≈ x :=
  letI := IsGalConj.setoid F E
  Quotient.mk_out x
#align gal_conj_classes.mk_out GalConjClasses.mk_out

theorem mk_eq_iff_out {x : E} {c : GalConjClasses F E} : mk F x = c ↔ x ≈g[F] c.out :=
  letI := IsGalConj.setoid F E
  Quotient.mk_eq_iff_out
#align gal_conj_classes.mk_eq_iff_out GalConjClasses.mk_eq_iff_out

theorem eq_mk_iff_out {c : GalConjClasses F E} {x : E} : c = mk F x ↔ c.out ≈g[F] x :=
  letI := IsGalConj.setoid F E
  Quotient.eq_mk_iff_out
#align gal_conj_classes.eq_mk_iff_out GalConjClasses.eq_mk_iff_out

@[simp]
theorem out_equiv_out {c₁ c₂ : GalConjClasses F E} : (c₁.out ≈g[F] c₂.out) ↔ c₁ = c₂ :=
  @Quotient.out_equiv_out _ _ c₁ c₂
#align gal_conj_classes.out_equiv_out GalConjClasses.out_equiv_out

theorem equiv_zero_iff (x : E) : (x ≈g[F] 0) ↔ x = 0 := by
  refine' ⟨fun h => _, fun h => by rw [h]⟩
  cases' h with a ha
  simp_rw [← ha, AlgEquiv.smul_def, map_zero]
#align gal_conj_classes.equiv_zero_iff GalConjClasses.equiv_zero_iff

theorem out_eq_zero_iff (c : GalConjClasses F E) : c.out = 0 ↔ c = 0 := by
  rw [zero_def, eq_mk_iff_out, equiv_zero_iff]
#align gal_conj_classes.out_eq_zero_iff GalConjClasses.out_eq_zero_iff

theorem zero_out : (0 : GalConjClasses F E).out = 0 :=
  (out_eq_zero_iff 0).mpr rfl
#align gal_conj_classes.zero_out GalConjClasses.zero_out

theorem mk_eq_zero_iff (x : E) : mk F x = 0 ↔ x = 0 := by
  rw [mk_eq_iff_out, zero_out, equiv_zero_iff]
#align gal_conj_classes.mk_eq_zero_iff GalConjClasses.mk_eq_zero_iff

theorem mk_zero : mk F (0 : E) = 0 :=
  (mk_eq_zero_iff 0).mpr rfl
#align gal_conj_classes.mk_zero GalConjClasses.mk_zero

nonrec def orbit (c : GalConjClasses F E) : Set E :=
  c.orbit
#align gal_conj_classes.orbit GalConjClasses.orbit

instance [DecidableEq E] [Fintype (E ≃ₐ[F] E)] (c : GalConjClasses F E) : Fintype c.orbit :=
  Quotient.recOnSubsingleton' c fun _ => Set.fintypeRange _

theorem mem_orbit {x : E} {c : GalConjClasses F E} : x ∈ c.orbit ↔ mk F x = c :=
  MulAction.orbitRel.Quotient.mem_orbit
#align gal_conj_classes.mem_orbit GalConjClasses.mem_orbit

theorem orbit_zero : (0 : GalConjClasses F E).orbit = {0} := by
  ext; rw [mem_orbit, mk_eq_zero_iff, Set.mem_singleton_iff]
#align gal_conj_classes.orbit_zero GalConjClasses.orbit_zero

instance : Neg (GalConjClasses F E) :=
  ⟨Quotient.lift (fun x : E => mk F (-x))
      (by
        rintro _ y ⟨f, rfl⟩; rw [eq]
        use f; change f (-y) = -f y; rw [AlgEquiv.map_neg])⟩

theorem mk_neg (x : E) : mk F (-x) = -mk F x :=
  rfl
#align gal_conj_classes.mk_neg GalConjClasses.mk_neg

instance : InvolutiveNeg (GalConjClasses F E) :=
  { (inferInstance : Neg (GalConjClasses F E)) with
    neg_neg := fun x => by rw [← out_eq x, ← mk_neg, ← mk_neg, neg_neg] }

theorem exist_mem_orbit_add_eq_zero (x y : GalConjClasses F E) :
    (∃ a b : E, (a ∈ x.orbit ∧ b ∈ y.orbit) ∧ a + b = 0) ↔ x = -y := by
  simp_rw [mem_orbit]
  constructor
  · rintro ⟨a, b, ⟨rfl, rfl⟩, h⟩
    rw [← mk_neg, eq, add_eq_zero_iff_eq_neg.mp h]
  · rintro rfl
    refine' ⟨-y.out, y.out, _⟩
    simp_rw [mk_neg, out_eq, neg_add_self, and_self]
#align gal_conj_classes.exist_mem_orbit_add_eq_zero GalConjClasses.exist_mem_orbit_add_eq_zero

noncomputable nonrec def minpoly : GalConjClasses F E → F[X] :=
  Quotient.lift (minpoly F) fun _ b ⟨f, h⟩ => h ▸ minpoly.algEquiv_eq f b
#align gal_conj_classes.minpoly GalConjClasses.minpoly

theorem minpoly_mk (x : E) : minpoly (mk F x) = _root_.minpoly F x :=
  rfl
#align gal_conj_classes.minpoly_mk GalConjClasses.minpoly_mk

theorem minpoly_out (c : GalConjClasses F E) : _root_.minpoly F c.out = minpoly c := by
  rw [← c.out_eq, minpoly_mk, c.out_eq]
#align gal_conj_classes.minpoly_out GalConjClasses.minpoly_out

variable [IsSeparable F E]
-- most lemmas work with Algebra.IsIntegral / Algebra.IsAlgebraic
-- but there isn't a lemma saying these are implied by `IsSeparable`

theorem monic_minpoly (c : GalConjClasses F E) : (minpoly c).Monic := by
  rw [← c.out_eq, minpoly_mk]; exact minpoly.monic (IsSeparable.isIntegral F _)
#align gal_conj_classes.minpoly.monic GalConjClasses.monic_minpoly

theorem minpoly_ne_zero (c : GalConjClasses F E) : minpoly c ≠ 0 := by
  rw [← c.out_eq, minpoly_mk]
  exact minpoly.ne_zero (IsSeparable.isIntegral F _)
#align gal_conj_classes.minpoly.ne_zero GalConjClasses.minpoly_ne_zero

theorem irreducible_minpoly (c : GalConjClasses F E) : Irreducible (minpoly c) := by
  rw [← c.out_eq, minpoly_mk]; exact minpoly.irreducible (IsSeparable.isIntegral F _)
#align gal_conj_classes.minpoly.irreducible GalConjClasses.irreducible_minpoly

theorem splits_minpoly [n : Normal F E] (c : GalConjClasses F E) :
    Splits (algebraMap F E) (minpoly c) := by rw [← c.out_eq, minpoly_mk]; exact n.splits c.out
#align gal_conj_classes.minpoly.splits GalConjClasses.splits_minpoly

theorem separable_minpoly (c : GalConjClasses F E) : Separable (minpoly c) := by
  rw [← c.out_eq, minpoly_mk]; exact IsSeparable.separable F c.out
#align gal_conj_classes.minpoly.separable GalConjClasses.separable_minpoly

theorem minpoly_inj [Normal F E] {c d : GalConjClasses F E} (h : minpoly c = minpoly d) :
    c = d := by
  induction' c using GalConjClasses.ind with x
  induction' d using GalConjClasses.ind with y
  let fc := IntermediateField.adjoinRootEquivAdjoin F (IsSeparable.isIntegral F x)
  let fd := IntermediateField.adjoinRootEquivAdjoin F (IsSeparable.isIntegral F y)
  let congr_f {px py : F[X]} (h : px = py) : AdjoinRoot px ≃ₐ[F] AdjoinRoot py :=
    h ▸ AlgEquiv.refl
  change _root_.minpoly F x = _root_.minpoly F y at h
  let f' := fc.symm.trans ((congr_f h).trans fd)
  let f := f'.liftNormal E
  rw [eq]
  refine' ⟨f.symm, _⟩
  dsimp only [AlgEquiv.smul_def]
  rw [AlgEquiv.symm_apply_eq]
  conv in x => rw [← IntermediateField.AdjoinSimple.algebraMap_gen F x]
  conv in y => rw [← IntermediateField.AdjoinSimple.algebraMap_gen F y]
  rw [AlgEquiv.liftNormal_commutes]
  apply congr_arg
  simp_rw [f', fc, fd, AlgEquiv.trans_apply, ← fd.symm_apply_eq,
    IntermediateField.adjoinRootEquivAdjoin_symm_apply_gen]
  rw [IntermediateField.adjoinRootEquivAdjoin_symm_apply_gen]
  have {px py} (h : px = py) : AdjoinRoot.root py = congr_f h (AdjoinRoot.root px) := by
    subst h; rfl
  exact this h

#align gal_conj_classes.minpoly.inj GalConjClasses.minpoly_inj

theorem minpoly_injective [Normal F E] : Function.Injective (@minpoly F _ E _ _) := fun _ _ =>
  minpoly_inj
#align gal_conj_classes.minpoly.injective GalConjClasses.minpoly_injective

theorem nodup_aroots_minpoly (c : GalConjClasses F E) : ((minpoly c).aroots E).Nodup :=
  nodup_roots c.separable_minpoly.map
#align gal_conj_classes.minpoly.nodup_aroots GalConjClasses.nodup_aroots_minpoly

theorem aeval_minpoly_iff [Normal F E] (x : E) (c : GalConjClasses F E) :
    aeval x (minpoly c) = 0 ↔ mk F x = c := by
  symm; constructor
  · rintro rfl; exact minpoly.aeval _ _
  intro h
  apply minpoly_inj
  rw [minpoly_mk, ← minpoly.eq_of_irreducible c.irreducible_minpoly h]
  rw [c.monic_minpoly.leadingCoeff, inv_one, map_one, mul_one]
#align gal_conj_classes.aeval_minpoly_iff GalConjClasses.aeval_minpoly_iff

theorem rootSet_minpoly_eq_orbit [Normal F E] (c : GalConjClasses F E) :
    (minpoly c).rootSet E = c.orbit := by
  ext x; rw [mem_orbit]
  simp_rw [mem_rootSet, aeval_minpoly_iff x c]
  simp [c.minpoly_ne_zero]
#align gal_conj_classes.root_set_minpoly_eq_orbit GalConjClasses.rootSet_minpoly_eq_orbit

theorem aroots_minpoly_eq_orbit_val [DecidableEq E] [Fintype (E ≃ₐ[F] E)] [Normal F E]
    (c : GalConjClasses F E) : (minpoly c).aroots E = c.orbit.toFinset.1 := by
  simp_rw [← rootSet_minpoly_eq_orbit, rootSet_def, Finset.toFinset_coe, Multiset.toFinset_val]
  symm; rw [Multiset.dedup_eq_self]
  exact nodup_roots ((separable_map _).mpr c.separable_minpoly)
#align gal_conj_classes.aroots_minpoly_eq_orbit_val GalConjClasses.aroots_minpoly_eq_orbit_val

theorem orbit_eq_mk_aroots_minpoly [DecidableEq E] [Fintype (E ≃ₐ[F] E)] [Normal F E]
    (c : GalConjClasses F E) :
    c.orbit.toFinset = ⟨(minpoly c).aroots E, c.nodup_aroots_minpoly⟩ := by
  simp only [aroots_minpoly_eq_orbit_val]
#align gal_conj_classes.orbit_eq_mk_aroots_minpoly GalConjClasses.orbit_eq_mk_aroots_minpoly

theorem minpoly.map_eq_prod [DecidableEq E] [Fintype (E ≃ₐ[F] E)] [Normal F E]
    (c : GalConjClasses F E) :
    (minpoly c).map (algebraMap F E) = ∏ x in c.orbit.toFinset, (X - C x) := by
  simp_rw [← rootSet_minpoly_eq_orbit, Finset.prod_eq_multiset_prod, rootSet_def,
    Finset.toFinset_coe, Multiset.toFinset_val]
  rw [Multiset.dedup_eq_self.mpr (nodup_roots _),
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Monic.map _ _)]
  · rw [splits_iff_card_roots.mp]; rw [splits_id_iff_splits]; exact c.splits_minpoly
  · exact c.monic_minpoly
  · exact c.separable_minpoly.map
#align gal_conj_classes.minpoly.map_eq_prod GalConjClasses.minpoly.map_eq_prod

end GalConjClasses

end GalConjClasses
