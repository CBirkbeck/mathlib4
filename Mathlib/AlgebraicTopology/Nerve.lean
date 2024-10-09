/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Mario Carneiro, Emily Riehl
-/
import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.ComposableArrows
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Basic


/-!

# The nerve of a category

This file provides the definition of the nerve of a category `C`,
which is a simplicial set `nerve C` (see [goerss-jardine-2009], Example I.1.4).
By definition, the type of `n`-simplices of `nerve C` is `ComposableArrows C n`,
which is the category `Fin (n + 1) ⥤ C`.

It also proves that `nerve C` is 2-coskeletal, meaning that the canonical map to the right
Kan extension of its restriction to the category of 2-truncated simplicial sets is an isomorphism.

In more detail:

* For a category `C`, `nerveRightExtension C` uses the identity natural transformation to exhibit
`nerve C`  as a right extension of its restriction to the 2-truncated simplex category along
`(Truncated.inclusion (n := 2)).op`.

* For each natural number `n`, `nerveRightExtension.coneAt C n` defines a cone with summit
`nerve C _[n]` over the diagram
`(StructuredArrow.proj (op [n]) (Truncated.inclusion (n := 2)).op ⋙ nerveFunctor₂.obj C)`
indexed by the category `StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op.`

* `isPointwiseRightKanExtensionAt C n` proves that this cone is a limit cone, and thus
`nerveRightExtension C` is a pointwise right Kan extension.

* It follows that the map induced by the identity defines a natural isomorphism
`cosk2Iso : nerveFunctor.{u, u} ≅ nerveFunctor₂.{u, u} ⋙ Truncated.cosk 2`.


## References
* [Paul G. Goerss, John F. Jardine, *Simplicial Homotopy Theory*][goerss-jardine-2009]

-/

open CategoryTheory.Category Simplicial SSet SimplexCategory Opposite CategoryTheory.Functor
  CategoryTheory.Limits

universe v u

namespace CategoryTheory

/-- The nerve of a category -/
@[simps]
def nerve (C : Type u) [Category.{v} C] : SSet.{max u v} where
  obj Δ := ComposableArrows C (Δ.unop.len)
  map f x := x.whiskerLeft (SimplexCategory.toCat.map f.unop)

instance {C : Type*} [Category C] {Δ : SimplexCategoryᵒᵖ} : Category ((nerve C).obj Δ) :=
  (inferInstance : Category (ComposableArrows C (Δ.unop.len)))

/-- The nerve of a category, as a functor `Cat ⥤ SSet` -/
@[simps]
def nerveFunctor : Cat ⥤ SSet where
  obj C := nerve C
  map F := { app := fun Δ => (F.mapComposableArrows _).obj }

namespace Nerve

variable {C : Type*} [Category C] {n : ℕ}

lemma δ₀_eq {x : nerve C _[n + 1]} : (nerve C).δ (0 : Fin (n + 2)) x = x.δ₀ := rfl

end Nerve

/-- The essential data of the nerve functor is contained in the 2-truncation, which is
recorded by the composite functor `nerveFunctor₂`.-/
def nerveFunctor₂ : Cat.{v, u} ⥤ SSet.Truncated 2 := nerveFunctor ⋙ truncation 2

/-- The essential data of the nerve of a category `C` is contained in the 2-truncation, which is
recorded by the 2-truncated simplicial set `nerve₂ C`.-/
abbrev nerve₂ (C : Type*) [Category C] : SSet.Truncated 2 := nerveFunctor₂.obj (Cat.of C)

theorem nerve₂_restrictedNerve (C : Type*) [Category C] :
    (Truncated.inclusion (n := 2)).op ⋙ nerve C = nerve₂ C := rfl

/-- By construction, `nerve₂ C` is the restriction of `nerve C` along the inclusion of the
2-truncated simplex category. -/
def nerve₂RestrictedIso (C : Type*) [Category C] :
    (Truncated.inclusion (n := 2)).op ⋙ nerve C ≅ nerve₂ C := Iso.refl _

namespace Nerve

/-- The identity natural transformation exhibits `nerve C`  as a right extension of its restriction
to the 2-truncated simplex category along `(Truncated.inclusion (n := 2)).op`.-/
def nerveRightExtension (C : Cat) :
    RightExtension (Truncated.inclusion (n := 2)).op (nerveFunctor₂.obj C) :=
  RightExtension.mk
    (nerveFunctor.obj C) (𝟙 ((Truncated.inclusion (n := 2)).op ⋙ nerveFunctor.obj C))

/-- The natural transformation in nerveRightExtension C defines a cone with summit
`nerve C _[n]` over the diagram
`(StructuredArrow.proj (op [n]) (Truncated.inclusion (n := 2)).op ⋙ nerveFunctor₂.obj C)`
indexed by the category StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op. -/
def nerveRightExtension.coneAt (C : Cat) (n : ℕ) :
    Cone
      (StructuredArrow.proj
        (op ([n] : SimplexCategory)) (Truncated.inclusion (n := 2)).op ⋙ nerveFunctor₂.obj C) :=
  RightExtension.coneAt (nerveRightExtension C) (op [n])

section

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

set_option quotPrecheck false
local macro:max (priority := high) "[" n:term "]₂" : term =>
  `((⟨SimplexCategory.mk $n, by decide⟩ : SimplexCategory.Truncated 2))

/-- The map [0] ⟶ [n] with image i.-/
private
def pt {n} (i : Fin (n + 1)) : ([0] : SimplexCategory) ⟶ [n] := SimplexCategory.const _ _ i

/-- The object of StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op corresponding to
`pt i`. -/
private
def pt' {n} (i : Fin (n + 1)) : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op :=
  .mk (Y := op [0]₂) (.op (pt i))

/-- The map [1] ⟶ [n] with image k : i ⟶ j.-/
private
def ar {n} {i j : Fin (n+1)} (k : i ⟶ j) : [1] ⟶ [n] := mkOfLe _ _ k.le

/-- The object of StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op corresponding to
`ar k`. -/
private
def ar' {n} {i j : Fin (n+1)} (k : i ⟶ j) :
    StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op :=
  .mk (Y := op [1]₂) (.op (ar k))

/-- The object of StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op corresponding to
ar Fin.hom_succ i. -/
private
def ar'succ {n} (i : Fin n) : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op :=
  ar' (Fin.hom_succ i)

theorem ran.lift.eq {C : Cat} {n}
    (s : Cone (StructuredArrow.proj (op [n])
      (Truncated.inclusion (n := 2)).op ⋙ nerveFunctor₂.obj C))
    (x : s.pt) {i j} (k : i ⟶ j) :
    (s.π.app (CategoryTheory.Nerve.pt' i) x).obj 0 =
    (s.π.app (CategoryTheory.Nerve.ar' k) x).obj 0 := by
  have hi := congr_fun (s.π.naturality <|
      StructuredArrow.homMk (f := ar' k) (f' := pt' i)
        (.op (SimplexCategory.const _ _ 0)) <| by
        apply Quiver.Hom.unop_inj
        ext z; revert z; intro (0 : Fin 1); rfl) x
  simp at hi
  rw [hi]
  exact rfl

theorem ran.lift.eq₂ {C : Cat} {n}
    (s : Cone (StructuredArrow.proj (op [n])
      (Truncated.inclusion (n := 2)).op ⋙ nerveFunctor₂.obj C))
    (x : s.pt) {i j} (k : i ⟶ j) :
    (s.π.app (CategoryTheory.Nerve.pt' j) x).obj 0 =
    (s.π.app (CategoryTheory.Nerve.ar' k) x).obj 1 := by
  have hj := congr_fun (s.π.naturality <|
      StructuredArrow.homMk (f := ar' k) (f' := pt' j)
        (.op (SimplexCategory.const _ _ 1)) <| by
        apply Quiver.Hom.unop_inj
        ext z; revert z; intro (0 : Fin 1); rfl) x
  simp at hj
  rw [hj]
  exact rfl

/-- This is the value at x : s.pt of the lift of the cone s through the cone with summit nerve
C _[n].-/
private
noncomputable def ran.lift {C : Cat} {n}
    (s : Cone (StructuredArrow.proj (op [n])
      (Truncated.inclusion (n := 2)).op ⋙ nerveFunctor₂.obj C))
    (x : s.pt) : nerve C _[n] := by
  fapply ComposableArrows.mkOfObjOfMapSucc
  · exact fun i ↦ s.π.app (pt' i) x |>.obj 0
  · exact fun i ↦ eqToHom (ran.lift.eq ..) ≫ (s.π.app (ar'succ i) x).map' 0 1 ≫
      eqToHom (ran.lift.eq₂ ..).symm

/-- A second less efficient construction of the above with more information about arbitrary maps.-/
private
def ran.lift' {C : Cat} {n}
    (s : Cone (StructuredArrow.proj (op [n])
      (Truncated.inclusion (n := 2)).op ⋙ nerveFunctor₂.obj C))
    (x : s.pt) : nerve C _[n] where
    obj i := s.π.app (pt' i) x |>.obj 0
    map {i j} (k : i ⟶ j) :=
      eqToHom (ran.lift.eq ..) ≫
      ((s.π.app (ar' k) x).map' 0 1) ≫
      eqToHom (ran.lift.eq₂ ..).symm
    map_id i := by
      have nat := congr_fun (s.π.naturality <|
        StructuredArrow.homMk (f := pt' i) (f' := ar' (𝟙 i))
          (.op (SimplexCategory.const _ _ 0)) <| by
            apply Quiver.Hom.unop_inj
            ext z; revert z; intro | 0 | 1 => rfl) x
      dsimp at nat ⊢
      refine ((conj_eqToHom_iff_heq' ..).2 ?_).symm
      have := congr_arg_heq (·.map' 0 1) nat
      simp [nerveFunctor₂, truncation, SimplicialObject.truncation] at this
      refine HEq.trans ?_ this.symm
      conv => rhs; rhs; equals 𝟙 _ => apply Subsingleton.elim
      simp; rfl
    map_comp := fun {i j k} f g => by
      let tri {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : [2] ⟶ [n] :=
          mkOfLeComp _ _ _ f.le g.le
      let tri' {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) :
        StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op :=
          .mk (Y := op [2]₂) (.op (tri f g))
      let facemap₂ {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : tri' f g ⟶ ar' f := by
        refine StructuredArrow.homMk (.op (SimplexCategory.δ 2)) (Quiver.Hom.unop_inj ?_)
        ext z; revert z;
        simp [ar']
        intro | 0 | 1 => rfl
      let facemap₀ {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : (tri' f g) ⟶ (ar' g) := by
        refine StructuredArrow.homMk (.op (SimplexCategory.δ 0)) (Quiver.Hom.unop_inj ?_)
        ext z; revert z;
        simp [ar']
        intro | 0 | 1 => rfl
      let facemap₁ {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : (tri' f g) ⟶ ar' (f ≫ g) := by
        refine StructuredArrow.homMk (.op (SimplexCategory.δ 1)) (Quiver.Hom.unop_inj ?_)
        ext z; revert z;
        simp [ar']
        intro | 0 | 1 => rfl
      let tri₀ {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : tri' f g ⟶ pt' i := by
        refine StructuredArrow.homMk (.op (SimplexCategory.const [0] _ 0)) (Quiver.Hom.unop_inj ?_)
        ext z; revert z
        simp [ar']
        intro | 0 => rfl
      let tri₁ {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : tri' f g ⟶ pt' j := by
        refine StructuredArrow.homMk (.op (SimplexCategory.const [0] _ 1)) (Quiver.Hom.unop_inj ?_)
        ext z; revert z
        simp [ar']
        intro | 0 => rfl
      let tri₂ {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : tri' f g ⟶ pt' k := by
        refine StructuredArrow.homMk (.op (SimplexCategory.const [0] _ 2)) (Quiver.Hom.unop_inj ?_)
        ext z; revert z
        simp [ar']
        intro | 0 => rfl
      apply eq_of_heq
      simp only [Fin.isValue, ← assoc, eqToHom_trans_assoc,
        heq_eqToHom_comp_iff, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
      simp [assoc]
      have h'f := congr_arg_heq (·.map' 0 1) (congr_fun (s.π.naturality (facemap₂ f g)) x)
      have h'g := congr_arg_heq (·.map' 0 1) (congr_fun (s.π.naturality (facemap₀ f g)) x)
      have h'fg := congr_arg_heq (·.map' 0 1) (congr_fun (s.π.naturality (facemap₁ f g)) x)
      refine ((heq_comp ?_ ?_ ?_ h'f ((eqToHom_comp_heq_iff ..).2 h'g)).trans ?_).symm
      · exact (ran.lift.eq ..).symm.trans congr($(congr_fun (s.π.naturality (tri₀ f g)) x).obj 0)
      · exact (ran.lift.eq₂ ..).symm.trans congr($(congr_fun (s.π.naturality (tri₁ f g)) x).obj 0)
      · exact (ran.lift.eq₂ ..).symm.trans congr($(congr_fun (s.π.naturality (tri₂ f g)) x).obj 0)
      refine (h'fg.trans ?_).symm
      simp [nerveFunctor₂, truncation, SimplicialObject.truncation, ← map_comp]; congr 1

theorem ran.lift.map {C : Cat} {n}
    (s : Cone (StructuredArrow.proj (op [n])
      (Truncated.inclusion (n := 2)).op ⋙ nerveFunctor₂.obj C))
    (x : s.pt) {i j} (k : i ⟶ j) :
    (ran.lift s x).map k =
      eqToHom (ran.lift.eq ..) ≫
      ((s.π.app (ar' k) x).map' 0 1) ≫
      eqToHom (ran.lift.eq₂ ..).symm := by
  have : ran.lift s x = ran.lift' s x := by
    fapply ComposableArrows.ext
    · intro; rfl
    · intro i hi
      dsimp only [CategoryTheory.Nerve.ran.lift]
      rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
      rw [eqToHom_refl, eqToHom_refl, id_comp, comp_id]; rfl
  exact eq_of_heq (congr_arg_heq (·.map k) this)

/-- An object `j : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op` defines a morphism
`Fin (jlen+1) -> Fin(n+1)`. This calculates the image of `i : Fin(jlen+1)`;
we might think of this as j(i). -/
private
def strArr.homEv {n}
    (j : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op)
    (i : Fin ((unop ((Truncated.inclusion (n := 2)).op.obj
      ((StructuredArrow.proj (op [n]) (Truncated.inclusion (n := 2)).op).obj j))).len + 1)) :
    Fin (n + 1) := (SimplexCategory.Hom.toOrderHom j.hom.unop) i

/-- This is the unique arrow in `StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op` from
j to pt' of the j(i) calculated above. This is used to prove that ran.lift defines a factorization
on objects.-/
private
def fact.obj.arr {n}
    (j : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op)
    (i : Fin ((unop ((Truncated.inclusion (n := 2)).op.obj
      ((StructuredArrow.proj (op [n]) (Truncated.inclusion (n := 2)).op).obj j))).len + 1)) :
      j ⟶ (pt' (strArr.homEv j i)) :=
  StructuredArrow.homMk (.op (SimplexCategory.const _ _ i)) <| by
    apply Quiver.Hom.unop_inj
    ext z; revert z; intro | 0 => rfl

/-- An object `j : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op` defines a morphism
`Fin (jlen+1) -> Fin(n+1)`. This calculates the image of i.succ : Fin(jlen+1); we might think of
this as j(i.succ). -/
private
def strArr.homEvSucc {n}
    (j : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op)
    (i : Fin (unop j.right).1.len) :
    Fin (n + 1) := (SimplexCategory.Hom.toOrderHom j.hom.unop) i.succ

/-- The unique arrow (strArr.homEv j i.castSucc) ⟶ (strArr.homEvSucc j i) in Fin(n+1). -/
private
def strArr.homEv.map {n}
    (j : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op)
    (i : Fin (unop j.right).1.len) :
    strArr.homEv j i.castSucc ⟶ strArr.homEvSucc j i :=
  (Monotone.functor (j.hom.unop.toOrderHom).monotone).map (Fin.hom_succ i)

/-- This is the unique arrow in `StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op` from j
to ar' of the map just
constructed. This is used to prove that ran.lift defines a factorization on maps.-/
private
def fact.map.arr {n}
    (j : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op)
    (i : Fin (unop j.right).1.len) : j ⟶ ar' (strArr.homEv.map j i) := by
  fapply StructuredArrow.homMk
  · exact .op (mkOfSucc i : [1] ⟶ [(unop j.right).1.len])
  · apply Quiver.Hom.unop_inj
    ext z; revert z
    intro
    | 0 => rfl
    | 1 => rfl

noncomputable def isPointwiseRightKanExtensionAt (C : Cat) (n : ℕ) :
    RightExtension.IsPointwiseRightKanExtensionAt
      (nerveRightExtension C) (op ([n] : SimplexCategory)) := by
  show IsLimit _
  unfold nerveRightExtension RightExtension.coneAt
  simp only [nerveFunctor_obj, RightExtension.mk_left, nerve_obj, SimplexCategory.len_mk,
    const_obj_obj, op_obj, comp_obj, StructuredArrow.proj_obj, whiskeringLeft_obj_obj,
    RightExtension.mk_hom, NatTrans.id_app, comp_id]
  exact {
    lift := fun s x => ran.lift s x
    fac := by
      intro s j
      ext x
      refine have obj_eq := ?_; ComposableArrows.ext obj_eq ?_
      · exact fun i ↦ congrArg (·.obj 0) <| congr_fun (s.π.naturality (fact.obj.arr j i)) x
      · intro i hi
        simp only [StructuredArrow.proj_obj, op_obj, const_obj_obj, comp_obj, nerveFunctor_obj,
          RightExtension.mk_left, nerve_obj, SimplexCategory.len_mk, whiskeringLeft_obj_obj,
          RightExtension.mk_hom, NatTrans.id_app, const_obj_map, Functor.comp_map,
          StructuredArrow.proj_map, StructuredArrow.mk_right, Fin.zero_eta, Fin.isValue, Fin.mk_one,
          ComposableArrows.map', types_comp_apply, nerve_map, SimplexCategory.toCat_map, id_eq,
          Int.reduceNeg, Int.Nat.cast_ofNat_Int, ComposableArrows.whiskerLeft_obj,
          Monotone.functor_obj, ComposableArrows.mkOfObjOfMapSucc_obj,
          ComposableArrows.whiskerLeft_map] at obj_eq ⊢
        rw [ran.lift.map]
        have nat := congr_fun (s.π.naturality (fact.map.arr j (Fin.mk i hi))) x
        have := congr_arg_heq (·.map' 0 1) <| nat
        refine (conj_eqToHom_iff_heq' _ _ _ _).2 ?_
        simpa only [Int.reduceNeg, StructuredArrow.proj_obj, op_obj, id_eq, Int.Nat.cast_ofNat_Int,
          Fin.mk_one, Fin.isValue, ComposableArrows.map', Int.reduceAdd, Int.reduceSub,
          Fin.zero_eta, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    uniq := by
      intro s lift' fact'
      ext x
      unfold ran.lift pt' pt ar'succ ar' ar
      fapply ComposableArrows.ext
      · exact fun i ↦ (congrArg (·.obj 0) <| congr_fun (fact'
          (StructuredArrow.mk (Y := op [0]₂) ([0].const [n] i).op)) x)
      · intro i hi
        rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
        have eq := congr_fun (fact' (ar'succ (Fin.mk i hi))) x
        simp at eq ⊢
        exact (conj_eqToHom_iff_heq' _ _ _ _).2 (congr_arg_heq (·.hom) <| eq)
  }
end

noncomputable def isPointwiseRightKanExtension (C : Cat) :
    RightExtension.IsPointwiseRightKanExtension (nerveRightExtension C) :=
  fun Δ => isPointwiseRightKanExtensionAt C Δ.unop.len

noncomputable def isPointwiseRightKanExtension.isUniversal (C : Cat) :
    CostructuredArrow.IsUniversal (nerveRightExtension C) :=
  RightExtension.IsPointwiseRightKanExtension.isUniversal (isPointwiseRightKanExtension C)

theorem isRightKanExtension (C : Cat) :
    (nerveRightExtension C).left.IsRightKanExtension (nerveRightExtension C).hom :=
  RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    (isPointwiseRightKanExtension C)

/-- The natural map from a nerve. -/
noncomputable def cosk2NatTrans : nerveFunctor.{u, v} ⟶
    nerveFunctor₂ ⋙ ran (Truncated.inclusion (n := 2)).op :=
  whiskerLeft nerveFunctor (coskAdj 2).unit

noncomputable def cosk2RightExtension.hom (C : Cat.{v, u}) :
    nerveRightExtension C ⟶
      RightExtension.mk _
        ((Truncated.inclusion (n := 2)).op.ranCounit.app
          ((Truncated.inclusion (n := 2)).op ⋙ nerveFunctor.obj C)) :=
  CostructuredArrow.homMk (cosk2NatTrans.app C)
    ((coskAdj 2).left_triangle_components (nerveFunctor.obj C))

instance cosk2RightExtension.hom_isIso (C : Cat) :
    IsIso (cosk2RightExtension.hom C) :=
  isIso_of_isTerminal (isPointwiseRightKanExtension.isUniversal C)
    (((Truncated.inclusion (n := 2)).op.ran.obj
      ((Truncated.inclusion (n := 2)).op ⋙ nerveFunctor.obj C)).isUniversalOfIsRightKanExtension
        ((Truncated.inclusion (n := 2)).op.ranCounit.app
          ((Truncated.inclusion (n := 2)).op ⋙ nerveFunctor.obj C)))
      (cosk2RightExtension.hom C)

noncomputable def cosk2RightExtension.component.hom.iso (C : Cat.{v, u}) :
    nerveRightExtension C ≅
      RightExtension.mk _
        ((Truncated.inclusion (n := 2)).op.ranCounit.app
          ((Truncated.inclusion (n := 2)).op ⋙ nerveFunctor.obj C)) :=
  asIso (cosk2RightExtension.hom C)

noncomputable def cosk2NatIso.component (C : Cat.{v, u}) :
    nerveFunctor.obj C ≅ (Truncated.cosk 2).obj (nerveFunctor₂.obj C) :=
  (CostructuredArrow.proj
    ((whiskeringLeft _ _ _).obj (Truncated.inclusion (n := 2)).op)
      ((Truncated.inclusion (n := 2)).op ⋙ nerveFunctor.obj C)).mapIso
      (cosk2RightExtension.component.hom.iso C)

/-- It follows that we have a natural isomorphism between `nerveFunctor` and
`nerveFunctor ⋙ Truncated.cosk 2` whose components are the isomorphisms just established. -/
noncomputable def cosk2Iso : nerveFunctor.{u, u} ≅
    nerveFunctor₂.{u, u} ⋙ Truncated.cosk 2 := by
  apply NatIso.ofComponents cosk2NatIso.component _
  have := cosk2NatTrans.{u, u}.naturality
  exact cosk2NatTrans.naturality

end Nerve

end CategoryTheory
