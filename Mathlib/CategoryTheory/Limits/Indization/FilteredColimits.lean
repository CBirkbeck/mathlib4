/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.FunctorToTypes
import Mathlib.CategoryTheory.Limits.Indization.IndObject
import Mathlib.Logic.Small.Set

/-!
# Ind-objects are closed under filtered colimits
-/

universe v v₁ u u₁

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section Good

variable {I : Type v} [SmallCategory I] [IsFiltered I] (F : I ⥤ Cᵒᵖ ⥤ Type v)
  (hF : ∀ i, IsIndObject (F.obj i))

variable {J : Type v} [SmallCategory J] [FinCategory J]

variable (G : J ⥤ CostructuredArrow yoneda (colimit F))

theorem step₁ : Nonempty <| limit <|
  G.op ⋙
    (CostructuredArrow.toOver yoneda (colimit F)).op ⋙
    yoneda.toPrefunctor.obj (Over.mk (𝟙 (colimit F))) := by
  refine ⟨Types.Limit.mk _ (fun j => Over.mkIdTerminal.from _) ?_⟩
  intros
  simp only [Functor.comp_obj, Functor.op_obj, Opposite.unop_op, yoneda_obj_obj, Functor.comp_map,
    Functor.op_map, Quiver.Hom.unop_op, yoneda_obj_map, IsTerminal.comp_from]

theorem step₂ : Nonempty <| limit <|
  G.op ⋙ (CostructuredArrow.toOver yoneda (colimit F)).op ⋙
    yoneda.obj (colimit.cocone F).toOver.pt :=
  step₁ _ _

theorem step₃ : Nonempty <| limit <|
  G.op ⋙ (CostructuredArrow.toOver yoneda (colimit F)).op ⋙
    yoneda.obj (colimit ((colimit.cocone F).toCostructuredArrow ⋙ CostructuredArrow.toOver _ _)) := by
  refine Nonempty.map ?_ (step₂ F G)
  let t : (colimit.cocone F).toOver.pt ≅ (colimit ((colimit.cocone F).toCostructuredArrow ⋙ CostructuredArrow.toOver _ _)) :=
    IsColimit.coconePointUniqueUpToIso (Over.isColimitToOver (colimit.isColimit F)) (colimit.isColimit _)
  let t' := whiskerLeft (G.op ⋙ (CostructuredArrow.toOver yoneda (colimit F)).op) (yoneda.map t.hom)
  exact limMap t'

section Interchange

variable {K : Type v} [SmallCategory K] (H : K ⥤ Over (colimit.cocone F).pt)

noncomputable def fullInterchange₂ :
  G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op ⋙
    colimit (H ⋙ yoneda) ≅
    colimit (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj (G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op)) := by
  refine isoWhiskerLeft _ (isoWhiskerLeft _ (colimitIsoFlipCompColim _)) ≪≫ ?_
  refine ?_ ≪≫ (colimitIsoFlipCompColim _).symm
  rfl

noncomputable def composedInterchange :
  G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op ⋙
    yoneda.obj (colimit H) ≅
    colimit (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj (G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op)) :=
  (isoWhiskerLeft G.op (CostructuredArrow.toOverCompYonedaColimit H)) ≪≫ fullInterchange₂ F G H

theorem full_interchange [IsFiltered K] (h : Nonempty <| limit <|
    G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op ⋙ yoneda.obj (colimit H)) :
    ∃ k, Nonempty <| limit <| G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op ⋙ yoneda.obj (H.obj k) := by
  obtain ⟨t⟩ := h
  let t₂ := limMap (composedInterchange F G H).hom t
  let t₃ := (colimitLimitIsoMax
  (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj (G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op)).flip
  ).inv t₂
  obtain ⟨k, y, -⟩ := Types.jointly_surjective'.{v, max u v} t₃
  refine ⟨k, ⟨?_⟩⟩
  let z := (limitObjIsoLimitCompEvaluation
  (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj (G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op)).flip
   k).hom y
  let y := flipCompEvaluation
    (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj (G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op))
    k
  exact (lim.mapIso y).hom z

end Interchange

noncomputable def myBetterFunctor : I ⥤ Jᵒᵖ ⥤ Type (max u v) :=
  (colimit.cocone F).toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙ yoneda ⋙
    (whiskeringLeft _ _ _).obj (G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op)

theorem step₇ : ∃ i, Nonempty <| limit <| (myBetterFunctor F G).obj i :=
  full_interchange F G ((colimit.cocone F).toCostructuredArrow ⋙ CostructuredArrow.toOver _ _)
  (step₃ _ _)

noncomputable def i : I := (step₇ F G).choose

theorem step₈ : Nonempty <| limit <| (myBetterFunctor F G).obj (i F G) :=
  (step₇ F G).choose_spec

noncomputable def pointwiseFunctor : Jᵒᵖ ⥤ Type (max u v) :=
  G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op ⋙
    yoneda.obj (Over.mk <| colimit.ι F (i F G))

noncomputable def betterIsoPointwise : (myBetterFunctor F G).obj (i F G) ≅ pointwiseFunctor F G :=
  Iso.refl _

theorem step₉ : Nonempty <| limit <| pointwiseFunctor F G :=
  step₈ F G

abbrev K : Type v := (hF (i F G)).presentation.I

noncomputable def Kc : Cocone ((hF (i F G)).presentation.F ⋙ yoneda) :=
  (hF (i F G)).presentation.cocone

noncomputable def Kcl : IsColimit (Kc F hF G) :=
  (hF (i F G)).presentation.coconeIsColimit

lemma Kcpt : (Kc F hF G).pt = F.obj (i F G) := rfl

noncomputable def mappedCone := (Over.map (colimit.ι F (i F G))).mapCocone (Kc F hF G).toOver

lemma mappedCone_pt : (mappedCone F hF G).pt = Over.mk (colimit.ι F (i F G)) :=
  rfl

noncomputable def isColimitTo : IsColimit (Kc F hF G).toOver :=
  Over.isColimitToOver <| Kcl F hF G

noncomputable def isColimitMappedCone : IsColimit (mappedCone F hF G) :=
  isColimitOfPreserves (Over.map (colimit.ι F (i F G))) (isColimitTo F hF G)

noncomputable def indexing : (hF (i F G)).presentation.I ⥤ Over (colimit.cocone F).pt :=
  (Cocone.toCostructuredArrow (Kc F hF G) ⋙
        CostructuredArrow.toOver ((IsIndObject.presentation _).F ⋙ yoneda) (Kc F hF G).pt) ⋙
      Over.map (colimit.ι F (i F G))

theorem step₁₀ : Nonempty <| limit <|
    G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op ⋙
      yoneda.obj (colimit (indexing F hF G)) := by
  refine Nonempty.map ?_ (step₉ F G)
  let y := IsColimit.coconePointUniqueUpToIso (isColimitMappedCone F hF G) (colimit.isColimit _)
  let y' := whiskerLeft (G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op)
    (yoneda.map y.hom)
  exact limMap y'

theorem step₁₁ : ∃ k, Nonempty <| limit <| G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op ⋙
    yoneda.obj ((indexing F hF G).obj k) :=
  full_interchange F G (indexing F hF G) (step₁₀ _ _ _)

noncomputable def k : K F hF G := (step₁₁ F hF G).choose

theorem step₁₂ : Nonempty <| limit <| G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op ⋙
    yoneda.obj ((indexing F hF G).obj (k F hF G)) :=
  (step₁₁ F hF G).choose_spec

theorem bla : ((Over.map (colimit.ι F (i F G))).toPrefunctor.obj
          ((CostructuredArrow.toOver ((IsIndObject.presentation _).F ⋙ yoneda) (Kc F hF G).pt).toPrefunctor.obj
            (CostructuredArrow.mk ((Kc F hF G).ι.app (k F hF G))))) =
          (CostructuredArrow.toOver yoneda (colimit F)).toPrefunctor.obj
    ((CostructuredArrow.pre (IsIndObject.presentation _).F yoneda (colimit F)).toPrefunctor.obj
      ((CostructuredArrow.map (colimit.ι F (i F G))).toPrefunctor.obj
        (CostructuredArrow.mk ((Kc F hF G).ι.app (k F hF G))))) := by
  rfl

end Good

theorem isIndObject_colimit (I : Type v) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Cᵒᵖ ⥤ Type v) (hF : ∀ i, IsIndObject (F.obj i)) : IsIndObject (colimit F) := by
  suffices IsFiltered (CostructuredArrow yoneda (colimit F)) by
    refine (isIndObject_iff _).mpr ⟨this, ?_⟩
    have : ∀ i, ∃ (s : Set (CostructuredArrow yoneda (F.obj i))) (_ : Small.{v} s),
        ∀ i, ∃ j ∈ s, Nonempty (i ⟶ j) :=
      fun i => (hF i).finallySmall.exists_small_weakly_terminal_set
    choose s hs j hjs hj using this
    refine finallySmall_of_small_weakly_terminal_set
      (⋃ i, (CostructuredArrow.map (colimit.ι F i)).obj '' (s i)) (fun A => ?_)
    obtain ⟨i, y, hy⟩ := FunctorToTypes.jointly_surjective'.{v, v} F _ (yonedaEquiv A.hom)
    let y' : CostructuredArrow yoneda (F.obj i) := CostructuredArrow.mk (yonedaEquiv.symm y)
    obtain ⟨x⟩ := hj _ y'
    refine ⟨(CostructuredArrow.map (colimit.ι F i)).obj (j i y'), ?_, ⟨?_⟩⟩
    · simp only [Set.mem_iUnion, Set.mem_image]
      refine ⟨i, j i y', hjs _ _, rfl⟩
    · refine ?_ ≫ (CostructuredArrow.map (colimit.ι F i)).map x
      refine CostructuredArrow.homMk (𝟙 A.left) (yonedaEquiv.injective ?_)
      simp [-EmbeddingLike.apply_eq_iff_eq, hy, yonedaEquiv_comp]

  refine IsFiltered.iff_nonempty_limit.mpr (fun {J _ _} G => ?_)
  have t := step₁₂ F hF G
  dsimp [indexing] at t
  rw [bla F hF G] at t
  let q := natIsoOfFullyFaithful.{v, max u v} (CostructuredArrow.toOver yoneda (colimit F))
  obtain ⟨t'⟩ := Nonempty.map (limMap (isoWhiskerLeft G.op (q _)).hom) t
  let v := preservesLimitIso uliftFunctor.{max u v, v} (G.op ⋙
    yoneda.toPrefunctor.obj
        ((CostructuredArrow.pre (IsIndObject.presentation _).F yoneda (colimit F)).toPrefunctor.obj
          ((CostructuredArrow.map (colimit.ι F (i F G))).toPrefunctor.obj
            (CostructuredArrow.mk ((Kc F hF G).ι.app (k F hF G))))))
  let t₂ := v.inv t'
  exact ⟨_, ⟨t₂.down⟩⟩

end CategoryTheory.Limits
