/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# (Co)limits on the (strict) Grothendieck Construction

* Shows that colimits of functors on the Grothendieck construction are colimits of
  "fibered colimits", i.e. of applying the colimit to each fiber of the functor.

-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {F : C ⥤ Cat}
variable {H : Type u₂} [Category.{v₂} H]
variable (G : Grothendieck F ⥤ H)

@[simps]
def Grothendieck.ιNatTrans {X Y : C} (f : X ⟶ Y) : ι F X ⟶ F.map f ⋙ ι F Y where
  app d := ⟨f, 𝟙 _⟩
  naturality _ _ _ := by
    simp only [ι, Functor.comp_obj, Functor.comp_map]
    exact Grothendieck.ext _ _ (by simp) (by simp [eqToHom_map])

def Grothendieck.coherence {X Y : Grothendieck F} (hF : X = Y) :
    eqToHom hF = { base := eqToHom (by subst hF; rfl), fiber := eqToHom (by subst hF; simp) } := by
  subst hF
  rfl

namespace Limits

lemma colimit.ι_coherence (F : C ⥤ H) [HasColimit F] {c c' : C} (hc : c = c') :
    colimit.ι F c = eqToHom (by subst hc; rfl) ≫ colimit.ι F c' := by
  subst hc
  simp

noncomputable section

variable [∀ {X Y : C} (f : X ⟶ Y), HasColimit (F.map f ⋙ Grothendieck.ι F Y ⋙ G)]

local instance : ∀ X, HasColimit (Grothendieck.ι F X ⋙ G) :=
  fun X => hasColimitOfIso (F := F.map (𝟙 _) ⋙ Grothendieck.ι F X ⋙ G) <|
    (Functor.leftUnitor (Grothendieck.ι F X ⋙ G)).symm ≪≫
    (isoWhiskerRight (eqToIso (F.map_id X).symm) (Grothendieck.ι F X ⋙ G))

/-- A functor taking a colimit on each fiber of a functor `G : Grothendieck F ⥤ H`. -/
@[simps]
def fiberwiseColimit : C ⥤ H where
  obj X := colimit (Grothendieck.ι F X ⋙ G)
  map {X Y} f := colimMap (whiskerRight (Grothendieck.ιNatTrans f) G ≫
    (Functor.associator _ _ _).hom) ≫ colimit.pre (Grothendieck.ι F Y ⋙ G) (F.map f)
  map_id X := by
    ext d
    simp only [Functor.comp_obj, Grothendieck.ιNatTrans, Grothendieck.ι_obj_base,
      Grothendieck.ι_obj_fiber, ι_colimMap_assoc, NatTrans.comp_app, whiskerRight_app,
      Functor.associator_hom_app, Category.comp_id, colimit.ι_pre]
    conv_rhs =>
      rw [colimit.ι_coherence (Grothendieck.ι F X ⋙ G) (c' := (F.map (𝟙 X)).obj d) (by simp)]
    rw [← eqToHom_map G (by simp), Grothendieck.coherence]
    rfl
  map_comp {X Y Z} f g := by
    ext d
    simp only [Functor.comp_obj, Grothendieck.ιNatTrans, Grothendieck.ι_obj_base,
      Grothendieck.ι_obj_fiber, ι_colimMap_assoc, NatTrans.comp_app, whiskerRight_app,
      Functor.associator_hom_app, Category.comp_id, colimit.ι_pre, Category.assoc,
      colimit.ι_pre_assoc]
    rw [← Category.assoc, ← G.map_comp]
    conv_rhs =>
      rw [colimit.ι_coherence (Grothendieck.ι F Z ⋙ G) (c' := (F.map (f ≫ g)).obj d) (by simp)]
    rw [← Category.assoc, ← eqToHom_map G (by simp), ← G.map_comp, Grothendieck.coherence]
    congr 2
    fapply Grothendieck.ext
    · simp only [Grothendieck.ι_obj_base, Cat.comp_obj, eqToHom_refl, Grothendieck.ι_obj_fiber,
        Category.assoc, Grothendieck.comp_base, Category.comp_id]
    · simp only [Grothendieck.ι_obj_base, Cat.comp_obj, eqToHom_refl, Grothendieck.ι_obj_fiber,
        Cat.id_obj, Grothendieck.comp_base, Category.comp_id, Grothendieck.comp_fiber,
        Functor.map_id]
      conv_rhs => enter [2, 1]; rw [eqToHom_map (F.map (𝟙 Z))]
      conv_rhs => rw [eqToHom_trans, eqToHom_trans]

/-- Every functor `G : Grothendieck F ⥤ H` induces a natural transformation from `G` to the
composition of the forgetful functor on `Grothendieck F` with the fiberwise colimit on `G`. -/
@[simps]
def natTransIntoForgetCompFiberwiseColimit :
    G ⟶ Grothendieck.forget F ⋙ fiberwiseColimit G where
  app X := colimit.ι (Grothendieck.ι F X.base ⋙ G) X.fiber
  naturality _ _ f := by
    simp only [Functor.comp_obj, Grothendieck.forget_obj, fiberwiseColimit_obj, Functor.comp_map,
      Grothendieck.forget_map, fiberwiseColimit_map, Grothendieck.ιNatTrans,
      Grothendieck.ι_obj_base, Grothendieck.ι_obj_fiber, ι_colimMap_assoc, NatTrans.comp_app,
      whiskerRight_app, Functor.associator_hom_app, Category.comp_id, colimit.ι_pre]
    rw [← colimit.w (Grothendieck.ι F _ ⋙ G) f.fiber]
    simp only [← Category.assoc, Functor.comp_obj, Functor.comp_map, ← G.map_comp]
    congr 2
    apply Grothendieck.ext <;> simp

variable {G} in
/-- A cocone on a functor `G : Grothendieck F ⥤ H` induces a cocone on the fiberwise colimit
on `G`. -/
@[simps]
def coconeFiberwiseColimitOfCocone (c : Cocone G) : Cocone (fiberwiseColimit G) where
  pt := c.pt
  ι := { app := fun X => colimit.desc _ (c.whisker (Grothendieck.ι F X)),
         naturality := fun _ _ f => by dsimp; ext; simp }

variable {G} in
/-- If `c` is a colimit cocone on `G : Grockendieck F ⥤ H`, then the induced cocone on the
fiberwise colimit on `G` is a colimit cocone, too. -/
def isColimitCoconeFiberwiseColimitOfCocone {c : Cocone G} (hc : IsColimit c) :
    IsColimit (coconeFiberwiseColimitOfCocone c) where
  desc s := hc.desc <| Cocone.mk s.pt <| natTransIntoForgetCompFiberwiseColimit G ≫
    whiskerLeft (Grothendieck.forget F) s.ι
  fac s c := by dsimp; ext; simp
  uniq s m hm := hc.hom_ext fun X => by
    have := hm X.base
    simp only [Functor.const_obj_obj, IsColimit.fac, NatTrans.comp_app, Functor.comp_obj,
      Grothendieck.forget_obj, fiberwiseColimit_obj, natTransIntoForgetCompFiberwiseColimit_app,
      whiskerLeft_app]
    simp only [fiberwiseColimit_obj, coconeFiberwiseColimitOfCocone_pt, Functor.const_obj_obj,
      coconeFiberwiseColimitOfCocone_ι_app] at this
    simp [← this, Grothendieck.ι]

section

variable [HasColimit G]

local instance hasColimitFiberwiseColimit : HasColimit (fiberwiseColimit G) where
  exists_colimit := ⟨⟨_, isColimitCoconeFiberwiseColimitOfCocone (colimit.isColimit _)⟩⟩

/-- For every functor `G` on the Grothendieck construction `Grothendieck F`, taking its colimit
is isomorphic to first taking the fiberwise colimit and then the colimit of the resulting fucntor.
-/
def colimitFiberwiseColimitIso [HasColimit G] :
    colimit (fiberwiseColimit G) ≅ colimit G :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit (fiberwiseColimit G))
    (isColimitCoconeFiberwiseColimitOfCocone (colimit.isColimit _))

end

section

variable [∀ {X Y : C} (f : X ⟶ Y), HasColimit (F.map f ⋙ Grothendieck.ι F Y ⋙ G)]

def coconeOfFiberwiseCocone (c : Cocone (fiberwiseColimit G)) : Cocone G where
  pt := c.pt
  ι := { app := fun X => colimit.ι (Grothendieck.ι F X.base ⋙ G) X.fiber ≫ c.ι.app X.base
         naturality := fun {X Y} ⟨f, g⟩ => by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
          rw [← Category.assoc, ← c.w f, ← Category.assoc]
          simp only [fiberwiseColimit_obj, fiberwiseColimit_map, Grothendieck.ιNatTrans,
            Functor.comp_obj, Grothendieck.ι_obj_base, Grothendieck.ι_obj_fiber, ι_colimMap_assoc,
            NatTrans.comp_app, whiskerRight_app, Functor.associator_hom_app, Category.comp_id,
            colimit.ι_pre]
          rw [← colimit.w _ g, ← Category.assoc, Functor.comp_map, ← G.map_comp]
          congr <;> simp }

/-- We can infer that a functor `G : Grothendieck F ⥤ H`, with `F : C ⥤ Cat`, has a colimit from
the fact that each of its fibers has a colimit and that these fiberwise colimits, as a functor
`C ⥤ H` have a colimit. -/
def hasColimitOfHasFiberwiseColimitOfHasBaseColimit
    [∀ {X Y : C} (f : X ⟶ Y), HasColimit (F.map f ⋙ Grothendieck.ι F Y ⋙ G)]
    [HasColimit (fiberwiseColimit G)] : HasColimit G where
  exists_colimit := ⟨⟨_, _⟩⟩

end

end

end Limits

end CategoryTheory
