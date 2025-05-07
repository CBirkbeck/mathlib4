/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Descent data ...

-/

namespace CategoryTheory

open Opposite Limits

namespace Pseudofunctor

variable {C : Type*} [Category C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
  {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))

namespace DescentData'

variable {F sq}

section

variable {obj obj' : ∀ (i : ι), F.obj (.mk (op (X i)))}
  (hom : ∀ (i j : ι), (F.map (sq i j).p₁.op.toLoc).obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).obj (obj' j))

noncomputable def pullHom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q := by aesop_cat) (hf₂ : f₂ ≫ f i₂ = q := by aesop_cat) :
    (F.map f₁.op.toLoc).obj (obj i₁) ⟶ (F.map f₂.op.toLoc).obj (obj' i₂) :=
  let p : Y ⟶ (sq i₁ i₂).pullback := (sq i₁ i₂).isPullback.lift f₁ f₂ (by aesop)
  (F.mapComp' (sq i₁ i₂).p₁.op.toLoc p.op.toLoc f₁.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsPullback.lift_fst])).hom.app _ ≫
      (F.map (.toLoc p.op)).map (hom i₁ i₂) ≫
      (F.mapComp' (sq i₁ i₂).p₂.op.toLoc p.op.toLoc f₂.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsPullback.lift_snd])).inv.app _

@[reassoc]
lemma pullHom_eq ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (p : Y ⟶ (sq i₁ i₂).pullback)
    (hp₁ : p ≫ (sq i₁ i₂).p₁ = f₁) (hp₂ : p ≫ (sq i₁ i₂).p₂ = f₂) :
  pullHom hom q f₁ f₂ hf₁ hf₂ =
    (F.mapComp' (sq i₁ i₂).p₁.op.toLoc p.op.toLoc f₁.op.toLoc (by aesop)).hom.app _ ≫
      (F.map (.toLoc p.op)).map (hom i₁ i₂) ≫
      (F.mapComp' (sq i₁ i₂).p₂.op.toLoc p.op.toLoc f₂.op.toLoc (by aesop)).inv.app _ := by
  obtain rfl : p = (sq i₁ i₂).isPullback.lift f₁ f₂ (by rw [hf₁, hf₂]) := by
    apply (sq i₁ i₂).isPullback.hom_ext <;> aesop
  rfl

@[reassoc]
lemma pullHom_comp' ⦃Y Y' : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S) (hq : g ≫ q = q')
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom hom q' gf₁ gf₂ =
      (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by aesop)).hom.app (obj i₁) ≫
        (F.map g.op.toLoc).map (pullHom hom q f₁ f₂ hf₁ hf₂) ≫
          (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by aesop)).inv.app (obj' i₂) := by
  let p := (sq i₁ i₂).isPullback.lift f₁ f₂ (by aesop)
  dsimp
  rw [pullHom_eq _ _ _ _ _ _ p (by aesop) (by aesop),
    pullHom_eq _ _ _ _ _ _ (g ≫ p) (by aesop) (by aesop)]
  dsimp
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.mapComp'_hom_app_comp_mapComp'_hom_app_map_obj_assoc
    _ _ _ _ _ _ (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsPullback.lift_fst]) rfl
    (by rw [← Quiver.Hom.comp_toLoc, ← Quiver.Hom.comp_toLoc, ← op_comp, ← op_comp,
        Category.assoc, IsPullback.lift_fst, hgf₁])]
  rw [F.map_map_mapComp'_inv_app_comp_mapComp'_inv_app
    _ _ _ _ _ _ (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsPullback.lift_snd]) rfl
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hgf₂]),
    mapComp'_inv_naturality_assoc, Iso.hom_inv_id_app_assoc]

end

section

variable {obj : ∀ (i : ι), F.obj (.mk (op (X i)))}
  (hom : ∀ (i j : ι), (F.map (sq i j).p₁.op.toLoc).obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).obj (obj j))

@[simp]
lemma pullHom_p₁_p₂ (i : ι) :
    pullHom hom (sq i i).p (sq i i).p₁ (sq i i).p₂ (by simp) (by simp) = hom i i := by
  rw [pullHom_eq hom (sq i i).p (sq i i).p₁ (sq i i).p₂ (by simp) (by simp)
    (𝟙 _) (by simp)  (by simp)]
  simp [mapComp'_comp_id_hom_app, mapComp'_comp_id_inv_app]

lemma pullHom_self' (hom_self : ∀ i, pullHom hom (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (hg : g ≫ f i = q) :
    pullHom hom q g g hg hg = 𝟙 _ := by
  simp [pullHom_comp' hom g (f i) q hg (𝟙 (X i)) (𝟙 (X i)) (by simp) (by simp) g g
    (by simp) (by simp), hom_self]

variable {sq₃} in
@[reassoc]
lemma comp_pullHom' (hom_comp : ∀ (i₁ i₂ i₃ : ι),
    pullHom hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
    pullHom hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
    pullHom hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
    pullHom hom q f₁ f₂ ≫ pullHom hom q f₂ f₃ = pullHom hom q f₁ f₃ := by
  obtain ⟨φ, _, _, _⟩ := (sq₃ i₁ i₂ i₃).exists_lift f₁ f₂ f₃ q hf₁ hf₂ hf₃
  rw [pullHom_comp'_assoc hom φ (sq₃ i₁ i₂ i₃).p _ _ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂,
    pullHom_comp' hom φ (sq₃ i₁ i₂ i₃).p _ _ (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃,
    pullHom_comp' hom φ (sq₃ i₁ i₂ i₃).p _ _ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃,
    Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, hom_comp]
  all_goals aesop

end

end DescentData'

open DescentData' in

structure DescentData' where
  obj (i : ι) : F.obj (.mk (op (X i)))
  hom : ∀ (i j : ι), (F.map (sq i j).p₁.op.toLoc).obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).obj (obj j)
  hom_self : ∀ i, pullHom hom (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _
  hom_comp (i₁ i₂ i₃ : ι) :
    pullHom hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
    pullHom hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
    pullHom hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃

namespace DescentData'

variable {F sq sq₃}

@[simp]
lemma pullHom_self (D : F.DescentData' sq sq₃)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (hg : g ≫ f i = q) :
    pullHom D.hom q g g hg hg = 𝟙 _ :=
  pullHom_self' _ D.hom_self _ _ _

@[reassoc (attr := simp)]
lemma comp_pullHom (D : F.DescentData' sq sq₃)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
    pullHom D.hom q f₁ f₂ hf₁ hf₂ ≫ pullHom D.hom q f₂ f₃ hf₂ hf₃ =
      pullHom D.hom q f₁ f₃ hf₁ hf₃ :=
  comp_pullHom' _ D.hom_comp _ _ _ _ hf₁ hf₂ hf₃

@[ext]
structure Hom (D₁ D₂ : F.DescentData' sq sq₃) where
  hom (i : ι) : D₁.obj i ⟶ D₂.obj i
  comm (i₁ i₂ : ι) :
    (F.map (sq i₁ i₂).p₁.op.toLoc).map (hom i₁) ≫
      pullHom D₂.hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ =
    pullHom D₁.hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ ≫
      (F.map (sq i₁ i₂).p₂.op.toLoc).map (hom i₂) := by aesop_cat

attribute [reassoc (attr := simp)] Hom.comm

@[simps]
def Hom.id (D : F.DescentData' sq sq₃) : Hom D D where
  hom _ := 𝟙 _

@[simps]
def Hom.comp {D₁ D₂ D₃ : F.DescentData' sq sq₃} (f : Hom D₁ D₂) (g : Hom D₂ D₃) : Hom D₁ D₃ where
  hom i := f.hom i ≫ g.hom i

instance : Category (F.DescentData' sq sq₃) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext]
lemma hom_ext {D₁ D₂ : F.DescentData' sq sq₃} {f g : D₁ ⟶ D₂}
    (h : ∀ i, f.hom i = g.hom i) : f = g :=
  Hom.ext (funext h)

@[reassoc, simp]
lemma comp_hom {D₁ D₂ D₃ : F.DescentData' sq sq₃} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) (i : ι) :
    (f ≫ g).hom i = f.hom i ≫ g.hom i :=
  rfl

@[simp]
lemma id_hom (D : F.DescentData' sq sq₃) (i : ι) :
    Hom.hom (𝟙 D) i = 𝟙 _ :=
  rfl

@[simps!]
noncomputable def descentData (D : F.DescentData' sq sq₃) : F.DescentData f :=
  .mk' D.obj
    (fun _ _ _ _ _ _ _ _ ↦ pullHom D.hom _ _ _ (by aesop) (by aesop))
    (fun _ _ _ _ _ hq _ _ _ _ _ _ _ _ hgf₁ hgf₂ ↦
      pullHom_comp' _ _ _ _ hq _ _ _ _ _ _ hgf₁ hgf₂)
    (by simp) (by simp)

end DescentData'

noncomputable def DescentData'.toDescentData : F.DescentData' sq sq₃ ⥤ F.DescentData f where
  obj D := D.descentData
  map φ :=
    { hom i := φ.hom i
      comm := sorry }
  map_id := by intros; ext; dsimp
  map_comp := by intros; ext; dsimp

end Pseudofunctor

end CategoryTheory
