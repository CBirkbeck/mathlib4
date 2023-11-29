import Mathlib.Topology.Category.LightProfinite.IsLight

universe u

open CategoryTheory

namespace LightProfinite

instance {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) [X.IsLight] [Y.IsLight] :
    (Profinite.pullback f g).IsLight := by
  let i : Profinite.pullback f g ⟶ Profinite.of (X × Y) := ⟨fun x ↦ x.val, continuous_induced_dom⟩
  have : Mono i := by
    rw [Profinite.mono_iff_injective]
    exact Subtype.val_injective
  exact mono_light i

section Pullback

-- TODO: is there a way to avoid this code duplication from `Profinite`?

variable {X Y B : LightProfinite.{u}} (f : X ⟶ B) (g : Y ⟶ B)

noncomputable
def pullback : LightProfinite.{u} :=
  ofIsLight.{u} (Profinite.pullback.{u} (lightToProfinite.{u}.map f) (lightToProfinite.{u}.map g))

/-- The projection from the pullback to the first component. -/
def pullback.fst : pullback f g ⟶ X where
  toFun := fun ⟨⟨x, _⟩, _⟩ => x
  continuous_toFun := Continuous.comp continuous_fst continuous_subtype_val

/-- The projection from the pullback to the second component. -/
def pullback.snd : pullback f g ⟶ Y where
  toFun := fun ⟨⟨_, y⟩, _⟩ => y
  continuous_toFun := Continuous.comp continuous_snd continuous_subtype_val

@[reassoc]
lemma pullback.condition : pullback.fst f g ≫ f = pullback.snd f g ≫ g := by
  ext ⟨_, h⟩
  exact h

/--
Construct a morphism to the explicit pullback given morphisms to the factors
which are compatible with the maps to the base.
This is essentially the universal property of the pullback.
-/
def pullback.lift {Z : LightProfinite.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    Z ⟶ pullback f g where
  toFun := fun z => ⟨⟨a z, b z⟩, by apply_fun (· z) at w; exact w⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_prod_mk]
    exact ⟨a.continuous, b.continuous⟩

@[reassoc (attr := simp)]
lemma pullback.lift_fst {Z : LightProfinite.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    pullback.lift f g a b w ≫ pullback.fst f g = a := rfl

@[reassoc (attr := simp)]
lemma pullback.lift_snd {Z : LightProfinite.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    pullback.lift f g a b w ≫ pullback.snd f g = b := rfl

lemma pullback.hom_ext {Z : LightProfinite.{u}} (a b : Z ⟶ pullback f g)
    (hfst : a ≫ pullback.fst f g = b ≫ pullback.fst f g)
    (hsnd : a ≫ pullback.snd f g = b ≫ pullback.snd f g) : a = b := by
  ext z
  apply_fun (· z) at hfst hsnd
  apply Subtype.ext
  apply Prod.ext
  · exact hfst
  · exact hsnd

/-- The pullback cone whose cone point is the explicit pullback. -/
@[simps! pt π]
noncomputable def pullback.cone : Limits.PullbackCone f g :=
  Limits.PullbackCone.mk (pullback.fst f g) (pullback.snd f g) (pullback.condition f g)

/-- The explicit pullback cone is a limit cone. -/
@[simps! lift]
def pullback.isLimit : Limits.IsLimit (pullback.cone f g) :=
  Limits.PullbackCone.isLimitAux _
    (fun s => pullback.lift f g s.fst s.snd s.condition)
    (fun _ => pullback.lift_fst _ _ _ _ _)
    (fun _ => pullback.lift_snd _ _ _ _ _)
    (fun _ _ hm => pullback.hom_ext _ _ _ _ (hm .left) (hm .right))

end Pullback

instance {α : Type} [Fintype α] (X : α → Profinite.{u}) [∀ a, (X a).IsLight] :
    (Profinite.finiteCoproduct X).IsLight where
  countable_clopens := by
    refine @Function.Surjective.countable ((a : α) → {s : Set (X a) // IsClopen s}) _ inferInstance
      (fun f ↦ ⟨⋃ (a : α), Sigma.mk a '' (f a).val, ?_⟩) ?_
    · apply isClopen_iUnion_of_finite
      intro i
      exact ⟨isOpenMap_sigmaMk _ (f i).prop.1, isClosedMap_sigmaMk _ (f i).prop.2⟩
    · intro ⟨s, ⟨hso, hsc⟩⟩
      rw [isOpen_sigma_iff] at hso
      rw [isClosed_sigma_iff] at hsc
      refine ⟨fun i ↦ ⟨_, ⟨hso i, hsc i⟩⟩, ?_⟩
      simp only [Subtype.mk.injEq]
      ext ⟨i, xi⟩
      refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
      · rw [Set.mem_iUnion] at hx
        obtain ⟨_, _, hj, hxj⟩ := hx
        simpa [hxj] using hj
      · rw [Set.mem_iUnion]
        refine ⟨i, xi, (by simpa using hx), rfl⟩

section FiniteCoproduct

variable {α : Type} [Fintype α] (X : α → LightProfinite.{u})

/--
The coproduct of a finite family of objects in `LightProfinite`, constructed as the disjoint
union with its usual topology.
-/
noncomputable
def finiteCoproduct : LightProfinite :=
  ofIsLight (Profinite.finiteCoproduct fun a ↦ (X a).toProfinite)

/-- The inclusion of one of the factors into the explicit finite coproduct. -/
def finiteCoproduct.ι (a : α) : X a ⟶ finiteCoproduct X where
  toFun := (⟨a, ·⟩)
  continuous_toFun := continuous_sigmaMk (σ := fun a => (X a).toProfinite)

/--
To construct a morphism from the explicit finite coproduct, it suffices to
specify a morphism from each of its factors.
This is essentially the universal property of the coproduct.
-/
def finiteCoproduct.desc {B : LightProfinite.{u}} (e : (a : α) → (X a ⟶ B)) :
    finiteCoproduct X ⟶ B where
  toFun := fun ⟨a, x⟩ => e a x
  continuous_toFun := by
    apply continuous_sigma
    intro a
    exact (e a).continuous

@[reassoc (attr := simp)]
lemma finiteCoproduct.ι_desc {B : LightProfinite.{u}} (e : (a : α) → (X a ⟶ B)) (a : α) :
    finiteCoproduct.ι X a ≫ finiteCoproduct.desc X e = e a := rfl

lemma finiteCoproduct.hom_ext {B : LightProfinite.{u}} (f g : finiteCoproduct X ⟶ B)
    (h : ∀ a : α, finiteCoproduct.ι X a ≫ f = finiteCoproduct.ι X a ≫ g) : f = g := by
  ext ⟨a, x⟩
  specialize h a
  apply_fun (· x) at h
  exact h

/-- The coproduct cocone associated to the explicit finite coproduct. -/
@[simps]
noncomputable def finiteCoproduct.cocone : Limits.Cocone (Discrete.functor X) where
  pt := finiteCoproduct X
  ι := Discrete.natTrans fun ⟨a⟩ => finiteCoproduct.ι X a

/-- The explicit finite coproduct cocone is a colimit cocone. -/
@[simps]
def finiteCoproduct.isColimit : Limits.IsColimit (finiteCoproduct.cocone X) where
  desc := fun s => finiteCoproduct.desc _ fun a => s.ι.app ⟨a⟩
  fac := fun s ⟨a⟩ => finiteCoproduct.ι_desc _ _ _
  uniq := fun s m hm => finiteCoproduct.hom_ext _ _ _ fun a => by
    specialize hm ⟨a⟩
    ext t
    apply_fun (· t) at hm
    exact hm

end FiniteCoproduct
