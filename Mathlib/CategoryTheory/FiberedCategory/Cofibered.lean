/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.FiberedCategory.Cocartesian

/-!

# Cofibered categories

This file defines what it means for a functor `p : 𝒳 ⥤ 𝒮` to be (pre)cofibered.

## Main definitions

- `IsPreCofibered p` expresses `𝒳` is cofibered over `𝒮` via a functor `p : 𝒳 ⥤ 𝒮`, as in SGA VI.6.1.
This means that any morphism in the base `𝒮` can be lifted to a cartesian morphism in `𝒳`.

- `IsCofibered p` expresses `𝒳` is cofibered over `𝒮` via a functor `p : 𝒳 ⥤ 𝒮`, as in SGA VI.6.1.
This means that it is precofibered, and that the composition of any two cartesian morphisms is
cartesian.

In the literature one often sees the notion of a cofibered category defined as the existence of
strongly cartesian morphisms lying over any given morphism in the base. This is equivalent to the
notion above, and we give an alternate constructor `IsCofibered.of_exists_IsCocartesian'` for
constructing a cofibered category this way.

## Implementation

The constructor of `IsPreCofibered` is called `exists_IsCocartesian'`. The reason for the prime is that
when wanting to apply this condition, it is recommended to instead use the lemma
`exists_IsCocartesian` (without the prime), which is more applicable with respect to non-definitional
equalities.

## References
* [A. Grothendieck, M. Raynaud, *SGA 1*](https://arxiv.org/abs/math/0206203)

-/

universe v₁ v₂ u₁ u₂

open CategoryTheory Functor Category IsHomLift

namespace CategoryTheory

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- Definition of a precofibered category. -/
class Functor.IsPreCofibered (p : 𝒳 ⥤ 𝒮) : Prop where
  exists_IsCocartesian' {a : 𝒳} {R : 𝒮} (f : p.obj a ⟶ R) :
    ∃ (b : 𝒳) (φ : a ⟶ b), IsCocartesian p f φ

protected lemma IsPreCofibered.exists_IsCocartesian (p : 𝒳 ⥤ 𝒮) [p.IsPreCofibered] {a : 𝒳} {R S : 𝒮}
    (ha : p.obj a = S) (f : R ⟶ S) : ∃ (b : 𝒳) (φ : b ⟶ a), IsCocartesian p f φ := by
  subst ha; exact IsPreCofibered.exists_IsCocartesian' f

/-- Definition of a cofibered category.

See SGA 1 VI.6.1. -/
class Functor.IsCofibered (p : 𝒳 ⥤ 𝒮) extends IsPreCofibered p : Prop where
  comp {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T) {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c)
    [IsCocartesian p f φ] [IsCocartesian p g ψ] : IsCocartesian p (f ≫ g) (φ ≫ ψ)

instance (p : 𝒳 ⥤ 𝒮) [p.IsCofibered] {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T) {a b c : 𝒳} (φ : a ⟶ b)
    (ψ : b ⟶ c) [IsCocartesian p f φ] [IsCocartesian p g ψ] : IsCocartesian p (f ≫ g) (φ ≫ ψ) :=
  IsCofibered.comp f g φ ψ

namespace Functor.IsPreCofibered

open IsCocartesian

variable {p : 𝒳 ⥤ 𝒮} [IsPreCofibered p] {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S)

/-- Given a cofibered category `p : 𝒳 ⥤ 𝒫`, a morphism `f : R ⟶ S` and an object `a` lying over `S`,
then `pullbackObj` is the domain of some choice of a cartesian morphism lying over `f` with
codomain `a`. -/
noncomputable def pullbackObj : 𝒳 :=
  Classical.choose (IsPreCofibered.exists_IsCocartesian p ha f)

/-- Given a cofibered category `p : 𝒳 ⥤ 𝒫`, a morphism `f : R ⟶ S` and an object `a` lying over `S`,
then `pullbackMap` is a choice of a cartesian morphism lying over `f` with codomain `a`. -/
noncomputable def pullbackMap : pullbackObj ha f ⟶ a :=
  Classical.choose (Classical.choose_spec (IsPreCofibered.exists_IsCocartesian p ha f))

instance pullbackMap.IsCocartesian : IsCocartesian p f (pullbackMap ha f) :=
  Classical.choose_spec (Classical.choose_spec (IsPreCofibered.exists_IsCocartesian p ha f))

lemma pullbackObj_proj : p.obj (pullbackObj ha f) = R :=
  domain_eq p f (pullbackMap ha f)

end Functor.IsPreCofibered

namespace Functor.IsCofibered

open IsCocartesian IsPreCofibered

/-- In a cofibered category, any cartesian morphism is strongly cartesian. -/
instance isStronglyCartesian_of_IsCocartesian (p : 𝒳 ⥤ 𝒮) [p.IsCofibered] {R S : 𝒮} (f : R ⟶ S)
    {a b : 𝒳} (φ : a ⟶ b) [p.IsCocartesian f φ] : p.IsStronglyCocartesian f φ where
  universal_property' g φ' hφ' := by
    -- Let `ψ` be a cartesian arrow lying over `g`
    let ψ := pullbackMap (domain_eq p f φ) g
    -- Let `τ` be the map induced by the universal property of `ψ ≫ φ`.
    let τ := IsCocartesian.map p (g ≫ f) (ψ ≫ φ) φ'
    use τ ≫ ψ
    -- It is easily verified that `τ ≫ ψ` lifts `g` and `τ ≫ ψ ≫ φ = φ'`
    refine ⟨⟨inferInstance, by simp only [assoc, IsCocartesian.fac, τ]⟩, ?_⟩
    -- It remains to check that `τ ≫ ψ` is unique.
    -- So fix another lift `π` of `g` satisfying `π ≫ φ = φ'`.
    intro π ⟨hπ, hπ_comp⟩
    -- Write `π` as `π = τ' ≫ ψ` for some `τ'` induced by the universal property of `ψ`.
    rw [← fac p g ψ π]
    -- It remains to show that `τ' = τ`. This follows again from the universal property of `ψ`.
    congr 1
    apply map_uniq
    rwa [← assoc, IsCocartesian.fac]

/-- In a category which admits strongly cartesian pullbacks, any cartesian morphism is
strongly cartesian. This is a helper-lemma for the fact that admitting strongly cartesian pullbacks
implies being cofibered. -/
lemma isStronglyCartesian_of_exists_IsCocartesian (p : 𝒳 ⥤ 𝒮) (h : ∀ (a : 𝒳) (R : 𝒮)
    (f : R ⟶ p.obj a), ∃ (b : 𝒳) (φ : b ⟶ a), IsStronglyCocartesian p f φ) {R S : 𝒮} (f : R ⟶ S)
      {a b : 𝒳} (φ : a ⟶ b) [p.IsCocartesian f φ] : p.IsStronglyCocartesian f φ := by
  constructor
  intro c g φ' hφ'
  subst_hom_lift p f φ; clear a b R S
  -- Let `ψ` be a cartesian arrow lying over `g`
  obtain ⟨a', ψ, hψ⟩ := h _ _ (p.map φ)
  -- Let `τ' : c ⟶ a'` be the map induced by the universal property of `ψ`
  let τ' := IsStronglyCocartesian.map p (p.map φ) ψ (f':= g ≫ p.map φ) rfl φ'
  -- Let `Φ : a' ≅ a` be natural isomorphism induced between `φ` and `ψ`.
  let Φ := domainUniqueUpToIso p (p.map φ) φ ψ
  -- The map induced by `φ` will be `τ' ≫ Φ.hom`
  use τ' ≫ Φ.hom
  -- It is easily verified that `τ' ≫ Φ.hom` lifts `g` and `τ' ≫ Φ.hom ≫ φ = φ'`
  refine ⟨⟨by simp only [Φ]; infer_instance, ?_⟩, ?_⟩
  · simp [τ', Φ, IsStronglyCocartesian.map_uniq p (p.map φ) ψ rfl φ']
  -- It remains to check that it is unique. This follows from the universal property of `ψ`.
  intro π ⟨hπ, hπ_comp⟩
  rw [← Iso.comp_inv_eq]
  apply IsStronglyCocartesian.map_uniq p (p.map φ) ψ rfl φ'
  simp [hπ_comp, Φ]

/-- Alternate constructor for `IsCofibered`, a functor `p : 𝒳 ⥤ 𝒴` is cofibered if any diagram of the
form
```
          a
          -
          |
          v
R --f--> p(a)
```
admits a strongly cartesian lift `b ⟶ a` of `f`. -/
lemma of_exists_isStronglyCartesian {p : 𝒳 ⥤ 𝒮}
    (h : ∀ (a : 𝒳) (R : 𝒮) (f : R ⟶ p.obj a),
      ∃ (b : 𝒳) (φ : b ⟶ a), IsStronglyCocartesian p f φ) :
    IsCofibered p where
  exists_IsCocartesian' := by
    intro a R f
    obtain ⟨b, φ, hφ⟩ := h a R f
    refine ⟨b, φ, inferInstance⟩
  comp := fun R S T f g {a b c} φ ψ _ _ =>
    have : p.IsStronglyCocartesian f φ := isStronglyCartesian_of_exists_IsCocartesian p h _ _
    have : p.IsStronglyCocartesian g ψ := isStronglyCartesian_of_exists_IsCocartesian p h _ _
    inferInstance

/-- Given a diagram
```
                  a
                  -
                  |
                  v
T --g--> R --f--> S
```
we have an isomorphism `T ×_S a ≅ T ×_R (R ×_S a)` -/
noncomputable def pullbackPullbackIso {p : 𝒳 ⥤ 𝒮} [IsCofibered p]
    {R S T : 𝒮}  {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) (g : T ⟶ R) :
      pullbackObj ha (g ≫ f) ≅ pullbackObj (pullbackObj_proj ha f) g :=
  domainUniqueUpToIso p (g ≫ f) (pullbackMap (pullbackObj_proj ha f) g ≫ pullbackMap ha f)
    (pullbackMap ha (g ≫ f))

end Functor.IsCofibered

end CategoryTheory
