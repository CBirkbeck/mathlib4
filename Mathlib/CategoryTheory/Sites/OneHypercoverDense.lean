import Mathlib.CategoryTheory.Sites.DenseSubsite

universe w v₀ v v' u₀ u u'

namespace CategoryTheory

open Category Limits

variable {C₀ : Type u₀} {C : Type u} [Category.{v₀} C₀] [Category.{v} C]

namespace Sieve

variable {I : Type*} {X : C} {Y : I → C} {f : ∀ i, Y i ⟶ X} {W : C} {g : W ⟶ X}
  (hg : ofArrows Y f g)

def ofArrows.exists : ∃ (i : I) (h : W ⟶ Y i), g = h ≫ f i := by
  obtain ⟨_, h, _, H, rfl⟩ := hg
  cases' H with i
  exact ⟨i, h, rfl⟩

noncomputable def ofArrows.i : I := (ofArrows.exists hg).choose
noncomputable def ofArrows.h : W ⟶ Y (i hg) := (ofArrows.exists hg).choose_spec.choose
noncomputable def ofArrows.fac : g = h hg ≫ f (i hg) :=
  (ofArrows.exists hg).choose_spec.choose_spec

end Sieve

namespace Functor

variable (F : C₀ ⥤ C) (J₀ : GrothendieckTopology C₀)
  (J : GrothendieckTopology C) {A : Type u'} [Category.{v'} A]

structure PreOneHypercoverDenseData (S : C) where
  I₀ : Type w
  X (i : I₀) : C₀
  f (i : I₀) : F.obj (X i) ⟶ S
  I₁ (i₁ i₂ : I₀) : Type w
  Y ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : C₀
  p₁ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₁
  p₂ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₂
  w ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : F.map (p₁ j) ≫ f i₁ = F.map (p₂ j) ≫ f i₂

namespace PreOneHypercoverDenseData

attribute [reassoc] w

variable {F}

variable {X : C} (data : F.PreOneHypercoverDenseData X)

@[simps]
def toPreOneHypercover : PreOneHypercover X where
  I₀ := data.I₀
  X i := F.obj (data.X i)
  f i := data.f i
  I₁ := data.I₁
  Y _ _ j := F.obj (data.Y j)
  p₁ _ _ j := F.map (data.p₁ j)
  p₂ _ _ j := F.map (data.p₂ j)
  w := data.w

/-- The sigma type of all `data.I₁ i₁ i₂` for `⟨i₁, i₂⟩ : data.I₀ × data.I₀`. -/
abbrev I₁' : Type w := Sigma (fun (i : data.I₀ × data.I₀) => data.I₁ i.1 i.2)

@[simps]
def multicospanIndex (P : C₀ᵒᵖ ⥤ A) : MulticospanIndex A where
  L := data.I₀
  R := data.I₁'
  fstTo j := j.1.1
  sndTo j := j.1.2
  left i := P.obj (Opposite.op (data.X i))
  right j := P.obj (Opposite.op (data.Y j.2))
  fst j := P.map ((data.p₁ j.2).op)
  snd j := P.map ((data.p₂ j.2).op)

@[simps]
def multicospanMap {P Q : C₀ᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (data.multicospanIndex P).multicospan ⟶ (data.multicospanIndex Q).multicospan where
  app x := match x with
    | WalkingMulticospan.left i => f.app _
    | WalkingMulticospan.right j => f.app _
  naturality := by
    rintro (i₁|j₁) (i₂|j₂) (_|_)
    all_goals simp

@[simps]
def multicospanMapIso {P Q : C₀ᵒᵖ ⥤ A} (e : P ≅ Q) :
    (data.multicospanIndex P).multicospan ≅ (data.multicospanIndex Q).multicospan where
  hom := data.multicospanMap e.hom
  inv := data.multicospanMap e.inv

@[simps]
def sieve₁₀ {i₁ i₂ : data.I₀} {W₀ : C₀} (p₁ : W₀ ⟶ data.X i₁) (p₂ : W₀ ⟶ data.X i₂) :
    Sieve W₀ where
  arrows Z₀ g := ∃ (j : data.I₁ i₁ i₂) (h : Z₀ ⟶ data.Y j),
    g ≫ p₁ = h ≫ data.p₁ j ∧ g ≫ p₂ = h ≫ data.p₂ j
  downward_closed := by
    rintro Z Z' g ⟨j, h, fac₁, fac₂⟩ φ
    exact ⟨j, φ ≫ h, by simpa using φ ≫= fac₁, by simpa using φ ≫= fac₂⟩

end PreOneHypercoverDenseData

structure OneHypercoverDenseData (S : C) extends PreOneHypercoverDenseData.{w} F S where
  mem₀ : toPreOneHypercoverDenseData.toPreOneHypercover.sieve₀ ∈ J S
  mem₁₀ (i₁ i₂ : I₀) ⦃W₀ : C₀⦄ (p₁ : W₀ ⟶ X i₁) (p₂ : W₀ ⟶ X i₂)
    (w : F.map p₁ ≫ f i₁ = F.map p₂ ≫ f i₂) :
    toPreOneHypercoverDenseData.sieve₁₀ p₁ p₂ ∈ J₀ W₀

class IsOneHypercoverDense : Prop where
  nonempty_oneHypercoverDenseData (X : C) :
    Nonempty (OneHypercoverDenseData.{w} F J₀ J X)

variable [IsOneHypercoverDense.{w} F J₀ J]

noncomputable def oneHypercoverDenseData (X : C) : F.OneHypercoverDenseData J₀ J X :=
  (IsOneHypercoverDense.nonempty_oneHypercoverDenseData X).some

lemma isDenseSubsite_of_isOneHypercoverDense [F.IsLocallyFull J] [F.IsLocallyFaithful J]
    (h : ∀ {X₀ : C₀} {S₀ : Sieve X₀},
      Sieve.functorPushforward F S₀ ∈ J.sieves (F.obj X₀) ↔ S₀ ∈ J₀.sieves X₀) :
    IsDenseSubsite J₀ J F where
  isCoverDense' := ⟨fun X ↦ by
    refine J.superset_covering ?_ ((F.oneHypercoverDenseData J₀ J X).mem₀)
    rintro Y _ ⟨_, a, _, h, rfl⟩
    cases' h with i
    exact ⟨{ fac := rfl}⟩⟩
  functorPushforward_mem_iff := h

variable [IsDenseSubsite J₀ J F]

namespace OneHypercoverDenseData

variable {F J₀ J}
variable {X : C} (data : F.OneHypercoverDenseData J₀ J X)

lemma mem₁ (i₁ i₂ : data.I₀) {W : C} (p₁ : W ⟶ F.obj (data.X i₁)) (p₂ : W ⟶ F.obj (data.X i₂))
    (w : p₁ ≫ data.f i₁ = p₂ ≫ data.f i₂) : data.toPreOneHypercover.sieve₁ p₁ p₂ ∈ J W := by
  have : F.Full := sorry
  let data₁ := F.oneHypercoverDenseData J₀ J W
  let R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ W⦄, data₁.toPreOneHypercover.sieve₀.arrows f → Sieve Y :=
    fun Y f hf => ((data.sieve₁₀ (F.preimage (data₁.f (Sieve.ofArrows.i hf) ≫ p₁))
      (F.preimage (data₁.f (Sieve.ofArrows.i hf) ≫ p₂))).functorPushforward F).pullback
        (Sieve.ofArrows.h hf)
  refine J.superset_covering ?_ (J.bind_covering data₁.mem₀ (R := R) ?_)
  · rintro Y f ⟨T, a, b, hb, ha, rfl⟩
    obtain ⟨X₀, c, d, hc, fac⟩ := ha
    obtain ⟨j, e, w₁, w₂⟩ := hc
    refine ⟨j, d ≫ F.map e, ?_, ?_⟩
    · rw [Sieve.ofArrows.fac hb, assoc, assoc, assoc]
      dsimp
      rw [← F.map_comp, ← w₁, F.map_comp, F.map_preimage, reassoc_of% fac]
    · rw [Sieve.ofArrows.fac hb, assoc, assoc, assoc]
      dsimp
      rw [← F.map_comp, ← w₂, F.map_comp, F.map_preimage, reassoc_of% fac]
  · intro Y f hf
    apply J.pullback_stable
    apply (IsDenseSubsite.coverPreserving J₀ J F).cover_preserve
    apply data.mem₁₀ i₁ i₂
    simp [w]

@[simps toPreOneHypercover]
def toOneHypercover {X : C} (data : F.OneHypercoverDenseData J₀ J X) :
    J.OneHypercover X where
  toPreOneHypercover := data.toPreOneHypercover
  mem₀ := data.mem₀
  mem₁ := data.mem₁

end OneHypercoverDenseData

end Functor

end CategoryTheory
