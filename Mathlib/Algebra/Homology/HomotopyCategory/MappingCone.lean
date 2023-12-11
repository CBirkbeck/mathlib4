/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Algebra.Homology.HomotopyCofiber

/-! # The mapping cone of a morphism of cochain complexes

In this file, we study the homotopy cofiber `HomologicalComplex.homotopyCofiber`
of a morphism `φ : F ⟶ G` of cochain complexes indexed by `ℤ`. In this case,
we redefine it as `CochainComplex.mappingCone φ`. The API involves definitions
`mappingCone.inl φ : Cochain F (mappingCone φ) (-1)`,
`mappingCone.inr φ : G ⟶ mappingCone φ`,
`mappingCone.fst φ : Cocycle (mappingCone φ) F 1` and
`mappingCone.snd φ : Cochain (mappingCone φ) G 0`.

-/

open CategoryTheory Limits

variable {C : Type*} [Category C] [Preadditive C]

namespace CochainComplex

open HomologicalComplex

section

variable {ι : Type*} [AddRightCancelSemigroup ι] [One ι]
    {F G : CochainComplex C ι} (φ : F ⟶ G)

instance [∀ p, HasBinaryBiproduct (F.X (p + 1)) (G.X p)] :
    HasHomotopyCofiber φ where
  hasBinaryBiproduct := by
    rintro i _ rfl
    infer_instance

end

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

instance : DecidableRel (ComplexShape.up ℤ).Rel := fun _ _ => by dsimp; infer_instance

variable [HasHomotopyCofiber φ]

/-- The mapping cone of a morphism of cochain complexes indexed by `ℤ`. -/
noncomputable def mappingCone := homotopyCofiber φ

namespace mappingCone

open HomComplex

/-- The left inclusion in the mapping cone, as a cochain of degree `-1`. -/
noncomputable def inl : Cochain F (mappingCone φ) (-1) :=
  Cochain.mk (fun p q hpq => homotopyCofiber.inlX φ p q  (by dsimp; linarith))

/-- The right inclusion in the mapping cone. -/
noncomputable def inr : G ⟶ mappingCone φ := homotopyCofiber.inr φ

/-- The first projection from the mapping cone, as a cocyle of degree `1`. -/
noncomputable def fst : Cocycle (mappingCone φ) F 1 :=
  Cocycle.mk (Cochain.mk (fun p q hpq => homotopyCofiber.fstX φ p q hpq)) 2 (by linarith) (by
    ext p _ rfl
    simp [δ_v 1 2 (by linarith) _ p (p + 2) (by linarith) (p + 1) (p + 1) (by linarith) rfl,
      homotopyCofiber.d_fstX φ p (p + 1) (p + 2) rfl, mappingCone,
      show Int.negOnePow 2 = 1 by rfl])

/-- The second projection from the mapping cone, as a cochain of degree `0`. -/
noncomputable def snd : Cochain (mappingCone φ) G 0 :=
  Cochain.ofHoms (homotopyCofiber.sndX φ)

@[reassoc (attr := simp)]
lemma inl_v_fst_v (p q : ℤ) (hpq : q + 1 = p) :
    (inl φ).v p q (by rw [← hpq, add_neg_cancel_right]) ≫
      (fst φ : Cochain (mappingCone φ) F 1).v q p hpq = 𝟙 _ := by
  simp [inl, fst]

@[reassoc (attr := simp)]
lemma inl_v_snd_v (p q : ℤ) (hpq : p + (-1) = q) :
    (inl φ).v p q hpq ≫ (snd φ).v q q (add_zero q) = 0 := by
  simp [inl, snd]

@[reassoc (attr := simp)]
lemma inr_f_fst_v (p q : ℤ) (hpq : p + 1 = q) :
    (inr φ).f p ≫ (fst φ).1.v p q hpq = 0 := by
  simp [inr, fst]

@[reassoc (attr := simp)]
lemma inr_f_snd_v (p : ℤ) :
    (inr φ).f p ≫ (snd φ).v p p (add_zero p) = 𝟙 _ := by
  simp [inr, snd]

@[simp]
lemma inl_fst :
    (inl φ).comp (fst φ).1 (neg_add_self 1) = Cochain.ofHom (𝟙 F) := by
  ext p
  simp [Cochain.comp_v _ _ (neg_add_self 1) p (p-1) p rfl (by linarith)]

@[simp]
lemma inl_snd :
    (inl φ).comp (snd φ) (add_zero (-1)) = 0 := by
  ext p q hpq
  simp [Cochain.comp_v _ _ (add_zero (-1)) p q q (by linarith) (by linarith)]

@[simp]
lemma inr_fst :
    (Cochain.ofHom (inr φ)).comp (fst φ).1 (zero_add 1) = 0 := by
  ext p q hpq
  simp [Cochain.comp_v _ _ (zero_add 1) p p q (by linarith) (by linarith)]

@[simp]
lemma inr_snd :
    (Cochain.ofHom (inr φ)).comp (snd φ) (zero_add 0) = Cochain.ofHom (𝟙 G) := by aesop_cat

/-! In order to obtain identities of cochains involving `inl`, `inr`, `fst` and `snd`,
it is often convenient to use an `ext` lemma, and use simp lemmas like `inl_v_f_fst_v`,
but it is sometimes possible to get identities of cochains by using rewrites of
identities of cochains like `inl_fst`. Then, similarly as in category theory,
if we associate to right the composition as much as possible, it is also interesting
to have `reassoc` variants of lemmas, like `inl_fst_assoc`. -/

@[simp]
lemma inl_fst_assoc {K : CochainComplex C ℤ} {d e : ℤ} (γ : Cochain F K d) (he : 1 + d = e) :
    (inl φ).comp ((fst φ).1.comp γ he) (by rw [← he, neg_add_cancel_left]) = γ := by
  rw [← Cochain.comp_assoc _ _ _ (neg_add_self 1) (by linarith) (by linarith), inl_fst,
    Cochain.id_comp]

@[simp]
lemma inl_snd_assoc {K : CochainComplex C ℤ} {d e f : ℤ} (γ : Cochain G K d)
    (he : 0 + d = e) (hf : -1 + e = f) :
    (inl φ).comp ((snd φ).comp γ he) hf = 0 := by
  obtain rfl : e = d := by linarith
  rw [← Cochain.comp_assoc_of_second_is_zero_cochain, inl_snd, Cochain.zero_comp]

@[simp]
lemma inr_fst_assoc {K : CochainComplex C ℤ} {d e f : ℤ} (γ : Cochain F K d)
    (he : 1 + d = e) (hf : 0 + e = f) :
    (Cochain.ofHom (inr φ)).comp ((fst φ).1.comp γ he) hf = 0 := by
  obtain rfl : e = f := by linarith
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, inr_fst, Cochain.zero_comp]

@[simp]
lemma inr_snd_assoc {K : CochainComplex C ℤ} {d e : ℤ} (γ : Cochain G K d) (he : 0 + d = e) :
    (Cochain.ofHom (inr φ)).comp ((snd φ).comp γ he) (by simp only [← he, zero_add]) = γ := by
  obtain rfl : d = e := by linarith
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, inr_snd, Cochain.id_comp]

lemma ext_to (i j : ℤ) (hij : i + 1 = j) {A : C} {f g : A ⟶ (mappingCone φ).X i}
    (h₁ : f ≫ (fst φ).1.v i j hij = g ≫ (fst φ).1.v i j hij)
    (h₂ : f ≫ (snd φ).v i i (add_zero i) = g ≫ (snd φ).v i i (add_zero i)) :
    f = g :=
  homotopyCofiber.ext_to_X φ i j hij h₁ (by simpa [snd] using h₂)

lemma ext_to_iff (i j : ℤ) (hij : i + 1 = j) {A : C} (f g : A ⟶ (mappingCone φ).X i) :
    f = g ↔ f ≫ (fst φ).1.v i j hij = g ≫ (fst φ).1.v i j hij ∧
      f ≫ (snd φ).v i i (add_zero i) = g ≫ (snd φ).v i i (add_zero i) := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    exact ext_to φ i j hij h₁ h₂

lemma ext_from (i j : ℤ) (hij : j + 1 = i) {A : C} {f g : (mappingCone φ).X j ⟶ A}
    (h₁ : (inl φ).v i j (by linarith) ≫ f = (inl φ).v i j (by linarith) ≫ g)
    (h₂ : (inr φ).f j ≫ f = (inr φ).f j ≫ g) :
    f = g :=
  homotopyCofiber.ext_from_X φ i j hij h₁ h₂

lemma ext_from_iff (i j : ℤ) (hij : j + 1 = i) {A : C} (f g : (mappingCone φ).X j ⟶ A) :
    f = g ↔ (inl φ).v i j (by linarith) ≫ f = (inl φ).v i j (by linarith) ≫ g ∧
      (inr φ).f j ≫ f = (inr φ).f j ≫ g := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    exact ext_from φ i j hij h₁ h₂

lemma ext_cochain_to_iff (i j : ℤ) (hij : i + 1 = j)
    {K : CochainComplex C ℤ} {γ₁ γ₂ : Cochain K (mappingCone φ) i} :
    γ₁ = γ₂ ↔ γ₁.comp (fst φ).1 hij = γ₂.comp (fst φ).1 hij ∧
      γ₁.comp (snd φ) (add_zero i) = γ₂.comp (snd φ) (add_zero i) := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    ext p q hpq
    rw [ext_to_iff φ q (q + 1) rfl]
    replace h₁ := Cochain.congr_v h₁ p (q + 1) (by linarith)
    replace h₂ := Cochain.congr_v h₂ p q hpq
    simp only [Cochain.comp_v _ _ _ p q (q + 1) hpq rfl] at h₁
    simp only [Cochain.comp_zero_cochain_v] at h₂
    exact ⟨h₁, h₂⟩

lemma ext_cochain_from_iff (i j : ℤ) (hij : i + 1 = j)
    {K : CochainComplex C ℤ} {γ₁ γ₂ : Cochain (mappingCone φ) K j} :
    γ₁ = γ₂ ↔
      (inl φ).comp γ₁ (show _ = i by linarith) = (inl φ).comp γ₂ (by linarith) ∧
        (Cochain.ofHom (inr φ)).comp γ₁ (zero_add j) =
          (Cochain.ofHom (inr φ)).comp γ₂ (zero_add j) := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    ext p q hpq
    rw [ext_from_iff φ (p + 1) p rfl]
    replace h₁ := Cochain.congr_v h₁ (p + 1) q (by linarith)
    replace h₂ := Cochain.congr_v h₂ p q (by linarith)
    simp only [Cochain.comp_v (inl φ) _ _ (p + 1) p q (by linarith) hpq] at h₁
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at h₂
    refine' ⟨h₁, h₂⟩

lemma id :
    (fst φ).1.comp (inl φ) (add_neg_self 1) +
      (snd φ).comp (Cochain.ofHom (inr φ)) (add_zero 0) = Cochain.ofHom (𝟙 _) := by
  simp [ext_cochain_from_iff φ (-1) 0 (neg_add_self 1)]

lemma id_X (p q : ℤ) (hpq : p + 1 = q) :
    (fst φ).1.v p q hpq ≫ (inl φ).v q p (by linarith) +
      (snd φ).v p p (add_zero p) ≫ (inr φ).f p = 𝟙 ((mappingCone φ).X p) := by
  simpa only [Cochain.add_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, id_f,
    Cochain.comp_v _ _ (add_neg_self 1) p q p hpq (by linarith)]
    using Cochain.congr_v (id φ) p p (add_zero p)

@[reassoc]
lemma inl_v_d (i j k : ℤ) (hij : i + (-1) = j) (hik : k + (-1) = i) :
    (inl φ).v i j hij ≫ (mappingCone φ).d j i =
      φ.f i ≫ (inr φ).f i - F.d i k ≫ (inl φ).v _ _ hik := by
  dsimp [mappingCone, inl, inr]
  rw [homotopyCofiber.inlX_d φ j i k (by dsimp; linarith) (by dsimp; linarith)]
  abel

@[reassoc (attr := simp 1100)]
lemma inr_f_d (n₁ n₂ : ℤ) :
    (inr φ).f n₁ ≫ (mappingCone φ).d n₁ n₂ = G.d n₁ n₂ ≫ (inr φ).f n₂ := by
  apply Hom.comm

@[reassoc]
lemma d_fst_v (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    (mappingCone φ).d i j ≫ (fst φ).1.v j k hjk =
      -(fst φ).1.v i j hij ≫ F.d j k := by
  apply homotopyCofiber.d_fstX

@[reassoc (attr := simp)]
lemma d_fst_v' (i j : ℤ) (hij : i + 1 = j) :
    (mappingCone φ).d (i - 1) i ≫ (fst φ).1.v i j hij =
      -(fst φ).1.v (i - 1) i (by linarith) ≫ F.d i j :=
  d_fst_v φ (i - 1) i j (by linarith) hij

@[reassoc]
lemma d_snd_v (i j : ℤ) (hij : i + 1 = j) :
    (mappingCone φ).d i j ≫ (snd φ).v j j (add_zero _) =
      (fst φ).1.v i j hij ≫ φ.f j + (snd φ).v i i (add_zero i) ≫ G.d i j := by
  dsimp [mappingCone, snd, fst]
  simp only [Cochain.ofHoms_v]
  apply homotopyCofiber.d_sndX

@[reassoc (attr := simp)]
lemma d_snd_v' (n : ℤ) :
    (mappingCone φ).d (n - 1) n ≫ (snd φ).v n n (add_zero n) =
    (fst φ : Cochain (mappingCone φ) F 1).v (n - 1) n (by linarith) ≫ φ.f n +
      (snd φ).v (n - 1) (n - 1) (add_zero _) ≫ G.d (n - 1) n := by
  apply d_snd_v

@[simp]
lemma δ_inl :
    δ (-1) 0 (inl φ) = Cochain.ofHom (φ ≫ inr φ) := by
  ext p
  simp [δ_v (-1) 0 (neg_add_self 1) (inl φ) p p (add_zero p) _ _ rfl rfl,
    inl_v_d φ p (p - 1) (p + 1) (by linarith) (by linarith)]

@[simp]
lemma δ_snd :
    δ 0 1 (snd φ) = -(fst φ).1.comp (Cochain.ofHom φ) (add_zero 1) := by
  ext p q hpq
  simp [d_snd_v φ p q hpq]

/-- Given `φ : F ⟶ G`, this is the cochain in `Cochain (mappingCone φ) K n` that is
constructed from two cochains `α : Cochain F K m` (with `m + 1 = n`) and `β : Cochain F K n`. -/
noncomputable def descCochain {K : CochainComplex C ℤ} {n m : ℤ} (α : Cochain F K m)
    (β : Cochain G K n) (h : m + 1 = n) : Cochain (mappingCone φ) K n :=
  (fst φ).1.comp α (by rw [← h, add_comm]) + (snd φ).comp β (zero_add n)

@[simp]
lemma inl_descCochain {K : CochainComplex C ℤ} {n m : ℤ} (α : Cochain F K m)
    (β : Cochain G K n) (h : m + 1 = n) :
    (inl φ).comp (descCochain φ α β h) (by linarith) = α := by
  simp [descCochain]

@[simp]
lemma inr_descCochain {K : CochainComplex C ℤ} {n m : ℤ} (α : Cochain F K m)
    (β : Cochain G K n) (h : m + 1 = n) :
    (Cochain.ofHom (inr φ)).comp (descCochain φ α β h) (zero_add n) = β := by
  simp [descCochain]

end mappingCone

end CochainComplex
