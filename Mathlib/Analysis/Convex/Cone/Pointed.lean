import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Algebra.Order.Nonneg.Ring
import Mathlib.Algebra.DirectSum.Module

structure PointedCone (𝕜 : Type _) (E : Type _) [OrderedSemiring 𝕜] [AddCommMonoid E]
     [SMul 𝕜 E] extends ConvexCone 𝕜 E where
  zero_mem' : 0 ∈ carrier

namespace PointedCone

variable {𝕜} [OrderedSemiring 𝕜]

section SMul
variable {E} [AddCommMonoid E] [SMul 𝕜 E]

instance : Coe (PointedCone 𝕜 E) (ConvexCone 𝕜 E) :=
  ⟨fun K => K.1⟩

theorem ext' : Function.Injective ((↑) : PointedCone 𝕜 E → ConvexCone 𝕜 E) := fun S T h => by
  cases S; cases T; congr

instance : SetLike (PointedCone 𝕜 E) E where
  coe K := K.carrier
  coe_injective' _ _ h := PointedCone.ext' (SetLike.coe_injective h)

@[ext]
theorem ext {S T : PointedCone 𝕜 E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
theorem mem_coe {x : E} {S : PointedCone 𝕜 E} : x ∈ (S : ConvexCone 𝕜 E) ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem zero_mem (S : PointedCone 𝕜 E) : 0 ∈ S :=
  S.zero_mem'

instance (S : PointedCone 𝕜 E) : Zero S := ⟨
  0, S.zero_mem⟩

protected theorem nonempty (S : PointedCone 𝕜 E) : (S : Set E).Nonempty :=
  ⟨0, S.zero_mem⟩

end SMul

section PositiveCone

variable (𝕜 E)
variable [OrderedSemiring 𝕜] [OrderedAddCommGroup E] [Module 𝕜 E] [OrderedSMul 𝕜 E]

/-- The positive cone is the proper cone formed by the set of nonnegative elements in an ordered
module. -/
def positive : PointedCone 𝕜 E where
  toConvexCone := ConvexCone.positive 𝕜 E
  zero_mem' := ConvexCone.pointed_positive _ _

@[simp]
theorem mem_positive {x : E} : x ∈ positive 𝕜 E ↔ 0 ≤ x :=
  Iff.rfl

@[simp]
theorem coe_positive : ↑(positive 𝕜 E) = ConvexCone.positive 𝕜 E :=
  rfl

end PositiveCone

section Module

variable [AddCommMonoid E] [Module 𝕜 E]
variable {S : PointedCone 𝕜 E}

set_option quotPrecheck false in
scoped notation "𝕜≥0" => { c : 𝕜 // 0 ≤ c }

instance : Module 𝕜≥0 E := Module.compHom E (@Nonneg.coeRingHom 𝕜 _)

protected theorem smul_mem {c : 𝕜} {x : E} (hc : 0 ≤ c) (hx : x ∈ S) : c • x ∈ S := by
  cases' eq_or_lt_of_le hc with hzero hpos
  . rw [← hzero, zero_smul]
    exact S.zero_mem
  . exact @ConvexCone.smul_mem 𝕜 E _ _ _ S _ _ hpos hx

instance hasSmul : SMul 𝕜≥0 S where
  smul := fun ⟨c, hc⟩ ⟨x, hx⟩ => ⟨c • x, S.smul_mem hc hx⟩

instance hasNsmul : SMul ℕ S where
  smul := fun n x => (n : 𝕜≥0) • x

@[simp]
protected theorem coe_smul (x : S) (n : 𝕜≥0) : n • x = n • (x : E) :=
  rfl

@[simp]
protected theorem nsmul_eq_smul_cast (x : S) (n : ℕ) : n • (x : E) = (n : 𝕜≥0) • (x : E) :=
  nsmul_eq_smul_cast _ _ _

@[simp]
theorem coe_nsmul (x : S) (n : ℕ) : (n • x : E) = n • (x : E) := by
  simp_rw [PointedCone.coe_smul, PointedCone.nsmul_eq_smul_cast] ; rfl

@[simp]
theorem coe_add : ∀ (x y : { x // x ∈ S }), (x + y : E) = ↑x + ↑y := by
  aesop

theorem add_mem ⦃x⦄ (hx : x ∈ S) ⦃y⦄ (hy : y ∈ S) : x + y ∈ S :=
  S.add_mem' hx hy

instance : AddMemClass (PointedCone 𝕜 E) E where
  add_mem ha hb := add_mem ha hb

instance : AddCommMonoid S :=
  Function.Injective.addCommMonoid (Subtype.val : S → E) Subtype.coe_injective rfl coe_add coe_nsmul

def subtype.addMonoidHom : S →+ E where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' := by aesop

@[simp]
theorem coeSubtype.addMonoidHom : (subtype.addMonoidHom : S → E) = Subtype.val := rfl

instance : Module 𝕜≥0 S := by
  apply Function.Injective.module (𝕜≥0) subtype.addMonoidHom
  simp only [coeSubtype.addMonoidHom, Subtype.coe_injective]
  simp only [coeSubtype.addMonoidHom, PointedCone.coe_smul, Subtype.forall, implies_true, forall_const] -- a single `simp` does not work!

def subtype.linearMap : S →ₗ[𝕜≥0] E where
  toFun := Subtype.val
  map_add' := by simp
  map_smul' := by simp

def toSubmodule (S : PointedCone 𝕜 E) : Submodule 𝕜≥0 E where
  carrier := S
  add_mem' := fun hx hy => S.add_mem hx hy
  zero_mem' := S.zero_mem
  smul_mem' := fun ⟨c, hc⟩ x => by
    cases' eq_or_lt_of_le hc with hzero hpos
    simp
    . rintro _
      convert S.zero_mem
      simpa [← hzero] using smul_eq_zero_of_left rfl x
    . apply ConvexCone.smul_mem
      convert hpos

def ofSubmodule (M : Submodule 𝕜≥0 E) : (PointedCone 𝕜 E) where
  carrier := M
  smul_mem' := fun c hc _ hx => M.smul_mem ⟨c, le_of_lt hc⟩ hx
  add_mem' := fun _ hx _ hy => M.add_mem hx hy
  zero_mem' := M.zero_mem

def toSubmoduleEquiv : (PointedCone 𝕜 E) ≃ (Submodule 𝕜≥0 E) where
  toFun := toSubmodule
  invFun := ofSubmodule
  left_inv := fun S => by aesop
  right_inv := fun M => by aesop

def ofLinearMap [AddCommMonoid M] [Module 𝕜≥0 M] (f : M →ₗ[𝕜≥0] E) : PointedCone 𝕜 E where
  carrier := Set.range f
  smul_mem' := fun c hc _ ⟨y, _⟩ => ⟨(⟨c, le_of_lt hc⟩ : 𝕜≥0) • y, by aesop⟩
  add_mem' := fun x1 ⟨y1, hy1⟩ x2 ⟨y2, hy2⟩ => ⟨y1 + y2, by aesop⟩
  zero_mem' := ⟨0, by aesop⟩

section Dual
variable {E}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def dual (S : PointedCone ℝ E) : PointedCone ℝ E where
  toConvexCone := (S : Set E).innerDualCone
  zero_mem' := pointed_innerDualCone (S : Set E)

@[simp]
theorem coe_dual (S : PointedCone ℝ E) : ↑(dual S) = (S : Set E).innerDualCone :=
  rfl

@[simp]
theorem mem_dual {S : PointedCone ℝ E} {y : E} : y ∈ dual S ↔ ∀ ⦃x⦄, x ∈ S → 0 ≤ ⟪x, y⟫_ℝ := by
  aesop

end Dual

end Module

section DirectSum
open DirectSum Set

variable {ι : Type _} [dec_ι : DecidableEq ι]
variable {𝔼 : ι → Type _} [∀ i, AddCommMonoid (𝔼 i)] [∀ i, Module 𝕜 (𝔼 i)]

protected def DirectSum (S : ∀ i, PointedCone 𝕜 (𝔼 i)) : PointedCone 𝕜 (⨁ (i : ι), 𝔼 i) :=
  ofLinearMap <| DFinsupp.mapRange.linearMap <| fun i => subtype.linearMap (S := S i)

-- TODO: DirectSum of Duals
end DirectSum

end PointedCone
