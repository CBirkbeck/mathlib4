import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.GroupObjects.Basic
import Mathlib.RingTheory.HopfAlgebra
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts

universe u v u' v'

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

variable {S : Scheme.{u}}

local instance : HasFiniteLimits (Over S) :=
  @Over.hasFiniteLimits _ _ _ (hasFiniteWidePullbacks_of_hasFiniteLimits Scheme.{u})

#check GroupObject (Over S)

namespace Bialgebra

variable {R : Type u'} {A : Type v'} [CommSemiring R] [Semiring A]

lemma comulAlgHom_coassoc [Bialgebra R A] :
  (TensorProduct.assoc R A A A).toLinearMap ∘ₗ LinearMap.rTensor A (comulAlgHom R A).toLinearMap
    ∘ₗ (comulAlgHom R A).toLinearMap =
    LinearMap.lTensor A (comulAlgHom R A).toLinearMap ∘ₗ (comulAlgHom R A).toLinearMap := by
  ext x
  simp only [comulAlgHom, AlgHom.toLinearMap_ofLinearMap, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Coalgebra.coassoc_apply]


end Bialgebra

namespace HopfAlgebra

variable {R : Type u'} {A : Type v'} [CommSemiring R] [Semiring A]

lemma antipode_apply_one [HopfAlgebra R A] : (inferInstance : HopfAlgebra R A).antipode 1 = 1 := by
  set H : HopfAlgebra R A := inferInstance
  have := H.mul_antipode_rTensor_comul
  apply_fun (fun f ↦ f 1) at this
  simp only [LinearMap.coe_comp, Function.comp_apply, Bialgebra.comul_one, Bialgebra.counit_one,
    Algebra.linearMap_apply, _root_.map_one] at this
  have that : ((LinearMap.rTensor A antipode) (1 ⊗ₜ[R] 1)) = H.antipode 1 ⊗ₜ[R] 1 := by
    simp only [LinearMap.rTensor_tmul]
  erw [that] at this
  simp only [LinearMap.mul'_apply, mul_one] at this
  exact this

lemma antipode_antiAlgHom [HopfAlgebra R A] (a b : A) :
    (inferInstance : HopfAlgebra R A).antipode (a * b) =
    (inferInstance : HopfAlgebra R A).antipode b * (inferInstance : HopfAlgebra R A).antipode a := by
  sorry

end HopfAlgebra

namespace CommHopfAlgebra

open HopfAlgebra

variable {R : Type u'} {A : Type v'} [CommSemiring R] [CommSemiring A]

def antipodeAsAlgHom [HopfAlgebra R A] : A →ₐ[R] A :=
  AlgHom.ofLinearMap (inferInstance : HopfAlgebra R A).antipode antipode_apply_one
  (fun _ _ ↦ by rw [antipode_antiAlgHom, mul_comm])

end CommHopfAlgebra

namespace AlgebraicGeometry.Scheme

open Bialgebra HopfAlgebra Opposite IsLimit

variable {A : Type} [CommRing A] [HopfAlgebra ℤ A]

#synth HasBinaryProducts Scheme

def GroupSchemeOfHopfAlgebra : GroupObject Scheme where
  X := Scheme.Spec.obj (Opposite.op (CommRingCat.of A))
  one := (conePointUniqueUpToIso terminalIsTerminal specZIsTerminal).hom ≫
      (Scheme.Spec.map (CommRingCat.ofHom (counitAlgHom ℤ A) : A →+* ℤ).op)
  mul := by
    set A' := CommRingCat.of A
    have := PreservesLimitPair.iso Scheme.Spec (Opposite.op A') (Opposite.op A')
    have := isCoproductOfIsInitialIsPushout _ _ _ _ CommRingCat.zIsInitial
      (CommRingCat.pushoutCoconeIsColimit
      (CommRingCat.ofHom (Int.castRingHom A)) (CommRingCat.ofHom (Int.castRingHom A)))
    simp only [CommRingCat.coe_of, AlgHom.toRingHom_eq_coe] at this

  inv := sorry
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  mul_left_inv := sorry


#exit



def GroupSchemeOfHopfAlgebra : GroupObject (Scheme.{u'}) where
  X := Scheme.Spec.obj (Opposite.op (CommRingCat.of A))
  one := by
    have := Scheme.Spec.map (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (counitAlgHom ℤ A) : A →+* (ULift ℤ))).op
  mul := sorry
  inv := sorry
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  mul_left_inv := sorry

#exit

variable {R : Type u'} {A : Type (max u' v')} [CommRing R] [CommRing A] [HopfAlgebra R A]

def GroupSchemeOfHopfAlgebra : GroupObject (Over (Scheme.Spec.obj (op (CommRingCat.of R)))) where
  X := sorry --Scheme.Spec.obj (Opposite.op (CommRingCat.of A))
  one := by
    have := Scheme.Spec.map (counitAlgHom R A : A →+* R)
  mul := sorry
  inv := sorry
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  mul_left_inv := sorry



end AlgebraicGeometry.Scheme
