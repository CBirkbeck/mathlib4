/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Group
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula

/-!
# Nonsingular rational points on Weierstrass curves in Jacobian coordinates

This file defines the type of points on a Weierstrass curve as a tuple, consisting of an equivalence
class of triples up to scaling by weights, satisfying a Weierstrass equation with a nonsingular
condition. This file also defines the negation and addition operations of the group law for this
type, and proves that they respect the Weierstrass equation and the nonsingular condition. The fact
that they form an abelian group is proven in `Mathlib/AlgebraicGeometry/EllipticCurve/Group.lean`.

## Mathematical background

Let `W` be a Weierstrass curve over a field `F`. A point on the weighted projective plane with
weights `(2, 3, 1)` is an equivalence class of triples `[x:y:z]` with coordinates in `F` such that
`(x, y, z) ∼ (x', y', z')` precisely if there is some unit `u` of `F` such that
`(x, y, z) = (u²x', u³y', uz')`, with an extra condition that `(x, y, z) ≠ (0, 0, 0)`. A rational
point is a point on the `(2, 3, 1)`-projective plane satisfying a `(2, 3, 1)`-homogeneous
Weierstrass equation `Y² + a₁XYZ + a₃YZ³ = X³ + a₂X²Z² + a₄XZ⁴ + a₆Z⁶`, and being nonsingular means
the partial derivatives `W_X(X, Y, Z)`, `W_Y(X, Y, Z)`, and `W_Z(X, Y, Z)` do not vanish
simultaneously. Note that the vanishing of the Weierstrass equation and its partial derivatives are
independent of the representative for `[x:y:z]`, and the nonsingularity condition already implies
`(x, y, z) ≠ (0, 0, 0)`, so a nonsingular rational point on `W` can simply be given by a tuple
consisting of `[x:y:z]` and the nonsingular condition on any representative. In cryptography, as
well as in this file, this is often called the Jacobian coordinates of `W`.

As in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine.lean`, the set of nonsingular rational points
forms an abelian group under the same secant-and-tangent process, but the polynomials involved are
`(2, 3, 1)`-homogeneous, and any instances of division become multiplication in the `Z`-coordinate.
Note that most computational proofs follow from their analogous proofs for affine coordinates.

## Main definitions

 * `WeierstrassCurve.Jacobian.neg`: the negation operation on a point representative.
 * `WeierstrassCurve.Jacobian.negMap`: the negation operation on a point class.
 * `WeierstrassCurve.Jacobian.add`: the addition operation on a point representative.
 * `WeierstrassCurve.Jacobian.addMap`: the addition operation on a point class.
 * `WeierstrassCurve.Jacobian.Point`: a nonsingular rational point.
 * `WeierstrassCurve.Jacobian.Point.neg`: the negation operation on a nonsingular rational point.
 * `WeierstrassCurve.Jacobian.Point.add`: the addition operation on a nonsingular rational point.
 * `WeierstrassCurve.Jacobian.Point.toAffineAddEquiv`: the equivalence between the nonsingular
    rational points in Jacobian coordinates with those in affine coordinates.

## Main statements

 * `WeierstrassCurve.Jacobian.nonsingular_neg`: negation preserves the nonsingular condition.
 * `WeierstrassCurve.Jacobian.nonsingular_add`: addition preserves the nonsingular condition.
 * `WeierstrassCurve.Jacobian.Point.instAddCommGroup`: the type of nonsingular rational points on a
    Jacobian Weierstrass curve forms an abelian group under addition.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, rational point, Jacobian coordinates
-/

local notation3 "x" => (0 : Fin 3)

local notation3 "y" => (1 : Fin 3)

local notation3 "z" => (2 : Fin 3)

universe r s u v w

/-! ## Weierstrass curves -/

namespace WeierstrassCurve.Jacobian

open MvPolynomial

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_C, map_X, map_neg, map_add, map_sub, map_mul, map_pow,
    map_div₀, WeierstrassCurve.map, Function.comp_apply])

variable {R : Type u} [CommRing R] {W' : Jacobian R} {F : Type v} [Field F] {W : Jacobian F}

section Negation

/-! ### Negation on point representatives -/

variable (W') in
/-- The negation of a point representative. -/
def neg (P : Fin 3 → R) : Fin 3 → R :=
  ![P x, W'.negY P, P z]

lemma neg_X (P : Fin 3 → R) : W'.neg P x = P x :=
  rfl

lemma neg_Y (P : Fin 3 → R) : W'.neg P y = W'.negY P :=
  rfl

lemma neg_Z (P : Fin 3 → R) : W'.neg P z = P z :=
  rfl

protected lemma neg_smul (P : Fin 3 → R) (u : R) : W'.neg (u • P) = u • W'.neg P := by
  rw [neg, negY_smul]
  rfl

lemma neg_smul_equiv (P : Fin 3 → R) {u : R} (hu : IsUnit u) : W'.neg (u • P) ≈ W'.neg P :=
  ⟨hu.unit, (W'.neg_smul ..).symm⟩

lemma neg_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.neg P ≈ W'.neg Q := by
  rcases h with ⟨u, rfl⟩
  exact neg_smul_equiv Q u.isUnit

lemma neg_of_Z_eq_zero' {P : Fin 3 → R} (hPz : P z = 0) : W'.neg P = ![P x, -P y, 0] := by
  rw [neg, negY_of_Z_eq_zero hPz, hPz]

lemma neg_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    W.neg P = -(P y / P x) • ![1, 1, 0] := by
  have hX {n : ℕ} : IsUnit <| P x ^ n := (isUnit_X_of_Z_eq_zero hP hPz).pow n
  erw [neg_of_Z_eq_zero' hPz, smul_fin3, neg_sq, div_pow, (equation_of_Z_eq_zero hPz).mp hP.left,
    pow_succ, hX.mul_div_cancel_left, mul_one, Odd.neg_pow <| by decide, div_pow, pow_succ,
    (equation_of_Z_eq_zero hPz).mp hP.left, hX.mul_div_cancel_left, mul_one, mul_zero]

lemma neg_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.neg P = P z • ![P x / P z ^ 2, W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3), 1] := by
  erw [neg, smul_fin3, mul_div_cancel₀ _ <| pow_ne_zero 2 hPz, ← negY_of_Z_ne_zero hPz,
    mul_div_cancel₀ _ <| pow_ne_zero 3 hPz, mul_one]

private lemma nonsingular_neg_of_Z_ne_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) :
    W.Nonsingular ![P x / P z ^ 2, W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3), 1] :=
  (nonsingular_some ..).mpr <| Affine.nonsingular_neg <| (nonsingular_of_Z_ne_zero hPz).mp hP

lemma nonsingular_neg {P : Fin 3 → F} (hP : W.Nonsingular P) : W.Nonsingular <| W.neg P := by
  by_cases hPz : P z = 0
  · simp only [neg_of_Z_eq_zero hP hPz, nonsingular_smul _
        ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg, nonsingular_zero]
  · simp only [neg_of_Z_ne_zero hPz, nonsingular_smul _ <| Ne.isUnit hPz,
      nonsingular_neg_of_Z_ne_zero hP hPz]

lemma addZ_neg (P : Fin 3 → R) : addZ P (W'.neg P) = 0 :=
  addZ_of_X_eq rfl

lemma addX_neg {P : Fin 3 → R} (hP : W'.Equation P) : W'.addX P (W'.neg P) = W'.dblZ P ^ 2 := by
  linear_combination (norm := (rw [addX, neg_X, neg_Y, neg_Z, dblZ, negY]; ring1))
    -2 * P z ^ 2 * (equation_iff _).mp hP

lemma negAddY_neg {P : Fin 3 → R} (hP : W'.Equation P) :
    W'.negAddY P (W'.neg P) = W'.dblZ P ^ 3 := by
  linear_combination (norm := (rw [negAddY, neg_X, neg_Y, neg_Z, dblZ, negY]; ring1))
    -2 * P z ^ 3 * (P y - W'.negY P) * (equation_iff _).mp hP

lemma addY_neg {P : Fin 3 → R} (hP : W'.Equation P) : W'.addY P (W'.neg P) = -W'.dblZ P ^ 3 := by
  rw [addY, addX_neg hP, negAddY_neg hP, addZ_neg, negY_of_Z_eq_zero rfl]
  rfl

lemma addXYZ_neg {P : Fin 3 → R} (hP : W'.Equation P) :
    W'.addXYZ P (W'.neg P) = -W'.dblZ P • ![1, 1, 0] := by
  erw [addXYZ, addX_neg hP, addY_neg hP, addZ_neg, smul_fin3, neg_sq, mul_one,
    Odd.neg_pow <| by decide, mul_one, mul_zero]

variable (W') in
/-- The negation of a point class. If `P` is a point representative,
then `W'.negMap ⟦P⟧` is definitionally equivalent to `W'.neg P`. -/
def negMap (P : PointClass R) : PointClass R :=
  P.map W'.neg fun _ _ => neg_equiv

lemma negMap_eq (P : Fin 3 → R) : W'.negMap ⟦P⟧ = ⟦W'.neg P⟧ :=
  rfl

lemma negMap_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    W.negMap ⟦P⟧ = ⟦![1, 1, 0]⟧ := by
  rw [negMap_eq, neg_of_Z_eq_zero hP hPz,
    smul_eq _ ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg]

lemma negMap_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.negMap ⟦P⟧ = ⟦![P x / P z ^ 2, W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3), 1]⟧ := by
  rw [negMap_eq, neg_of_Z_ne_zero hPz, smul_eq _ <| Ne.isUnit hPz]

lemma nonsingularLift_negMap {P : PointClass F} (hP : W.NonsingularLift P) :
    W.NonsingularLift <| W.negMap P := by
  rcases P with ⟨_⟩
  exact nonsingular_neg hP

end Negation

section Addition

/-! ### Addition on point representatives -/

open Classical in
variable (W') in
/-- The addition of two point representatives. -/
noncomputable def add (P Q : Fin 3 → R) : Fin 3 → R :=
  if P ≈ Q then W'.dblXYZ P else W'.addXYZ P Q

lemma add_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.add P Q = W'.dblXYZ P :=
  if_pos h

lemma add_smul_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    W'.add (u • P) (v • Q) = u ^ 4 • W'.add P Q := by
  rw [add_of_equiv <| (smul_equiv_smul P Q hu hv).mpr h, dblXYZ_smul, add_of_equiv h]

lemma add_self (P : Fin 3 → R) : W'.add P P = W'.dblXYZ P :=
  add_of_equiv <| Setoid.refl _

lemma add_of_eq {P Q : Fin 3 → R} (h : P = Q) : W'.add P Q = W'.dblXYZ P :=
  h ▸ add_self P

lemma add_of_not_equiv {P Q : Fin 3 → R} (h : ¬P ≈ Q) : W'.add P Q = W'.addXYZ P Q :=
  if_neg h

lemma add_smul_of_not_equiv {P Q : Fin 3 → R} (h : ¬P ≈ Q) {u v : R} (hu : IsUnit u)
    (hv : IsUnit v) : W'.add (u • P) (v • Q) = (u * v) ^ 2 • W'.add P Q := by
  rw [add_of_not_equiv <| h.comp (smul_equiv_smul P Q hu hv).mp, addXYZ_smul, add_of_not_equiv h]

lemma add_smul_equiv (P Q : Fin 3 → R) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    W'.add (u • P) (v • Q) ≈ W'.add P Q := by
  by_cases h : P ≈ Q
  · exact ⟨hu.unit ^ 4, by convert (add_smul_of_equiv h hu hv).symm⟩
  · exact ⟨(hu.unit * hv.unit) ^ 2, by convert (add_smul_of_not_equiv h hu hv).symm⟩

lemma add_equiv {P P' Q Q' : Fin 3 → R} (hP : P ≈ P') (hQ : Q ≈ Q') :
    W'.add P Q ≈ W'.add P' Q' := by
  rcases hP, hQ with ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  exact add_smul_equiv P' Q' u.isUnit v.isUnit

lemma add_of_Z_eq_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : W.add P Q = P x ^ 2 • ![1, 1, 0] := by
  rw [add_of_equiv <| equiv_of_Z_eq_zero hP hQ hPz hQz, dblXYZ_of_Z_eq_zero hP.left hPz]

lemma add_of_Z_eq_zero_left {P Q : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) (hQz : Q z ≠ 0) :
    W'.add P Q = (P x * Q z) • Q := by
  rw [add_of_not_equiv <| not_equiv_of_Z_eq_zero_left hPz hQz, addXYZ_of_Z_eq_zero_left hP hPz]

lemma add_of_Z_eq_zero_right {P Q : Fin 3 → R} (hQ : W'.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z = 0) : W'.add P Q = -(Q x * P z) • P := by
  rw [add_of_not_equiv <| not_equiv_of_Z_eq_zero_right hPz hQz, addXYZ_of_Z_eq_zero_right hQ hQz]

lemma add_of_Y_eq {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W.negY Q * P z ^ 3) : W.add P Q = W.dblU P • ![1, 1, 0] := by
  rw [add_of_equiv <| equiv_of_X_eq_of_Y_eq hPz hQz hx hy, dblXYZ_of_Y_eq hQz hx hy hy']

lemma add_of_Y_ne {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) :
    W.add P Q = addU P Q • ![1, 1, 0] := by
  rw [add_of_not_equiv <| not_equiv_of_Y_ne hy, addXYZ_of_X_eq hP hQ hPz hQz hx]

lemma add_of_Y_ne' {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) :
    W.add P Q = W.dblZ P •
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1] := by
  rw [add_of_equiv <| equiv_of_X_eq_of_Y_eq hPz hQz hx <| Y_eq_of_Y_ne' hP hQ hx hy,
    dblXYZ_of_Z_ne_zero hP hQ hPz hQz hx hy]

lemma add_of_X_ne {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) : W.add P Q = addZ P Q •
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1] := by
  rw [add_of_not_equiv <| not_equiv_of_X_ne hx, addXYZ_of_Z_ne_zero hP hQ hPz hQz hx]

private lemma nonsingular_add_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hxy : ¬(P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3)) : W.Nonsingular
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)), 1] :=
  (nonsingular_some ..).mpr <| Affine.nonsingular_add ((nonsingular_of_Z_ne_zero hPz).mp hP)
    ((nonsingular_of_Z_ne_zero hQz).mp hQ) <| by rwa [← X_eq_iff hPz hQz, ← Y_eq_iff' hPz hQz]

lemma nonsingular_add {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.Nonsingular <| W.add P Q := by
  by_cases hPz : P z = 0
  · by_cases hQz : Q z = 0
    · simp only [add_of_Z_eq_zero hP hQ hPz hQz,
        nonsingular_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2, nonsingular_zero]
    · simpa only [add_of_Z_eq_zero_left hP.left hPz hQz,
        nonsingular_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).mul <| Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · simpa only [add_of_Z_eq_zero_right hQ.left hPz hQz,
        nonsingular_smul _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg]
    · by_cases hxy : P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3
      · by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
        · simp only [add_of_Y_eq hPz hQz hxy.left hy hxy.right, nonsingular_smul _ <|
              isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, nonsingular_zero]
        · simp only [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
            nonsingular_smul _ <| isUnit_addU_of_Y_ne hPz hQz hy, nonsingular_zero]
      · have := nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy
        by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
        · simpa only [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx,
            nonsingular_smul _ <| isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hx <| not_and.mp hxy hx]
        · simpa only [add_of_X_ne hP.left hQ.left hPz hQz hx,
            nonsingular_smul _ <| isUnit_addZ_of_X_ne hx]

variable (W') in
/-- The addition of two point classes. If `P` is a point representative,
then `W.addMap ⟦P⟧ ⟦Q⟧` is definitionally equivalent to `W.add P Q`. -/
noncomputable def addMap (P Q : PointClass R) : PointClass R :=
  Quotient.map₂ W'.add (fun _ _ hP _ _ hQ => add_equiv hP hQ) P Q

lemma addMap_eq (P Q : Fin 3 → R) : W'.addMap ⟦P⟧ ⟦Q⟧ = ⟦W'.add P Q⟧ :=
  rfl

lemma addMap_of_Z_eq_zero_left {P : Fin 3 → F} {Q : PointClass F} (hP : W.Nonsingular P)
    (hQ : W.NonsingularLift Q) (hPz : P z = 0) : W.addMap ⟦P⟧ Q = Q := by
  revert hQ
  refine Q.inductionOn (motive := fun Q => _ → W.addMap _ Q = Q) fun Q hQ => ?_
  by_cases hQz : Q z = 0
  · rw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
      smul_eq _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2, Quotient.eq]
    exact Setoid.symm <| equiv_zero_of_Z_eq_zero hQ hQz
  · rw [addMap_eq, add_of_Z_eq_zero_left hP.left hPz hQz,
      smul_eq _ <| (isUnit_X_of_Z_eq_zero hP hPz).mul <| Ne.isUnit hQz]

lemma addMap_of_Z_eq_zero_right {P : PointClass F} {Q : Fin 3 → F} (hP : W.NonsingularLift P)
    (hQ : W.Nonsingular Q) (hQz : Q z = 0) : W.addMap P ⟦Q⟧ = P := by
  revert hP
  refine P.inductionOn (motive := fun P => _ → W.addMap P _ = P) fun P hP => ?_
  by_cases hPz : P z = 0
  · rw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
      smul_eq _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2, Quotient.eq]
    exact Setoid.symm <| equiv_zero_of_Z_eq_zero hP hPz
  · rw [addMap_eq, add_of_Z_eq_zero_right hQ.left hPz hQz,
      smul_eq _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg]

lemma addMap_of_Y_eq {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy' : P y * Q z ^ 3 = W.negY Q * P z ^ 3) : W.addMap ⟦P⟧ ⟦Q⟧ = ⟦![1, 1, 0]⟧ := by
  by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
  · rw [addMap_eq, add_of_Y_eq hPz hQz hx hy hy',
      smul_eq _ <| isUnit_dblU_of_Y_eq hP hPz hQz hx hy hy']
  · rw [addMap_eq, add_of_Y_ne hP.left hQ hPz hQz hx hy,
      smul_eq _ <| isUnit_addU_of_Y_ne hPz hQz hy]

lemma addMap_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hxy : ¬(P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3)) :
    W.addMap ⟦P⟧ ⟦Q⟧ =
      ⟦![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1]⟧ := by
  by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
  · rw [addMap_eq, add_of_Y_ne' hP hQ hPz hQz hx <| not_and.mp hxy hx,
      smul_eq _ <| isUnit_dblZ_of_Y_ne' hP hQ hPz hx <| not_and.mp hxy hx]
  · rw [addMap_eq, add_of_X_ne hP hQ hPz hQz hx, smul_eq _ <| isUnit_addZ_of_X_ne hx]

lemma nonsingularLift_addMap {P Q : PointClass F} (hP : W.NonsingularLift P)
    (hQ : W.NonsingularLift Q) : W.NonsingularLift <| W.addMap P Q := by
  rcases P; rcases Q
  exact nonsingular_add hP hQ

end Addition

/-! ### Nonsingular rational points -/

variable (W') in
/-- A nonsingular rational point on `W'`. -/
@[ext]
structure Point where
  /-- The point class underlying a nonsingular rational point on `W'`. -/
  {point : PointClass R}
  /-- The nonsingular condition underlying a nonsingular rational point on `W'`. -/
  (nonsingular : W'.NonsingularLift point)

namespace Point

lemma mk_point {P : PointClass R} (h : W'.NonsingularLift P) : (mk h).point = P :=
  rfl

instance [Nontrivial R] : Zero W'.Point :=
  ⟨⟨nonsingularLift_zero⟩⟩

lemma zero_def [Nontrivial R] : (0 : W'.Point) = ⟨nonsingularLift_zero⟩ :=
  rfl

lemma zero_point [Nontrivial R] : (0 : W'.Point).point = ⟦![1, 1, 0]⟧ :=
  rfl

lemma mk_ne_zero [Nontrivial R] {X Y : R} (h : W'.NonsingularLift ⟦![X, Y, 1]⟧) : mk h ≠ 0 :=
  (not_equiv_of_Z_eq_zero_right one_ne_zero rfl).comp <| Quotient.eq.mp.comp Point.ext_iff.mp

/-- The map from a nonsingular rational point on a Weierstrass curve `W'` in affine coordinates
to the corresponding nonsingular rational point on `W'` in Jacobian coordinates. -/
def fromAffine [Nontrivial R] : W'.toAffine.Point → W'.Point
  | 0 => 0
  | .some h => ⟨(nonsingularLift_some ..).mpr h⟩

lemma fromAffine_zero [Nontrivial R] : fromAffine 0 = (0 : W'.Point) :=
  rfl

lemma fromAffine_some [Nontrivial R] {X Y : R} (h : W'.toAffine.Nonsingular X Y) :
    fromAffine (.some h) = ⟨(nonsingularLift_some ..).mpr h⟩ :=
  rfl

lemma fromAffine_some_ne_zero [Nontrivial R] {X Y : R} (h : W'.toAffine.Nonsingular X Y) :
    fromAffine (.some h) ≠ 0 :=
  mk_ne_zero <| (nonsingularLift_some ..).mpr h

@[deprecated (since := "2025-02-01")] alias fromAffine_ne_zero := fromAffine_some_ne_zero

/-- The negation of a nonsingular rational point on `W`.
Given a nonsingular rational point `P` on `W`, use `-P` instead of `neg P`. -/
def neg (P : W.Point) : W.Point :=
  ⟨nonsingularLift_negMap P.nonsingular⟩

instance : Neg W.Point :=
  ⟨neg⟩

lemma neg_def (P : W.Point) : -P = P.neg :=
  rfl

lemma neg_point (P : W.Point) : (-P).point = W.negMap P.point :=
  rfl

/-- The addition of two nonsingular rational points on `W`.
Given two nonsingular rational points `P` and `Q` on `W`, use `P + Q` instead of `add P Q`. -/
noncomputable def add (P Q : W.Point) : W.Point :=
  ⟨nonsingularLift_addMap P.nonsingular Q.nonsingular⟩

noncomputable instance : Add W.Point :=
  ⟨add⟩

lemma add_def (P Q : W.Point) : P + Q = P.add Q :=
  rfl

lemma add_point (P Q : W.Point) : (P + Q).point = W.addMap P.point Q.point :=
  rfl

end Point

section Affine

/-! ### Equivalence with affine coordinates -/

namespace Point

open Classical in
variable (W) in
/-- The map from a point representative that is nonsingular on a Weierstrass curve `W` in Jacobian
coordinates to the corresponding nonsingular rational point on `W` in affine coordinates. -/
noncomputable def toAffine (P : Fin 3 → F) : W.toAffine.Point :=
  if hP : W.Nonsingular P ∧ P z ≠ 0 then .some <| (nonsingular_of_Z_ne_zero hP.2).mp hP.1 else 0

lemma toAffine_of_singular {P : Fin 3 → F} (hP : ¬W.Nonsingular P) : toAffine W P = 0 := by
  rw [toAffine, dif_neg <| not_and_of_not_left _ hP]

lemma toAffine_of_Z_eq_zero {P : Fin 3 → F} (hPz : P z = 0) : toAffine W P = 0 := by
  rw [toAffine, dif_neg <| not_and_not_right.mpr fun _ => hPz]

lemma toAffine_zero : toAffine W ![1, 1, 0] = 0 :=
  toAffine_of_Z_eq_zero rfl

lemma toAffine_of_Z_ne_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) :
    toAffine W P = .some ((nonsingular_of_Z_ne_zero hPz).mp hP) := by
  rw [toAffine, dif_pos ⟨hP, hPz⟩]

lemma toAffine_some {X Y : F} (h : W.Nonsingular ![X, Y, 1]) :
    toAffine W ![X, Y, 1] = .some ((nonsingular_some ..).mp h) := by
  simp only [toAffine_of_Z_ne_zero h one_ne_zero, fin3_def_ext, one_pow, div_one]

lemma toAffine_smul (P : Fin 3 → F) {u : F} (hu : IsUnit u) :
    toAffine W (u • P) = toAffine W P := by
  by_cases hP : W.Nonsingular P
  · by_cases hPz : P z = 0
    · rw [toAffine_of_Z_eq_zero <| mul_eq_zero_of_right u hPz, toAffine_of_Z_eq_zero hPz]
    · rw [toAffine_of_Z_ne_zero ((nonsingular_smul P hu).mpr hP) <| mul_ne_zero hu.ne_zero hPz,
        toAffine_of_Z_ne_zero hP hPz, Affine.Point.some.injEq]
      simp only [smul_fin3_ext, mul_pow, mul_div_mul_left _ _ (hu.pow _).ne_zero, and_self]
  · rw [toAffine_of_singular <| hP.comp (nonsingular_smul P hu).mp, toAffine_of_singular hP]

lemma toAffine_of_equiv {P Q : Fin 3 → F} (h : P ≈ Q) : toAffine W P = toAffine W Q := by
  rcases h with ⟨u, rfl⟩
  exact toAffine_smul Q u.isUnit

lemma toAffine_neg {P : Fin 3 → F} (hP : W.Nonsingular P) :
    toAffine W (W.neg P) = -toAffine W P := by
  by_cases hPz : P z = 0
  · rw [neg_of_Z_eq_zero hP hPz,
      toAffine_smul _ ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg,
      toAffine_zero, toAffine_of_Z_eq_zero hPz, Affine.Point.neg_zero]
  · rw [neg_of_Z_ne_zero hPz, toAffine_smul _ <| Ne.isUnit hPz, toAffine_some <|
        (nonsingular_smul _ <| Ne.isUnit hPz).mp <| neg_of_Z_ne_zero hPz ▸ nonsingular_neg hP,
      toAffine_of_Z_ne_zero hP hPz, Affine.Point.neg_some]

private lemma toAffine_add_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hxy : ¬(P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3)) : toAffine W
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1] = toAffine W P + toAffine W Q := by
  rw [toAffine_some <| nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy, toAffine_of_Z_ne_zero hP hPz,
    toAffine_of_Z_ne_zero hQ hQz,
    Affine.Point.add_some <| by rwa [← X_eq_iff hPz hQz, ← Y_eq_iff' hPz hQz]]

lemma toAffine_add {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    toAffine W (W.add P Q) = toAffine W P + toAffine W Q := by
  by_cases hPz : P z = 0
  · rw [toAffine_of_Z_eq_zero hPz, zero_add]
    by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero hP hQ hPz hQz, toAffine_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2,
        toAffine_zero, toAffine_of_Z_eq_zero hQz]
    · rw [add_of_Z_eq_zero_left hP.left hPz hQz,
        toAffine_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).mul <| Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero_right hQ.left hPz hQz,
        toAffine_smul _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg,
        toAffine_of_Z_eq_zero hQz, add_zero]
    · by_cases hxy : P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3
      · rw [toAffine_of_Z_ne_zero hP hPz, toAffine_of_Z_ne_zero hQ hQz, Affine.Point.add_of_Y_eq
            ((X_eq_iff hPz hQz).mp hxy.left) ((Y_eq_iff' hPz hQz).mp hxy.right)]
        by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
        · rw [add_of_Y_eq hPz hQz hxy.left hy hxy.right,
            toAffine_smul _ <| isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, toAffine_zero]
        · rw [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
            toAffine_smul _ <| isUnit_addU_of_Y_ne hPz hQz hy, toAffine_zero]
      · have := toAffine_add_of_Z_ne_zero hP hQ hPz hQz hxy
        by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
        · rwa [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx,
            toAffine_smul _ <| isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hx <| not_and.mp hxy hx]
        · rwa [add_of_X_ne hP.left hQ.left hPz hQz hx, toAffine_smul _ <| isUnit_addZ_of_X_ne hx]

/-- The map from a nonsingular rational point on a Weierstrass curve `W` in Jacobian coordinates
to the corresponding nonsingular rational point on `W` in affine coordinates. -/
noncomputable def toAffineLift (P : W.Point) : W.toAffine.Point :=
  P.point.lift _ fun _ _ => toAffine_of_equiv

lemma toAffineLift_eq {P : Fin 3 → F} (hP : W.NonsingularLift ⟦P⟧) :
    toAffineLift ⟨hP⟩ = toAffine W P :=
  rfl

lemma toAffineLift_of_Z_eq_zero {P : Fin 3 → F} (hP : W.NonsingularLift ⟦P⟧) (hPz : P z = 0) :
    toAffineLift ⟨hP⟩ = 0 :=
  toAffine_of_Z_eq_zero hPz

lemma toAffineLift_zero : toAffineLift (0 : W.Point) = 0 :=
  toAffine_zero

lemma toAffineLift_of_Z_ne_zero {P : Fin 3 → F} {hP : W.NonsingularLift ⟦P⟧} (hPz : P z ≠ 0) :
    toAffineLift ⟨hP⟩ = .some ((nonsingular_of_Z_ne_zero hPz).mp hP) :=
  toAffine_of_Z_ne_zero hP hPz

lemma toAffineLift_some {X Y : F} (h : W.NonsingularLift ⟦![X, Y, 1]⟧) :
    toAffineLift ⟨h⟩ = .some ((nonsingular_some ..).mp h) :=
  toAffine_some h

lemma toAffineLift_neg (P : W.Point) : (-P).toAffineLift = -P.toAffineLift := by
  rcases P with @⟨⟨_⟩, hP⟩
  exact toAffine_neg hP

lemma toAffineLift_add (P Q : W.Point) :
    (P + Q).toAffineLift = P.toAffineLift + Q.toAffineLift := by
  rcases P, Q with ⟨@⟨⟨_⟩, hP⟩, @⟨⟨_⟩, hQ⟩⟩
  exact toAffine_add hP hQ

variable (W) in
/-- The equivalence between the nonsingular rational points on a Weierstrass curve `W` in Jacobian
coordinates with the nonsingular rational points on `W` in affine coordinates. -/
@[simps]
noncomputable def toAffineAddEquiv : W.Point ≃+ W.toAffine.Point where
  toFun := toAffineLift
  invFun := fromAffine
  left_inv := by
    rintro @⟨⟨P⟩, hP⟩
    by_cases hPz : P z = 0
    · rw [Point.ext_iff, toAffineLift_eq, toAffine_of_Z_eq_zero hPz]
      exact Quotient.eq.mpr <| Setoid.symm <| equiv_zero_of_Z_eq_zero hP hPz
    · rw [Point.ext_iff, toAffineLift_eq, toAffine_of_Z_ne_zero hP hPz]
      exact Quotient.eq.mpr <| Setoid.symm <| equiv_some_of_Z_ne_zero hPz
  right_inv := by
    rintro (_ | _)
    · rw [← Affine.Point.zero_def, fromAffine_zero, toAffineLift_zero]
    · rw [fromAffine_some, toAffineLift_some]
  map_add' := toAffineLift_add

noncomputable instance : AddCommGroup W.Point where
  nsmul := nsmulRec
  zsmul := zsmulRec
  zero_add _ := (toAffineAddEquiv W).injective <| by
    simp only [map_add, toAffineAddEquiv_apply, toAffineLift_zero, zero_add]
  add_zero _ := (toAffineAddEquiv W).injective <| by
    simp only [map_add, toAffineAddEquiv_apply, toAffineLift_zero, add_zero]
  neg_add_cancel P := (toAffineAddEquiv W).injective <| by
    simp only [map_add, toAffineAddEquiv_apply, toAffineLift_neg, neg_add_cancel, toAffineLift_zero]
  add_comm _ _ := (toAffineAddEquiv W).injective <| by simp only [map_add, add_comm]
  add_assoc _ _ _ := (toAffineAddEquiv W).injective <| by simp only [map_add, add_assoc]

end Point

end Affine

section Map

/-! ### Maps across ring homomorphisms -/

variable {S : Type v} [CommRing S] (f : R →+* S)

@[simp]
protected lemma map_neg (P : Fin 3 → R) : (W'.map f).toJacobian.neg (f ∘ P) = f ∘ W'.neg P := by
  simp only [neg, map_negY, comp_fin3]
  map_simp

@[simp]
protected lemma map_add {K : Type v} [Field K] (f : F →+* K) {P Q : Fin 3 → F}
    (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    (W.map f).toJacobian.add (f ∘ P) (f ∘ Q) = f ∘ W.add P Q := by
  by_cases h : P ≈ Q
  · rw [add_of_equiv <| (comp_equiv_comp f hP hQ).mpr h, add_of_equiv h, map_dblXYZ]
  · rw [add_of_not_equiv <| h.comp (comp_equiv_comp f hP hQ).mp, add_of_not_equiv h, map_addXYZ]

end Map

section BaseChange

/-! ### Base changes across algebra homomorphisms -/

variable {R : Type r} [CommRing R] (W' : Jacobian R) {S : Type s} [CommRing S] [Algebra R S]
  {A : Type u} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  {B : Type v} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B] (f : A →ₐ[S] B)

lemma baseChange_neg (P : Fin 3 → A) :
    (W'.baseChange B).toJacobian.neg (f ∘ P) = f ∘ (W'.baseChange A).toJacobian.neg P := by
  rw [← RingHom.coe_coe, ← WeierstrassCurve.Jacobian.map_neg, map_baseChange]

variable [Algebra R F] [Algebra S F] [IsScalarTower R S F] {K : Type v} [Field K] [Algebra R K]
  [Algebra S K] [IsScalarTower R S K] (f : F →ₐ[S] K)

lemma baseChange_add {P Q : Fin 3 → F} (hP : (W'.baseChange F).toJacobian.Nonsingular P)
    (hQ : (W'.baseChange F).toJacobian.Nonsingular Q) :
    (W'.baseChange K).toJacobian.add (f ∘ P) (f ∘ Q) =
      f ∘ (W'.baseChange F).toJacobian.add P Q := by
  rw [← RingHom.coe_coe, ← WeierstrassCurve.Jacobian.map_add f hP hQ (K := K), map_baseChange]

end BaseChange

end WeierstrassCurve.Jacobian

/-- An abbreviation for `WeierstrassCurve.Jacobian.Point.fromAffine` for dot notation. -/
abbrev WeierstrassCurve.Affine.Point.toJacobian {R : Type u} [CommRing R] [Nontrivial R]
    {W : Affine R} (P : W.Point) : W.toJacobian.Point :=
  Jacobian.Point.fromAffine P
