/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathlib.Algebra.Ring.ULift
import Mathlib.RingTheory.WittVector.Basic
import Mathlib.Data.MvPolynomial.Funext

#align_import ring_theory.witt_vector.is_poly from "leanprover-community/mathlib"@"48fb5b5280e7c81672afc9524185ae994553ebf4"
/-!
# The `is_poly` predicate

`WittVector.IsPoly` is a (type-valued) predicate on functions `f : Π R, 𝕎 R → 𝕎 R`.
It asserts that there is a family of polynomials `φ : ℕ → MvPolynomial ℕ ℤ`,
such that the `n`th coefficient of `f x` is equal to `φ n` evaluated on the coefficients of `x`.
Many operations on Witt vectors satisfy this predicate (or an analogue for higher arity functions).
We say that such a function `f` is a *polynomial function*.

The power of satisfying this predicate comes from `WittVector.IsPoly.ext`.
It shows that if `φ` and `ψ` witness that `f` and `g` are polynomial functions,
then `f = g` not merely when `φ = ψ`, but in fact it suffices to prove
```
∀ n, bind₁ φ (wittPolynomial p _ n) = bind₁ ψ (wittPolynomial p _ n)
```
(in other words, when evaluating the Witt polynomials on `φ` and `ψ`, we get the same values)
which will then imply `φ = ψ` and hence `f = g`.

Even though this sufficient condition looks somewhat intimidating,
it is rather pleasant to check in practice;
more so than direct checking of `φ = ψ`.

In practice, we apply this technique to show that the composition of `WittVector.frobenius`
and `WittVector.verschiebung` is equal to multiplication by `p`.

## Main declarations

* `WittVector.IsPoly`, `WittVector.IsPoly₂`:
  two predicates that assert that a unary/binary function on Witt vectors
  is polynomial in the coefficients of the input values.
* `WittVector.IsPoly.ext`, `WittVector.IsPoly₂.ext`:
  two polynomial functions are equal if their families of polynomials are equal
  after evaluating the Witt polynomials on them.
* `WittVector.IsPoly.comp` (+ many variants) show that unary/binary compositions
  of polynomial functions are polynomial.
* `WittVector.idIsPoly`, `WittVector.negIsPoly`,
  `WittVector.addIsPoly₂`, `WittVector.mulIsPoly₂`:
  several well-known operations are polynomial functions
  (for Verschiebung, Frobenius, and multiplication by `p`, see their respective files).

## On higher arity analogues

Ideally, there should be a predicate `IsPolyₙ` for functions of higher arity,
together with `IsPolyₙ.comp` that shows how such functions compose.
Since mathlib does not have a library on composition of higher arity functions,
we have only implemented the unary and binary variants so far.
Nullary functions (a.k.a. constants) are treated
as constant functions and fall under the unary case.

## Tactics

There are important metaprograms defined in this file:
the tactics `ghost_simp` and `ghost_calc` and the attribute `@[ghost_simps]`.
These are used in combination to discharge proofs of identities between polynomial functions.

The `ghost_calc` tactic makes use of the `IsPoly` and `IsPoly₂` typeclass and its instances.
(In Lean 3, there was an `@[is_poly]` attribute to manage these instances,
because typeclass resolution did not play well with function composition.
This no longer seems to be an issue, so that such instances can be defined directly.)

Any lemma doing "ring equation rewriting" with polynomial functions should be tagged
`@[ghost_simps]`, e.g.
```lean
@[ghost_simps]
lemma bind₁_frobenius_poly_wittPolynomial (n : ℕ) :
  bind₁ (frobenius_poly p) (wittPolynomial p ℤ n) = (wittPolynomial p ℤ (n+1))
```

Proofs of identities between polynomial functions will often follow the pattern
```lean
  ghost_calc _
  <minor preprocessing>
  ghost_simp
```

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

namespace WittVector

universe u

variable {p : ℕ} {R S : Type u} {σ idx : Type*} [CommRing R] [CommRing S]

local notation "𝕎" => WittVector p -- type as `\bbW`

open MvPolynomial

open Function (uncurry)

variable (p)

noncomputable section

/-!
### The `IsPoly` predicate
-/


theorem poly_eq_of_wittPolynomial_bind_eq' [Fact p.Prime] (f g : ℕ → MvPolynomial (idx × ℕ) ℤ)
    (h : ∀ n, bind₁ f (wittPolynomial p _ n) = bind₁ g (wittPolynomial p _ n)) : f = g := by
  ext1 n
  -- ⊢ f n = g n
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  -- ⊢ ↑(MvPolynomial.map (Int.castRingHom ℚ)) (f n) = ↑(MvPolynomial.map (Int.cast …
  rw [← Function.funext_iff] at h
  -- ⊢ ↑(MvPolynomial.map (Int.castRingHom ℚ)) (f n) = ↑(MvPolynomial.map (Int.cast …
  replace h :=
    congr_arg (fun fam => bind₁ (MvPolynomial.map (Int.castRingHom ℚ) ∘ fam) (xInTermsOfW p ℚ n)) h
  simpa only [Function.comp, map_bind₁, map_wittPolynomial, ← bind₁_bind₁,
    bind₁_wittPolynomial_xInTermsOfW, bind₁_X_right] using h
#align witt_vector.poly_eq_of_witt_polynomial_bind_eq' WittVector.poly_eq_of_wittPolynomial_bind_eq'

theorem poly_eq_of_wittPolynomial_bind_eq [Fact p.Prime] (f g : ℕ → MvPolynomial ℕ ℤ)
    (h : ∀ n, bind₁ f (wittPolynomial p _ n) = bind₁ g (wittPolynomial p _ n)) : f = g := by
  ext1 n
  -- ⊢ f n = g n
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  -- ⊢ ↑(MvPolynomial.map (Int.castRingHom ℚ)) (f n) = ↑(MvPolynomial.map (Int.cast …
  rw [← Function.funext_iff] at h
  -- ⊢ ↑(MvPolynomial.map (Int.castRingHom ℚ)) (f n) = ↑(MvPolynomial.map (Int.cast …
  replace h :=
    congr_arg (fun fam => bind₁ (MvPolynomial.map (Int.castRingHom ℚ) ∘ fam) (xInTermsOfW p ℚ n)) h
  simpa only [Function.comp, map_bind₁, map_wittPolynomial, ← bind₁_bind₁,
    bind₁_wittPolynomial_xInTermsOfW, bind₁_X_right] using h
#align witt_vector.poly_eq_of_witt_polynomial_bind_eq WittVector.poly_eq_of_wittPolynomial_bind_eq

-- Ideally, we would generalise this to n-ary functions
-- But we don't have a good theory of n-ary compositions in mathlib
/--
A function `f : Π R, 𝕎 R → 𝕎 R` that maps Witt vectors to Witt vectors over arbitrary base rings
is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th
coefficient of `f x` is given by evaluating `φₙ` at the coefficients of `x`.

See also `WittVector.IsPoly₂` for the binary variant.

The `ghost_calc` tactic makes use of the `IsPoly` and `IsPoly₂` typeclass and its instances.
(In Lean 3, there was an `@[is_poly]` attribute to manage these instances,
because typeclass resolution did not play well with function composition.
This no longer seems to be an issue, so that such instances can be defined directly.)
-/
class IsPoly (f : ∀ ⦃R⦄ [CommRing R], WittVector p R → 𝕎 R) : Prop where mk' ::
  poly :
    ∃ φ : ℕ → MvPolynomial ℕ ℤ,
      ∀ ⦃R⦄ [CommRing R] (x : 𝕎 R), (f x).coeff = fun n => aeval x.coeff (φ n)
#align witt_vector.is_poly WittVector.IsPoly

/-- The identity function on Witt vectors is a polynomial function. -/
instance idIsPoly : IsPoly p fun _ _ => id :=
  ⟨⟨X, by intros; simp only [aeval_X, id]⟩⟩
          -- ⊢ (id x✝).coeff = fun n => ↑(aeval x✝.coeff) (X n)
                  -- 🎉 no goals
#align witt_vector.id_is_poly WittVector.idIsPoly

instance idIsPolyI' : IsPoly p fun _ _ a => a :=
  WittVector.idIsPoly _
#align witt_vector.id_is_poly_i' WittVector.idIsPolyI'

namespace IsPoly

instance : Inhabited (IsPoly p fun _ _ => id) :=
  ⟨WittVector.idIsPoly p⟩

variable {p}

theorem ext [Fact p.Prime] {f g} (hf : IsPoly p f) (hg : IsPoly p g)
    (h : ∀ (R : Type u) [_Rcr : CommRing R] (x : 𝕎 R) (n : ℕ),
        ghostComponent n (f x) = ghostComponent n (g x)) :
    ∀ (R : Type u) [_Rcr : CommRing R] (x : 𝕎 R), f x = g x := by
  obtain ⟨φ, hf⟩ := hf
  -- ⊢ ∀ (R : Type u) [_Rcr : CommRing R] (x : 𝕎 R), f x = g x
  obtain ⟨ψ, hg⟩ := hg
  -- ⊢ ∀ (R : Type u) [_Rcr : CommRing R] (x : 𝕎 R), f x = g x
  intros
  -- ⊢ f x✝ = g x✝
  ext n
  -- ⊢ coeff (f x✝) n = coeff (g x✝) n
  rw [hf, hg, poly_eq_of_wittPolynomial_bind_eq p φ ψ]
  -- ⊢ ∀ (n : ℕ), ↑(bind₁ φ) (wittPolynomial p ℤ n) = ↑(bind₁ ψ) (wittPolynomial p  …
  intro k
  -- ⊢ ↑(bind₁ φ) (wittPolynomial p ℤ k) = ↑(bind₁ ψ) (wittPolynomial p ℤ k)
  apply MvPolynomial.funext
  -- ⊢ ∀ (x : ℕ → ℤ), ↑(MvPolynomial.eval x) (↑(bind₁ φ) (wittPolynomial p ℤ k)) =  …
  intro x
  -- ⊢ ↑(MvPolynomial.eval x) (↑(bind₁ φ) (wittPolynomial p ℤ k)) = ↑(MvPolynomial. …
  simp only [hom_bind₁]
  -- ⊢ ↑(eval₂Hom (RingHom.comp (MvPolynomial.eval x) C) fun i => ↑(MvPolynomial.ev …
  specialize h (ULift ℤ) (mk p fun i => ⟨x i⟩) k
  -- ⊢ ↑(eval₂Hom (RingHom.comp (MvPolynomial.eval x) C) fun i => ↑(MvPolynomial.ev …
  simp only [ghostComponent_apply, aeval_eq_eval₂Hom] at h
  -- ⊢ ↑(eval₂Hom (RingHom.comp (MvPolynomial.eval x) C) fun i => ↑(MvPolynomial.ev …
  apply (ULift.ringEquiv.symm : ℤ ≃+* _).injective
  -- ⊢ ↑(RingEquiv.symm ULift.ringEquiv) (↑(eval₂Hom (RingHom.comp (MvPolynomial.ev …
  simp only [← RingEquiv.coe_toRingHom, map_eval₂Hom]
  -- ⊢ ↑(eval₂Hom (RingHom.comp (↑(RingEquiv.symm ULift.ringEquiv)) (RingHom.comp ( …
  convert h using 1
  -- ⊢ ↑(eval₂Hom (RingHom.comp (↑(RingEquiv.symm ULift.ringEquiv)) (RingHom.comp ( …
  all_goals
    --  porting note: this proof started with `funext i`
    simp only [hf, hg, MvPolynomial.eval, map_eval₂Hom]
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    ext1
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    simp only [coeff_mk]; rfl
#align witt_vector.is_poly.ext WittVector.IsPoly.ext

/-- The composition of polynomial functions is polynomial. -/
-- Porting note: made this an instance
instance comp {g f} [hg : IsPoly p g] [hf : IsPoly p f] :
    IsPoly p fun R _Rcr => @g R _Rcr ∘ @f R _Rcr := by
  obtain ⟨φ, hf⟩ := hf
  -- ⊢ IsPoly p fun R _Rcr => g ∘ f
  obtain ⟨ψ, hg⟩ := hg
  -- ⊢ IsPoly p fun R _Rcr => g ∘ f
  use fun n => bind₁ φ (ψ n)
  -- ⊢ ∀ ⦃R : Type ?u.543620⦄ [inst : CommRing R] (x : 𝕎 R), ((g ∘ f) x).coeff = fu …
  intros
  -- ⊢ ((g ∘ f) x✝).coeff = fun n => ↑(aeval x✝.coeff) (↑(bind₁ φ) (ψ n))
  simp only [aeval_bind₁, Function.comp, hg, hf]
  -- 🎉 no goals
#align witt_vector.is_poly.comp WittVector.IsPoly.comp

end IsPoly

/-- A binary function `f : Π R, 𝕎 R → 𝕎 R → 𝕎 R` on Witt vectors
is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th
coefficient of `f x y` is given by evaluating `φₙ` at the coefficients of `x` and `y`.

See also `WittVector.IsPoly` for the unary variant.

The `ghost_calc` tactic makes use of the `IsPoly` and `IsPoly₂` typeclass and its instances.
(In Lean 3, there was an `@[is_poly]` attribute to manage these instances,
because typeclass resolution did not play well with function composition.
This no longer seems to be an issue, so that such instances can be defined directly.)
-/
class IsPoly₂ (f : ∀ ⦃R⦄ [CommRing R], WittVector p R → 𝕎 R → 𝕎 R) : Prop where mk' ::
  poly :
    ∃ φ : ℕ → MvPolynomial (Fin 2 × ℕ) ℤ,
      ∀ ⦃R⦄ [CommRing R] (x y : 𝕎 R), (f x y).coeff = fun n => peval (φ n) ![x.coeff, y.coeff]
#align witt_vector.is_poly₂ WittVector.IsPoly₂

variable {p}

/-- The composition of polynomial functions is polynomial. -/
-- Porting note: made this an instance
instance IsPoly₂.comp {h f g} [hh : IsPoly₂ p h] [hf : IsPoly p f] [hg : IsPoly p g] :
    IsPoly₂ p fun R _Rcr x y => h (f x) (g y) := by
  obtain ⟨φ, hf⟩ := hf
  -- ⊢ IsPoly₂ p fun R _Rcr x y => h (f x) (g y)
  obtain ⟨ψ, hg⟩ := hg
  -- ⊢ IsPoly₂ p fun R _Rcr x y => h (f x) (g y)
  obtain ⟨χ, hh⟩ := hh
  -- ⊢ IsPoly₂ p fun R _Rcr x y => h (f x) (g y)
  refine' ⟨⟨fun n ↦ bind₁ (uncurry <|
    ![fun k ↦ rename (Prod.mk (0 : Fin 2)) (φ k),
      fun k ↦ rename (Prod.mk (1 : Fin 2)) (ψ k)]) (χ n), _⟩⟩
  intros
  -- ⊢ (h (f x✝) (g y✝)).coeff = fun n => peval ((fun n => ↑(bind₁ (uncurry ![fun k …
  funext n
  -- ⊢ coeff (h (f x✝) (g y✝)) n = peval ((fun n => ↑(bind₁ (uncurry ![fun k => ↑(r …
  simp only [peval, aeval_bind₁, Function.comp, hh, hf, hg, uncurry]
  -- ⊢ ↑(aeval fun a => Matrix.vecCons (fun n => ↑(aeval x✝.coeff) (φ n)) ![fun n = …
  apply eval₂Hom_congr rfl _ rfl
  -- ⊢ (fun a => Matrix.vecCons (fun n => ↑(aeval x✝.coeff) (φ n)) ![fun n => ↑(aev …
  ext ⟨i, n⟩
  -- ⊢ Matrix.vecCons (fun n => ↑(aeval x✝.coeff) (φ n)) ![fun n => ↑(aeval y✝.coef …
  fin_cases i <;>
  -- ⊢ Matrix.vecCons (fun n => ↑(aeval x✝.coeff) (φ n)) ![fun n => ↑(aeval y✝.coef …
    simp only [aeval_eq_eval₂Hom, eval₂Hom_rename, Function.comp, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one]
    -- porting note: added the rest of the proof.
    <;>
    open Matrix in
    simp only [algebraMap_int_eq, coe_eval₂Hom, Fin.mk_zero, Fin.mk_one, cons_val', empty_val',
      cons_val_fin_one, cons_val_zero, cons_val_one, eval₂Hom_rename, Function.comp, head_fin_const]

#align witt_vector.is_poly₂.comp WittVector.IsPoly₂.comp

/-- The composition of a polynomial function with a binary polynomial function is polynomial. -/
-- Porting note: made this an instance
instance IsPoly.comp₂ {g f} [hg : IsPoly p g] [hf : IsPoly₂ p f] :
    IsPoly₂ p fun R _Rcr x y => g (f x y) := by
  obtain ⟨φ, hf⟩ := hf
  -- ⊢ IsPoly₂ p fun R _Rcr x y => g (f x y)
  obtain ⟨ψ, hg⟩ := hg
  -- ⊢ IsPoly₂ p fun R _Rcr x y => g (f x y)
  use fun n => bind₁ φ (ψ n)
  -- ⊢ ∀ ⦃R : Type ?u.617923⦄ [inst : CommRing R] (x y : 𝕎 R), (g (f x y)).coeff =  …
  intros
  -- ⊢ (g (f x✝ y✝)).coeff = fun n => peval (↑(bind₁ φ) (ψ n)) ![x✝.coeff, y✝.coeff]
  simp only [peval, aeval_bind₁, Function.comp, hg, hf]
  -- 🎉 no goals
#align witt_vector.is_poly.comp₂ WittVector.IsPoly.comp₂

/-- The diagonal `λ x, f x x` of a polynomial function `f` is polynomial. -/
-- Porting note: made this an instance
instance IsPoly₂.diag {f} [hf : IsPoly₂ p f] : IsPoly p fun R _Rcr x => f x x := by
  obtain ⟨φ, hf⟩ := hf
  -- ⊢ IsPoly p fun R _Rcr x => f x x
  refine' ⟨⟨fun n => bind₁ (uncurry ![X, X]) (φ n), _⟩⟩
  -- ⊢ ∀ ⦃R : Type ?u.635107⦄ [inst : CommRing R] (x : 𝕎 R), (f x x).coeff = fun n  …
  intros; funext n
  -- ⊢ (f x✝ x✝).coeff = fun n => ↑(aeval x✝.coeff) ((fun n => ↑(bind₁ (uncurry ![X …
          -- ⊢ coeff (f x✝ x✝) n = ↑(aeval x✝.coeff) ((fun n => ↑(bind₁ (uncurry ![X, X]))  …
  simp only [hf, peval, uncurry, aeval_bind₁]
  -- ⊢ ↑(aeval fun a => Matrix.vecCons x✝.coeff ![x✝.coeff] a.fst a.snd) (φ n) = ↑( …
  apply eval₂Hom_congr rfl _ rfl
  -- ⊢ (fun a => Matrix.vecCons x✝.coeff ![x✝.coeff] a.fst a.snd) = fun i => ↑(aeva …
  ext ⟨i, k⟩;
  -- ⊢ Matrix.vecCons x✝.coeff ![x✝.coeff] (i, k).fst (i, k).snd = ↑(aeval x✝.coeff …
  fin_cases i <;>
  -- ⊢ Matrix.vecCons x✝.coeff ![x✝.coeff] ({ val := 0, isLt := (_ : 0 < 2) }, k).f …
    simp only [Matrix.head_cons, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    -- ⊢ Matrix.vecCons x✝.coeff ![x✝.coeff] { val := 0, isLt := (_ : 0 < 2) } k = ↑( …
    -- ⊢ Matrix.vecCons x✝.coeff ![x✝.coeff] { val := 1, isLt := (_ : (fun a => a < 2 …
    --  porting note: the end of the proof was added in the port.
    open Matrix in
    simp only [Fin.mk_zero, Fin.mk_one, cons_val', empty_val', cons_val_fin_one, cons_val_zero,
      aeval_X, head_fin_const, cons_val_one]
#align witt_vector.is_poly₂.diag WittVector.IsPoly₂.diag

-- Porting note: Lean 4's typeclass inference is sufficiently more powerful that we no longer
-- need the `@[is_poly]` attribute. Use of the attribute should just be replaced by changing the
-- theorem to an `instance`.

/-- The additive negation is a polynomial function on Witt vectors. -/
-- Porting note: replaced `@[is_poly]` with `instance`.
instance negIsPoly [Fact p.Prime] : IsPoly p fun R _ => @Neg.neg (𝕎 R) _ :=
  ⟨⟨fun n => rename Prod.snd (wittNeg p n), by
      intros; funext n
      -- ⊢ (-x✝).coeff = fun n => ↑(aeval x✝.coeff) ((fun n => ↑(rename Prod.snd) (witt …
              -- ⊢ coeff (-x✝) n = ↑(aeval x✝.coeff) ((fun n => ↑(rename Prod.snd) (wittNeg p n …
      rw [neg_coeff, aeval_eq_eval₂Hom, eval₂Hom_rename]
      -- ⊢ peval (wittNeg p n) ![x✝.coeff] = ↑(eval₂Hom (algebraMap ℤ R✝) (x✝.coeff ∘ P …
      apply eval₂Hom_congr rfl _ rfl
      -- ⊢ uncurry ![x✝.coeff] = x✝.coeff ∘ Prod.snd
      ext ⟨i, k⟩; fin_cases i; rfl⟩⟩
      -- ⊢ uncurry ![x✝.coeff] (i, k) = (x✝.coeff ∘ Prod.snd) (i, k)
                  -- ⊢ uncurry ![x✝.coeff] ({ val := 0, isLt := (_ : 0 < 1) }, k) = (x✝.coeff ∘ Pro …
                               -- 🎉 no goals
#align witt_vector.neg_is_poly WittVector.negIsPoly

section ZeroOne

/- To avoid a theory of 0-ary functions (a.k.a. constants)
we model them as constant unary functions. -/
/-- The function that is constantly zero on Witt vectors is a polynomial function. -/
instance zeroIsPoly [Fact p.Prime] : IsPoly p fun _ _ _ => 0 :=
  ⟨⟨0, by intros; funext n; simp only [Pi.zero_apply, AlgHom.map_zero, zero_coeff]⟩⟩
          -- ⊢ 0.coeff = fun n => ↑(aeval x✝.coeff) (OfNat.ofNat 0 n)
                  -- ⊢ coeff 0 n = ↑(aeval x✝.coeff) (OfNat.ofNat 0 n)
                            -- 🎉 no goals
#align witt_vector.zero_is_poly WittVector.zeroIsPoly

@[simp]
theorem bind₁_zero_wittPolynomial [Fact p.Prime] (n : ℕ) :
    bind₁ (0 : ℕ → MvPolynomial ℕ R) (wittPolynomial p R n) = 0 := by
  rw [← aeval_eq_bind₁, aeval_zero, constantCoeff_wittPolynomial, RingHom.map_zero]
  -- 🎉 no goals
#align witt_vector.bind₁_zero_witt_polynomial WittVector.bind₁_zero_wittPolynomial

/-- The coefficients of `1 : 𝕎 R` as polynomials. -/
def onePoly (n : ℕ) : MvPolynomial ℕ ℤ :=
  if n = 0 then 1 else 0
#align witt_vector.one_poly WittVector.onePoly

@[simp]
theorem bind₁_onePoly_wittPolynomial [hp : Fact p.Prime] (n : ℕ) :
    bind₁ onePoly (wittPolynomial p ℤ n) = 1 := by
  ext  -- porting note: `ext` was not in the mathport output.
  -- ⊢ MvPolynomial.coeff m✝ (↑(bind₁ onePoly) (wittPolynomial p ℤ n)) = MvPolynomi …
  rw [wittPolynomial_eq_sum_C_mul_X_pow, AlgHom.map_sum, Finset.sum_eq_single 0]
  · simp only [onePoly, one_pow, one_mul, AlgHom.map_pow, C_1, pow_zero, bind₁_X_right, if_true,
      eq_self_iff_true]
  · intro i _hi hi0
    -- ⊢ ↑(bind₁ onePoly) (↑C (↑p ^ i) * X i ^ p ^ (n - i)) = 0
    simp only [onePoly, if_neg hi0, zero_pow (pow_pos hp.1.pos _), mul_zero,
      AlgHom.map_pow, bind₁_X_right, AlgHom.map_mul]
  · rw [Finset.mem_range]
    -- ⊢ ¬0 < n + 1 → ↑(bind₁ onePoly) (↑C (↑p ^ 0) * X 0 ^ p ^ (n - 0)) = 0
    -- porting note: was `decide`
    simp only [add_pos_iff, or_true, not_true, pow_zero, map_one, ge_iff_le, nonpos_iff_eq_zero,
      tsub_zero, one_mul, gt_iff_lt, IsEmpty.forall_iff]
#align witt_vector.bind₁_one_poly_witt_polynomial WittVector.bind₁_onePoly_wittPolynomial

/-- The function that is constantly one on Witt vectors is a polynomial function. -/
instance oneIsPoly [Fact p.Prime] : IsPoly p fun _ _ _ => 1 :=
  ⟨⟨onePoly, by
      intros; funext n; cases n
      -- ⊢ 1.coeff = fun n => ↑(aeval x✝.coeff) (onePoly n)
              -- ⊢ coeff 1 n = ↑(aeval x✝.coeff) (onePoly n)
                        -- ⊢ coeff 1 Nat.zero = ↑(aeval x✝.coeff) (onePoly Nat.zero)
      · -- porting note: was `simp only [...]` but with slightly different `[...]`.
        simp only [Nat.zero_eq, lt_self_iff_false, one_coeff_zero, onePoly, ite_true, map_one]
        -- 🎉 no goals
      · -- porting note: was `simp only [...]` but with slightly different `[...]`.
        simp only [Nat.succ_pos', one_coeff_eq_of_pos, onePoly, Nat.succ_ne_zero, ite_false,
          map_zero]
  ⟩⟩
#align witt_vector.one_is_poly WittVector.oneIsPoly

end ZeroOne

/-- Addition of Witt vectors is a polynomial function. -/
-- Porting note: replaced `@[is_poly]` with `instance`.
instance addIsPoly₂ [Fact p.Prime] : IsPoly₂ p fun _ _ => (· + ·) :=
  --  porting note: the proof was
  --  `⟨⟨wittAdd p, by intros; dsimp only [WittVector.hasAdd]; simp [eval]⟩⟩`
  ⟨⟨wittAdd p, by intros; ext; exact add_coeff _ _ _⟩⟩
                  -- ⊢ (x✝ + y✝).coeff = fun n => peval (wittAdd p n) ![x✝.coeff, y✝.coeff]
                          -- ⊢ coeff (x✝¹ + y✝) x✝ = peval (wittAdd p x✝) ![x✝¹.coeff, y✝.coeff]
                               -- 🎉 no goals
#align witt_vector.add_is_poly₂ WittVector.addIsPoly₂

/-- Multiplication of Witt vectors is a polynomial function. -/
-- Porting note: replaced `@[is_poly]` with `instance`.
instance mulIsPoly₂ [Fact p.Prime] : IsPoly₂ p fun _ _ => (· * ·) :=
  --  porting note: the proof was
  -- `⟨⟨wittMul p, by intros; dsimp only [WittVector.hasMul]; simp [eval]⟩⟩`
  ⟨⟨wittMul p, by intros; ext; exact mul_coeff _ _ _⟩⟩
                  -- ⊢ (x✝ * y✝).coeff = fun n => peval (wittMul p n) ![x✝.coeff, y✝.coeff]
                          -- ⊢ coeff (x✝¹ * y✝) x✝ = peval (wittMul p x✝) ![x✝¹.coeff, y✝.coeff]
                               -- 🎉 no goals
#align witt_vector.mul_is_poly₂ WittVector.mulIsPoly₂

-- unfortunately this is not universe polymorphic, merely because `f` isn't
theorem IsPoly.map [Fact p.Prime] {f} (hf : IsPoly p f) (g : R →+* S) (x : 𝕎 R) :
    map g (f x) = f (map g x) := by
  -- this could be turned into a tactic “macro” (taking `hf` as parameter)
  -- so that applications do not have to worry about the universe issue
  -- see `IsPoly₂.map` for a slightly more general proof strategy
  obtain ⟨φ, hf⟩ := hf
  -- ⊢ ↑(WittVector.map g) (f x) = f (↑(WittVector.map g) x)
  ext n
  -- ⊢ coeff (↑(WittVector.map g) (f x)) n = coeff (f (↑(WittVector.map g) x)) n
  simp only [map_coeff, hf, map_aeval]
  -- ⊢ ↑(eval₂Hom (RingHom.comp g (algebraMap ℤ R)) fun i => ↑g (coeff x i)) (φ n)  …
  apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
  -- ⊢ (fun i => ↑g (coeff x i)) = (↑(WittVector.map g) x).coeff
  ext  -- porting note: this `ext` was not present in the mathport output
  -- ⊢ ↑g (coeff x x✝) = coeff (↑(WittVector.map g) x) x✝
  simp only [map_coeff]
  -- 🎉 no goals
#align witt_vector.is_poly.map WittVector.IsPoly.map

namespace IsPoly₂

--  porting note: the argument `(fun _ _ => (· + ·))` to `IsPoly₂` was just `_`.
instance [Fact p.Prime] : Inhabited (IsPoly₂ p (fun _ _ => (· + ·))) :=
  ⟨addIsPoly₂⟩

-- Porting note: maybe just drop this now that it works by `inferInstance`
/-- The composition of a binary polynomial function
 with a unary polynomial function in the first argument is polynomial. -/
theorem compLeft {g f} [IsPoly₂ p g] [IsPoly p f] :
    IsPoly₂ p fun _R _Rcr x y => g (f x) y :=
  inferInstance
#align witt_vector.is_poly₂.comp_left WittVector.IsPoly₂.compLeft

-- Porting note: maybe just drop this now that it works by `inferInstance`
/-- The composition of a binary polynomial function
 with a unary polynomial function in the second argument is polynomial. -/
theorem compRight {g f} [IsPoly₂ p g] [IsPoly p f] :
    IsPoly₂ p fun _R _Rcr x y => g x (f y) :=
  inferInstance
#align witt_vector.is_poly₂.comp_right WittVector.IsPoly₂.compRight

theorem ext [Fact p.Prime] {f g} (hf : IsPoly₂ p f) (hg : IsPoly₂ p g)
    (h : ∀ (R : Type u) [_Rcr : CommRing R] (x y : 𝕎 R) (n : ℕ),
        ghostComponent n (f x y) = ghostComponent n (g x y)) :
    ∀ (R) [_Rcr : CommRing R] (x y : 𝕎 R), f x y = g x y := by
  obtain ⟨φ, hf⟩ := hf
  -- ⊢ ∀ (R : Type u) [_Rcr : CommRing R] (x y : 𝕎 R), f x y = g x y
  obtain ⟨ψ, hg⟩ := hg
  -- ⊢ ∀ (R : Type u) [_Rcr : CommRing R] (x y : 𝕎 R), f x y = g x y
  intros
  -- ⊢ f x✝ y✝ = g x✝ y✝
  ext n
  -- ⊢ coeff (f x✝ y✝) n = coeff (g x✝ y✝) n
  rw [hf, hg, poly_eq_of_wittPolynomial_bind_eq' p φ ψ]
  -- ⊢ ∀ (n : ℕ), ↑(bind₁ φ) (wittPolynomial p ℤ n) = ↑(bind₁ ψ) (wittPolynomial p  …
  --  porting note: `clear x y` does not work, since `x, y` are now hygienic
  intro k
  -- ⊢ ↑(bind₁ φ) (wittPolynomial p ℤ k) = ↑(bind₁ ψ) (wittPolynomial p ℤ k)
  apply MvPolynomial.funext
  -- ⊢ ∀ (x : Fin 2 × ℕ → ℤ), ↑(MvPolynomial.eval x) (↑(bind₁ φ) (wittPolynomial p  …
  intro x
  -- ⊢ ↑(MvPolynomial.eval x) (↑(bind₁ φ) (wittPolynomial p ℤ k)) = ↑(MvPolynomial. …
  simp only [hom_bind₁]
  -- ⊢ ↑(eval₂Hom (RingHom.comp (MvPolynomial.eval x) C) fun i => ↑(MvPolynomial.ev …
  specialize h (ULift ℤ) (mk p fun i => ⟨x (0, i)⟩) (mk p fun i => ⟨x (1, i)⟩) k
  -- ⊢ ↑(eval₂Hom (RingHom.comp (MvPolynomial.eval x) C) fun i => ↑(MvPolynomial.ev …
  simp only [ghostComponent_apply, aeval_eq_eval₂Hom] at h
  -- ⊢ ↑(eval₂Hom (RingHom.comp (MvPolynomial.eval x) C) fun i => ↑(MvPolynomial.ev …
  apply (ULift.ringEquiv.symm : ℤ ≃+* _).injective
  -- ⊢ ↑(RingEquiv.symm ULift.ringEquiv) (↑(eval₂Hom (RingHom.comp (MvPolynomial.ev …
  simp only [← RingEquiv.coe_toRingHom, map_eval₂Hom]
  -- ⊢ ↑(eval₂Hom (RingHom.comp (↑(RingEquiv.symm ULift.ringEquiv)) (RingHom.comp ( …
  convert h using 1
  -- ⊢ ↑(eval₂Hom (RingHom.comp (↑(RingEquiv.symm ULift.ringEquiv)) (RingHom.comp ( …
  all_goals
    --  porting note: this proof started with `funext i`
    simp only [hf, hg, MvPolynomial.eval, map_eval₂Hom]
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    ext1
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    ext ⟨b, _⟩
    fin_cases b <;> simp only [coeff_mk, uncurry] <;> rfl
#align witt_vector.is_poly₂.ext WittVector.IsPoly₂.ext

-- unfortunately this is not universe polymorphic, merely because `f` isn't
theorem map [Fact p.Prime] {f} (hf : IsPoly₂ p f) (g : R →+* S) (x y : 𝕎 R) :
    map g (f x y) = f (map g x) (map g y) := by
  -- this could be turned into a tactic “macro” (taking `hf` as parameter)
  -- so that applications do not have to worry about the universe issue
  obtain ⟨φ, hf⟩ := hf
  -- ⊢ ↑(WittVector.map g) (f x y) = f (↑(WittVector.map g) x) (↑(WittVector.map g) …
  ext n
  -- ⊢ coeff (↑(WittVector.map g) (f x y)) n = coeff (f (↑(WittVector.map g) x) (↑( …
  simp only [map_coeff, hf, map_aeval, peval, uncurry]
  -- ⊢ ↑(eval₂Hom (RingHom.comp g (algebraMap ℤ R)) fun i => ↑g (Matrix.vecCons x.c …
  apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
  -- ⊢ (fun i => ↑g (Matrix.vecCons x.coeff ![y.coeff] i.fst i.snd)) = fun a => Mat …
  try ext ⟨i, k⟩; fin_cases i
  -- ⊢ ↑g (Matrix.vecCons x.coeff ![y.coeff] ({ val := 0, isLt := (_ : 0 < 2) }, k) …
  all_goals simp only [map_coeff, Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
  -- ⊢ ↑g (Matrix.vecCons x.coeff ![y.coeff] { val := 0, isLt := (_ : 0 < 2) } k) = …
  -- porting note: added the rest of the proof
  all_goals
    simp only [Fin.mk_zero, Fin.mk_one, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero, map_coeff, Matrix.head_fin_const]
#align witt_vector.is_poly₂.map WittVector.IsPoly₂.map

end IsPoly₂

attribute [ghost_simps] AlgHom.map_zero AlgHom.map_one AlgHom.map_add AlgHom.map_mul AlgHom.map_sub
  AlgHom.map_neg AlgHom.id_apply map_natCast RingHom.map_zero RingHom.map_one RingHom.map_mul
  RingHom.map_add RingHom.map_sub RingHom.map_neg RingHom.id_apply mul_add add_mul add_zero zero_add
  mul_one one_mul mul_zero zero_mul Nat.succ_ne_zero add_tsub_cancel_right
  Nat.succ_eq_add_one if_true eq_self_iff_true if_false forall_true_iff forall₂_true_iff
  forall₃_true_iff

end

namespace Tactic
open Lean Parser.Tactic Elab.Tactic

/-- A macro for a common simplification when rewriting with ghost component equations. -/
syntax (name := ghostSimp) "ghost_simp" (simpArgs)? : tactic

macro_rules
  | `(tactic| ghost_simp $[[$simpArgs,*]]?) => do
    let args := simpArgs.map (·.getElems) |>.getD #[]
    `(tactic| simp only [← sub_eq_add_neg, ghost_simps, $args,*])


/-- `ghost_calc` is a tactic for proving identities between polynomial functions.
Typically, when faced with a goal like
```lean
∀ (x y : 𝕎 R), verschiebung (x * frobenius y) = verschiebung x * y
```
you can
1. call `ghost_calc`
2. do a small amount of manual work -- maybe nothing, maybe `rintro`, etc
3. call `ghost_simp`

and this will close the goal.

`ghost_calc` cannot detect whether you are dealing with unary or binary polynomial functions.
You must give it arguments to determine this.
If you are proving a universally quantified goal like the above,
call `ghost_calc _ _`.
If the variables are introduced already, call `ghost_calc x y`.
In the unary case, use `ghost_calc _` or `ghost_calc x`.

`ghost_calc` is a light wrapper around type class inference.
All it does is apply the appropriate extensionality lemma and try to infer the resulting goals.
This is subtle and Lean's elaborator doesn't like it because of the HO unification involved,
so it is easier (and prettier) to put it in a tactic script.
-/
syntax (name := ghostCalc) "ghost_calc" (ppSpace colGt term:max)* : tactic

private def runIntro (ref : Syntax) (n : Name) : TacticM FVarId := do
  let fvarId ← liftMetaTacticAux fun g => do
    let (fv, g') ← g.intro n
    return (fv, [g'])
  withMainContext do
    Elab.Term.addLocalVarInfo ref (mkFVar fvarId)
  return fvarId

private def getLocalOrIntro (t : Term) : TacticM FVarId := do
  match t with
    | `(_) => runIntro t `_
    | `($id:ident) => getFVarId id <|> runIntro id id.getId
    | _ => Elab.throwUnsupportedSyntax

elab_rules : tactic | `(tactic| ghost_calc $[$ids']*) => do
  let ids ← ids'.mapM getLocalOrIntro
  withMainContext do
  let idsS ← ids.mapM (fun id => Elab.Term.exprToSyntax (.fvar id))
  let some (α, lhs, rhs) := (← getMainTarget'').eq?
    | throwError "ghost_calc expecting target to be an equality"
  let (``WittVector, #[_, R]) := α.getAppFnArgs
    | throwError "ghost_calc expecting target to be an equality of `WittVector`s"
  let instR ← Meta.synthInstance (← Meta.mkAppM ``CommRing #[R])
  unless instR.isFVar do
    throwError "{← Meta.inferType instR} instance is not local"
  let f ← Meta.mkLambdaFVars (#[R, instR] ++ ids.map .fvar) lhs
  let g ← Meta.mkLambdaFVars (#[R, instR] ++ ids.map .fvar) rhs
  let fS ← Elab.Term.exprToSyntax f
  let gS ← Elab.Term.exprToSyntax g
  match idsS with
    | #[x] => evalTactic (← `(tactic| refine IsPoly.ext (f := $fS) (g := $gS) ?_ ?_ ?_ _ $x))
    | #[x, y] => evalTactic (← `(tactic| refine IsPoly₂.ext (f := $fS) (g := $gS) ?_ ?_ ?_ _ $x $y))
    | _ => throwError "ghost_calc takes either one or two arguments"
  let nm ← withMainContext <|
    if let .fvar fvarId := (R : Expr) then
      fvarId.getUserName
    else
      Meta.getUnusedUserName `R
  evalTactic <| ← `(tactic| iterate 2 infer_instance)
  let R := mkIdent nm
  evalTactic <| ← `(tactic| clear! $R)
  evalTactic <| ← `(tactic| intro $(mkIdent nm):ident $(mkIdent (.str nm "_inst")):ident $ids'*)

end Tactic

end WittVector
