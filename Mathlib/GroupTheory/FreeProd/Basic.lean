/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import Mathlib.Algebra.PUnitInstances
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Congruence
import Mathlib.GroupTheory.Submonoid.Membership

/-!
# Free product of two monoids or groups

In this file we define `FreeProd M N` (notation: `M ⋆ N`) to be the free product of two monoids. The
same type is used for the free product of two monoids and for the free product of two groups.

The free product `M ⋆ N` has the following universal property: for any monoid `P` and homomorphisms
`f : M →* P`, `g : N →* P`, there exists a unique homomorphism `fg : M ⋆ N →* P` such that
`fg ∘ FreeProd.inl = f` and `fg ∘ FreeProd.inr = g`, where `FreeProd.inl : M →* M ⋆ N` and
`FreeProd.inr : N →* M ⋆ N` are canonical embeddings. This homomorphism `fg` is given by
`FreeProd.lift f g`.

We also define some homomorphisms and isomorphisms about `M ⋆ N`, and provide additive versions of
all definitions and theorems.

## Main definitions

### Types

* `FreeProd M N` (a.k.a. `M ⋆ N`): the free product of two monoids `M` and `N`.
* `FreeSum M N` (no notation): the additive version of `FreeProd`.

In other sections, we only list multiplicative definitions.

### Instances

* `MulOneClass`, `Monoid`, and `Group` structures on the free product `M ⋆ N`.

### Monoid homomorphisms

* `FreeProd.mk`: the projection `FreeMonoid (M ⊕ N) →* M ⋆ N`.

* `FreeProd.inl`, `FreeProd.inr`: canonical embeddings `M →* M ⋆ N` and `N →* M ⋆ N`.

* `FreeProd.lift`: construct a monoid homomorphism `M ⋆ N →* P` from homomorphisms `M →* P` and
  `N →* P`; see also `FreeProd.lift_equiv`.

* `FreeProd.clift`: a constructor for homomorphisms `M ⋆ N →* P` that allows the user to control the
  computational behavior.

* `FreeProd.map`: combine two homomorphisms `f : M →* N` and `g : M' →* N'` into `M ⋆ M' →* N ⋆ N'`.

* `FreeProd.swap`: the natural homomorphism `M ⋆ N →* N ⋆ M`.

* `FreeProd.fst`, `FreeProd.snd`, and `FreeProd.toProd`: natural projections `M ⋆ N →* M`,
  `M ⋆ N →* N`, and `M ⋆ N →* M × N`.

### Monoid isomorphisms

* `MulEquiv.freeProdCongr`: a `MulEquiv` version of `FreeProd.map`.
* `MulEquiv.freeProdComm`: a `MulEquiv` version of `FreeProd.swap`.
* `MulEquiv.freeProdAssoc`: associativity of the free product.
* `MulEquiv.freeProdPUnit`, `MulEquiv.punitFreeProd`: free product by `PUnit` on the left or on the
  right is isomorphic to the original monoid.

## Main results

The universal property of the free product is given by the definition `FreeProd.lift` and the lemma
`FreeProd.lift_unique`. We also prove a slightly more general extensionality lemma
`FreeProd.hom_ext` for homomorphisms `M ⋆ N →* P` and prove lots of basic lemmas like
`FreeProd.fst_comp_inl`.

## Implementation details

The definition of the free product of indexed families of monoids is [formalized in Mathlib
3](https://leanprover-community.github.io/mathlib_docs/find/free_product) under the name
`free_product` and is [not yet
ported](https://leanprover-community.github.io/mathlib-port-status/file/group_theory/free_product)
to Mathlib 4 at the time of writing. We refer to this formalization as `FreeProduct` in the rest of
this section.

While mathematically `M ⋆ N` is a particular case of the free product of an indexed family of
monoids, it is easier to build API from scratch instead of using something like

```
def FreeProd M N := FreeProduct ![M, N]
```

or

```
def FreeProd M N := FreeProduct (fun b : Bool => cond b M N)
```

There are several reasons to build an API from scratch.

- API about `Con` makes it easy to define the required type and prove the universal property, so
  there is little overhead compared to transfering API from `FreeProduct`.
- If `M` and `N` live in different universes, then the definition has to add `ULift`s; this makes
  it harder to transfer API and definitions.
- As of now, we have now way to automatically build an instance of `∀ k : Fin 2, Monoid (![M, N] k)`
  from `[Monoid M]` and `[Monoid N]`, not even speaking about more advanced typeclass assumptions
  that involve both `M` and `N`.
- Using list of `M ⊕ N` instead of, e.g., a list of `Σ k : Fin 2, ![M, N] k` as the underlying type
  makes it possible to write computationally effective code.

## Tags

group, monoid, free product

-/

open FreeMonoid Function List Set

/-- The minimal congruence relation on `FreeMonoid (M ⊕ N)` such that `FreeMonoid.of ∘ Sum.inl` and
`FreeMonoid.of ∘ Sum.inr` are monoid homomorphisms. -/
@[to_additive "The minimal congruence relation on `FreeMonoid (M ⊕ N)` such that `FreeMonoid.of ∘
Sum.inl` and `FreeMonoid.of ∘ Sum.inr` are monoid homomorphisms."]
def freeProdCon (M N : Type _) [MulOneClass M] [MulOneClass N] : Con (FreeMonoid (M ⊕ N)) :=
infₛ {c |
  (∀ x y : M, c (of (Sum.inl (x * y))) (of (Sum.inl x) * of (Sum.inl y)))
  ∧ (∀ x y : N, c (of (Sum.inr (x * y))) (of (Sum.inr x) * of (Sum.inr y)))
  ∧ c (of $ Sum.inl 1) 1 ∧ c (of $ Sum.inr 1) 1}

/-- Free product of two monoids or groups. -/
@[to_additive "Free product of two additive monoids or groups."]
def FreeProd (M N : Type _) [MulOneClass M] [MulOneClass N] := (freeProdCon M N).Quotient

@[inherit_doc]
local infix:70 " ⋆ " => FreeProd

namespace FreeProd

section MulOneClass

variable {M N M' N' P : Type _} [MulOneClass M] [MulOneClass N] [MulOneClass M'] [MulOneClass N']
  [MulOneClass P]

@[to_additive] protected instance : MulOneClass (M ⋆ N) := Con.mulOneClass _

/-- The natural projection `FreeMonoid (M ⊕ N) →* M ⋆ N`. -/
@[to_additive "The natural projection `FreeAddMonoid (M ⊕ N) →+ FreeSum M N`."]
def mk : FreeMonoid (M ⊕ N) →* M ⋆ N := Con.mk' _

@[to_additive (attr := simp)]
theorem con_ker_mk : Con.ker mk = freeProdCon M N := Con.mk'_ker _

@[to_additive]
theorem mk_surjective : Surjective (@mk M N _ _) := surjective_quot_mk _

@[to_additive (attr := simp)]
theorem mrange_mk : MonoidHom.mrange (@mk M N _ _) = ⊤ := Con.mrange_mk'

@[to_additive]
theorem mk_eq_mk {w₁ w₂ : FreeMonoid (M ⊕ N)} : mk w₁ = mk w₂ ↔ freeProdCon M N w₁ w₂ := Con.eq _

/-- The natural embedding `M →* M ⋆ N`. -/
@[to_additive "The natural embedding `M →+ FreeSum M N`."]
def inl : M →* M ⋆ N where
  toFun := fun x => mk (of (.inl x))
  map_one' := mk_eq_mk.2 $ fun _c hc => hc.2.2.1
  map_mul' := fun x y => mk_eq_mk.2 $ fun _c hc => hc.1 x y

/-- The natural embedding `N →* M ⋆ N`. -/
@[to_additive "The natural embedding `N →+ FreeSum M N`."]
def inr : N →* M ⋆ N where
  toFun := fun x => mk (of (.inr x))
  map_one' := mk_eq_mk.2 $ fun _c hc => hc.2.2.2
  map_mul' := fun x y => mk_eq_mk.2 $ fun _c hc => hc.2.1 x y

@[to_additive (attr := simp)]
theorem mk_of_inl (x : M) : (mk (of (.inl x)) : M ⋆ N) = inl x := rfl

@[to_additive (attr := simp)]
theorem mk_of_inr (x : N) : (mk (of (.inr x)) : M ⋆ N) = inr x := rfl

/-- Lift a monoid homomorphism `FreeMonoid (M ⊕ N) →* P` satisfying additional properties to
`M ⋆ N →* P`. In many cases, `FreeProd.lift` is more convenient.

Compared to `FreeProd.lift`, this definition allows a user to provide a custom computational
behavior. Also, it only needs `MulOneclass` assumptions while `FreeProd.lift` needs a `Monoid`
structure.
-/
@[to_additive "Lift an additive monoid homomorphism `FreeAddMonoid (M ⊕ N) →+ P` satisfying
additional properties to `FreeSum M N →+ P`.

Compared to `FreeSum.lift`, this definition allows a user to provide a custom computational
behavior. Also, it only needs `AddZeroclass` assumptions while `FreeSum.lift` needs an `AddMonoid`
structure. "]
def clift (f : FreeMonoid (M ⊕ N) →* P)
    (hM₁ : f (of (.inl 1)) = 1) (hN₁ : f (of (.inr 1)) = 1)
    (hM : ∀ x y, f (of (.inl (x * y))) = f (of (.inl x) * of (.inl y)))
    (hN : ∀ x y, f (of (.inr (x * y))) = f (of (.inr x) * of (.inr y))) :
    M ⋆ N →* P :=
  Con.lift _ f $ infₛ_le ⟨hM, hN, hM₁.trans (map_one f).symm, hN₁.trans (map_one f).symm⟩

@[to_additive (attr := simp)]
theorem clift_apply_inl (f : FreeMonoid (M ⊕ N) →* P) (hM₁ hN₁ hM hN) (x : M) :
    clift f hM₁ hN₁ hM hN (inl x) = f (of (.inl x)) :=
  rfl

@[to_additive (attr := simp)]
theorem clift_apply_inr (f : FreeMonoid (M ⊕ N) →* P) (hM₁ hN₁ hM hN) (x : N) :
    clift f hM₁ hN₁ hM hN (inr x) = f (of (.inr x)) :=
rfl

@[to_additive (attr := simp)]
theorem clift_apply_mk (f : FreeMonoid (M ⊕ N) →* P) (hM₁ hN₁ hM hN w) :
    clift f hM₁ hN₁ hM hN (mk w) = f w :=
rfl

@[to_additive (attr := simp)]
theorem clift_comp_mk (f : FreeMonoid (M ⊕ N) →* P) (hM₁ hN₁ hM hN) :
    (clift f hM₁ hN₁ hM hN).comp mk = f :=
FunLike.ext' rfl

@[to_additive (attr := simp)]
theorem mclosure_range_inl_union_inr :
    Submonoid.closure (range (inl : M →* M ⋆ N) ∪ range (inr : N →* M ⋆ N)) = ⊤ := by
  rw [← mrange_mk, MonoidHom.mrange_eq_map, ← closure_range_of, MonoidHom.map_mclosure,
    ← range_comp, Sum.range_eq]; rfl

@[to_additive (attr := simp)] theorem mrange_inl_sup_mrange_inr :
    MonoidHom.mrange (inl : M →* M ⋆ N) ⊔ MonoidHom.mrange (inr : N →* M ⋆ N) = ⊤ := by
  rw [← mclosure_range_inl_union_inr, Submonoid.closure_union, ← MonoidHom.coe_mrange,
    ← MonoidHom.coe_mrange, Submonoid.closure_eq, Submonoid.closure_eq]

/-- Extensionality lemma for monoid homomorphisms `M ⋆ N →* P`. If two homomorphisms agree on the
ranges of `FreeProd.inl` and `FreeProd.inr`, then they are equal. -/
@[to_additive (attr := ext 1100) "Extensionality lemma for additive monoid homomorphisms
`FreeSum M N →+ P`. If two homomorphisms agree on the ranges of `FreeSum.inl` and `FreeSum.inr`,
then they are equal."]
theorem hom_ext {f g : M ⋆ N →* P} (h₁ : f.comp inl = g.comp inl) (h₂ : f.comp inr = g.comp inr) :
    f = g :=
  MonoidHom.eq_of_eqOn_denseM mclosure_range_inl_union_inr $ eqOn_union.2
    ⟨eqOn_range.2 $ FunLike.ext'_iff.1 h₁, eqOn_range.2 $ FunLike.ext'_iff.1 h₂⟩

@[to_additive (attr := simp)]
theorem clift_mk :
    clift (mk : FreeMonoid (M ⊕ N) →* M ⋆ N) (map_one inl) (map_one inr) (map_mul inl)
      (map_mul inr) = .id _ :=
  hom_ext rfl rfl

/-- Map `M ⋆ N` to `M' ⋆ N'` by applying `Sum.map f g` to each element of the underlying list. -/
@[to_additive "Map `FreeSum M N` to `FreeSum M' N'` by applying `Sum.map f g` to each element of the
underlying list."]
def map (f : M →* M') (g : N →* N') : M ⋆ N →* M' ⋆ N' :=
  clift (mk.comp <| FreeMonoid.map <| Sum.map f g)
    (by simp only [MonoidHom.comp_apply, map_of, Sum.map_inl, map_one, mk_of_inl])
    (by simp only [MonoidHom.comp_apply, map_of, Sum.map_inr, map_one, mk_of_inr])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.map_inl, map_mul, mk_of_inl])
    fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.map_inr, map_mul, mk_of_inr]

@[to_additive (attr := simp)]
theorem map_mk_ofList (f : M →* M') (g : N →* N') (l : List (M ⊕ N)) :
    map f g (mk (ofList l)) = mk (ofList (l.map (Sum.map f g))) :=
  rfl

@[to_additive (attr := simp)]
theorem map_apply_inl (f : M →* M') (g : N →* N') (x : M) : map f g (inl x) = inl (f x) := rfl

@[to_additive (attr := simp)]
theorem map_apply_inr (f : M →* M') (g : N →* N') (x : N) : map f g (inr x) = inr (g x) := rfl

@[to_additive (attr := simp)]
theorem map_comp_inl (f : M →* M') (g : N →* N') : (map f g).comp inl = inl.comp f := rfl

@[to_additive (attr := simp)]
theorem map_comp_inr (f : M →* M') (g : N →* N') : (map f g).comp inr = inr.comp g := rfl

@[to_additive (attr := simp)]
theorem map_id_id : map (.id M) (.id N) = .id (M ⋆ N) := hom_ext rfl rfl

@[to_additive]
theorem map_comp_map {M'' N''} [MulOneClass M''] [MulOneClass N''] (f' : M' →* M'') (g' : N' →* N'')
    (f : M →* M') (g : N →* N') : (map f' g').comp (map f g) = map (f'.comp f) (g'.comp g) :=
  hom_ext rfl rfl

@[to_additive]
theorem map_map {M'' N''} [MulOneClass M''] [MulOneClass N''] (f' : M' →* M'') (g' : N' →* N'')
    (f : M →* M') (g : N →* N') (x : M ⋆ N) :
    map f' g' (map f g x) = map (f'.comp f) (g'.comp g) x :=
  FunLike.congr_fun (map_comp_map f' g' f g) x

variable (M N)

/-- Map `M ⋆ N` to `N ⋆ M` by applying `Sum.swap` to each element of the underlying list.

See also `MulEquiv.freeProdComm` for a `MulEquiv` version. -/
@[to_additive "Map `FreeSum M N` to `FreeSum N M` by applying `Sum.swap` to each element of the
underlying list.

See also `AddEquiv.freeSumComm` for an `AddEquiv` version."]
def swap : M ⋆ N →* N ⋆ M :=
  clift (mk.comp <| FreeMonoid.map Sum.swap)
    (by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inl, mk_of_inr, map_one])
    (by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inr, mk_of_inl, map_one])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inl, mk_of_inr, map_mul])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inr, mk_of_inl, map_mul])

@[to_additive (attr := simp)]
theorem swap_comp_swap : (swap M N).comp (swap N M) = .id _ := hom_ext rfl rfl

variable {M N}

@[to_additive (attr := simp)]
theorem swap_swap (x : M ⋆ N) : swap N M (swap M N x) = x :=
  FunLike.congr_fun (swap_comp_swap _ _) x

@[to_additive]
theorem swap_comp_map (f : M →* M') (g : N →* N') :
    (swap M' N').comp (map f g) = (map g f).comp (swap M N) :=
  hom_ext rfl rfl

@[to_additive]
theorem swap_map (f : M →* M') (g : N →* N') (x : M ⋆ N) :
    swap M' N' (map f g x) = map g f (swap M N x) :=
  FunLike.congr_fun (swap_comp_map f g) x

@[to_additive (attr := simp)] theorem swap_comp_inl : (swap M N).comp inl = inr := rfl
@[to_additive (attr := simp)] theorem swap_inl (x : M) : swap M N (inl x) = inr x := rfl
@[to_additive (attr := simp)] theorem swap_comp_inr : (swap M N).comp inr = inl := rfl
@[to_additive (attr := simp)] theorem swap_inr (x : N) : swap M N (inr x) = inl x := rfl

end MulOneClass

section Lift

variable {M N : Type _} [MulOneClass M] [MulOneClass N] [Monoid P]

/-- Lift a pair of monoid homomorphisms `f : M →* P`, `g : N →* P` to a monoid homomorphism
`M ⋆ N →* P`.

See also `FreeProd.clift` for a version that allows custom computational behavior and works for a
`MulOneClass` codomain.
-/
@[to_additive "Lift a pair of additive monoid homomorphisms `f : M →+ P`, `g : N →+ P` to an
additive monoid homomorphism `FreeSum M N →+ P`.

See also `FreeSum.clift` for a version that allows custom computational behavior and works for an
`AddZeroClass` codomain."]
def lift (f : M →* P) (g : N →* P) : (M ⋆ N) →* P :=
  clift (FreeMonoid.lift $ Sum.elim f g) (map_one f) (map_one g) (map_mul f) (map_mul g)

@[to_additive (attr := simp)]
theorem lift_apply_mk (f : M →* P) (g : N →* P) (x : FreeMonoid (M ⊕ N)) :
    lift f g (mk x) = FreeMonoid.lift (Sum.elim f g) x :=
  rfl

@[to_additive (attr := simp)]
theorem lift_apply_inl (f : M →* P) (g : N →* P) (x : M) : lift f g (inl x) = f x :=
  rfl

@[to_additive]
theorem lift_unique {f : M →* P} {g : N →* P} {fg : M ⋆ N →* P} (h₁ : fg.comp inl = f)
    (h₂ : fg.comp inr = g) : fg = lift f g :=
  hom_ext h₁ h₂

@[to_additive (attr := simp)]
theorem lift_comp_inl (f : M →* P) (g : N →* P) : (lift f g).comp inl = f := rfl

@[to_additive (attr := simp)]
theorem lift_apply_inr (f : M →* P) (g : N →* P) (x : N) : lift f g (inr x) = g x :=
  rfl

@[to_additive (attr := simp)]
theorem lift_comp_inr (f : M →* P) (g : N →* P) : (lift f g).comp inr = g := rfl

@[to_additive (attr := simp)]
theorem lift_comp_swap (f : M →* P) (g : N →* P) : (lift f g).comp (swap N M) = lift g f :=
  hom_ext rfl rfl

@[to_additive (attr := simp)]
theorem lift_swap (f : M →* P) (g : N →* P) (x : N ⋆ M) : lift f g (swap N M x) = lift g f x :=
  FunLike.congr_fun (lift_comp_swap f g) x

@[to_additive]
theorem comp_lift [Monoid P'] (f : P →* P') (g₁ : M →* P) (g₂ : N →* P) :
  f.comp (lift g₁ g₂) = lift (f.comp g₁) (f.comp g₂) :=
hom_ext (by rw [MonoidHom.comp_assoc, lift_comp_inl, lift_comp_inl])
  (by rw [MonoidHom.comp_assoc, lift_comp_inr, lift_comp_inr])

/-- `FreeProd.lift` as an equivalence. -/
@[to_additive "`FreeSum.lift` as an equivalence."]
def lift_equiv : (M →* P) × (N →* P) ≃ (M ⋆ N →* P) where
  toFun fg := lift fg.1 fg.2
  invFun f := (f.comp inl, f.comp inr)
  left_inv _ := rfl
  right_inv _ := Eq.symm <| lift_unique rfl rfl

end Lift

section ToProd
  
variable {M N : Type _} [Monoid M] [Monoid N]

@[to_additive] instance : Monoid (M ⋆ N) := Con.monoid _

/-- The natural projection `M ⋆ N →* M`. -/
@[to_additive "The natural projection `FreeSum M N →+ M`."]
def fst : M ⋆ N →* M := lift (.id M) 1

/-- The natural projection `M ⋆ N →* N`. -/
@[to_additive "The natural projection `FreeSum M N →+ N`."]
def snd : M ⋆ N →* N := lift 1 (.id N)

/-- The natural projection `M ⋆ N →* M × N`. -/
@[to_additive "The natural projection `FreeSum M N →+ M × N`."]
def toProd : M ⋆ N →* M × N := lift (.inl _ _) (.inr _ _)

@[to_additive (attr := simp)] theorem fst_comp_inl : (fst : M ⋆ N →* M).comp inl = .id _ := rfl
@[to_additive (attr := simp)] theorem fst_apply_inl (x : M) : fst (inl x : M ⋆ N) = x := rfl
@[to_additive (attr := simp)] theorem fst_comp_inr : (fst : M ⋆ N →* M).comp inr = 1 := rfl
@[to_additive (attr := simp)] theorem fst_apply_inr (x : N) : fst (inr x : M ⋆ N) = 1 := rfl
@[to_additive (attr := simp)] theorem snd_comp_inl : (snd : M ⋆ N →* N).comp inl = 1 := rfl
@[to_additive (attr := simp)] theorem snd_apply_inl (x : M) : snd (inl x : M ⋆ N) = 1 := rfl
@[to_additive (attr := simp)] theorem snd_comp_inr : (snd : M ⋆ N →* N).comp inr = .id _ := rfl
@[to_additive (attr := simp)] theorem snd_apply_inr (x : N) : snd (inr x : M ⋆ N) = x := rfl

@[to_additive (attr := simp)]
theorem toProd_comp_inl : (toProd : M ⋆ N →* M × N).comp inl = .inl _ _ := rfl

@[to_additive (attr := simp)]
theorem toProd_comp_inr : (toProd : M ⋆ N →* M × N).comp inr = .inr _ _ := rfl

@[to_additive (attr := simp)]
theorem toProd_apply_inl (x : M) : toProd (inl x : M ⋆ N) = (x, 1) := rfl

@[to_additive (attr := simp)]
theorem toProd_apply_inr (x : N) : toProd (inr x : M ⋆ N) = (1, x) := rfl

@[to_additive (attr := simp)]
theorem fst_prod_snd : (fst : M ⋆ N →* M).prod snd = toProd := by ext1 <;> rfl

@[to_additive (attr := simp)]
theorem prod_mk_fst_snd (x : M ⋆ N) : (fst x, snd x) = toProd x := by
  rw [← fst_prod_snd, MonoidHom.prod_apply]

@[to_additive (attr := simp)]
theorem fst_comp_toProd : (MonoidHom.fst M N).comp toProd = fst := by
  rw [← fst_prod_snd, MonoidHom.fst_comp_prod]

@[to_additive (attr := simp)]
theorem fst_toProd (x : M ⋆ N) : (toProd x).1 = fst x := by
  rw [← fst_comp_toProd]; rfl

@[to_additive (attr := simp)]
theorem snd_comp_toProd : (MonoidHom.snd M N).comp toProd = snd := by
  rw [← fst_prod_snd, MonoidHom.snd_comp_prod]

@[to_additive (attr := simp)]
theorem snd_toProd (x : M ⋆ N) : (toProd x).2 = snd x := by
  rw [← snd_comp_toProd]; rfl

@[to_additive (attr := simp)]
theorem fst_comp_swap : fst.comp (swap M N) = snd := lift_comp_swap _ _

@[to_additive (attr := simp)]
theorem fst_swap (x : M ⋆ N) : fst (swap M N x) = snd x := lift_swap _ _ _

@[to_additive (attr := simp)]
theorem snd_comp_swap : snd.comp (swap M N) = fst := lift_comp_swap _ _

@[to_additive (attr := simp)]
theorem snd_swap (x : M ⋆ N) : snd (swap M N x) = fst x := lift_swap _ _ _

@[to_additive (attr := simp)]
theorem lift_inr_inl : lift (inr : M →* N ⋆ M) inl = swap M N := hom_ext rfl rfl

@[to_additive (attr := simp)]
theorem lift_inl_inr : lift (inl : M →* M ⋆ N) inr = .id _ := hom_ext rfl rfl

end ToProd

section Group

variable {G H : Type _} [Group G] [Group H]

theorem mk_of_inv_mul : ∀ x : G ⊕ H, mk (of (x.map Inv.inv Inv.inv)) * mk (of x) = 1
| Sum.inl _ => map_mul_eq_one inl (mul_left_inv _)
| Sum.inr _ => map_mul_eq_one inr (mul_left_inv _)

theorem con_mul_left_inv (x : FreeMonoid (G ⊕ H)) :
    freeProdCon G H (ofList (x.toList.map (Sum.map Inv.inv Inv.inv)).reverse * x) 1 := by
  rw [← mk_eq_mk, map_mul, map_one]
  induction x using FreeMonoid.recOn
  case h0 => simp [Con.refl]
  case ih x xs ihx =>
    simp only [toList_of_mul, map_cons, reverse_cons, ofList_append, map_mul, ihx, ofList_singleton]
    rwa [mul_assoc, ← mul_assoc (mk (of _)), mk_of_inv_mul, one_mul]

instance : Inv (G ⋆ H) where
  inv := Quotient.map' (fun w => ofList (w.toList.map (Sum.map Inv.inv Inv.inv)).reverse)
    ((freeProdCon G H).map_of_mul_left_rel_one _ con_mul_left_inv)

theorem inv_def (w : FreeMonoid (G ⊕ H)) :
  (mk w)⁻¹ = mk (ofList (w.toList.map (Sum.map Inv.inv Inv.inv)).reverse) :=
rfl

instance : Group (G ⋆ H) where
  mul_left_inv := mk_surjective.forall.2 <| fun x => mk_eq_mk.2 (con_mul_left_inv x)

end Group

end FreeProd

open FreeProd

namespace MulEquiv

section MulOneClass

variable {M N M' N' : Type _} [MulOneClass M] [MulOneClass N] [MulOneClass M']
    [MulOneClass N']

/-- Lift two monoid equivalences `e : M ≃* N` and `e' : M' ≃* N'` to a monoid equivalence
`(M ⋆ M') ≃* (N ⋆ N')`. -/
@[to_additive (attr := simps! (config := { fullyApplied := false })) "Lift two additive monoid
equivalences `e : M ≃+ N` and `e' : M' ≃+ N'` to an additive monoid equivalence
`(FreeSum M M') ≃+ (FreeSum N N')`."]
def freeProdCongr (e : M ≃* N) (e' : M' ≃* N') : (M ⋆ M') ≃* (N ⋆ N') :=
  (FreeProd.map (e : M →* N) (e' : M' →* N')).toMulEquiv (FreeProd.map e.symm e'.symm)
    (by ext <;> simp) (by ext <;> simp)

variable (M N)

/-- A `MulEquiv` version of `FreeProd.swap`. -/
@[to_additive (attr := simps! (config := { fullyApplied := false }))
  "An `AddEquiv` version of `FreeSum.swap`."]
def freeProdComm : M ⋆ N ≃* N ⋆ M :=
  (FreeProd.swap _ _).toMulEquiv (FreeProd.swap _ _) (FreeProd.swap_comp_swap _ _)
    (FreeProd.swap_comp_swap _ _)

end MulOneClass

variable (M N P : Type _) [Monoid M] [Monoid N] [Monoid P]

/-- A multiplicative equivalence between `(M ⋆ N) ⋆ P` and `M ⋆ (N ⋆ P)`. -/
@[to_additive "An additive equivalence between `FreeSum (FreeSum M N) P` and
`FreeSum M (FreeSum N P)`."]
def freeProdAssoc : (M ⋆ N) ⋆ P ≃* M ⋆ (N ⋆ P) :=
  MonoidHom.toMulEquiv
    (FreeProd.lift (FreeProd.map (.id M) inl) (inr.comp inr))
    (FreeProd.lift (inl.comp inl) (FreeProd.map inr (.id P)))
    (by ext <;> rfl) (by ext <;> rfl)

variable {M N P}

@[to_additive (attr := simp)]
theorem freeProdAssoc_apply_inl_inl (x : M) : freeProdAssoc M N P (inl (inl x)) = inl x := rfl

@[to_additive (attr := simp)]
theorem freeProdAssoc_apply_inl_inr (x : N) : freeProdAssoc M N P (inl (inr x)) = inr (inl x) := rfl

@[to_additive (attr := simp)]
theorem freeProdAssoc_apply_inr (x : P) : freeProdAssoc M N P (inr x) = inr (inr x) := rfl

@[to_additive (attr := simp)]
theorem freeProdAssoc_symm_apply_inl (x : M) : (freeProdAssoc M N P).symm (inl x) = inl (inl x) :=
  rfl

@[to_additive (attr := simp)]
theorem freeProdAssoc_symm_apply_inr_inl (x : N) :
    (freeProdAssoc M N P).symm (inr (inl x)) = inl (inr x) :=
  rfl

@[to_additive (attr := simp)]
theorem freeProdAssoc_symm_apply_inr_inr (x : P) :
    (freeProdAssoc M N P).symm (inr (inr x)) = inr x :=
  rfl

variable (M)

/-- Isomorphism between `M ⋆ PUnit` and `M`. -/
@[simps! (config := {fullyApplied := false})]
def freeProdPUnit : M ⋆ PUnit ≃* M :=
  MonoidHom.toMulEquiv fst inl (hom_ext rfl <| Subsingleton.elim _ _) fst_comp_inl

/-- Isomorphism between `PUnit ⋆ M` and `M`. -/
@[simps! (config := {fullyApplied := false})]
def punitFreeProd : PUnit ⋆ M ≃* M :=
  MonoidHom.toMulEquiv snd inr (hom_ext (Subsingleton.elim _ _) rfl) snd_comp_inr

end MulEquiv

-- TODO: use `to_additive` to generate the next 2 `AddEquiv`s

namespace AddEquiv

variable [AddMonoid M]

/-- Isomorphism between `M ⋆ PUnit` and `M`. -/
@[simps! (config := {fullyApplied := false})]
def freeSumUnit : FreeSum M PUnit ≃+ M :=
  AddMonoidHom.toAddEquiv FreeSum.fst FreeSum.inl
    (FreeSum.hom_ext rfl <| Subsingleton.elim _ _) FreeSum.fst_comp_inl

/-- Isomorphism between `PUnit ⋆ M` and `M`. -/
@[simps! (config := {fullyApplied := false})]
def punitFreeSumrod : FreeSum PUnit M ≃+ M :=
  AddMonoidHom.toAddEquiv FreeSum.snd FreeSum.inr
    (FreeSum.hom_ext (Subsingleton.elim _ _) rfl) FreeSum.snd_comp_inr

end AddEquiv
