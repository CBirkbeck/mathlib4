/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/
import Mathlib.Topology.Sheaves.PUnit
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.Functors

#align_import topology.sheaves.skyscraper from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Skyscraper (pre)sheaves

A skyscraper (pre)sheaf `𝓕 : (pre)sheaf C X` is the (pre)sheaf with value `A` at point `p₀` that is
supported only at open sets contain `p₀`, i.e. `𝓕(U) = A` if `p₀ ∈ U` and `𝓕(U) = *` if `p₀ ∉ U`
where `*` is a terminal object of `C`. In terms of stalks, `𝓕` is supported at all specializations
of `p₀`, i.e. if `p₀ ⤳ x` then `𝓕ₓ ≅ A` and if `¬ p₀ ⤳ x` then `𝓕ₓ ≅ *`.

## Main definitions

* `skyscraper_presheaf`: `skyscraper_presheaf p₀ A` is the skyscraper presheaf at point `p₀` with
  value `A`.
* `skyscraper_sheaf`: the skyscraper presheaf satisfies the sheaf condition.

## Main statements

* `skyscraper_presheaf_stalk_of_specializes`: if `y ∈ closure {p₀}` then the stalk of
  `skyscraper_presheaf p₀ A` at `y` is `A`.
* `skyscraper_presheaf_stalk_of_not_specializes`: if `y ∉ closure {p₀}` then the stalk of
  `skyscraper_presheaf p₀ A` at `y` is `*` the terminal object.

TODO: generalize universe level when calculating stalks, after generalizing universe level of stalk.
-/

noncomputable section

open TopologicalSpace TopCat CategoryTheory CategoryTheory.Limits Opposite

universe u v w

variable {X : TopCat.{u}} (p₀ : X) [∀ U : Opens X, Decidable (p₀ ∈ U)]

section

variable {C : Type v} [Category.{w} C] [HasTerminal C] (A : C)

/-- A skyscraper presheaf is a presheaf supported at a single point: if `p₀ ∈ X` is a specified
point, then the skyscraper presheaf `𝓕` with value `A` is defined by `U ↦ A` if `p₀ ∈ U` and
`U ↦ *` if `p₀ ∉ A` where `*` is some terminal object.
-/
@[simps]
def skyscraperPresheaf : Presheaf C X where
  obj U := if p₀ ∈ unop U then A else terminal C
  map {U V} i :=
    if h : p₀ ∈ unop V then eqToHom <| by dsimp; erw [if_pos h, if_pos (leOfHom i.unop h)]
                                          -- ⊢ (if p₀ ∈ U.unop then A else ⊤_ C) = if p₀ ∈ V.unop then A else ⊤_ C
                                                 -- 🎉 no goals
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  map_id U :=
    (em (p₀ ∈ U.unop)).elim (fun h => dif_pos h) fun h =>
      ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext _ _
  map_comp {U V W} iVU iWV := by
    by_cases hW : p₀ ∈ unop W
    -- ⊢ { obj := fun U => if p₀ ∈ U.unop then A else ⊤_ C, map := fun {U V} i => if  …
    · have hV : p₀ ∈ unop V := leOfHom iWV.unop hW
      -- ⊢ { obj := fun U => if p₀ ∈ U.unop then A else ⊤_ C, map := fun {U V} i => if  …
      simp only [dif_pos hW, dif_pos hV, eqToHom_trans]
      -- 🎉 no goals
    · dsimp; rw [dif_neg hW]; apply ((if_neg hW).symm.ndrec terminalIsTerminal).hom_ext
      -- ⊢ (if h : p₀ ∈ W.unop then eqToHom (_ : (if p₀ ∈ U.unop then A else ⊤_ C) = if …
             -- ⊢ IsTerminal.from ((_ : (⊤_ C) = if p₀ ∈ W.unop then A else ⊤_ C) ▸ terminalIs …
                              -- 🎉 no goals
#align skyscraper_presheaf skyscraperPresheaf

theorem skyscraperPresheaf_eq_pushforward
    [hd : ∀ U : Opens (TopCat.of PUnit.{u + 1}), Decidable (PUnit.unit ∈ U)] :
    skyscraperPresheaf p₀ A =
      ContinuousMap.const (TopCat.of PUnit) p₀ _*
        skyscraperPresheaf (X := TopCat.of PUnit) PUnit.unit A := by
  convert_to @skyscraperPresheaf X p₀ (fun U => hd <| (Opens.map <| ContinuousMap.const _ p₀).obj U)
    C _ _ A = _ <;> congr
                    -- 🎉 no goals
                    -- 🎉 no goals
#align skyscraper_presheaf_eq_pushforward skyscraperPresheaf_eq_pushforward

/-- Taking skyscraper presheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
@[simps]
def SkyscraperPresheafFunctor.map' {a b : C} (f : a ⟶ b) :
    skyscraperPresheaf p₀ a ⟶ skyscraperPresheaf p₀ b where
  app U :=
    if h : p₀ ∈ U.unop then eqToHom (if_pos h) ≫ f ≫ eqToHom (if_pos h).symm
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  naturality U V i := by
    simp only [skyscraperPresheaf_map]; by_cases hV : p₀ ∈ V.unop
    -- ⊢ ((if h : p₀ ∈ V.unop then eqToHom (_ : (fun U => if p₀ ∈ U.unop then a else  …
                                        -- ⊢ ((if h : p₀ ∈ V.unop then eqToHom (_ : (fun U => if p₀ ∈ U.unop then a else  …
    · have hU : p₀ ∈ U.unop := leOfHom i.unop hV; split_ifs <;>
      -- ⊢ ((if h : p₀ ∈ V.unop then eqToHom (_ : (fun U => if p₀ ∈ U.unop then a else  …
                                                  -- ⊢ eqToHom (_ : (fun U => if p₀ ∈ U.unop then a else ⊤_ C) U = (fun U => if p₀  …
      simp only [eqToHom_trans_assoc, Category.assoc, eqToHom_trans]
      -- 🎉 no goals
      -- 🎉 no goals
    · apply ((if_neg hV).symm.ndrec terminalIsTerminal).hom_ext
      -- 🎉 no goals
#align skyscraper_presheaf_functor.map' SkyscraperPresheafFunctor.map'

theorem SkyscraperPresheafFunctor.map'_id {a : C} :
    SkyscraperPresheafFunctor.map' p₀ (𝟙 a) = 𝟙 _ := by
  -- Porting note : `ext1` doesn't work here,
  -- see https://github.com/leanprover-community/mathlib4/issues/5229
  refine NatTrans.ext _ _ <| funext fun U => ?_
  -- ⊢ NatTrans.app (map' p₀ (𝟙 a)) U = NatTrans.app (𝟙 (skyscraperPresheaf p₀ a)) U
  simp only [SkyscraperPresheafFunctor.map'_app, NatTrans.id_app]; split_ifs <;> aesop_cat
  -- ⊢ (if h : p₀ ∈ U.unop then eqToHom (_ : (if p₀ ∈ U.unop then a else ⊤_ C) = a) …
                                                                   -- ⊢ eqToHom (_ : (if p₀ ∈ U.unop then a else ⊤_ C) = a) ≫ 𝟙 a ≫ eqToHom (_ : a = …
                                                                                 -- 🎉 no goals
                                                                                 -- 🎉 no goals
#align skyscraper_presheaf_functor.map'_id SkyscraperPresheafFunctor.map'_id

theorem SkyscraperPresheafFunctor.map'_comp {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    SkyscraperPresheafFunctor.map' p₀ (f ≫ g) =
      SkyscraperPresheafFunctor.map' p₀ f ≫ SkyscraperPresheafFunctor.map' p₀ g := by
  -- Porting note : `ext1` doesn't work here,
  -- see https://github.com/leanprover-community/mathlib4/issues/5229
  refine NatTrans.ext _ _ <| funext fun U => ?_
  -- ⊢ NatTrans.app (map' p₀ (f ≫ g)) U = NatTrans.app (map' p₀ f ≫ map' p₀ g) U
  -- Porting note : change `simp` to `rw`
  rw [NatTrans.comp_app]
  -- ⊢ NatTrans.app (map' p₀ (f ≫ g)) U = NatTrans.app (map' p₀ f) U ≫ NatTrans.app …
  simp only [SkyscraperPresheafFunctor.map'_app]
  -- ⊢ (if h : p₀ ∈ U.unop then eqToHom (_ : (if p₀ ∈ U.unop then a else ⊤_ C) = a) …
  split_ifs with h <;> aesop_cat
  -- ⊢ eqToHom (_ : (if p₀ ∈ U.unop then a else ⊤_ C) = a) ≫ (f ≫ g) ≫ eqToHom (_ : …
                       -- 🎉 no goals
                       -- 🎉 no goals
#align skyscraper_presheaf_functor.map'_comp SkyscraperPresheafFunctor.map'_comp

/-- Taking skyscraper presheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
@[simps]
def skyscraperPresheafFunctor : C ⥤ Presheaf C X where
  obj := skyscraperPresheaf p₀
  map := SkyscraperPresheafFunctor.map' p₀
  map_id _ := SkyscraperPresheafFunctor.map'_id p₀
  map_comp := SkyscraperPresheafFunctor.map'_comp p₀
#align skyscraper_presheaf_functor skyscraperPresheafFunctor

end

section

-- In this section, we calculate the stalks for skyscraper presheaves.
-- We need to restrict universe level.
variable {C : Type v} [Category.{u} C] (A : C) [HasTerminal C]

/-- The cocone at `A` for the stalk functor of `skyscraper_presheaf p₀ A` when `y ∈ closure {p₀}`
-/
@[simps]
def skyscraperPresheafCoconeOfSpecializes {y : X} (h : p₀ ⤳ y) :
    Cocone ((OpenNhds.inclusion y).op ⋙ skyscraperPresheaf p₀ A) where
  pt := A
  ι :=
    { app := fun U => eqToHom <| if_pos <| h.mem_open U.unop.1.2 U.unop.2
      naturality := fun U V inc => by
        change dite _ _ _ ≫ _ = _; rw [dif_pos]
        -- ⊢ (if h : p₀ ∈ ((OpenNhds.inclusion y).op.obj V).unop then (fun h => eqToHom ( …
                                   -- ⊢ (fun h => eqToHom (_ : (fun U => if p₀ ∈ U.unop then A else ⊤_ C) ((OpenNhds …
        swap -- Porting note : swap goal to prevent proving same thing twice
        -- ⊢ p₀ ∈ ((OpenNhds.inclusion y).op.obj V).unop
        · exact h.mem_open V.unop.1.2 V.unop.2
          -- 🎉 no goals
        · erw [Category.comp_id, eqToHom_trans] }
          -- 🎉 no goals
#align skyscraper_presheaf_cocone_of_specializes skyscraperPresheafCoconeOfSpecializes

/--
The cocone at `A` for the stalk functor of `skyscraper_presheaf p₀ A` when `y ∈ closure {p₀}` is a
colimit
-/
noncomputable def skyscraperPresheafCoconeIsColimitOfSpecializes {y : X} (h : p₀ ⤳ y) :
    IsColimit (skyscraperPresheafCoconeOfSpecializes p₀ A h) where
  desc c := eqToHom (if_pos trivial).symm ≫ c.ι.app (op ⊤)
  fac c U := by
    dsimp -- Porting note : added a `dsimp`
    -- ⊢ eqToHom (_ : (if p₀ ∈ U.unop.obj.carrier then A else ⊤_ C) = A) ≫ eqToHom (_ …
    rw [← c.w (homOfLE <| (le_top : unop U ≤ _)).op]
    -- ⊢ eqToHom (_ : (if p₀ ∈ U.unop.obj.carrier then A else ⊤_ C) = A) ≫ eqToHom (_ …
    change _ ≫ _ ≫ dite _ _ _ ≫ _ = _
    -- ⊢ eqToHom (_ : (if p₀ ∈ U.unop.obj.carrier then A else ⊤_ C) = A) ≫ eqToHom (_ …
    rw [dif_pos]
    -- ⊢ eqToHom (_ : (if p₀ ∈ U.unop.obj.carrier then A else ⊤_ C) = A) ≫ eqToHom (_ …
    · simp only [skyscraperPresheafCoconeOfSpecializes_ι_app, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, unop_op, op_unop]
    · exact h.mem_open U.unop.1.2 U.unop.2
      -- 🎉 no goals
  uniq c f h := by
    dsimp -- Porting note : added a `dsimp`
    -- ⊢ f = eqToHom (_ : A = if True then A else ⊤_ C) ≫ NatTrans.app c.ι (op ⊤)
    rw [← h, skyscraperPresheafCoconeOfSpecializes_ι_app, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
#align skyscraper_presheaf_cocone_is_colimit_of_specializes skyscraperPresheafCoconeIsColimitOfSpecializes

/-- If `y ∈ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ A` at `y` is `A`.
-/
noncomputable def skyscraperPresheafStalkOfSpecializes [HasColimits C] {y : X} (h : p₀ ⤳ y) :
    (skyscraperPresheaf p₀ A).stalk y ≅ A :=
  colimit.isoColimitCocone ⟨_, skyscraperPresheafCoconeIsColimitOfSpecializes p₀ A h⟩
#align skyscraper_presheaf_stalk_of_specializes skyscraperPresheafStalkOfSpecializes

/-- The cocone at `*` for the stalk functor of `skyscraper_presheaf p₀ A` when `y ∉ closure {p₀}`
-/
@[simps]
def skyscraperPresheafCocone (y : X) : Cocone ((OpenNhds.inclusion y).op ⋙ skyscraperPresheaf p₀ A)
    where
  pt := terminal C
  ι :=
    { app := fun _ => terminal.from _
      naturality := fun _ _ _ => terminalIsTerminal.hom_ext _ _ }
#align skyscraper_presheaf_cocone skyscraperPresheafCocone

/--
The cocone at `*` for the stalk functor of `skyscraper_presheaf p₀ A` when `y ∉ closure {p₀}` is a
colimit
-/
noncomputable def skyscraperPresheafCoconeIsColimitOfNotSpecializes {y : X} (h : ¬p₀ ⤳ y) :
    IsColimit (skyscraperPresheafCocone p₀ A y) :=
  let h1 : ∃ U : OpenNhds y, p₀ ∉ U.1 :=
    let ⟨U, ho, h₀, hy⟩ := not_specializes_iff_exists_open.mp h
    ⟨⟨⟨U, ho⟩, h₀⟩, hy⟩
  { desc := fun c => eqToHom (if_neg h1.choose_spec).symm ≫ c.ι.app (op h1.choose)
    fac := fun c U => by
      change _ = c.ι.app (op U.unop)
      -- ⊢ NatTrans.app (skyscraperPresheafCocone p₀ A y).ι U ≫ (fun c => eqToHom (_ :  …
      simp only [← c.w (homOfLE <| @inf_le_left _ _ h1.choose U.unop).op, ←
        c.w (homOfLE <| @inf_le_right _ _ h1.choose U.unop).op, ← Category.assoc]
      congr 1
      -- ⊢ (NatTrans.app (skyscraperPresheafCocone p₀ A y).ι U ≫ eqToHom (_ : (skyscrap …
      refine' ((if_neg _).symm.ndrec terminalIsTerminal).hom_ext _ _
      -- ⊢ ¬p₀ ∈ ((OpenNhds.inclusion y).op.obj (op (Exists.choose (_ : ∃ U, ¬p₀ ∈ U.ob …
      exact fun h => h1.choose_spec h.1
      -- 🎉 no goals
    uniq := fun c f H => by
      dsimp -- Porting note : added a `dsimp`
      -- ⊢ f = eqToHom (_ : (⊤_ C) = if p₀ ∈ (Exists.choose (_ : ∃ U, ¬p₀ ∈ U.obj)).obj …
      rw [← Category.id_comp f, ← H, ← Category.assoc]
      -- ⊢ 𝟙 (skyscraperPresheafCocone p₀ A y).pt ≫ f = (eqToHom (_ : (⊤_ C) = if p₀ ∈  …
      congr 1; apply terminalIsTerminal.hom_ext }
      -- ⊢ 𝟙 (skyscraperPresheafCocone p₀ A y).pt = eqToHom (_ : (⊤_ C) = if p₀ ∈ (Exis …
               -- 🎉 no goals
#align skyscraper_presheaf_cocone_is_colimit_of_not_specializes skyscraperPresheafCoconeIsColimitOfNotSpecializes

/-- If `y ∉ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ A` at `y` is isomorphic to a
terminal object.
-/
noncomputable def skyscraperPresheafStalkOfNotSpecializes [HasColimits C] {y : X} (h : ¬p₀ ⤳ y) :
    (skyscraperPresheaf p₀ A).stalk y ≅ terminal C :=
  colimit.isoColimitCocone ⟨_, skyscraperPresheafCoconeIsColimitOfNotSpecializes _ A h⟩
#align skyscraper_presheaf_stalk_of_not_specializes skyscraperPresheafStalkOfNotSpecializes

/-- If `y ∉ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ A` at `y` is a terminal object
-/
def skyscraperPresheafStalkOfNotSpecializesIsTerminal [HasColimits C] {y : X} (h : ¬p₀ ⤳ y) :
    IsTerminal ((skyscraperPresheaf p₀ A).stalk y) :=
  IsTerminal.ofIso terminalIsTerminal <| (skyscraperPresheafStalkOfNotSpecializes _ _ h).symm
#align skyscraper_presheaf_stalk_of_not_specializes_is_terminal skyscraperPresheafStalkOfNotSpecializesIsTerminal

theorem skyscraperPresheaf_isSheaf : (skyscraperPresheaf p₀ A).IsSheaf := by
  classical exact
    (Presheaf.isSheaf_iso_iff (eqToIso <| skyscraperPresheaf_eq_pushforward p₀ A)).mpr <|
      (Sheaf.pushforward_sheaf_of_sheaf _
        (Presheaf.isSheaf_on_punit_of_isTerminal _ (by
          dsimp [skyscraperPresheaf]
          rw [if_neg]
          · exact terminalIsTerminal
          · exact Set.not_mem_empty PUnit.unit)))
#align skyscraper_presheaf_is_sheaf skyscraperPresheaf_isSheaf

/--
The skyscraper presheaf supported at `p₀` with value `A` is the sheaf that assigns `A` to all opens
`U` that contain `p₀` and assigns `*` otherwise.
-/
def skyscraperSheaf : Sheaf C X :=
  ⟨skyscraperPresheaf p₀ A, skyscraperPresheaf_isSheaf _ _⟩
#align skyscraper_sheaf skyscraperSheaf

/-- Taking skyscraper sheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
def skyscraperSheafFunctor : C ⥤ Sheaf C X where
  obj c := skyscraperSheaf p₀ c
  map f := Sheaf.Hom.mk <| (skyscraperPresheafFunctor p₀).map f
  map_id _ := Sheaf.Hom.ext _ _ <| (skyscraperPresheafFunctor p₀).map_id _
  map_comp _ _ := Sheaf.Hom.ext _ _ <| (skyscraperPresheafFunctor p₀).map_comp _ _
#align skyscraper_sheaf_functor skyscraperSheafFunctor

namespace StalkSkyscraperPresheafAdjunctionAuxs

variable [HasColimits C]

/-- If `f : 𝓕.stalk p₀ ⟶ c`, then a natural transformation `𝓕 ⟶ skyscraper_presheaf p₀ c` can be
defined by: `𝓕.germ p₀ ≫ f : 𝓕(U) ⟶ c` if `p₀ ∈ U` and the unique morphism to a terminal object
if `p₀ ∉ U`.
-/
@[simps]
def toSkyscraperPresheaf {𝓕 : Presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c) :
    𝓕 ⟶ skyscraperPresheaf p₀ c where
  app U :=
    if h : p₀ ∈ U.unop then 𝓕.germ ⟨p₀, h⟩ ≫ f ≫ eqToHom (if_pos h).symm
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  naturality U V inc := by
    -- Porting note : don't know why original proof fell short of working, add `aesop_cat` finished
    -- the proofs anyway
    dsimp; by_cases hV : p₀ ∈ V.unop
    -- ⊢ (𝓕.map inc ≫ if h : p₀ ∈ V.unop then Presheaf.germ 𝓕 { val := p₀, property : …
           -- ⊢ (𝓕.map inc ≫ if h : p₀ ∈ V.unop then Presheaf.germ 𝓕 { val := p₀, property : …
    · have hU : p₀ ∈ U.unop := leOfHom inc.unop hV; split_ifs
      -- ⊢ (𝓕.map inc ≫ if h : p₀ ∈ V.unop then Presheaf.germ 𝓕 { val := p₀, property : …
                                                    -- ⊢ 𝓕.map inc ≫ Presheaf.germ 𝓕 { val := p₀, property := h✝ } ≫ f ≫ eqToHom (_ : …
      erw [← Category.assoc, 𝓕.germ_res inc.unop, Category.assoc, Category.assoc, eqToHom_trans]
      -- ⊢ 𝓕.map inc ≫ Presheaf.germ 𝓕 { val := p₀, property := hV } ≫ f ≫ eqToHom (_ : …
      aesop_cat
      -- 🎉 no goals
    · split_ifs; apply ((if_neg hV).symm.ndrec terminalIsTerminal).hom_ext; aesop_cat
      -- ⊢ 𝓕.map inc ≫ Presheaf.germ 𝓕 { val := p₀, property := h✝ } ≫ f ≫ eqToHom (_ : …
                 -- ⊢ 𝓕.map inc ≫ IsTerminal.from ((_ : (⊤_ C) = if p₀ ∈ V.unop then c else ⊤_ C)  …
                                                                            -- 🎉 no goals
#align stalk_skyscraper_presheaf_adjunction_auxs.to_skyscraper_presheaf StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf

/-- If `f : 𝓕 ⟶ skyscraper_presheaf p₀ c` is a natural transformation, then there is a morphism
`𝓕.stalk p₀ ⟶ c` defined as the morphism from colimit to cocone at `c`.
-/
def fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) : 𝓕.stalk p₀ ⟶ c :=
  let χ : Cocone ((OpenNhds.inclusion p₀).op ⋙ 𝓕) :=
    Cocone.mk c <|
      { app := fun U => f.app (op U.unop.1) ≫ eqToHom (if_pos U.unop.2)
        naturality := fun U V inc => by
          dsimp
          -- ⊢ 𝓕.map ((OpenNhds.inclusion p₀).map inc.unop).op ≫ NatTrans.app f (op V.unop. …
          erw [Category.comp_id, ← Category.assoc, comp_eqToHom_iff, Category.assoc,
            eqToHom_trans, f.naturality, skyscraperPresheaf_map]
          -- Porting note : added this `dsimp` and `rfl` in the end
          dsimp only [skyscraperPresheaf_obj, unop_op, Eq.ndrec]
          -- ⊢ (NatTrans.app f (op ((OpenNhds.inclusion p₀).obj U.unop)) ≫ if h : p₀ ∈ (Ope …
          have hV : p₀ ∈ (OpenNhds.inclusion p₀).obj V.unop := V.unop.2; split_ifs <;>
          -- ⊢ (NatTrans.app f (op ((OpenNhds.inclusion p₀).obj U.unop)) ≫ if h : p₀ ∈ (Ope …
                                                                         -- ⊢ NatTrans.app f (op ((OpenNhds.inclusion p₀).obj U.unop)) ≫ eqToHom (_ : (fun …
          simp only [comp_eqToHom_iff, Category.assoc, eqToHom_trans, eqToHom_refl,
            Category.comp_id] <;> rfl }
                                  -- 🎉 no goals
                                  -- 🎉 no goals
  colimit.desc _ χ
#align stalk_skyscraper_presheaf_adjunction_auxs.from_stalk StalkSkyscraperPresheafAdjunctionAuxs.fromStalk

theorem to_skyscraper_fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) :
    toSkyscraperPresheaf p₀ (fromStalk _ f) = f :=
  NatTrans.ext _ _ <|
    funext fun U =>
      (em (p₀ ∈ U.unop)).elim
        (fun h => by
          dsimp; split_ifs;
          -- ⊢ (if h : p₀ ∈ U.unop then Presheaf.germ 𝓕 { val := p₀, property := h } ≫ from …
                 -- ⊢ Presheaf.germ 𝓕 { val := p₀, property := h } ≫ fromStalk p₀ f ≫ eqToHom (_ : …
          erw [← Category.assoc, colimit.ι_desc, Category.assoc, eqToHom_trans, eqToHom_refl,
            Category.comp_id]
          rfl)
          -- 🎉 no goals
        fun h => by dsimp; split_ifs; apply ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext
                    -- ⊢ (if h : p₀ ∈ U.unop then Presheaf.germ 𝓕 { val := p₀, property := h } ≫ from …
                           -- ⊢ IsTerminal.from ((_ : (⊤_ C) = if p₀ ∈ U.unop then c else ⊤_ C) ▸ terminalIs …
                                      -- 🎉 no goals
#align stalk_skyscraper_presheaf_adjunction_auxs.to_skyscraper_from_stalk StalkSkyscraperPresheafAdjunctionAuxs.to_skyscraper_fromStalk

theorem fromStalk_to_skyscraper {𝓕 : Presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c) :
    fromStalk p₀ (toSkyscraperPresheaf _ f) = f :=
  colimit.hom_ext fun U => by
    erw [colimit.ι_desc]; dsimp; rw [dif_pos U.unop.2];
    -- ⊢ NatTrans.app { pt := c, ι := NatTrans.mk fun U => NatTrans.app (toSkyscraper …
                          -- ⊢ (if h : p₀ ∈ U.unop.obj then Presheaf.germ 𝓕 { val := p₀, property := h } ≫  …
                                 -- ⊢ (Presheaf.germ 𝓕 { val := p₀, property := (_ : p₀ ∈ U.unop.obj) } ≫ f ≫ eqTo …
    rw [Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
      Presheaf.germ]
    congr 3
    -- 🎉 no goals
#align stalk_skyscraper_presheaf_adjunction_auxs.from_stalk_to_skyscraper StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper

/-- The unit in `presheaf.stalk ⊣ skyscraper_presheaf_functor`
-/
@[simps]
protected def unit : 𝟭 (Presheaf C X) ⟶ Presheaf.stalkFunctor C p₀ ⋙ skyscraperPresheafFunctor p₀
    where
  app 𝓕 := toSkyscraperPresheaf _ <| 𝟙 _
  naturality 𝓕 𝓖 f := by
    ext U; dsimp
    -- ⊢ NatTrans.app ((𝟭 (Presheaf C X)).map f ≫ (fun 𝓕 => toSkyscraperPresheaf p₀ ( …
           -- ⊢ NatTrans.app (f ≫ toSkyscraperPresheaf p₀ (𝟙 (Presheaf.stalk 𝓖 p₀))) (op U)  …
    -- Porting note : added the following `rw` and `dsimp` to make it compile
    rw [NatTrans.comp_app, toSkyscraperPresheaf_app, NatTrans.comp_app, toSkyscraperPresheaf_app]
    -- ⊢ (NatTrans.app f (op U) ≫ if h : p₀ ∈ (op U).unop then Presheaf.germ 𝓖 { val  …
    dsimp only [skyscraperPresheaf_obj, unop_op, Eq.ndrec, SkyscraperPresheafFunctor.map'_app]
    -- ⊢ (NatTrans.app f (op U) ≫ if h : p₀ ∈ U then Presheaf.germ 𝓖 { val := p₀, pro …
    split_ifs with h
    -- ⊢ NatTrans.app f (op U) ≫ Presheaf.germ 𝓖 { val := p₀, property := h } ≫ 𝟙 (Pr …
    · simp only [Category.id_comp, ← Category.assoc]; rw [comp_eqToHom_iff]
      -- ⊢ (NatTrans.app f (op U) ≫ Presheaf.germ 𝓖 { val := p₀, property := h }) ≫ eqT …
                                                      -- ⊢ NatTrans.app f (op U) ≫ Presheaf.germ 𝓖 { val := p₀, property := h } = ((((P …
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      -- ⊢ NatTrans.app f (op U) ≫ Presheaf.germ 𝓖 { val := p₀, property := h } = Presh …
      erw [colimit.ι_map]; rfl
      -- ⊢ NatTrans.app f (op U) ≫ Presheaf.germ 𝓖 { val := p₀, property := h } = NatTr …
                           -- 🎉 no goals
    · apply ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext
      -- 🎉 no goals
#align stalk_skyscraper_presheaf_adjunction_auxs.unit StalkSkyscraperPresheafAdjunctionAuxs.unit

/-- The counit in `presheaf.stalk ⊣ skyscraper_presheaf_functor`
-/
@[simps]
protected def counit :
    skyscraperPresheafFunctor p₀ ⋙ (Presheaf.stalkFunctor C p₀ : Presheaf C X ⥤ C) ⟶ 𝟭 C where
  app c := (skyscraperPresheafStalkOfSpecializes p₀ c specializes_rfl).hom
  naturality x y f := colimit.hom_ext fun U => by
    erw [← Category.assoc, colimit.ι_map, colimit.isoColimitCocone_ι_hom_assoc,
      skyscraperPresheafCoconeOfSpecializes_ι_app (h := specializes_rfl), Category.assoc,
      colimit.ι_desc, whiskeringLeft_obj_map, whiskerLeft_app, SkyscraperPresheafFunctor.map'_app,
      dif_pos U.unop.2, skyscraperPresheafCoconeOfSpecializes_ι_app (h := specializes_rfl),
      comp_eqToHom_iff, Category.assoc, eqToHom_comp_iff, ← Category.assoc, eqToHom_trans,
      eqToHom_refl, Category.id_comp, comp_eqToHom_iff, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id, CategoryTheory.Functor.id_map]
#align stalk_skyscraper_presheaf_adjunction_auxs.counit StalkSkyscraperPresheafAdjunctionAuxs.counit

end StalkSkyscraperPresheafAdjunctionAuxs

section

open StalkSkyscraperPresheafAdjunctionAuxs

/-- `skyscraper_presheaf_functor` is the right adjoint of `presheaf.stalk_functor`
-/
def skyscraperPresheafStalkAdjunction [HasColimits C] :
    (Presheaf.stalkFunctor C p₀ : Presheaf C X ⥤ C) ⊣ skyscraperPresheafFunctor p₀ where
  homEquiv c 𝓕 :=
    { toFun := toSkyscraperPresheaf _
      invFun := fromStalk _
      left_inv := fromStalk_to_skyscraper _
      right_inv := to_skyscraper_fromStalk _ }
  unit := StalkSkyscraperPresheafAdjunctionAuxs.unit _
  counit := StalkSkyscraperPresheafAdjunctionAuxs.counit _
  homEquiv_unit {𝓕} c α := by
    ext U;
    -- ⊢ NatTrans.app (↑((fun c 𝓕 => { toFun := toSkyscraperPresheaf p₀, invFun := fr …
    -- Porting note : `NatTrans.comp_app` is not picked up by `simp`
    rw [NatTrans.comp_app]
    -- ⊢ NatTrans.app (↑((fun c 𝓕 => { toFun := toSkyscraperPresheaf p₀, invFun := fr …
    simp only [Equiv.coe_fn_mk, toSkyscraperPresheaf_app, SkyscraperPresheafFunctor.map'_app,
      skyscraperPresheafFunctor_map, unit_app]
    split_ifs with h
    -- ⊢ Presheaf.germ 𝓕 { val := p₀, property := (_ : p₀ ∈ (op U).unop) } ≫ α ≫ eqTo …
    · erw [Category.id_comp, ← Category.assoc, comp_eqToHom_iff, Category.assoc, Category.assoc,
        Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, ←
        Category.assoc _ _ α, eqToHom_trans, eqToHom_refl, Category.id_comp]
    · apply ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext
      -- 🎉 no goals
  homEquiv_counit {𝓕} c α := by
    -- Porting note : added a `dsimp`
    dsimp; ext U; simp only [Equiv.coe_fn_symm_mk, counit_app]
    -- ⊢ fromStalk p₀ α = (Presheaf.stalkFunctor C p₀).map α ≫ (skyscraperPresheafSta …
           -- ⊢ Presheaf.germ 𝓕 { val := p₀, property := hxU✝ } ≫ fromStalk p₀ α = Presheaf. …
                  -- ⊢ Presheaf.germ 𝓕 { val := p₀, property := hxU✝ } ≫ fromStalk p₀ α = Presheaf. …
    erw [colimit.ι_desc, ← Category.assoc, colimit.ι_map, whiskerLeft_app, Category.assoc,
      colimit.ι_desc]
    rfl
    -- 🎉 no goals
#align skyscraper_presheaf_stalk_adjunction skyscraperPresheafStalkAdjunction

instance [HasColimits C] : IsRightAdjoint (skyscraperPresheafFunctor p₀ : C ⥤ Presheaf C X) :=
  ⟨_, skyscraperPresheafStalkAdjunction _⟩

instance [HasColimits C] : IsLeftAdjoint (Presheaf.stalkFunctor C p₀) :=
  ⟨_, skyscraperPresheafStalkAdjunction _⟩

/-- Taking stalks of a sheaf is the left adjoint functor to `skyscraper_sheaf_functor`
-/
def stalkSkyscraperSheafAdjunction [HasColimits C] :
    Sheaf.forget C X ⋙ Presheaf.stalkFunctor _ p₀ ⊣ skyscraperSheafFunctor p₀ where
  -- Porting note : `ext1` is changed to `Sheaf.Hom.ext`,
  -- see https://github.com/leanprover-community/mathlib4/issues/5229
  homEquiv 𝓕 c :=
    ⟨fun f => ⟨toSkyscraperPresheaf p₀ f⟩, fun g => fromStalk p₀ g.1, fromStalk_to_skyscraper p₀,
      fun g => Sheaf.Hom.ext _ _ <| to_skyscraper_fromStalk _ _⟩
  unit :=
    { app := fun 𝓕 => ⟨(StalkSkyscraperPresheafAdjunctionAuxs.unit p₀).app 𝓕.1⟩
      naturality := fun 𝓐 𝓑 f => Sheaf.Hom.ext _ _ <| by
        apply (StalkSkyscraperPresheafAdjunctionAuxs.unit p₀).naturality }
        -- 🎉 no goals
  counit := StalkSkyscraperPresheafAdjunctionAuxs.counit p₀
  homEquiv_unit {𝓐} c f := Sheaf.Hom.ext _ _ (skyscraperPresheafStalkAdjunction p₀).homEquiv_unit
  homEquiv_counit {𝓐} c f := (skyscraperPresheafStalkAdjunction p₀).homEquiv_counit
#align stalk_skyscraper_sheaf_adjunction stalkSkyscraperSheafAdjunction

instance [HasColimits C] : IsRightAdjoint (skyscraperSheafFunctor p₀ : C ⥤ Sheaf C X) :=
  ⟨_, stalkSkyscraperSheafAdjunction _⟩

end

end
