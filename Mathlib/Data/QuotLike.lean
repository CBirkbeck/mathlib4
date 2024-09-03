/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Logic.Relator
import Mathlib.Logic.Unique
import Mathlib.Util.Notation3
import Qq.MetaM

/-!
# Typeclass for quotient types
-/

universe u ua ub uc v

theorem Quot.exact {α r} [IsEquiv α r] {a b : α} : Quot.mk r a = Quot.mk r b → r a b :=
  Quotient.exact (s := ⟨r, refl, symm, _root_.trans⟩)

namespace QuotLike

set_option linter.dupNamespace false in
/-- [TODO] -/
class QuotLike (Q : Sort u) (α : outParam (Sort u)) (r : outParam (α → α → Prop)) where
  /-- The canonical quotient map. -/
  mkQ : α → Q := by exact Quot.mk _
  /-- The canonical map from quotient to `Quot r`. -/
  toQuot : Q → Quot r := by exact (·)
  /-- [TODO] -/
  toQuot_mkQ : ∀ a, toQuot (mkQ a) = Quot.mk r a := by exact fun _ ↦ rfl
  /-- The analogue of `Quot.ind`: every element of `Q` is of the form `mkQ a` -/
  ind {motive : Q → Prop} : (∀ a : α, motive (mkQ a)) → ∀ q : Q, motive q := by exact Quot.ind
  /--
  The analogue of `Quot.sound`: If `a` and `b` are related by the equivalence relation,
  then they have equal equivalence classes.
  -/
  sound {a b : α} : r a b → mkQ a = mkQ b := by exact Quot.sound

export QuotLike (mkQ toQuot toQuot_mkQ ind sound)

attribute [elab_as_elim] ind

@[inherit_doc mkQ]
notation3:arg "⟦" a "⟧" => mkQ a

open Lean Elab Term Meta Qq

/-- [TODO] -/
class HasQuot (α : Sort u) (Q : outParam (Sort u)) (r : outParam (α → α → Prop))
    [QuotLike Q α r] where

/-- [TODO] -/
elab:arg "⟦" t:term "⟧'" : term => do
  let t ← withSynthesize do elabTerm t none
  synthesizeSyntheticMVars
  let t ← instantiateMVars t
  let α ← inferType t
  let u ← match ← inferType α with | .sort u => pure u | _ => mkFreshLevelMVar
  have α : Q(Sort u) := α
  have t : Q($α) := t
  let Q ← mkFreshExprMVarQ q(Sort u)
  let r ← mkFreshExprMVarQ q($α → $α → Prop)
  let inst ← mkFreshExprMVarQ q(QuotLike $Q $α $r)
  let .some _ ← trySynthInstanceQ q(@HasQuot $α $Q $r $inst) |
    throwError "Cannot find `HasQuot` instance for type `{α}`."
  pure q(@mkQ $Q $α $r $inst $t)

/-- [TODO] -/
macro:arg "⟦" t:term " : " α:term "⟧'" : term => `(⟦($t : $α)⟧')

/-- [TODO] -/
class HasQuotHint (α : Sort u) (Hint : Sort v) (hint : Hint)
    (Q : outParam (Sort u)) (r : outParam (α → α → Prop)) [QuotLike Q α r] where

/-- [TODO] -/
elab:arg "⟦" t:term "⟧_" noWs h:term:max : term => do
  let t ← withSynthesize do elabTerm t none
  let h ← withSynthesize do elabTerm h none
  synthesizeSyntheticMVars
  let t ← instantiateMVars t
  let α ← inferType t
  let h ← instantiateMVars h
  let H ← inferType h
  let u ← match ← inferType α with | .sort u => pure u | _ => mkFreshLevelMVar
  let v ← match ← inferType H with | .sort v => pure v | _ => mkFreshLevelMVar
  have α : Q(Sort u) := α
  have t : Q($α) := t
  have H : Q(Sort v) := H
  have h : Q($H) := h
  let Q ← mkFreshExprMVarQ q(Sort u)
  let r ← mkFreshExprMVarQ q($α → $α → Prop)
  let inst ← mkFreshExprMVarQ q(QuotLike $Q $α $r)
  let .some _ ← trySynthInstanceQ q(@HasQuotHint $α $H $h $Q $r $inst) |
    throwError "Cannot find `HasQuotHint` instance for type `{α}` and hint `{h}`."
  pure q(@mkQ $Q $α $r $inst $t)

/-- [TODO] -/
macro:arg "⟦" t:term " : " α:term "⟧_" noWs h:term:max : term => `(⟦($t : $α)⟧_$h)

end QuotLike

export QuotLike (QuotLike mkQ)

namespace Quot

instance instQuotLike {α} (r : α → α → Prop) : QuotLike (Quot r) α r where

scoped instance instHasQuotHint {α} (r : α → α → Prop) :
    QuotLike.HasQuotHint α (α → α → Prop) r (Quot r) r where

end Quot

namespace Quotient

instance instQuotLike {α} (s : Setoid α) : QuotLike (Quotient s) α (· ≈ ·) where
  mkQ := Quotient.mk _

scoped instance instHasQuot {α} [s : Setoid α] : QuotLike.HasQuot α (Quotient s) (· ≈ ·) where

end Quotient

namespace QuotLike

section

variable {Q : Sort u} {α : Sort u} {r : α → α → Prop} [QuotLike Q α r]

/--
The analogue of `Quot.lift`: if `f : α → β` respects the equivalence relation `r`,
then it lifts to a function on `Q` such that `lift f h ⟦a⟧ = f a`.
-/
protected def lift {β : Sort v} (f : α → β) (h : ∀ (a b : α), r a b → f a = f b) : Q → β :=
  fun q ↦ Quot.lift f h (toQuot q)

/--
The analogue of `Quot.liftOn`: if `f : α → β` respects the equivalence relation `r`,
then it lifts to a function on `Q` such that `liftOn ⟦a⟧ f h = f a`.
-/
protected abbrev liftOn {β : Sort v} (q : Q) (f : α → β) (c : (a b : α) → r a b → f a = f b) : β :=
  QuotLike.lift f c q

@[simp]
theorem lift_mkQ {β : Sort v} (f : α → β) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) (a : α) :
    QuotLike.lift f h (⟦a⟧ : Q) = f a := by
  rw [QuotLike.lift, toQuot_mkQ]

theorem liftOn_mkQ {β : Sort v} (a : α) (f : α → β) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) :
    QuotLike.liftOn (⟦a⟧ : Q) f h = f a :=
  lift_mkQ f h a

@[elab_as_elim]
protected theorem inductionOn {motive : Q → Prop}
    (q : Q) (h : (a : α) → motive ⟦a⟧) : motive q :=
  ind h q

theorem exists_rep (q : Q) : ∃ a, ⟦a⟧ = q :=
  QuotLike.inductionOn q (fun a ↦ ⟨a, rfl⟩)

section
variable {motive : Q → Sort v} (f : (a : α) → motive ⟦a⟧)

/-- Auxiliary definition for `Quot.rec`. -/
@[reducible, macro_inline]
protected def indep (a : α) : PSigma motive :=
  ⟨⟦a⟧, f a⟩

protected theorem indepCoherent
    (h : (a b : α) → (p : r a b) → Eq.ndrec (f a) (sound p) = f b) :
    (a b : α) → r a b → QuotLike.indep f a = QuotLike.indep f b :=
  fun a b e ↦ PSigma.eta (sound e) (h a b e)

protected theorem liftIndepPr1
    (h : ∀ (a b : α) (p : r a b), Eq.ndrec (f a) (sound p) = f b) (q : Q) :
    (QuotLike.lift (QuotLike.indep f) (QuotLike.indepCoherent f h) q).1 = q := by
  induction q using QuotLike.ind
  rw [lift_mkQ]

end

/-- The analogue of `Quot.rec` for `QuotLike`. See `Quot.rec`. -/
@[inline, elab_as_elim]
protected def rec {motive : Q → Sort v}
    (f : (a : α) → motive ⟦a⟧)
    (h : (a b : α) → (p : r a b) → Eq.ndrec (f a) (sound p) = f b)
    (q : Q) :
    motive q :=
  Eq.ndrecOn (QuotLike.liftIndepPr1 f h q)
    ((QuotLike.lift (QuotLike.indep f) (QuotLike.indepCoherent f h) q).2)

@[simp]
theorem rec_mkQ {motive : Q → Sort v}
    (f : (a : α) → motive ⟦a⟧)
    (h : (a b : α) → (p : r a b) → Eq.ndrec (f a) (sound p) = f b)
    (a : α) :
    _root_.QuotLike.rec f h ⟦a⟧ = f a := by
  rw [_root_.QuotLike.rec, ← heq_iff_eq, eqRec_heq_iff_heq, lift_mkQ]

/-- The analogue of `Quot.recOn` for `QuotLike`. See `Quot.recOn`. -/
@[elab_as_elim]
protected abbrev recOn {motive : Q → Sort v}
    (q : Q)
    (f : (a : α) → motive ⟦a⟧)
    (h : (a b : α) → (p : r a b) → Eq.ndrec (f a) (sound p) = f b) :
    motive q :=
  _root_.QuotLike.rec f h q

/-- The analogue of `Quot.recOnSubsingleton` for `QuotLike`. See `Quot.recOnSubsingleton`. -/
@[elab_as_elim]
protected abbrev recOnSubsingleton {motive : Q → Sort v}
    [_h : ∀ a, Subsingleton (motive ⟦a⟧)]
    (q : Q)
    (f : (a : α) → motive ⟦a⟧) :
    motive q :=
  _root_.QuotLike.recOn q f (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- The analogue of `Quot.hrecOn` for `QuotLike`. See `Quot.hrecOn`. -/
@[elab_as_elim]
protected abbrev hrecOn {motive : Q → Sort v}
    (q : Q)
    (f : (a : α) → motive ⟦a⟧)
    (h : (a b : α) → r a b → HEq (f a) (f b)) :
    motive q :=
  _root_.QuotLike.recOn q f fun a b p ↦ eq_of_heq <| (eqRec_heq_self _ _).trans (h a b p)

theorem hrecOn_mkQ {motive : Q → Sort v}
    (a : α)
    (f : (a : α) → motive ⟦a⟧)
    (h : (a b : α) → r a b → HEq (f a) (f b)) :
    QuotLike.hrecOn ⟦a⟧ f h = f a := by
  simp

end

section

variable {Qa α : Sort ua} {ra : α → α → Prop} [QuotLike Qa α ra]
variable {Qb β : Sort ub} {rb : β → β → Prop} [QuotLike Qb β rb]
variable {Qc γ : Sort uc} {rc : γ → γ → Prop} [QuotLike Qc γ rc]
variable {φ : Sort v}

/-- Map a function `f : α → β` that sends equivalent elements to equivalent elements to a
function `f : Qa → Qb`. -/
protected def map (f : α → β) (h : (ra ⇒ rb) f f) : Qa → Qb :=
  (QuotLike.lift fun x ↦ ⟦f x⟧) fun _ _ ↦ (QuotLike.sound <| h ·)

@[simp]
theorem map_mkQ (f : α → β) (h : (ra ⇒ rb) f f) (a : α) :
    QuotLike.map f h (⟦a⟧ : Qa) = (⟦f a⟧ : Qb) :=
  lift_mkQ _ _ _

/-- Lift a binary function to a quotient on both arguments. -/
protected def lift₂'
    (f : α → β → φ)
    (ha : ∀ a₁ a₂ b, ra a₁ a₂ → f a₁ b = f a₂ b)
    (hb : ∀ a b₁ b₂, rb b₁ b₂ → f a b₁ = f a b₂) :
    Qa → Qb → φ :=
  QuotLike.lift (fun a ↦ QuotLike.lift (f a) (hb a))
    (fun a₁ a₂ h ↦ funext (QuotLike.ind (fun b ↦ by simpa [lift_mkQ] using ha a₁ a₂ b h)))

@[simp]
lemma lift₂'_mkQ
    (f : α → β → φ)
    (ha : ∀ a₁ a₂ b, ra a₁ a₂ → f a₁ b = f a₂ b)
    (hb : ∀ a b₁ b₂, rb b₁ b₂ → f a b₁ = f a b₂)
    (a : α) (b : β) :
    QuotLike.lift₂' f ha hb (⟦a⟧ : Qa) (⟦b⟧ : Qb) = f a b := by
  simp [QuotLike.lift₂']

/-- Lift a binary function to a quotient on both arguments. -/
protected abbrev liftOn₂'
    (qa : Qa) (qb : Qb)
    (f : α → β → φ)
    (ha : ∀ a₁ a₂ b, ra a₁ a₂ → f a₁ b = f a₂ b)
    (hb : ∀ a b₁ b₂, rb b₁ b₂ → f a b₁ = f a b₂) : φ :=
  QuotLike.lift₂' f ha hb qa qb

lemma liftOn₂'_mkQ
    (a : α) (b : β)
    (f : α → β → φ)
    (ha : ∀ a₁ a₂ b, ra a₁ a₂ → f a₁ b = f a₂ b)
    (hb : ∀ a b₁ b₂, rb b₁ b₂ → f a b₁ = f a b₂) :
    QuotLike.liftOn₂' (⟦a⟧ : Qa) (⟦b⟧ : Qb) f ha hb = f a b := by
  simp

/-- Lift a binary function to a quotient on both arguments. -/
protected abbrev lift₂ [IsRefl α ra] [IsRefl β rb]
    (f : α → β → φ)
    (h : ∀ a₁ a₂ b₁ b₂, ra a₁ a₂ → rb b₁ b₂ → f a₁ b₁ = f a₂ b₂) :
    Qa → Qb → φ :=
  QuotLike.lift₂' f (h · · · _ · (refl _)) (h · _ · · (refl _) ·)

lemma lift₂_mkQ [IsRefl α ra] [IsRefl β rb]
    (f : α → β → φ)
    (h : ∀ a₁ a₂ b₁ b₂, ra a₁ a₂ → rb b₁ b₂ → f a₁ b₁ = f a₂ b₂)
    (a : α) (b : β) :
    QuotLike.lift₂ f h (⟦a⟧ : Qa) (⟦b⟧ : Qb) = f a b := by
  simp

/-- Lift a binary function to a quotient on both arguments. -/
protected abbrev liftOn₂ [IsRefl α ra] [IsRefl β rb]
    (qa : Qa) (qb : Qb)
    (f : α → β → φ)
    (h : ∀ a₁ a₂ b₁ b₂, ra a₁ a₂ → rb b₁ b₂ → f a₁ b₁ = f a₂ b₂) : φ :=
  QuotLike.lift₂ f h qa qb

lemma liftOn₂_mkQ [IsRefl α ra] [IsRefl β rb]
    (a : α) (b : β)
    (f : α → β → φ)
    (h : ∀ a₁ a₂ b₁ b₂, ra a₁ a₂ → rb b₁ b₂ → f a₁ b₁ = f a₂ b₂) :
    QuotLike.liftOn₂ (⟦a⟧ : Qa) (⟦b⟧ : Qb) f h = f a b := by
  simp

/-- Map a function `f : α → β → γ` that sends equivalent elements to equivalent elements to a
function `f : Qa → Qb → Qc`. -/
protected def map₂ [IsRefl α ra] [IsRefl β rb] (f : α → β → γ)
    (h : (ra ⇒ rb ⇒ rc) f f) : Qa → Qb → Qc :=
  (QuotLike.lift₂ fun x y ↦ ⟦f x y⟧) fun _ _ _ _ ↦ (QuotLike.sound <| h · ·)

@[simp]
theorem map₂_mkQ [IsRefl α ra] [IsRefl β rb] (f : α → β → γ) (h : (ra ⇒ rb ⇒ rc) f f)
    (a : α) (b : β) :
    QuotLike.map₂ f h (⟦a⟧ : Qa) (⟦b⟧ : Qb) = (⟦f a b⟧ : Qc) := by
  simp [QuotLike.map₂]

@[elab_as_elim]
protected theorem ind₂ {motive : Qa → Qb → Prop}
    (h : (a : α) → (b : β) → motive ⟦a⟧ ⟦b⟧)
    (qa : Qa) (qb : Qb) :
    motive qa qb :=
  QuotLike.ind (QuotLike.ind h qa) qb

@[elab_as_elim]
protected theorem inductionOn₂ {motive : Qa → Qb → Prop}
    (qa : Qa) (qb : Qb)
    (h : (a : α) → (b : β) → motive ⟦a⟧ ⟦b⟧) :
    motive qa qb :=
  QuotLike.ind₂ h qa qb

/-- A binary version of `Quot.recOnSubsingleton`. -/
@[elab_as_elim]
protected def recOnSubsingleton₂ {motive : Qa → Qb → Sort*}
    [_h : ∀ a b, Subsingleton (motive ⟦a⟧ ⟦b⟧)]
    (qa : Qa) (qb : Qb) (f : ∀ a b, motive ⟦a⟧ ⟦b⟧) :
    motive qa qb :=
  QuotLike.recOnSubsingleton (_h := fun _ ↦ QuotLike.ind inferInstance qb) qa
    fun a ↦ QuotLike.recOnSubsingleton qb fun b ↦ f a b

/-- Recursion on two `QuotLike` arguments `qa` and `qb`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
@[elab_as_elim]
protected def hrecOn₂ [IsRefl α ra] [IsRefl β rb] {motive : Qa → Qb → Sort*}
    (qa : Qa) (qb : Qb) (f : ∀ a b, motive ⟦a⟧ ⟦b⟧)
    (h : ∀ a₁ a₂ b₁ b₂, ra a₁ a₂ → rb b₁ b₂ → HEq (f a₁ b₁) (f a₂ b₂)) :
    motive qa qb :=
  QuotLike.hrecOn qa
    (fun a ↦ QuotLike.hrecOn qb (f a) (fun b₁ b₂ pb ↦ h _ _ _ _ (refl _) pb))
    fun a₁ a₂ pa ↦ by exact QuotLike.inductionOn qb fun b ↦ by simp [h, pa, refl]

@[simp]
theorem hrecOn₂_mkQ [IsRefl α ra] [IsRefl β rb] {motive : Qa → Qb → Sort*}
    (a : α) (b : β) (f : ∀ a b, motive ⟦a⟧ ⟦b⟧)
    (h : ∀ a₁ a₂ b₁ b₂, ra a₁ a₂ → rb b₁ b₂ → HEq (f a₁ b₁) (f a₂ b₂)) :
    QuotLike.hrecOn₂ ⟦a⟧ ⟦b⟧ f h = f a b := by
  simp [QuotLike.hrecOn₂]

@[elab_as_elim]
protected theorem ind₃ {motive : Qa → Qb → Qc → Prop}
    (h : (a : α) → (b : β) → (c : γ) → motive ⟦a⟧ ⟦b⟧ ⟦c⟧)
    (qa : Qa) (qb : Qb) (qc : Qc) :
    motive qa qb qc :=
  QuotLike.ind (QuotLike.ind₂ h qa qb) qc

@[elab_as_elim]
protected theorem inductionOn₃ {motive : Qa → Qb → Qc → Prop}
    (qa : Qa) (qb : Qb) (qc : Qc)
    (h : (a : α) → (b : β) → (c : γ) → motive ⟦a⟧ ⟦b⟧ ⟦c⟧) :
    motive qa qb qc :=
  QuotLike.ind₃ h qa qb qc

end

section

variable {Q α : Sort u} {r : α → α → Prop} [QuotLike Q α r]

/-- Makes a quotient from `Quot r`. -/
def ofQuot : Quot r → Q :=
  Quot.lift mkQ fun _ _ ↦ sound

@[simp]
theorem ofQuot_toQuot (q : Q) : ofQuot (toQuot q) = q :=
  ind (fun a ↦ by rw [toQuot_mkQ, ofQuot]) q

theorem toQuot_injective : Function.Injective (toQuot (Q := Q)) :=
  Function.LeftInverse.injective ofQuot_toQuot

theorem eq_iff_quotMk {a b : α} : (⟦a⟧ : Q) = ⟦b⟧ ↔ Quot.mk r a = Quot.mk r b := by
  rw [← toQuot_mkQ (Q := Q), ← toQuot_mkQ (Q := Q), toQuot_injective.eq_iff]

theorem exact [IsEquiv α r] {a b : α} : (⟦a⟧ : Q) = ⟦b⟧ → r a b :=
  fun h ↦ Quot.exact (eq_iff_quotMk.mp h)

@[simp]
theorem eq [IsEquiv α r] {a b : α} : (⟦a⟧ : Q) = ⟦b⟧ ↔ r a b :=
  ⟨exact, sound⟩

alias mkQ_eq_mkQ := eq

protected theorem «forall» {p : Q → Prop} : (∀ q, p q) ↔ ∀ a, p ⟦a⟧ :=
  ⟨fun h _ ↦ h _, QuotLike.ind⟩

protected theorem «exists» {p : Q → Prop} : (∃ q, p q) ↔ ∃ a, p ⟦a⟧ :=
  ⟨fun ⟨q, hq⟩ ↦ QuotLike.ind .intro q hq, fun ⟨a, ha⟩ ↦ ⟨⟦a⟧, ha⟩⟩

instance (priority := 800) [Inhabited α] : Inhabited Q :=
  ⟨⟦default⟧⟩

instance (priority := 800) [Subsingleton α] : Subsingleton Q where
  allEq := QuotLike.ind₂ fun x y ↦ congrArg mkQ (Subsingleton.elim x y)

instance (priority := 800) [Unique α] : Unique Q := Unique.mk' _

instance (priority := 800) [IsEquiv α r] [dec : DecidableRel r] : DecidableEq Q :=
  fun q₁ q₂ ↦ QuotLike.recOnSubsingleton₂ q₁ q₂ fun a₁ a₂ ↦
    match dec a₁ a₂ with
    | isTrue  h₁ => isTrue (QuotLike.sound h₁)
    | isFalse h₂ => isFalse (fun h ↦ absurd (QuotLike.exact h) h₂)

@[simp]
theorem surjective_lift {β : Sort v} {f : α → β} {h : ∀ a b, r a b → f a = f b} :
    Function.Surjective (QuotLike.lift f h : Q → β) ↔ Function.Surjective f :=
  ⟨fun hf => by simpa only [lift_mkQ, · ∘ ·] using hf.comp QuotLike.exists_rep,
    fun hf y => let ⟨x, hx⟩ := hf y; ⟨mkQ x, by simpa only [lift_mkQ] using hx⟩⟩

@[simp]
lemma surjective_liftOn {β : Sort v} {f : α → β} {h : ∀ a b, r a b → f a = f b} :
    Function.Surjective (fun x : Q ↦ QuotLike.liftOn x f h) ↔ Function.Surjective f :=
  surjective_lift

@[simp]
theorem lift_comp_mkQ {β : Sort v} {f : α → β} (h : ∀ a b, r a b → f a = f b) :
    (QuotLike.lift f h : Q → β) ∘ mkQ = f :=
  funext <| QuotLike.lift_mkQ f h

instance (priority := 800) (f : α → Prop) [hf : DecidablePred f] (h : ∀ a b, r a b → f a = f b) :
    DecidablePred (QuotLike.lift f h : Q → Prop) :=
  fun q ↦ QuotLike.recOnSubsingleton q fun _ ↦ by simpa using hf _

instance (priority := 800)
    {Qa α : Sort ua} {ra : α → α → Prop} [QuotLike Qa α ra] [IsRefl α ra]
    {Qb β : Sort ub} {rb : β → β → Prop} [QuotLike Qb β rb] [IsRefl β rb]
    (f : α → β → Prop) [hf : ∀ a, DecidablePred (f a)]
    (h : ∀ a₁ a₂ b₁ b₂, ra a₁ a₂ → rb b₁ b₂ → f a₁ b₁ = f a₂ b₂)
    (qa : Qa) (qb : Qb) :
    Decidable (QuotLike.lift₂ f h qa qb) :=
  QuotLike.recOnSubsingleton₂ qa qb fun _ _ ↦ by simpa using hf _ _

/-- Choose an element of the equivalence class using the axiom of choice. -/
noncomputable def out (q : Q) : α :=
  Classical.choose (exists_rep q)

@[simp]
theorem mkQ_out (q : Q) : ⟦QuotLike.out q⟧ = q :=
  Classical.choose_spec (exists_rep q)

-- Note: cannot be a `simp` lemma because lhs has variable as head symbol
theorem out_mkQ [IsEquiv α r] (a : α) : r (out (⟦a⟧ : Q)) a :=
  exact (mkQ_out _)

theorem mkQ_eq_iff_out [IsEquiv α r] {x : α} {y : Q} :
    ⟦x⟧ = y ↔ r x (out y) := by
  rw [← eq (Q := Q), mkQ_out]

theorem eq_mkQ_iff_out [IsEquiv α r] {x : Q} {y : α} :
    x = ⟦y⟧ ↔ r (out x) y := by
  rw [← eq (Q := Q), mkQ_out]

-- Note: cannot be a `simp` lemma because lhs has variable as head symbol
-- Note: not sure about the name
theorem out_equiv_out [IsEquiv α r] {x y : Q} : r (out x) (out y) ↔ x = y := by
  rw [← eq_mkQ_iff_out (Q := Q), mkQ_out]

theorem out_injective [IsEquiv α r] : Function.Injective (QuotLike.out : Q → α) :=
  fun _ _ h ↦ out_equiv_out.1 <| h ▸ refl _

@[simp]
theorem out_inj {x y : Q} [IsEquiv α r] : out x = out y ↔ x = y :=
  ⟨fun h ↦ out_injective h, fun h ↦ h ▸ rfl⟩

@[elab_as_elim]
theorem inductionOnPi {ι : Sort*} {Q : ι → Sort u} {α : ι → Sort u}
    {r : (i : ι) → α i → α i → Prop} [∀ i, QuotLike (Q i) (α i) (r i)]
    {p : (∀ i, Q i) → Prop} (q : ∀ i, Q i)
    (h : ∀ a : ∀ i, α i, p fun i ↦ ⟦a i⟧) : p q := by
  rw [← (funext fun i ↦ QuotLike.mkQ_out (q i) : (fun i ↦ ⟦out (q i)⟧) = q)]
  apply h

theorem nonempty_quotient_iff (s : Setoid α) : Nonempty (Quotient s) ↔ Nonempty α :=
  ⟨fun ⟨a⟩ ↦ Quotient.inductionOn a Nonempty.intro, fun ⟨a⟩ ↦ ⟨⟦a⟧⟩⟩

end

end QuotLike

export QuotLike (mkQ_eq_mkQ)
