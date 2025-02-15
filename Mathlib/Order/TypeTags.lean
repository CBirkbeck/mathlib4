/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Yury Kudryashov
-/
import Mathlib.Order.Notation

/-!
# Order-related type synonyms

In this file we define `WithBot`, `WithTop`, `ENat`, and `PNat`.
The definitions were moved to this file without any theory
so that, e.g., `Data/Countable/Basic` can prove `Countable ENat`
without exploding its imports.
-/

variable {α : Type*}

/-- Attach `⊥` to a type. -/
@[order_dual]
def WithBot (α : Type*) := Option α

namespace WithBot

@[order_dual]
instance [Repr α] : Repr (WithBot α) :=
  ⟨fun o _ =>
    match o with
    | none => "⊥"
    | some a => "↑" ++ repr a⟩

/-- The canonical map from `α` into `WithBot α` -/
@[order_dual (attr := coe, match_pattern)] def some : α → WithBot α :=
  Option.some

-- Porting note: changed this from `CoeTC` to `Coe` but I am not 100% confident that's correct.
@[order_dual]
instance coe : Coe α (WithBot α) :=
  ⟨some⟩

@[order_dual]
instance bot : Bot (WithBot α) :=
  ⟨none⟩

@[order_dual]
instance inhabited : Inhabited (WithBot α) :=
  ⟨⊥⟩

/-- Recursor for `WithBot` using the preferred forms `⊥` and `↑a`. -/
@[order_dual (attr := elab_as_elim, induction_eliminator, cases_eliminator)
"Recursor for `WithTop` using the preferred forms `⊤` and `↑a`."]
def recBotCoe {C : WithBot α → Sort*} (bot : C ⊥) (coe : ∀ a : α, C a) : ∀ n : WithBot α, C n
  | ⊥ => bot
  | (a : α) => coe a

@[order_dual (attr := simp)]
theorem recBotCoe_bot {C : WithBot α → Sort*} (d : C ⊥) (f : ∀ a : α, C a) :
    @recBotCoe _ C d f ⊥ = d :=
  rfl

@[order_dual (attr := simp)]
theorem recBotCoe_coe {C : WithBot α → Sort*} (d : C ⊥) (f : ∀ a : α, C a) (x : α) :
    @recBotCoe _ C d f ↑x = f x :=
  rfl

end WithBot

--TODO(Mario): Construct using order dual on `WithBot`
-- /-- Attach `⊤` to a type. -/
-- def WithTop (α : Type*) :=
--   Option α

namespace WithTop

-- instance [Repr α] : Repr (WithTop α) :=
--   ⟨fun o _ =>
--     match o with
--     | none => "⊤"
--     | some a => "↑" ++ repr a⟩

/-- The canonical map from `α` into `WithTop α` -/
-- @[coe, match_pattern] def some : α → WithTop α :=
--   Option.some

@[order_dual]
instance coeTC : CoeTC α (WithTop α) :=
  ⟨some⟩

-- instance top : Top (WithTop α) :=
--   ⟨none⟩

-- instance inhabited : Inhabited (WithTop α) :=
--   ⟨⊤⟩

-- /-- Recursor for `WithTop` using the preferred forms `⊤` and `↑a`. -/
-- @[elab_as_elim, induction_eliminator, cases_eliminator]
-- def recTopCoe {C : WithTop α → Sort*} (top : C ⊤) (coe : ∀ a : α, C a) : ∀ n : WithTop α, C n
--   | none => top
--   | Option.some a => coe a

-- @[simp]
-- theorem recTopCoe_top {C : WithTop α → Sort*} (d : C ⊤) (f : ∀ a : α, C a) :
--     @recTopCoe _ C d f ⊤ = d :=
--   rfl

-- @[simp]
-- theorem recTopCoe_coe {C : WithTop α → Sort*} (d : C ⊤) (f : ∀ a : α, C a) (x : α) :
--     @recTopCoe _ C d f ↑x = f x :=
--   rfl

end WithTop
