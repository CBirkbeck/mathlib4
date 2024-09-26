import Mathlib.Tactic.Tendsto.Multiseries.Colist
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace TendstoTactic

abbrev Basis := List (ℝ → ℝ)

abbrev PreMS (basis : Basis) : Type :=
  match basis with
  | [] => ℝ
  | _ :: tl => CoList (ℝ × PreMS tl)

namespace PreMS

instance (basis : Basis) : Inhabited (PreMS basis) where
  default := match basis with
  | [] => default
  | _ :: _ => default

def leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis} (ms : PreMS (basis_hd :: basis_tl)) : WithBot ℝ :=
  ms.casesOn'
  (nil := ⊥)
  (cons := fun (deg, _) _ ↦ deg)

theorem leadingExp_eq_bot {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    ms = .nil ↔ ms.leadingExp = ⊥ := by
  apply ms.casesOn
  · simp [leadingExp]
  · intros
    simp [leadingExp]

-- theorem leadingExp_eq_real

inductive wellOrdered : {basis : Basis} → (PreMS basis) → Prop
| const (ms : PreMS []) : wellOrdered ms
| colist {hd : _} {tl : _} (ms : PreMS (hd :: tl))
    (h_coef : ∀ i x, ms.get i = .some x → x.2.wellOrdered)
    (h_wo : ∀ i j x y, (i < j) → (ms.get i = .some x) →
      (ms.get j = .some y) → (y.1 < x.1)) : ms.wellOrdered


theorem wellOrdered.nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    wellOrdered (basis := basis_hd :: basis_tl) .nil := by
  constructor
  · intro i x
    intro h
    simp at h
  · intro i j x y _ h
    simp at h

theorem wellOrdered.cons_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} (h_coef : coef.wellOrdered) :
    wellOrdered (basis := basis_hd :: basis_tl) <| .cons (deg, coef) .nil := by
  constructor
  · intro i x h
    cases i with
    | zero =>
      simp at h
      rw [← h]
      simpa
    | succ j =>
      simp at h
  · intro i j x y h_lt _ hj
    cases j with
    | zero => simp at h_lt
    | succ k => simp at hj

-- theorem wellOrdered.cons_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg1 deg2 : ℝ}
--     {coef1 coef2 : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
--     (h_coef1 : coef1.wellOrdered) (h_coef2: coef2.wellOrdered)
--     (h_tl : tl.wellOrdered) (h_lt : deg1 > deg2) :
--     wellOrdered (basis := basis_hd :: basis_tl) (.cons (deg1, coef1) (.cons (deg2, coef2) tl)) := by
--   cases h_tl with | colist _ h_tl_coef h_tl_tl =>
--   constructor
--   · intro i (deg, coef)
--     cases i with
--     | zero =>
--       simp
--       intro _ h
--       exact h ▸ h_coef1
--     | succ j =>
--       cases j with
--       | zero =>
--         simp
--         intro _ h
--         exact h ▸ h_coef2
--       | succ k =>
--         simp
--         simp at h_tl_coef
--         solve_by_elim
--   · intro i j x y h hi hj
--     sorry -- many cases

theorem wellOrdered.cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} (h_coef : coef.wellOrdered)
    (h_tl : tl.wellOrdered)
    (h_comp : ∀ tl_deg tl_coef tl_tl, (tl = .cons (tl_deg, tl_coef) tl_tl) → tl_deg < deg) :
    wellOrdered (basis := basis_hd :: basis_tl) <| .cons (deg, coef) tl := by
  cases h_tl with | colist _ h_tl_coef h_tl_tl =>
  constructor
  · intro i x h
    cases i with
    | zero =>
      simp at h
      rw [← h]
      simpa
    | succ j =>
      simp at h
      simp at h_tl_coef
      solve_by_elim
  · intro i j x y h_lt hi hj
    cases j with
    | zero => simp at h_lt
    | succ k =>
      revert hi hj h_comp h_tl_tl
      apply tl.casesOn
      · intro h_comp h_tl_tl hi hj
        focus
        simp at hj
      · intro (tl_deg, tl_coef) tl_tl h_comp h_tl_tl hi hj
        specialize h_comp _ _ _ (by rfl)
        cases i with
        | zero =>
          simp at hi
          cases k with
          | zero =>
            simp at hj
            simpa [← hi, ← hj]
          | succ l =>
            simp at hj
            specialize h_tl_tl 0 (l + 1) (tl_deg, tl_coef) y (by omega)
            simp at h_tl_tl
            specialize h_tl_tl hj
            simp [← hi]
            linarith
        | succ m =>
          cases k with
          | zero => simp at h_lt
          | succ l =>
            simp at hi
            simp at hj
            specialize h_tl_tl m (l + 1) x y (by omega)
            simp at h_tl_tl
            exact h_tl_tl hi hj

theorem wellOrdered_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)}
    (h : wellOrdered (basis := basis_hd :: basis_tl) (.cons (deg, coef) tl)) :
    coef.wellOrdered ∧ tl.wellOrdered ∧
      (∀ tl_deg tl_coef tl_tl, tl = .cons (tl_deg, tl_coef) tl_tl → (tl_deg < deg)) := by
  cases h with | colist _ h_coef h_comp =>
  constructor
  · specialize h_coef 0 (deg, coef)
    simpa using h_coef
  constructor
  · constructor
    · intro i x hx
      specialize h_coef (i + 1) x
      simp at h_coef hx
      exact h_coef hx
    · intro i j x y h_lt hx hy
      specialize h_comp (i + 1) (j + 1) x y
      simp at h_comp hx hy
      exact h_comp h_lt hx hy
  · intro tl_deg tl_coef tl_tl h_tl_eq
    subst h_tl_eq
    specialize h_comp 0 1 (deg, coef) (tl_deg, tl_coef) (by linarith)
    simpa using h_comp

theorem wellOrdered_coind {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (motive : (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (h_survive : ∀ ms, motive ms →
      (ms = .nil) ∨
      (
        ∃ deg coef tl, ms = .cons (deg, coef) tl ∧
        coef.wellOrdered ∧
        (∀ tl_deg tl_coef tl_tl, tl = .cons (tl_deg, tl_coef) tl_tl → (tl_deg < deg)) ∧
        (motive tl)
      )
    ) {ms : PreMS (basis_hd :: basis_tl)}
    (h : motive ms) : ms.wellOrdered := by
  have h_all : ∀ n, motive (CoList.tail^[n] ms) := by
    intro n
    induction n with
    | zero => simpa
    | succ m ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      specialize h_survive _ ih
      cases h_survive with
      | inl h_ms_eq =>
        rw [h_ms_eq] at ih ⊢
        simpa
      | inr h =>
        obtain ⟨deg, coef, tl, h_ms_eq, _, _, h_tl⟩ := h
        rw [h_ms_eq]
        simp
        exact h_tl
  constructor
  · intro i x hx
    simp at hx
    specialize h_survive _ (h_all i)
    cases h_survive with
    | inl h_ms_eq =>
      rw [h_ms_eq] at hx
      simp at hx
    | inr h =>
      obtain ⟨deg, coef, tl, h_ms_eq, h_coef, h_comp, h_tl⟩ := h
      rw [h_ms_eq] at hx
      simp at hx
      simpa [← hx]
  · intro i j x y h_lt hx hy
    replace h_lt := Nat.exists_eq_add_of_lt h_lt
    obtain ⟨k, hj⟩ := h_lt
    rw [add_assoc, add_comm] at hj
    subst hj
    induction k generalizing y with
    | zero =>
      simp at hx
      simp [CoList.get_eq_head, Function.iterate_add, Function.comp_apply] at hy
      specialize h_survive _ (h_all i)
      cases h_survive with
      | inl h_ms_eq =>
        simp [h_ms_eq] at hx
      | inr h =>
        obtain ⟨deg, coef, tl, h_ms_eq, _, h_comp, _⟩ := h
        simp [h_ms_eq] at hx hy
        revert h_comp hy
        apply tl.casesOn
        · intro _ hy
          simp at hy
        · intro (tl_deg, tl_coef) tl_tl h_comp hy
          simp at hy
          specialize h_comp _ _ _ (by rfl)
          simpa [← hx, ← hy]
    | succ l ih =>
      simp at hx hy ih
      rw [show l + 1 + 1 + i = l + 1 + i + 1 by linarith] at hy
      simp only [Function.iterate_succ', Function.comp_apply] at hy
      specialize h_survive _ (h_all (l + 1 + i))
      cases h_survive with
      | inl h_ms_eq =>
        simp [h_ms_eq] at hy
      | inr h =>
        obtain ⟨deg, coef, tl, h_ms_eq, _, h_comp, _⟩ := h
        simp [h_ms_eq] at hx hy ih
        revert h_comp hy
        apply tl.casesOn
        · intro _ hy
          simp at hy
        · intro (tl_deg, tl_coef) tl_tl h_comp hy
          simp at hy
          specialize h_comp _ _ _ (by rfl)
          rw [← hy]
          linarith

def allLt {basis_hd : ℝ → ℝ} {basis_tl : Basis} (ms : PreMS (basis_hd :: basis_tl)) (a : ℝ) :
    Prop :=
  ms.all fun (deg, coef) ↦ deg < a

theorem wellOrdered_cons_allLt {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    {tl : PreMS (basis_hd :: basis_tl)} {a : ℝ}
    (h_wo : wellOrdered (basis := basis_hd :: basis_tl) (CoList.cons (deg, coef) tl))
    (h_lt : deg < a) :
    allLt (basis_hd := basis_hd) (CoList.cons (deg, coef) tl) a := by
  simp only [allLt]
  let motive : PreMS (basis_hd :: basis_tl) → Prop := fun ms =>
    ∀ deg coef tl, ms = .cons (deg, coef) tl → deg < a ∧
      wellOrdered (basis := basis_hd :: basis_tl) (.cons (deg, coef) tl)
  apply CoList.all.coind motive
  · intro (deg, coef) tl ih
    simp only [motive] at ih
    specialize ih deg coef tl (by rfl)
    obtain ⟨h_lt, h_wo⟩ := ih
    constructor
    · exact h_lt
    simp only [motive]
    intro tl_deg tl_coef tl_tl h_tl_eq
    replace h_wo := wellOrdered_cons h_wo
    obtain ⟨_, h_tl_wo, h_comp⟩ := h_wo
    specialize h_comp tl_deg tl_coef tl_tl h_tl_eq
    constructor
    · linarith
    · rwa [← h_tl_eq]
  · simp only [motive]
    intro deg' coef' tl' h
    simp at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    subst h1 h2 h3
    constructor
    · exact h_lt
    · exact h_wo


noncomputable def partialSumsFrom (Cs : CoList (ℝ → ℝ)) (degs : CoList ℝ) (basis_fun : ℝ → ℝ)
    (init : ℝ → ℝ) : CoList (ℝ → ℝ) :=
  Cs.zip degs |>.fold init fun acc (C, deg) =>
    fun x ↦ acc x + (basis_fun x)^deg * (C x)

noncomputable def partialSums (Cs : CoList (ℝ → ℝ)) (degs : CoList ℝ) (basis_fun : ℝ → ℝ) :
    CoList (ℝ → ℝ) :=
  partialSumsFrom Cs degs basis_fun 0

theorem partialSumsFrom_nil {degs : CoList ℝ} {basis_fun : ℝ → ℝ} {init : ℝ → ℝ} :
    partialSumsFrom .nil degs basis_fun init = .cons init .nil := by
  simp [partialSumsFrom]

theorem partialSumsFrom_cons {Cs_hd : ℝ → ℝ} {Cs_tl : CoList (ℝ → ℝ)} {degs_hd : ℝ}
    {degs_tl : CoList ℝ} {basis_fun : ℝ → ℝ} {init : ℝ → ℝ} :
    partialSumsFrom (.cons Cs_hd Cs_tl) (.cons degs_hd degs_tl) basis_fun init =
    (.cons init <| partialSumsFrom Cs_tl degs_tl basis_fun
      (fun x ↦ init x + (basis_fun x)^degs_hd * (Cs_hd x))) := by
  simp [partialSumsFrom]

theorem partialSumsFrom_eq_map {Cs : CoList (ℝ → ℝ)} {degs : CoList ℝ} {basis_fun : ℝ → ℝ}
    {init : ℝ → ℝ} (h : Cs.atLeastAsLongAs degs) :
    partialSumsFrom Cs degs basis_fun init =
      (partialSums Cs degs basis_fun).map fun G => init + G := by

  let motive : CoList (ℝ → ℝ) → CoList (ℝ → ℝ) → Prop := fun x y =>
    ∃ Cs degs init D,
      Cs.atLeastAsLongAs degs ∧
      (
        (x = partialSumsFrom Cs degs basis_fun (D + init)) ∧
        (y = (partialSumsFrom Cs degs basis_fun init).map fun G => D + G)
      ) ∨
      (x = .nil ∧ y = .nil)
  apply CoList.Eq.coind motive
  · intro x y ih
    simp [motive] at ih
    obtain ⟨Cs', degs', init', D, ih⟩ := ih
    cases' ih with ih ih
    · left
      obtain ⟨h_alal, h_x_eq, h_y_eq⟩ := ih
      revert h_alal h_x_eq h_y_eq
      apply degs'.casesOn
      · simp [partialSums, partialSumsFrom]
        intro h_x_eq h_y_eq
        use D + init'
        use .nil
        constructor
        · assumption
        use D + init'
        use .nil
        constructor
        · assumption
        constructor
        · rfl
        simp [motive]
      · intro degs_hd degs_tl h_alal h_x_eq h_y_eq
        obtain ⟨Cs_hd, Cs_tl, h_Cs⟩ := CoList.atLeastAsLongAs_cons h_alal
        subst h_Cs
        simp [partialSums, partialSumsFrom_cons] at h_x_eq h_y_eq
        use D + init'
        use (partialSumsFrom Cs_tl degs_tl basis_fun fun x ↦ D x + init' x +
          basis_fun x ^ degs_hd * Cs_hd x)
        use D + init'
        use (CoList.map (fun G ↦ D + G) (partialSumsFrom Cs_tl degs_tl basis_fun fun x ↦ init' x +
          basis_fun x ^ degs_hd * Cs_hd x))
        constructor
        · assumption
        constructor
        · assumption
        constructor
        · rfl
        simp [motive]
        simp at h_alal
        use Cs_tl
        use degs_tl
        use fun x ↦ init' x + basis_fun x ^ degs_hd * Cs_hd x
        use D
        left
        constructor
        · assumption
        constructor
        · congr
          eta_expand
          simp
          ext
          ring_nf
        rfl
    · right
      exact ih
  · simp [motive]
    use Cs
    use degs
    use 0
    use init
    left
    constructor
    · assumption
    constructor
    · simp
    · simp [partialSums]

-- a non valid occurrence of the datatypes being declared
-- inductive isApproximation : (ℝ → ℝ) → (basis : Basis) → PreMS basis → Prop where
-- | const {c : ℝ} {F : ℝ → ℝ} (h : F =ᶠ[Filter.atTop] fun _ ↦ c) : isApproximation F [] c
-- | colist {F basis_hd : ℝ → ℝ} {basis_tl : Basis} (ms : PreMS (basis_hd :: basis_tl))
--   (Cs : CoList (ℝ → ℝ))
--   (h_coef : (Cs.zip ms).all fun (C, (deg, coef)) => isApproximation C basis_tl coef)
--   (h_comp : (partialSums Cs (ms.map fun x => x.1) basis_hd).zip (ms.map fun x => x.1) |>.all
--     fun (ps, deg) => ∀ deg', deg < deg' → (fun x ↦ F x - ps x) =o[Filter.atTop]
--       (fun x ↦ (basis_hd x)^deg')) :
--   isApproximation F (basis_hd :: basis_tl) ms

def isApproximation (F : ℝ → ℝ) (basis : Basis) (ms : PreMS basis) : Prop :=
  match basis with
  | [] => F =ᶠ[Filter.atTop] fun _ ↦ ms
  | basis_hd :: basis_tl =>
    ∃ Cs : CoList (ℝ → ℝ),
    Cs.atLeastAsLongAs ms ∧
    ((Cs.zip ms).all fun (C, (_, coef)) => isApproximation C basis_tl coef) ∧
    (
      let degs := ms.map fun x => x.1;
      let degs' : CoList (Option ℝ) := (degs.map .some).append (.cons .none .nil);
      (partialSums Cs degs basis_hd).zip degs' |>.all fun (ps, deg?) =>
        match deg? with
        | .some deg => ∀ deg', deg < deg' → (fun x ↦ F x - ps x) =o[Filter.atTop]
          fun x ↦ (basis_hd x)^deg'
        | .none => (fun x ↦ F x - ps x) =ᶠ[Filter.atTop] 0
    )

theorem isApproximation_nil {F basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h : isApproximation F (basis_hd :: basis_tl) CoList.nil) :
    F =ᶠ[Filter.atTop] 0 := by
  unfold isApproximation at h
  obtain ⟨Cs, _, _, h_comp⟩ := h
  simp at h_comp
  unfold CoList.all at h_comp
  specialize h_comp 0
  simpa [partialSums, partialSumsFrom] using h_comp

theorem isApproximation_cons {F basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : isApproximation F (basis_hd :: basis_tl) (.cons (deg, coef) tl)) :
    ∃ C,
      isApproximation C basis_tl coef ∧
      (∀ deg', deg < deg' → F =o[Filter.atTop] (fun x ↦ (basis_hd x)^deg')) ∧
      isApproximation (fun x ↦ F x - (basis_hd x)^deg * (C x)) (basis_hd :: basis_tl) tl := by
  unfold isApproximation at h
  obtain ⟨Cs, h_alal, h_coef, h_comp⟩ := h
  obtain ⟨C, Cs_tl, h_alal⟩ := CoList.atLeastAsLongAs_cons h_alal
  subst h_alal
  use C
  simp [CoList.all_cons] at h_coef
  constructor
  · exact h_coef.left
  · constructor
    · simp [partialSums, partialSumsFrom] at h_comp
      exact h_comp.left
    · simp at h_alal
      unfold isApproximation
      use Cs_tl
      constructor
      · assumption
      · constructor
        · exact h_coef.right
        · simp [partialSums, partialSumsFrom_cons] at h_comp
          replace h_comp := h_comp.right
          rw [partialSumsFrom_eq_map (CoList.atLeastAsLongAs_map h_alal)] at h_comp
          rw [CoList.map_zip_left] at h_comp
          replace h_comp := CoList.map_all_iff.mp h_comp
          apply CoList.all_mp _ h_comp
          intro (C', deg?)
          simp
          intro h
          ring_nf at h
          ring_nf
          exact h

private structure isApproximation_coind_auxT (motive : (F : ℝ → ℝ) → (basis_hd : ℝ → ℝ) →
    (basis_tl : Basis) → (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (basis_hd : ℝ → ℝ) (basis_tl : Basis) where
  val : PreMS (basis_hd :: basis_tl)
  F : ℝ → ℝ
  h : motive F basis_hd basis_tl val

theorem isApproximation_coind' (motive : (F : ℝ → ℝ) → (basis_hd : ℝ → ℝ) →
    (basis_tl : Basis) → (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (h_survive : ∀ basis_hd basis_tl F ms, motive F basis_hd basis_tl ms →
      (ms = .nil ∧ F =ᶠ[Filter.atTop] 0) ∨
      (
        ∃ deg coef tl C, ms = .cons (deg, coef) tl ∧
        (isApproximation C basis_tl coef) ∧
        (∀ deg', deg < deg' → F =o[Filter.atTop] fun x ↦ (basis_hd x)^deg') ∧
        (motive (fun x ↦ F x - (basis_hd x)^deg * (C x)) basis_hd basis_tl tl)
      )
    ) {basis_hd : ℝ → ℝ} {basis_tl : Basis} {F : ℝ → ℝ} {ms : PreMS (basis_hd :: basis_tl)}
    (h : motive F basis_hd basis_tl ms) : isApproximation F (basis_hd :: basis_tl) ms := by
  simp [isApproximation]
  let T := isApproximation_coind_auxT motive basis_hd basis_tl
  let g : T → CoList.OutType (ℝ → ℝ) T := fun ⟨val, F, h⟩ =>
    (val.casesOn (motive := fun ms => motive F basis_hd basis_tl ms → CoList.OutType (ℝ → ℝ) T)
    (nil := fun _ => .nil)
    (cons := fun (deg, coef) tl =>
      fun h =>
        have spec : ∃ C,
            isApproximation C basis_tl coef ∧
            (∀ (deg' : ℝ), deg < deg' → F =o[Filter.atTop] fun x ↦ basis_hd x ^ deg') ∧
            motive (fun x ↦ F x - basis_hd x ^ deg * C x) basis_hd basis_tl tl := by
          specialize h_survive _ _ _ _ h
          simp at h_survive
          obtain ⟨deg_1, coef_1, tl_1, ⟨⟨h_deg, h_coef⟩, h_tl⟩, h_survive⟩ := h_survive
          subst h_deg
          subst h_coef
          subst h_tl
          exact h_survive
        let C := spec.choose
        .cons C ⟨tl, fun x ↦ F x - (basis_hd x)^deg * (C x), spec.choose_spec.right.right⟩
    )
    ) h
  let Cs : CoList (ℝ → ℝ) := CoList.corec g ⟨ms, F, h⟩
  use Cs
  constructor
  · let motive' : CoList (ℝ → ℝ) → CoList (ℝ × PreMS basis_tl) → Prop := fun Cs ms =>
      ∃ F h, Cs = (CoList.corec g ⟨ms, F, h⟩)
    apply CoList.atLeastAsLong.coind motive'
    · intro Cs ms ih (deg, coef) tl h_ms_eq
      simp only [motive'] at ih
      obtain ⟨F, h, h_Cs_eq⟩ := ih
      subst h_ms_eq
      rw [CoList.corec_cons] at h_Cs_eq
      pick_goal 2
      · simp [g]
        constructor <;> rfl
      use ?_
      use ?_
      constructor
      · exact h_Cs_eq
      simp only [motive']
      generalize_proofs p1 p2
      use fun x ↦ F x - basis_hd x ^ deg * p1.choose x
      use p2
    · simp only [motive']
      use F
      use h
  · constructor
    · let motive' : CoList ((ℝ → ℝ) × ℝ × PreMS basis_tl) → Prop := fun li =>
        ∃ (ms : CoList (ℝ × PreMS basis_tl)), ∃ F h,
          li = (CoList.corec g ⟨ms, F, h⟩).zip ms
      apply CoList.all.coind motive'
      · intro (C, (deg, coef)) tl ih
        simp only
        simp only [motive'] at ih
        obtain ⟨ms, F, h, h_eq⟩ := ih
        specialize h_survive _ _ _ _ h
        revert h h_eq h_survive
        apply ms.casesOn
        · intro h h_eq h_survive
          simp at h_eq
        · intro (ms_deg, ms_coef) ms_tl h h_eq h_survive
          rw [CoList.corec_cons] at h_eq
          pick_goal 2
          · simp [g]
            constructor <;> rfl
          simp at h_eq
          obtain ⟨⟨h1, ⟨h2, h3⟩⟩, h_eq⟩ := h_eq
          constructor
          · subst h1
            subst h2
            subst h3
            generalize_proofs p
            exact p.choose_spec.left
          · simp only [motive']
            use ?_
            use ?_
            use ?_
      · simp only [motive']
        use ms
        use F
        use h
    · simp [partialSums]
      let motive' : CoList ((ℝ → ℝ) × Option ℝ) → Prop := fun li =>
        li = .nil ∨ ∃ (ms : CoList (ℝ × PreMS basis_tl)), ∃ G h init,
          li = ((partialSumsFrom (CoList.corec g ⟨ms, G, h⟩) (CoList.map (fun x ↦ x.1) ms) basis_hd init).zip
      ((CoList.map some (CoList.map (fun x ↦ x.1) ms)).append (CoList.cons none CoList.nil))) ∧
      G + init =ᶠ[Filter.atTop] F
      apply CoList.all.coind motive'
      · intro (F', deg?) li_tl ih
        simp only [motive'] at ih
        cases ih with
        | inl ih => simp at ih
        | inr ih =>
        obtain ⟨ms, G, h_mot, init, h_eq, hF_eq⟩ := ih
        · simp
          revert h_mot h_eq
          apply ms.casesOn
          · intro h_mot h_eq
            rw [CoList.corec_nil] at h_eq
            swap
            · simp [g]
            simp [partialSumsFrom_nil] at h_eq
            obtain ⟨⟨h1, h2⟩, h3⟩ := h_eq
            subst h1 h2 h3
            simp
            specialize h_survive _ _ _ _ h_mot
            cases h_survive with
            | inr h_survive => simp at h_survive
            | inl h_survive =>
              simp at h_survive
              constructor
              · apply Filter.eventuallyEq_iff_sub.mp
                trans
                · exact hF_eq.symm
                conv => rhs; ext x; rw [← zero_add (F' x)]
                apply Filter.EventuallyEq.add h_survive
                rfl
              · simp [motive']
          · intro (deg, coef) tl h_mot h_eq
            rw [CoList.corec_cons] at h_eq
            swap
            · simp [g]
              constructor <;> rfl
            simp [partialSumsFrom_cons] at h_eq
            obtain ⟨⟨h1, h2⟩, h3⟩ := h_eq
            subst h1 h2 h3
            simp
            constructor
            · intro deg' h_deg
              apply Filter.EventuallyEq.trans_isLittleO (f₂ := G)
              · apply Filter.eventuallyEq_iff_sub.mpr
                replace hF_eq := Filter.eventuallyEq_iff_sub.mp hF_eq.symm
                trans F - (G + F')
                · apply Filter.eventuallyEq_iff_sub.mpr
                  eta_expand
                  simp
                  ring_nf!
                  rfl
                · exact hF_eq
              · generalize_proofs h at h_eq
                obtain ⟨_, _, h_comp, _⟩ := h
                apply h_comp _ h_deg
            · simp [motive']
              right
              generalize_proofs h1 h2
              use tl
              use fun x ↦ G x - basis_hd x ^ deg * h1.choose x
              use h2
              use fun x ↦ F' x + basis_hd x ^ deg * h1.choose x
              constructor
              · rfl
              apply Filter.eventuallyEq_iff_sub.mpr
              eta_expand
              simp
              ring_nf!
              conv =>
                lhs; ext x; rw [show G x + (F' x - F x) = (G x + F' x) - F x by ring]
              apply Filter.eventuallyEq_iff_sub.mp
              exact hF_eq
      · simp only [motive']
        right
        use ms
        use F
        use h
        use 0
        constructor
        · rfl
        simp

-- without basis in motive
theorem isApproximation_coind {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (motive : (F : ℝ → ℝ) → (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (h_survive : ∀ F ms, motive F ms →
      (ms = .nil ∧ F =ᶠ[Filter.atTop] 0) ∨
      (
        ∃ deg coef tl C, ms = .cons (deg, coef) tl ∧
        (isApproximation C basis_tl coef) ∧
        (∀ deg', deg < deg' → F =o[Filter.atTop] fun x ↦ (basis_hd x)^deg') ∧
        (motive (fun x ↦ F x - (basis_hd x)^deg * (C x)) tl)
      )
    ) {F : ℝ → ℝ} {ms : PreMS (basis_hd :: basis_tl)}
    (h : motive F ms) : isApproximation F (basis_hd :: basis_tl) ms := by
  let motive' : (F : ℝ → ℝ) → (basis_hd : ℝ → ℝ) →
    (basis_tl : Basis) → (ms : PreMS (basis_hd :: basis_tl)) → Prop :=
    fun F' basis_hd' basis_tl' ms' =>
      ∃ (h_hd : basis_hd' = basis_hd) (h_tl : basis_tl' = basis_tl), motive F' (h_tl ▸ (h_hd ▸ ms'))
  apply isApproximation_coind' motive'
  · intro basis_hd' basis_tl' F' ms' ih
    simp [motive'] at ih ⊢
    obtain ⟨h_hd, h_tl, ih⟩ := ih
    subst h_hd h_tl
    specialize h_survive F' ms' ih
    cases h_survive with
    | inl h_survive =>
      left
      exact h_survive
    | inr h_survive =>
      right
      obtain ⟨deg, coef, tl, C, h_ms_eq, h_coef, h_comp, h_tl⟩ := h_survive
      use deg
      use coef
      use tl
      constructor
      · exact h_ms_eq
      use C
      constructor
      · exact h_coef
      constructor
      · exact h_comp
      simpa
  · simp [motive']
    assumption

-- Prove with coinduction?
theorem isApproximation.nil {F : ℝ → ℝ} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h : F =ᶠ[Filter.atTop] 0) : isApproximation F (basis_hd :: basis_tl) .nil := by
  simp [isApproximation]
  use .nil
  simpa [partialSums, partialSumsFrom]

theorem isApproximation.cons {F : ℝ → ℝ} {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (C : ℝ → ℝ) (h_coef : coef.isApproximation C basis_tl)
    (h_comp : (∀ deg', deg < deg' → F =o[Filter.atTop] (fun x ↦ (basis_hd x)^deg')))
    (h_tl : tl.isApproximation (fun x ↦ F x - (basis_hd x)^deg * (C x)) (basis_hd :: basis_tl)) :
    isApproximation F (basis_hd :: basis_tl) (.cons (deg, coef) tl) := by
  simp [isApproximation] at h_tl ⊢
  obtain ⟨Cs, h_tl_alal, h_tl_coef, h_tl_comp⟩ := h_tl
  use .cons C Cs
  constructor
  · simpa
  constructor
  · simp
    constructor
    · exact h_coef
    · exact h_tl_coef
  · unfold partialSums at h_tl_comp ⊢
    simp [partialSumsFrom_cons]
    constructor
    · exact h_comp
    · rw [partialSumsFrom_eq_map (CoList.atLeastAsLongAs_map h_tl_alal)] -- copypaste from `isApproximation_cons`
      rw [CoList.map_zip_left]
      apply CoList.map_all_iff.mpr
      apply CoList.all_mp _ h_tl_comp
      intro (C', deg?)
      simp
      intro h
      ring_nf at h
      ring_nf
      exact h

---------

theorem isApproximation_of_EventuallyEq {basis : Basis} {ms : PreMS basis} {F F' : ℝ → ℝ}
    (h_approx : ms.isApproximation F basis) (h_equiv : F =ᶠ[Filter.atTop] F') :
    ms.isApproximation F' basis :=
  match basis with
  | [] => by
    simp [isApproximation] at h_approx
    exact Filter.EventuallyEq.trans h_equiv.symm h_approx
  | basis_hd :: basis_tl => by
    let motive : (F : ℝ → ℝ) → (ms : PreMS (basis_hd :: basis_tl)) → Prop :=
      fun F' ms =>
        ∃ F, F =ᶠ[Filter.atTop] F' ∧ isApproximation F (basis_hd :: basis_tl) ms
    apply isApproximation_coind motive
    · intro F' ms ih
      revert ih
      apply ms.casesOn
      · intro ih
        left
        simp [motive] at ih
        obtain ⟨F, h_equiv, hF⟩ := ih
        replace hF := isApproximation_nil hF
        constructor
        · rfl
        · exact Filter.EventuallyEq.trans h_equiv.symm hF
      · intro (deg, coef) tl ih
        right
        use deg
        use coef
        use tl
        simp
        simp [motive] at ih
        obtain ⟨F, h_equiv, hF⟩ := ih
        replace hF := isApproximation_cons hF
        obtain ⟨C, h_coef, h_comp, h_tl⟩ := hF
        use C
        constructor
        · exact h_coef
        constructor
        · intro deg' h
          apply Filter.EventuallyEq.trans_isLittleO h_equiv.symm
          apply h_comp _ h
        · simp [motive]
          use fun x ↦ F x - basis_hd x ^ deg * (C x)
          constructor
          · apply Filter.EventuallyEq.sub h_equiv
            apply Filter.EventuallyEq.rfl
          · exact h_tl
    · simp only [motive]
      use F

-- Try to prove later
-- theorem EventuallyEq_of_isApproximation {F F' : ℝ → ℝ} {basis : Basis} {ms : PreMS basis}
--     (h_approx : ms.isApproximation F basis) (h_approx' : ms.isApproximation F' basis) :
--     F =ᶠ[Filter.atTop] F' :=
--   match basis with
--   | [] => by
--     simp [isApproximation] at *
--     trans (fun _ ↦ ms)
--     · exact h_approx
--     · exact h_approx'.symm
--   | basis_hd :: basis_tl => by

--     revert h_approx h_approx'
--     apply ms.casesOn
--     · intro h_approx h_approx'
--       replace h_approx := isApproximation_nil h_approx
--       replace h_approx' := isApproximation_nil h_approx'
--       trans (fun _ ↦ 0)
--       · exact h_approx
--       · exact h_approx'.symm
--     · intro (deg, coef) tl h_approx h_approx'
--       replace h_approx := isApproximation_cons h_approx
--       replace h_approx' := isApproximation_cons h_approx'
--       obtain ⟨C, h_coef, h_comp, h_tl⟩ := h_approx
--       obtain ⟨C', h_coef', h_comp', h_tl'⟩ := h_approx'



--   induction ms using PreMS.rec' generalizing F F' basis with
--   | nil =>
--     cases h_approx with | nil _ _ h =>
--     cases h_approx' with | nil _ _ h' =>
--     trans 0
--     · exact h
--     · exact h'.symm
--   | const c =>
--     cases h_approx with | const _ _ h =>
--     cases h_approx' with | const _ _ h' =>
--     trans (fun _ ↦ c)
--     · exact h
--     · exact h'.symm
--   | cons deg coef tl coef_ih tl_ih =>
--     cases h_approx with | cons _ _ _ _ C basis_hd basis_tl h_coef h_tl h_comp =>
--     cases h_approx' with | cons _ _ _ _ C' _ _ h_coef' h_tl' h_comp' =>
--     have : (fun x ↦ basis_hd x ^ deg * C x) =ᶠ[Filter.atTop] (fun x ↦ basis_hd x ^ deg * C' x) :=
--       Filter.EventuallyEq.mul (by rfl) (coef_ih h_coef h_coef')
--     have := (tl_ih h_tl h_tl').add this
--     simpa using this

---------

def const (c : ℝ) (basis : Basis) : PreMS basis :=
  match basis with
  | [] => c
  | _ :: basis_tl =>
    .cons (0, const c basis_tl) .nil

def zero (basis) : PreMS basis :=
  match basis with
  | [] => 0
  | _ :: _ => .nil

def one (basis : Basis) : PreMS basis :=
  const 1 basis

end PreMS

structure MS where
  basis : Basis
  val : PreMS basis
  F : ℝ → ℝ
  h_wo : val.wellOrdered
  h_approx : val.isApproximation F basis

end TendstoTactic
