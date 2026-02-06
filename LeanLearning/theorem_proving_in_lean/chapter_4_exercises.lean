import LeanLearning.theorem_proving_in_lean.chapter_3_exercises
set_option linter.unusedVariables false
open Classical

/- Exercise 1 -/

theorem fa_property_1 {α : Type} {p q : α → Prop} :
(∀ x : α, p x ∧ q x) ↔ (∀ x : α, p x) ∧ (∀ x : α, q x) :=
  Iff.intro

    (
      λ h : ∀ x : α, p x ∧ q x ↦
        have f₁ : (x : α) → p x := λ x : α ↦ (h x).left
        have f₂ : (x : α) → q x := λ x : α ↦ (h x).right
        show (∀ x : α, p x) ∧ (∀ x : α, q x) from ⟨f₁, f₂⟩
    )

    (
      λ (h : (∀ x : α, p x) ∧ (∀ x : α, q x)) (x : α) ↦ ⟨h.left x, h.right x⟩
    )

theorem fa_property_2 {α : Type} {p q : α → Prop} :
(∀ x : α, p x → q x) → (∀ x : α, p x) → (∀ x : α, q x) :=
  λ (h : ∀ x : α, p x → q x) (hp: ∀ x : α, p x) (x : α) ↦ (h x) (hp x)

theorem fa_property_3 {α : Type} {p q : α → Prop} :
(∀ x : α, p x) ∨ (∀ x : α, q x) → ∀ x : α, p x ∨ q x :=
  λ h : (∀ x : α, p x) ∨ (∀ x : α, q x) ↦
    have impl1: (∀ x : α, p x) → ∀ x : α, p x ∨ q x := λ (hp : ∀ x : α, p x) (x : α) ↦ Or.inl (hp x)
    have impl2: (∀ x : α, q x) → ∀ x : α, p x ∨ q x := λ (hq : ∀ x : α, q x) (x : α) ↦ Or.inr (hq x)
    show ∀ x : α, p x ∨ q x from Or.elim h impl1 impl2

/- Exercise 2 -/

theorem fa_property_4 {α : Type} {r : Prop} :
α → ((∀ x : α, r) ↔ r) := λ x : α ↦
  Iff.intro

    (λ h : (∀ x : α, r) ↦ h x)

    (λ (hr : r) (y : α) ↦ hr)

theorem lem_fa_prop_5 {p q : Prop} : (p ∨ q) → ¬ q → p :=
  λ (hpq : p ∨ q) (hnq: ¬ q) ↦
    have impl1: p → p := id
    have impl2: q → p := λ hq : q ↦ absurd hq hnq
    show p from Or.elim hpq impl1 impl2

theorem fa_property_5 {α : Type} {p : α → Prop} {r : Prop} :
(∀ x : α, p x ∨ r) ↔ (∀ x : α, p x) ∨ r :=
  Iff.intro

    (
      λ h : (∀ x : α, p x ∨ r) ↦
        have emr : r ∨ ¬ r := em r
        have impl1: r → (∀ x : α, p x) ∨ r := λ hr : r ↦ Or.inr hr
        have impl2: ¬ r → (∀ x : α, p x) ∨ r := λ hnr : ¬ r ↦
          have hpx : (∀ x : α, p x) := λ x : α ↦ lem_fa_prop_5 (h x) hnr
          show (∀ x : α, p x) ∨ r from Or.inl hpx
        show (∀ x : α, p x) ∨ r from Or.elim emr impl1 impl2
    )

    (
      λ h : (∀ x : α, p x) ∨ r ↦
        have impl1: (∀ x : α, p x) → (∀ x : α, p x ∨ r) := λ (hpx: (∀ x : α, p x)) (x : α) ↦ Or.inl (hpx x)
        have impl2: r → (∀ x : α, p x ∨ r) := λ (hr : r) (x : α) ↦ Or.inr hr
        show (∀ x : α, p x ∨ r) from Or.elim h impl1 impl2
    )

theorem fa_property_6 {α : Type} {p : α → Prop} {r : Prop} :
(∀ x : α, r → p x) ↔ (r → ∀ x : α, p x) :=
  Iff.intro

    (
      λ (h : (∀ x : α, r → p x)) (hr : r) (x : α) ↦ h x hr
    )

    (
      λ (h : (r → ∀ x : α, p x)) (x : α) (hr : r) ↦ h hr x
    )

/- Exercise 3
The barber paradox
-/

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have hb : shaves barber barber ∨ ¬ shaves barber barber := em (shaves barber barber)
  have case1 : shaves barber barber → False := λ hpos : shaves barber barber ↦
    have hn : ¬ shaves barber barber := (h barber).mp hpos
    show False from hn hpos
  have case2 : ¬ shaves barber barber → False := λ hn: ¬ shaves barber barber ↦
    have hpos : shaves barber barber := (h barber).mpr hn
    show False from hn hpos
  show False from Or.elim hb case1 case2

/- Exercise 4
Properly formulate all of the below propositions
-/

def even (n : Nat) : Prop := sorry

def prime (n : Nat) : Prop := sorry

def infinitely_many_primes : Prop := sorry

def Fermat_prime (n : Nat) : Prop := sorry

def infinitely_many_Fermat_primes : Prop := sorry

def goldbach_conjecture : Prop := sorry

def Goldbach's_weak_conjecture : Prop := sorry

def Fermat's_last_theorem : Prop := sorry

/- Exercise 5 -/

#check Exists.elim

theorem e_property_1 {α : Type} {r : Prop} :
(∃ x : α, r) → r := λ h : (∃ x : α, r) ↦
  Exists.elim h
    (
      λ (y : α) (hr : r) ↦ hr
    )

theorem e_property_2 {α : Type} {r : Prop} (a : α) :
r → (∃ x : α, r) := λ hr : r ↦ ⟨a, hr⟩

theorem e_property_3 {α : Type} {p : α → Prop} {r : Prop} :
(∃ x : α, p x ∧ r) ↔ (∃ x : α, p x) ∧ r :=
  Iff.intro

    (
      λ h : (∃ x : α, p x ∧ r) ↦
        -- use 'match' for pattern matching
        match h with
        | ⟨y, hpx, hr⟩ =>
        -- alternatively, 'let' works too
        --let ⟨y, hpx, hr⟩ : (∃ x : α, p x ∧ r) := h
        have left : (∃ x : α, p x) := ⟨y, hpx⟩
        have right : r := hr
        show (∃ x : α, p x) ∧ r from ⟨left, right⟩
    )

    (
      λ h : (∃ x : α, p x) ∧ r ↦
        let ⟨y, hpx⟩ : (∃ x : α, p x) := h.left
        let hr : r := h.right
        show (∃ x : α, p x ∧ r) from ⟨y, hpx, hr⟩
    )

theorem e_property_4 {α : Type} {p q : α → Prop} :
(∃ x : α, p x ∨ q x) ↔ (∃ x : α, p x) ∨ (∃ x : α, q x) :=
  Iff.intro

    (
      λ h : (∃ x : α, p x ∨ q x) ↦
        let ⟨y, hpq⟩ := h
        have impl1: p y → (∃ x : α, p x) ∨ (∃ x : α, q x) := λ hpy : p y ↦ Or.inl ⟨y, hpy⟩
        have impl2: q y → (∃ x : α, p x) ∨ (∃ x : α, q x) := λ hqy : q y ↦ Or.inr ⟨y, hqy⟩
        show (∃ x : α, p x) ∨ (∃ x : α, q x) from Or.elim hpq impl1 impl2
    )

    (
      λ h : (∃ x : α, p x) ∨ (∃ x : α, q x) ↦
        have impl1: (∃ x : α, p x) → (∃ x : α, p x ∨ q x) := λ hp : (∃ x : α, p x) ↦
          let ⟨y, hpx⟩ := hp
          show (∃ x : α, p x ∨ q x) from ⟨y, Or.inl hpx⟩
        have impl2: (∃ x : α, q x) → (∃ x : α, p x ∨ q x) := λ hq : (∃ x : α, q x) ↦
          let ⟨y, hqx⟩ := hq
          show (∃ x : α, p x ∨ q x) from ⟨y, Or.inr hqx⟩
        show (∃ x : α, p x ∨ q x) from Or.elim h impl1 impl2
    )

theorem e_property_5 {α : Type} {p : α → Prop}:
(∀ x : α, p x) ↔ ¬ (∃ x : α, ¬ p x) :=
  Iff.intro

    (
      λ (h : (∀ x : α, p x)) (hn : (∃ x : α, ¬ p x)) ↦
        let ⟨y, hnp⟩ := hn
        show False from hnp (h y)
    )

    (
      λ (h : ¬ (∃ x : α, ¬ p x)) (x : α) ↦
        /-we try out some anonymous notation here instead of
          naming every proof term and then use ‹ › to automatically
          infer the term later on
        -/
        have : p x ∨ ¬ (p x) := em (p x)
        have : p x → p x := id
        have : ¬ (p x) → p x := λ hn : ¬ (p x) ↦
          have : (∃ x : α, ¬ p x) := ⟨x, hn⟩
          show p x from absurd this h
        show p x from Or.elim ‹p x ∨ ¬ (p x)›  ‹p x → p x› ‹¬ p x → p x›
    )


theorem e_property_6 {α : Type} {p: α → Prop}:
(∃ x : α, p x) ↔ ¬ (∀ x : α, ¬ p x) :=
  Iff.intro
    /-
    TODO: even though the proof is easy using the previous property,
    it's still cumbersome to spell out all the details. Maybe revisit with tactics?
    -/
    (
      -- auxiliary statement using previous property
      have impl: ¬ (¬ (∀ x : α, ¬ p x)) → ¬ (∃ x : α, p x) := λ h : ¬ (¬ (∀ x : α, ¬ p x)) ↦
        have : (∀ x : α, ¬ p x) := pf_by_contr.mp h
        have f : ¬ (∃ x : α, ¬ (¬ (p x))) := e_property_5.mp this
        show ¬ (∃ x : α, p x) from λ h : (∃ x : α, p x) ↦
          let ⟨y, hpy⟩ := h
          show False from f (⟨y, pf_by_contr.mpr hpy⟩)

      λ h : (∃ x : α, p x) ↦
        have nimpl := property_18 impl
        show ¬ (∀ x : α, ¬ p x) from pf_by_contr.mp (nimpl (pf_by_contr.mpr h))
    )

    (
      -- auxiliary statement using previous property
      have impl: ¬ (∃ x : α, p x) → (∀ x : α, ¬ p x) := λ h : ¬ (∃ x : α, p x) ↦
        have : ¬ (∃ x : α, ¬ (¬ p x)) := λ (h_ : (∃ x : α, ¬ (¬ p x))) ↦
          let ⟨y, hpy⟩ := h_
          have : (∃ x : α, p x) := ⟨y, pf_by_contr.mp hpy⟩
          show False from h this
        show (∀ x : α, ¬ p x) from e_property_5.mpr ‹¬ (∃ x : α, ¬ (¬ p x))›

      λ h : ¬ (∀ x : α, ¬ p x) ↦
        have nimpl := property_18 impl
        show (∃ x : α, p x) from pf_by_contr.mp (nimpl h)
    )

theorem e_property_7 {α : Type} {p : α → Prop} :
(¬ ∃ x : α, p x) ↔ (∀ x : α, ¬ p x) :=
  Iff.intro

    (
      λ h : (¬ ∃ x : α, p x) ↦
        have : (¬ ∃ x : α, p x) → ¬ ¬ (∀ x : α, ¬ p x) := property_18 (e_property_6.mpr)
        show (∀ x : α, ¬ p x) from pf_by_contr.mp (this h)
    )

    (
      λ h : (∀ x : α, ¬ p x) ↦
        have : ¬ ¬ (∀ x : α, ¬ p x) → (¬ ∃ x : α, p x) := property_18 (e_property_6.mp)
        show (¬ ∃ x : α, p x) from this (pf_by_contr.mpr h)
    )

theorem e_property_8 {α : Type} {p : α → Prop} :
(¬ ∀ x : α, p x) ↔ (∃ x : α, ¬ p x) :=
  Iff.intro

    (
      λ h : (¬ ∀ x : α, p x) ↦
        have : (¬ ∀ x : α, p x) → ¬ ¬ (∃ x : α, ¬ p x) := property_18 (e_property_5.mpr)
        show (∃ x : α, ¬ p x) from pf_by_contr.mp (this h)
    )

    (
      λ h : (∃ x : α, ¬ p x) ↦
        have : (∃ x : α, ¬ p x) → (¬ ∀ x : α, ¬ (¬ p x)) := e_property_6.mp
        show (¬ ∀ x : α, p x) from λ ha : (∀ x : α, p x) ↦ (this h) (λ (x : α) ↦ pf_by_contr.mpr (ha x))
    )

theorem e_property_9 {α : Type} {p : α → Prop} {r : Prop} :
(∀ x : α, p x → r) ↔ (∃ x : α, p x) → r := sorry

theorem e_property_10 {α : Type} {p : α → Prop} {r : Prop} (a : α) :
(∃ x : α, p x → r) ↔ (∀ x : α, p x) → r := sorry

theorem e_property_11 {α : Type} {p : α → Prop} {r : Prop} (a : α) :
(∃ x : α, r → p x) ↔ (r → ∃ x : α, p x) := sorry
