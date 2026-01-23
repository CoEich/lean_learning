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

theorem fa_property_6 {α : Type} {p q : α → Prop} {r : Prop} :
(∀ x : α, r → p x) ↔ (r → ∀ x : α, p x) := sorry

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

theorem e_property_1 {α : Type} {r : Prop} :
(∃ x : α, r) → r := sorry

theorem e_property_2 {α : Type} {r : Prop} (a : α) :
r → (∃ x : α, r) := sorry

theorem e_property_3 {α : Type} {p : α → Prop} {r : Prop} :
(∃ x : α, p x ∧ r) ↔ (∃ x : α, p x) ∧ r := sorry

theorem e_property_4 {α : Type} {p q : α → Prop} :
(∃ x : α, p x ∨ q x) ↔ (∃ x : α, p x) ∨ (∃ x : α, q x) := sorry

theorem e_property_5 {α : Type} {p : α → Prop}:
(∀ x : α, p x) ↔ ¬ (∃ x : α, ¬ p x) := sorry

theorem e_property_6 {α : Type} {p: α → Prop}:
(∃ x : α, p x) ↔ ¬ (∀ x : α, ¬ p x) := sorry

theorem e_property_7 {α : Type} {p : α → Prop} :
(¬ ∃ x : α, p x) ↔ (∀ x : α, ¬ p x) := sorry

theorem e_property_8 {α : Type} {p : α → Prop} :
(¬ ∀ x : α, p x) ↔ (∃ x : α, ¬ p x) := sorry

theorem e_property_9 {α : Type} {p : α → Prop} {r : Prop} :
(∀ x : α, p x → r) ↔ (∃ x : α, p x) → r := sorry

theorem e_property_10 {α : Type} {p : α → Prop} {r : Prop} (a : α) :
(∃ x : α, p x → r) ↔ (∀ x : α, p x) → r := sorry

theorem e_property_11 {α : Type} {p : α → Prop} {r : Prop} (a : α) :
(∃ x : α, r → p x) ↔ (r → ∃ x : α, p x) := sorry
