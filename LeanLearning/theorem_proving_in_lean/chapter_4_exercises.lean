/- Exercise 1 -/

theorem fa_property_1 {α : Type} {p q : α → Prop} :
(∀ x : α, p x ∧ q x) ↔ (∀ x : α, p x) ∧ (∀ x : α, q x) := sorry

theorem fa_property_2 {α : Type} {p q : α → Prop} :
(∀ x : α, p x → q x) → (∀ x : α, p x) → (∀ x : α, q x) := sorry

theorem fa_property_3 {α : Type} {p q : α → Prop} :
(∀ x : α, p x) ∨ (∀ x : α, q x) → ∀ x : α, p x ∨ q x := sorry

/- Exercise 2 -/

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

theorem fa_property_4 {α : Type} {p q : α → Prop} {r : Prop} :
α → ((∀ x : α, r) ↔ r) := sorry

theorem fa_property_5 {α : Type} {p q : α → Prop} {r : Prop} :
(∀ x : α, p x ∨ r) ↔ (∀ x : α, p x) ∨ r := sorry

theorem fa_property_6 {α : Type} {p q : α → Prop} {r : Prop} :
(∀ x : α, r → p x) ↔ (r → ∀ x : α, p x) := sorry

/- Exercise 3
The barber paradox
-/

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  sorry

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

open Classical

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
