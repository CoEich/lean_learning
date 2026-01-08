/- -------------------------------- Exercise 1.13
Using propositions-as-types, derive the double negation of the principle of excluded middle,
i.e. prove not (not (P or not P))
-/

/- We use two auxiliary lemmas-/

/-1. p and not p implies a contradiction-/
theorem lem1 {p: Prop} : p ∧ ¬ p -> False :=
  λ (h : p ∧ ¬ p) =>
    show False from  h.right h.left

/-2. One-sided De Morgan rule-/
theorem lem2 {p q : Prop}: ¬ (p ∨ q) → ¬ p ∧ ¬ q :=
  λ (f: ¬ (p ∨ q)) =>
    have hnp: ¬ p := λ (hp : p) => f (Or.inl hp)
    have hnq: ¬ q := λ (hq : q) => f (Or.inr hq)
    show ¬ p ∧ ¬ q from ⟨hnp, hnq⟩

/- The desired statement follows by applying both lemmas-/
theorem double_negate_lem (p: Prop) : ¬ (¬ (p ∨ ¬ p)) :=
  λ (f : ¬ (p ∨ ¬ p)) =>
  show False from lem1 (lem2 f)


/- ---------------------- Exercise 1.2
Derive the recursion principle for products recA×B using only the projections, and
verify that the definitional equalities are valid. Do the same for Σ-types.

-/

/- non-dependent version

section
  variable {α β : Type}

  def proj_1 (p: α × β) : α := p.1
  def proj_2 (p: α × β) : β := p.2

  def rec {γ : Type} (f: α → β → γ) : α × β → γ := λ (p: α × β) => f (proj_1 p) (proj_2 p)

  theorem rec_defining_eq {γ : Type} (f: α → β → γ) (a : α) (b : β) : rec f (a,b) = f a b := rfl

-/

section

  variable {α : Type} {β : α → Type}

  def proj_1 (p: (x : α) × β x) : α := p.1
  def proj_2 (p: (x : α) × β x) : β p.1 := p.2

  def rec {γ : Type} (f: (x: α) → β x → γ) : (x : α) × β x → γ :=
    λ (p: (x : α) × β x) => f (proj_1 p) (proj_2 p)

  theorem rec_defining_eq {γ : Type} (f: (x: α) → β x → γ) (a : α) (b : β a) : rec f ⟨a,b⟩ = f a b := rfl
