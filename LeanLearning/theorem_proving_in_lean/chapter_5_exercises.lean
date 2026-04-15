---- Exercise 1: Redo as many exercises as you can from previous chapters with tactics

example (p q : Prop) : ¬p → (p → q) := by
  -- use intro tactic instead of λ hnp hp
  -- lean infers the correct types for hnp and hp automatically here
  intro hnp hp
  -- the . helps lean "focus" on one subgoal at a time for a more readable info view
  apply absurd
  . exact hp
  . exact hnp

example (p: Prop) : ¬ (p ↔ ¬ p) := by
  intro h
  -- we mix tactics with some term-style proofs
  have : ¬ p := by
    intro hp
    apply h.mp
    . exact hp
    . exact hp
  have : p := by
    apply h.mpr
    . exact this
  apply absurd
    -- using assumption here looks for suitable assumptions in the context, similar to anonymous notation ‹p›
  . assumption
  . assumption

    -- if we use a tactic multiple times, one can also use the "repeat" tactic
    -- repeat assumption

-- try intro tactic together with a match expression
example (p q: Prop) : (¬p ∨ q) → (p → q) := by
  intro
  | Or.inl hnp =>
    intro hp
    apply absurd
    repeat assumption
  | Or.inr hq =>
    intro
    assumption

-- similar when using "cases" tactic
example (p q: Prop) : (¬p ∨ q) → (p → q) := by
  intro h
  cases h with
  | inl =>
    intro
    apply absurd
    repeat assumption
  | inr =>
    intro
    assumption

-- we try to push it here with anonymous notation, this leads to having to use the @ operator
example (p q: Prop) : (¬p ∨ q) → (p → q) := by
  intros
  cases ‹¬p ∨ q›
  . apply @absurd p _
    repeat assumption
  . assumption

-- even shorter with the contradiction tactic
example (p q: Prop) : (¬p ∨ q) → (p → q) := by
  intros
  cases ‹¬p ∨ q›
  . contradiction
  . assumption

open Classical

example (α : Type) (p : α → Prop):
(∀ x : α, p x) ↔ ¬ (∃ x : α, ¬ p x) := by
apply Iff.intro

. intro h₁ ⟨x, h₂⟩
  have : p x := by apply h₁ x
  contradiction

. intro h x
  have : p x ∨ ¬ p x := by apply em (p x)
  cases this
  . assumption
  . have : ∃ x : α, ¬ p x := by exists x
    contradiction
