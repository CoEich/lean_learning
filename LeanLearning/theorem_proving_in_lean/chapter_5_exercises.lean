---- Exercise 1: Redo as many exercises as you can from previous chapters with tactics

example (p q : Prop) : ¬p → (p → q) := by
  -- use intro tactic instead of λ hnp hp
  -- lean infers the correct types for hnp and hp automatically here
  intro hnp hp
  -- the . helps lean "focus" on one subgoal at a time for a more readable info view
  . apply absurd
    . exact hp
    . exact hnp

example (p: Prop) : ¬ (p ↔ ¬ p) := by
  intro h
  -- we mix tactics with some term-style proofs
  have : ¬ p := by
    intro hp
    . apply h.mp
      . exact hp
      . exact hp
  have : p := by
    . apply h.mpr
      . exact this
  . apply absurd
    . assumption
    . assumption
    -- using assumption here looks for suitable assumptions in the context, similar (but shorter) to
    -- . exact ‹p›
    -- . exact ‹¬ p›
