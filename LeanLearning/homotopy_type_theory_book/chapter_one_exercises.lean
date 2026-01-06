/--------------------------------- Exercise 1.13
Using propositions-as-types, derive the double negation of the principle of excluded middle,
i.e. prove not (not (P or not P))
-/

/- We use two auxiliary lemmas-/

/-1. p and not p implies a contradiction-/
theorem lem1 {p: Prop} : p ∧ ¬ p -> False := λ (h : p ∧ ¬ p) => h.right h.left

/-2. One-sided De Morgan rule-/
theorem lem2 {p q : Prop}: ¬ (p ∨ q) → ¬ p ∧ ¬ q := λ (f: ¬ (p ∨ q)) => ⟨λ (hp: p) => f (Or.inl hp), λ (hq: q) => f (Or.inr hq)⟩

/- The desired statement follows by applying both lemmas-/
theorem double_negate_lem (p: Prop) : ¬ (¬ (p ∨ ¬ p)) := λ (f : ¬ (p ∨ ¬ p)) => lem1 (lem2 f)
