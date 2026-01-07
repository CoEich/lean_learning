/- De Morgan rule -/

def de_morgan {p q: Prop} : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q :=
  Iff.intro
    (
      λ (f: ¬ (p ∨ q)) =>
        have hnp: ¬ p := λ (hp : p) => f (Or.inl hp)
        have hnq: ¬ q := λ (hq : q) => f (Or.inr hq)
        show ¬ p ∧ ¬ q from ⟨hnp, hnq⟩
    )
    (
      λ (h : ¬ p ∧ ¬ q) =>
        have hnp: ¬ p := h.left
        have hnq: ¬ q := h.right
        show ¬ (p ∨ q) from λ (hpq : p ∨ q) =>
          Or.elim hpq hnp hnq
    )
