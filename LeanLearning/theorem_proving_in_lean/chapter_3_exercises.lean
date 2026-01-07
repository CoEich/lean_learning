/- De Morgan rule -/

def de_morgan {p q: Prop} : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q :=
  -- we need to provide two proofs as arguments to 'Iff.intro'
  Iff.intro
    (
      λ (f: ¬ (p ∨ q)) =>
        -- we are gonna construct terms for not p, not q respecively and apply the and constructor

        -- use 'have' for local definitions, here we get witnesses of not p and not q from f
        have hnp: ¬ p := λ (hp : p) =>
          have hpl: p ∨ q := Or.inl hp
          -- use 'show' for syntactic sugar, the expression 'f hpl' would suffice here
          show False from f hpl
        -- same reasoning for q
        have hnq: ¬ q := λ (hq : q) =>
          have hqr: p ∨ q := Or.inr hq
          show False from f hqr

        show ¬ p ∧ ¬ q from ⟨hnp, hnq⟩
    )
    (
      λ (h : ¬ p ∧ ¬ q) =>
        have hnp: ¬ p := h.left
        have hnq: ¬ q := h.right
        -- we show the conclusion here by applying the case-analysis, i.e the eliminator for coproducts
        show ¬ (p ∨ q) from λ (hpq : p ∨ q) =>
          Or.elim hpq hnp hnq
    )



/- Other exercises -/

variable (p q r : Prop)

-- commutativity of ∧ and ∨
def lem_1 {s t : Prop} : s ∧ t → t ∧ s :=
  λ (h: s ∧ t) =>
        have hs : s := h.left
        have ht : t := h.right
        show t ∧ s from ⟨ht, hs⟩

example : p ∧ q ↔ q ∧ p := Iff.intro lem_1 lem_1

def lem_2 {s t : Prop} : s ∨ t → t ∨ s :=
  λ (h : s ∨ t) =>
    -- We use 'suffices' here to reach the goal conditioned on a hypothesis that we have to show below
    suffices impls : (s → t ∨ s) ∧ (t → t ∨ s) from Or.elim h impls.left impls.right
    show (s → t ∨ s) ∧ (t → t ∨ s) from
      have left_impl: s → t ∨ s := λ (hs: s) => Or.inr hs
      have right_impl: t → t ∨ s := λ (ht: t) => Or.inl ht
      ⟨left_impl, right_impl⟩

example : p ∨ q ↔ q ∨ p := Iff.intro lem_2 lem_2

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := de_morgan
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
