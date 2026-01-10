/- De Morgan rule -/

 theorem de_morgan {p q: Prop} : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q :=
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

-- because the statements are symmetric it's shorter to just apply these lemmas in both directions
theorem lem_1 {s t : Prop} : s ∧ t → t ∧ s :=
  λ (h: s ∧ t) =>
    have hs : s := h.left
    have ht : t := h.right
    show t ∧ s from ⟨ht, hs⟩

theorem lem_2 {s t : Prop} : s ∨ t → t ∨ s :=
  λ (h : s ∨ t) =>
    -- We use 'suffices' here to reach the goal conditioned on a hypothesis that we have to show below
    suffices impls : (s → t ∨ s) ∧ (t → t ∨ s) from Or.elim h impls.left impls.right
    show (s → t ∨ s) ∧ (t → t ∨ s) from
      have left_impl: s → t ∨ s := λ (hs: s) => Or.inr hs
      have right_impl: t → t ∨ s := λ (ht: t) => Or.inl ht
      ⟨left_impl, right_impl⟩

example : p ∧ q ↔ q ∧ p := Iff.intro lem_1 lem_1

example : p ∨ q ↔ q ∨ p := Iff.intro lem_2 lem_2

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (
      λ (h: (p ∧ q) ∧ r) =>
        have hp: p := h.left.left
        have hq: q := h.left.right
        have hr: r := h.right
        show p ∧ (q ∧ r) from ⟨hp, hq, hr⟩
    )

    (
      λ (h: p ∧ (q ∧ r)) =>
        have hp: p := h.left
        have hq: q := h.right.left
        have hr: r := h.right.right
        -- note: ⟨hp, hq, hr⟩ does not work here
        show (p ∧ q) ∧ r from ⟨⟨ hp, hq⟩ , hr⟩
    )

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := de_morgan

theorem lem_3 {p q : Prop} : ¬ p → ¬(p ∧ q) :=
  λ (hnp: ¬ p) (hpq: (p ∧ q)) => hnp hpq.left

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  λ (h: ¬p ∨ ¬q) =>
    have impl1 : ¬ p → ¬(p ∧ q) := lem_3
    -- we get the second case by lem_3 and swapping (lem_1)
    have impl2: ¬q → ¬(p ∧ q) := λ (hnq: ¬q) =>
      have hnqp : ¬(q ∧ p) := lem_3 hnq
      show ¬(p ∧ q) from λ (hpq: p ∧ q) => hnqp (lem_1 hpq)
    show ¬(p ∧ q) from Or.elim h impl1 impl2

example : ¬(p ∧ ¬p) :=
  λ (h: p ∧ ¬p) => h.right h.left

example : p ∧ ¬q → ¬(p → q) :=
  λ (h: p ∧ ¬ q) (impl: p → q) =>
    have hq: q := impl h.left
    show False from False.elim (h.right hq)


theorem lem_4 {p q : Prop}: ¬p → (p → q) := λ (hnp: ¬ p) (hp: p) => False.elim (hnp hp)

example : (¬p ∨ q) → (p → q) :=
  λ (h : ¬p ∨ q) =>
    suffices impls: (¬ p → (p → q)) ∧ (q → (p → q)) from Or.elim h impls.left impls.right
      have inp: ¬ p → (p → q) := lem_4
      have iq: q → (p → q) := λ (hq: q) (hp: p) => hq
      show (¬ p → (p → q)) ∧ (q → (p → q)) from
        ⟨inp, iq⟩


example : p ∨ False ↔ p :=
  Iff.intro
    (
      λ (h: p ∨ False) =>
      have c1: p → p := id
      have c2: False → p := False.elim
      show p from Or.elim h c1 c2
    )

    λ (h: p) => show p ∨ False from Or.inl h

example : p ∧ False ↔ False :=
  Iff.intro (λ (h: p ∧ False) => False.elim h.right) False.elim

example : (p → q) → (¬q → ¬p) :=
  λ (ipq: p → q) (hnq: ¬ q) (hp: p) => hnq (ipq hp)
