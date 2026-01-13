set_option linter.unusedVariables false

/- De Morgan rule -/

 theorem de_morgan {p q: Prop} : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q :=
  -- we need to provide two proofs as arguments to 'Iff.intro'
  Iff.intro
    (
      λ (f: ¬ (p ∨ q)) ↦
        -- we are gonna construct terms for not p, not q respecively and apply the and constructor

        -- use 'have' for local definitions, here we get witnesses of not p and not q from f
        have hnp: ¬ p := λ (hp : p) ↦
          have hpl: p ∨ q := Or.inl hp
          -- use 'show' for syntactic sugar, the expression 'f hpl' would suffice here
          show False from f hpl
        -- same reasoning for q
        have hnq: ¬ q := λ (hq : q) ↦
          have hqr: p ∨ q := Or.inr hq
          show False from f hqr

        show ¬ p ∧ ¬ q from ⟨hnp, hnq⟩
    )
    (
      λ (h : ¬ p ∧ ¬ q) ↦
        have hnp: ¬ p := h.left
        have hnq: ¬ q := h.right
        -- we show the conclusion here by applying the case-analysis, i.e the eliminator for coproducts
        show ¬ (p ∨ q) from λ (hpq : p ∨ q) ↦
          Or.elim hpq hnp hnq
    )



/- Other exercises -/

-- commutativity of ∧ and ∨

-- because the statements are symmetric it's shorter to just apply these lemmas in both directions
theorem lem_prop_1 {s t : Prop} : s ∧ t → t ∧ s :=
  λ (h: s ∧ t) ↦
    have hs : s := h.left
    have ht : t := h.right
    show t ∧ s from ⟨ht, hs⟩

theorem property_1 {p q: Prop} : p ∧ q ↔ q ∧ p := Iff.intro lem_prop_1 lem_prop_1

theorem lem_prop_2 {s t : Prop} : s ∨ t → t ∨ s :=
  λ (h : s ∨ t) ↦
    -- We use 'suffices' here to reach the goal conditioned on a hypothesis that we have to show below
    suffices impls : (s → t ∨ s) ∧ (t → t ∨ s) from Or.elim h impls.left impls.right
    show (s → t ∨ s) ∧ (t → t ∨ s) from
      have left_impl: s → t ∨ s := λ (hs: s) ↦ Or.inr hs
      have right_impl: t → t ∨ s := λ (ht: t) ↦ Or.inl ht
      ⟨left_impl, right_impl⟩

theorem property_2 {p q: Prop} : p ∨ q ↔ q ∨ p := Iff.intro lem_prop_2 lem_prop_2

-- associativity of ∧ and ∨

-- again we formulate one direction of the equivalence as its own lemma
theorem lem_prop_3 {p q r: Prop} : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
  λ (h: (p ∧ q) ∧ r) ↦
        have hp: p := h.left.left
        have hq: q := h.left.right
        have hr: r := h.right
        show p ∧ (q ∧ r) from ⟨hp, hq, hr⟩

theorem property_3 {p q r: Prop} : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    lem_prop_3

    λ h: p ∧ (q ∧ r) ↦

      /- Solution 1: copy paste lem_prop_3 more or less
      have hp: p := h.left
      have hq: q := h.right.left
      have hr: r := h.right.right
      -- note: ⟨hp, hq, hr⟩ does not work here
      show (p ∧ q) ∧ r from ⟨⟨ hp, hq⟩ , hr⟩ -/

      -- Solution 2: Be more cool and use lemmas and theorems we already have :-)
      have hswap1 : (q ∧ r) ∧ p := Iff.mp property_1 h
      have assoc1: q ∧ (r ∧ p) := lem_prop_3 hswap1
      have hswap2: (r ∧ p) ∧ q := Iff.mp property_1 assoc1
      have assoc2: r ∧ (p ∧ q) := lem_prop_3 hswap2
      show (p ∧ q) ∧ r from Iff.mp property_1 assoc2


-- same strategy as before
theorem lem_prop_4 {p q r: Prop} : (p ∨ q) ∨ r → p ∨ (q ∨ r) :=
  λ h: (p ∨ q) ∨ r ↦
        have impl1 : (p ∨ q) → p ∨ (q ∨ r) := λ hpq: p ∨ q ↦
          have implp: p → p ∨ (q ∨ r) := λ hp : p ↦ Or.inl hp
          have implq: q → p ∨ (q ∨ r) := λ hq: q ↦ Or.inr (Or.inl hq)
          show p ∨ (q ∨ r) from Or.elim hpq implp implq
        have impl2: r → p ∨ (q ∨ r) := λ hr: r ↦ Or.inr (Or.inr hr)
        show p ∨ (q ∨ r) from Or.elim h impl1 impl2


theorem property_4 {p q r: Prop} : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    lem_prop_4

    λ h: p ∨ (q ∨ r) ↦
    /-
    Thought: We apply the exact same trick here as in property 3. This screams for abstraction.
    TODO for the future: Formulate an even more abstract proof for "commutative" operators on propositions
    (or more generally, types)
    -/
    have hswap1 : (q ∨ r) ∨ p := Iff.mp property_2 h
      have assoc1: q ∨ (r ∨ p) := lem_prop_4 hswap1
      have hswap2: (r ∨ p) ∨ q := Iff.mp property_2 assoc1
      have assoc2: r ∨ (p ∨ q) := lem_prop_4 hswap2
      show (p ∨ q) ∨ r from Iff.mp property_2 assoc2

-- distributivity
theorem property_5 {p q r: Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro

  (
    λ h: p ∧ (q ∨ r) ↦
      -- auxiliary implication which "moves the p to the right" so we can apply Or.elim
      have f : (q ∨ r) → (p → (p ∧ q) ∨ (p ∧ r)) := λ hqr : (q ∨ r) ↦
        have impl1: q → (p → (p ∧ q) ∨ (p ∧ r)) := λ (hq: q) (hp: p) ↦ Or.inl ⟨hp, hq⟩
        have impl2: r → (p → (p ∧ q) ∨ (p ∧ r)) := λ (hr: r) (hp: p) ↦ Or.inr ⟨hp, hr⟩
        show (p → (p ∧ q) ∨ (p ∧ r)) from Or.elim hqr impl1 impl2
      have hp : p := h.left
      have hqr : (q ∨ r) := h.right
      show (p ∧ q) ∨ (p ∧ r) from f hqr hp
  )

  (
    λ h: (p ∧ q) ∨ (p ∧ r) ↦
      have impl1: (p ∧ q) → p ∧ (q ∨ r) := λ hpq : p ∧ q ↦ ⟨hpq.left, Or.inl hpq.right⟩
      have impl2: (p ∧ r) → p ∧ (q ∨ r) := λ hpr : p ∧ r ↦ ⟨hpr.left, Or.inr hpr.right⟩
      show p ∧ (q ∨ r) from Or.elim h impl1 impl2
  )


theorem property_6 {p q r: Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
theorem property_7 {p q r: Prop} : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
      (λ (h: p → (q → r)) (hpq: p ∧ q) ↦ h hpq.left hpq.right )

      (λ (h: p ∧ q → r) (hp: p) (hq: q) ↦ h ⟨hp, hq⟩)

theorem property_8 {p q r: Prop} : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (
      λ h: (p ∨ q) → r ↦
        have impl1: p → r := λ hp : p ↦ h (Or.inl hp)
        have impl2: q → r := λ hq : q ↦ h (Or.inr hq)
        show (p → r) ∧ (q → r) from ⟨impl1, impl2⟩
    )

    λ (h: (p → r) ∧ (q → r)) (hpq: p ∨ q) ↦ Or.elim hpq h.left h.right

theorem property_9 {p q: Prop} : ¬(p ∨ q) ↔ ¬p ∧ ¬q := de_morgan

theorem lem_prop_10 {p q : Prop} : ¬ p → ¬(p ∧ q) :=
  λ (hnp: ¬ p) (hpq: (p ∧ q)) ↦ hnp hpq.left

theorem property_10 {p q: Prop} : ¬p ∨ ¬q → ¬(p ∧ q) :=
  λ (h: ¬p ∨ ¬q) ↦
    have impl1 : ¬ p → ¬(p ∧ q) := lem_prop_10
    -- we get the second case by lem_3 and swapping (property_1)
    have impl2: ¬q → ¬(p ∧ q) := λ (hnq: ¬q) ↦
      have hnqp : ¬(q ∧ p) := lem_prop_10 hnq
      show ¬(p ∧ q) from λ (hpq: p ∧ q) ↦ hnqp (Iff.mp property_1 hpq)
    show ¬(p ∧ q) from Or.elim h impl1 impl2

theorem property_11 {p: Prop} : ¬(p ∧ ¬p) :=
  λ (h: p ∧ ¬p) ↦ h.right h.left

theorem property_12 {p q: Prop} : p ∧ ¬q → ¬(p → q) :=
  λ (h: p ∧ ¬ q) (impl: p → q) ↦
    have hq: q := impl h.left
    show False from False.elim (h.right hq)


theorem property_13 {p q : Prop}: ¬p → (p → q) := λ (hnp: ¬ p) (hp: p) ↦ False.elim (hnp hp)

theorem property_14 {p q: Prop} : (¬p ∨ q) → (p → q) :=
  λ (h : ¬p ∨ q) ↦
    suffices impls: (¬ p → (p → q)) ∧ (q → (p → q)) from Or.elim h impls.left impls.right
      have inp: ¬ p → (p → q) := property_13
      have iq: q → (p → q) := λ (hq: q) (hp: p) ↦ hq
      show (¬ p → (p → q)) ∧ (q → (p → q)) from
        ⟨inp, iq⟩


theorem property_15 {p: Prop} : p ∨ False ↔ p :=
  Iff.intro
    (
      λ (h: p ∨ False) ↦
      have c1: p → p := id
      have c2: False → p := False.elim
      show p from Or.elim h c1 c2
    )

    λ (h: p) ↦ show p ∨ False from Or.inl h

theorem property_16 {p: Prop} : p ∧ False ↔ False :=
  Iff.intro (λ (h: p ∧ False) ↦ False.elim h.right) False.elim

theorem property_17 {p: Prop} : ¬ (p ↔ ¬ p) :=
  λ h : p ↔ ¬ p ↦
    have limpl: p → ¬ p := h.mp
    have rimpl: ¬ p → p := h.mpr
    have hnp : ¬ p := λ hp: p ↦ limpl hp hp
    have hp: p := rimpl hnp
    -- absurd is just the theorem p → ¬p → False
    show False from absurd hp hnp

theorem property_18 {p q: Prop} : (p → q) → (¬q → ¬p) :=
  λ (ipq: p → q) (hnq: ¬ q) (hp: p) ↦ hnq (ipq hp)
