
/-A hypothesis implies negation of its negation-/
theorem double_negate_pf_by_contr (p: Prop) : p -> ¬ (¬ p) := λ (h : p) (f : ¬ p) => f h

#check double_negate_pf_by_contr

/-A contradiction implies anything-/
theorem contr_implies_anything (p: Prop) : False -> p := False.elim

#check contr_implies_anything

/-A hypothesis and its negation imply a contradiction-/
theorem p_and_not_p_implies_contr (p: Prop) : p ∧ ¬ p -> False := λ (h : p ∧ ¬ p) => h.right h.left

#check p_and_not_p_implies_contr

universe u v

variable (α : Type) (β : α → Type)

#check (x : α) → β x
#check (x : α) × β x

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

#check f
