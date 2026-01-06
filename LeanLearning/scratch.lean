
/-A hypothesis implies negation of its negation-/
theorem double_negate_pf_by_contr (p: Prop) : p -> ¬ (¬ p) := λ (h : p) (f : ¬ p) => f h

#check double_negate_pf_by_contr

/-A contradiction implies anything-/
theorem contr_implies_anything (p: Prop) : False -> p := False.elim

#check contr_implies_anything

/-A hypothesis and its negation imply a contradiction-/
theorem p_and_not_p_implies_contr (p: Prop) : p ∧ ¬ p -> False := λ (h : p ∧ ¬ p) => h.right h.left

#check p_and_not_p_implies_contr
