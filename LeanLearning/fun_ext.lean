/- We prove here that function extensionality follows
  from the existence of quotients - a result that was only
  sketched in the last chapter.
-/

universe u v

variable {α : Sort u} {β : α → Sort v}

def ext_eq (f₁ f₂ : (x : α) → β x) : Prop := ∀ x : α, f₁ x = f₂ x

def fun_appl_quot (g : Quot (@ext_eq α β)) (x : α) : β x :=
  let appl_x : ((y : α) → β y) → β x := λ f ↦ f x   -- TODO: 'have' does not work here, but 'let' does. Don't really understand why.
  have hquot : ∀ f₁ f₂ : (y : α) → β y, ext_eq f₁ f₂ →  appl_x f₁ = appl_x f₂ :=
    λ (f₁ f₂ : (y : α) → β y) (h : ext_eq f₁ f₂) ↦
      calc
        appl_x f₁ = f₁ x := rfl
        _    = f₂ x := h x
        _    = appl_x f₂ := rfl

  Quot.lift appl_x hquot g

theorem fun_ext (f₁ f₂ : (x : α) → β x) : ext_eq f₁ f₂ → f₁ = f₂ :=
  λ h : ext_eq f₁ f₂ ↦
    have heq : Quot.mk ext_eq f₁ = Quot.mk ext_eq f₂ := Quot.sound h
    calc
      f₁ = fun_appl_quot (Quot.mk ext_eq f₁) := rfl
      _  = fun_appl_quot (Quot.mk ext_eq f₂) := congrArg fun_appl_quot heq
      _  = f₂ := rfl
