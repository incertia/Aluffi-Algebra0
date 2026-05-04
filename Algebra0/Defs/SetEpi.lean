def MyEpi (f : α → β) : Prop :=
  ∀γ : Type, ∀g h : β → γ, g ∘ f = h ∘ f → g = h
