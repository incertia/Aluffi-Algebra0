/-
Prove that the inverse of a bijection is a bijection and that the composition of
two bijections is a bijection.
-/

import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

-- inverse of bijection is bijection
theorem inv_bijection_bijection
  (bij : Function.Bijective (f : α → b))
    : Function.Bijective (Function.surjInv bij.right) := by
  constructor
  -- Function.Injective (Function.surjInv bij.right)
  · unfold Function.Injective
    intro b₁ b₂ h
    -- this invocation of apply_fun does not produce an injective goal because
    -- if we already know a = b, then f a = f b
    apply_fun f at h
    rewrite [Function.surjInv_eq bij.right, Function.surjInv_eq bij.right] at h
    exact h
  -- Function.Surjective (Function.surjInv bij.right)
  · unfold Function.Surjective
    intro a
    exists f a

    -- Function.surjInv bij.right (f a) = a
    -- if the goal is to prove b = a, it suffices to prove f b = f a as long as
    -- f is injective
    apply_fun f using bij.left
    rewrite [Function.surjInv_eq bij.right]
    rfl

-- composition of bijections is bijection
theorem comp_bijection_bijection
  (bij_f : Function.Bijective (f : α → β))
  (bij_g : Function.Bijective (g : β → γ))
    : Function.Bijective (g ∘ f) := by
  constructor
  · unfold Function.Injective
    intro a₁ a₂ h
    exact bij_f.left (bij_g.left h)
  · unfold Function.Surjective
    intro c
    exists Function.surjInv bij_f.right (Function.surjInv bij_g.right c)

    -- (g ∘ f) (Function.surjInv bij_f.right (Function.surjInv bij_g.right c)) = c
    show g (f (Function.surjInv bij_f.right (Function.surjInv bij_g.right c))) = c
    rewrite [Function.surjInv_eq bij_f.right, Function.surjInv_eq bij_g.right]
    rfl
