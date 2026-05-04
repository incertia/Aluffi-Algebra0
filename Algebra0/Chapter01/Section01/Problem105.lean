/-
Give an example of a relation that is reflexive and symmetric but not
transitive. What happens if you attempt to use this relation to define a
partition on the set?
-/

import Mathlib.Algebra.Order.AbsoluteValue.Basic

-- we claim that the following relation is reflexive and symmetric but not
-- transitive
def nearby (x: ℤ) (y: ℤ) : Prop := |x - y| ≤ 1

theorem not_equiv_nearby
    : (∀x, nearby x x)
    ∧ (∀x y, nearby x y → nearby y x)
    ∧ (∃ x y z, ¬(nearby x y ∧ nearby y z → nearby x z)) := by

  unfold nearby
  refine ⟨?refl, ?symm, ?trans⟩
  case refl =>
    intro _
    rewrite [sub_self, abs_zero]
    exact zero_le_one
  case symm =>
    intro x y h
    rewrite [abs_sub_comm] at h
    exact h
  case trans =>
    exists 0, 1, 2
