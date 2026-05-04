/-
Prove that isomorphism (\cref*{iso-def}) is an equivalence relation on any set of
sets.
-/

import Algebra0.Defs.SetIso
import Algebra0.Chapter01.Section02.Problem203

import Mathlib.Logic.Function.Basic

-- we simplify the theorem to just reflexive, symmetric, and transitive on types
-- it should be clear that from these properties one can form an equivalence on
-- a set of sets
theorem setiso_equiv
    : (∀α, SetIso α α)
    ∧ (∀α β, SetIso α β → SetIso β α)
    ∧ (∀α β γ, SetIso α β ∧ SetIso β γ → SetIso α γ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro α
    use id
    exact Function.bijective_id
  · intro α β iso
    obtain ⟨f, bij⟩ := iso
    use Function.surjInv bij.right
    exact inv_bijection_bijection bij
  · intro α β γ ⟨⟨f, bij1⟩, ⟨g, bij2⟩⟩
    use g ∘ f
    exact comp_bijection_bijection bij1 bij2
