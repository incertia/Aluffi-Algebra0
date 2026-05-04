/-
Formulate a notion of \textit{epimorphism}, in the style of the notion of
\textit{monomorphism} seen in \cref{def:mono}, and prove a result analogous to
\cref{inj-iff-mono}, for epimorphisms and surjections.
-/

/-
Before we rely on Mathlib's powerful category theory tools, we will first
formulate epimorphism in Lean's type-functions (set-functions) and use the
Mathlib definitions later.

def MyEpi (f : α → β) : Prop :=
  ∀γ : Type, ∀g h : β → γ, g ∘ f = h ∘ f → g = h
equivalently, f (as a function on typed values) is epi if and only if for all γ
and functions out of β → γ, you can cancel any fs on the right
-/
import Algebra0.Defs.SetEpi

import Mathlib.Tactic

/-
A function $f$ is surjective if and only if it is an epimorphism.
-/
theorem epi_iff_surj
    : ∀α β : Type, ∀f : α → β, Function.Surjective f ↔ MyEpi f := by
  intro α β f
  constructor
  -- Function.Surjective f → MyEpi f
  -- this way is the easy way
  · intro surj γ g h eq
    apply_fun flip Function.comp (Function.surjInv surj) at eq
    unfold flip at eq
    rewrite [ Function.comp_assoc
            , Function.comp_assoc
            , Function.comp_surjInv
            , Function.comp_id
            , Function.comp_id] at eq
    exact eq
  -- MyEpi f → Function.Surjective f
  -- The strategy is as follows
  -- we define two functions
  -- const_true b = true
  -- prop_fn b = if ∃a, f a = b then true else false
  -- we then show that const_true ∘ f = prop_fn ∘ f
  -- thus by f being epi, const_true = prop_fn
  -- therefore the if condition must be true
  · intro epi b
    unfold MyEpi at epi
    let const_true : β → Prop := fun _ => True
    let prop_fn b : Prop := ∃a, f a = b
    have epi_cond : const_true ∘ f = prop_fn ∘ f := by
      ext a
      rewrite [Function.comp_apply, Function.comp_apply]
      unfold const_true
      unfold prop_fn
      constructor
      · intro _
        exists a
      · intro _
        trivial

    -- utilize the epi condition to obtain eq : const_true = prop_fn
    have eq := epi Prop const_true prop_fn epi_cond
    -- use funext to turn it into a function we can apply at b
    rewrite [funext_iff] at eq

    -- now eq : ∀ (x : β), const_true x = prop_fn x
    have goal := eq b
    unfold const_true prop_fn at goal

    -- really weird case where we have h : True = goal
    rewrite [← goal]
    trivial
