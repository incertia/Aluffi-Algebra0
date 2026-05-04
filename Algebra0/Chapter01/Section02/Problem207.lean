/-
Let $f : A \to B$ be any function. Prove that the graph $\Gamma_f$ of $f$ is
isomorphic to $A$.
-/

import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic

def graph (f : α → β) : Type := {p // ∃a, (a, f a) = p}
theorem a_iso_graph (f : α → β) : ∃φ : α → graph f, Function.Bijective φ := by
  exists fun a => ⟨(a, f a), by exists a⟩
  constructor
  · unfold Function.Injective
    beta_reduce
    intro a b h

    -- this unfold graph is VERY IMPORTANT
    -- lean cannot see that graph f is a subtype unless you do this unfold,
    -- which changes nothing in the infoview so you think it is not actually
    -- doing anything
    unfold graph at h
    -- rewrite rules for (a, b).1 = a are hidden away in Lean.Omega for some
    -- reason
    rewrite [ Subtype.mk_eq_mk
            , Prod.ext_iff
            , Lean.Omega.Prod.fst_mk
            , Lean.Omega.Prod.fst_mk
            , Lean.Omega.Prod.snd_mk
            , Lean.Omega.Prod.snd_mk] at h
    exact h.left
  · unfold Function.Surjective
    beta_reduce
    intro ⟨x, ⟨a, h⟩⟩
    exists a

    -- we cannot use ext so we directly apply Subtype.ext
    apply Subtype.ext
    -- use push_cast to simplify the cast expressions
    push_cast
    exact h
