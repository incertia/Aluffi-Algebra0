/-
Let $f : A \to B$ be any function. Prove that the graph $\Gamma_f$ of $f$ is
isomorphic to $A$.
-/

import Mathlib.Data.Subtype
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.DefEqTransformations

-- use abbrev so that the type is transparent to lean
abbrev graph (f : α → β) : Type := {p // ∃a, (a, f a) = p}
theorem a_iso_graph (f : α → β) : ∃φ : α → graph f, Function.Bijective φ
:= by
  exists fun a => ⟨(a, f a), by exists a⟩
  constructor
  · unfold Function.Injective
    beta_reduce
    intro a b h

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

    -- for various reasons it's easier if we use the a from the ∃ clause
    exists a

    -- ⟨(a, f a), Exists.intro a (Eq.refl (a, f a))⟩ = ⟨x, Exists.intro a h⟩
    -- use extensionality, but only once
    ext1
    push_cast
    exact h
