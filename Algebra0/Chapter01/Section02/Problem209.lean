/-
Show that if $A' \iso A''$ and $B' \iso B''$ and $A' \cap B' = \varnothing$ and
$A'' \cap B'' = \varnothing$, then $A' \cup B' \iso A'' \cup B''$. Conclude that
$A \amalg B$ (as described in \cref*{df:set-disjoint-union}) is well-defined up
to isomorphism.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.DefEqTransformations

theorem disjoint_unions_iso (α : Type)
    : ∀a b a' b' : Set α
    , ∀_ : a ≃ a', ∀_ : b ≃ b'
    , a ∩ b = ∅ ∧ a' ∩ b' = ∅
    → ∃_ : ↑(a ∪ b) ≃ ↑(a' ∪ b'), True
    := by
  intro a b a' b' f g ⟨h₁, h₂⟩

  let forwards (x : ↑(a ∪ b)) : ↑(a' ∪ b') :=
    match Classical.dec (x.val ∈ a) with
    | isTrue h => by
      replace x : ↑a := ⟨↑x, h⟩
      -- ugly proof term... whatever
      -- exact ⟨↑(f x), (Set.mem_union ↑(f x) a' b').mpr (Or.inl (Subtype.coe_prop (f x)))⟩
      -- just use simp because we don't care
      exact ⟨↑(f x), by simp⟩
    | isFalse h => by
      replace x : ↑b := ⟨↑x, x.prop.resolve_left h⟩
      exact ⟨↑(g x), by simp⟩

  -- construct Equiv via bijection, deferring the proof of bijection
  use Equiv.ofBijective forwards ?_

  -- declare some easy lemmas
  replace f_prop : ∀x, (h : x ∈ a) → ↑(f ⟨x, h⟩) ∈ a' := by simp
  replace g_prop : ∀x, (h : x ∈ b) → ↑(g ⟨x, h⟩) ∈ b' := by simp

  -- prove the bijection
  unfold forwards
  constructor
  -- prove injectivity
  · intro x y h
    beta_reduce at h
    split at h
    · next _ xa _ =>
      split at h
      -- x ∈ a, y ∈ a
      · rewrite [Subtype.ext_iff] at h
        push_cast at h
        rewrite [← Subtype.ext_iff] at h
        -- idk how to do this any other way
        replace h := f.injective h
        rewrite [ Subtype.ext_iff, Subtype.coe_inj
                , Subtype.mk_eq_mk, ← Subtype.ext_iff] at h
        exact h
      -- x ∈ a, y ∈ b
      · next _ nya _ =>
        have contra : _ ∧ _ :=
          ⟨(f_prop ↑x xa), (g_prop ↑y (y.prop.resolve_left nya))⟩
        rewrite [Subtype.ext_iff] at h
        rewrite [ ← h, ← Set.mem_inter_iff
                , h₂, Set.mem_empty_iff_false] at contra
        exact False.elim contra
    · next _ nxa _ =>
      split at h
      -- x ∈ b, y ∈ a
      -- once again, this is the exact same proof as before just with some sets
      -- flipped
      · next _ ya _ =>
        have contra : _ ∧ _ :=
          ⟨f_prop ↑y ya, g_prop ↑x (x.prop.resolve_left nxa)⟩
        rewrite [Subtype.ext_iff] at h
        rewrite [ ← h, ← Set.mem_inter_iff
                , h₂, Set.mem_empty_iff_false] at contra
        exact False.elim contra
      -- this is the exact proof as x ∈ a, y ∈ a but with g.injective instead of
      -- f.injective
      · rewrite [Subtype.ext_iff] at h
        push_cast at h
        rewrite [← Subtype.ext_iff] at h
        -- idk how to do this any other way
        replace h := g.injective h
        rewrite [ Subtype.ext_iff, Subtype.coe_inj
                , Subtype.mk_eq_mk, ← Subtype.ext_iff] at h
        exact h
  -- prove surjectivity
  · intro x
    -- easy lemma, x ∈ a' ∪ b' → x = f a or x = g b
    have h : (∃a : ↑a, (f a).val = x.val) ∨ (∃b : ↑b, (g b).val = x.val) := by
      by_cases xa' : ↑x ∈ a'
      · obtain ⟨a, ha⟩ := f.surjective ⟨↑x, xa'⟩
        left
        exists a
        rewrite [ha]
        rfl
      · obtain ⟨b, hb⟩ := g.surjective ⟨↑x, x.prop.resolve_left xa'⟩
        right
        exists b
        rewrite [hb]
        rfl

    -- split the cases of h
    obtain ⟨z, h⟩ | ⟨z, h⟩ := h
    -- x = f z
    · exists ⟨z, Or.inl z.prop⟩
      beta_reduce
      split
      -- z ∈ a (forwards)
      · rewrite [← Subtype.val_inj]
        exact h
      -- z ∈ b (forwards)
      · next _ h' _ =>
        have z_in_empty : ↑z ∈ a ∩ b :=
          Set.mem_inter z.mem (False.elim (Eq.mp (eq_false h') z.mem))
        rewrite [h₁, Set.mem_empty_iff_false] at z_in_empty
        exact False.elim z_in_empty
    -- x = g z
    · exists ⟨z, Or.inr z.prop⟩
      beta_reduce
      split
      -- z ∈ a (forwards)
      · next _ h' _ =>
        have z_in_empty := Set.mem_inter h' z.mem
        rewrite [h₁, Set.mem_empty_iff_false] at z_in_empty
        exact False.elim z_in_empty
      -- z ∈ b (forwards)
      · rewrite [← Subtype.val_inj]
        exact h
