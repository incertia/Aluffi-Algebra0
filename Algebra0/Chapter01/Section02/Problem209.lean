/-
Show that if $A' \iso A''$ and $B' \iso B''$ and $A' \cap B' = \varnothing$ and
$A'' \cap B'' = \varnothing$, then $A' \cup B' \iso A'' \cup B''$. Conclude that
$A \amalg B$ (as described in \cref*{df:set-disjoint-union}) is well-defined up
to isomorphism.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.DefEqTransformations

theorem disjoint_unions_iso (α : Type)
    : ∀a b a' b' : Set α
    , ∀_ : a ≃ a', ∀_ : b ≃ b'
    , a ∩ b = ∅ ∧ a' ∩ b' = ∅
    → ∃_ : ↑(a ∪ b) ≃ ↑(a' ∪ b'), True
    := by
  intro a b a' b' f g ⟨h₁, h₂⟩

  -- these will be nice to use inside forwards
  have f_prop : ∀x : ↑a, ↑(f x) ∈ a' ∪ b' := by
    intro
    left
    apply Subtype.coe_prop
  have g_prop : ∀x : ↑b, ↑(g x) ∈ a' ∪ b' := by
    intro
    right
    apply Subtype.coe_prop

  let forwards (x : ↑(a ∪ b)) : ↑(a' ∪ b') :=
    match Classical.dec (x.val ∈ a) with
    | isTrue h => by
      replace x : ↑a := ⟨↑x, h⟩
      exact ⟨↑(f x), f_prop x⟩
    | isFalse h => by
      have x_in_ab := x.prop
      rewrite [Set.mem_union] at x_in_ab
      let x_in_b := x_in_ab.resolve_left h
      replace x : ↑b := ⟨↑x, x_in_b⟩
      exact ⟨↑(g x), g_prop x⟩

  -- construct Equiv via bijection, deferring the proof of bijection
  use Equiv.ofBijective forwards ?_

  -- declare some similar prop lemmas
  replace f_prop : ∀x, (h : x ∈ a) → ↑(f ⟨x, h⟩) ∈ a' := by
    intro _ _
    apply Subtype.coe_prop
  replace g_prop : ∀x, (h : x ∈ b) → ↑(g ⟨x, h⟩) ∈ b' := by
    intro _ _
    apply Subtype.coe_prop

  -- prove the bijection
  unfold forwards
  constructor
  -- prove injectivity
  · intro x y h
    beta_reduce at h
    split at h
    · rename ↑x ∈ a => xa
      split at h
      -- x ∈ a, y ∈ a
      · rewrite [Subtype.ext_iff] at h
        push_cast at h
        rewrite [← Subtype.ext_iff] at h
        -- idk how to do this any other way
        replace h := f.injective h
        rewrite [Subtype.ext_iff] at h
        push_cast at h
        rewrite [Subtype.coe_inj] at h
        exact h
      -- x ∈ a, y ∈ b
      · exfalso
        rename ¬↑y ∈ a => nya
        have fx_in_a := f_prop ↑x xa
        have gy_in_b := g_prop ↑y (y.prop.resolve_left nya)
        rewrite [Subtype.ext_iff] at h
        push_cast at h
        have fx_in_b := gy_in_b
        rewrite [← h] at fx_in_b
        have fx_in_empty := Set.mem_inter fx_in_a fx_in_b
        rewrite [h₂, Set.mem_empty_iff_false] at fx_in_empty
        exact fx_in_empty
    · rename ¬↑x ∈ a => nxa
      split at h
      -- x ∈ b, y ∈ a
      -- once again, this is the exact same proof as before just with some sets
      -- flipped
      · exfalso
        rename ↑y ∈ a => ya
        have gx_in_b := g_prop ↑x (x.prop.resolve_left nxa)
        have fy_in_b := f_prop ↑y ya
        rewrite [Subtype.ext_iff] at h
        push_cast at h
        have gx_in_a := fy_in_b
        rewrite [← h] at gx_in_a
        have fx_in_empty := Set.mem_inter gx_in_a gx_in_b
        rewrite [h₂, Set.mem_empty_iff_false] at fx_in_empty
        exact fx_in_empty
      -- this is the exact proof as x ∈ a, y ∈ a but with g.injective instead of
      -- f.injective
      · rewrite [Subtype.ext_iff] at h
        push_cast at h
        rewrite [← Subtype.ext_iff] at h
        -- idk how to do this any other way
        replace h := g.injective h
        rewrite [Subtype.ext_iff] at h
        push_cast at h
        rewrite [Subtype.coe_inj] at h
        exact h
  -- prove surjectivity
  · intro x

    -- easy lemma, x ∈ a' ∪ b' → x = f a or x = g b
    have h : (∃a : ↑a, (f a).val = x.val) ∨ (∃b : ↑b, (g b).val = x.val) := by
      by_cases xa' : ↑x ∈ a'
      · obtain ⟨a, ha⟩ := f.surjective ⟨↑x, xa'⟩
        left
        exists a
        apply_fun (fun x => x.val) at ha
        exact ha
      · have xb' := x.prop.resolve_left xa'
        obtain ⟨b, hb⟩ := g.surjective ⟨↑x, xb'⟩
        right
        exists b
        apply_fun (fun x => x.val) at hb
        exact hb

    -- split the cases of h
    obtain ⟨z, h⟩ | ⟨z, h⟩ := h
    -- x = f z
    · have z_in_union : ↑z ∈ a ∪ b := by
        rewrite [Set.mem_union]
        left
        exact z.prop
      exists ⟨z, z_in_union⟩
      beta_reduce
      split
      -- z ∈ a (forwards)
      · apply_fun Subtype.val using Subtype.val_injective
        exact h
      -- z ∈ b (forwards)
      · rename ¬↑z ∈ a => h'
        exfalso
        have z_in_a := z.mem
        have z_in_b := z_in_union.resolve_left h'
        have z_in_empty := Set.mem_inter z_in_a z_in_b
        rewrite [h₁, Set.mem_empty_iff_false] at z_in_empty
        exact z_in_empty
    -- x = g z
    · have z_in_union : ↑z ∈ a ∪ b := by
        rewrite [Set.mem_union]
        right
        exact z.prop
      exists ⟨z, z_in_union⟩
      beta_reduce
      split
      -- z ∈ a (forwards)
      · rename ↑z ∈ a => h'
        exfalso
        have z_in_a := h'
        have z_in_b := z.mem
        have z_in_empty := Set.mem_inter z_in_a z_in_b
        rewrite [h₁, Set.mem_empty_iff_false] at z_in_empty
        exact z_in_empty
      -- z ∈ b (forwards)
      · apply_fun Subtype.val using Subtype.val_injective
        exact h
