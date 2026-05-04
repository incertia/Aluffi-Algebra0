/- 1.1.2
Prove that if $\sim$ is an equivalence relation on a set $S$, then the
corresponding family $\mathscr{P}_\sim$ defined in \sref{equiv} is indeed a
partition of S: that is, its elements are nonempty, disjoint, and their union is
$S$.
-/

import Algebra0.Defs.Part

import Mathlib.Init
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

-- hepler function to take equivalence classes
def equiv_classes (_ : Equivalence (f : α → α → Prop)) : Set (Set α) :=
  {setOf (f a) | a ∈ Set.univ}

-- pull out some lemmas that we may need in future problems

-- this claims that ∀s ∈ classes, ∃a ∈ s such that the orbit of a is s
-- i.e. we may obtain a representative from any equivalence class
lemma rep (e: Equivalence f)
    : ∀s, s ∈ equiv_classes e → ∃a ∈ s, setOf (f a) = s := by
  intro s s_elem
  obtain ⟨a, a_elem, a_orbit⟩ := s_elem
  exists a
  nth_rewrite 1 [← a_orbit]
  -- we can use refine in place of constructor (exact a) (exact b)
  refine ⟨e.refl a, a_orbit⟩

-- this is defined as a function to produce a partition with the desired
-- properties by equivalence classes
def equiv_class_part (e : Equivalence (f : α → α → Prop))
    : MyPart α := by
   -- ∃p : MyPart α, p.part = equiv_classes e := by
  -- this claims that ∀a, a is in its orbit by ∼
  have a_in_class : ∀a, a ∈ setOf (f a) := e.refl

  -- this claims that any class is nonempty
  have empty_not_class : ∀s, s ∈ equiv_classes e → s ≠ ∅ := by
    intro s s_elem
    obtain ⟨a, a_elem, _⟩ := rep e s s_elem
    by_contra h
    rewrite [h, Set.mem_empty_iff_false] at a_elem
    exact a_elem

  -- this claims ∀s ∈ classes, the orbit of any element is itself
  have orbit : ∀s, s ∈ equiv_classes e → ∀x, x ∈ s → setOf (f x) = s := by
    intro s s_elem x x_elem

    -- get a, a ∈ s, setOf (f a) = s
    obtain ⟨a, a_elem, a_orbit⟩ := rep e s s_elem
    rewrite [← a_orbit] at x_elem
    let fax := x_elem.out
    let fxa := e.symm fax

    -- setOf (f x) = s ↔ setOf (f x) = setOf (f a) ↔ in one set iff in the other
    rewrite [← a_orbit]

    -- ∀ (y : α), y ∈ f x ↔ y ∈ f a
    ext y
    refine ⟨?fx, ?fa⟩
    case fx =>
      -- y ∈ f x → y ∈ f a
      intro yfx
      exact e.trans fax yfx.out
    case fa =>
      -- y ∈ f a → y ∈ f x
      intro yfa
      exact e.trans fxa yfa.out

  have disjoint :
        ∀s t
      , s ≠ t ∧ s ∈ equiv_classes e ∧ t ∈ equiv_classes e
      → s ∩ t = ∅ := by
    -- get our s, t, s ≠ t, s ∈ classes, t ∈ classes
    intro s t ⟨neq, s_elem, t_elem⟩

    -- get elements x ∈ s, y ∈ t such that s = setOf (f x) and y = setOf (f y)
    obtain ⟨x, x_elem, x_orbit⟩ := rep e s s_elem
    obtain ⟨y, y_elem, y_orbit⟩ := rep e t t_elem

    -- assume for the sake of contradiction that s ∪ t ≠ ∅
    by_contra h
    -- h : ¬s ∩ t = ∅
    -- rewrite it so that we can choose out of the intersection
    rewrite [← ne_eq, ← Set.nonempty_iff_ne_empty] at h
    obtain ⟨a, aₛ, aₜ⟩ := h

    -- aₛ : a ∈ s, aₜ : a ∈ t, and obtain results that s = setOf (f a) = t
    have orbit_a_s := orbit s s_elem a aₛ
    have orbit_a_t := orbit t t_elem a aₜ
    have st : s = t := by
      rewrite [← orbit_a_s, ← orbit_a_t]
      rfl

    -- we now have proofs that s ≠ t (by assumption) and s = t (by assuming the
    -- result was false), so something has gone wrong
    exact neq st

  have a_in_union : ∀a, a ∈ ⋃₀equiv_classes e := by
    intro a
    rewrite [Set.mem_sUnion]
    exists setOf (f a)
    unfold equiv_classes
    rewrite [Set.mem_setOf_eq]

    -- (∃ a_1 ∈ Set.univ, setOf (f a_1) = setOf (f a)) ∧ a ∈ setOf (f a)
    exact ⟨(by exists a), a_in_class a⟩

  -- ⋃₀classes = Set.univ
  have unions_into_set : ⋃₀equiv_classes e = Set.univ := by
    ext a

    unfold equiv_classes
    rewrite [Set.mem_sUnion]

    refine ⟨?l, ?r⟩
    case l =>
      -- (∃ t ∈ {x | ∃ a ∈ Set.univ, setOf (f a) = x}, a ∈ t) → a ∈ Set.univ
      -- we don't care about the hypothesis here, as we have an a already
      intro _
      exact Set.mem_univ a
    case r =>
      -- a ∈ Set.univ → ∃ t ∈ {x | ∃ a ∈ Set.univ, setOf (f a) = x}, a ∈ t
      intro _
      exists setOf (f a)
      rewrite [Set.mem_setOf_eq]

      -- (∃ a_1 ∈ Set.univ, setOf (f a_1) = setOf (f a)) ∧ a ∈ setOf (f a)
      -- the lhs here is pretty obviously satisfied by a, and the rhs is
      -- something we have proven
      exact ⟨(by exists a), a_in_class a⟩

  let partition : MyPart α := {
    part := equiv_classes e,
    no_empty := by
      -- suppose ∅ ∈ classes
      by_contra h
      -- obtain ∅ ≠ ∅
      specialize empty_not_class ∅ h
      -- lean trickery to get False
      rewrite [ne_self_iff_false] at empty_not_class
      exact empty_not_class
    disjoint := disjoint,
    full_union := unions_into_set,
  }

  exact partition
