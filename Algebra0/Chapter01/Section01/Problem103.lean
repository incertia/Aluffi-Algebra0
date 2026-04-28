/-
Given a partition $\mathscr{P}$ on a set $S$, show how to define a relation
$\sim$ on $S$ such that $\mathscr{P}$ is the corresponding partition.
-/

import Mathlib.Init
import Algebra0.Chapter01.Section01.Problem102

-- if you really think about it, this problem is asking for two separate things
--
-- 1. we first need to use the partition to obtain an equivalence relation
-- 2. we need to show that the partition from the equivalence relation (as
--    defined previously) is equal to the original partition


-- given an element a give us the representative set of the partition
lemma rep_set (part: MyPart α): ∀a, ∃!s, a ∈ s ∧ s ∈ part.part := by
  intro a
  let p := part.part

  have mem_union : a ∈ ⋃₀p := by
    rewrite [part.full_union]
    exact Set.mem_univ a

  obtain ⟨s, sₚ, aₛ⟩ := mem_union

  have unique_contains : ∀a s t, s ∈ p ∧ t ∈ p ∧ a ∈ s ∧ a ∈ t → s = t := by
    intro a s t ⟨sₚ, tₚ, aₛ, aₜ⟩
    by_contra neq
    rewrite [← ne_eq] at neq
    have disjoint := part.disjoint s t ⟨neq, sₚ, tₚ⟩
    have not_disjoint : s ∩ t ≠ ∅ := by
      rewrite [← Set.nonempty_iff_ne_empty]
      unfold Set.Nonempty
      use a
      rewrite [Set.mem_inter_iff]
      exact ⟨aₛ, aₜ⟩

    exact not_disjoint disjoint

  use s
  refine ⟨?exist, ?unique⟩
  case exist =>
    -- we can use dsimp to perform the beta reduction
    -- (fun s => a ∈ s ∧ s ∈ p) s -> a ∈ s ∧ s ∈ p
    exact ⟨aₛ, sₚ⟩
  case unique =>
    intro t ⟨aₜ, tₚ⟩
    apply Eq.symm
    exact unique_contains a s t ⟨sₚ, tₚ, aₛ, aₜ⟩

-- we can now use the previous lemma to define a function for the partition
-- partial application means derive_f_from_part part: α → α → Prop
def derive_f_from_part (part: MyPart α) (a: α) (b: α): Prop :=
  Classical.choose (rep_set part a) = Classical.choose (rep_set part b)

-- the first theorem is the reverse of the theorme from Problem102
theorem equiv_from_part (part: MyPart α)
    : Equivalence (derive_f_from_part part) := by

  unfold derive_f_from_part

  refine ⟨?refl, ?symm, ?trans⟩
  case refl =>
    intro _
    rfl
  case symm =>
    intro _ _ st
    rewrite [st]
    rfl
  case trans =>
    intro _ _ _ st tu
    rewrite [st, tu]
    rfl

-- the second theorem is showing that the partitions are equal
theorem part_eq_equiv_from_part (part: MyPart α)
    : part = equiv_class_part (equiv_from_part part) := by
  unfold equiv_class_part

  -- use ext to extract something to prove equality
  ext s

  -- simplify the goal a bit
  suffices s ∈ part.part ↔ s ∈ equiv_classes (equiv_from_part part) by
    exact this

  -- we now have an s: Set α and we need to prove
  -- s ∈ part.part ↔ s ∈ equiv_classes (equiv_from_part part)
  refine ⟨?part_equiv, ?equiv_part⟩
  case part_equiv =>
    -- s ∈ part.part → s ∈ equiv_classes (equiv_from_part part)
    intro s_elem
    unfold equiv_classes derive_f_from_part
    rewrite [Set.mem_setOf_eq]

    -- the goal is now
    -- ∃ a ∈ Set.univ,
    -- {b | Classical.choose (rep_set part a) = Classical.choose (rep_set part
    --    b)} = s

    -- prove this fact so we can pick an element
    have s_nonempty : s ≠ ∅ := by
      by_contra h
      have no_empty := part.no_empty
      rewrite [← h] at no_empty
      exact no_empty s_elem
    rewrite [← Set.nonempty_iff_ne_empty] at s_nonempty
    obtain ⟨a, aₛ⟩ := s_nonempty
    use a

    -- a ∈ Set.univ ∧ setOf (derive_f_from_part part a) = s
    -- we can refine the first part out of the goal
    refine ⟨Set.mem_univ a, ?_⟩

    -- we can prove that the choice is unique
    have s_eq_choose : s = Classical.choose (rep_set part a) := by
      let ⟨_, unique⟩ := Classical.choose_spec (rep_set part a)
      exact unique s ⟨aₛ, s_elem⟩

    -- we now have another set equality to show
    ext b
    refine ⟨?l, ?r⟩
    case l =>
      -- b ∈ {b | Classical.choose (rep_set part a) = Classical.choose
      --    (rep_set part b)} → b ∈ s
      intro b_elem

      -- simplify b_elem
      rewrite [Set.mem_setOf_eq] at b_elem
      -- b_elem: Classical.choose (rep_set part a) = Classical.choose (rep_set part b)
      -- simplify lhs to s
      rewrite [← s_eq_choose] at b_elem
      -- so we can replace the goal with b ∈ Classical.choose (rep_set part b)
      rewrite [b_elem]
      -- choose_spec gets us the properties of choose, and we are only
      -- interested in the first bit
      obtain ⟨⟨bₛ, _⟩, _⟩ := Classical.choose_spec (rep_set part b)
      exact bₛ
    case r =>
      -- b ∈ s → b ∈ {b | Classical.choose (rep_set part a) = Classical.choose
      --   (rep_set part b)}
      intro b_elem
      rewrite [Set.mem_setOf_eq]

      -- the goal is now
      -- Classical.choose (rep_set part a) = Classical.choose (rep_set part b)
      -- use uniqueness to show they are the same
      have s_eq_choose' : s = Classical.choose (rep_set part b) := by
        let ⟨_, unique⟩ := Classical.choose_spec (rep_set part b)
        exact unique s ⟨b_elem, s_elem⟩
      rewrite [← s_eq_choose, ← s_eq_choose']
      rfl
  case equiv_part =>
    -- s ∈ equiv_classes (equiv_from_part part) → s ∈ part.part
    intro s_elem
    unfold equiv_classes derive_f_from_part at s_elem
    obtain ⟨a, _, eq_s⟩ := s_elem

    -- obtain aliases for rep_set part a
    let (eq := t_def) t := Classical.choose (rep_set part a)
    let ⟨⟨_, t_elem⟩, _⟩ := Classical.choose_spec (rep_set part a)
    rewrite [← t_def] at eq_s t_elem

    -- The main goal is to show that s = t, so we can use t ∈ part.part to solve
    -- s ∈ part.part
    have s_eq_t : s = t := by
      rewrite [← eq_s]
      ext b
      refine ⟨?l, ?r⟩
      case l =>
        -- b ∈ {b | t = Classical.choose (rep_set part b)} → b ∈ t
        intro b_elem

        -- obtain b_elem: t = Classical.choose (rep_set part b)
        rewrite [Set.mem_setOf_eq] at b_elem
        rewrite [b_elem]

        -- obtain properties about the rep set of b, namely,
        -- b ∈ Classical.choose (rep_set part b)
        let ⟨⟨b_in_orbit, _⟩, _⟩ := Classical.choose_spec (rep_set part b)
        exact b_in_orbit
      case r =>
        -- b ∈ t → b ∈ {b | t = Classical.choose (rep_set part b)}
        intro bₜ
        rewrite [Set.mem_setOf_eq]

        -- t = Classical.choose (rep_set part b)
        -- to prove this, we borrow the uniqueness of the rep set of b
        let ⟨_, unique_u⟩ := Classical.choose_spec (rep_set part b)
        exact unique_u t ⟨bₜ, t_elem⟩

    -- the goal is to prove s ∈ part.part, but s = t and t ∈ part.part
    rewrite [s_eq_t]
    exact t_elem
