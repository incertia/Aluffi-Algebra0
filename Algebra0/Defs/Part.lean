import Mathlib.Order.SetNotation

-- we define what it means to be a partition
-- Part is already defined somewhere in Mathlib, hence MyPart
-- in order to specify a subset, one should use {a : α // p a}
@[ext]
structure MyPart α where
  part: Set (Set (α))
  -- the empty set cannot be part of a partition
  no_empty : ∅ ∉ part
  -- unequal partitions must be disjoint
  disjoint : ∀s t, s ≠ t ∧ s ∈ part ∧ t ∈ part → s ∩ t = ∅
  -- the union must be the entire set
  full_union : ⋃₀part = Set.univ
