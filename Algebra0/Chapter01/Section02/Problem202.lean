/-
Prove statement \cref*{surj-rinverse} in \cref{inverse-iff}. You may assume that
given a family of disjoint nonempty subsets of a set, there is a way to choose
one element in each member of the family.

· $f$ has a right inverse if and only if $f$ is surjective.
-/

theorem rinv_iff_surj (f : α → β)
    : (∃g, Function.RightInverse g f) ↔ Function.Surjective f := by
  --refine ⟨?l, ?r⟩
  constructor
  · intro h
    obtain ⟨g, hg⟩ := h
    unfold Function.Surjective
    intro b
    exists g b
    --unfold Function.RightInverse Function.LeftInverse at hg
    exact hg b
  · intro h
    unfold Function.Surjective at h
    let g (b : β) : α := Classical.choose (h b)
    exists g
    --unfold Function.RightInverse Function.LeftInverse
    intro b
    exact Classical.choose_spec (h b)
