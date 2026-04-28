/-
Define a relation $\sim$ on the set $\RR$ of real numbers by setting $a \sim b
\iff b - a \in \ZZ$. Prove that this is an equivalence relatoin, and find a
`compelling' description for $R / {\sim}$. Do the same for the relation
$\approx$ on the plane $\RR \times \RR$ define by declaring $(a_1, a_2) \approx
(b_1, b_2) \iff b_1 - a_1 \in \ZZ \text{ and } b_2 - a_2 \in \ZZ$.
-/

import Mathlib.Data.Real.Basic

-- these are the relations converted to lean
def r1 (a: ℝ) (b: ℝ) : Prop := ∃n : ℤ, b - a = ↑n
def r2 (a : ℝ × ℝ) (b : ℝ × ℝ) : Prop := r1 a.1 b.1 ∧ r1 a.2 b.2

-- we first show r1 is a relation
theorem r1_equiv : Equivalence r1 := by
  unfold r1
  refine ⟨?refl, ?symm, ?trans⟩
  case refl =>
    intro x
    use 0
    rewrite [sub_self, Int.cast_zero]
    rfl
  case symm =>
    intro x y h
    obtain ⟨n, h⟩ := h
    use -n
    rewrite [Int.cast_neg, ← h]
    norm_num
  case trans =>
    intro x y z h1 h2
    obtain ⟨n₁, h1⟩ := h1
    obtain ⟨n₂, h2⟩ := h2
    use n₁ + n₂
    rewrite [Int.cast_add]
    rewrite [← h1, ← h2]
    norm_num

-- we then show r2 is a relation
theorem r2_equiv : Equivalence r2 := by
  unfold r2
  refine ⟨?refl, ?symm, ?trans⟩
  case refl =>
    intro x
    exact ⟨r1_equiv.refl x.1, r1_equiv.refl x.2⟩
  case symm =>
    intro x y ⟨hx, hy⟩
    exact ⟨r1_equiv.symm hx, r1_equiv.symm hy⟩
  case trans =>
    intro x y z h1 h2
    exact ⟨r1_equiv.trans h1.1 h2.1, r1_equiv.trans h1.2 h2.2⟩

-- words cannot really explain but r1 defines a circle and r2 defines a donut
