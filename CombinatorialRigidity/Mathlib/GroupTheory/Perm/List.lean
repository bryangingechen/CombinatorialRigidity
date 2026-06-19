/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.GroupTheory.Perm.List

/-!
# Upstream candidate: `List.formPerm` as a product of adjacent transpositions

For any list `l`, the cyclic permutation `l.formPerm` factors as the product of
the adjacent-element transpositions `Equiv.swap l[0] l[1] * Equiv.swap l[1] l[2] * ⋯`,
i.e. the product over `zipWith Equiv.swap l l.tail` (the adjacent pairs `(l[s], l[s+1])`).

This is the iterated form of the already-mathlib `List.formPerm_cons_cons`
(`(x :: y :: l).formPerm = Equiv.swap x y * (y :: l).formPerm`): unfolding that
recursion all the way down spells `formPerm` as the left-to-right product of the
window swaps. The combinatorial-rigidity project uses it to identify the
`shiftPerm` index-shift cycle (KT 2011 eq. (6.54), the `i`-cycle
`v₁ → ⋯ → vᵢ → v₁`) with the iterated single-transposition transport its
cycle-W9a row-span fold composes (one adjacent swap per moved degree-2 body).

The lemma is upstream-eligible: a pure fact about `List.formPerm` with no
project-specific concepts.

Mirror path: `Mathlib/GroupTheory/Perm/List.lean`.
-/

@[expose] public section

namespace List

variable {α : Type*} [DecidableEq α]

/-- `l.formPerm` is the product of the adjacent-element transpositions along `l`:
`Equiv.swap l[0] l[1] * Equiv.swap l[1] l[2] * ⋯`, i.e. the product over
`zipWith Equiv.swap l l.tail`. The iterated form of `List.formPerm_cons_cons`. -/
theorem formPerm_eq_prod_zipWith_swap_tail (l : List α) :
    l.formPerm = (l.zipWith (fun a b => Equiv.swap a b) l.tail).prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      rw [List.formPerm_cons_cons, ih, List.tail_cons]
      rfl

end List
