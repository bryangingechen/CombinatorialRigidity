/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Set.Card.Arithmetic

/-!
# Upstream candidate: disjoint-family cardinality fusion over a `Fintype` index

`Mathlib.Data.Set.Card.Arithmetic` proves `Set.ncard_iUnion_of_finite` (the `Finite ι` version,
right-hand side a `finsum`) and `Set.ncard_iUnion_le_of_fintype` (the unconditional inequality for
`Fintype ι`, right-hand side a `Finset.sum`), but not the equality member of the `Fintype ι` /
`Finset.sum` family. This project's disjoint-forest-packing counting arguments repeatedly chain
`Set.ncard_iUnion_of_finite` with `finsum_eq_sum_of_fintype` to get from a `finsum` back to a
`Finset.sum` over a concrete `Fin n` index — `Set.ncard_iUnion_of_fintype` below fuses the two into
one lemma.

Mirror path: `Mathlib/Data/Set/Card/Arithmetic.lean`. Promotion to mathlib is a copy-paste into the
upstream file, directly below `Set.ncard_iUnion_of_finite`.
-/

@[expose] public section

namespace Set

variable {α ι : Type*}

/-- **Disjoint-family cardinality fusion (`Fintype` index).** For a `Fintype`-indexed family `s` of
pairwise disjoint finite sets, the cardinality of the union is the `Finset.sum` of the individual
cardinalities. Companion to `Set.ncard_iUnion_of_finite` (the `Finite ι` version, `finsum` on the
right) and to `Set.ncard_iUnion_le_of_fintype` (the unconditional inequality); this is the missing
equality member of that family, collapsing the `Set.ncard_iUnion_of_finite` +
`finsum_eq_sum_of_fintype` two-step rewrite. -/
theorem ncard_iUnion_of_fintype [Fintype ι] {s : ι → Set α} (hs : ∀ i, (s i).Finite)
    (h : Pairwise (Function.onFun Disjoint s)) : (⋃ i, s i).ncard = ∑ i, (s i).ncard := by
  rw [ncard_iUnion_of_finite hs h, finsum_eq_sum_of_fintype]

end Set
