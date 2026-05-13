/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import Mathlib.Data.Finset.Card

/-!
# Mirror file: `Mathlib/Data/Finset/Card.lean`

Upstream-eligible lemmas about `Finset.card`. See `DESIGN.md`
*Mirror directory* and `notes/FRICTION.md` *Mirrored* for the project convention.
-/

namespace Finset

variable {α : Type*}

/-- If a finset has cardinality at most one and contains a given element, it is the singleton
of that element.

The dual reading of `Finset.card_le_one_iff`: the `≤ 1` cardinality bound *plus* a witnessing
element collapse to a singleton equality. -/
lemma eq_singleton_of_mem_of_card_le_one {s : Finset α} {z : α}
    (hz : z ∈ s) (h : s.card ≤ 1) : s = {z} :=
  (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hz)
    (h.trans_eq (Finset.card_singleton z).symm)).symm

end Finset
