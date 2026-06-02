/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Set.Insert

/-!
# Mirror file: `Mathlib/Data/Finset/Insert.lean`

Upstream-eligible lemmas about `Finset` pairs `{a, b}`. See `DESIGN.md`
*Mirror directory* and `notes/FRICTION.md` *Mirrored* for the project convention.
-/

@[expose] public section

namespace Finset

variable {α : Type*}

/-- The `Finset` analogue of `Set.pair_eq_pair_iff`: two unordered pairs are equal iff their
entries match in one of the two orders. Bridges to the `Set` version through `Finset.coe_inj`
and `Finset.coe_pair`. -/
lemma pair_eq_pair_iff [DecidableEq α] {a b c d : α} :
    ({a, b} : Finset α) = {c, d} ↔ a = c ∧ b = d ∨ a = d ∧ b = c := by
  rw [← Finset.coe_inj, Finset.coe_pair, Finset.coe_pair, Set.pair_eq_pair_iff]

end Finset
