/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Finset.Card

/-!
# Mirror file: `Mathlib/Data/Finset/Card.lean`

Upstream-eligible lemmas about `Finset.card`. See `DESIGN.md`
*Mirror directory* and `notes/FRICTION.md` *Mirrored* for the project convention.
-/

@[expose] public section

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

/-- The `k`-scaled form of `Finset.card_union_add_card_inter`: multiplying both sides by a
common `Nat` factor distributes through union/intersection-pair cardinalities.

Saves three `rw` rewrites at each call site (`← Nat.mul_add` twice, then
`Finset.card_union_add_card_inter`) — useful when an `IsTightOn`-style accounting needs
to bridge `k * |s| + k * |t|` to `k * |s ∪ t| + k * |s ∩ t|`. -/
lemma mul_card_union_add_mul_card_inter [DecidableEq α] (s t : Finset α) (k : ℕ) :
    k * s.card + k * t.card = k * (s ∪ t).card + k * (s ∩ t).card := by
  rw [← Nat.mul_add, ← Nat.mul_add, Finset.card_union_add_card_inter]

/-- Three distinct elements of a finset force its cardinality to be at least three. -/
lemma three_le_card_of_three_distinct_mem {s : Finset α} {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) : 3 ≤ s.card := by
  classical
  have h3 : ({a, b, c} : Finset α).card = 3 := by
    simp [Finset.card_insert_of_notMem, hab, hac, hbc]
  have hsub : ({a, b, c} : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  exact h3 ▸ Finset.card_le_card hsub

end Finset
