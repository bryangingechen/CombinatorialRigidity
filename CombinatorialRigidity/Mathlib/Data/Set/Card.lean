/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import Mathlib.Data.Set.Card

/-!
# Upstream candidates: small `Set.ncard` lemmas

The Lean namespace is the upstream one (`Set`), so promotion to mathlib is a
copy-paste. See `Archive/CombinatorialRigidity/DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Data/Set/Card.lean`)

* `Set.ncard_pair_le` — `({a, b} : Set α).ncard ≤ 2`. Unconditional companion
  to `Set.ncard_pair` (which gives `= 2` under `a ≠ b`); collapses the
  `ncard_insert_le` + `ncard_singleton` boilerplate when bounding the
  cardinality of a literal pair without first ruling out collisions.
* `Set.ncard_triple_le` — `({a, b, c} : Set α).ncard ≤ 3`. Same pattern,
  one level deeper.
* `Set.ncard_eq_card_coe` — `s.ncard = Fintype.card s` under `[Fintype s]`.
  Bridges `Set.ncard` to the `Fintype.card`-based dimension lemmas
  (`Module.finrank_pi`, `LinearMap.toMatrix`) without the
  `Set.ncard_eq_toFinset_card'` / `Set.toFinset_card` two-step rewrite.
-/

namespace Set

variable {α : Type*}

/-- An unconditional bound for the cardinality of a literal pair: it is at most `2`
regardless of whether `a = b`. The companion `Set.ncard_pair` gives the exact `= 2`
under `a ≠ b`. -/
theorem ncard_pair_le (a b : α) : ({a, b} : Set α).ncard ≤ 2 :=
  (ncard_insert_le _ _).trans (by rw [ncard_singleton])

/-- An unconditional bound for the cardinality of a literal triple: it is at most `3`
regardless of any equalities among `a, b, c`. -/
theorem ncard_triple_le (a b c : α) : ({a, b, c} : Set α).ncard ≤ 3 :=
  (ncard_insert_le _ _).trans (Nat.add_le_add_right (ncard_pair_le _ _) _)

/-- A direct bridge between `Set.ncard` and `Fintype.card`: `s.ncard = Fintype.card ↥s`
under `[Fintype s]`. The `Set.ncard_eq_toFinset_card'` (`s.ncard = s.toFinset.card`) +
`Set.toFinset_card` (`s.toFinset.card = Fintype.card s`) two-step rewrite collapses to
this one lemma. -/
theorem ncard_eq_card_coe (s : Set α) [Fintype s] : s.ncard = Fintype.card s := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]

end Set
