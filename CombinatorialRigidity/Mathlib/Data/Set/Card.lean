/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import Mathlib.Data.Set.Card

/-!
# Upstream candidates: unconditional `Set.ncard` bounds for pair / triple sets

Mathlib has `Set.ncard_pair` (`{a, b}.ncard = 2` under `a ≠ b`) but no companion
unconditional `≤` bound. Whenever a proof bounds the cardinality of a literal
pair / triple of edges without first ruling out collisions, the calc chain expands
to `ncard_insert_le` + `ncard_singleton` boilerplate (sometimes nested for a
3-element set). The lemmas below collapse those chains to one application.

The Lean namespace is the upstream one (`Set`), so promotion to mathlib is a
copy-paste alongside `Set.ncard_pair`. See
`Archive/CombinatorialRigidity/DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Data/Set/Card.lean`)

* `Set.ncard_pair_le` — `({a, b} : Set α).ncard ≤ 2`.
* `Set.ncard_triple_le` — `({a, b, c} : Set α).ncard ≤ 3`.
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

end Set
