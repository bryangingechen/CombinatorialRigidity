/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Fintype.Card

/-!
# Upstream candidate: cardinality of the complement of a singleton finset

Companion of `Finset.coe_compl_singleton` in
`CombinatorialRigidity/Mathlib/Data/Finset/BooleanAlgebra.lean`. The
`card` form requires `Fintype α`, so it lands next to `Finset.card_compl`
in `Mathlib/Data/Fintype/Card.lean`.

The Lean namespace is the upstream one (`Finset`), not the project's, so
promotion is a copy-paste alongside `Finset.card_compl`. See
`DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Data/Fintype/Card.lean`)

* `Finset.card_compl_singleton` — `(({a} : Finset α)ᶜ).card = Fintype.card α - 1`.
-/

@[expose] public section

namespace Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

@[simp]
theorem card_compl_singleton (a : α) :
    (({a} : Finset α)ᶜ).card = Fintype.card α - 1 := by
  rw [card_compl, card_singleton]

end Finset
