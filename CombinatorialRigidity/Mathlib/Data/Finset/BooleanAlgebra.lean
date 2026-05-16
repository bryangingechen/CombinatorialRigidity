/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Finset.BooleanAlgebra

/-!
# Upstream candidate: coercion of the complement of a singleton finset

Mathlib's `Finset.coe_compl` and `Finset.coe_singleton` give the two ingredient
rewrites; this file packages their composition as a single `simp`/`norm_cast`
lemma.

Companion `card_compl_singleton` (which needs `Fintype α`) lives in
`Mathlib/Data/Fintype/Card.lean` (mirrored at
`CombinatorialRigidity/Mathlib/Data/Fintype/Card.lean`).

The Lean namespace is the upstream one (`Finset`), not the project's, so
promotion is a copy-paste alongside `Finset.coe_compl`. See
`DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Data/Finset/BooleanAlgebra.lean`)

* `Finset.coe_compl_singleton` — `(({a} : Finset α)ᶜ : Set α) = ({a} : Set α)ᶜ`.
-/

@[expose] public section

namespace Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

@[norm_cast]
theorem coe_compl_singleton (a : α) :
    ((({a} : Finset α)ᶜ : Finset α) : Set α) = ({a} : Set α)ᶜ := by
  rw [coe_compl, coe_singleton]

end Finset
