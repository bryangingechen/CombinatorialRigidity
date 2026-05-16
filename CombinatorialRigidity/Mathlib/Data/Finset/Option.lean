/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import Mathlib.Data.Finset.Option

/-!
# Upstream candidate: addition-form cardinality lemma for `Finset.eraseNone`

Mathlib has `Finset.card_eraseNone_of_mem`:
```
(h : none ∈ s) : #s.eraseNone = #s - 1
```
in `ℕ`-subtraction form. This project uniformly avoids `ℕ`-subtraction (see
`ROADMAP.md` "Engineering conventions"), so consumers of the lemma have to
re-derive `s.eraseNone.card + 1 = s.card` via `Nat.sub_add_cancel` plus a
positivity witness — three extra tokens at every call site.

The Lean namespace is the upstream one (`Finset`), so promotion to mathlib is
a copy-paste alongside `Finset.card_eraseNone_of_mem`. See
`DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Data/Finset/Option.lean`)

* `Finset.card_eraseNone_add_one_of_mem` — `none ∈ s → #s.eraseNone + 1 = #s`.
-/

namespace Finset

variable {α : Type*}

/-- Addition-form companion to `Finset.card_eraseNone_of_mem`: when `none ∈ s`,
the some-elements of `s` plus the `none` itself recover `#s`. Phrased without
`ℕ`-subtraction so that `omega` and `grind` can chain it directly. -/
theorem card_eraseNone_add_one_of_mem {s : Finset (Option α)} (h : none ∈ s) :
    s.eraseNone.card + 1 = s.card := by
  rw [card_eraseNone_of_mem h, Nat.sub_add_cancel (Finset.card_pos.mpr ⟨_, h⟩)]

end Finset
