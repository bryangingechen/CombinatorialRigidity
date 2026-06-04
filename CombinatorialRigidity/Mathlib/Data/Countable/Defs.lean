/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.Real.Basic

/-!
# Upstream candidate: a countable type embeds injectively into `ℝ`

The Lean namespace is the upstream one (`Countable`), so promotion to mathlib is
a copy-paste. See `DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Data/Countable/Defs.lean`)

* `Countable.exists_injective_real` — `∃ f : α → ℝ, Function.Injective f` for any
  `[Countable α]`. The real-valued companion to `Countable.exists_injective_nat`,
  obtained by post-composing with the injective cast `ℕ → ℝ`. Used by the
  Phase-21b Case-I realization producer to supply the injective panel parameter
  map `param : α → ℝ` (`PanelHingeFramework.ofParam`) from finiteness of the body
  set alone, discharging the `Function.Injective param` obligation.
-/

@[expose] public section

namespace Countable

variable (α : Sort*) [Countable α]

/-- A countable type embeds injectively into `ℝ`: post-compose the integer
embedding `Countable.exists_injective_nat` with the injective cast `ℕ → ℝ`. -/
theorem exists_injective_real : ∃ f : α → ℝ, Function.Injective f := by
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat α
  exact ⟨fun a => (g a : ℝ), Nat.cast_injective.comp hg⟩

end Countable
