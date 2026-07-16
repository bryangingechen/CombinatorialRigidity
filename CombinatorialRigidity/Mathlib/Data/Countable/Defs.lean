/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.Fintype.EquivFin

/-!
# Upstream candidate: a countable type embeds injectively into any infinite type

The Lean namespace is the upstream one (`Countable`), so promotion to mathlib is
a copy-paste. See `DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Data/Countable/Defs.lean`)

* `Countable.exists_injective_of_infinite` — `∃ f : α → β, Function.Injective f`
  for `[Countable α] [Infinite β]`. Composes the natural-number embedding
  `Countable.exists_injective_nat` with `Infinite.natEmbedding β : ℕ ↪ β`. Used by
  the Phase-21b Case-I realization producer to supply the injective panel
  parameter map `param : α → K` (`PanelHingeFramework.ofParam`, `K` an infinite
  field) from finiteness of the body set alone, discharging the
  `Function.Injective param` obligation — the named replacement (Phase 33
  PROSPECT G1) for the hidden-`[CharZero K]` trap of composing
  `Countable.exists_injective_nat` with the numeral cast `ℕ → K` directly (that
  cast is injective only in characteristic zero; `Infinite.natEmbedding` has no
  such hypothesis).
-/

@[expose] public section

namespace Countable

variable (α : Sort*) [Countable α]

/-- A countable type embeds injectively into any infinite type `β`: post-compose the
natural-number embedding `Countable.exists_injective_nat` with `Infinite.natEmbedding β`. -/
theorem exists_injective_of_infinite (β : Type*) [Infinite β] :
    ∃ f : α → β, Function.Injective f := by
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat α
  exact ⟨(Infinite.natEmbedding β) ∘ g, (Infinite.natEmbedding β).injective.comp hg⟩

end Countable
