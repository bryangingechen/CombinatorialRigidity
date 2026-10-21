/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Basic.Countable.Defs
public import Mathlib.Data.Fintype.EquivFin

/-!
# Upstream candidate: a countable type embeds injectively into any infinite type

The Lean namespace is the upstream one (`Countable`), so promotion to mathlib is
a copy-paste. See `DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Basic/Countable/Defs.lean`)

* `Countable.exists_injective_of_infinite` — `∃ f : α → β, Function.Injective f`
  for `[Countable α] [Infinite β]`. Composes the natural-number embedding
  `Countable.exists_injective_nat` with `Infinite.natEmbedding β : ℕ ↪ β`.
  Composing with the cast `ℕ → K` into a field instead would need characteristic
  zero, as that cast is injective only there; `Infinite.natEmbedding` needs only
  `Infinite β`. The combinatorial-rigidity project's algebraic induction
  (`Molecular/AlgebraicInduction/`) uses it to choose an injective map from the
  finite set of bodies to an infinite field `K`, at whose moment-curve normals the
  general-position polynomial is nonzero (`exists_generalPosition_polynomial`).
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
