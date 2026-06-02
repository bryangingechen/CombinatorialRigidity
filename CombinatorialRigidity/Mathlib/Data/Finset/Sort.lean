/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Finset.Sort

/-!
# Mirror file: `Mathlib/Data/Finset/Sort.lean`

Upstream-eligible lemmas about `Finset.orderEmbOfFin`. See `DESIGN.md`
*Mirror directory* and `notes/FRICTION.md` *Mirrored* for the project convention.
-/

@[expose] public section

namespace Finset

variable {α : Type*}

/-- The increasing enumeration of `Finset.univ : Finset (Fin n)` is the identity.

`Finset.univ.orderEmbOfFin h` is the unique `StrictMono` map `Fin n → Fin n` landing in
`univ`, and `id` is such a map; `orderEmbOfFin_unique` identifies the two. The cardinality
hypothesis `h : (univ : Finset (Fin n)).card = n` is `Finset.card_fin n`. -/
@[simp]
lemma univ_orderEmbOfFin {n : ℕ} (h : (Finset.univ : Finset (Fin n)).card = n) :
    ⇑(Finset.univ.orderEmbOfFin h) = (id : Fin n → Fin n) :=
  (Finset.orderEmbOfFin_unique h (fun _ => Finset.mem_univ _) strictMono_id).symm

end Finset
