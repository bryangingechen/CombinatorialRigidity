/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Framework

/-!
# The rigidity matroid

Linear-algebra infrastructure used by the `(⇒)` direction of Laman's theorem
(`IsGenericallyRigid.exists_isLaman_le` in `LamanTheorem.lean`). The eventual
home for the rigidity-matroid side of Lovász–Yemini's identification of the
rigidity matroid in dimension 2 with the `(2, 3)`-count matroid.

## Project context

Phase 4 (`Framework.lean`) deliberately kept the abstract rigidity matroid
out of the core framework API; Phase 6 stands this file up alongside it.
Per `notes/Phase6.md` *Architectural choices*, we stay matroid-agnostic in
the proof body and defer the `Mathlib.Combinatorics.Matroid` packaging:
closing `exists_isLaman_le` needs only the row-independence relation and
two linear-algebra facts (a rank lower bound at a generically rigid
placement, and `(2, 3)`-sparsity-from-row-independence). Building the
abstract `Matroid` instance is reusable infrastructure but not on the
critical path.

See `ROADMAP.md` §6, `notes/Phase6.md`, and the `(⇒)` subsection of
`blueprint/src/chapter/laman-theorem.tex`.
-/

namespace SimpleGraph

variable {V : Type*}

/-- **Rank lower bound at a generically rigid placement, dim 2.** If `G` is
generically rigid in dimension 2, some framework `p` realises the bound
`2 * #V ≤ rank (G.RigidityMap p) + 3`.

This is the rank half of `IsGenericallyRigid.card_mul_le_two`: the same
rank-nullity argument that gives `2 * #V ≤ #E + 3`, stopping one step
earlier (before replacing `rank` by `#E` via `rigidityMap_finrank_range_le`).
The Phase 6 `(⇒)` direction uses this lemma to extract a row-independent
edge basis of size `2 * #V - 3` from the rigidity matrix's rows. -/
theorem rigidityMap_finrank_range_ge_of_isGenericallyRigid_two [Fintype V]
    {G : SimpleGraph V} (hG : G.IsGenericallyRigid 2) :
    ∃ p : Framework V 2,
      2 * Fintype.card V ≤ Module.finrank ℝ (LinearMap.range (G.RigidityMap p)) + 3 := by
  obtain ⟨p, h_ker⟩ := hG
  refine ⟨p, ?_⟩
  have h_ker : Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) ≤ 3 := h_ker
  have h_total : Module.finrank ℝ (Framework V 2) = 2 * Fintype.card V := by
    rw [Framework.finrank, mul_comm]
  have h_rn := LinearMap.finrank_range_add_finrank_ker (G.RigidityMap p)
  omega

end SimpleGraph
