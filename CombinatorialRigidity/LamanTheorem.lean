/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Framework
import CombinatorialRigidity.Laman

/-!
# Laman's theorem

For `n ≥ 2` vertices, a simple graph is generically rigid in the plane iff it
contains a Laman spanning subgraph (a `(2, 3)`-tight subgraph on the same
vertex set):

```
G.IsGenericallyRigid 2 ↔ ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman
```

The two directions land separately for phasing reasons:

* `IsLaman.isGenericallyRigid_two` — the (⇐) direction. Henneberg induction
  on `Fintype.card V`. Phase 5 milestone 3.
* `IsGenericallyRigid.exists_isLaman_le` — the (⇒) direction. Lovász–Yemini
  rigidity-matroid duality. Phase 6.
* `isGenericallyRigid_two_iff_exists_isLaman_le` — the iff, composed from
  the two directional theorems above.

See `notes/Phase5.md` (Phase 5 plan, including the milestone breakdown for
the (⇐) direction) and ROADMAP.md §5–6.

## Project context

Phase 4 (`Framework.lean`) develops `IsGenericallyRigid` and ships
`IsGenericallyRigid.card_mul_le` for general dimension. Phase 5 specializes
that bound to `d = 2` here as `IsGenericallyRigid.card_mul_le_two`.
-/

namespace SimpleGraph

variable {V : Type*}

/-- Edge-count corollary for generic rigidity in dimension 2: every generically
rigid graph in the plane has at least `2 * #V − 3` edges. Phrased additively
per the no-`ℕ`-subtraction rule.

The `d = 2` specialization of `IsGenericallyRigid.card_mul_le`. -/
theorem IsGenericallyRigid.card_mul_le_two [Fintype V] {G : SimpleGraph V}
    (hG : G.IsGenericallyRigid 2) : 2 * Fintype.card V ≤ G.edgeSet.ncard + 3 :=
  hG.card_mul_le

/-- Every Laman graph is generically rigid in dimension 2.

Proved by Henneberg induction on `Fintype.card V`: the K₂ base case is
`top_fin_two_isGenericallyRigid 2`; the inductive step uses
`IsLaman.exists_typeI_or_typeII_reverse` plus per-move rigidity preservation
plus iso transport (`IsGenericallyRigid.iso`).

**Phase 5 milestone 3.** -/
theorem IsLaman.isGenericallyRigid_two [Fintype V] {G : SimpleGraph V}
    (h : G.IsLaman) : G.IsGenericallyRigid 2 := by
  sorry

/-- Every graph that is generically rigid in dimension 2 contains a Laman
spanning subgraph.

Proved via the equality of the rigidity matroid and the `(2, 3)`-count
matroid in dimension 2 (Lovász–Yemini): row-independence of the rigidity
matrix at a generic placement equals `(2, 3)`-sparsity, so a basis of the
rigidity matroid (size `2n − 3`) spans a Laman subgraph.

**Phase 6: Lovász–Yemini matroid duality.** -/
theorem IsGenericallyRigid.exists_isLaman_le [Fintype V] {G : SimpleGraph V}
    (h : G.IsGenericallyRigid 2) (hV : 2 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman := by
  sorry

/-- **Laman's theorem.** A simple graph on `n ≥ 2` vertices is generically rigid
in the plane iff it contains a Laman spanning subgraph.

The iff is composed from the two named directional theorems
`IsLaman.isGenericallyRigid_two` and `IsGenericallyRigid.exists_isLaman_le`;
each unproven content arm lives in its own `sorry`-blocked named theorem
(see those for which phase resolves which arm). -/
theorem isGenericallyRigid_two_iff_exists_isLaman_le [Fintype V] {G : SimpleGraph V}
    (hV : 2 ≤ Fintype.card V) :
    G.IsGenericallyRigid 2 ↔ ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman :=
  ⟨fun h => h.exists_isLaman_le hV,
   fun ⟨_, hHG, hLam⟩ => hLam.isGenericallyRigid_two.mono hHG⟩

end SimpleGraph
