/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Sym.Sym2
public import CombinatorialRigidity.Search.DFS
public import CombinatorialRigidity.Sparsity

/-!
# The `(k, ℓ)`-pebble game

Phase 9. Formalizes the basic `(k, ℓ)`-pebble game of Lee–Streinu 2008
(generalising the original `(2, 3)` algorithm of Jacobs–Hendrickson 1997)
and its correctness theorem in the matroidal regime `ℓ < 2k` matching
Phase 7. The target shape is a structured `Sum`: on success,
`runPebbleGame k ℓ G` returns a partial orientation `D` certifying
`(k, ℓ)`-sparsity of `G`; on failure, it returns a vertex subset `V'`
together with a proof that `|edgesIn G V'| > k * V'.card - ℓ`,
witnessing non-sparsity. The matroidal-independence corollary against
Phase 7's `countMatroid` follows directly from
`countMatroid_indep_iff`.

This file is currently a **scaffold**. The forward-mode dep-graph in
`blueprint/src/chapter/pebble-game.tex` is the authoritative lemma
index; subsequent code commits flip one leaf-most red node green at a
time. The leaf-most red node to attack first is L-S Lemma 10
(the four pebble-game invariants) traced through `SimpleGraph` for
both ranges `ℓ < k` and `k ≤ ℓ < 2k`.

## Style island

This file (together with `CombinatorialRigidity/Search/DFS.lean`) is
a deliberate **style island**: it takes `[Fintype V] [DecidableEq V]`
directly in algorithm signatures and uses `Finset.card` end-to-end,
departing from the project's default `[Finite V]` + inline
`Fintype.ofFinite V` bridge idiom. The algorithm body builds
`Finset (V × V)`-backed partial orientations and iterates over
out-neighbourhoods; the state machine cannot run at `[Finite V]`
strength (no `Finset.univ`, no enumeration), and the certificate-form
correctness statement requires `#eval` and `decide` to fire end-to-end.
The math layer / exec layer split (state stays `Finset`-backed, while
enumeration goes through `List V` to dodge `Finset.toList`'s
non-computability) is established in `Search/DFS.lean`; the
`PartialOrientation V` representation here follows the same pattern.
See `../DESIGN.md` *Pebble-game style island* for the rationale and
forward-compatibility note.

## References

* A. Lee, I. Streinu, *Pebble game algorithms and sparse graphs*,
  Discrete Math. **308** (2008) 1425–1437.
* D.J. Jacobs, B. Hendrickson, *An algorithm for two-dimensional
  rigidity percolation: the pebble game*, J. Comput. Phys. **137**
  (1997) 346–365 — the original `(2, 3)` version.

See `ROADMAP.md` §9, `notes/Phase9.md` (architectural choices, deferred
questions, hand-off), and the blueprint chapter
`blueprint/src/chapter/pebble-game.tex` (authoritative dep-graph and
lemma index).
-/

@[expose] public section

namespace CombinatorialRigidity.PebbleGame

end CombinatorialRigidity.PebbleGame
