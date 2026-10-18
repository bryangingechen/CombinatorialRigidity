/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.PebbleGame.Exec
public meta import CombinatorialRigidity.PebbleGame.Exec

/-!
# Executable pebble game — worked examples

This file runs the `Decidable` instances for `SimpleGraph.IsSparse`,
`SimpleGraph.IsTight`, and `SimpleGraph.IsLaman` (registered in
`CombinatorialRigidity.PebbleGame.Exec`) on a small fixed set of `Fin n`
graphs, end-to-end. Each `#eval (decide …)` line runs the instance,
whose body calls `runPebbleGameExec`, in Lean's interpreter, and the
comment above it records the expected answer. No bound on the running
time is proved; `lake exe pebble-game` (`Main.lean`) runs the same
function compiled, on the same graphs as `examples/*.txt`.

## Worked examples

* `Examples.k4MinusE` — `K₄ \ {s(2, 3)}` on `Fin 4`. 4 vertices, 5
  edges, Laman (`2 · 4 − 3 = 5`). The Phase 3 / `HennebergReverse.lean`
  worked example `top_fin_four_minus_edge_isLaman`, surfaced through
  decidability; verifies the minimal non-trivial accept path through
  the pebble game.
* `Examples.moserSpindle` — Moser spindle. 7 vertices, 11 edges, Laman
  (`2 · 7 − 3 = 11`); verifies the accept path on a graph large enough
  for the DFS to fire non-trivially.
* `Examples.k4` — `K₄` on `Fin 4`. 4 vertices, 6 edges; not Laman, not
  even `(2, 3)`-sparse (`6 > 2 · 4 − 3 = 5`). The pebble game rejects
  at the full-vertex subset on the sparsity step.
* `Examples.path5` — path on `Fin 5`. 5 vertices, 4 edges; `(2, 3)`-sparse
  but not `(2, 3)`-tight (`4 ≠ 2 · 5 − 3 = 7`), hence not Laman. The
  pebble game accepts, and the global edge-count equation of
  `IsTight` rejects.

See `blueprint/src/chapter/executable.tex` §*Worked examples* for the
prose narrative; the `#eval` outputs below are the operational
counterpart.

## Implementation notes

The four `SimpleGraph (Fin n)` graphs are defined via
`SimpleGraph.fromEdgeSet` on an explicit `Finset (Sym2 (Fin n))` (or
`(⊤ : SimpleGraph (Fin 4)).deleteEdges …` for K₄ minus one edge,
matching `HennebergReverse.lean`'s construction). Each carries an
explicit `DecidableRel _.Adj` instance bridging through
`fromEdgeSet_adj` / `deleteEdges_adj` to a `Decidable (… ∧ _ ≠ _)`
form; this is what unlocks the `instDecidableIsLaman` /
`instDecidableIsSparse` typeclass synthesis at each `#eval` callsite.

The `public meta import` on `PebbleGame.Exec` makes the Phase 10
`Decidable` instances visible to `#eval`'s meta-time instance
synthesis (the alternative would be to drop this file from the
`module` system entirely, but the rest of the project is uniformly
module-converted per `PERFORMANCE.md`).
-/

public section

namespace CombinatorialRigidity.Examples

open SimpleGraph

/-! ### Example 1 — `K₄ \ {s(2, 3)}` is Laman -/

/-- The complete graph on `Fin 4` minus one edge — the Phase 3 worked
example formalised in `SimpleGraph.top_fin_four_minus_edge_isLaman`,
surfaced here through Phase 10's `Decidable` instance. -/
@[expose] def k4MinusE : SimpleGraph (Fin 4) :=
  (⊤ : SimpleGraph (Fin 4)).deleteEdges {s(2, 3)}

instance : DecidableRel k4MinusE.Adj := fun a b =>
  decidable_of_iff
    ((⊤ : SimpleGraph (Fin 4)).Adj a b ∧ s(a, b) ∉ ({s(2, 3)} : Set (Sym2 (Fin 4))))
    SimpleGraph.deleteEdges_adj.symm

-- Expected: `5`.
#eval k4MinusE.edgeFinset.card

-- Expected: `true` — `K₄ \ e` is Laman.
#eval decide k4MinusE.IsLaman

/-! ### Example 2 — the Moser spindle is Laman -/

/-- Edge set of the Moser spindle on `Fin 7`: two triangles sharing the
apex vertex `0`, with two "rim" vertices `5` (adjacent to `1, 2`) and
`6` (adjacent to `3, 4`), and a bridging edge `5–6`. 11 edges
total. -/
def moserEdges : Finset (Sym2 (Fin 7)) :=
  {s(0, 1), s(0, 2), s(1, 2),
   s(0, 3), s(0, 4), s(3, 4),
   s(1, 5), s(2, 5),
   s(3, 6), s(4, 6),
   s(5, 6)}

/-- The Moser spindle on `Fin 7`. -/
@[expose] def moserSpindle : SimpleGraph (Fin 7) :=
  SimpleGraph.fromEdgeSet (moserEdges : Set (Sym2 (Fin 7)))

instance : DecidableRel moserSpindle.Adj := fun a b =>
  decidable_of_iff (s(a, b) ∈ moserEdges ∧ a ≠ b)
    (SimpleGraph.fromEdgeSet_adj _).symm

-- Expected: `11`.
#eval moserSpindle.edgeFinset.card

-- Expected: `true` — the Moser spindle is Laman.
#eval decide moserSpindle.IsLaman

/-! ### Example 3 — `K₄` is not Laman -/

/-- The complete graph on `Fin 4`. 6 edges, globally over-constrained:
`6 > 2 · 4 − 3 = 5`. -/
def k4 : SimpleGraph (Fin 4) := (⊤ : SimpleGraph (Fin 4))

instance : DecidableRel k4.Adj :=
  inferInstanceAs (DecidableRel (⊤ : SimpleGraph (Fin 4)).Adj)

-- Expected: `6`.
#eval k4.edgeFinset.card

-- Expected: `false` — `K₄` is not `(2, 3)`-sparse (6 edges, but every
-- spanning subset must have ≤ `2 · |V'| − 3` edges, violated at
-- `V' = univ`).
#eval decide (k4.IsSparse 2 3)

-- Expected: `false` — `K₄` is therefore not Laman.
#eval decide k4.IsLaman

/-! ### Example 4 — the 5-vertex path is sparse but not tight -/

/-- Edge set of the 5-vertex path `0 — 1 — 2 — 3 — 4`. 4 edges. -/
def path5Edges : Finset (Sym2 (Fin 5)) :=
  {s(0, 1), s(1, 2), s(2, 3), s(3, 4)}

/-- The 5-vertex path on `Fin 5`. -/
@[expose] def path5 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet (path5Edges : Set (Sym2 (Fin 5)))

instance : DecidableRel path5.Adj := fun a b =>
  decidable_of_iff (s(a, b) ∈ path5Edges ∧ a ≠ b)
    (SimpleGraph.fromEdgeSet_adj _).symm

-- Expected: `4`.
#eval path5.edgeFinset.card

-- Expected: `true` — `path5` is `(2, 3)`-sparse (every subset has ≤
-- `2 · |V'| − 3` edges; in fact the path is acyclic).
#eval decide (path5.IsSparse 2 3)

-- Expected: `false` — `path5` is not `(2, 3)`-tight: `|E| = 4`, but
-- `2 · 5 − 3 = 7`.
#eval decide (path5.IsTight 2 3)

-- Expected: `false` — `path5` is therefore not Laman.
#eval decide path5.IsLaman

end CombinatorialRigidity.Examples
