/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Search.DFS
import CombinatorialRigidity.PebbleGame.Examples

/-!
# The pebble game's search, timed; what `decide` does with the pebble game's instances

Run with `lake lean scripts/DFSTiming.lean` from the repository root (never `lake env lean`, which
drops the lakefile's options). It is not part of the `CombinatorialRigidity` library and
`lake build` never compiles it. It has two parts.

**The timing.** `CombinatorialRigidity.Search.reachableFinding` searches with one marked set,
threaded through the sibling calls (RECONCILE round 3's task 17,
`notes/Reconcile-lean-cleanup.md`). Before that, every recursive call
from `v` got the same `insert v visited`, so the search marked only the vertices of the current
walk, and when no vertex satisfies `P` it followed every simple walk from its start.
`perWalkFindingAux` below is that search, its body as it stood at `671366e4`
(`Search/DFS.lean`'s `reachableFindingAux`), renamed. `diamondSucc n` is a chain of `n` diamonds:
`3n + 1` vertices, `4n` arcs, and `2 ^ n` walks from `0` to `3n`, all of them simple since every
arc goes up. The `#eval` runs both searches from `0` with `P` false everywhere, at
`n = 8, 10, …, 18`, and prints the graph's counts, each search's answer and time, and the number
of vertices the new search marks: `3n + 1`, as every vertex is reachable from `0`. The counts,
the answers and the marked set do not move; the times do.

**The `decide` facts.** Each is a tactic that fails the file if it stops holding. Neither
`decide` nor `decide +kernel` proves `Examples.k4MinusE.IsLaman`; `decide +kernel` proves
`(⊤ : SimpleGraph (Fin 2)).IsLaman`; `native_decide` proves `k4MinusE.IsLaman` and
`¬ Examples.k4.IsLaman`. The reasons are the ledger's (`notes/Prose-findings.md`, `F-047` and
`F-276`; RECONCILE round 3's task 16 probed them): the elaborator does not unfold the search or
`tryAddEdgeWith`, which are defined by well-founded recursion, and the kernel does not unfold
core's `List.mergeSort`, which `Finset.sort` uses to build the pebble game's lists.

**The importer kind matters, and this file is deliberately *not* a `module`,** as
`scripts/BlueprintDeps.lean` is not: a `module` file that imports a `module` sees only the bodies
it exports, and task 16 measured `decide +kernel` failing on `(⊤ : SimpleGraph (Fin 2)).IsLaman`
from a `module` file.
-/

namespace CombinatorialRigidity.DFSTiming

open CombinatorialRigidity.Search

universe u
variable {V : Type u}

/-! ## The search before task 17 -/

/-- `Search/DFS.lean`'s `reachableFindingAux` at `671366e4`, renamed: the per-walk search. Every
recursive call from `v` gets the same `insert v visited`, so `visited` holds only the vertices of
the current walk. -/
def perWalkFindingAux [Fintype V] [DecidableEq V]
    (succ : V → List V) (P : V → Bool)
    (visited : Finset V) (v : V) :
    Option (Σ w : V, DirectedWalk (fun a b => b ∈ succ a) v w) :=
  if _hv : v ∈ visited then
    none
  else if P v = true then
    some ⟨v, .nil v⟩
  else
    (succ v).attach.findSome? fun ⟨u, hu⟩ =>
      (perWalkFindingAux succ P (insert v visited) u).map fun ⟨w, p⟩ =>
        ⟨w, .cons hu p⟩
  termination_by (Finset.univ \ visited).card
  decreasing_by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_of_subset (Finset.sdiff_subset_sdiff
      (Finset.Subset.refl _) (Finset.subset_insert _ _)) |>.mpr ⟨v, ?_, ?_⟩
    · simp [_hv]
    · simp

/-- `reachableFinding` at `671366e4`, renamed: the per-walk search from nothing marked. -/
def perWalkFinding [Fintype V] [DecidableEq V] (succ : V → List V) (P : V → Bool) (v : V) :
    Option (Σ w : V, DirectedWalk (fun a b => b ∈ succ a) v w) :=
  perWalkFindingAux succ P ∅ v

/-! ## The diamond chain -/

/-- A chain of `n` diamonds on `Fin (3n + 1)`: `3i` has the arcs to `3i + 1` and `3i + 2`, and
each of these the arc to `3i + 3`, for `i < n`. -/
def diamondSucc (n : ℕ) (x : Fin (3 * n + 1)) : List (Fin (3 * n + 1)) :=
  if x.val % 3 = 0 then
    if h : x.val + 2 < 3 * n + 1 then [⟨x.val + 1, by omega⟩, ⟨x.val + 2, h⟩] else []
  else if h : x.val + 2 < 3 * n + 1 ∧ x.val % 3 = 1 then [⟨x.val + 2, h.1⟩]
  else if h : x.val + 1 < 3 * n + 1 then [⟨x.val + 1, h⟩] else []

/-- The number of arcs of `diamondSucc n`. -/
def diamondArcs (n : ℕ) : ℕ :=
  ((List.finRange (3 * n + 1)).map fun x => (diamondSucc n x).length).sum

/-- The number of walks from `0` to `3n` in `diamondSucc n`, counted from the end: every arc goes
up, so the count at a vertex is the sum of the counts at its out-neighbours. -/
def diamondWalks (n : ℕ) : ℕ :=
  let m := 3 * n + 1
  let c := (List.finRange m).reverse.foldl (init := Array.replicate m 0) fun c x =>
    c.set! x.val (if x.val = 3 * n then 1 else ((diamondSucc n x).map fun y => c[y.val]!).sum)
  c[0]!

/-! ## The timing -/

/-- Run `f ()` and return its value with the time it took, in microseconds. The value is written
to a reference before the clock is read again, so it is computed in between. -/
@[noinline]
def timeMicros (f : Unit → Bool) : IO (Bool × ℕ) := do
  let r ← IO.mkRef false
  let t0 ← IO.monoNanosNow
  r.set (f ())
  let t1 ← IO.monoNanosNow
  return (← r.get, (t1 - t0) / 1000)

/-- One line for `n`: the graph's counts, then each search from `0` with `P` false everywhere,
its answer and its time, and the number of vertices the new search marks. -/
def timeBoth (n : ℕ) : IO Unit := do
  let (a, ta) ← timeMicros fun _ => (perWalkFinding (diamondSucc n) (fun _ => false) 0).isSome
  let (b, tb) ← timeMicros fun _ => (reachableFinding (diamondSucc n) (fun _ => false) 0).isSome
  let marked := (reachableFindingAux (diamondSucc n) (fun _ => false) ∅ 0).1.1.card
  let finds (found : Bool) : String := if found then "a vertex" else "nothing"
  IO.println s!"n = {n}: {3 * n + 1} vertices, {diamondArcs n} arcs, {diamondWalks n} walks \
    end to end; the per-walk search finds {finds a} in {ta} µs; the search with one marked set \
    finds {finds b} in {tb} µs and marks {marked} vertices"

#eval do for n in [8, 10, 12, 14, 16, 18] do timeBoth n

/-! ## The `decide` facts -/

section Decide

-- These facts are about what `native_decide` proves. Mathlib's linter bars it from proofs in
-- the library, and this file is not part of the library.
set_option linter.style.nativeDecide false

/-- Neither `decide` nor `decide +kernel` proves `k4MinusE.IsLaman`; `native_decide` does. -/
example : Examples.k4MinusE.IsLaman := by
  fail_if_success decide
  fail_if_success decide +kernel
  native_decide

/-- `native_decide` proves that `K₄` is not Laman. -/
example : ¬ Examples.k4.IsLaman := by native_decide

/-- `decide +kernel` proves that the graph on two vertices with its one edge is Laman. -/
example : (⊤ : SimpleGraph (Fin 2)).IsLaman := by decide +kernel

end Decide

end CombinatorialRigidity.DFSTiming
