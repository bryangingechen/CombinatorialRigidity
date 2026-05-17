/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Chain

/-!
# Verified DFS with witness paths

A reusable depth-first search primitive on a finite type, presented as
the relation `fun a b => b ∈ succ a` for a user-supplied out-neighbour
function `succ : V → Finset V`. Given a source vertex `v` and a
predicate `P : V → Bool`, `reachableFinding succ P v` returns either
`some ⟨w, p⟩` with `P w` and `p` a simple walk from `v` to `w`, or
`none` when no such `w` is reachable from `v`.

We model termination on `Batteries.UnionFind`, whose
`termination_by self.rankMax - self.rank x` is a strictly-decreasing
numeric measure on a finite data structure; here the measure is
`(Finset.univ \ visited).card` for a finset of already-visited
vertices.

This file is pre-Phase-9 infrastructure: the pebble game's
`tryReachPebble` (Phase 9) specialises `reachableFinding` and
post-composes a path-reversal step. The DFS itself is reusable across
that and any future application that needs reachability with a
witness path.

## Main declarations

* `CombinatorialRigidity.Search.DirectedWalk` — inductive walks along
  an arbitrary relation `R : V → V → Prop`, indexed by endpoints.
* `CombinatorialRigidity.Search.DirectedWalk.IsPath` — a walk is a
  *path* when its vertex list has no duplicates.
* `CombinatorialRigidity.Search.reachableFinding` — the DFS itself.
* `CombinatorialRigidity.Search.reachableFinding_sound`,
  `CombinatorialRigidity.Search.reachableFinding_complete` —
  soundness and completeness against the `Relation.ReflTransGen`
  closure of the out-neighbour relation.

## Style island

This file takes `[Fintype V] [DecidableEq V]` directly in algorithm
signatures and uses `Finset.card` end-to-end, departing from the rest
of the project's `[Finite V]` + inline `Fintype.ofFinite V` bridge
idiom. The state machine cannot run at `[Finite V]` strength (no
`Finset.univ`, no enumeration); `#eval` / `decide` on extracted
certificates needs the typeclasses throughout. See
`../../DESIGN.md` *Pebble-game style island* for the rationale.

## References

* A. Lee, I. Streinu, *Pebble game algorithms and sparse graphs*,
  Discrete Math. **308** (2008) 1425–1437 — motivates the
  reachability primitive (§3, "free pebble reachable from `u` or `v`").
* `Batteries.UnionFind` — pattern model for the strictly-decreasing
  numeric termination measure on a finite data structure.
-/

@[expose] public section

namespace CombinatorialRigidity.Search

universe u
variable {V : Type u}

/-! ## Directed walks

`DirectedWalk R u w` is a walk from `u` to `w` along the relation `R`
on `V`. The shape mirrors `SimpleGraph.Walk`: a list-like inductive
indexed by endpoints, with `nil` for the empty walk and `cons` to
extend along an arc. -/

/-- An `R`-walk from `u` to `w`: either the empty walk at `u`, or an
`R u v` arc followed by an `R`-walk from `v` to `w`. -/
inductive DirectedWalk (R : V → V → Prop) : V → V → Type u
  | nil (u : V) : DirectedWalk R u u
  | cons {u v w : V} (h : R u v) (p : DirectedWalk R v w) : DirectedWalk R u w

namespace DirectedWalk

variable {R : V → V → Prop} {u v w : V}

/-- Number of arcs in the walk. `(nil u).length = 0`; each `cons`
extends by one. -/
def length : ∀ {u w : V}, DirectedWalk R u w → ℕ
  | _, _, nil _      => 0
  | _, _, cons _ p   => p.length + 1

/-- The list of vertices visited by the walk, in order. Has length
`p.length + 1` (every walk visits at least one vertex). -/
def vertices : ∀ {u w : V}, DirectedWalk R u w → List V
  | u, _, nil _      => [u]
  | u, _, cons _ p   => u :: p.vertices

/-- The walk visits each vertex at most once. -/
def IsPath (p : DirectedWalk R u w) : Prop := p.vertices.Nodup

end DirectedWalk

/-! ## The DFS primitive

`reachableFinding succ P v` searches outward from `v` along
`succ`-arcs, returning the first vertex `w` reachable from `v` with
`P w`, packaged with a simple walk from `v` to `w`. -/

variable [Fintype V] [DecidableEq V]

/-- Depth-first search for a `P`-satisfying vertex reachable from `v`
along the relation `fun a b => b ∈ succ a`.

* On success: `some ⟨w, p⟩`, where `P w = true` and `p` is a simple
  `succ`-walk from `v` to `w` (cf. `reachableFinding_sound`).
* On failure: `none`, in which case no vertex in the `succ`-closure
  of `v` satisfies `P` (cf. `reachableFinding_complete`).

Termination is by `(Finset.univ \ visited).card` on the internal
recursive helper that threads a `visited` set; cf. the file
docstring's *Batteries.UnionFind* comparison.

Body deferred — this declaration is currently a scaffolding stub. -/
noncomputable def reachableFinding (succ : V → Finset V) (P : V → Bool) (v : V) :
    Option (Σ w : V, DirectedWalk (fun a b => b ∈ succ a) v w) := sorry

/-- **Soundness.** If `reachableFinding succ P v = some ⟨w, p⟩`, then
`P w` holds and the returned walk `p` is simple. -/
theorem reachableFinding_sound {succ : V → Finset V} {P : V → Bool} {v : V}
    {w : V} {p : DirectedWalk (fun a b => b ∈ succ a) v w}
    (hres : reachableFinding succ P v = some ⟨w, p⟩) :
    P w = true ∧ p.IsPath := sorry

/-- **Completeness.** If some vertex `w` in the `succ`-reachability
closure of `v` satisfies `P`, then `reachableFinding` returns
`some ⟨w', p⟩` for some such `w'` (possibly `w' ≠ w`, since the DFS
returns the first match in its traversal order). -/
theorem reachableFinding_complete {succ : V → Finset V} {P : V → Bool} {v : V}
    (h : ∃ w : V, Relation.ReflTransGen (fun a b => b ∈ succ a) v w ∧ P w = true) :
    ∃ (w' : V) (p : DirectedWalk (fun a b => b ∈ succ a) v w'),
      reachableFinding succ P v = some ⟨w', p⟩ := sorry

end CombinatorialRigidity.Search
