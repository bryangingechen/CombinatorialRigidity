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

variable {V : Type*}

/-- A *partial orientation* on `V` is a finite set of directed arcs satisfying
two structural invariants:

* (no loops) no arc has equal endpoints;
* (no antiparallel pairs) at most one of `(u, v)` and `(v, u)` is present.

This is the algorithmic state of the `(k, ℓ)`-pebble game (Lee–Streinu §3,
blueprint `def:partial-orientation`). Storing the arcs as a `Finset (V × V)`
keeps the state fully decidable and computable, matching the style island
described in the file header; pebble counts (the per-vertex `out`-degree
budget remainder) are bookkeeping derived from the arcs. -/
structure PartialOrientation (V : Type*) [DecidableEq V] where
  /-- The underlying finite set of directed arcs. -/
  arcs : Finset (V × V)
  /-- No loops: no arc has equal endpoints. -/
  no_loops : ∀ ⦃v : V⦄, (v, v) ∉ arcs
  /-- No antiparallel pairs: at most one of `(u, v)` and `(v, u)` is an arc. -/
  no_antiparallel : ∀ ⦃u v : V⦄, (u, v) ∈ arcs → (v, u) ∉ arcs

namespace PartialOrientation

variable [DecidableEq V]

/-- The empty partial orientation: no arcs. The initial state of the
pebble-game algorithm. -/
def empty : PartialOrientation V where
  arcs := ∅
  no_loops _ := Finset.notMem_empty _
  no_antiparallel _ _ h := absurd h (Finset.notMem_empty _)

@[simp] lemma arcs_empty : (empty : PartialOrientation V).arcs = ∅ := rfl

variable (D : PartialOrientation V)

/-- The out-neighbour set of `v` in `D`: vertices `u` with `(v, u) ∈ D.arcs`. -/
def outNbhd (v : V) : Finset V :=
  (D.arcs.filter (·.1 = v)).image Prod.snd

lemma mem_outNbhd {v u : V} : u ∈ D.outNbhd v ↔ (v, u) ∈ D.arcs := by
  simp only [outNbhd, Finset.mem_image, Finset.mem_filter]
  refine ⟨?_, fun h => ⟨(v, u), ⟨h, rfl⟩, rfl⟩⟩
  rintro ⟨⟨a, b⟩, ⟨hmem, hfst⟩, hsnd⟩
  dsimp at hfst hsnd
  subst hfst; subst hsnd; exact hmem

/-- Out-degree at `v`: number of arcs of `D` sourced at `v`. Equivalently
`(D.outNbhd v).card`; cf. `def:pebble-counts`. -/
def out (v : V) : ℕ := (D.outNbhd v).card

/-- Pebble count at `v` with budget `k`: `k - out v` (truncated `ℕ`
subtraction). The structural invariant `out v ≤ k`, maintained by the
algorithm via `lem:pebble-game-invariants` (1), ensures this behaves
additively against `out v`. -/
def peb (k : ℕ) (v : V) : ℕ := k - D.out v

/-- Arcs of `D` with both endpoints in `V'`. -/
def spanArcs (V' : Finset V) : Finset (V × V) :=
  D.arcs.filter (fun p => p.1 ∈ V' ∧ p.2 ∈ V')

/-- Span of `V'` in `D`: number of arcs with both endpoints in `V'`. -/
def span (V' : Finset V) : ℕ := (D.spanArcs V').card

/-- Arcs of `D` with source in `V'` and head outside `V'`. -/
def boundaryArcs (V' : Finset V) : Finset (V × V) :=
  D.arcs.filter (fun p => p.1 ∈ V' ∧ p.2 ∉ V')

/-- Out-boundary count of `V'` in `D`: number of arcs leaving `V'`. -/
def outOn (V' : Finset V) : ℕ := (D.boundaryArcs V').card

/-- Total pebble count on `V'`: sum of `peb k v` over `v ∈ V'`. -/
def pebOn (k : ℕ) (V' : Finset V) : ℕ := ∑ v ∈ V', D.peb k v

@[simp] lemma outNbhd_empty (v : V) :
    (empty : PartialOrientation V).outNbhd v = ∅ := by
  simp [outNbhd]

@[simp] lemma out_empty (v : V) : (empty : PartialOrientation V).out v = 0 := by
  simp [out]

@[simp] lemma peb_empty (k : ℕ) (v : V) :
    (empty : PartialOrientation V).peb k v = k := by
  simp [peb]

@[simp] lemma spanArcs_empty (V' : Finset V) :
    (empty : PartialOrientation V).spanArcs V' = ∅ := by
  simp [spanArcs]

@[simp] lemma span_empty (V' : Finset V) :
    (empty : PartialOrientation V).span V' = 0 := by
  simp [span]

@[simp] lemma boundaryArcs_empty (V' : Finset V) :
    (empty : PartialOrientation V).boundaryArcs V' = ∅ := by
  simp [boundaryArcs]

@[simp] lemma outOn_empty (V' : Finset V) :
    (empty : PartialOrientation V).outOn V' = 0 := by
  simp [outOn]

@[simp] lemma pebOn_empty (k : ℕ) (V' : Finset V) :
    (empty : PartialOrientation V).pebOn k V' = V'.card * k := by
  simp [pebOn, Finset.sum_const, smul_eq_mul, mul_comm]

/-! ### Path reversal

The path-reversal move (Lee–Streinu §3, blueprint `def:path-reversal`):
given a simple directed path `p` in `D` from `u_0` to `u_m`, invert every
arc of `p` in `D`. The result is again a partial orientation; underlying
edges are preserved, but out-degree at `u_0` decreases by one while
out-degree at `u_m` increases by one (with all other vertices unchanged).
This file lands the definition and the invariant-preservation half;
structural lemmas about `out`/`peb`/`span`/`outOn` follow in a subsequent
commit (feeding `lem:pebble-game-invariants` (3)). -/

section Reverse

open CombinatorialRigidity.Search

variable {u w : V}

/-- The path-reversal of `D` along the simple directed path `p` in `D`.
Removes `p`'s arcs from `D` and inserts their reversals. The two
structural invariants of `PartialOrientation` survive:

* `no_loops`: no new self-loop arcs because `hp : p.IsPath` rules out
  `u_i = u_{i+1}`;
* `no_antiparallel`: the only potential conflict is between an original
  arc `(u_i, u_{i+1}) ∈ D.arcs` and its inserted reversal
  `(u_{i+1}, u_i)`, but the former is removed by the `sdiff`. The `IsPath`
  hypothesis discharges the case where two distinct path arcs would be
  reverses of each other.

Cf. Lee–Streinu §3 path-reversal move, blueprint `def:path-reversal`. -/
def reverse (p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w)
    (hp : p.IsPath) : PartialOrientation V where
  arcs := (D.arcs \ p.arcsFinset) ∪ p.reversedArcsFinset
  no_loops v hv := by
    rw [Finset.mem_union, Finset.mem_sdiff] at hv
    rcases hv with ⟨h, _⟩ | h
    · exact D.no_loops h
    · rw [p.mem_reversedArcsFinset_iff] at h
      exact hp.notMem_loop_arcsFinset v h
  no_antiparallel a b hab hba := by
    rw [Finset.mem_union, Finset.mem_sdiff] at hab
    rw [Finset.mem_union, Finset.mem_sdiff] at hba
    rcases hab with ⟨hab_D, hab_notArcs⟩ | hab_revArcs
    · rcases hba with ⟨hba_D, _⟩ | hba_revArcs
      · exact D.no_antiparallel hab_D hba_D
      · rw [p.mem_reversedArcsFinset_iff] at hba_revArcs
        exact hab_notArcs hba_revArcs
    · rw [p.mem_reversedArcsFinset_iff] at hab_revArcs
      rcases hba with ⟨_, hba_notArcs⟩ | hba_revArcs
      · exact hba_notArcs hab_revArcs
      · rw [p.mem_reversedArcsFinset_iff] at hba_revArcs
        exact hp.notMem_antiparallel_arcsFinset hab_revArcs hba_revArcs

@[simp] lemma arcs_reverse
    (p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w) (hp : p.IsPath) :
    (D.reverse p hp).arcs = (D.arcs \ p.arcsFinset) ∪ p.reversedArcsFinset :=
  rfl

end Reverse

end PartialOrientation

end CombinatorialRigidity.PebbleGame
