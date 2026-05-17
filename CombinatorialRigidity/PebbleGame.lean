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

/-- The out-degree at `v` equals the cardinality of the source-`v` slice of
`D.arcs`. Used by the `out_reverse` lemmas to reduce to set-arithmetic on the
arc finset, bypassing the `outNbhd` `image Prod.snd` indirection. -/
lemma out_eq_card_filter_fst (v : V) :
    D.out v = (D.arcs.filter (·.1 = v)).card := by
  rw [out, outNbhd, Finset.card_image_of_injOn]
  rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ hsnd
  rw [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
  obtain ⟨_, rfl⟩ := h₁
  obtain ⟨_, rfl⟩ := h₂
  simp only at hsnd
  rw [hsnd]

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

/-- The sum of per-vertex out-degrees over a subset `V'` partitions arcs sourced
in `V'` by their target: arcs landing in `V'` are counted by `D.span V'`, arcs
leaving `V'` by `D.outOn V'`. Bridges per-vertex `out` to the subset-level
`span`/`outOn` accounting; consumed by `pebOn_add_span_add_outOn`. -/
lemma sum_out_eq_span_add_outOn (V' : Finset V) :
    ∑ v ∈ V', D.out v = D.span V' + D.outOn V' := by
  simp_rw [out_eq_card_filter_fst]
  rw [Finset.sum_card_fiberwise_eq_card_filter,
    ← Finset.card_filter_add_card_filter_not (p := fun p : V × V => p.2 ∈ V'),
    Finset.filter_filter, Finset.filter_filter]
  rfl

/-- Lee–Streinu Invariant (2) (algebraic form): under the per-vertex bound
`D.out v ≤ k` on `V'`, the subset's pebble count, span, and out-boundary sum to
`k|V'|`. Combines Invariant (1) (`peb v + out v = k`) summed over `V'` with the
fiberwise identity `sum_out_eq_span_add_outOn`. Feeds
`lem:pebble-game-invariants` (2). -/
lemma pebOn_add_span_add_outOn (k : ℕ) (V' : Finset V)
    (hbd : ∀ v ∈ V', D.out v ≤ k) :
    D.pebOn k V' + D.span V' + D.outOn V' = k * V'.card := by
  have h_peb_out : D.pebOn k V' + ∑ v ∈ V', D.out v = k * V'.card := by
    rw [pebOn, ← Finset.sum_add_distrib]
    have h : ∀ v ∈ V', D.peb k v + D.out v = k := fun v hv => by
      unfold peb; exact Nat.sub_add_cancel (hbd v hv)
    rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, mul_comm]
  have h_sum := D.sum_out_eq_span_add_outOn V'
  omega

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

/-- The arcs of a walk along `D`'s arc relation lie in `D.arcs`. Specialises
`DirectedWalk.mem_arcsFinset_imp` to `R := fun a b => (a, b) ∈ D.arcs`. -/
lemma arcsFinset_subset_arcs
    (p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w) :
    p.arcsFinset ⊆ D.arcs := fun _ h => p.mem_arcsFinset_imp h

/-- The complement of a walk's arcs in `D` is disjoint from the walk's
reversed arcs: an arc and its reverse cannot coexist in `D.arcs` by
`D.no_antiparallel`. -/
lemma disjoint_sdiff_reversedArcsFinset
    (p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w) :
    Disjoint (D.arcs \ p.arcsFinset) p.reversedArcsFinset := by
  rw [Finset.disjoint_left]
  rintro ⟨a, b⟩ hx hy
  rw [Finset.mem_sdiff] at hx
  rw [p.mem_reversedArcsFinset_iff] at hy
  exact D.no_antiparallel hx.1 (p.mem_arcsFinset_imp hy)

/-- Unified equation for the effect of path reversal on per-vertex out-degree:
the new out-count plus a path-arc indicator equals the old out-count plus a
reversed-arc indicator. Every interior path vertex sits in both indicators (so
its out-degree is unchanged), the initial vertex sits only in the path-arc
indicator (out-degree drops by `1` at `u`), and the terminal sits only in the
reversed-arc indicator (out-degree rises by `1` at `w`). Off-path vertices
satisfy neither, again leaving the out-degree fixed.

Three convenience corollaries (`out_reverse_of_not_endpoint`,
`out_reverse_head`, `out_reverse_tail`) extract the head/tail/middle cases. -/
lemma out_reverse_add
    (p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w) (hp : p.IsPath) (v : V) :
    (D.reverse p hp).out v + (if v ∈ p.vertices ∧ v ≠ w then 1 else 0)
      = D.out v + (if v ∈ p.vertices ∧ v ≠ u then 1 else 0) := by
  -- Approach: factor the calculation through filter-cardinality equalities so
  -- the rewrites never touch `D.arcs` directly (which appears in `p`'s type
  -- via the relation `fun a b => (a, b) ∈ D.arcs`, breaking `rw`'s motive
  -- abstraction).
  simp only [out_eq_card_filter_fst]
  have h_subset : p.arcsFinset ⊆ D.arcs := D.arcsFinset_subset_arcs p
  have h_disj_arcs : Disjoint (D.arcs \ p.arcsFinset) p.arcsFinset :=
    Finset.sdiff_disjoint
  have h_disj_rev : Disjoint (D.arcs \ p.arcsFinset) p.reversedArcsFinset :=
    D.disjoint_sdiff_reversedArcsFinset p
  -- The two ext-based equalities sidestep the motive issue cleanly: we never
  -- rewrite `D.arcs`, only assert finset equalities and `rw` them as units.
  have h_arc_decomp : D.arcs.filter (·.1 = v) =
      (D.arcs \ p.arcsFinset).filter (·.1 = v) ∪ p.arcsFinset.filter (·.1 = v) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨hx, hpred⟩
      by_cases h_path : x ∈ p.arcsFinset
      · exact Or.inr ⟨h_path, hpred⟩
      · exact Or.inl ⟨⟨hx, h_path⟩, hpred⟩
    · rintro (⟨⟨hx, _⟩, hpred⟩ | ⟨hxp, hpred⟩)
      · exact ⟨hx, hpred⟩
      · exact ⟨h_subset hxp, hpred⟩
  rw [h_arc_decomp, Finset.card_union_of_disjoint
      (h_disj_arcs.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
    arcs_reverse, Finset.filter_union, Finset.card_union_of_disjoint
      (h_disj_rev.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
    hp.card_arcsFinset_filter_fst v, hp.card_reversedArcsFinset_filter_fst v]
  omega

/-- A non-nil simple walk has distinct endpoints: `IsPath` says the vertex list
is `Nodup`, and `0 < p.length` produces an extra cons whose `Nodup` forbids the
initial vertex `u` from reappearing as the terminal `w` (which is the head of
the inner walk's vertex list). -/
lemma _root_.CombinatorialRigidity.Search.DirectedWalk.IsPath.head_ne_tail_of_pos
    {V : Type*} {R : V → V → Prop} {u w : V} {p : DirectedWalk R u w}
    (hp : p.IsPath) (hpos : 0 < p.length) : u ≠ w := by
  cases p with
  | nil _ => simp [DirectedWalk.length] at hpos
  | @cons u' v' w' h_arc q' =>
    rw [DirectedWalk.IsPath, DirectedWalk.vertices, List.nodup_cons] at hp
    intro h_eq
    exact hp.1 (h_eq ▸ q'.tail_mem_vertices)

/-- For a vertex distinct from both endpoints of the reversed path, the
out-degree is unchanged. Interior path vertices fall under this case: their
path-arc out (`(u_i, u_{i+1})`) and reversed-arc out (`(u_i, u_{i-1})`) cancel;
off-path vertices have neither. -/
lemma out_reverse_of_not_endpoint
    (p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w) (hp : p.IsPath)
    {v : V} (hu : v ≠ u) (hw : v ≠ w) :
    (D.reverse p hp).out v = D.out v := by
  have h := D.out_reverse_add p hp v
  -- Both if-clauses share `v ∈ p.vertices`; the `v ≠ w` and `v ≠ u` conjuncts
  -- are settled by hypothesis, so the ifs take the same value either way.
  have h_eq : (if v ∈ p.vertices ∧ v ≠ w then 1 else 0 : ℕ) =
      (if v ∈ p.vertices ∧ v ≠ u then 1 else 0) := by
    by_cases hmem : v ∈ p.vertices
    · rw [if_pos ⟨hmem, hw⟩, if_pos ⟨hmem, hu⟩]
    · rw [if_neg (fun h => hmem h.1), if_neg (fun h => hmem h.1)]
  omega

/-- Head endpoint: the initial vertex of a non-nil reversed path loses one
out-arc. The path arc `(u, u_1)` is removed; no reversed arc is added at `u`
(the reversed arcs all source from `u_1, …, u_m`). -/
lemma out_reverse_head
    (p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w) (hp : p.IsPath)
    (hpos : 0 < p.length) :
    (D.reverse p hp).out u + 1 = D.out u := by
  have h := D.out_reverse_add p hp u
  have h_mem : u ∈ p.vertices := p.head_mem_vertices
  have h_ne : u ≠ w := hp.head_ne_tail_of_pos hpos
  rw [if_pos ⟨h_mem, h_ne⟩, if_neg (fun ⟨_, h⟩ => h rfl)] at h
  omega

/-- Tail endpoint: the terminal vertex of a non-nil reversed path gains one
out-arc. The reversed arc `(u_m, u_{m-1})` is added; no path arc was sourced
at `u_m` (the terminal has no outgoing path arc). -/
lemma out_reverse_tail
    (p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w) (hp : p.IsPath)
    (hpos : 0 < p.length) :
    (D.reverse p hp).out w = D.out w + 1 := by
  have h := D.out_reverse_add p hp w
  have h_mem : w ∈ p.vertices := p.tail_mem_vertices
  have h_ne : w ≠ u := (hp.head_ne_tail_of_pos hpos).symm
  rw [if_neg (fun ⟨_, h⟩ => h rfl), if_pos ⟨h_mem, h_ne⟩] at h
  omega

/-- The pebble count is unchanged at vertices distinct from both endpoints of
the reversed path. Direct corollary of `out_reverse_of_not_endpoint`: pebble
count is `k - out`, and the underlying out-count is preserved. -/
lemma peb_reverse_of_not_endpoint
    (p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w) (hp : p.IsPath)
    (k : ℕ) {v : V} (hu : v ≠ u) (hw : v ≠ w) :
    (D.reverse p hp).peb k v = D.peb k v := by
  rw [peb, peb, D.out_reverse_of_not_endpoint p hp hu hw]

/-- Head endpoint, under the algorithmic invariant `out u ≤ k`: the initial
vertex of a non-nil reversed path gains one pebble (mirror of the out-count
dropping by one). The hypothesis `D.out u ≤ k` is what
`lem:pebble-game-invariants` (1) maintains. -/
lemma peb_reverse_head
    (p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w) (hp : p.IsPath)
    (hpos : 0 < p.length) (k : ℕ) (hbd : D.out u ≤ k) :
    (D.reverse p hp).peb k u = D.peb k u + 1 := by
  have h_out : (D.reverse p hp).out u + 1 = D.out u :=
    D.out_reverse_head p hp hpos
  rw [peb, peb]
  omega

/-- Tail endpoint, under the algorithmic precondition `D.out w < k`: the
terminal vertex of a non-nil reversed path loses one pebble (mirror of the
out-count rising by one). `out w < k` is the precondition for the path-reversal
move to be valid (the head of the reachability search must have a free pebble
to send). -/
lemma peb_reverse_tail
    (p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w) (hp : p.IsPath)
    (hpos : 0 < p.length) (k : ℕ) (hbd : D.out w < k) :
    (D.reverse p hp).peb k w + 1 = D.peb k w := by
  have h_out : (D.reverse p hp).out w = D.out w + 1 :=
    D.out_reverse_tail p hp hpos
  rw [peb, peb]
  omega

/-- The span of `V'` is invariant under path reversal: each path arc with
both endpoints in `V'` is removed and its reverse is inserted, and both
sit in `spanArcs V'`. Feeds `lem:pebble-game-invariants` (2) on path-reversal
moves. -/
lemma span_reverse_eq
    (p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w) (hp : p.IsPath)
    (V' : Finset V) :
    (D.reverse p hp).span V' = D.span V' := by
  -- Setup: the span predicate, its swap-symmetry, the path-arcs-in-D subset.
  set Q : V × V → Prop := fun pp => pp.1 ∈ V' ∧ pp.2 ∈ V' with hQ
  have hQ_swap : ∀ pp, Q (Prod.swap pp) ↔ Q pp := by
    intro ⟨a, b⟩; simp [Q, and_comm]
  have h_subset : p.arcsFinset ⊆ D.arcs := D.arcsFinset_subset_arcs p
  -- Decompose D.arcs as (D.arcs \ p.arcsFinset) ⊔ p.arcsFinset, filter, sum cards.
  have h_decomp : D.arcs = (D.arcs \ p.arcsFinset) ∪ p.arcsFinset :=
    (Finset.sdiff_union_of_subset h_subset).symm
  have h_disj_arcs : Disjoint (D.arcs \ p.arcsFinset) p.arcsFinset :=
    Finset.sdiff_disjoint
  have h_disj_rev : Disjoint (D.arcs \ p.arcsFinset) p.reversedArcsFinset :=
    D.disjoint_sdiff_reversedArcsFinset p
  simp only [span, spanArcs, arcs_reverse]
  conv_rhs => rw [h_decomp]
  rw [Finset.filter_union, Finset.filter_union,
      Finset.card_union_of_disjoint
        (h_disj_rev.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      Finset.card_union_of_disjoint
        (h_disj_arcs.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  -- Reduce to filter-card equality between p.arcsFinset and p.reversedArcsFinset.
  congr 1
  -- Bijection via `Prod.swap`: `p.reversedArcsFinset = p.arcsFinset.image Prod.swap`,
  -- and `Q` is swap-symmetric, so the filtered cards match.
  rw [p.reversedArcsFinset_eq_image_swap, Finset.filter_image,
      Finset.card_image_of_injective _ Prod.swap_injective,
      Finset.filter_congr (fun pp _ => hQ_swap pp)]

/-- The sum of subset-level pebble count and out-boundary is invariant under
path reversal: span is invariant by `span_reverse_eq`, so the L-S Invariant (2)
algebraic identity `pebOn + span + outOn = k|V'|` applied to both `D` and
`D.reverse p hp` forces `pebOn + outOn` to match. While `outOn V'` itself
shifts by `[w ∈ V'] - [u ∈ V']` per the head/tail accounting in
`out_reverse_head` / `out_reverse_tail`, the corresponding shift in `pebOn k V'`
cancels it. Feeds `lem:pebble-game-invariants` (2) on path-reversal moves. -/
lemma pebOn_add_outOn_reverse_eq
    (p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w) (hp : p.IsPath)
    {k : ℕ} {V' : Finset V}
    (hbd : ∀ v ∈ V', D.out v ≤ k) (hbd' : ∀ v ∈ V', (D.reverse p hp).out v ≤ k) :
    (D.reverse p hp).pebOn k V' + (D.reverse p hp).outOn V'
      = D.pebOn k V' + D.outOn V' := by
  have h_D := D.pebOn_add_span_add_outOn k V' hbd
  have h_D' := (D.reverse p hp).pebOn_add_span_add_outOn k V' hbd'
  rw [D.span_reverse_eq p hp V'] at h_D'
  omega

end Reverse

/-! ### Arc insertion

The arc-insertion move (Lee–Streinu §3, the edge-insertion half of
`def:tryAddEdge`): given a directed pair `(u, v)` with `u ≠ v` and
`(v, u) ∉ D.arcs`, extend `D` by `(u, v)`. The two `PartialOrientation`
invariants survive directly from the preconditions. Per-vertex
accounting lemmas additionally assume `(u, v) ∉ D.arcs` to ensure the
`Finset.insert` is a genuine extension rather than a no-op. -/

section AddArc

/-- Add the directed arc `(u, v)` to `D`. The two `PartialOrientation`
invariants survive under the preconditions: `huv : u ≠ v` rules out a
self-loop, and `hnotin_rev : (v, u) ∉ D.arcs` rules out an antiparallel
pair. The accounting lemmas (`out_addArc_source`, etc.) additionally
take `(u, v) ∉ D.arcs` to ensure `Finset.insert` is a genuine extension.

Cf. Lee–Streinu §3 arc-insertion move; together with `def:path-reversal`,
the two state transitions used by the pebble game's `def:tryAddEdge`. -/
def addArc (u v : V) (huv : u ≠ v) (hnotin_rev : (v, u) ∉ D.arcs) :
    PartialOrientation V where
  arcs := insert (u, v) D.arcs
  no_loops w hw := by
    rw [Finset.mem_insert] at hw
    rcases hw with heq | h
    · -- `(w, w) = (u, v)` forces `w = u` and `w = v`, hence `u = v`, against `huv`.
      have h1 : w = u := (Prod.mk.inj heq).1
      have h2 : w = v := (Prod.mk.inj heq).2
      exact huv (h1.symm.trans h2)
    · exact D.no_loops h
  no_antiparallel a b hab hba := by
    rw [Finset.mem_insert] at hab hba
    -- `subst` would eliminate the *older* free variables `u`/`v` rather than
    -- `a`/`b` (cf. TACTICS-QUIRKS § 4); rewrite into `hba`/`hab` via `rw` to
    -- preserve `u`/`v` in scope for the contradictions.
    rcases hab with hab | hab
    · have h1 : a = u := (Prod.mk.inj hab).1
      have h2 : b = v := (Prod.mk.inj hab).2
      rw [h1, h2] at hba
      rcases hba with hba | hba
      · -- `(v, u) = (u, v)` forces `v = u`.
        exact huv ((Prod.mk.inj hba).1).symm
      · exact hnotin_rev hba
    · rcases hba with hba | hba
      · have h1 : b = u := (Prod.mk.inj hba).1
        have h2 : a = v := (Prod.mk.inj hba).2
        rw [h1, h2] at hab
        exact hnotin_rev hab
      · exact D.no_antiparallel hab hba

@[simp] lemma arcs_addArc (u v : V) (huv : u ≠ v) (hnotin_rev : (v, u) ∉ D.arcs) :
    (D.addArc u v huv hnotin_rev).arcs = insert (u, v) D.arcs := rfl

/-- Adding the arc `(u, v)` to `D` raises `out u` by `1`, provided the arc
was not already present. The non-source vertices are unaffected
(`out_addArc_of_ne_source`). -/
lemma out_addArc_source (u v : V) (huv : u ≠ v) (hnotin_rev : (v, u) ∉ D.arcs)
    (hnotin : (u, v) ∉ D.arcs) :
    (D.addArc u v huv hnotin_rev).out u = D.out u + 1 := by
  simp only [out_eq_card_filter_fst, arcs_addArc]
  rw [Finset.filter_insert, if_pos rfl]
  exact Finset.card_insert_of_notMem
    (by rw [Finset.mem_filter]; exact fun h => hnotin h.1)

/-- Adding the arc `(u, v)` to `D` leaves out-degree at every non-source
vertex unchanged. The inserted arc is sourced at `u`, so the source-`x`
slice of `D.arcs` is unaffected for any `x ≠ u`. -/
lemma out_addArc_of_ne_source (u v : V) (huv : u ≠ v) (hnotin_rev : (v, u) ∉ D.arcs)
    {x : V} (hxu : x ≠ u) :
    (D.addArc u v huv hnotin_rev).out x = D.out x := by
  simp only [out_eq_card_filter_fst, arcs_addArc]
  rw [Finset.filter_insert, if_neg (fun h => hxu h.symm)]

/-- Adding the arc `(u, v)` to `D` drops the pebble count at `u` by `1`,
under the precondition `D.out u < k` (a free pebble at `u`; cf.
`lem:pebble-game-invariants` (1)). The non-source pebble counts are
unaffected (`peb_addArc_of_ne_source`). -/
lemma peb_addArc_source (u v : V) (huv : u ≠ v) (hnotin_rev : (v, u) ∉ D.arcs)
    (hnotin : (u, v) ∉ D.arcs) {k : ℕ} (hk : D.out u < k) :
    (D.addArc u v huv hnotin_rev).peb k u + 1 = D.peb k u := by
  rw [peb, peb, D.out_addArc_source u v huv hnotin_rev hnotin]
  omega

/-- Adding the arc `(u, v)` to `D` leaves the pebble count at every
non-source vertex unchanged. Direct corollary of
`out_addArc_of_ne_source` and `peb := k - out`. -/
lemma peb_addArc_of_ne_source (u v : V) (huv : u ≠ v) (hnotin_rev : (v, u) ∉ D.arcs)
    (k : ℕ) {x : V} (hxu : x ≠ u) :
    (D.addArc u v huv hnotin_rev).peb k x = D.peb k x := by
  rw [peb, peb, D.out_addArc_of_ne_source u v huv hnotin_rev hxu]

/-! #### Subset-level accounting for arc insertion

The next four lemmas trace how `span`, `outOn`, `pebOn` shift on a subset
`V'` when a fresh arc `(u, v)` is inserted. Each is a unified additive
identity keyed on the position of `u`/`v` relative to `V'`; together they
yield the combined identity `pebOn_add_outOn_addArc_add` which feeds
`lem:pebble-game-invariants` (3) at the arc-insertion step. -/

/-- Span of `V'` rises by `1` exactly when both endpoints of the inserted arc
lie in `V'`, and is unchanged otherwise. Unified additive identity, like
`out_reverse_add` for the path-reversal case. -/
lemma span_addArc (u v : V) (huv : u ≠ v) (hnotin_rev : (v, u) ∉ D.arcs)
    (hnotin : (u, v) ∉ D.arcs) (V' : Finset V) :
    (D.addArc u v huv hnotin_rev).span V'
      = D.span V' + (if u ∈ V' ∧ v ∈ V' then 1 else 0) := by
  simp only [span, spanArcs, arcs_addArc, Finset.filter_insert]
  by_cases h : u ∈ V' ∧ v ∈ V'
  · rw [if_pos h, if_pos h]
    refine Finset.card_insert_of_notMem ?_
    rw [Finset.mem_filter]
    exact fun ⟨h_in, _⟩ => hnotin h_in
  · rw [if_neg h, if_neg h, Nat.add_zero]

/-- Out-boundary of `V'` rises by `1` exactly when the inserted arc has its
source in `V'` and its head outside `V'`, and is unchanged otherwise. -/
lemma outOn_addArc (u v : V) (huv : u ≠ v) (hnotin_rev : (v, u) ∉ D.arcs)
    (hnotin : (u, v) ∉ D.arcs) (V' : Finset V) :
    (D.addArc u v huv hnotin_rev).outOn V'
      = D.outOn V' + (if u ∈ V' ∧ v ∉ V' then 1 else 0) := by
  simp only [outOn, boundaryArcs, arcs_addArc, Finset.filter_insert]
  by_cases h : u ∈ V' ∧ v ∉ V'
  · rw [if_pos h, if_pos h]
    refine Finset.card_insert_of_notMem ?_
    rw [Finset.mem_filter]
    exact fun ⟨h_in, _⟩ => hnotin h_in
  · rw [if_neg h, if_neg h, Nat.add_zero]

/-- Total pebble count on `V'` drops by `1` exactly when the source vertex `u`
lies in `V'`, and is unchanged otherwise. Stated additively (so that ℕ-
subtraction never appears) as `pebOn(new) + [u ∈ V'] = pebOn(old)`. The
precondition `D.out u < k` keeps `peb k u` honest under truncated subtraction;
see `peb_addArc_source`. -/
lemma pebOn_addArc (u v : V) (huv : u ≠ v) (hnotin_rev : (v, u) ∉ D.arcs)
    (hnotin : (u, v) ∉ D.arcs) {k : ℕ} (hk : D.out u < k) (V' : Finset V) :
    (D.addArc u v huv hnotin_rev).pebOn k V' + (if u ∈ V' then 1 else 0)
      = D.pebOn k V' := by
  by_cases hu : u ∈ V'
  · -- Split off the `u`-term from both sides via `Finset.add_sum_erase`. The
    -- residual sum over `V'.erase u` agrees between `D` and `D.addArc …` by
    -- `peb_addArc_of_ne_source`; the `u`-term shifts by `1` by
    -- `peb_addArc_source` (under `D.out u < k`).
    rw [if_pos hu]
    simp only [pebOn]
    rw [← Finset.add_sum_erase _ _ hu, ← Finset.add_sum_erase _ _ hu]
    have h_peb_u : (D.addArc u v huv hnotin_rev).peb k u + 1 = D.peb k u := by
      rw [peb, peb, D.out_addArc_source u v huv hnotin_rev hnotin]
      omega
    have h_peb_rest : ∑ x ∈ V'.erase u, (D.addArc u v huv hnotin_rev).peb k x
        = ∑ x ∈ V'.erase u, D.peb k x :=
      Finset.sum_congr rfl (fun x hx =>
        D.peb_addArc_of_ne_source u v huv hnotin_rev k (Finset.ne_of_mem_erase hx))
    rw [h_peb_rest]
    omega
  · -- `u ∉ V'`: every `x ∈ V'` has `x ≠ u`, so new `peb` agrees with old.
    rw [if_neg hu, Nat.add_zero]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    exact D.peb_addArc_of_ne_source u v huv hnotin_rev k (fun heq => hu (heq ▸ hx))

/-- Combined accounting identity for `pebOn + outOn` under arc insertion: the
sum decreases by `1` exactly when both endpoints of the inserted arc lie in
`V'`, and is unchanged otherwise. Direct consequence of `outOn_addArc` and
`pebOn_addArc`: in the only case where `outOn` rises (source in `V'`, head
outside `V'`), `pebOn` drops by `1` in lockstep, cancelling the shift; in the
"both inside" case, `outOn` is unchanged but `pebOn` still drops by `1`,
producing the net decrease.
Feeds `lem:pebble-game-invariants` (3) at the arc-insertion step: the
threshold precondition `peb(u) + peb(v) ≥ ℓ + 1` for an accepted insertion
forces `pebOn V' ≥ ℓ + 1` when `u, v ∈ V'`, so the post-insertion bound
`pebOn(V') + outOn(V') ≥ ℓ` is preserved. -/
lemma pebOn_add_outOn_addArc_add (u v : V) (huv : u ≠ v) (hnotin_rev : (v, u) ∉ D.arcs)
    (hnotin : (u, v) ∉ D.arcs) {k : ℕ} (hk : D.out u < k) (V' : Finset V) :
    (D.addArc u v huv hnotin_rev).pebOn k V' + (D.addArc u v huv hnotin_rev).outOn V'
        + (if u ∈ V' ∧ v ∈ V' then 1 else 0)
      = D.pebOn k V' + D.outOn V' := by
  have h_peb := D.pebOn_addArc u v huv hnotin_rev hnotin hk V'
  have h_out := D.outOn_addArc u v huv hnotin_rev hnotin V'
  -- Combine: the two if-indicators on `(u ∈ V', v ∈ V')` sum to `[u ∈ V']`.
  by_cases hu : u ∈ V'
  · by_cases hv : v ∈ V'
    · simp [hu, hv] at h_peb h_out ⊢; omega
    · simp [hu, hv] at h_peb h_out ⊢; omega
  · simp [hu] at h_peb h_out ⊢; omega

end AddArc

/-! ### Reachability and the four pebble-game invariants

A partial orientation `D` is `(k, ℓ)`-*reachable* if it can be obtained from
the empty orientation by a sequence of valid moves: path reversals
(requiring `D.out w < k` at the path's tail, so the new arc fits without
exceeding the out-degree budget) and accepted insertions (requiring
`u ≠ v`, `(u, v) ∉ D.arcs`, `(v, u) ∉ D.arcs`, `D.out u < k`, and the
threshold `ℓ + 1 ≤ peb k u + peb k v` from Lee–Streinu §3). The four
invariants of `lem:pebble-game-invariants` hold on every reachable
orientation:

* (1) `D.out v ≤ k` (equivalently `D.peb k v + D.out v = k` under
  truncated ℕ-subtraction) — `Reachable.out_le` / `Reachable.peb_add_out_eq`.
* (2) `pebOn k V' + span V' + outOn V' = k * V'.card` —
  `Reachable.pebOn_add_span_add_outOn`.
* (3) `ℓ ≤ pebOn k V' + outOn V'` under `ℓ ≤ k * V'.card` —
  `Reachable.pebOn_add_outOn_ge` (the substantive piece).
* (4) `span V' + ℓ ≤ k * V'.card` (the project-style additive form of the
  blueprint's `span V' ≤ k|V'| - ℓ`) under the same size hypothesis —
  `Reachable.span_add_le`, an algebraic consequence of (2) and (3).

The size hypothesis `ℓ ≤ k * V'.card` unifies L-S's two regime-dependent
cases: `|V'| ≥ 1 ∧ ℓ ≤ k` and `|V'| ≥ 2 ∧ ℓ < 2k` both imply it (the
single quantity the empty base case actually requires). -/

section Reachability

open CombinatorialRigidity.Search

variable {k ℓ : ℕ}

/-- A partial orientation `D` is `(k, ℓ)`-*reachable* if it can be obtained
from the empty orientation by a sequence of valid path-reversal and
accepted-insertion moves. The path-reversal constructor requires
`D.out w < k` at the path's tail (so the new arc fits within the out-degree
budget); the arc-insertion constructor requires `u ≠ v`, that neither
`(u, v)` nor `(v, u)` is already in `D.arcs`, `D.out u < k` at the source,
and the threshold `ℓ + 1 ≤ peb k u + peb k v` from Lee–Streinu §3.

The four invariants of `lem:pebble-game-invariants` are proved on
`Reachable`-orientations by induction on the move sequence. -/
inductive Reachable (k ℓ : ℕ) : PartialOrientation V → Prop
  | empty : Reachable k ℓ (empty : PartialOrientation V)
  | reverse {D : PartialOrientation V} (hD : Reachable k ℓ D)
      {u w : V} (p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w)
      (hp : p.IsPath) (hw : D.out w < k) :
      Reachable k ℓ (D.reverse p hp)
  | addArc {D : PartialOrientation V} (hD : Reachable k ℓ D)
      {u v : V} (huv : u ≠ v) (hnotin : (u, v) ∉ D.arcs)
      (hnotin_rev : (v, u) ∉ D.arcs) (hu_out : D.out u < k)
      (hk : ℓ + 1 ≤ D.peb k u + D.peb k v) :
      Reachable k ℓ (D.addArc u v huv hnotin_rev)

/-- L-S Invariant (1), primal form: every out-degree of a `(k, ℓ)`-reachable
orientation is bounded by `k`. By induction on the `Reachable` derivation:
the path-reversal case uses `out_reverse_add` (only `v = w` can shift the
count upward, and `D.out w < k` from the constructor absorbs the `+1`);
arc insertion uses `out_addArc_source` / `out_addArc_of_ne_source` (only
`v = u` shifts, and `D.out u < k` from the constructor absorbs the `+1`). -/
lemma Reachable.out_le {D : PartialOrientation V} (h : Reachable k ℓ D) (v : V) :
    D.out v ≤ k := by
  induction h with
  | empty => simp
  | @reverse D' hD' u w p hp hw ih =>
    by_cases hvw : v = w
    · subst hvw
      have h_add := D'.out_reverse_add p hp v
      have h_lhs : (if v ∈ p.vertices ∧ v ≠ v then (1 : ℕ) else 0) = 0 := by simp
      rw [h_lhs] at h_add
      split_ifs at h_add <;> omega
    · by_cases hvu : v = u
      · subst hvu
        have h_add := D'.out_reverse_add p hp v
        have h_rhs : (if v ∈ p.vertices ∧ v ≠ v then (1 : ℕ) else 0) = 0 := by simp
        rw [h_rhs] at h_add
        split_ifs at h_add <;> omega
      · rw [D'.out_reverse_of_not_endpoint p hp hvu hvw]
        exact ih
  | @addArc D' hD' a b hab hnotin hnotin_rev ha_out _hk ih =>
    by_cases hva : v = a
    · subst hva
      rw [D'.out_addArc_source v b hab hnotin_rev hnotin]
      omega
    · rw [D'.out_addArc_of_ne_source a b hab hnotin_rev hva]
      exact ih

/-- L-S Invariant (1), additive form: `peb k v + out v = k` for every vertex
of a reachable orientation. Direct from `out_le` via `Nat.sub_add_cancel`. -/
lemma Reachable.peb_add_out_eq {D : PartialOrientation V} (h : Reachable k ℓ D)
    (v : V) : D.peb k v + D.out v = k := by
  rw [peb]
  exact Nat.sub_add_cancel (h.out_le v)

/-- L-S Invariant (2): on a reachable orientation, the subset-level pebble
count, span, and out-boundary sum to `k * V'.card`. Direct consequence of the
unconditional algebraic identity `PartialOrientation.pebOn_add_span_add_outOn`
(whose hypothesis is exactly Invariant (1)) and `Reachable.out_le`. -/
lemma Reachable.pebOn_add_span_add_outOn {D : PartialOrientation V}
    (h : Reachable k ℓ D) (V' : Finset V) :
    D.pebOn k V' + D.span V' + D.outOn V' = k * V'.card :=
  D.pebOn_add_span_add_outOn k V' (fun v _ => h.out_le v)

/-- Helper: a pair of distinct vertices inside `V'` contributes at most
`pebOn k V'`. Used in `Reachable.pebOn_add_outOn_ge`'s arc-insertion step
to turn the per-edge threshold `peb u + peb v ≥ ℓ + 1` into a subset-level
lower bound when both endpoints lie in `V'`. -/
lemma peb_pair_le_pebOn (D : PartialOrientation V) (k : ℕ) {u v : V} (huv : u ≠ v)
    {V' : Finset V} (hu : u ∈ V') (hv : v ∈ V') :
    D.peb k u + D.peb k v ≤ D.pebOn k V' := by
  rw [show D.peb k u + D.peb k v = ∑ x ∈ ({u, v} : Finset V), D.peb k x from
        (Finset.sum_pair huv).symm, pebOn]
  refine Finset.sum_le_sum_of_subset ?_
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hu
  · rcases Finset.mem_singleton.mp hx with rfl
    exact hv

/-- L-S Invariant (3): on a reachable orientation, `ℓ ≤ pebOn V' + outOn V'`
provided `ℓ ≤ k * V'.card`. This is the substantive piece of
`lem:pebble-game-invariants`. The size hypothesis is the unified shape of
L-S's two regime-dependent cases (`|V'| ≥ 1 ∧ ℓ ≤ k` or `|V'| ≥ 2 ∧ ℓ < 2k`,
both implying `ℓ ≤ k * V'.card`).

Inductive proof:
* Empty: `pebOn V' + outOn V' = V'.card * k`, hypothesised `≥ ℓ`.
* Reverse: `pebOn_add_outOn_reverse_eq` gives subset-level invariance.
* AddArc: `pebOn_add_outOn_addArc_add` shifts the sum by `[u, v ∈ V']`.
  Off the "both inside" branch, the sum is unchanged and the IH closes.
  On the "both inside" branch, `peb_pair_le_pebOn` + the threshold
  precondition `ℓ + 1 ≤ peb u + peb v` give `pebOn V' ≥ ℓ + 1` *before*
  the insertion, which absorbs the `−1` shift. -/
lemma Reachable.pebOn_add_outOn_ge {D : PartialOrientation V}
    (h : Reachable k ℓ D) {V' : Finset V} (h_size : ℓ ≤ k * V'.card) :
    ℓ ≤ D.pebOn k V' + D.outOn V' := by
  induction h with
  | empty =>
    rw [pebOn_empty, outOn_empty, Nat.add_zero, mul_comm V'.card k]
    exact h_size
  | @reverse D' hD' u w p hp hw ih =>
    have hbd : ∀ x ∈ V', D'.out x ≤ k := fun x _ => hD'.out_le x
    have hbd' : ∀ x ∈ V', (D'.reverse p hp).out x ≤ k :=
      fun x _ => (Reachable.reverse hD' p hp hw).out_le x
    rw [D'.pebOn_add_outOn_reverse_eq p hp hbd hbd']
    exact ih
  | @addArc D' hD' a b hab hnotin hnotin_rev ha_out hk ih =>
    have h_combined :=
      D'.pebOn_add_outOn_addArc_add a b hab hnotin_rev hnotin ha_out V'
    by_cases hboth : a ∈ V' ∧ b ∈ V'
    · rw [if_pos hboth] at h_combined
      have h_pair := peb_pair_le_pebOn D' k hab hboth.1 hboth.2
      omega
    · rw [if_neg hboth] at h_combined
      omega

/-- L-S Invariant (4): on a reachable orientation, `span V' + ℓ ≤ k * V'.card`
provided `ℓ ≤ k * V'.card`. Stated additively per project convention (no
ℕ-subtraction in propositions); equivalent to the blueprint's
`span V' ≤ k|V'| - ℓ`. Algebraic consequence of Invariants (2) and (3):
`pebOn + span + outOn = k|V'|` and `ℓ ≤ pebOn + outOn` give the result by
`omega`. -/
lemma Reachable.span_add_le {D : PartialOrientation V}
    (h : Reachable k ℓ D) {V' : Finset V} (h_size : ℓ ≤ k * V'.card) :
    D.span V' + ℓ ≤ k * V'.card := by
  have h2 := h.pebOn_add_span_add_outOn V'
  have h3 := h.pebOn_add_outOn_ge h_size
  omega

end Reachability

end PartialOrientation

end CombinatorialRigidity.PebbleGame
