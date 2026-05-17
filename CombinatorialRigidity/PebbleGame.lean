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

end Reverse

end PartialOrientation

end CombinatorialRigidity.PebbleGame
