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

/-- List view of the out-neighbour set, for feeding into the verified DFS
`Search.reachableFinding`. The DFS primitive takes a `List V`-valued `succ`
function (computable; see `Search/DFS.lean` *Style island*); converting a
`Finset V` to a `List V` goes through `Finset.toList`, which is
noncomputable in mathlib because `Multiset.toList` lifts through a
`Classical`-flavored `Quotient.lift`. The math-layer wrapper
`tryReachPebble` therefore inherits `noncomputable` (consuming `outList`);
IO-driven callers should call the computable workhorse
`tryReachPebbleWith` directly with their own `List`-shaped adjacency and
the matching membership proof, bypassing `outList` entirely. This is the
boundary between the (noncomputable) math layer's `Finset (V × V)`
orientation storage and the (computable) DFS exec layer. -/
noncomputable def outList (v : V) : List V := (D.outNbhd v).toList

lemma mem_outList {v u : V} : u ∈ D.outList v ↔ (v, u) ∈ D.arcs := by
  rw [outList, Finset.mem_toList, mem_outNbhd]

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

/-- The *underlying edge set* `underline(D) ⊆ Sym₂ V` (blueprint
`def:partial-orientation`): the set of unoriented edges of `D`, obtained by
forgetting orientation on each arc. Both `(u, v) ∈ D.arcs` and `(v, u) ∈ D.arcs`
project to the same `Sym2 V` element `s(u, v) = s(v, u)`, so the algorithm's
no-antiparallel invariant means each edge of `underline D` lifts uniquely to an
arc of `D`. Consumed by `thm:pebble-game-soundness` and the wrapper
`runPebbleGame G k ℓ`'s correctness statement, where the invariant
`underline D = E(G)` ties the algorithm's structural state back to the input
graph. -/
def underline : Finset (Sym2 V) :=
  D.arcs.image (fun p => s(p.1, p.2))

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

@[simp] lemma underline_empty : (empty : PartialOrientation V).underline = ∅ := by
  simp [underline]

/-- Membership characterisation of `D.underline` on a `Sym2.mk` representative:
the unoriented edge `s(a, b)` lies in `D.underline` iff at least one of its two
orientations `(a, b)`, `(b, a)` sits in `D.arcs`. -/
lemma mem_underline {a b : V} :
    s(a, b) ∈ D.underline ↔ (a, b) ∈ D.arcs ∨ (b, a) ∈ D.arcs := by
  simp only [underline, Finset.mem_image, Prod.exists]
  constructor
  · rintro ⟨x, y, hxy, h_eq⟩
    rcases (Sym2.eq_iff.mp h_eq) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hxy
    · exact Or.inr hxy
  · rintro (h | h)
    · exact ⟨a, b, h, rfl⟩
    · exact ⟨b, a, h, Sym2.eq_swap⟩

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

/-- Path reversal preserves the underlying unoriented edge set
`underline(D) ⊆ Sym2 V` (blueprint `def:path-reversal`): every arc removed from
`D` along the path is replaced by its reverse, and `s(a, b) = s(b, a)` so the
two cancel under the `Sym2.mk`-image. Consumed by the fold-level
underlying-edge invariant for `runPebbleGameWith`. -/
lemma underline_reverse_eq
    (p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w) (hp : p.IsPath) :
    (D.reverse p hp).underline = D.underline := by
  have h_subset : p.arcsFinset ⊆ D.arcs := D.arcsFinset_subset_arcs p
  have h_decomp : D.arcs = (D.arcs \ p.arcsFinset) ∪ p.arcsFinset :=
    (Finset.sdiff_union_of_subset h_subset).symm
  -- Reduce: `(reverse).arcs.image Sym2.mk = (D.arcs \ path ∪ path.reversed).image Sym2.mk`
  -- and `path.reversed.image Sym2.mk = path.image Sym2.mk` via `Prod.swap` + `Sym2.eq_swap`.
  have h_rev_im :
      p.reversedArcsFinset.image (fun pp : V × V => s(pp.1, pp.2))
        = p.arcsFinset.image (fun pp : V × V => s(pp.1, pp.2)) := by
    rw [p.reversedArcsFinset_eq_image_swap, Finset.image_image]
    refine Finset.image_congr (fun pp _ => ?_)
    simp [Function.comp_apply, Sym2.eq_swap]
  simp only [underline, arcs_reverse, Finset.image_union, h_rev_im]
  conv_rhs => rw [h_decomp, Finset.image_union]

/-- A directed pair `(a, b)` not in `D.arcs` and whose reverse `(b, a)` is also
not in `D.arcs` remains absent from `D.reverse p hp`'s arcs. Path reversal
removes some arcs and inserts their reverses; an arc `(a, b)` could re-enter
only if `(b, a)` was on the path (hence in `D.arcs`), so the second hypothesis
rules this out. Consumed by `tryAddEdge`'s recursive call to thread the
"candidate edge fresh" preconditions across path-reversal steps. -/
lemma notMem_arcs_reverse_of_notMem
    (p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w) (hp : p.IsPath)
    {a b : V} (h : (a, b) ∉ D.arcs) (h_rev : (b, a) ∉ D.arcs) :
    (a, b) ∉ (D.reverse p hp).arcs := by
  rw [arcs_reverse, Finset.mem_union, Finset.mem_sdiff]
  rintro (⟨h_in, _⟩ | h_rev')
  · exact h h_in
  · rw [p.mem_reversedArcsFinset_iff] at h_rev'
    exact h_rev (p.mem_arcsFinset_imp h_rev')

/-- Path reversal preserves the per-vertex out-degree bound `D.out x ≤ k`,
provided the tail's out-degree was strictly below `k` (the algorithmic
precondition that makes the new tail-source arc fit within budget). The only
vertex whose out-count can rise is the path's tail `w`, and the hypothesis
`D.out w < k` absorbs the `+1`. Consumed by `tryAddEdge`'s recursive call to
thread Invariant (1)'s out-degree bound across path-reversal steps. -/
lemma out_reverse_le_of_outle
    (p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w) (hp : p.IsPath)
    {k : ℕ} (h_outle : ∀ x, D.out x ≤ k) (hw : D.out w < k) (x : V) :
    (D.reverse p hp).out x ≤ k := by
  have h_add := D.out_reverse_add p hp x
  have h_x := h_outle x
  -- The unified equation `(reverse).out x + L = D.out x + R` with `L, R ∈ {0, 1}`
  -- means `(reverse).out x ≤ D.out x + 1`, with the `+1` only when `x = w`.
  split_ifs at h_add with hL hR hR
  all_goals try omega
  -- The remaining case is `hL = false, hR = true`: `x ∈ vertices ∧ x ≠ u` (so on
  -- path but ≠ u), and `¬(x ∈ vertices ∧ x ≠ w)` (so x = w, since x ∈ vertices).
  have hxw : x = w := by
    by_contra hne
    exact hL ⟨hR.1, hne⟩
  rw [hxw] at h_add ⊢
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

/-- Arc insertion adds exactly one unoriented edge to `underline(D)`: the new
edge `s(u, v)` (blueprint `def:arc-insertion`). The `Finset.insert` is a
genuine extension iff the edge `s(u, v)` was absent before, which holds in the
`tryAddEdge` context (where both `(u, v) ∉ D.arcs` and `(v, u) ∉ D.arcs` are
preconditions, so neither orientation lifts to a representative of `s(u, v)`
in `D.underline`); the equation itself holds unconditionally on the
`(u, v) ∉ D.arcs` hypothesis because `Finset.image_insert` is unconditional.
Consumed by the fold-level underlying-edge invariant for
`runPebbleGameWith`. -/
lemma underline_addArc (u v : V) (huv : u ≠ v) (hnotin_rev : (v, u) ∉ D.arcs) :
    (D.addArc u v huv hnotin_rev).underline = insert s(u, v) D.underline := by
  simp [underline, arcs_addArc, Finset.image_insert]

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

/-- L-S Lemma 13 (algebraic core): given a reachable orientation `D` and a
candidate edge `{u, v}` whose endpoints sit inside a finset `V'` closed under
`D`'s outgoing arcs (`D.outOn V' = 0`), if inserting `{u, v}` would still
satisfy the span-sparsity bound on `V'` but the two endpoints together hold
fewer than `ℓ + 1` free pebbles, then some other vertex of `V'` carries a
free pebble.

Invariant (2) under `outOn V' = 0` collapses to
`pebOn k V' + span V' = k * V'.card`; the post-insertion span bound
`span V' + 1 + ℓ ≤ k * V'.card` lifts `pebOn k V'` to `≥ ℓ + 1`, exceeding
the below-threshold `peb u + peb v < ℓ + 1`. The slack lives on
`V' \ {u, v}`, so some `w` there has positive pebble count.

This is the algorithm-side algebraic core of
`lem:pebble-game-independent-brings-pebble`. Callers
(`tryAddEdgeWith`'s completeness side, downstream) discharge the
post-insertion span bound from a `SimpleGraph` sparsity hypothesis via the
`underline` / `span_eq_ncard_edgesIn` bridge; the natural `V'` is
`Reach_D(u) ∪ Reach_D(v)`, for which `outOn V' = 0` from closure under
out-arcs. Lee–Streinu Lemma 13. -/
lemma Reachable.independent_brings_pebble
    {D : PartialOrientation V} (hR : Reachable k ℓ D)
    {u v : V} (huv : u ≠ v)
    {V' : Finset V} (hu : u ∈ V') (hv : v ∈ V')
    (h_closed : D.outOn V' = 0)
    (h_sparse : D.span V' + 1 + ℓ ≤ k * V'.card)
    (h_below : D.peb k u + D.peb k v < ℓ + 1) :
    ∃ w ∈ V', w ≠ u ∧ w ≠ v ∧ 0 < D.peb k w := by
  have h_inv2 := hR.pebOn_add_span_add_outOn V'
  have h_pebOn : ℓ + 1 ≤ D.pebOn k V' := by omega
  have huv_sub : ({u, v} : Finset V) ⊆ V' := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hu
    · rcases Finset.mem_singleton.mp hx with rfl
      exact hv
  have h_sdiff : ∑ x ∈ V' \ ({u, v} : Finset V), D.peb k x +
                   ∑ x ∈ ({u, v} : Finset V), D.peb k x =
                 D.pebOn k V' := by
    rw [pebOn]; exact Finset.sum_sdiff huv_sub
  have h_pair : ∑ x ∈ ({u, v} : Finset V), D.peb k x = D.peb k u + D.peb k v :=
    Finset.sum_pair huv
  have h_pos : 0 < ∑ w ∈ V' \ ({u, v} : Finset V), D.peb k w := by omega
  obtain ⟨w, hw_mem, hw_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h_pos.ne'
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hw_mem
  refine ⟨w, hw_mem.1, ?_, ?_, Nat.pos_of_ne_zero hw_ne⟩
  · intro heq; exact hw_mem.2 (Or.inl heq)
  · intro heq; exact hw_mem.2 (Or.inr heq)

end Reachability

/-! ### Try-reach-pebble: DFS with path reversal

The computable workhorse `tryReachPebbleWith D P v succ h_succ` runs the
verified DFS `Search.reachableFinding` along a caller-supplied
out-neighbour enumeration `succ : V → List V` (with a propositional
witness `h_succ` that `succ` matches `D`'s outgoing-arc relation); on
success it bundles the witness walk and target into a
`TryReachPebbleResult D P v`, on failure it returns `none`. The math-layer
convenience `tryReachPebble D P v` is a one-line noncomputable wrapper
plugging in `succ := D.outList`.

Splitting the API this way lets IO-driven callers (parser → algorithm →
output pipelines, in which the user already holds adjacency data in
`List`-shape) call `tryReachPebbleWith` directly with their own enumeration
and stay fully computable, while abstract math-layer use of `tryReachPebble`
remains terse. Downstream soundness/completeness theorems will live on
`tryReachPebbleWith` and inherit to `tryReachPebble` for free.

Cf. Lee–Streinu §3 (one pebble-search attempt inside `tryAddEdge`),
blueprint `def:tryReachPebble`. -/

section TryReachPebble

variable [Fintype V]

open CombinatorialRigidity.Search

/-- Certificate-form result returned by a successful `tryReachPebble` /
`tryReachPebbleWith` run: the target vertex `target` reached from `v` along
`D.arcs`-arrows, the witness walk `walk`, a proof `isPath` that the walk is
simple, and a proof `hP` that the target satisfies the predicate. The
caller obtains the path-reversed orientation via
`TryReachPebbleResult.newOrient`. -/
structure TryReachPebbleResult (D : PartialOrientation V) (P : V → Bool) (v : V) where
  /-- Target vertex reached. -/
  target : V
  /-- Witness walk along the outgoing-arc relation of `D`. -/
  walk : DirectedWalk (fun a b => (a, b) ∈ D.arcs) v target
  /-- The witness walk is simple. -/
  isPath : walk.IsPath
  /-- The target satisfies the predicate. -/
  hP : P target = true

/-- Computable workhorse for `tryReachPebble`. Runs the verified DFS
`Search.reachableFinding` with a caller-supplied out-neighbour enumeration
`succ : V → List V` plus a propositional witness `h_succ` that `succ`
agrees with `D`'s outgoing-arc relation; transports the resulting walk to
the orientation's arc relation via `DirectedWalk.mapRel` and packages the
output as a `TryReachPebbleResult D P v`.

Stays computable as long as `succ` is. This is the form an IO pipeline
calls directly with a `List`-shaped adjacency built from input data;
soundness / completeness theorems will land here and inherit to the
math-layer wrapper `tryReachPebble`. Lee–Streinu §3, blueprint
`def:tryReachPebble`. -/
def tryReachPebbleWith (P : V → Bool) (v : V)
    (succ : V → List V) (h_succ : ∀ {a b : V}, b ∈ succ a ↔ (a, b) ∈ D.arcs) :
    Option (TryReachPebbleResult D P v) :=
  match h_eq : reachableFinding succ P v with
  | none => none
  | some ⟨w, p⟩ =>
    have hsound := reachableFinding_sound h_eq
    some
      { target := w
        walk := p.mapRel (fun hab => h_succ.mp hab)
        isPath := (DirectedWalk.mapRel_isPath_iff _ p).mpr hsound.2
        hP := hsound.1 }

/-- Math-layer convenience: specialise `tryReachPebbleWith` to
`succ := D.outList`, with the propositional witness supplied by
`D.mem_outList`. `noncomputable` because `D.outList` goes through
`Finset.toList` (see `outList`); IO callers should use `tryReachPebbleWith`
directly with a list-shaped adjacency to stay computable. -/
noncomputable def tryReachPebble (P : V → Bool) (v : V) :
    Option (TryReachPebbleResult D P v) :=
  D.tryReachPebbleWith P v D.outList (fun {_ _} => D.mem_outList)

/-- The orientation produced by the path-reversal move along the witness
walk of a successful `tryReachPebble` / `tryReachPebbleWith` result.
Convenience for callers threading the result into `tryAddEdge`'s outer
loop; equivalent to `D.reverse r.walk r.isPath`. -/
def TryReachPebbleResult.newOrient {D : PartialOrientation V}
    {P : V → Bool} {v : V} (r : TryReachPebbleResult D P v) :
    PartialOrientation V :=
  D.reverse r.walk r.isPath

omit [Fintype V] in
/-- `Reachable k ℓ` is preserved by a single DFS-plus-reversal step: given a
reachable input orientation `D` and a target with strictly-positive free pebble
count (i.e. `D.out r.target < k`), the post-reversal orientation
`r.newOrient = D.reverse r.walk r.isPath` is again reachable, via the
`Reachable.reverse` constructor. The `h_target` hypothesis is supplied by
`tryAddEdgeWith`'s predicate `0 < D.peb k w ∧ ...` at the recursive call. -/
lemma TryReachPebbleResult.reachable_newOrient {D : PartialOrientation V}
    {P : V → Bool} {v : V} (r : TryReachPebbleResult D P v) {k ℓ : ℕ}
    (hD : Reachable k ℓ D) (h_target : D.out r.target < k) :
    Reachable k ℓ r.newOrient :=
  Reachable.reverse hD r.walk r.isPath h_target

omit [Fintype V] in
/-- The underlying unoriented edge set is preserved by a single
DFS-plus-reversal step: `r.newOrient = D.reverse r.walk r.isPath` has the same
`underline` as `D`. Direct corollary of `underline_reverse_eq`. -/
lemma TryReachPebbleResult.underline_newOrient_eq {D : PartialOrientation V}
    {P : V → Bool} {v : V} (r : TryReachPebbleResult D P v) :
    r.newOrient.underline = D.underline :=
  D.underline_reverse_eq r.walk r.isPath

/-- **Completeness of `tryReachPebbleWith`.** If the DFS-driven pebble search
returned `none`, then no vertex `w` reachable from `v` along `D`'s out-arcs
satisfies the predicate `P`. The orientation-side `ReflTransGen` of
`fun a b => (a, b) ∈ D.arcs` is bridged to the algorithm-side `ReflTransGen`
of `fun a b => b ∈ succ a` by `h_succ`, after which
`Search.reachableFinding_complete` produces a contradiction with the `none`
result. Used by `tryAddEdgeWith_isSome` to discharge the case where both
endpoint-DFS searches fail. -/
lemma tryReachPebbleWith_eq_none_imp {D : PartialOrientation V}
    {P : V → Bool} {v : V}
    {succ : V → List V}
    (h_succ : ∀ {a b : V}, b ∈ succ a ↔ (a, b) ∈ D.arcs)
    (h_none : D.tryReachPebbleWith P v succ h_succ = none)
    {w : V}
    (hreach : Relation.ReflTransGen (fun a b => (a, b) ∈ D.arcs) v w) :
    P w ≠ true := by
  have hreach' : Relation.ReflTransGen (fun a b => b ∈ succ a) v w := by
    induction hreach with
    | refl => exact .refl
    | tail _ hrel ih => exact ih.tail (h_succ.mpr hrel)
  intro hPw
  obtain ⟨w', p', hsome⟩ := reachableFinding_complete ⟨w, hreach', hPw⟩
  have hrf_none : reachableFinding succ P v = none := by
    unfold tryReachPebbleWith at h_none
    split at h_none
    · assumption
    · simp at h_none
  rw [hsome] at hrf_none
  cases hrf_none

end TryReachPebble

/-! ### Try-add-edge: outer loop driving DFS + path reversal + insertion

`tryAddEdgeWith D k ℓ u v ... toSucc h_toSucc` processes a candidate edge
`{u, v}` against the orientation `D` (blueprint `def:tryAddEdge`):

* If `peb k u + peb k v ≥ ℓ + 1`: insert the directed arc, orienting `(u, v)`
  when `0 < peb k u` (free pebble at `u`) and `(v, u)` otherwise; return the
  updated orientation.
* Else: search for a vertex `w ≠ u, v` with a free pebble reachable from `u`
  along `D`'s out-arcs via `tryReachPebbleWith`. On success, reverse the path
  to send a pebble back to `u` and recurse. If `u`-search fails, try the
  symmetric `v`-search; on success, reverse + recurse. If both DFS attempts
  fail, return `none`.

Termination measure: `(ℓ + 1) - (D.peb k u + D.peb k v)`, which strictly
decreases per successful reversal — the predicate's `w ≠ u, v` clauses ensure
the head endpoint of the reversed path is `u` (resp. `v`) and the tail is
neither, so `out_reverse_head` raises `peb k u` (resp. `peb k v`) by exactly
`1` while leaving the other endpoint's pebble count untouched.

The caller supplies the out-neighbour enumeration `toSucc D'` for *every*
intermediate orientation `D'` the recursion can encounter — necessary because
path reversal mutates `D.arcs`. The agreement witness `h_toSucc` is the
universally-quantified analogue of `tryReachPebbleWith`'s `h_succ`. As with
the DFS layer, the math-layer convenience `tryAddEdge` plugs in
`toSucc D' := D'.outList`, inheriting `noncomputable` from `outList`'s use of
`Finset.toList`; IO callers staying inside the computable layer should invoke
`tryAddEdgeWith` directly with a `List`-shaped adjacency they already hold.

The failure branch returns `none` rather than the reach-closure subset
described in the blueprint's prose; extracting the blocking-witness subset
`Reach_D(u) ∪ Reach_D(v)` from the failure state is a separate computation
(left to a follow-up: a `reachClosure` helper in `Search/DFS.lean`,
post-composed at the failure site). This keeps the algorithm's signature
minimal and matches the `Option`-shape of `tryReachPebbleWith`. -/

section TryAddEdge

variable [Fintype V]

open CombinatorialRigidity.Search

/-- Computable workhorse for the pebble-game's outer-loop combinator
`tryAddEdge`. See the section docstring for the algorithm description; the
math-layer convenience `tryAddEdge` is a one-line `noncomputable` wrapper
plugging in `toSucc := (·.outList)`. Blueprint `def:tryAddEdge`. -/
def tryAddEdgeWith
    (D : PartialOrientation V) (k ℓ : ℕ) (u v : V) (huv : u ≠ v)
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (h_outle : ∀ x, D.out x ≤ k)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs) :
    Option (PartialOrientation V) :=
  if h_thr : ℓ + 1 ≤ D.peb k u + D.peb k v then
    -- Threshold met: insert the arc. Orient based on which endpoint has a free
    -- pebble (at least one does, since `ℓ + 1 ≥ 1`).
    if 0 < D.peb k u then
      some (D.addArc u v huv hnotin_rev)
    else
      some (D.addArc v u huv.symm hnotin)
  else
    -- Below threshold: try DFS for a free pebble reachable from `u`, then `v`.
    let P : V → Bool := fun w =>
      decide (0 < D.peb k w) && decide (w ≠ u) && decide (w ≠ v)
    match D.tryReachPebbleWith P u (toSucc D) (h_toSucc D) with
    | some r =>
      tryAddEdgeWith r.newOrient k ℓ u v huv
        (D.notMem_arcs_reverse_of_notMem r.walk r.isPath hnotin hnotin_rev)
        (D.notMem_arcs_reverse_of_notMem r.walk r.isPath hnotin_rev hnotin)
        (fun x => by
          have h_target : D.out r.target < k := by
            have h := r.hP
            simp only [P, Bool.and_eq_true, decide_eq_true_eq] at h
            rw [peb] at h
            omega
          exact D.out_reverse_le_of_outle r.walk r.isPath h_outle h_target x)
        toSucc h_toSucc
    | none =>
      match D.tryReachPebbleWith P v (toSucc D) (h_toSucc D) with
      | some r =>
        tryAddEdgeWith r.newOrient k ℓ u v huv
          (D.notMem_arcs_reverse_of_notMem r.walk r.isPath hnotin hnotin_rev)
          (D.notMem_arcs_reverse_of_notMem r.walk r.isPath hnotin_rev hnotin)
          (fun x => by
            have h_target : D.out r.target < k := by
              have h := r.hP
              simp only [P, Bool.and_eq_true, decide_eq_true_eq] at h
              rw [peb] at h
              omega
            exact D.out_reverse_le_of_outle r.walk r.isPath h_outle h_target x)
          toSucc h_toSucc
      | none => none
  termination_by (ℓ + 1) - (D.peb k u + D.peb k v)
  decreasing_by
    -- u-DFS success branch: walk `u → r.target` with `r.target ≠ u, v`,
    -- so reversal raises `peb k u` by 1 and leaves `peb k v` fixed.
    · simp only [TryReachPebbleResult.newOrient]
      have h := r.hP
      simp only [P, Bool.and_eq_true, decide_eq_true_eq] at h
      have h_ne_u : r.target ≠ u := h.1.2
      have h_ne_v : r.target ≠ v := h.2
      have hpos : 0 < r.walk.length :=
        DirectedWalk.length_pos_of_ne (fun heq => h_ne_u heq.symm)
      have h_peb_u : (D.reverse r.walk r.isPath).peb k u = D.peb k u + 1 :=
        D.peb_reverse_head r.walk r.isPath hpos k (h_outle u)
      have h_peb_v : (D.reverse r.walk r.isPath).peb k v = D.peb k v :=
        D.peb_reverse_of_not_endpoint r.walk r.isPath k huv.symm
          (fun heq => h_ne_v heq.symm)
      omega
    -- v-DFS success branch: walk `v → r.target` with `r.target ≠ u, v`,
    -- so reversal raises `peb k v` by 1 and leaves `peb k u` fixed.
    · simp only [TryReachPebbleResult.newOrient]
      have h := r.hP
      simp only [P, Bool.and_eq_true, decide_eq_true_eq] at h
      have h_ne_u : r.target ≠ u := h.1.2
      have h_ne_v : r.target ≠ v := h.2
      have hpos : 0 < r.walk.length :=
        DirectedWalk.length_pos_of_ne (fun heq => h_ne_v heq.symm)
      have h_peb_v : (D.reverse r.walk r.isPath).peb k v = D.peb k v + 1 :=
        D.peb_reverse_head r.walk r.isPath hpos k (h_outle v)
      have h_peb_u : (D.reverse r.walk r.isPath).peb k u = D.peb k u :=
        D.peb_reverse_of_not_endpoint r.walk r.isPath k huv h_ne_u.symm
      omega

/-- Math-layer convenience: specialise `tryAddEdgeWith` to
`toSucc := (·.outList)`, with the agreement witness supplied uniformly by
`mem_outList`. `noncomputable` because `outList` goes through `Finset.toList`;
IO callers should use `tryAddEdgeWith` directly with a list-shaped adjacency to
stay computable. Blueprint `def:tryAddEdge`. -/
noncomputable def tryAddEdge
    (D : PartialOrientation V) (k ℓ : ℕ) (u v : V) (huv : u ≠ v)
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (h_outle : ∀ x, D.out x ≤ k) :
    Option (PartialOrientation V) :=
  tryAddEdgeWith D k ℓ u v huv hnotin hnotin_rev h_outle
    (fun D' => D'.outList) (fun D' {_ _} => D'.mem_outList)

/-- `tryAddEdgeWith` preserves `Reachable k ℓ`: if the input orientation `D`
is reachable and the call returns `some D'`, then `D'` is also reachable. By
induction on the function's recursion structure
(`tryAddEdgeWith.induct`); the threshold-accept branches close via the
`Reachable.addArc` constructor (the threshold + the structural `h_outle`
bound supply the constructor's `D.out _ < k` precondition), and the
DFS-success branches close by composing
`TryReachPebbleResult.reachable_newOrient` with the inductive hypothesis. -/
lemma tryAddEdgeWith_reachable {k ℓ : ℕ} {u v : V} (huv : u ≠ v)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    {D : PartialOrientation V}
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (h_outle : ∀ x, D.out x ≤ k)
    (hD : Reachable k ℓ D)
    {D' : PartialOrientation V}
    (h : D.tryAddEdgeWith k ℓ u v huv hnotin hnotin_rev h_outle toSucc h_toSucc
      = some D') :
    Reachable k ℓ D' := by
  induction D, hnotin, hnotin_rev, h_outle using
    tryAddEdgeWith.induct (k := k) (ℓ := ℓ) (huv := huv)
      (toSucc := toSucc) (h_toSucc := h_toSucc)
    generalizing D'
  case case1 D hnotin hnotin_rev h_outle hthr hpu_pos =>
    -- Threshold met, free pebble at `u`: result is `D.addArc u v huv hnotin_rev`.
    rw [tryAddEdgeWith, dif_pos hthr, if_pos hpu_pos] at h
    have h_out_u : D.out u < k := by
      have h1 := h_outle u
      have h2 : D.peb k u = k - D.out u := rfl
      omega
    cases h
    exact Reachable.addArc hD huv hnotin hnotin_rev h_out_u hthr
  case case2 D hnotin hnotin_rev h_outle hthr hpu_neg =>
    -- Threshold met, no free pebble at `u`: result is `D.addArc v u huv.symm hnotin`.
    rw [tryAddEdgeWith, dif_pos hthr, if_neg hpu_neg] at h
    have hpu_zero : D.peb k u = 0 := Nat.eq_zero_of_not_pos hpu_neg
    have h_out_v : D.out v < k := by
      have h1 := h_outle v
      have h2 : D.peb k v = k - D.out v := rfl
      omega
    cases h
    refine Reachable.addArc hD huv.symm hnotin_rev hnotin h_out_v ?_
    have : D.peb k v + D.peb k u = D.peb k u + D.peb k v := Nat.add_comm _ _
    omega
  case case3 D hnotin hnotin_rev h_outle hthr P r hr_eq ih =>
    -- Below threshold, u-DFS succeeds: recurse on `r.newOrient`.
    rw [tryAddEdgeWith, dif_neg hthr] at h
    simp only at h
    rw [hr_eq] at h
    -- Establish `Reachable k ℓ r.newOrient` from `r.hP`.
    have hP_decomp : (0 < D.peb k r.target ∧ r.target ≠ u) ∧ r.target ≠ v := by
      have := r.hP; simp only [P, Bool.and_eq_true, decide_eq_true_eq] at this; exact this
    have h_target : D.out r.target < k := by
      have h1 := h_outle r.target
      have h2 : D.peb k r.target = k - D.out r.target := rfl
      have := hP_decomp.1.1
      omega
    have hR_new : Reachable k ℓ r.newOrient := r.reachable_newOrient hD h_target
    exact ih hR_new h
  case case4 D hnotin hnotin_rev h_outle hthr P hu_none r hr_eq ih =>
    -- Below threshold, u-DFS fails, v-DFS succeeds: recurse on `r.newOrient`.
    rw [tryAddEdgeWith, dif_neg hthr] at h
    simp only at h
    rw [hu_none, hr_eq] at h
    have hP_decomp : (0 < D.peb k r.target ∧ r.target ≠ u) ∧ r.target ≠ v := by
      have := r.hP; simp only [P, Bool.and_eq_true, decide_eq_true_eq] at this; exact this
    have h_target : D.out r.target < k := by
      have h1 := h_outle r.target
      have h2 : D.peb k r.target = k - D.out r.target := rfl
      have := hP_decomp.1.1
      omega
    have hR_new : Reachable k ℓ r.newOrient := r.reachable_newOrient hD h_target
    exact ih hR_new h
  case case5 D hnotin hnotin_rev h_outle hthr P hu_none hv_none =>
    -- Both DFS attempts fail: result is `none`, contradicting `h`.
    rw [tryAddEdgeWith, dif_neg hthr] at h
    dsimp only at h
    rw [hu_none, hv_none] at h
    exact nomatch h

/-- `tryAddEdgeWith` on accept rewrites the underlying unoriented edge set as
`insert s(u, v) D.underline`. By the same `tryAddEdgeWith.induct` dispatch as
`tryAddEdgeWith_reachable`: both threshold-accept branches close via
`underline_addArc` (with `s(u, v) = s(v, u)` collapsing the orientation choice
to the same `Sym2` element); the DFS-success branches compose
`TryReachPebbleResult.underline_newOrient_eq` with the inductive hypothesis;
the both-DFS-fail branch is contradictory by `nomatch`. -/
lemma tryAddEdgeWith_underline {k ℓ : ℕ} {u v : V} (huv : u ≠ v)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    {D : PartialOrientation V}
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (h_outle : ∀ x, D.out x ≤ k)
    {D' : PartialOrientation V}
    (h : D.tryAddEdgeWith k ℓ u v huv hnotin hnotin_rev h_outle toSucc h_toSucc
      = some D') :
    D'.underline = insert s(u, v) D.underline := by
  induction D, hnotin, hnotin_rev, h_outle using
    tryAddEdgeWith.induct (k := k) (ℓ := ℓ) (huv := huv)
      (toSucc := toSucc) (h_toSucc := h_toSucc)
    generalizing D'
  case case1 D hnotin hnotin_rev h_outle hthr hpu_pos =>
    -- Threshold met, free pebble at `u`: insert `(u, v)`.
    rw [tryAddEdgeWith, dif_pos hthr, if_pos hpu_pos] at h
    cases h
    exact D.underline_addArc u v huv hnotin_rev
  case case2 D hnotin hnotin_rev h_outle hthr hpu_neg =>
    -- Threshold met, no free pebble at `u`: insert `(v, u)`. `s(v, u) = s(u, v)`.
    rw [tryAddEdgeWith, dif_pos hthr, if_neg hpu_neg] at h
    cases h
    rw [D.underline_addArc v u huv.symm hnotin, Sym2.eq_swap]
  case case3 D hnotin hnotin_rev h_outle hthr P r hr_eq ih =>
    -- Below threshold, u-DFS succeeds: recurse on `r.newOrient`, transport via
    -- `underline_newOrient_eq`.
    rw [tryAddEdgeWith, dif_neg hthr] at h
    simp only at h
    rw [hr_eq] at h
    rw [ih h, r.underline_newOrient_eq]
  case case4 D hnotin hnotin_rev h_outle hthr P hu_none r hr_eq ih =>
    rw [tryAddEdgeWith, dif_neg hthr] at h
    simp only at h
    rw [hu_none, hr_eq] at h
    rw [ih h, r.underline_newOrient_eq]
  case case5 D hnotin hnotin_rev h_outle hthr P hu_none hv_none =>
    rw [tryAddEdgeWith, dif_neg hthr] at h
    dsimp only at h
    rw [hu_none, hv_none] at h
    exact nomatch h

end TryAddEdge

/-! ### Run-pebble-game: fold tryAddEdge over an edge enumeration

`runPebbleGameWith D k ℓ toSucc h_toSucc edges` folds `tryAddEdgeWith` over a
caller-supplied `List (V × V)` of candidate ordered pairs starting from the
orientation `D`, threading the orientation through each call. For each pair
`(u, v)`:

* If `u = v` (loop), or either `(u, v)` or `(v, u)` is already in `D.arcs`
  (parallel / antiparallel duplicate of an already-accepted edge), or the
  algorithmic invariant `∀ x, D.out x ≤ k` fails on the current `D`, the
  step is a no-op (skip + recurse on the unchanged `D`). The first three
  cases are decided per `[DecidableEq V]`; the fourth uses `[Fintype V]`'s
  decidable universal quantifier.
* Otherwise call `D.tryAddEdgeWith`; on `some D'` recurse from `D'`, on
  `none` propagate `none` as the whole-run output.

Termination is by `edges.length`, which strictly decreases per recursive call
(cf. Lee–Streinu §3 outer fold).

The math-layer convenience `runPebbleGame G k ℓ` is a noncomputable wrapper
taking a `SimpleGraph V` (with `[Fintype G.edgeSet]`): it enumerates
`G.edgeFinset.toList`, projects each `Sym2 V` to a representative ordered pair
via `Quot.out`, and runs `runPebbleGameWith` from `empty` with the default
`toSucc := (·.outList)`. The wrapper inherits `noncomputable` from `outList`
(`Finset.toList`) and `Quot.out` (`Classical.choice`); IO-driven callers can
invoke `runPebbleGameWith` directly with their own `List (V × V)` enumeration
and a list-shaped adjacency and stay fully computable.

The failure branch returns `none` rather than the blocking-witness subset
described in the blueprint's prose; extracting `Reach_D(u) ∪ Reach_D(v)`
from the failure state is a separate computation (deferred to a planned
`reachClosure` helper in `Search/DFS.lean`, post-composed at the failure
site). This keeps the algorithm's signature minimal and matches the
`Option`-shape of `tryAddEdgeWith`. Blueprint `def:runPebbleGame`. -/

section RunPebbleGame

variable [Fintype V]

open CombinatorialRigidity.Search

/-- Computable workhorse for the pebble-game's outer fold. See the section
docstring for the algorithm description; the math-layer convenience
`runPebbleGame` is a `noncomputable` wrapper. Blueprint `def:runPebbleGame`. -/
def runPebbleGameWith
    (D : PartialOrientation V) (k ℓ : ℕ)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs) :
    List (V × V) → Option (PartialOrientation V)
  | [] => some D
  | (u, v) :: es =>
      if h : u ≠ v ∧ (u, v) ∉ D.arcs ∧ (v, u) ∉ D.arcs ∧ (∀ x, D.out x ≤ k) then
        match D.tryAddEdgeWith k ℓ u v h.1 h.2.1 h.2.2.1 h.2.2.2 toSucc h_toSucc with
        | some D' => D'.runPebbleGameWith k ℓ toSucc h_toSucc es
        | none => none
      else
        D.runPebbleGameWith k ℓ toSucc h_toSucc es

/-- Math-layer convenience: enumerate `G.edgeFinset` as a `List (V × V)` via
`G.edgeFinset.toList.map Quot.out`, then run `runPebbleGameWith` from the
empty orientation with the default `toSucc := (·.outList)`. `noncomputable`
because of `Finset.toList` (under `outList` and the edge enumeration) and
`Quot.out` (the `Sym2 V → V × V` projection). IO callers should call
`runPebbleGameWith` directly with their own list-shaped data to stay
computable. Blueprint `def:runPebbleGame`. -/
noncomputable def runPebbleGame (G : SimpleGraph V) [Fintype G.edgeSet]
    (k ℓ : ℕ) : Option (PartialOrientation V) :=
  (empty : PartialOrientation V).runPebbleGameWith k ℓ
    (fun D' => D'.outList) (fun D' {_ _} => D'.mem_outList)
    (G.edgeFinset.toList.map Quot.out)

/-- `runPebbleGameWith` preserves `Reachable k ℓ`: if the input orientation `D`
is reachable and the fold returns `some D'`, then `D'` is also reachable. By
structural induction on the edge list; the per-step glue is
`tryAddEdgeWith_reachable` on accept-branch hits and the IH directly on
no-op (skipped) edges. -/
lemma runPebbleGameWith_reachable {k ℓ : ℕ}
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs) :
    ∀ (edges : List (V × V)) {D : PartialOrientation V} (_ : Reachable k ℓ D)
      {D' : PartialOrientation V},
      D.runPebbleGameWith k ℓ toSucc h_toSucc edges = some D' →
      Reachable k ℓ D'
  | [], D, hD, D', h => by
    rw [runPebbleGameWith] at h
    cases h
    exact hD
  | (u, v) :: es, D, hD, D', h => by
    rw [runPebbleGameWith] at h
    by_cases hcond : u ≠ v ∧ (u, v) ∉ D.arcs ∧ (v, u) ∉ D.arcs ∧ (∀ x, D.out x ≤ k)
    · rw [dif_pos hcond] at h
      match heq : D.tryAddEdgeWith k ℓ u v hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2
          toSucc h_toSucc with
      | some Dmid =>
        rw [heq] at h
        have hR_mid : Reachable k ℓ Dmid :=
          tryAddEdgeWith_reachable hcond.1 toSucc h_toSucc hcond.2.1 hcond.2.2.1
            hcond.2.2.2 hD heq
        exact runPebbleGameWith_reachable toSucc h_toSucc es hR_mid h
      | none =>
        rw [heq] at h
        exact nomatch h
    · rw [dif_neg hcond] at h
      exact runPebbleGameWith_reachable toSucc h_toSucc es hD h

/-- `runPebbleGameWith` tracks the underlying unoriented edge set across the
fold (infrastructure piece (ii) for `thm:pebble-game-soundness`). On success,
`D'.underline` lies between the input `D.underline` (monotone: nothing is ever
removed by the move sequence — `underline_reverse_eq` shows reversal preserves
it, `underline_addArc` shows arc insertion grows it) and the union with the
`Sym2.mk`-image of the candidate edge list (upper bound: every edge of
`D'.underline` either started in `D.underline` or got accepted from a list
entry; skipped entries either were already in `D.underline` or did not
contribute, and accept-branch hits add exactly one new `s(u, v)` per
`tryAddEdgeWith_underline`).

By structural induction on the edge list; the per-step glue is
`tryAddEdgeWith_underline` on accept-branch hits and the IH directly on no-op
(skipped) edges. -/
lemma runPebbleGameWith_underline_subset {k ℓ : ℕ}
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs) :
    ∀ (edges : List (V × V)) {D D' : PartialOrientation V},
      D.runPebbleGameWith k ℓ toSucc h_toSucc edges = some D' →
      D.underline ⊆ D'.underline ∧
      D'.underline ⊆ D.underline ∪ (edges.map (fun p : V × V => s(p.1, p.2))).toFinset
  | [], D, D', h => by
    rw [runPebbleGameWith] at h
    cases h
    refine ⟨subset_refl _, ?_⟩
    simp
  | (u, v) :: es, D, D', h => by
    rw [runPebbleGameWith] at h
    by_cases hcond : u ≠ v ∧ (u, v) ∉ D.arcs ∧ (v, u) ∉ D.arcs ∧ (∀ x, D.out x ≤ k)
    · rw [dif_pos hcond] at h
      match heq : D.tryAddEdgeWith k ℓ u v hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2
          toSucc h_toSucc with
      | some Dmid =>
        rw [heq] at h
        have h_mid : Dmid.underline = insert s(u, v) D.underline :=
          tryAddEdgeWith_underline hcond.1 toSucc h_toSucc
            hcond.2.1 hcond.2.2.1 hcond.2.2.2 heq
        obtain ⟨ih_mono, ih_upper⟩ :=
          runPebbleGameWith_underline_subset toSucc h_toSucc es h
        refine ⟨?_, ?_⟩
        · -- D.underline ⊆ Dmid.underline (= insert s(u,v) D.underline) ⊆ D'.underline.
          intro e he
          exact ih_mono (h_mid ▸ Finset.mem_insert_of_mem he)
        · -- D'.underline ⊆ Dmid.underline ∪ (es-image) ⊆ insert s(u,v) D.underline ∪ es-image
          --               ⊆ D.underline ∪ ((u, v) :: es)-image.
          intro e he
          have he' := ih_upper he
          rw [h_mid] at he'
          simp only [List.map_cons, List.toFinset_cons, Finset.mem_union,
            Finset.mem_insert] at he' ⊢
          tauto
      | none =>
        rw [heq] at h
        exact nomatch h
    · rw [dif_neg hcond] at h
      obtain ⟨ih_mono, ih_upper⟩ :=
        runPebbleGameWith_underline_subset toSucc h_toSucc es h
      refine ⟨ih_mono, ?_⟩
      intro e he
      have he' := ih_upper he
      simp only [List.map_cons, List.toFinset_cons, Finset.mem_union,
        Finset.mem_insert] at he' ⊢
      tauto

/-- No-skip-fires converse to `runPebbleGameWith_underline_subset`: under
hypotheses ensuring every runtime check passes at every step (`Reachable k ℓ`
for the out-degree bound; per-edge `p.1 ≠ p.2` for the loop check; per-edge
freshness `s(p.1, p.2) ∉ D.underline` plus pairwise Sym2-distinctness across
the list for the two arc-membership checks), every input edge ends up in
`D'.underline`.

Combined with `runPebbleGameWith_underline_subset` this gives the tight
identity `D'.underline = D.underline ∪ (edges.map s(·,·)).toFinset` at
termination; the wrapper `runPebbleGame G k ℓ` specialises at
`D = empty` to obtain `D'.underline = G.edgeFinset`. -/
lemma runPebbleGameWith_mem_underline {k ℓ : ℕ}
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs) :
    ∀ (edges : List (V × V)) {D : PartialOrientation V} (_hD : Reachable k ℓ D)
      (_hloops : ∀ p ∈ edges, p.1 ≠ p.2)
      (_hfresh : ∀ p ∈ edges, s(p.1, p.2) ∉ D.underline)
      (_hpairwise : edges.Pairwise
        (fun p q : V × V => s(p.1, p.2) ≠ s(q.1, q.2)))
      {D' : PartialOrientation V},
      D.runPebbleGameWith k ℓ toSucc h_toSucc edges = some D' →
      ∀ p ∈ edges, s(p.1, p.2) ∈ D'.underline
  | [], _D, _hD, _hloops, _hfresh, _hpairwise, _D', _h, _p, hp => by
    simp at hp
  | (u, v) :: es, D, hD, hloops, hfresh, hpairwise, D', h, p, hp => by
    have h_uv_ne : u ≠ v := hloops (u, v) (List.mem_cons_self)
    have h_uv_fresh : s(u, v) ∉ D.underline := hfresh (u, v) (List.mem_cons_self)
    have h_uv_arc : (u, v) ∉ D.arcs := fun harc =>
      h_uv_fresh (D.mem_underline.mpr (Or.inl harc))
    have h_vu_arc : (v, u) ∉ D.arcs := fun harc =>
      h_uv_fresh (D.mem_underline.mpr (Or.inr harc))
    have h_outle : ∀ x, D.out x ≤ k := hD.out_le
    have hcond : u ≠ v ∧ (u, v) ∉ D.arcs ∧ (v, u) ∉ D.arcs ∧ (∀ x, D.out x ≤ k) :=
      ⟨h_uv_ne, h_uv_arc, h_vu_arc, h_outle⟩
    obtain ⟨hpw_head, hpw_tail⟩ := List.pairwise_cons.mp hpairwise
    rw [runPebbleGameWith, dif_pos hcond] at h
    match heq : D.tryAddEdgeWith k ℓ u v hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2
        toSucc h_toSucc with
    | some Dmid =>
      rw [heq] at h
      have h_underline_mid : Dmid.underline = insert s(u, v) D.underline :=
        tryAddEdgeWith_underline hcond.1 toSucc h_toSucc
          hcond.2.1 hcond.2.2.1 hcond.2.2.2 heq
      have hR_mid : Reachable k ℓ Dmid :=
        tryAddEdgeWith_reachable hcond.1 toSucc h_toSucc
          hcond.2.1 hcond.2.2.1 hcond.2.2.2 hD heq
      have hloops_es : ∀ q ∈ es, q.1 ≠ q.2 :=
        fun q hq => hloops q (List.mem_cons_of_mem _ hq)
      have hfresh_es : ∀ q ∈ es, s(q.1, q.2) ∉ Dmid.underline := by
        intro q hq
        rw [h_underline_mid, Finset.mem_insert]
        push Not
        exact ⟨(hpw_head q hq).symm, hfresh q (List.mem_cons_of_mem _ hq)⟩
      rcases List.mem_cons.mp hp with rfl | hp_in_es
      · obtain ⟨h_mono, _⟩ :=
          runPebbleGameWith_underline_subset toSucc h_toSucc es h
        exact h_mono (h_underline_mid ▸ Finset.mem_insert_self _ _)
      · exact runPebbleGameWith_mem_underline toSucc h_toSucc es hR_mid hloops_es
          hfresh_es hpw_tail h p hp_in_es
    | none =>
      rw [heq] at h
      exact nomatch h

/-- The wrapper `runPebbleGame G k ℓ` on success produces an orientation whose
underlying unoriented edge set equals `G.edgeFinset`. The ⊆ direction
specialises `runPebbleGameWith_underline_subset` at `D = empty` (its
`underline` is `∅`); the ⊇ direction discharges
`runPebbleGameWith_mem_underline`'s four hypotheses against the input list
`G.edgeFinset.toList.map Quot.out` — no-loops from `not_isDiag_of_mem_edgeSet`,
freshness trivially, pairwise distinctness from `Finset.nodup_toList` and the
Sym2 round-trip `s((Quot.out e).1, (Quot.out e).2) = e`. Closes the
no-skip-fires gap noted in `thm:pebble-game-soundness`'s prose proof. -/
theorem runPebbleGame_underline_eq_edgeFinset {G : SimpleGraph V}
    [Fintype G.edgeSet] {k ℓ : ℕ} {D' : PartialOrientation V}
    (h : runPebbleGame G k ℓ = some D') : D'.underline = G.edgeFinset := by
  rw [runPebbleGame] at h
  set edges := G.edgeFinset.toList.map (Quot.out : Sym2 V → V × V) with hedges
  -- The Sym2-image of `edges` is `G.edgeFinset` (round-trip).
  have h_img : (edges.map (fun p : V × V => s(p.1, p.2))).toFinset = G.edgeFinset := by
    rw [hedges, List.map_map]
    have h_id : (fun p : V × V => s(p.1, p.2)) ∘ (Quot.out : Sym2 V → V × V)
        = id := by
      funext e
      exact Quot.out_eq e
    rw [h_id, List.map_id, G.edgeFinset.toList_toFinset]
  -- No loops: each `Quot.out e` for `e ∈ G.edgeFinset` has distinct components.
  have hloops : ∀ p ∈ edges, p.1 ≠ p.2 := by
    intro p hp h_eq
    simp only [hedges, List.mem_map, Finset.mem_toList] at hp
    obtain ⟨e, he, rfl⟩ := hp
    apply G.not_isDiag_of_mem_edgeSet (G.mem_edgeFinset.mp he)
    rw [← Quot.out_eq e]
    exact Sym2.mk_isDiag_iff.mpr h_eq
  -- Freshness w.r.t. `empty.underline = ∅` is trivial.
  have hfresh : ∀ p ∈ edges, s(p.1, p.2) ∉ (empty : PartialOrientation V).underline := by
    intro p _; simp
  -- Pairwise Sym2-distinctness from `Finset.nodup_toList` + the round-trip.
  have hpairwise : edges.Pairwise
      (fun p q : V × V => s(p.1, p.2) ≠ s(q.1, q.2)) := by
    rw [hedges, List.pairwise_map]
    refine G.edgeFinset.nodup_toList.imp ?_
    intro e e' hne h_eq
    apply hne
    rw [← Quot.out_eq e, ← Quot.out_eq e']
    exact h_eq
  -- Combine both inclusions.
  have h_supset : ∀ p ∈ edges, s(p.1, p.2) ∈ D'.underline :=
    runPebbleGameWith_mem_underline _ _ edges Reachable.empty hloops hfresh hpairwise h
  obtain ⟨_, h_upper⟩ :=
    runPebbleGameWith_underline_subset _ _ edges h
  apply le_antisymm
  · -- D'.underline ⊆ G.edgeFinset (via the subset lemma's upper bound).
    intro e he
    have he' := h_upper he
    simp only [underline_empty, Finset.empty_union] at he'
    exact h_img ▸ he'
  · -- G.edgeFinset ⊆ D'.underline (every `e` is hit by some `p ∈ edges`).
    intro e he
    rw [← h_img] at he
    simp only [List.mem_toFinset, List.mem_map] at he
    obtain ⟨p, hp, rfl⟩ := he
    exact h_supset p hp

end RunPebbleGame

/-! ### Soundness

The basic pebble game is **sound**: if `runPebbleGame G k ℓ` succeeds on a
finite simple graph `G`, the returned orientation `D'` certifies that `G` is
`(k, ℓ)`-sparse. The proof is a one-step assembly of three pieces that
landed in earlier commits:

* `Reachable.span_add_le` (Invariant (4) of `lem:pebble-game-invariants`):
  every subset satisfies `D'.span V' + ℓ ≤ k * V'.card`.
* `runPebbleGame_underline_eq_edgeFinset`: the wrapper threads
  `D'.underline = G.edgeFinset` through the fold.
* The structural identity `span_eq_ncard_edgesIn` below: under the underline
  identity, `D'.span V' = (G.edgesIn ↑V').ncard`. The bijection
  `D.spanArcs V' → G.edgesIn ↑V'` via `(a, b) ↦ s(a, b)` has injectivity
  from `no_antiparallel` (`sym2_mk_injOn_arcs`) and surjectivity from
  `D.underline = G.edgeFinset` (`image_spanArcs_eq_edgesIn`).

Cf. Lee–Streinu Theorem 8 (forward direction), blueprint
`thm:pebble-game-soundness`. -/

section Soundness

/-- The map `(a, b) ↦ s(a, b)` from arcs to unoriented edges is injective on
`D.arcs`: the only way two arcs share a `Sym2 V`-image is to be equal as
ordered pairs. The `no_antiparallel` invariant blocks the antiparallel case
`(a, b), (b, a)`. -/
lemma sym2_mk_injOn_arcs (D : PartialOrientation V) :
    Set.InjOn (fun p : V × V => s(p.1, p.2)) ↑D.arcs := by
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
  simp only [Finset.mem_coe] at hab hab'
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd hab (D.no_antiparallel hab')

/-- Image equation: the `Sym2.mk`-image of the arcs spanning `V'` is exactly
`G.edgesIn ↑V'`, under the underline identity `D.underline = G.edgeFinset`.
The ⊆ inclusion lifts an arc to its underline element (sitting in `G.edgeFinset`
by the hypothesis) and re-packages with the in-`V'` endpoint conditions; the
⊇ inclusion lifts an edge `e ∈ G.edgesIn ↑V'` to a span-arc via
`mem_underline`, with both endpoints in `V'` by `(↑e : Set V) ⊆ ↑V'`. -/
lemma image_spanArcs_eq_edgesIn (D : PartialOrientation V)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : D.underline = G.edgeFinset) (V' : Finset V) :
    (fun p : V × V => s(p.1, p.2)) '' (↑(D.spanArcs V') : Set (V × V)) =
      G.edgesIn (↑V' : Set V) := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨⟨a, b⟩, hab, rfl⟩
    simp only [Finset.mem_coe, spanArcs, Finset.mem_filter] at hab
    obtain ⟨h_arc, ha, hb⟩ := hab
    have h_edge : s(a, b) ∈ G.edgeSet := by
      have h_underline : s(a, b) ∈ D.underline := D.mem_underline.mpr (Or.inl h_arc)
      rw [hG, G.mem_edgeFinset] at h_underline
      exact h_underline
    exact SimpleGraph.mk_mem_edgesIn h_edge ha hb
  · intro e he
    rw [SimpleGraph.mem_edgesIn] at he
    obtain ⟨h_edge, h_sub⟩ := he
    have he_underline : e ∈ D.underline := by
      rw [hG]; exact G.mem_edgeFinset.mpr h_edge
    rw [underline, Finset.mem_image] at he_underline
    obtain ⟨⟨a, b⟩, ha_arc, h_eq⟩ := he_underline
    refine ⟨(a, b), ?_, h_eq⟩
    simp only [Finset.mem_coe, spanArcs, Finset.mem_filter]
    refine ⟨ha_arc, h_sub ?_, h_sub ?_⟩
    · rw [← h_eq]; exact Sym2.mem_mk_left a b
    · rw [← h_eq]; exact Sym2.mem_mk_right a b

/-- Structural bridge from the algorithm's `span` count to the project's
`edgesIn` count: under `D.underline = G.edgeFinset`, the orientation's span of
`V'` equals `(G.edgesIn ↑V').ncard`. Combines `image_spanArcs_eq_edgesIn`
(image equation) with `sym2_mk_injOn_arcs` (injectivity) via
`Set.ncard_image_of_injOn`. -/
lemma span_eq_ncard_edgesIn (D : PartialOrientation V)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : D.underline = G.edgeFinset) (V' : Finset V) :
    D.span V' = (G.edgesIn ↑V').ncard := by
  rw [span, ← Set.ncard_coe_finset, ← image_spanArcs_eq_edgesIn D hG V']
  refine ((sym2_mk_injOn_arcs D).mono ?_).ncard_image.symm
  intro p hp
  simp only [Finset.mem_coe, spanArcs, Finset.mem_filter] at hp
  exact Finset.mem_coe.mpr hp.1

/-- **Soundness of the basic `(k, ℓ)`-pebble game.** If
`runPebbleGame G k ℓ` succeeds on a finite simple graph `G` with output
orientation `D'`, then `G` is `(k, ℓ)`-sparse. Three-piece assembly:
*(i)* `runPebbleGameWith_reachable` lifts the initial `Reachable.empty` to
`Reachable k ℓ D'`; *(ii)* `Reachable.span_add_le` (Invariant (4)) gives the
algebraic inequality `D'.span s + ℓ ≤ k * s.card` for every `s` of the right
size; *(iii)* the span/edgesIn bridge `span_eq_ncard_edgesIn` (under
`runPebbleGame_underline_eq_edgeFinset`) translates that into
`(G.edgesIn ↑s).ncard + ℓ ≤ k * s.card`, which is `IsSparse`.

Lee–Streinu Theorem 8 (forward direction); blueprint
`thm:pebble-game-soundness`. The blueprint chapter states the result under
the matroidal-regime assumption `ℓ < 2k`; Lean does not require it here,
because `IsSparse`'s definition already gates on `ℓ ≤ k * s.card`. -/
theorem runPebbleGame_sound [Fintype V] {G : SimpleGraph V} [Fintype G.edgeSet]
    {k ℓ : ℕ} {D' : PartialOrientation V} (h : runPebbleGame G k ℓ = some D') :
    G.IsSparse k ℓ := by
  have h_eq : D'.underline = G.edgeFinset := runPebbleGame_underline_eq_edgeFinset h
  have hR : Reachable k ℓ D' := by
    rw [runPebbleGame] at h
    exact runPebbleGameWith_reachable (fun D' => D'.outList)
      (fun D' {_ _} => D'.mem_outList) _ Reachable.empty h
  intro s hs
  have h_span := hR.span_add_le hs
  rw [span_eq_ncard_edgesIn D' h_eq s] at h_span
  exact h_span

end Soundness

/-! ### Completeness — towards the failure-witness lemma

The completeness side of L-S Theorem 8 routes through Lemma 13: if the
candidate edge `{u, v}` is independent (in the matroid sense), then a
free pebble is reachable from within `Reach_D(u) ∪ Reach_D(v)` without
disturbing the other endpoint's count. The algebraic core
`Reachable.independent_brings_pebble` landed in an earlier commit; this
section adds the closure-of-reachability infrastructure
(`PartialOrientation.reach` and the out-arc closure lemmas) and the
SimpleGraph-form wrapper of Lemma 13 that the upcoming `tryAddEdgeWith`
completeness recursion will iterate.

Cf. blueprint `lem:pebble-game-independent-brings-pebble` (the
SimpleGraph-form proof body of the algebraic-core lemma, now discharged
by the wrapper below). -/

section Completeness

open CombinatorialRigidity.Search

variable [Fintype V]

/-- `D.reach v` is the set of vertices reachable from `v` along `D`'s
out-arcs, packaged as a `Finset V`. Noncomputable: this is the
math-layer view, used by the pebble game's completeness side to
construct the blocking-witness set `D.reach u ∪ D.reach v`. The
algorithm side uses `tryReachPebble` (the verified DFS) to query
reachability without ever materialising the full closure. -/
noncomputable def reach (D : PartialOrientation V) (v : V) : Finset V :=
  reachClosure (fun a b => (a, b) ∈ D.arcs) v

@[simp] lemma mem_reach {D : PartialOrientation V} {v w : V} :
    w ∈ D.reach v ↔
      Relation.ReflTransGen (fun a b => (a, b) ∈ D.arcs) v w :=
  mem_reachClosure

lemma self_mem_reach (D : PartialOrientation V) (v : V) : v ∈ D.reach v :=
  self_mem_reachClosure _ _

lemma reach_closed {D : PartialOrientation V} {v a b : V}
    (ha : a ∈ D.reach v) (hab : (a, b) ∈ D.arcs) : b ∈ D.reach v :=
  reachClosure_closed ha hab

omit [Fintype V] in
/-- A finset `V'` closed under `D`'s outgoing arcs has `outOn V' = 0`:
no arc leaves `V'`. -/
lemma outOn_eq_zero_of_closed (D : PartialOrientation V) {V' : Finset V}
    (h_closed : ∀ a ∈ V', ∀ b, (a, b) ∈ D.arcs → b ∈ V') :
    D.outOn V' = 0 := by
  have h_empty : D.boundaryArcs V' = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    rintro ⟨a, b⟩ h
    simp only [boundaryArcs, Finset.mem_filter] at h
    exact h.2.2 (h_closed a h.2.1 b h.1)
  rw [outOn, h_empty, Finset.card_empty]

/-- The reach-union of two vertices is out-closed under `D.arcs`:
`D.outOn (D.reach u ∪ D.reach v) = 0`. Direct consequence of
`reach_closed` applied to each component. -/
lemma outOn_reach_union_eq_zero (D : PartialOrientation V) (u v : V) :
    D.outOn (D.reach u ∪ D.reach v) = 0 := by
  apply D.outOn_eq_zero_of_closed
  intro a ha b hab
  rw [Finset.mem_union] at ha ⊢
  rcases ha with ha | ha
  · exact Or.inl (reach_closed ha hab)
  · exact Or.inr (reach_closed ha hab)

omit [Fintype V] in
/-- Post-insertion sparsity bridge: when `s(u, v)` is fresh w.r.t.
`D.underline`, both endpoints `u, v` are in `V'`, the candidate edge
`s(u, v)` sits in `G.edgeFinset`, and `D.underline ⊆ G.edgeFinset`,
the `(G.edgesIn ↑V').ncard` count exceeds the orientation's span on
`V'` by at least one: `D.span V' + 1 ≤ (G.edgesIn ↑V').ncard`. The
`+ 1` is the candidate edge itself; the underlying span is included
via the Sym2-image of `D.spanArcs V'`, which is disjoint from
`s(u, v)` by freshness.

Stated with `s(u, v) ∈ G.edgeFinset ∧ D.underline ⊆ G.edgeFinset`
rather than the tight `G.edgeFinset = insert s(u, v) D.underline`: the
proof only needs the inclusions, and the relaxed form is what
`tryAddEdgeWith_eq_none_imp_exists_witness`'s fold-level consumer
threads through `runPebbleGameWith`'s recursion (where `G` has more
edges than the running orientation's underline plus the candidate). -/
lemma span_succ_le_edgesIn_ncard_of_subset (D : PartialOrientation V)
    {u v : V} (h_fresh : s(u, v) ∉ D.underline)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (h_uv : s(u, v) ∈ G.edgeFinset)
    (h_sub : D.underline ⊆ G.edgeFinset)
    {V' : Finset V} (hu : u ∈ V') (hv : v ∈ V') :
    D.span V' + 1 ≤ (G.edgesIn ↑V').ncard := by
  set S : Finset (Sym2 V) := (D.spanArcs V').image (fun p => s(p.1, p.2)) with hS
  have h_S_sub : (↑S : Set (Sym2 V)) ⊆ G.edgesIn ↑V' := by
    intro e he
    rw [Finset.mem_coe, hS, Finset.mem_image] at he
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := he
    simp only [spanArcs, Finset.mem_filter] at hab
    obtain ⟨h_arc, ha, hb⟩ := hab
    have h_edge : s(a, b) ∈ G.edgeSet :=
      G.mem_edgeFinset.mp (h_sub (D.mem_underline.mpr (Or.inl h_arc)))
    exact G.mk_mem_edgesIn h_edge ha hb
  have h_uv_in : s(u, v) ∈ G.edgesIn ↑V' :=
    G.mk_mem_edgesIn (G.mem_edgeFinset.mp h_uv) hu hv
  have h_uv_notin_S : s(u, v) ∉ S := by
    intro h_in
    rw [hS, Finset.mem_image] at h_in
    obtain ⟨⟨a, b⟩, hab, h_eq⟩ := h_in
    simp only [spanArcs, Finset.mem_filter] at hab
    exact h_fresh (h_eq ▸ D.mem_underline.mpr (Or.inl hab.1))
  have h_combined_sub : (↑(insert s(u, v) S : Finset (Sym2 V)) : Set (Sym2 V))
      ⊆ G.edgesIn ↑V' := by
    rw [Finset.coe_insert, Set.insert_subset_iff]
    exact ⟨h_uv_in, h_S_sub⟩
  have h_card : (insert s(u, v) S).card = S.card + 1 :=
    Finset.card_insert_of_notMem h_uv_notin_S
  have h_S_card : S.card = D.span V' := by
    rw [hS, span]
    refine Finset.card_image_of_injOn ((sym2_mk_injOn_arcs D).mono ?_)
    intro p hp
    simp only [Finset.mem_coe, spanArcs, Finset.mem_filter] at hp
    exact Finset.mem_coe.mpr hp.1
  have h_finite : (G.edgesIn ↑V').Finite :=
    G.edgeSet.toFinite.subset (fun _ he => he.1)
  calc D.span V' + 1
      = S.card + 1 := by rw [h_S_card]
    _ = (insert s(u, v) S).card := h_card.symm
    _ = (↑(insert s(u, v) S : Finset (Sym2 V)) : Set (Sym2 V)).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ (G.edgesIn ↑V').ncard := Set.ncard_le_ncard h_combined_sub h_finite

/-- **L-S Lemma 13, SimpleGraph form.** Given a `(k, ℓ)`-reachable
partial orientation `D`, a candidate edge `s(u, v)` fresh w.r.t.
`D.underline` (with `u ≠ v`), and a finite simple graph `G` with edge
set `insert s(u, v) D.underline` that is `(k, ℓ)`-sparse, the
below-threshold condition `D.peb k u + D.peb k v < ℓ + 1` forces the
existence of a vertex `w ∈ D.reach u ∪ D.reach v` distinct from `u` and
`v` with a free pebble (`0 < D.peb k w`). Iterating this brings enough
pebbles to `u, v` for the threshold to be met.

Wraps the algebraic-core `Reachable.independent_brings_pebble` by
instantiating `V' = D.reach u ∪ D.reach v`: the closure
`D.outOn V' = 0` follows from `reach_closed` (`outOn_reach_union_eq_zero`),
and the post-insertion sparsity bound `D.span V' + 1 + ℓ ≤ k * V'.card`
combines `G.IsSparse` at `V'` (under the size hypothesis from the
matroidal regime `ℓ < 2k` and `|V'| ≥ 2`) with the
`span_succ_le_edgesIn_ncard_of_subset` bridge (instantiated from the
equality `hG` via `Finset.mem_insert_self` / `Finset.mem_insert_of_mem`). -/
lemma Reachable.independent_brings_pebble_simpleGraph_form
    {k ℓ : ℕ} {D : PartialOrientation V} (hR : Reachable k ℓ D)
    {u v : V} (huv : u ≠ v) (h_fresh : s(u, v) ∉ D.underline)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : G.edgeFinset = insert s(u, v) D.underline)
    (hSparse : G.IsSparse k ℓ) (h_matroidal : ℓ < 2 * k)
    (h_below : D.peb k u + D.peb k v < ℓ + 1) :
    ∃ w ∈ D.reach u ∪ D.reach v, w ≠ u ∧ w ≠ v ∧ 0 < D.peb k w := by
  set V' := D.reach u ∪ D.reach v with hV'_def
  have hu : u ∈ V' := Finset.mem_union.mpr (Or.inl (D.self_mem_reach u))
  have hv : v ∈ V' := Finset.mem_union.mpr (Or.inr (D.self_mem_reach v))
  have h_card : 2 ≤ V'.card := by
    have : ({u, v} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [huv]), Finset.card_singleton]
    rw [← this]
    apply Finset.card_le_card
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hu
    · rcases Finset.mem_singleton.mp hx with rfl
      exact hv
  have h_size : ℓ ≤ k * V'.card := by
    have h2k : 2 * k ≤ k * V'.card := by
      rw [mul_comm 2 k]
      exact Nat.mul_le_mul_left k h_card
    omega
  have h_closed : D.outOn V' = 0 := D.outOn_reach_union_eq_zero u v
  have h_uv : s(u, v) ∈ G.edgeFinset := hG ▸ Finset.mem_insert_self _ _
  have h_sub : D.underline ⊆ G.edgeFinset := fun _ he => hG ▸ Finset.mem_insert_of_mem he
  have h_bridge : D.span V' + 1 ≤ (G.edgesIn ↑V').ncard :=
    D.span_succ_le_edgesIn_ncard_of_subset h_fresh h_uv h_sub hu hv
  have h_sparse_V' : (G.edgesIn ↑V').ncard + ℓ ≤ k * V'.card := hSparse V' h_size
  have h_post_sparse : D.span V' + 1 + ℓ ≤ k * V'.card := by omega
  exact hR.independent_brings_pebble huv hu hv h_closed h_post_sparse h_below

/-- **Completeness of `tryAddEdgeWith` (⇐ of L-S Lemma 14 / blueprint
`lem:pebble-game-tryAddEdge-iff-independent`).** Given a `(k, ℓ)`-reachable
orientation `D` and a candidate edge `s(u, v)` fresh w.r.t. `D.underline`, if
the finite simple graph `G` with `G.edgeFinset = insert s(u, v) D.underline`
is `(k, ℓ)`-sparse (in the matroidal regime `ℓ < 2*k`), then
`D.tryAddEdgeWith k ℓ u v ...` returns `some D'` — it cannot return `none`.

Proof by `tryAddEdgeWith.induct` over the algorithm's five-case dispatch:
* (case1, case2) Threshold met: the function returns `some` directly.
* (case3, case4) DFS at `u` or `v` succeeds: recurse via the IH on
  `r.newOrient`. The IH preconditions transport via
  `TryReachPebbleResult.reachable_newOrient` (preserves reachability) and
  `TryReachPebbleResult.underline_newOrient_eq` (preserves the underline,
  hence the freshness and sparsity-bridge hypotheses).
* (case5) Both DFS searches fail: contradicted by Lemma 13 SimpleGraph form
  (`Reachable.independent_brings_pebble_simpleGraph_form`), which produces a
  free pebble `w ∈ D.reach u ∪ D.reach v` distinct from `u, v`; the
  reach-membership routes through `tryReachPebbleWith_eq_none_imp` against
  the corresponding endpoint's `= none` hypothesis, contradicting the
  predicate `P w = true`. -/
lemma tryAddEdgeWith_isSome {k ℓ : ℕ} {u v : V} (huv : u ≠ v)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hSparse : G.IsSparse k ℓ) (h_matroidal : ℓ < 2 * k)
    {D : PartialOrientation V}
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (h_outle : ∀ x, D.out x ≤ k)
    (hD : Reachable k ℓ D)
    (h_fresh : s(u, v) ∉ D.underline)
    (hG : G.edgeFinset = insert s(u, v) D.underline) :
    ∃ D' : PartialOrientation V,
      D.tryAddEdgeWith k ℓ u v huv hnotin hnotin_rev h_outle toSucc h_toSucc
        = some D' := by
  induction D, hnotin, hnotin_rev, h_outle using
    tryAddEdgeWith.induct (k := k) (ℓ := ℓ) (huv := huv)
      (toSucc := toSucc) (h_toSucc := h_toSucc)
  case case1 D hnotin hnotin_rev h_outle hthr hpu_pos =>
    rw [tryAddEdgeWith, dif_pos hthr, if_pos hpu_pos]
    exact ⟨_, rfl⟩
  case case2 D hnotin hnotin_rev h_outle hthr hpu_neg =>
    rw [tryAddEdgeWith, dif_pos hthr, if_neg hpu_neg]
    exact ⟨_, rfl⟩
  case case3 D hnotin hnotin_rev h_outle hthr P r hr_eq ih =>
    rw [tryAddEdgeWith, dif_neg hthr]
    simp only
    rw [hr_eq]
    have hP_decomp : (0 < D.peb k r.target ∧ r.target ≠ u) ∧ r.target ≠ v := by
      have := r.hP; simp only [P, Bool.and_eq_true, decide_eq_true_eq] at this; exact this
    have h_target : D.out r.target < k := by
      have h1 := h_outle r.target
      have h2 : D.peb k r.target = k - D.out r.target := rfl
      have := hP_decomp.1.1
      omega
    have hR_new : Reachable k ℓ r.newOrient := r.reachable_newOrient hD h_target
    have h_fresh_new : s(u, v) ∉ r.newOrient.underline := by
      rw [r.underline_newOrient_eq]; exact h_fresh
    have hG_new : G.edgeFinset = insert s(u, v) r.newOrient.underline := by
      rw [r.underline_newOrient_eq]; exact hG
    exact ih hR_new h_fresh_new hG_new
  case case4 D hnotin hnotin_rev h_outle hthr P hu_none r hr_eq ih =>
    rw [tryAddEdgeWith, dif_neg hthr]
    simp only
    rw [hu_none, hr_eq]
    have hP_decomp : (0 < D.peb k r.target ∧ r.target ≠ u) ∧ r.target ≠ v := by
      have := r.hP; simp only [P, Bool.and_eq_true, decide_eq_true_eq] at this; exact this
    have h_target : D.out r.target < k := by
      have h1 := h_outle r.target
      have h2 : D.peb k r.target = k - D.out r.target := rfl
      have := hP_decomp.1.1
      omega
    have hR_new : Reachable k ℓ r.newOrient := r.reachable_newOrient hD h_target
    have h_fresh_new : s(u, v) ∉ r.newOrient.underline := by
      rw [r.underline_newOrient_eq]; exact h_fresh
    have hG_new : G.edgeFinset = insert s(u, v) r.newOrient.underline := by
      rw [r.underline_newOrient_eq]; exact hG
    exact ih hR_new h_fresh_new hG_new
  case case5 D hnotin hnotin_rev h_outle hthr P hu_none hv_none =>
    exfalso
    have h_below : D.peb k u + D.peb k v < ℓ + 1 := by omega
    obtain ⟨w, hw_mem, hw_u, hw_v, hw_pos⟩ :=
      hD.independent_brings_pebble_simpleGraph_form huv h_fresh hG hSparse h_matroidal
        h_below
    have hPw : P w = true := by
      simp only [P, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hw_pos, hw_u⟩, hw_v⟩
    rw [Finset.mem_union] at hw_mem
    rcases hw_mem with hu_reach | hv_reach
    · rw [mem_reach] at hu_reach
      exact tryReachPebbleWith_eq_none_imp (h_toSucc D) hu_none hu_reach hPw
    · rw [mem_reach] at hv_reach
      exact tryReachPebbleWith_eq_none_imp (h_toSucc D) hv_none hv_reach hPw

/-- **`tryAddEdgeWith` accept ⇒ post-insertion sparse** (⇒ half of
`lem:pebble-game-tryAddEdge-iff-independent`). If `tryAddEdgeWith` on a
`(k, ℓ)`-reachable `D` returns `some D'`, then any finite simple graph `G`
with `G.edgeFinset = insert s(u, v) D.underline` is `(k, ℓ)`-sparse.

Three-piece assembly mirroring `runPebbleGame_sound`:
*(i)* `tryAddEdgeWith_underline` plus the hypothesis `G.edgeFinset = insert
s(u, v) D.underline` give the underline identity `D'.underline = G.edgeFinset`.
*(ii)* `tryAddEdgeWith_reachable` lifts `Reachable k ℓ D` to `Reachable k ℓ D'`,
which delivers Invariant (4) `D'.span V' + ℓ ≤ k * V'.card` via
`Reachable.span_add_le`.
*(iii)* `span_eq_ncard_edgesIn` rewrites `D'.span V'` to `(G.edgesIn ↑V').ncard`.

This is the per-step soundness of `tryAddEdgeWith`. Composed with the ⇐ half
`tryAddEdgeWith_isSome`, it gives the full iff of L-S Lemma 14. -/
lemma tryAddEdgeWith_isSparse {k ℓ : ℕ} {u v : V} (huv : u ≠ v)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {D : PartialOrientation V}
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (h_outle : ∀ x, D.out x ≤ k)
    (hD : Reachable k ℓ D)
    (hG : G.edgeFinset = insert s(u, v) D.underline)
    {D' : PartialOrientation V}
    (h : D.tryAddEdgeWith k ℓ u v huv hnotin hnotin_rev h_outle toSucc h_toSucc
      = some D') :
    G.IsSparse k ℓ := by
  have h_und : D'.underline = G.edgeFinset :=
    (tryAddEdgeWith_underline huv toSucc h_toSucc hnotin hnotin_rev h_outle h).trans hG.symm
  have hR : Reachable k ℓ D' :=
    tryAddEdgeWith_reachable huv toSucc h_toSucc hnotin hnotin_rev h_outle hD h
  intro s hs
  have h_span := hR.span_add_le hs
  rw [span_eq_ncard_edgesIn D' h_und s] at h_span
  exact h_span

/-- **Failure-witness extraction at the per-edge layer** (blueprint
`lem:pebble-game-failure-witness`). Given a `(k, ℓ)`-reachable orientation `D`
and a candidate edge `s(u, v)` whose underlying ambient graph `G` already
contains `s(u, v)` and every edge of `D.underline`, in the matroidal regime
`ℓ < 2k`, if `D.tryAddEdgeWith` returns `none` then there exists a vertex
subset `V'` whose count exceeds the sparsity bound:
`k * V'.card < (G.edgesIn ↑V').ncard + ℓ` under the size hypothesis
`ℓ ≤ k * V'.card`. Equivalently, `G` is not `(k, ℓ)`-sparse.

The freshness `s(u, v) ∉ D.underline` is derived from the algorithmic
preconditions `(u, v) ∉ D.arcs ∧ (v, u) ∉ D.arcs` (via `mem_underline`); we
do not require it as a separate hypothesis. The ambient-graph hypothesis is
stated as `s(u, v) ∈ G.edgeFinset ∧ D.underline ⊆ G.edgeFinset` (rather than
the tight equality `G.edgeFinset = insert s(u, v) D.underline`) so the
fold-level consumer `runPebbleGameWith_eq_none_imp_exists_witness` can
thread it through `runPebbleGameWith`'s structural recursion against the
full input graph (whose edge set strictly extends `D.underline` plus the
candidate at any intermediate step).

Proof by `tryAddEdgeWith.induct`'s five-case dispatch:
* (case1, case2) Threshold met: function returns `some`, contradicting `h`.
* (case3, case4) DFS success at `u` or `v`: recurse via the IH on
  `r.newOrient`. Reachability + underline-subset transport via
  `TryReachPebbleResult.reachable_newOrient` /
  `TryReachPebbleResult.underline_newOrient_eq`.
* (case5) Both DFS searches fail: take `V' := D.reach u ∪ D.reach v`. The
  closure of reach under out-arcs gives `D.outOn V' = 0`
  (`outOn_reach_union_eq_zero`). Both DFS failures (via
  `tryReachPebbleWith_eq_none_imp` on the predicate `P`) plus the predicate's
  exclusion of `u, v` force `D.peb k w = 0` for every `w ∈ V'` with
  `w ≠ u, v`, so `D.pebOn k V' = D.peb k u + D.peb k v ≤ ℓ` (the latter from
  the below-threshold hypothesis `¬ (ℓ + 1 ≤ D.peb k u + D.peb k v)`).
  Invariant (2) then gives `D.span V' + (D.peb k u + D.peb k v) = k * V'.card`,
  and `span_succ_le_edgesIn_ncard_of_subset` lifts to
  `(G.edgesIn ↑V').ncard ≥ D.span V' + 1`. Combining:
  `(G.edgesIn ↑V').ncard + ℓ ≥ D.span V' + 1 + ℓ ≥ k * V'.card + 1`.

The size hypothesis `ℓ ≤ k * V'.card` is discharged from `|V'| ≥ 2` (since
`u, v ∈ V'` and `u ≠ v`) plus `ℓ < 2k ≤ k * V'.card`. This is the only place
the matroidal-regime hypothesis enters the failure-witness construction
formally. -/
lemma tryAddEdgeWith_eq_none_imp_exists_witness {k ℓ : ℕ} {u v : V} (huv : u ≠ v)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (h_matroidal : ℓ < 2 * k)
    {D : PartialOrientation V}
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (h_outle : ∀ x, D.out x ≤ k)
    (hD : Reachable k ℓ D)
    (h_uv : s(u, v) ∈ G.edgeFinset)
    (h_sub : D.underline ⊆ G.edgeFinset)
    (h : D.tryAddEdgeWith k ℓ u v huv hnotin hnotin_rev h_outle toSucc h_toSucc
      = none) :
    ∃ V' : Finset V, ℓ ≤ k * V'.card ∧ k * V'.card < (G.edgesIn ↑V').ncard + ℓ := by
  induction D, hnotin, hnotin_rev, h_outle using
    tryAddEdgeWith.induct (k := k) (ℓ := ℓ) (huv := huv)
      (toSucc := toSucc) (h_toSucc := h_toSucc)
  case case1 D hnotin hnotin_rev h_outle hthr hpu_pos =>
    rw [tryAddEdgeWith, dif_pos hthr, if_pos hpu_pos] at h
    exact absurd h (Option.some_ne_none _)
  case case2 D hnotin hnotin_rev h_outle hthr hpu_neg =>
    rw [tryAddEdgeWith, dif_pos hthr, if_neg hpu_neg] at h
    exact absurd h (Option.some_ne_none _)
  case case3 D hnotin hnotin_rev h_outle hthr P r hr_eq ih =>
    rw [tryAddEdgeWith, dif_neg hthr] at h
    simp only at h
    rw [hr_eq] at h
    have hP_decomp : (0 < D.peb k r.target ∧ r.target ≠ u) ∧ r.target ≠ v := by
      have := r.hP; simp only [P, Bool.and_eq_true, decide_eq_true_eq] at this; exact this
    have h_target : D.out r.target < k := by
      have h1 := h_outle r.target
      have h2 : D.peb k r.target = k - D.out r.target := rfl
      have := hP_decomp.1.1
      omega
    have hR_new : Reachable k ℓ r.newOrient := r.reachable_newOrient hD h_target
    have h_sub_new : r.newOrient.underline ⊆ G.edgeFinset := by
      rw [r.underline_newOrient_eq]; exact h_sub
    exact ih hR_new h_sub_new h
  case case4 D hnotin hnotin_rev h_outle hthr P hu_none r hr_eq ih =>
    rw [tryAddEdgeWith, dif_neg hthr] at h
    simp only at h
    rw [hu_none, hr_eq] at h
    have hP_decomp : (0 < D.peb k r.target ∧ r.target ≠ u) ∧ r.target ≠ v := by
      have := r.hP; simp only [P, Bool.and_eq_true, decide_eq_true_eq] at this; exact this
    have h_target : D.out r.target < k := by
      have h1 := h_outle r.target
      have h2 : D.peb k r.target = k - D.out r.target := rfl
      have := hP_decomp.1.1
      omega
    have hR_new : Reachable k ℓ r.newOrient := r.reachable_newOrient hD h_target
    have h_sub_new : r.newOrient.underline ⊆ G.edgeFinset := by
      rw [r.underline_newOrient_eq]; exact h_sub
    exact ih hR_new h_sub_new h
  case case5 D hnotin hnotin_rev h_outle hthr P hu_none hv_none =>
    -- Freshness from the algorithmic preconditions on `D`'s arcs.
    have h_fresh : s(u, v) ∉ D.underline := fun h_mem => by
      rcases D.mem_underline.mp h_mem with hm | hm
      · exact hnotin hm
      · exact hnotin_rev hm
    -- Substantive case: build the witness V' := D.reach u ∪ D.reach v.
    set V' := D.reach u ∪ D.reach v with hV'_def
    have hu_V' : u ∈ V' := Finset.mem_union.mpr (Or.inl (D.self_mem_reach u))
    have hv_V' : v ∈ V' := Finset.mem_union.mpr (Or.inr (D.self_mem_reach v))
    -- |V'| ≥ 2 because {u, v} ⊆ V' and u ≠ v.
    have h_card : 2 ≤ V'.card := by
      have h2 : ({u, v} : Finset V).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [huv]), Finset.card_singleton]
      rw [← h2]
      apply Finset.card_le_card
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hu_V'
      · rcases Finset.mem_singleton.mp hx with rfl
        exact hv_V'
    -- ℓ ≤ k * V'.card via ℓ < 2k ≤ k * V'.card.
    have h_size : ℓ ≤ k * V'.card := by
      have h2k : 2 * k ≤ k * V'.card := by
        rw [mul_comm 2 k]
        exact Nat.mul_le_mul_left k h_card
      omega
    -- V' is out-closed under D's arcs.
    have h_outOn : D.outOn V' = 0 := D.outOn_reach_union_eq_zero u v
    -- DFS-failure ⇒ every w ∈ V' with w ≠ u, v has peb k w = 0.
    have h_zero_outside : ∀ w ∈ V', w ≠ u → w ≠ v → D.peb k w = 0 := by
      intro w hw_mem hw_u hw_v
      by_contra hw_ne_zero
      have hw_pos : 0 < D.peb k w := Nat.pos_of_ne_zero hw_ne_zero
      have hPw : P w = true := by
        simp only [P, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hw_pos, hw_u⟩, hw_v⟩
      rw [Finset.mem_union] at hw_mem
      rcases hw_mem with hu_reach | hv_reach
      · rw [mem_reach] at hu_reach
        exact tryReachPebbleWith_eq_none_imp (h_toSucc D) hu_none hu_reach hPw
      · rw [mem_reach] at hv_reach
        exact tryReachPebbleWith_eq_none_imp (h_toSucc D) hv_none hv_reach hPw
    -- Algebraic decomposition: pebOn V' = peb u + peb v.
    have huv_sub : ({u, v} : Finset V) ⊆ V' := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hu_V'
      · rcases Finset.mem_singleton.mp hx with rfl
        exact hv_V'
    have h_sdiff : ∑ x ∈ V' \ ({u, v} : Finset V), D.peb k x +
                     ∑ x ∈ ({u, v} : Finset V), D.peb k x =
                   D.pebOn k V' := by
      rw [pebOn]; exact Finset.sum_sdiff huv_sub
    have h_pair : ∑ x ∈ ({u, v} : Finset V), D.peb k x = D.peb k u + D.peb k v :=
      Finset.sum_pair huv
    have h_sdiff_zero : ∑ x ∈ V' \ ({u, v} : Finset V), D.peb k x = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hw
      exact h_zero_outside w hw.1
        (fun heq => hw.2 (Or.inl heq))
        (fun heq => hw.2 (Or.inr heq))
    -- Invariant (2) gives span V' + (peb u + peb v) = k * V'.card.
    have h_inv2 := hD.pebOn_add_span_add_outOn V'
    -- The +1 bridge: (G.edgesIn ↑V').ncard ≥ D.span V' + 1.
    have h_bridge := D.span_succ_le_edgesIn_ncard_of_subset h_fresh h_uv h_sub hu_V' hv_V'
    refine ⟨V', h_size, ?_⟩
    -- Below-threshold from `hthr`: peb u + peb v ≤ ℓ.
    omega

/-! #### Correctness theorem -/

/-- **Fold-level failure-witness extraction** for the outer pebble-game loop:
if `runPebbleGameWith` returns `none` on a reachable orientation `D` whose
underlying edge set sits in `G.edgeFinset` and whose candidate edge list
ranges within `G.edgeFinset`, then there exists a vertex subset `V'`
witnessing non-sparsity of `G`. Fold-level analogue of the per-edge witness
`tryAddEdgeWith_eq_none_imp_exists_witness`.

By structural recursion on the edge list. The empty case contradicts the
hypothesis (the fold returns `some D`). On `(u, v) :: es`, the runtime-check
`if`-condition either fails (no-op skip: recurse with the same `D`) or
succeeds, in which case we match on `tryAddEdgeWith`'s output:
* on `some Dmid`, recurse on `es` with `Dmid`, threading reachability via
  `tryAddEdgeWith_reachable`, the underline-subset via
  `tryAddEdgeWith_underline` (`Dmid.underline = insert s(u, v) D.underline`)
  combined with `s(u, v) ∈ G.edgeFinset` from the head of the membership
  hypothesis;
* on `none`, apply `tryAddEdgeWith_eq_none_imp_exists_witness` at the
  failure point directly — its broadened (subset-form) hypothesis matches
  the per-step state.

Cf. blueprint `thm:pebble-game-correct` part (2). -/
lemma runPebbleGameWith_eq_none_imp_exists_witness {k ℓ : ℕ}
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (h_matroidal : ℓ < 2 * k) :
    ∀ (edges : List (V × V)) {D : PartialOrientation V} (_hD : Reachable k ℓ D)
      (_hmem : ∀ p ∈ edges, s(p.1, p.2) ∈ G.edgeFinset)
      (_hsub : D.underline ⊆ G.edgeFinset),
      D.runPebbleGameWith k ℓ toSucc h_toSucc edges = none →
      ∃ V' : Finset V, ℓ ≤ k * V'.card ∧ k * V'.card < (G.edgesIn ↑V').ncard + ℓ
  | [], _D, _hD, _hmem, _hsub, h => by
    rw [runPebbleGameWith] at h
    exact absurd h (Option.some_ne_none _)
  | (u, v) :: es, D, hD, hmem, hsub, h => by
    rw [runPebbleGameWith] at h
    by_cases hcond : u ≠ v ∧ (u, v) ∉ D.arcs ∧ (v, u) ∉ D.arcs ∧ (∀ x, D.out x ≤ k)
    · rw [dif_pos hcond] at h
      match heq : D.tryAddEdgeWith k ℓ u v hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2
          toSucc h_toSucc with
      | some Dmid =>
        rw [heq] at h
        have hR_mid : Reachable k ℓ Dmid :=
          tryAddEdgeWith_reachable hcond.1 toSucc h_toSucc hcond.2.1 hcond.2.2.1
            hcond.2.2.2 hD heq
        have h_mid : Dmid.underline = insert s(u, v) D.underline :=
          tryAddEdgeWith_underline hcond.1 toSucc h_toSucc
            hcond.2.1 hcond.2.2.1 hcond.2.2.2 heq
        have h_uv_in : s(u, v) ∈ G.edgeFinset := hmem (u, v) List.mem_cons_self
        have h_sub_mid : Dmid.underline ⊆ G.edgeFinset := by
          rw [h_mid]
          intro e he
          rcases Finset.mem_insert.mp he with rfl | he
          · exact h_uv_in
          · exact hsub he
        have h_mem_es : ∀ p ∈ es, s(p.1, p.2) ∈ G.edgeFinset := fun p hp =>
          hmem p (List.mem_cons_of_mem _ hp)
        exact runPebbleGameWith_eq_none_imp_exists_witness toSucc h_toSucc h_matroidal
          es hR_mid h_mem_es h_sub_mid h
      | none =>
        have h_uv_in : s(u, v) ∈ G.edgeFinset := hmem (u, v) List.mem_cons_self
        exact tryAddEdgeWith_eq_none_imp_exists_witness hcond.1 toSucc h_toSucc
          h_matroidal hcond.2.1 hcond.2.2.1 hcond.2.2.2 hD h_uv_in hsub heq
    · rw [dif_neg hcond] at h
      have h_mem_es : ∀ p ∈ es, s(p.1, p.2) ∈ G.edgeFinset := fun p hp =>
        hmem p (List.mem_cons_of_mem _ hp)
      exact runPebbleGameWith_eq_none_imp_exists_witness toSucc h_toSucc h_matroidal
        es hD h_mem_es hsub h

end Completeness

/-! ### Correctness theorem — assembly

The certificate-form correctness theorem (Lee–Streinu Theorem 8, blueprint
`thm:pebble-game-correct`): assembled from `runPebbleGame_sound` on the
`some` branch and the new wrapper `runPebbleGame_eq_none_imp_exists_witness`
on the `none` branch. Stated with explicit `[Fintype V]` (rather than the
project-default `[Finite V]`) because the signature elaborates the
`runPebbleGame G k ℓ` term, whose body autobinds `[Fintype V]` from the
section that defines it; `Fintype.ofFinite` cannot bridge from `[Finite V]`
at signature-elaboration time. -/

section Correctness

/-- **Wrapper-level failure-witness for `runPebbleGame`**: a `none` return on
a finite simple graph `G` in the matroidal regime produces a vertex subset
`V'` witnessing non-sparsity of `G`. Specialises
`runPebbleGameWith_eq_none_imp_exists_witness` to `D = empty` and
`edges = G.edgeFinset.toList.map Quot.out`; the membership hypothesis is
discharged by the `Quot.out_eq` round-trip already used in
`runPebbleGame_underline_eq_edgeFinset`, and the `D.underline ⊆ G.edgeFinset`
hypothesis is `underline_empty` plus `Finset.empty_subset`. -/
theorem runPebbleGame_eq_none_imp_exists_witness [Fintype V]
    {G : SimpleGraph V} [Fintype G.edgeSet] {k ℓ : ℕ}
    (h_matroidal : ℓ < 2 * k) (h : runPebbleGame G k ℓ = none) :
    ∃ V' : Finset V, ℓ ≤ k * V'.card ∧ k * V'.card < (G.edgesIn ↑V').ncard + ℓ := by
  rw [runPebbleGame] at h
  set edges := G.edgeFinset.toList.map (Quot.out : Sym2 V → V × V) with hedges
  have h_img : (edges.map (fun p : V × V => s(p.1, p.2))).toFinset = G.edgeFinset := by
    rw [hedges, List.map_map]
    have h_id : (fun p : V × V => s(p.1, p.2)) ∘ (Quot.out : Sym2 V → V × V)
        = id := by
      funext e; exact Quot.out_eq e
    rw [h_id, List.map_id, G.edgeFinset.toList_toFinset]
  have h_mem : ∀ p ∈ edges, s(p.1, p.2) ∈ G.edgeFinset := by
    intro p hp
    rw [← h_img]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have h_sub : (empty : PartialOrientation V).underline ⊆ G.edgeFinset := by
    rw [underline_empty]; exact Finset.empty_subset _
  exact runPebbleGameWith_eq_none_imp_exists_witness _ _ h_matroidal edges
    Reachable.empty h_mem h_sub h

/-- **Certificate-form correctness of the basic `(k, ℓ)`-pebble game**
(Lee–Streinu Theorem 8, certificate form; blueprint
`thm:pebble-game-correct`): in the matroidal regime `ℓ < 2k`, the finite
simple graph `G` is `(k, ℓ)`-sparse iff `runPebbleGame G k ℓ` returns
`some D` for some partial orientation `D`. Two-line assembly:
* (⇐) `runPebbleGame_sound`: an accepted run certifies sparsity.
* (⇒) Contrapositive: if `runPebbleGame G k ℓ = none`,
  `runPebbleGame_eq_none_imp_exists_witness` produces a subset violating
  `G.IsSparse k ℓ`.

The matroidal hypothesis `ℓ < 2k` is needed only for the contrapositive
direction (it discharges `ℓ ≤ k * V'.card` from `|V'| ≥ 2` in the witness
construction); `runPebbleGame_sound` itself is regime-agnostic. Beyond this
iff, the success branch additionally satisfies `D.underline = G.edgeFinset`
(`runPebbleGame_underline_eq_edgeFinset`) — together this is the full
content of the blueprint theorem. -/
theorem runPebbleGame_correct [Fintype V] {G : SimpleGraph V} [Fintype G.edgeSet]
    {k ℓ : ℕ} (h_matroidal : ℓ < 2 * k) :
    G.IsSparse k ℓ ↔ ∃ D : PartialOrientation V, runPebbleGame G k ℓ = some D := by
  refine ⟨?_, ?_⟩
  · intro hG
    match h_opt : runPebbleGame G k ℓ with
    | some D => exact ⟨D, rfl⟩
    | none =>
      obtain ⟨V', h_size, h_lt⟩ :=
        runPebbleGame_eq_none_imp_exists_witness h_matroidal h_opt
      exfalso
      have := hG V' h_size
      omega
  · rintro ⟨_, hD⟩
    exact runPebbleGame_sound hD

end Correctness

end PartialOrientation

end CombinatorialRigidity.PebbleGame
