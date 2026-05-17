# Phase 9 — Pebble game (work log)

**Status:** planning.

This file is the per-phase work record. See `../ROADMAP.md` §9 for
the high-level plan (**pending** — the ROADMAP Status table row and
the §9 planning section land in the same commit that opens this
phase) and `../DESIGN.md` for cross-cutting design choices.

**Workflow:** Phase 9 runs in **forward blueprint mode** per
`../blueprint/DESIGN.md`. The new chapter
`chapter/pebble-game.tex` will be the authoritative dep-graph and
lemma index; this file carries architectural choices, decisions,
and hand-off — *not* the lemma checklist. The chapter is opened in
the first Phase 9 commit.

**References.**
- A. Lee, I. Streinu, *Pebble game algorithms and sparse graphs*,
  Discrete Math. **308** (2008) 1425–1437. PDF in
  `../.refs/lee-streinu-2008.pdf`. The phase formalizes the *basic*
  $(k, \ell)$-pebble game of §3–§4 and its correctness theorem
  (Theorem 8).
- D.J. Jacobs, B. Hendrickson, *An algorithm for two-dimensional
  rigidity percolation: the pebble game*, J. Comput. Phys. **137**
  (1997) 346–365 — the original $(2, 3)$ version.
- T. Jordán, *Combinatorial rigidity*, MSJ Memoirs (2016) —
  background survey, `../.refs/jordan-2016-msj-memoirs.pdf`.
- A. Lee, I. Streinu, L. Theran, *Finding and maintaining rigid
  components*, CCCG '05 (2005). PDF in
  `../.refs/lee-streinu-theran-finding-and-maintaining.pdf`.
  Introduces the *union pair-find* data structure for the $O(n^2)$
  *component pebble game*. **Out of scope for Phase 9** (basic
  pebble game only); pointer for any future component-pebble-game
  phase.

## Current state

Planning. Architectural choices below are settled before Phase 9
opens; the lemma index will be filled in
`chapter/pebble-game.tex` once the chapter lands. No Lean code yet.

The phase target is Lee–Streinu Theorem 8 in certificate form:
$\mathtt{runPebbleGame}\,G$ returns either a `PartialOrientation`
satisfying the four invariants (witness of $(k, \ell)$-sparsity) or
a vertex subset $V'$ with $|E(G[V'])| > k|V'| - \ell$ (witness of
non-sparsity). The matroidal-independence corollary against
Phase 7's `CountMatroid` follows as a one-liner.

**Pre-Phase-9 DFS warmup.** Before Phase 9 opens, a tightly-scoped
verified-DFS exercise lands as a separate small artifact (likely
`CombinatorialRigidity/Search/DFS.lean`, ~200–300 LoC, 1–2
sessions). The only precedent in the immediate ecosystem is
`Batteries.UnionFind` (Lean core has nothing relevant; mathlib's
two DFSes are `partial def` inside tactic metaprogramming); the
warmup exercises the `termination_by (Finset.univ \ visited).card`
pattern in isolation and produces a reusable
`reachableFinding : Digraph V → V → (V → Bool) → Option (Walk V)`
with soundness + completeness. The pebble game's `tryReachPebble`
specializes this (DFS + path reversal during the walk). Logged
inline here unless it grows beyond ~2 sessions, in which case
promote to a dedicated `Phase9-warmup.md`.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Match Phase 7's matroidal regime: simple graphs, $\ell < 2k$,
  both ranges in scope.** Lee–Streinu state results for *multi-graphs*
  with loops, covering $\ell \in [0, 2k)$. We work in `SimpleGraph V`,
  matching the regime of `CountMatroid.lean` and `Sparsity.lean`
  exactly. Loops in L-S's lower range $\ell < k$ contribute single-
  vertex blocks; their absence in `SimpleGraph`-land changes the
  corner-case structure but not the overall theory — the lower
  range is genuinely interesting (tree-packing / arboricity
  applications, cf. Nash-Williams–Tutte) and stays in scope. Corner-
  case verification of L-S Lemmas 10–14 against `SimpleGraph` is an
  early-Phase 9 task (see *Blockers*). Lifting to multi-graphs is a
  much larger project (no mathlib `MultiGraph` infrastructure
  exists) and is out of scope.

- **Finset-first computability style with `[Fintype V] [DecidableEq V]`.**
  The repo defaults to `Set.ncard` + noncomputable definitions on
  `[Finite V]`. The pebble game needs `Finset (V × V)`-backed
  orientations and decidable equality end-to-end so `#eval` and
  `decide` actually run — the extracted-certificate output requires
  it, and `[Finite V]` carries no algorithmic content (you can't
  enumerate or build `Finset`s from it). `PebbleGame.lean` is a
  deliberate style island: `[Fintype V]` + `[DecidableEq V]` in
  signatures, `Finset.card` over `Set.ncard` in algorithm bodies,
  fully computable. A thin shim section bridges to the noncomputable
  `IsSparse`/`IsTight` statements from `Sparsity.lean`. DESIGN.md
  note expected at first Lean commit.

- **Decouple algorithm state from input-graph shape.**
  `PartialOrientation V` and the algorithm body are defined purely
  on `V` and edge-insertion requests (`List (Sym2 V)` or
  `Multiset (Sym2 V)`), not on a specific `SimpleGraph V`.
  `SimpleGraph` enters only at the statement-level wrapper
  `theorem runPebbleGame_simpleGraph_correct (G : SimpleGraph V) :
  …`. The four invariants (Lemma 10) are stated on orientation
  states, not on the input graph; they port unchanged to a future
  multi-graph version (which would just relax the no-parallel-pair
  invariant on `PartialOrientation`). Hypergraph generalisation
  requires redesigning the orientation shape — out of scope to
  design for, but the input/state decoupling at least does not
  actively block it. Cost: one extra wrapper definition + one
  extra wrapper theorem.

- **Algorithm output: structured `Sum`, not L-S's four-way
  classification.** Lee–Streinu return one of
  `{well-, under-, over-constrained, other}`. We collapse to
  ```
  runPebbleGame : … → CertifiedOrientation V k ℓ ⊕ BlockingWitness G k ℓ
  ```
  where the left branch is a `PartialOrientation V` bundled with
  proof of L-S Invariants (1)–(4), and the right branch is
  `{S : Finset V // |edgesIn S| > k * S.card - ℓ}`. Both branches
  positively certify their conclusions. The well-vs-under-vs-over
  trichotomy is a downstream corollary on the size of `peb(V)` and
  is recovered without changing the algorithm shape. Rejected
  alternative: a `PebbleGameResult` four-case enum — adds API
  surface for content already captured by the certificates.

- **Single-phase scope: basic pebble game, both directions.** Phase 9
  covers L-S §3–§4 end-to-end: definitions (state, moves), the four
  invariants (Lemma 10), soundness (accept $\Rightarrow$ sparse,
  Corollary 12), completeness (sparse $\Rightarrow$ accept,
  Lemmas 13–15), and failure-witness extraction. Deferred to
  potential later phases: the *component pebble game* (§5,
  $O(n^2)$ speedup using rigidity components); the Henneberg-
  sequence application (§6, which generalises Phase 3's
  Laman-specific Henneberg construction); circuit / redundancy
  detection (§6 end). Splitting basic correctness across two phases
  was considered and rejected — soundness and completeness share
  too much state-and-invariant machinery to pay the phase-boundary
  cost.

- **New file `CombinatorialRigidity/PebbleGame.lean`.** Slots after
  `LinearRigidityMatroid.lean` for related-material ordering; no
  dependency on it. Imports `Sparsity.lean` (for `IsSparse`,
  `edgesIn`, and the Phase 7 `IsSparse.maxBlock` / block-edge-
  disjointness API the failure-witness branch reuses) and
  `Mathlib.Data.Finset.Basic` / `Mathlib.Data.Sym.Sym2`. No matroid
  dependency — the correctness theorem is structural; the matroidal-
  independence corollary against `CountMatroid` is a downstream
  one-liner that can live in `PebbleGame.lean` or be deferred.

- **Forward-mode blueprint chapter `chapter/pebble-game.tex`.** Per
  the Phase 6+ convention. Sections mirror L-S: *State and moves*
  → *Invariants* → *Algorithm* → *Soundness* → *Completeness* →
  *Correctness theorem* → *Matroidal-independence corollary*. The
  chapter's dep-graph is the lemma index; this file does not
  duplicate it. The chapter opens in the first Phase 9 commit
  alongside the ROADMAP §9 planning section.

## Lemma checklist

**Maintained in the blueprint, not here.** Forthcoming
`chapter/pebble-game.tex` will carry the dep-graph; once it lands,
this section becomes a pointer (cf. `Phase8.md` §"Lemma checklist").

## Decisions made during this phase

*(Empty — phase has not started.)*

## Blockers / open questions

- **Simple-graph vs L-S multi-graph corner cases.** L-S's proofs
  use loops to handle single-vertex blocks (a vertex with $k - \ell$
  loops forms a block in the lower range $\ell < k$). In
  `SimpleGraph`-land single vertices span $0$ edges, so single-
  vertex blocks can't arise — Invariant (4)'s $\mathrm{span}(V')
  \leq k|V'| - \ell$ for $|V'| = 1$ becomes $0 \leq k - \ell$,
  automatic when $\ell \leq k$. For $\ell > k$, L-S restricts
  subset claims to $n' \geq 2$ in Lemma 10's statement, which
  carries over directly. **Action:** in the first Phase 9 session,
  trace L-S Lemmas 10–14 through `SimpleGraph`-eyes for *both*
  ranges. The lower range $\ell < k$ stays in scope (cf. choice 1
  above); work through whatever corner-case gaps surface lemma-by-
  lemma rather than restricting the target prophylactically. If a
  structural gap genuinely forces a regime restriction, document
  the specific obstruction here and revisit.

- **Termination measure for `tryReachPebble`.** Path reversal in
  L-S is bounded informally by "at most $\ell$ DFS searches per
  edge"; for Lean, an explicit decreasing measure is needed. The
  only ecosystem precedent for a verified iterative-graph-state
  algorithm is `Batteries.UnionFind` (`termination_by self.rankMax
  - self.rank x`); model on that. For the inner DFS,
  `(Finset.univ \ visited).card` is the natural measure (visited
  grows monotonically, vertex set is finite). For the outer
  `tryAddEdge` loop, `(ℓ + 1) - (peb u + peb v)` decreases per
  successful path-reversal. The pre-Phase-9 DFS warmup (see
  *Current state*) exercises this pattern in isolation. Friction-
  log entry expected at the termination-proof commit.

- **`PartialOrientation V` representation.** Three options:
  (i) `Finset (V × V)` with antiparallel-free invariant;
  (ii) `V → Finset V` (out-neighbour adjacency lists);
  (iii) function `V → V → Bool` with finiteness via `[Fintype V]`.
  (i) is most direct for definitions and invariants; (ii) is
  efficient for `tryReachPebble`'s reachability search. Defer the
  decision to the first Phase 9 coding commit — write the natural
  one first; refactor if `tryReachPebble`'s termination proof gets
  ugly.

- **Whether to land the matroidal-independence corollary in
  Phase 9 or defer.** The bridge
  `runPebbleGame G = .inl _ ↔ G.edgeSet ∈ (countMatroid k ℓ).Indep`
  is a direct corollary of L-S Theorem 8 + Phase 7's
  `CountMatroid` indep-iff-sparse. Landing it in Phase 9 ties the
  pebble-game story to the existing matroid scaffolding; deferring
  to a later "applications" phase keeps `PebbleGame.lean`
  matroid-independent. Weak preference for landing it (cheap, ties
  the loop); revisit if `Phase9.md`'s end-state is over budget.

## Hand-off / next phase

*(Empty — phase in planning.)*
