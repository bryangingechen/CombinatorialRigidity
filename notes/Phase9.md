# Phase 9 — Pebble game (work log)

**Status:** complete.

This file is the per-phase work record. See `../ROADMAP.md` §9 for
the high-level plan and `../DESIGN.md` for cross-cutting design
choices.

**Workflow:** Phase 9 ran in **forward blueprint mode** per
`../blueprint/DESIGN.md`. The chapter `chapter/pebble-game.tex` is
the authoritative dep-graph and lemma index; this file does not
duplicate it.

**References.**
- A. Lee, I. Streinu, *Pebble game algorithms and sparse graphs*,
  Discrete Math. **308** (2008) 1425–1437. PDF in
  `../.refs/lee-streinu-2008.pdf`. Phase 9 formalises the *basic*
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

**Phase 9 complete.** `chapter/pebble-game.tex`'s dep-graph is fully
green: all 22 nodes carry `\leanok`. The basic $(k, \ell)$-pebble
game of Lee–Streinu 2008 is formalised end-to-end in
`PebbleGame.lean` (~2500 LoC) plus the verified-DFS warmup in
`Search/DFS.lean` (~770 LoC), in the matroidal regime $\ell < 2k$,
including:

- definitions (`PartialOrientation V`, the pebble counts, the two
  state-machine moves) with full per-vertex + subset-level
  preservation lemmas;
- the `Reachable k ℓ` inductive predicate and the four L-S
  invariants of Lemma 10;
- three algorithm layers (`tryReachPebble`, `tryAddEdge`,
  `runPebbleGame`), each split computable workhorse + noncomputable
  math-layer wrapper;
- soundness `thm:pebble-game-soundness` (with the bridge identity
  `lem:span-eq-ncard-edgesIn`), completeness (L-S Lemma 13 algebraic
  core + SimpleGraph-form wrapper, the iff `tryAddEdge_isSome_iff_sparse`
  narrative-bridge shim, per-edge failure-witness);
- certificate-form correctness `thm:pebble-game-correct` and the
  matroidal-independence corollary
  `SimpleGraph.countMatroid_indep_iff_runPebbleGame` tying the
  algorithm to Phase 7's count matroid.

Build + lint clean; `checkdecls` green post-`inv web`. The chapter
dep-graph at `blueprint/web/dep_graph_document.html` is the
authoritative lemma index. The post-closure cleanup round opens at
`notes/Phase9-cleanup.md` and the parallel perf pass at
`notes/Phase9-perf.md`.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Match Phase 7's matroidal regime: simple graphs, $\ell < 2k$,
  both ranges in scope.** Lee–Streinu state results for *multi-graphs*
  with loops, covering $\ell \in [0, 2k)$. We work in `SimpleGraph V`,
  matching the regime of `CountMatroid.lean` and `Sparsity.lean`
  exactly. Loops in L-S's lower range $\ell < k$ contribute single-
  vertex blocks; their absence in `SimpleGraph`-land changes the
  corner-case structure but not the overall theory — the lower range
  is genuinely interesting (tree-packing / arboricity applications,
  cf. Nash-Williams–Tutte) and stays in scope. The corner-case
  verification of L-S Lemmas 10–14 against `SimpleGraph` cleared as
  Phase 9-cleanup bucket A3 (audit-only, no Lean changes). Lifting to
  multi-graphs is a much larger project (no mathlib `MultiGraph`
  infrastructure exists) and is out of scope.

- **Finset-first computability style with `[Fintype V] [DecidableEq V]`.**
  The repo defaults to `Set.ncard` + noncomputable definitions on
  `[Finite V]`. The pebble game needs `Finset (V × V)`-backed
  orientations and decidable equality end-to-end so `#eval` and
  `decide` actually run — the extracted-certificate output requires
  it, and `[Finite V]` carries no algorithmic content (you can't
  enumerate or build `Finset`s from it). `PebbleGame.lean` is a
  deliberate style island: `[Fintype V]` + `[DecidableEq V]` in
  signatures, `Finset.card` over `Set.ncard` in algorithm bodies,
  fully computable. See DESIGN.md *Pebble-game style island*.

- **Decouple algorithm state from input-graph shape.**
  `PartialOrientation V` and the algorithm body are defined purely
  on `V` and edge-insertion requests (`List (V × V)`), not on a
  specific `SimpleGraph V`. `SimpleGraph` enters only at the
  statement-level wrapper `runPebbleGame G k ℓ` and the soundness /
  correctness theorems. The four invariants (Lemma 10) are stated
  on orientation states, so they port unchanged to a future
  multi-graph version (which would just relax `no_antiparallel`).

- **Algorithm output: `Option (PartialOrientation V)`, witness via a
  post-composed theorem.** L-S's prose returns one of
  `{well-, under-, over-constrained, other}`; we collapse the success
  side to `some D'` (a partial orientation carrying L-S Invariants
  (1)–(4) via `Reachable k ℓ D'`) and recover the rejection-side
  blocking witness through a separate post-composed theorem
  `runPebbleGame_eq_none_imp_exists_witness`. The well-vs-under-vs-over
  trichotomy is a downstream corollary on the size of `peb(V)`,
  recovered without changing the algorithm shape. A structured `Sum`
  return was considered and dropped: the witness extraction pass over
  the DFS visited-set doesn't compose cleanly into `tryReachPebbleWith`
  (which only carries one `target`+walk, not a closure).

- **Single-phase scope: basic pebble game, both directions.** Phase 9
  covers L-S §3–§4 end-to-end: definitions, the four invariants,
  soundness, completeness, certificate-form correctness, and the
  matroidal-independence corollary. Deferred to potential later phases:
  the *component pebble game* (§5, $O(n^2)$); the Henneberg-sequence
  application (§6); circuit / redundancy detection (§6 end).

- **New file `CombinatorialRigidity/PebbleGame.lean`.** Slots after
  `LinearRigidityMatroid.lean` for related-material ordering. Imports
  `Sparsity.lean`, `Search/DFS.lean`, and `CountMatroid.lean` (added
  late in the phase for the matroidal-independence corollary —
  resolved the "no matroid dependency" open question toward
  *land in-phase*).

- **Forward-mode blueprint chapter `chapter/pebble-game.tex`.** Per
  the Phase 6+ convention. The chapter's dep-graph is the lemma
  index; this file does not duplicate it.

## Lemma checklist

**Maintained in the blueprint, not here.** All 22 dep-graph nodes
in `chapter/pebble-game.tex` are `\leanok`-tagged green; the
dep-graph closes.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **`PartialOrientation V` is option (i): `Finset (V × V)` bundled
  with `no_loops` + `no_antiparallel`.** Cleanest for definitions and
  invariants — `arcs.filter`-based `out`/`span`/`outOn` and
  `Finset.sum`-based `pebOn` derive directly. Out-adjacency for DFS
  uses an `outNbhd : V → Finset V` view; the `outList : V → List V`
  shim lands at the `-With`-variant boundary. Rejected (ii) `V →
  Finset V` (forces duplicated bookkeeping for `no_antiparallel`) and
  (iii) `V → V → Bool` (hostile to `Finset.card`-based counts).

- **Pebble counts: distinct Lean names per type.** Per-vertex `out v`
  / `peb k v`; per-subset `span V'` / `outOn V'` / `pebOn k V'`. Breaks
  the L-S `out_D(v)` / `out_D(V')` overload. `peb k v := k - out v`
  uses ℕ-subtraction directly — the algorithm's structural
  `out v ≤ k` invariant makes Invariant (1) (`peb + out = k`) follow
  from `Nat.sub_add_cancel`. The "avoid ℕ-subtraction" convention
  applies to *propositions*, not *definitions*.

- **Subset-level accounting via 3 building blocks + algebraic
  combine.** For path reversal and arc insertion, the natural shape
  is three independent unified additive identities (`span` / `outOn`
  / `pebOn` each keyed on endpoint position w.r.t. `V'`) combined by
  `omega` on a 2-way case split. The split-then-combine pattern keeps
  each building block trivial and confines case analysis to a single
  `omega`. Path reversal's
  `pebOn_add_outOn_reverse_eq` is then factored through the algebraic
  Invariant (2) helper `pebOn_add_span_add_outOn`, not a direct
  boundary-crossing argument; the helpers (`sum_out_eq_span_add_outOn`
  + `pebOn_add_span_add_outOn`) pay forward to
  `lem:pebble-game-invariants` itself.

- **Source-cardinality unified by a single `if-then-else` formula.**
  For a simple walk `p : DirectedWalk R u w`,
  `(p.arcsFinset.filter (·.1 = v)).card = 1` iff
  `v ∈ p.vertices ∧ v ≠ w` (else `0`); symmetrically for
  `reversedArcsFinset` with `≠ u`. The `nil` case handles itself
  (`v ∈ [u]` ∧ `v ≠ u` is `False`), so a single induction covers both
  cases. Pairing gives `out_reverse_add` (new-out + path-source =
  old-out + reversed-source), from which the three endpoint
  corollaries fall out by case-analysis.

- **`Reachable k ℓ` as an inductive predicate, not a `def` on
  reachable-from-empty walks.** Three constructors (`empty`,
  `reverse`, `addArc`) carry the per-move out-degree preconditions
  `D.out w < k` / `D.out u < k` and the threshold
  `ℓ + 1 ≤ peb k u + peb k v`. These are algorithmically free (the
  procedure enforces them at each call site) and make Invariant (1)
  survive the move. Threading `Reachable k ℓ D` as a *hypothesis*
  (not part of `tryAddEdgeWith.induct`'s motive, introduced before
  `induction ... generalizing D'`) keeps case bodies clean.

- **Unified size hypothesis `ℓ ≤ k * V'.card` on Invariants (3)/(4).**
  L-S's Lemma 10 splits the size condition into
  `|V'| ≥ 1 ∧ ℓ ≤ k` and `|V'| ≥ 2 ∧ k < ℓ < 2k`. Both imply the
  single inequality, which is what the empty base case actually
  needs; downstream callers re-derive the regime-dependent form from
  `ℓ < 2k` plus the relevant `V'.card` bound. No information loss
  because the inductive step has the same arithmetic content either
  way. The blueprint chapter notes the form-mismatch inline.

- **`tryAddEdge` predicate excludes both endpoints (`w ≠ u ∧ w ≠ v`),
  not just `w = source`.** A path-reversal ending at the *other*
  endpoint shifts a pebble *between* `u` and `v`, leaving
  `peb k u + peb k v` unchanged and the termination measure stuck.
  The exclusion clauses guarantee strict decrease per reversal.
  Termination measure is `(ℓ + 1) - (peb k u + peb k v)`.

- **`Reach` closure as noncomputable `Finset.univ.filter`, not an
  exhausted-DFS computable mirror.** `reachClosure (R) [Fintype V]
  (v) : Finset V := Finset.univ.filter (Relation.ReflTransGen R v ·)`
  via `Classical.decPred`. Fine because the algorithm side never
  materialises the full closure (only DFS-finds single matches via
  `tryReachPebbleWith`); the closure surfaces only on the
  completeness side's blocking-witness construction
  (`D.reach u ∪ D.reach v`).

- **Soundness bridge factored into three pieces.**
  `sym2_mk_injOn_arcs` (injectivity from `no_antiparallel`,
  generic) + `image_spanArcs_eq_edgesIn` (the one place `G.edgeFinset`
  enters) + `Set.InjOn.ncard_image` combines to
  `span_eq_ncard_edgesIn` (`D.span V' = (G.edgesIn ↑V').ncard` under
  the underline identity). Soundness `runPebbleGame_sound` is then a
  one-`rw` assembly on top of `Reachable.span_add_le` (Invariant (4)),
  `runPebbleGame_underline_eq_edgeFinset`, and the bridge. The
  blueprint's `ℓ < 2k` regime hypothesis is not propagated to Lean —
  `IsSparse`'s definition gates on `ℓ ≤ k * V'.card` directly.

- **Lemma 13 stated algebraically; SimpleGraph wrapper builds on
  top.** `Reachable.independent_brings_pebble` takes abstract `V'`
  with `D.outOn V' = 0` + post-insertion span bound + below-threshold
  hypothesis. The Reach-closure shape is committed only in the
  SimpleGraph-form wrapper, which adds the closure-to-zero bridge
  `outOn_eq_zero_of_closed` + `outOn_reach_union_eq_zero`, the
  post-insertion sparsity bridge
  `span_succ_le_edgesIn_ncard_of_insert` (later broadened to
  `_of_subset` for fold-level reuse — see DESIGN.md
  *Strengthen the existing lemma*), and the size-hypothesis discharge
  from `|V'| ≥ 2` + `ℓ < 2k`. The matroidal-regime hypothesis enters
  only at the size-discharge step — the algebraic core stays
  regime-agnostic.

- **Correctness theorems in a fresh `section Correctness` with
  explicit `[Fintype V]`.** Inside `section Completeness` (which has
  `variable [Fintype V]` autobound on `runPebbleGameWith`), the
  wrapper-level theorems triggered `linter.unusedSectionVars` even
  though the variable IS used transitively via `runPebbleGame G k ℓ`.
  Moving to a fresh section + stating `[Fintype V]` explicitly
  satisfies both `unusedSectionVars` and `unusedFintypeInType`. The
  fold-level helper stays inside `section Completeness` (its
  autobinding is genuinely surfaced via the recursive self-call).

- **DFS warmup: `DirectedWalk` inductive, `succ : V → List V`,
  single-function body via `List.findSome?`.** Mirrors
  `SimpleGraph.Walk` with `nil`/`cons`. `List V` over `Finset V`
  keeps the algorithm computable (`Finset.toList` is mathlib-
  noncomputable). A first attempt used a `mutual` block but
  structural recursion failed on `List {u // u ∈ succ v}`; the
  single-function shape with `(succ v).attach.findSome?` lets Lean's
  WF tactic see through the recursive call and the
  `(Finset.univ \ visited).card` measure dispatches in one
  `decreasing_by` proof.

- **`dropUntilBundle` returns a `Subtype` rather than def + lemmas.**
  Truncating a `DirectedWalk` at the first occurrence of a target
  vertex needs three artefacts (truncated walk, length-bound,
  vertex-subset witness). The first-attempt split into separate def
  + lemmas hit `simp [dropUntil]` not reducing through the body's
  `subst h`; bundling into a single `Subtype`-returning definition
  handles all three obligations per branch with one-liners and avoids
  the equational-rewrite chase. Reusable wherever a dependently-
  indexed inductive needs truncation with auxiliary witnesses.

- **Completeness needs an inner length-induction on top of
  `reachableFindingAux.induct`.** The walk-revisit branch
  (`v ∈ p'.vertices`) hands off to the inner IH at the *same*
  `visited` via `dropUntilBundle`; the no-revisit branch hands off
  to the outer IH at `(insert v visited, v')`. The user-facing
  `ReflTransGen` lift uses `Relation.ReflTransGen.head_induction_on`
  (head-first recursion matches `DirectedWalk.cons`'s arc-at-head
  shape).

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *`induction _ using funName.induct` on a function with `let` in its
  body trips three closely-related quirks* → TACTICS-QUIRKS § 19;
  FRICTION *[resolved] `induction _ using funName.induct` binder count
  + inner-`let` shadowing*.
- *`rw [D.field_eq]` motive failure when another local's type
  references `D.field`* → TACTICS-QUIRKS § 18; FRICTION *[resolved]
  `rw [D.field_eq]` fails motive when a local's type references the
  field*.
- *`rw` over a cons-pattern endpoint variable trips motive on the
  sibling walk's type* → FRICTION *[resolved] `rw` over a cons-pattern
  endpoint variable trips motive on the sibling walk's type*.
- *`ring` treats alpha-renamed `Finset.sum`s as distinct atoms* →
  FRICTION *[resolved] `ring` treats alpha-renamed `Finset.sum` as
  distinct atoms*.
- *`Finset.toList` is noncomputable — math/exec layer split* →
  FRICTION *[resolved] `Finset.toList` is noncomputable*; DESIGN.md
  *Pebble-game style island → Math layer / exec layer split*.
- *`subst` between two free variables picks the wrong one (older)* →
  TACTICS-QUIRKS § 4 (existing); the `no_antiparallel` and
  `subst hvw : v = w` sites are Phase 9 instances.
- *`match h : <expr> with | pat => …` substitutes `expr ↦ pat`* →
  TACTICS-QUIRKS § 17; `runPebbleGame_correct`'s `match h_opt` is a
  Phase 9 instance.
- *Math / exec layer split + `-With` variant pattern for
  computable + noncomputable algorithm wrappers* → DESIGN.md
  *Pebble-game style island → Math layer / exec layer split + The
  `-With` variant pattern* (the `[Fintype V] [DecidableEq V]` style
  island itself is captured in *Architectural choices* above).

### Cleanup pass summaries

The post-closure cleanup round + perf pass run in parallel work logs:
- `Phase9-cleanup.md` (buckets A–D, currently bucket D in progress —
  see that file's *Current state* for status).
- `Phase9-perf.md` (module-system conversion of the two new files
  plus the broader cleanup-round-flagged structural levers, per
  `../CLEANUP.md` *What a cleanup round is not*).

## Blockers / open questions

All Phase 9 open questions resolved:

- ~~**Simple-graph vs L-S multi-graph corner cases.**~~ **Resolved**
  (Phase 9-cleanup A3, audit-only). L-S Lemmas 10–15 walk
  statement-by-statement against the simple-graph regime in
  `chapter/pebble-game.tex`'s `\emph{Multigraphs.}` paragraph: every
  L-S lemma in the matroidal regime specialises directly to
  SimpleGraph land, with Invariant (1)'s loop-free `span(v) = 0`
  collapse and the size-hypothesis unification `ℓ ≤ k|V'|` as the
  only two regime differences.
- ~~**Termination measure for `tryReachPebble`.**~~ **Resolved.**
  Inner DFS uses `(Finset.univ \ visited).card`; outer `tryAddEdge`
  loop uses `(ℓ + 1) - (peb k u + peb k v)`; outer `runPebbleGame`
  fold uses `edges.length` (structural on the list).
- ~~**`PartialOrientation V` representation.**~~ **Resolved as (i).**
  See *Decisions made → `PartialOrientation V` is option (i)*.
- ~~**Matroidal-independence corollary placement.**~~ **Resolved as
  *land in-phase*.** `SimpleGraph.countMatroid_indep_iff_runPebbleGame`
  lives in `section Matroidal` at the bottom of `PebbleGame.lean` via
  `_root_.SimpleGraph.`, mirroring `MatroidIdentification.lean`'s
  precedent. One import added (`CombinatorialRigidity.CountMatroid`);
  three-`rw` proof capped by `and_iff_right`. See *Architectural
  choices → New file `PebbleGame.lean`*.

## Hand-off / next phase

Phase 9 closes the basic pebble game end-to-end. No follow-up phase
is queued. Possible next directions:

- **Component pebble game (L-S §5, $O(n^2)$ speedup).** Out of scope
  for Phase 9 by initial design; uses a union pair-find data
  structure (Lee–Streinu–Theran 2005). A follow-up phase would need
  new state machinery + a fresh correctness theorem on top of the
  basic algorithm.
- **Henneberg-sequence application (L-S §6).** Out of scope for
  Phase 9 by initial design; would generalize Phase 3's
  Laman-specific Henneberg construction across $(k, \ell)$-matroidal
  regimes and connect to circuit / redundancy detection.
- **Multigraph generalization.** Out of scope by initial design; no
  mathlib `MultiGraph` infrastructure exists, and lifting the
  pebble-game state machinery to handle loops + parallel edges is a
  much larger project than the basic algorithm.
- **Post-Phase-9 cleanup round + perf pass.** Opened in
  `Phase9-cleanup.md` + `Phase9-perf.md`; see those files for status
  and round-level manual `../CLEANUP.md` / `PERFORMANCE.md` for
  discipline.
