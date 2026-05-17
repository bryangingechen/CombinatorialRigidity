# Phase 9 — Pebble game (work log)

**Status:** in progress.

This file is the per-phase work record. See `../ROADMAP.md` §9 for
the high-level plan and `../DESIGN.md` for cross-cutting design
choices.

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

Phase 9 is in progress. The forward-mode blueprint chapter
`chapter/pebble-game.tex` is the authoritative dep-graph and lemma
index; `PebbleGame.lean` ships the leaf-most state-machine
definitions `PartialOrientation V` (bundled `Finset (V × V)` with
`no_loops` and `no_antiparallel` invariants), the derived pebble
counts `out`, `peb`, `span`, `outOn`, `pebOn` (plus `empty` and
basic `simp`-level lemmas), the path-reversal move
`PartialOrientation.reverse D p hp` along a simple directed path
`p : DirectedWalk (· ∈ D.arcs) u w` with `hp : p.IsPath`, the
arc-insertion move `PartialOrientation.addArc D u v huv hnotin_rev`,
and the DFS-plus-path-reversal step `tryReachPebbleWith` / the
noncomputable convenience `tryReachPebble` (see *Decisions made →
`-With` pattern for math/exec split*).
The two `PartialOrientation` invariants (`no_loops`,
`no_antiparallel`) survive both moves. Structural per-vertex /
subset lemmas:

- *Path reversal*: `span_reverse_eq` (span invariant on every
  subset), `out_reverse_add` (unified additive identity for the
  head/tail/interior cases) with three corollaries
  `out_reverse_of_not_endpoint` / `out_reverse_head` /
  `out_reverse_tail`; pebble-count corollaries
  `peb_reverse_of_not_endpoint` / `peb_reverse_head` /
  `peb_reverse_tail` (the last two under the algorithmic
  preconditions `D.out u ≤ k` / `D.out w < k` mirroring
  `lem:pebble-game-invariants` (1)); subset-level
  `pebOn_add_outOn_reverse_eq` routed through
  `pebOn_add_span_add_outOn` and `span_reverse_eq`.
- *Arc insertion*: `out_addArc_source` (source `u` gains one out-arc,
  under `(u, v) ∉ D.arcs`) and `out_addArc_of_ne_source`
  (non-source vertices unaffected); pebble-count corollaries
  `peb_addArc_source` (under `D.out u < k`) and
  `peb_addArc_of_ne_source`; subset-level unified additive
  identities `span_addArc` (`span` rises by `1` iff both endpoints in
  `V'`), `outOn_addArc` (`outOn` rises by `1` iff `u ∈ V'`, `v ∉ V'`),
  `pebOn_addArc` (`pebOn` drops by `1` iff `u ∈ V'`, under
  `D.out u < k`); combined identity `pebOn_add_outOn_addArc_add`
  (`pebOn + outOn` drops by `1` iff both endpoints in `V'`,
  unchanged otherwise) — direct algebraic consequence of the three
  building-block lemmas via `omega` on a 2-way case-split.

Supporting arc-swap and source-count infrastructure lives in
`Search/DFS.lean`: `mem_arcsFinset_imp`,
`reversedArcsFinset_eq_image_swap`, `card_reversedArcsFinset`,
`tail_mem_vertices`, `fst_mem_vertices_of_mem_reversedArcsFinset`,
`IsPath.notMem_snd_initial`, and the two source-cardinality lemmas
`IsPath.card_arcsFinset_filter_fst` /
`IsPath.card_reversedArcsFinset_filter_fst`. PebbleGame-level glue
(`arcsFinset_subset_arcs`, `disjoint_sdiff_reversedArcsFinset`,
`out_eq_card_filter_fst`, `IsPath.head_ne_tail_of_pos`) and the two
general structural identities `sum_out_eq_span_add_outOn`
(fiberwise + partition) and `pebOn_add_span_add_outOn` (L-S
Invariant (2) algebraic form under `∀ v ∈ V', out v ≤ k`) sit in
`PebbleGame.lean`. The `Reachable k ℓ : PartialOrientation V → Prop`
inductive predicate (empty / path-reversal / accepted-insertion
constructors with the move-validity preconditions
`D.out w < k` / `D.out u < k` and the L-S threshold
`ℓ + 1 ≤ peb k u + peb k v`) packages the algorithmic state-space;
the four invariants of L-S Lemma 10 are proved on `Reachable`
orientations: `Reachable.out_le` and `Reachable.peb_add_out_eq`
(Invariant (1)), `Reachable.pebOn_add_span_add_outOn`
(Invariant (2)), `Reachable.pebOn_add_outOn_ge` (Invariant (3), the
substantive piece, under unified size hypothesis
`ℓ ≤ k * V'.card`), `Reachable.span_add_le` (Invariant (4),
algebraic from (2) + (3); stated as `span + ℓ ≤ k * V'.card` per the
project's no-ℕ-subtraction-in-propositions convention). Blueprint
`def:partial-orientation`, `def:pebble-counts`, `def:path-reversal`,
`def:arc-insertion`, the new `def:reachable-orientation`, and
`lem:pebble-game-invariants` are all green.

The DFS-plus-path-reversal step `tryReachPebbleWith D P v succ h_succ`
(blueprint `def:tryReachPebble`) runs `Search.reachableFinding` along
a caller-supplied out-neighbour enumeration `succ : V → List V` with a
propositional witness `h_succ : ∀ {a b}, b ∈ succ a ↔ (a, b) ∈ D.arcs`,
transports the output walk to `D`'s arc relation via
`DirectedWalk.mapRel`, and packages the result as a
`TryReachPebbleResult D P v` (target vertex + walk + `IsPath` + `P`-
witness). The `noncomputable` math-layer wrapper
`tryReachPebble D P v` plugs in `succ := D.outList` /
`h_succ := D.mem_outList`; IO-driven callers use
`tryReachPebbleWith` directly with a `List`-shaped adjacency built
from input data and stay fully computable (verified by `#eval` on a
`Fin 3` example returning `some 1`). The new
`DirectedWalk.mapRel` / `mapRel_length` / `mapRel_vertices` /
`mapRel_isPath_iff` transport infrastructure lives in
`Search/DFS.lean`.

The phase target is Lee–Streinu Theorem 8 in certificate form:
$\mathtt{runPebbleGame}\,G$ returns either a `PartialOrientation`
satisfying the four invariants (witness of $(k, \ell)$-sparsity) or
a vertex subset $V'$ with $|E(G[V'])| > k|V'| - \ell$ (witness of
non-sparsity). The matroidal-independence corollary against
Phase 7's `CountMatroid` follows as a one-liner.

**Pre-Phase-9 DFS warmup — closed.** `CombinatorialRigidity/Search/DFS.lean`
(~360 LoC) ships `reachableFinding` (the primitive itself,
`(succ v).attach.findSome?` body + `(Finset.univ \ visited).card`
termination measure) and the full correctness theorem
(`reachableFinding_sound` + `reachableFinding_complete`). Build +
lint clean. The function is **fully computable**:
`succ : V → List V` (not `V → Finset V`) for child enumeration,
with `visited : Finset V` retained only for the math-layer
termination measure. `#eval reachableFinding succEx (· == 2) 0` on a
`Fin 4` example returns `some (2, [0, 1, 2])` — directly executable,
satisfying the `IO`-pipeline use case (parser → DFS → emitter) raised
mid-session. See *Decisions made → DFS warmup* below + DESIGN.md
*Pebble-game style island* (math/exec layer split paragraph) +
`FRICTION.md` *[resolved] `Finset.toList` is noncomputable* for the
design history. Blueprint `def:reachable-finding`,
`thm:reachable-finding-correct`, and `def:directed-walk` are all
green; `chapter/dfs.tex`'s dep-graph closes.

**Completeness shape.** Soundness used a strengthened helper +
`reachableFindingAux.induct` (auto-generated three-case recursor on
visited-revisit / `P v` hit / `findSome?` recurse); completeness
uses the same outer recursor, with an *inner* induction on a walk
length bound `n` to handle the recursive case's two sub-cases:
*(i)* walk revisits the current source `v` — extract a strictly
shorter walk from `v` via `DirectedWalk.dropUntilBundle` (a
`Subtype`-bundled truncation carrying its length-bound and
vertex-subset witnesses) and recurse via the inner IH at the
**same** `visited`; *(ii)* walk-tail avoids the enlarged
`insert v visited` and the outer IH at `(insert v visited, v')`
closes. Lifting the user-facing `ReflTransGen` hypothesis to an
explicit `DirectedWalk` uses `Relation.ReflTransGen.head_induction_on`
(head-first recursion, matching `DirectedWalk.cons`).

Next concrete commit: descend to `def:tryAddEdge` — the outer-loop
combinator that calls `tryReachPebbleWith` on each endpoint of a
candidate edge until the threshold `peb u + peb v ≥ ℓ + 1` is met
(insert) or both DFS attempts fail (reject + emit blocking-witness
subset). Outer-loop termination is measured by
`(ℓ + 1) - (peb u + peb v)`, which strictly decreases per successful
reversal (Lee–Streinu §3). See *Hand-off / next phase*.

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

### State and counts (Phase 9 main, opening commit)

- **`PartialOrientation V`: option (i), `Finset (V × V)` bundled
  with `no_loops` + `no_antiparallel`.** Cleanest for definitions
  and invariants — `arcs.filter`-based `out`/`span`/`outOn` and
  `Finset.sum`-based `pebOn` derive directly. Out-adjacency for DFS
  uses a `outNbhd : V → Finset V` view (`arcs.filter (·.1 = v) |>
  .image Prod.snd`); the `outList : V → List V` shim lands with
  `tryReachPebble`. Rejected (ii) `V → Finset V` (forces duplicated
  `(u, v)` / `(v, u)` bookkeeping for `no_antiparallel`) and (iii)
  `V → V → Bool` (hostile to `Finset.card`-based counts).

- **Pebble counts: distinct Lean names per type to break the
  `out_D(v)` / `out_D(V')` overload.** Per-vertex `out v` and
  `peb k v`; per-subset `span V'`, `outOn V'` (arcs *leaving*
  `V'`), `pebOn k V'`. `peb k v := k - out v` uses ℕ-subtraction
  directly — the algorithm's structural `out v ≤ k` invariant
  makes Invariant (1) (`peb + out = k`) follow from
  `Nat.sub_add_cancel`. The "avoid ℕ-subtraction" project
  convention applies to *propositions*, not *definitions*.

### Path reversal (Phase 9 main)

- **Walk-arcs lemmas live in `Search/DFS.lean`, not
  `PebbleGame.lean`.** `DirectedWalk.arcsFinset` /
  `reversedArcsFinset` are pure `DirectedWalk` operations
  (independent of `PartialOrientation`); they belong in DFS.lean
  alongside the inductive itself. The downstream `IsPath`
  guarantees `notMem_loop_arcsFinset` /
  `notMem_antiparallel_arcsFinset` are the two facts the
  `PartialOrientation.reverse` invariants consume; the names sit
  in `DirectedWalk.IsPath` so dot notation `hp.notMem_…` works.

- **`obtain ⟨rfl, rfl⟩ := Prod.mk.inj …` on `(a, b) = (u_out, u_int)`
  in a `DirectedWalk` cons induction triggers motive issues.** The
  cons-pattern indices `u_out, u_int` ride on `q : DirectedWalk R
  u_int w`'s type, so an `rfl` substitution of `u_int := …` (or
  the follow-up `rw [← h_eq]`) tries to rewrite `u_int` in `q`'s
  type and fails with *motive is not type correct*. Same shape as
  `TACTICS-QUIRKS.md` § 4 (subst between two free variables) but
  the failure surfaces at the next `rw`, not at the `obtain`. Fix:
  bind the pair equalities to named hypotheses (`have h_uo : v =
  u_out := (Prod.mk.inj heq).1`), rewrite only in goals whose
  ambient terms don't depend on the substituted variable, and
  factor the "head vertex is in `vertices`" obligation through a
  one-line `head_mem_vertices` helper rather than `cases q <;>
  simp [vertices]`. The helper is `@[simp]`, will be reused by
  the structural-lemma commit. See FRICTION `[resolved] `rw` over a
  cons-pattern endpoint variable trips motive on the sibling
  walk's type`.

- **Source-cardinality lemmas unify head/tail/interior via a single
  `if-then-else` formula keyed on `IsPath`.** For a simple walk
  `p : DirectedWalk R u w`, `(p.arcsFinset.filter (·.1 = v)).card`
  is `1` iff `v ∈ p.vertices ∧ v ≠ w` (and `0` otherwise);
  symmetrically for `reversedArcsFinset` with the `≠ w` clause
  replaced by `≠ u`. The formula handles `nil` walks correctly
  without a special `0 < length` clause (when `nil u`, `v ∈ [u]`
  combined with `v ≠ u` is automatically `False`), so a single
  induction on `p` covers both cases. Pairing the two lemmas gives
  the unified additive identity `out_reverse_add` (new-out + path-
  source = old-out + reversed-source), from which the three
  endpoint corollaries fall out by case-analysis on whether `v` is
  on `p.vertices` and which endpoint it is.

- *`rw [D.field_eq]` motive failure when another local's type
  references `D.field`* → TACTICS-QUIRKS § 18, FRICTION
  *[resolved] `rw [D.field_eq]` fails motive when a local's type
  references the field*. Bit `out_reverse_add` first; the
  `Finset.ext`-based workaround will apply again at the subset-
  level reversal lemma.

- **`pebOn_add_outOn_reverse_eq` factored through algebraic
  Invariant (2), not direct boundary-crossing.** The hand-off
  suggested mirroring `span_reverse_eq` (swap-symmetry on path-arc
  predicates), which would have required a "boundary-crossing
  telescoping" argument on path-arc indicators. Instead, landed two
  general structural helpers — `sum_out_eq_span_add_outOn`
  (fiberwise + partition) and `pebOn_add_span_add_outOn` (L-S
  Invariant (2) algebraic form under `∀ v ∈ V', out v ≤ k`) — and
  derived the reverse-invariance as a three-line corollary
  combining the algebraic identity on both `D` and `D.reverse` with
  `span_reverse_eq`. The structural helpers are useful infrastructure
  for `lem:pebble-game-invariants` itself, so they pay forward.

### Arc insertion (Phase 9 main)

- **`addArc` def takes `(v, u) ∉ D.arcs` as the only non-trivial
  precondition; `(u, v) ∉ D.arcs` is a separate hypothesis on the
  accounting lemmas.** The `no_antiparallel` invariant requires
  `(v, u) ∉ D.arcs`; `no_loops` requires `u ≠ v`. Both are intrinsic
  to "this is a valid move." But the per-vertex `out_addArc_source`
  / `peb_addArc_source` lemmas additionally need `(u, v) ∉ D.arcs`
  so that `Finset.insert (u, v) D.arcs` is a genuine extension; if
  the arc is already in `D.arcs`, the `out` count is unchanged and
  the +1 conclusion fails. Putting this on the lemmas (rather than
  on the def) keeps the move's domain wide and the accounting tight.
  The pebble game's actual `tryAddEdge` will discharge both
  `(u, v) ∉ D.arcs` and `(v, u) ∉ D.arcs` from the input invariant
  "edge `{u, v}` is fresh."

- **Subset-level accounting: three building blocks + algebraic
  combine, not a direct combined-identity proof.** The natural shape
  is three independent unified additive identities
  (`span_addArc` / `outOn_addArc` / `pebOn_addArc`, each keyed on
  position of `u`, `v` relative to `V'`), then combine them by `omega`
  on a 2-way case split (`u ∈ V'` × `v ∈ V'`). The arc-insertion
  case has 4 sub-cases (vs path reversal's 3 endpoint cases), and the
  direct boundary-crossing approach would need to track all 4 in one
  proof. The split-then-combine pattern makes each building block
  trivial (`Finset.filter_insert` + `Finset.card_insert_of_notMem` for
  span/outOn; `Finset.add_sum_erase` + `peb_addArc_source` for pebOn)
  and confines case analysis to a single 4-line `omega` block. The
  same `pebOn + outOn` shape (drops by `1` iff both endpoints in `V'`,
  unchanged otherwise) is what `lem:pebble-game-invariants` (3)
  consumes at the arc-insertion step.

- **`rw [Finset.sum_congr rfl h]` cross-form `omega` trap.** When
  rewriting one of two `Finset.sum`s via `Finset.sum_congr rfl h`,
  the rewriter produced the LHS sum in `s.sum (fun x => f x)` form
  while the RHS sum stayed in `∑ x ∈ s, f x` notation —
  `omega` sees these as *different atoms* and fails with a
  counterexample suggesting two unrelated naturals. Fix: produce
  *both* sums via the same operation (here `← Finset.add_sum_erase`
  symmetrically on both sides, then `rw` the sum-congr equation as a
  packaged `have`) so the atomic shapes match. Below FRICTION
  threshold; recorded here for the pattern.

- **`subst h` between two free variables in `no_antiparallel`
  eliminates `u`/`v` (older), not `a`/`b` (newer).** Inside the
  `no_antiparallel a b hab hba` lambda body, `subst h1 : a = u`
  was substituting `u := a` rather than `a := u` (older-wins
  heuristic). Symptom: `Unknown identifier u` at the follow-up
  `have h3 : v = u := …` line. Fix: replace `subst h1; subst h2`
  with `rw [h1, h2] at hba` so the `u`/`v` names stay in scope for
  the contradictions. This is the same trap as TACTICS-QUIRKS § 4
  on `Sym2`-induction `rfl, rfl` patterns; logged inline in the
  Lean as a single-line aside since the rule is already documented.

### Reachability and the four invariants (Phase 9 main)

- **`Reachable k ℓ` as an inductive predicate over `PartialOrientation V`.**
  Three constructors: `empty`, `reverse` (with the move precondition
  `D.out w < k` at the tail), `addArc` (with `huv : u ≠ v`,
  `hnotin / hnotin_rev` for both directions, `hu_out : D.out u < k`,
  and the L-S threshold `ℓ + 1 ≤ peb k u + peb k v`). The two
  per-move out-degree preconditions are what makes Invariant (1)
  (`out v ≤ k`) survive the move; they're algorithmically free
  because the actual pebble game enforces them (`tryReachPebble`
  only fires when the tail has a free pebble; `tryAddEdge` only
  adds an arc from an endpoint with a free pebble).

- **Size hypothesis on Invariants (3)/(4): unified `ℓ ≤ k * V'.card`.**
  L-S's Lemma 10 splits the size condition into
  `|V'| ≥ 1 ∧ ℓ ≤ k` and `|V'| ≥ 2 ∧ k < ℓ < 2k`. Both imply the
  single inequality `ℓ ≤ k * V'.card`, which is what the empty base
  case actually needs (`pebOn_empty V' + outOn_empty V' = k * V'.card`
  must be `≥ ℓ`). The unified form drops the case-split at the
  statement level; downstream callers (`thm:pebble-game-soundness`
  etc.) can re-derive the regime-dependent form from `ℓ < 2k` and
  the relevant `V'.card` bound. No information loss because the
  inductive step has the same arithmetic content either way.

- **Invariant (4) stated as `span V' + ℓ ≤ k * V'.card` (additive
  form).** The blueprint says `span V' ≤ k|V'| - ℓ` (with
  ℕ-subtraction); the Lean statement is rephrased per the project's
  no-ℕ-subtraction-in-propositions convention
  (ROADMAP *Engineering conventions*). The two are equivalent under
  the implicit `ℓ ≤ k * V'.card` hypothesis. The blueprint entry
  for `lem:pebble-game-invariants` calls out the difference inline
  so a reader following the Lean source isn't confused by the form
  mismatch.

- **Invariant (1) reverse case: `out_reverse_add` collapses to a
  `split_ifs` + `omega` after one `by_cases hvw : v = w` /
  `by_cases hvu : v = u`.** The unified additive identity gives
  `(reverse).out v + I[v ∈ p.vertices ∧ v ≠ w] = D'.out v +
  I[v ∈ p.vertices ∧ v ≠ u]`; for `v = w` the LHS indicator is
  always `0` (`v ≠ v` false), leaving `(reverse).out v = D'.out v +
  I_RHS`, which `D'.out w < k` absorbs via `omega`. For `v = u`
  symmetric (RHS indicator zero). For `v` distinct from both
  endpoints, `out_reverse_of_not_endpoint` (no `0 < p.length`
  precondition) reduces to the IH directly.

- **`subst hvw : v = w` (with `v` outer-bound and `w` constructor-
  bound) eliminates the older `v`.** Per TACTICS-QUIRKS § 4, the
  older free variable goes. After subst, the goal's `v`s become
  `w`s and the IH `D'.out v ≤ k` becomes `D'.out w ≤ k`, which
  composes cleanly with `hw : D'.out w < k`. (Same trap shape as
  the `no_antiparallel` subst above, but here the direction
  happens to be what we want — no `rw`-workaround needed.)

- **`peb_pair_le_pebOn` helper for the addArc inductive step of
  Invariant (3).** When the inserted arc has both endpoints in
  `V'`, the threshold precondition `ℓ + 1 ≤ peb u + peb v` needs to
  be lifted to `ℓ + 1 ≤ pebOn V'` to absorb the `pebOn + outOn`
  shift's `−1`. The helper is a one-liner around `Finset.sum_pair`
  + `Finset.sum_le_sum_of_subset` (the latter requires
  `CanonicallyOrderedAdd`, which ℕ satisfies). Kept as a local
  helper in `PebbleGame.lean` rather than mirrored: it's specific
  to `peb`/`pebOn` and not upstream-eligible.

### `tryReachPebble` (Phase 9 main)

- **`-With` pattern for math/exec split.** `tryReachPebble`'s naive
  realisation (call `reachableFinding` on `D.outList`) is
  noncomputable because `D.outList` goes through `Finset.toList`
  (mathlib-noncomputable; see FRICTION *[resolved] `Finset.toList` is
  noncomputable*). The user surfaced this as a real concern: an
  IO-driven implementation (parser → DFS → emitter) would `#eval`-fail
  on the whole pipeline. Adopted the *`-With` variant* pattern:
  computable workhorse `tryReachPebbleWith D P v succ h_succ` takes a
  caller-supplied `succ : V → List V` plus a propositional agreement
  witness `h_succ`; math-layer convenience `tryReachPebble D P v` is
  a one-line noncomputable wrapper plugging in `succ := D.outList`.
  Downstream sound/complete theorems will land on the workhorse and
  inherit to the wrapper for any `succ`. Verified end-to-end on a
  `Fin 3` example: `#eval ... |>.map (·.target) = some 1`. Promoted
  to DESIGN.md *Pebble-game style island → The `-With` variant
  pattern* as the general realisation rule for subsequent layers
  (`tryAddEdge`, `runPebbleGame`).
- **`DirectedWalk.mapRel` for relation transport.**
  `reachableFinding` returns a walk along `fun a b => b ∈ succ a`;
  `PartialOrientation.reverse` consumes a walk along
  `fun a b => (a, b) ∈ D.arcs`. The `mapRel` family
  (`mapRel` + `mapRel_length` + `mapRel_vertices` +
  `mapRel_isPath_iff`) bridges via the `h_succ` propositional
  witness, preserving every walk attribute. Lives in `Search/DFS.lean`
  alongside the rest of the `DirectedWalk` API.

### DFS warmup (pre-Phase-9)

- **Style island formalized in DESIGN.md.** Phase 9's architectural
  choice 2 (`[Fintype V] [DecidableEq V]` end-to-end for the pebble-
  game line) is now documented as a fixed section in `../DESIGN.md`
  *Pebble-game style island*. The DFS file is the first instance of
  the style island, so the note landed with the scaffold commit
  rather than waiting for `PebbleGame.lean`. Both files (DFS warmup
  + Phase 9 main) referenced.

- **`DirectedWalk` is inductive, indexed by endpoints.** Mirroring
  `SimpleGraph.Walk`, with `nil`/`cons` constructors and `length` /
  `vertices` / `IsPath := vertices.Nodup` accessors. Rejected
  alternative: `{ p : List V // p ≠ [] ∧ p.Chain' R ∧ … }` subtype —
  more compact but noisier proof-engineering at every `cons` /
  case-split. The inductive shape matches the project / mathlib idiom
  for walks and keeps the API surface low.

- **Relation as `succ : V → List V` plumbed via the predicate
  `fun a b => b ∈ succ a`.** `DirectedWalk` itself stays parametric
  over an abstract `R : V → V → Prop`; the DFS function passes the
  out-neighbour-membership relation to it. The signature uses
  `List V` rather than `Finset V` so the algorithm is fully
  computable — `Finset.toList` is noncomputable in mathlib (see
  *Decisions made → math/exec layer split*), and an enumeration-based
  DFS body propagates that. Callers holding adjacency data in
  `Finset` form expose a list projection at the DFS boundary; the
  projection itself can stay noncomputable in isolation without
  contaminating the algorithm.

- **Predicate `P : V → Bool`, completeness against `ReflTransGen`.**
  `P : V → Bool` matches the blueprint exactly (decidable by
  construction; `decide` fires). The completeness theorem quantifies
  against `Relation.ReflTransGen (fun a b => b ∈ succ a) v w` rather
  than via the walk type itself — separates "is reachable" from
  "carries a walk witness" cleanly.

- **Body: single-function with `List.findSome?` over mutual
  recursion.** Initial attempt used a `mutual` block with separate
  `reachableFindingAux` / `reachableFindingChildren` helpers, but
  structural recursion failed because the children-list parameter
  has type `List {u // u ∈ succ v}` — depending on the function
  parameter `v`. Restructured to a single `reachableFindingAux` that
  iterates children inline via `(succ v).attach.findSome?`, with the
  recursive call inside the lambda. Lean's WF tactic sees through
  `List.findSome?` to the recursive call and the
  `(Finset.univ \ visited).card` measure dispatches in one
  `decreasing_by` proof.

- **Math/exec layer split: `succ : V → List V`, `visited : Finset V`.**
  `Finset.toList` is noncomputable in mathlib (it lifts through
  `Multiset.toList`'s `Classical`-flavored `Quotient.lift`), so an
  enumeration-based DFS body taking `succ : V → Finset V` would
  silently force the whole algorithm `noncomputable`. The DFS warmup
  was first drafted with `Finset` and observed the friction; we
  refactored to `succ : V → List V` (exec layer, computable) while
  keeping `visited : Finset V` (math layer, needed for
  `Finset.univ \ visited`'s cardinality termination measure). Sanity
  check: `#eval reachableFinding succEx (· == 2) 0` returns
  `some (2, [0, 1, 2])` on a `Fin 4` example. Phase 9 main's
  `PartialOrientation V` is expected to follow the same pattern:
  store as `Finset (V × V)` internally for invariants, expose
  `outList : V → List V` at the DFS boundary. See FRICTION.md
  *[resolved] `Finset.toList` is noncomputable* + DESIGN.md
  *Pebble-game style island*.

- **`[Fintype V]` bound explicitly on `reachableFindingAux`, not just
  via `variable`.** Adding `[Fintype V] [DecidableEq V]` as section
  variables and letting them auto-bind to the recursive def produced
  a confusing *"MVar does not look like a recursive call"* error —
  `[Fintype V]`, used only in `termination_by`'s `Finset.univ`,
  landed at the *end* of the auto-bound signature (`... → V → Fintype
  V`), confusing Lean's recursive-call recognition. Pinning the
  typeclasses explicitly on the def fixes it; cheap and clear.

- **`dropUntilBundle` returns a `Subtype`, not separate def +
  lemmas.** Truncating a `DirectedWalk` at the first occurrence of a
  target vertex needs three artefacts: the truncated walk itself
  (changing the `(u, w)` endpoint indices), a length-bound, and a
  vertex-subset witness. First-attempt split this into `dropUntil`
  (def) + `dropUntil_length_le` + `mem_dropUntil_vertices` (lemmas),
  but the def's body uses `subst h` to rewrite the index variable
  (so the inductive case `cons` produces a walk with the *substituted*
  endpoint), and `simp [dropUntil]` doesn't reduce through the tactic-
  mode `subst` cleanly — the lemmas need to chase the same `subst`
  via `rfl`-blocked equational rewrites. Bundling into a single
  `Subtype`-returning definition with one `induction p` handles all
  three obligations per branch (`refine ⟨walk, ?_, ?_⟩` + close each
  with a one-liner) and avoids the equational-rewrite chase entirely.
  Pattern is reusable wherever a dependently-indexed inductive needs
  truncation with auxiliary witnesses.

- **Inner length-induction for completeness's recursive case.**
  Helper `reachableFindingAux_complete` proves the contrapositive:
  if the aux returns `none`, no walk from `v` to a `P`-satisfying
  vertex avoiding `visited` exists. Outer induction is via
  `reachableFindingAux.induct` (same as soundness), but the recursive
  case can't go through directly — when the walk revisits the current
  source `v`, the walk-tail violates `∀ x ∈ p'.vertices,
  x ∉ insert v visited`. Adding an inner induction on a length bound
  `n` lets that branch recurse on the *same* `visited` via
  `dropUntilBundle`, while the *no-revisit* sub-branch hands off to
  the outer IH at `(insert v visited, v')` as expected. The
  `ReflTransGen → DirectedWalk` lift in the user-facing theorem uses
  `Relation.ReflTransGen.head_induction_on` (head-first recursion
  matches `DirectedWalk.cons`'s arc-at-head shape).

## Blockers / open questions

- **Simple-graph vs L-S multi-graph corner cases — Lemma 10 cleared.**
  L-S's Lemma 10 has `span(v)` (= loops at `v`) appearing additively
  in Invariant (1); SimpleGraph's loop-free regime makes `span(v) = 0`
  always, so the per-vertex invariant collapses to
  `peb v + out v = k` with no further case-split. Invariant (3)'s
  size condition (`|V'| ≥ 1` for `ℓ ≤ k`, `|V'| ≥ 2` for `k < ℓ < 2k`)
  is unified in the Lean statement as `ℓ ≤ k * V'.card`, which both
  cases imply. The substantive piece (Invariant (3)'s arc-insertion
  step) goes through cleanly for both ranges, since the
  `peb_pair_le_pebOn` lift of the threshold precondition doesn't
  depend on the regime. **Remaining work** in this open question:
  trace L-S Lemmas 13–15 through SimpleGraph-eyes for the
  completeness side. Expected to clear similarly (Lemma 13's
  `Reach(u) ∪ Reach(v)` is always `≥ 2`-sized when `u ≠ v`, which
  matches the upper-range size constraint).

- **Termination measure for `tryReachPebble`.** Path reversal in
  L-S is bounded informally by "at most $\ell$ DFS searches per
  edge"; for Lean, an explicit decreasing measure is needed. Pattern
  model is `Batteries.UnionFind` (`termination_by self.rankMax -
  self.rank x` — a strictly-decreasing numeric measure on a finite
  data structure). For the inner DFS,
  `(Finset.univ \ visited).card` is the natural measure (visited
  grows monotonically, vertex set is finite). For the outer
  `tryAddEdge` loop, `(ℓ + 1) - (peb u + peb v)` decreases per
  successful path-reversal. The pre-Phase-9 DFS warmup (see
  *Current state*) exercises this pattern in isolation. Friction-
  log entry expected at the termination-proof commit.

- **`PartialOrientation V` representation — resolved as (i).** Bundle
  `arcs : Finset (V × V)` with the two invariants `no_loops` and
  `no_antiparallel`; see *Decisions made → `PartialOrientation V`
  representation*. Out-adjacency uses (ii) only at the DFS boundary
  via a `outNbhd : V → Finset V` shim derived as
  `arcs.filter (·.1 = v) |>.image Prod.snd`, with a `outList`
  projection (List V) to follow when `tryReachPebble` lands. Refactor
  to (ii) or (iii) only if `tryReachPebble`'s termination proof
  surfaces a structural problem.

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

Phase 9 main is in progress. `PebbleGame.lean` now carries:

* Both state-transition moves with per-vertex *and* subset-level
  preservation lemmas: path reversal (`reverse` + `out_reverse_*` /
  `peb_reverse_*` / `span_reverse_eq` / `pebOn_add_outOn_reverse_eq`)
  and arc insertion (`addArc` + `out_addArc_source` /
  `out_addArc_of_ne_source` / `peb_addArc_source` /
  `peb_addArc_of_ne_source` / `span_addArc` / `outOn_addArc` /
  `pebOn_addArc` / `pebOn_add_outOn_addArc_add`).
* The supporting general structural identities
  `sum_out_eq_span_add_outOn` (fiberwise + partition) and
  `pebOn_add_span_add_outOn` (L-S Invariant (2) algebraic form
  under `∀ v ∈ V', out v ≤ k`).
* The `Reachable k ℓ : PartialOrientation V → Prop` inductive
  predicate packaging the algorithmic state-space (empty,
  path-reversal under `D.out w < k`, accepted insertion under
  `D.out u < k` + `ℓ + 1 ≤ peb k u + peb k v`).
* The four pebble-game invariants of L-S Lemma 10 as
  `Reachable.out_le`, `Reachable.peb_add_out_eq`,
  `Reachable.pebOn_add_span_add_outOn`,
  `Reachable.pebOn_add_outOn_ge` (substantive piece, under unified
  size hypothesis `ℓ ≤ k * V'.card`), and `Reachable.span_add_le`
  (additive form of the blueprint's `span ≤ k|V'| - ℓ` per project
  convention).
* The DFS-plus-path-reversal step (blueprint `def:tryReachPebble`):
  computable workhorse `tryReachPebbleWith D P v succ h_succ` taking
  a caller-supplied `succ : V → List V` and the propositional
  agreement witness `h_succ`, math-layer convenience
  `tryReachPebble D P v` as a noncomputable wrapper specialising to
  `succ := D.outList`. Output `TryReachPebbleResult` bundles
  target / walk / `IsPath` / `P`-witness, with
  `TryReachPebbleResult.newOrient := D.reverse r.walk r.isPath` as
  the post-reversal-orientation accessor.

Supporting `Search/DFS.lean` infrastructure: existing arc-swap /
endpoint-membership / source-cardinality lemmas unchanged, plus new
relation-transport family `DirectedWalk.mapRel` /
`mapRel_length` / `mapRel_vertices` / `mapRel_isPath_iff`.
Blueprint `def:partial-orientation`, `def:pebble-counts`,
`def:path-reversal`, `def:arc-insertion`,
`def:reachable-orientation`, `lem:pebble-game-invariants`, and
`def:tryReachPebble` are all green. Build + lint clean.

Next concrete commit: **`def:tryAddEdge`** — the outer-loop
combinator that processes one candidate edge `{u, v}` against the
current orientation `D`. Repeatedly calls `tryReachPebbleWith` on
`u`'s and `v`'s endpoints with the target predicate
`fun w => 0 < D.peb k w` (free pebble at `w`), folding each
successful reversal back into `D`, until either
`peb k u + peb k v ≥ ℓ + 1` (insert `(u, v)` via
`PartialOrientation.addArc`) or both DFS attempts fail (reject,
returning the reachability closure as a blocking witness). Outer-loop
termination is by `(ℓ + 1) - (peb k u + peb k v)`, which strictly
decreases per successful reversal (Lee–Streinu §3). The `-With`
pattern propagates: `tryAddEdgeWith` takes the user's `succ`, the
math-layer `tryAddEdge` is the noncomputable wrapper.

Subsequent commits descend the dep-graph:
`def:tryAddEdge` → `def:runPebbleGame` (fold over `E(G)` with the
outer-loop measure decreasing per accepted edge) →
`thm:pebble-game-soundness` (direct from Invariant (4) on the final
state) → completeness side
(`lem:pebble-game-independent-brings-pebble` /
`lem:pebble-game-tryAddEdge-iff-independent` /
`lem:pebble-game-failure-witness`) → `thm:pebble-game-correct` →
`cor:pebble-game-countMatroid-indep`. The completeness-side
SimpleGraph-vs-multigraph corner-case check (open question above)
is the only known open structural unknown.

Architectural question still open: *whether to land the matroidal-
independence corollary in-phase or defer* (weak preference: land —
cheap, ties the loop to Phase 7's `countMatroid`).
