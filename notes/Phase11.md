# Phase 11 — Witness extraction (work log)

**Status:** complete (closed by Layer 5 commit).

This file is the per-phase work record. See `../ROADMAP.md` §11 for
the high-level plan and `../DESIGN.md` for cross-cutting design
choices.

**Workflow:** Phase 11 is a **structural-edit phase**, not the usual
new-theorem-development phase. There is *no new blueprint chapter*;
the substantive Lean work reshapes existing Phase 9/10 algorithms
(`tryAddEdge` / `runPebbleGame` / `runPebbleGameExec`) from
`Option`-shaped to verdict-bearing returns, with the matching
blueprint updates landing **in place** in `chapter/dfs.tex`,
`chapter/pebble-game.tex`, and `chapter/executable.tex` alongside
each Layer's Lean. The phase's authoritative to-do list lives in
the *Layer plan* section below, not in a blueprint chapter.

**References.** Jacobs–Hendrickson 1997 §4 (blocking-set extraction
at failure as reach-closure of source vertices in the partial
orientation's directed digraph); Lee–Streinu 2008 §3 (the same in
$(k, \ell)$ generality). The algebraic content already lives in
Phase 9's `Reachable.independent_brings_pebble`; Phase 11 lifts the
surface return type to carry the witness as data. The Phase 9
`runPebbleGame_eq_none_imp_exists_witness`'s $V'$ was
mathematically `D.reach u ∪ D.reach v`, routed through the
noncomputable `Search.reachClosure`; Phase 10 closed
end-to-end-executability with only the trichotomy label
(both witness halves explicitly deferred).

## Current state

All five layers closed. The pebble game's user-facing surface is now
end-to-end witness-bearing: the math- and exec-layer wrappers
`runPebbleGame` / `runPebbleGameExec` return a verdict-bearing
`PebbleGameResult G k ℓ` directly, and the CLI prints the witness
data on both branches. Per-layer landings in *Layer plan* below;
phase-shape decisions in *Architectural choices*. The Phase 9/10
math-layer (`runPebbleGame`, `noncomputable`) vs. exec-layer
(`runPebbleGameExec`, computable via `[LinearOrder V]`) split
survives — what reshapes is the return type, not the math/exec
boundary.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Maximal reshape, not parallel extraction.** Phase 11's central
  design choice: replace the `Option (PartialOrientation V)` return
  of `runPebbleGameWith` / `runPebbleGame` / `runPebbleGameExec`
  with a verdict-bearing inductive end-to-end, rather than ship a
  parallel `runPebbleGameExec_blocking_witness` extraction wrapper.
  Phase 9's `_isSome` / `_eq_none_imp_exists_witness` chain
  (~200 LoC in `Correctness.lean`) is absorbed into `tryAddEdgeWith`'s
  case-5 inline witness construction; the `runPebbleGameExec_correct`
  iff (Phase 10) collapses into the verdict's type. Trade: a
  Phase-10-sized restate of the workhorse `_reachable` /
  `_underline_*` / `_sound` lemmas plus re-routing Phase 7 /
  Phase 10 wrappers through `.isAccept`. The mathematical content
  (`independent_brings_pebble`, the `Reachable` invariants) is
  preserved verbatim.

- **Blueprint reshape happens in-place, per Layer.** No new chapter.
  Each Layer commit ships its blueprint reshape in step with the
  Lean, so the dep-graph never has a long-lived red region in a
  chapter that was green. The per-Layer blueprint deltas are listed
  in *Layer plan* below.

- **Workhorse witness is algorithm-side data, no `G` parameter.** At
  the workhorse layer (`tryAddEdgeWith`, `runPebbleGameWith`), the
  witness structure is `G`-free; full field list in
  `PebbleGame/Basic.lean`'s `WorkhorseWitness` declaration and
  `chapter/pebble-game.tex` `def:workhorseWitness`. The `G`-shaped
  sparsity-violation certificate is recovered at the wrapper layer
  via `WorkhorseWitness.certifies_against`, whose body is the
  existing `Reachable.independent_brings_pebble_simpleGraph_form`
  content, unchanged. Rationale: adding `G` to the workhorse
  signature would propagate a `D.underline ⊆ G.edgeFinset` bridge
  hypothesis through every call site for no benefit; the wrapper
  layer is where the `G`-shaped story belongs.

- **User-facing verdict.** The wrapper layer returns
  `PebbleGameResult G k ℓ` with `.accept` (carrying the orientation,
  the `D.underline = G.edgeFinset` discharge, and the `Reachable`
  invariant) and `.reject` (carrying the blocking subset $V'$ with
  the inline `ℓ ≤ k * V'.card ∧ k * V'.card < (G.edgesIn ↑V').ncard + ℓ`
  certificate). Full inductive declaration in
  `PebbleGame/Correctness.lean` and blueprint
  `chapter/pebble-game.tex` *User-facing verdict* subsection
  (`def:pebbleGameResult`). The verdict's constructor *is* the
  certificate; the certificate-form iff theorems collapse into the
  *type* of the wrapper's return. Boolean projections
  `.isAccept : PebbleGameResult G k ℓ → Bool` drive the `Decidable`
  instances.

- **One unified `D.reach` def, computable.** Redefine
  `PartialOrientation.reach : V → Finset V` (previously
  `noncomputable def` via `Search.reachClosure`) directly through
  the new computable `reachClosureComputable`. The consumer-facing
  `mem_reach` iff against `Relation.ReflTransGen` is preserved
  unchanged; downstream proofs using only the iff are unaffected.
  Rationale: Phase 10's *One `Decidable` instance per predicate*
  principle generalises to *one canonical reduction body per
  algorithm-bearing definition*. The
  `[Fintype V] [DecidableEq V]` style island already supplies both
  typeclasses at every callsite.

- **`PebbleGameResult` placement** finalised at `Correctness.lean`,
  not `Exec.lean` as the opener proposed — the math-layer wrapper
  `runPebbleGame` needs the verdict's return type and sits above
  `Exec.lean` in the import chain. The exec-layer wrapper re-uses
  the same definition without re-declaring it. The `WorkhorseWitness`
  structure lives in `PebbleGame/Basic.lean` (parallel state, not
  derived from `PartialOrientation`); `WorkhorseWitness.certifies_against`
  in `PebbleGame/Correctness.lean` (where `independent_brings_pebble`
  already lives).

- **`reachClosureComputable` placement.** Added to `Search/DFS.lean`,
  sibling of the existing `reachableFinding`. Layer 1 addition was
  ~110 LoC, keeping the file at ~830 LoC, well under the ~1050-LoC
  split threshold; no `Search/Reachability.lean` split needed.

- **CLI surface (Layer 5).** Output schema (one row per verdict):
  ```
  LAMAN                 SPARSE_NOT_TIGHT      NOT_SPARSE
  ARCS u₀ v₀            ARCS u₀ v₀            BLOCKING <count>
  ARCS u₁ v₁            ARCS u₁ v₁            VERTEX w₀
  ...                   ...                   VERTEX w₁
                                              ...
  ```
  Backward-incompatible vs Phase 10's trichotomy-only format; the
  four `examples/*.txt`-shipped fixtures' commented expected-output
  blocks update accordingly. Scripts parsing only the trichotomy
  read the first line unchanged.

## Layer 0 audits — outcomes

All audits resolved in the opener commit; the *Layer plan* below
incorporates the outcomes.

1. **Witness-type unification across algorithm levels.** ✓ Both
   `tryAddEdgeWith`-level failure and `runPebbleGameWith`-level
   failure produce the same existential shape; the fold-level
   witness is the per-step witness propagated forward unchanged
   through the first `.inl`. One `WorkhorseWitness k ℓ V` suffices.
2. **`G`-parameter for `tryAddEdgeWith`.** ✗ Don't add — workhorse
   is `G`-free (rationale above).
3. **Verdict shape.** ✓ Two-constructor inductive (full shape in
   *Architectural choices: User-facing verdict* above).
4. **Math/exec split survives.** ✓ Reshape touches the return type
   only; the split rationale (`../DESIGN.md` *Pebble-game style
   island*) is orthogonal.
5. **`D.reach` unification.** ✓ One `def`, computable.
6. **Blueprint workflow.** ✓ Structural-edit phase; in-place
   reshape per Layer.
7. **`reachableFinding` factoring.** ✓ Resolved at Layer 1:
   `reachClosureComputable succ v` filters `Finset.univ` by
   `(reachableFinding succ (· = w) v).isSome`, with soundness and
   completeness reduced to `reachableFinding_sound` / `_complete`
   plus a small `DirectedWalk.toReflTransGen` bridge. The original
   plan envisioned a parallel accumulating DFS, but the proof
   effort for a custom WF recursion with `foldl`-over-children
   correctness against `Relation.ReflTransGen` was disproportionate
   to the math-layer benefit. Trade-off: $O(n)$ DFS invocations per
   closure (quadratic worst-case), not visible at the math layer
   since the closure is only materialised at the blueprint
   argument; future perf work could swap the implementation behind
   `mem_reachClosureComputable` without touching downstream.
8. **`Search/DFS.lean` file split.** ✓ Resolved in-file at Layer 1
   (file lands at ~830 LoC, under the ~1050 threshold).

## Layer plan

- **Layer 0** ✓. Phase opener: notes, ROADMAP §11 + status row,
  README / home_page / intro.tex flips. No Lean, no blueprint
  changes.

- **Layer 1** ✓. `reachClosureComputable` in `Search/DFS.lean`
  (~110 LoC). Routed through `reachableFinding` (audit point 7).
  `PartialOrientation.reach` redefined through the new primitive;
  stays `noncomputable` because of `outList`'s use of
  `Finset.toList`, but `mem_reach` iff preserved verbatim and
  downstream proofs re-derive cleanly. `Search.reachClosure`
  removed. Blueprint: `chapter/dfs.tex` gains
  `def:reachClosureComputable` + `lem:mem-reachClosureComputable`
  in a new *Reachability closure (computable)* subsection;
  `chapter/pebble-game.tex` updates closure-primitive mentions in
  `def:tryAddEdge` / `def:runPebbleGame`.

- **Layer 2** ✓. `WorkhorseWitness k ℓ V` in `Basic.lean` (outside
  `PartialOrientation` namespace — parallel state, not derived);
  `WorkhorseWitness.certifies_against` in `Correctness.lean` at
  end-of-file. The witness's `h_pebOn_le : D.pebOn k V' ≤ ℓ`
  strengthens the originally-proposed per-vertex
  `h_below : peb u + peb v ≤ ℓ` to absorb the DFS-failure
  "no free pebble outside `{u, v}`" guarantee into a single field
  (decision rationale in *Decisions made* below). Blueprint:
  `chapter/pebble-game.tex` gains `def:workhorseWitness` +
  `lem:workhorseWitness-certifies` immediately after
  `lem:pebble-game-independent-brings-pebble-graph`. Total Lean
  delta: ~80 LoC.

- **Layer 3** ✓. Workhorse reshape (~+500 LoC across
  `PebbleGame/{Basic, Algorithm, Correctness, Exec}.lean`, ~−300 LoC
  in `Correctness.lean` from absorption). `tryAddEdgeWith` returns
  `Sum (WorkhorseWitness k ℓ V) (PartialOrientation V)` and takes
  `hD : Reachable k ℓ D` (absorbing `h_outle`). The case-5 inline
  construction builds the `WorkhorseWitness` directly from `hD`,
  `hthr`, and the DFS-failure data; the `V'` field uses
  `reachClosureComputable (toSucc D)` so the workhorse stays
  computable (decision rationale in *Decisions made* below). The
  reach-closure-on-orientations API
  (`reach`, `mem_reach`, `self_mem_reach`, `reach_closed`,
  `outOn_eq_zero_of_closed`, `outOn_reach_union_eq_zero`) moves
  from `Correctness.lean` to `Basic.lean`. The
  `tryAddEdgeWith_isSome` / `*_eq_none_imp_exists_witness*` /
  `tryAddEdge_isSome_iff_sparse` chain eliminated;
  `tryAddEdgeWith_isSparse` (the surviving accept-implies-sparse
  half) restated against `.inr`. Two new helpers in `Algorithm.lean`
  (`tryAddEdgeWith_witness_uv`, `tryAddEdgeWith_witness_underline_eq`)
  plus one new bridge in `Correctness.lean`
  (`runPebbleGameWith_witness_bridges`) discharge the wrapper-level
  path from `.inl w` to `WorkhorseWitness.certifies_against`'s
  preconditions. `runPebbleGame_correct` /
  `runPebbleGameExec_correct` / `countMatroid_indep_iff_runPebbleGame`
  restated against `.inr`. Blueprint: `chapter/pebble-game.tex`
  updated for the new return shape; obsolete `lem:` nodes retired;
  `thm:pebble-game-correct` restated. `chapter/executable.tex`'s
  wrapper / Decidable nodes restated.

- **Layer 4** ✓. `PebbleGameResult G k ℓ` inductive in
  `Correctness.lean` (placement micro-decision: it sits above
  `Exec.lean` in the import chain). Initially shipped *additively*
  — parallel verdict-bearing wrappers `runPebbleGame_result` /
  `runPebbleGameExec_result` alongside the Layer 3 `Sum`-returning
  raw `runPebbleGame` / `runPebbleGameExec`; three `Decidable`
  instances re-routed through `.isAccept` of the wrappers.

- **Layer 4b** ✓. Collapsed Layer 4's additive wrappers into the
  verdict-returning `runPebbleGame` / `runPebbleGameExec` directly
  per *Architectural choices: Maximal reshape*. The raw
  `Sum`-returning math- and exec-layer wrappers retired; the
  workhorse-level `runPebbleGameWith` keeps the `Sum` return type
  (it is `G`-free). The math-layer
  `runPebbleGame_underline_eq_edgeFinset` helper consolidated into a
  single discharge bundle `runPebbleGame_edges_discharges` consumed
  by the verdict construction inside `runPebbleGame.aux`. The
  certificate-form `runPebbleGame_correct` /
  `runPebbleGameExec_correct` iffs retire; the workhorse-level
  `runPebbleGameWith_correct` is the single source of truth, and the
  verdict-form `runPebbleGame_isAccept_iff` /
  `runPebbleGameExec_isAccept_iff` (proved via the same
  `*_aux_isAccept` bridge as before) are the user-facing
  restatements. Phase 7's `countMatroid_indep_iff_runPebbleGame`
  restated against `PebbleGameResult.isAccept`; `_result` analog
  retired. CLI surface (`Main.lean`) unchanged at this Layer.
  Implementation note: the dep-graph cannot accept extra `\uses{}`
  edges that create diamond explosions — attempting to add
  `def:pebbleGameResult` and `lem:workhorseWitness-certifies` to
  `def:runPebbleGame`'s `\uses{}` crashed `inv web` with
  `RecursionError` in `plastexdepgraph.ancestors`. Fix: keep
  `def:runPebbleGame`'s `\uses{}` minimal and let the verdict /
  workhorse-witness dependencies surface through the verdict-form
  theorem's `\uses{}`. Total Lean delta on the maximal reshape:
  ~−150 LoC.

- **Layer 5** ✓. `Main.lean` bumped: `classify` invokes
  `PartialOrientation.runPebbleGameExec G 2 3 (by omega)` directly
  (was: `decide G.IsLaman` → `decide (G.IsSparse 2 3)` two-step) and
  pattern-matches the returned `PebbleGameResult G 2 3`. Emits
  `LAMAN` / `SPARSE_NOT_TIGHT` (disambiguated on `.accept` by
  `G.edgeFinset.card + 3 = 2 * n`) with arc lines, or `NOT_SPARSE`
  with `BLOCKING` + `VERTEX` lines. Arc-sorting via
  `(D.arcs.image toLex).sort (· ≤ ·)` against
  `LinearOrder (Lex (Fin n × Fin n))`; vertex-sorting via
  `Finset.sort (· ≤ ·)` directly on `Finset (Fin n)`. Total Lean
  delta: ~+50 LoC. Four `examples/*.txt` fixtures updated to carry
  the full Layer 5 expected output in their leading comment blocks
  (decision rationale below). Blueprint
  `chapter/executable.tex`'s CLI subsection updated with the
  three-column output schema and the verdict-direct invocation
  step.

Total estimated delta: ~900–1300 LoC across the pebble-game files
plus `Search/DFS.lean` and `Main.lean`. Of that, the substantive
work is Layer 3 (algorithm reshape) and Layer 1 (computable reach);
Layers 2 and 4 are mostly mechanical packaging; Layer 5 is CLI
plumbing. Math content preserved verbatim.

## Lemma checklist

**Maintained in the blueprint, not here.** The Phase 11 lemma
index is spread across `chapter/dfs.tex` (Layer 1's
`reachClosureComputable` nodes), `chapter/pebble-game.tex`
(Layers 2–4's workhorse-witness, algorithm-reshape, and verdict
nodes), and `chapter/executable.tex` (Layer 4's wrapper-reshape and
Decidable-instance updates, Layer 5's CLI subsection); each
Layer's commit ships its blueprint updates in step. The *Layer
plan* section above is the authoritative to-do list — what each
commit ships, blueprint and Lean.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **Layer 1: `reachClosureComputable` routes through
  `reachableFinding`, not a sibling iterative DFS.** Filtering
  through the already-iterative `reachableFinding` gives the same
  iff contract in ~110 LoC total versus a parallel accumulating DFS
  whose `foldl`-over-children correctness proof against
  `Relation.ReflTransGen` would be disproportionate. Trade-off
  documented in audit point 7; future perf work could swap the
  implementation behind `mem_reachClosureComputable` transparently.

- **Layer 2: `WorkhorseWitness` carries `h_pebOn_le : pebOn V' ≤ ℓ`,
  not the per-vertex `h_below : peb u + peb v ≤ ℓ` initially
  proposed.** The case-5 data is strictly stronger — the DFS-failure
  "no free pebble outside `{u, v}` in `V'`" guarantee combines with
  per-vertex below-threshold to force `pebOn V' = peb u + peb v ≤ ℓ`
  via `Finset.sum_eq_zero` over `V' \ {u, v}`. The stronger single
  field (a) keeps `certifies_against` to one `omega` chain
  (Invariant (2) with `outOn V' = 0` rearranges directly), (b)
  removes a redundant "no-free-pebble" field, (c) doesn't lose
  information at the case-5 construction site.

- **Layer 3: `tryAddEdgeWith` / `runPebbleGameWith` take
  `hD : Reachable k ℓ D` as a hypothesis (absorbing `h_outle`).**
  The case-5 inline witness construction needs `Reachable k ℓ D` for
  the `h_reachable` field; adding `hD` to the signature also lets
  the recursive calls (cases 3, 4) compute fresh reachability via
  `r.reachable_newOrient_of_addEdgePred hD hD.out_le` without a
  separate `h_outle` argument. At the fold layer, `runPebbleGameWith`
  takes `hD` and drops its previous `(∀ x, D.out x ≤ k)` runtime
  check. Trade: the recursive call now goes through
  `tryAddEdgeWith_reachable` to compute the updated `hD`, forcing a
  `match heq : ... with` pattern that requires `split at h` (not
  `rw [heq]`) in downstream `_underline_subset` / `_mem_underline` /
  `_reachable` proofs.

- **Layer 3: case-5 inline `V' := reachClosureComputable (toSucc D) u
  ∪ reachClosureComputable (toSucc D) v`, not `D.reach u ∪ D.reach v`.**
  `D.reach` is `noncomputable` (goes through `outList`); using it
  would force `tryAddEdgeWith` itself noncomputable, breaking Phase
  10's exec-layer claim. Using `reachClosureComputable` against the
  caller-supplied `toSucc D` adjacency keeps the workhorse fully
  computable. Bridge: `mem_reachClosureComputable` + `h_toSucc D`
  with a one-line `ReflTransGen` induction equating the
  `toSucc D`-shaped and `D.arcs`-shaped reachability relations.

- **Layer 4: `*.aux` helper to dodge TACTICS-QUIRKS § 17.** A direct
  term-level `match h_opt : runPebbleGame G k ℓ with ...` body for
  the verdict-bearing wrapper would put `h_opt` in scope of each
  branch with the substituted type `<pat> = <pat>` (per § 17), so
  downstream proof-field references fail with
  `Application type mismatch`. A `*.aux` helper taking the
  `Sum`-shaped result and its equation as explicit arguments,
  followed by `*_result G k ℓ h := *.aux G k ℓ h (runPebbleGame G k ℓ) rfl`,
  sidesteps the substitution. Pattern carried through both
  math- and exec-layer wrappers; promoted to TACTICS-QUIRKS § 17
  third bullet.

- **Layer 5: complete (not truncated) fixture comment blocks.**
  Kept the four `examples/*.txt` expected-output blocks at their
  full Layer 5 schema rather than truncating. The Moser spindle's
  11 ARCS lines and $K_4$'s 4-vertex BLOCKING block expand the
  comment block by 8–11 lines per file — each fixture still fits a
  single screen of input — and gives scripts (and human readers)
  the full schema rendered next to the input as a manual smoke test
  + future regression-test seed data should a CLI-output golden-file
  harness ever land.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *Data-building `match h_opt :` quirk fix via `*.aux` helper* →
  TACTICS-QUIRKS § 17 (third bullet of *Fix*). The Layer 4
  `*.aux` pattern takes the scrutinee `s` and its equation
  `h_opt : foo G = s` as separate explicit args.

*(Likely future promotion candidates, to assess at the
Phase11-cleanup D3 FRICTION re-skim: the *Strengthen past results
to reduce duplication* principle that drove the maximal-reshape
choice — a project-philosophy entry for `../DESIGN.md`; and the
*Blueprint reshape in-place per Layer* sequencing decision — a
workflow-mode entry for `../blueprint/DESIGN.md` if the pattern
recurs in future structural-edit phases.)*

### Cleanup pass summaries

*(Not applicable; cleanup pass is `Phase11-cleanup.md`.)*

## Blockers / open questions

- **Layer 1 micro-call:** ✓ Resolved in-file (file at ~830 LoC,
  under the ~1050 threshold).
- **Layer 4 micro-call:** ✓ Resolved at Layer 4 entry to option (b)
  additively; superseded at Layer 4b by the maximal-reshape
  collapse.
- **Layer 5 micro-call:** ✓ Resolved by keeping the comment blocks
  complete (rationale in *Decisions made* above).

## Hand-off / next phase

Phase 11 closed at Layer 5. The pebble game's user-facing surface is
now end-to-end witness-bearing: every accept/reject branch carries
structurally-recoverable certificate data, and the CLI prints it. No
deferred work; no `sorry`s; no open friction items specific to this
phase. The dep-graph has every Phase 11 node green across
`chapter/{dfs,pebble-game,executable}.tex`; the structural-edit work
that Layer 3 / 4b put through the existing chapters'
previously-green nodes is fully discharged.

The next phase has no forced ordering. Hand-off candidates, ranked
loosely by what unlocks downstream work:

1. **Component pebble game** (L–S §5; $O(n^2)$ speedup via union
   pair-find maintained across `runPebbleGameWith`'s fold). The
   biggest standalone Phase-12 candidate: takes the Phase-11
   verdict-bearing API as input and improves the constant factor on
   the algorithm. Touches `PebbleGame/Algorithm.lean` (the fold) and
   adds a sibling state structure for component tracking.
2. **Henneberg-sequence extraction** (L–S §6). Composes Phase 11's
   accept-branch orientation $D$ with Phase 3's
   `IsLaman.exists_typeI_or_typeII_reverse` to produce an
   executable Henneberg-construction sequence from a Laman graph.
   The smallest tractable next phase; mostly composition work.
3. **Benchmarks harness** comparing `runPebbleGameExec` against a
   brute-force `Decidable G.IsSparse` baseline on small graphs.
   Lighter, no new math; useful as a runtime sanity check that the
   Phase-10 polynomial-time claim holds on real inputs and as a
   regression detector for future algorithm changes.

The candidate list above is replicated from notes for backward
reference; the live tracking lives in the next-phase's
`notes/PhaseN.md` if/when one opens. As of Phase 11 close, no phase
has been selected.
