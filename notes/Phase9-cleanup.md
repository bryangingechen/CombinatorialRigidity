# Phase 9 cleanup round — work log

**Status:** in progress.

This is the inter-phase cleanup round after Phase 9 closed. See
`../CLEANUP.md` for the round-level operating manual: when to run a
round, the three audit categories (A blueprint-divergence, B
code-smell, C long-proof, D project-organization), and the
per-round workflow. The task list below is the round's "lemma
checklist" equivalent — populated up front per CLEANUP.md's *Sweep
first, fix later* + *Task list discipline* so a session that runs
out of time can hand off cleanly.

Phase 9 added two new files of substantial size — `Search/DFS.lean`
(~770 LoC) and `PebbleGame.lean` (~2500 LoC) — plus a 1459-line
`notes/Phase9.md` that ran far past the 250-LoC soft budget. The
round therefore scopes A–D to the **Phase 9 surface** (the two new
files + new blueprint chapters `chapter/dfs.tex` and
`chapter/pebble-game.tex` + the Phase 9 attribution in
`chapter/rigidity-matroid.tex` / `chapter/count-matroid.tex` if
present) plus a focused D pass to discharge the Phase9.md
compression debt. Project-wide drift was discharged by the Phase 7
and Phase 8 cleanup rounds; Phase 9's contributions to FRICTION /
TACTICS-* (5 resolved FRICTION entries + TACTICS-QUIRKS § 19) are
already lifted in-commit.

The accompanying **perf pass** opens in a parallel work log
(`Phase9-perf.md`); module-system conversion of the two new files
+ the broader cleanup-round-flagged structural levers route through
that pass per `../CLEANUP.md` *What a cleanup round is not* (not a
performance pass).

## Current state

A1 closed: `chapter/dfs.tex` ↔ `Search/DFS.lean` walk is faithful;
all five pinned names resolve; prose-proof structure tracks the
Lean. Two A2-bound carry-overs surfaced (stale "planned
`reachClosure` helper" prose in the pebble-game chapter;
informational notes on `DirectedWalk.mapRel` /
`arcsFinset` family selectivity) and are recorded inline under
A2's task body. No Lean or blueprint changes landed yet; the
A2 commit will discharge the prose updates.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Scope A–D to Phase 9 surface.** Same rationale as Phase 8-cleanup:
  the project-wide backlog of classical / Fintype / `change` /
  `noncomputable` / `rw`-chain smells was discharged by Phase 7-cleanup.
  Re-running those project-wide would be ~80% re-audit of closed
  resolutions; the marginal find rate doesn't justify it. Buckets A–D
  therefore restrict to the new files (`Search/DFS.lean` +
  `PebbleGame.lean`) and the new blueprint chapters
  (`chapter/dfs.tex` + `chapter/pebble-game.tex`).
- **Bucket D carries Phase9.md compression debt.** At 1459 LoC,
  `notes/Phase9.md` is ~6× over the 250-LoC soft budget — the
  largest single overflow in the project's history. The
  *Current state* commit-narrative and the *Hand-off / next phase*
  recap are both candidates for collapse to per-blueprint-node
  bullets now that the chapter is closed. This is a substantive
  D-bucket task; budget ~1 session.
- **Audit-only for the multigraph corner-case check.** Phase 9's
  architectural choice #1 committed to `SimpleGraph V` + `ℓ < 2k`,
  while Lee--Streinu state results for multi-graphs with loops in
  `ℓ ∈ [0, 2k)`. The formalization landed end-to-end, but a
  defensive statement-by-statement audit of L--S Lemmas 10--15
  against the simple-graph regime is nominally open per
  Phase9.md's *Blockers / open questions*. Lives as A3 below;
  audit-only (document what's used in what regime), not a
  refactor — any actual multi-graph lift is its own (multi-phase)
  project.
- **Perf pass separate.** Module-system conversion of the two new
  files routes through `Phase9-perf.md` per `../CLEANUP.md` *What a
  cleanup round is not*. Cleanup commits can incidentally reduce
  per-file build time but don't measure it; the 4-run A/B protocol
  in `PERFORMANCE.md` is the right gate.
- **Each fix as its own commit.** A cleanup commit obeys the same
  per-commit friction review and build/lint gates as a forward-work
  commit. Cleanup-round value is the trail of small principled
  commits, not a single mega-commit.

## Task checklist

### Bucket A — Blueprint ↔ Lean divergence audit (Phase 9 surface)

- [x] **A1:** `chapter/dfs.tex` ↔ `Search/DFS.lean` walk. Three
  dep-graph nodes: `def:directed-walk`, `def:reachable-finding`,
  `thm:reachable-finding-correct` (plus any newer additions for the
  `reachClosure` / `DirectedWalk.mapRel` family). For each:
  - confirm the `\lean{...}` pin resolves;
  - compare blueprint statement form against Lean signature
    (hypotheses, conclusion form, implicit/explicit binders);
  - re-read prose proof and flag any "the Lean does X via Y where Y
    is harder than X" pattern per `../CLEANUP.md` §A.
  Watch for: the `DirectedWalk.dropUntilBundle` `Subtype`-bundled
  truncation being honestly flagged as a Lean-side bookkeeping
  device (math has implicit truncation, Lean needs the bundle); the
  inner length-induction in `reachableFindingAux_complete` being
  presented faithfully (not glossed over as a one-step argument).

  **Disposition.** All five pinned names resolve under
  `CombinatorialRigidity.Search` (`DirectedWalk`,
  `DirectedWalk.IsPath`, `reachableFinding`, `reachableFinding_sound`,
  `reachableFinding_complete`). Statement forms are faithful:
  the inductive `DirectedWalk` realises the prose "non-empty list
  of vertices satisfying $R\,v_i\,v_{i+1}$"; `IsPath` ≡
  `vertices.Nodup` realises "simple"; `reachableFinding`'s
  `Option (Σ w, DirectedWalk ... v w)` return realises the
  "$\mathrm{some}\,(p, w)\,/\,\mathrm{none}$" prose with a harmless
  presentation gap (prose pair-order `(p, w)` vs Lean's Σ-encoding
  `⟨w, p⟩`); the soundness+completeness multi-pin matches the
  prose's enumerated parts. Prose proof faithfully tracks the Lean:
  outer `reachableFindingAux.induct` (3-case visited / `P v` / else)
  ↔ "outer auto-induction on the DFS recursion"; inner
  `induction n with | zero | succ ih_inner` length bound ↔
  "inner induction on the walk-length bound"; `dropUntilBundle` in
  the `v ∈ p'.vertices` branch honestly flagged as Lean-side
  bookkeeping per `../CLEANUP.md` §A;
  `Relation.ReflTransGen.head_induction_on` lifting in
  `reachableFinding_complete` ↔ prose "lifts to an explicit
  $R$-walk by head-first induction on $\mathrm{ReflTransGen}$".
  No A1-internal Lean simplification opportunities (the flagged
  bookkeeping is structural, not friction). No Lean or blueprint
  changes from A1's own scope; two carry-overs surface for A2,
  recorded inline under A2 below.
- [ ] **A2:** `chapter/pebble-game.tex` ↔ `PebbleGame.lean` walk.
  ~20 dep-graph nodes covering: `def:partial-orientation`,
  `def:pebble-counts`, `def:path-reversal`, `def:arc-insertion`,
  `def:reachable-orientation`, `lem:pebble-game-invariants`,
  `def:tryReachPebble`, `def:tryAddEdge`, `def:runPebbleGame`,
  `lem:runPebbleGameWith-underline-subset`,
  `lem:runPebbleGame-underline-eq`, `lem:span-eq-ncard-edgesIn`,
  `thm:pebble-game-soundness`,
  `lem:pebble-game-independent-brings-pebble` (+ -graph variant),
  `lem:pebble-game-tryAddEdgeWith-isSome`,
  `lem:pebble-game-tryAddEdgeWith-isSparse`,
  `lem:pebble-game-tryAddEdge-iff-independent`,
  `lem:pebble-game-failure-witness`, `thm:pebble-game-correct`,
  `cor:pebble-game-countMatroid-indep`. Same three checks per node
  as A1. Watch for: the `Reachable.{...}` invariant lemmas being
  honestly stated under the unified `ℓ ≤ k * V'.card` hypothesis
  (not L--S's regime-split form, see Phase9.md *Decisions →
  Reachability and the four invariants*); the `(V × V)`-list vs
  `(Sym2 V)`-list `runPebbleGameWith` shape being faithfully
  described (or honestly flagged as a `-With`-pattern bookkeeping
  device).

  **Carry-overs from A1 (DFS chapter walk).**
  - `chapter/pebble-game.tex` refers to `reachClosure` twice as a
    *"planned helper"* — once in the `def:tryAddEdge` prose
    ("a planned `reachClosure` helper post-composed at the failure
    site") and once in `def:runPebbleGame` ("deferred to a planned
    `reachClosure` helper, consumed by
    `lem:pebble-game-failure-witness`"). The helper has shipped in
    `Search/DFS.lean` (`reachClosure` + `mem_reachClosure` /
    `self_mem_reachClosure` / `reachClosure_closed`). Update the
    pebble-game prose to drop the "planned" qualifier; the
    follow-up question of whether to surface `reachClosure` as a
    dep-graph node in `chapter/dfs.tex` (so the pebble-game prose's
    `\uses{}` chain can thread through it) is an A2 call. Note
    that the actual blocking-witness extraction in
    `PebbleGame.lean` is `tryReachPebbleWith_eq_none_imp_no_reachable`
    / `runPebbleGame_eq_none_imp_exists_witness`; the chapter's
    *Blocking witness* machinery may have evolved past the
    "planned helper" framing entirely.
  - `chapter/pebble-game.tex` mentions `DirectedWalk.mapRel`
    inline at the `def:tryReachPebble` Lean-encoding aside
    ("transported from `reachableFinding`'s walk on the
    out-neighbour-list relation via `DirectedWalk.mapRel`").
    Honestly flagged, no fix needed.
  - `DirectedWalk.arcsFinset` / `reversedArcsFinset` and their
    `IsPath`-form filter-count lemmas are purely Lean-side
    structural support for `def:path-reversal` and are not
    surfaced in blueprint prose. Per *What to include vs. skip*
    (structural support, churn-prone), skip dep-graph entry; flag
    only if the A2 prose walk surfaces a `\uses{}` chain that
    would benefit from one.
- [ ] **A3:** Multigraph corner-case audit (audit-only, no
  refactor). Walk L--S Lemmas 10--15 statement by statement against
  the simple-graph regime. Document each lemma in the blueprint as
  *either*: (i) stated in a form whose simple-graph specialization
  is exactly what `PebbleGame.lean` proves, with `span(v) = 0`
  collapsing the loop-counted term where applicable; *or* (ii)
  L--S's multi-graph form is strictly more general and Phase 9
  proves a strict specialization (note the difference inline). The
  Phase9.md *Blockers* prose claims Lemma 10 already cleared and
  Lemmas 13--15 "expected to clear similarly" — this audit
  discharges that prediction in writing. Result: a short
  "Multigraph regime" preamble subsection in
  `chapter/pebble-game.tex` + per-lemma `\uses{}` / prose notes
  where regime differences matter.
- [ ] **A4:** Run `lake exe checkdecls blueprint/lean_decls` (after
  `inv web`) to confirm every Phase 9 `\lean{...}` resolves. Phase 9
  notes claim "the chapter dep-graph is fully green" — verify
  post-hoc.
- [ ] **A5:** Formalization-aside scan. Re-skim
  `chapter/pebble-game.tex` (and `chapter/dfs.tex`) prose proofs for
  asides flagging Lean-side bookkeeping (custom `Equiv`s,
  named-helper one-step substitutes, case-splits the Lean had to
  take that the math wouldn't). Each is a candidate for either Lean
  simplification (collapse the aside) or a more concrete
  formalization-cost note (make the residual cost honest). Per
  `../blueprint/CLAUDE.md` *Proof verbosity* the bias is *Lean
  simplification first, prose aside only if simplification fails*.

### Bucket B — Code-smell sweep (Phase 9 surface)

Initial grep results pre-sweep, restricted to `Search/DFS.lean` +
`PebbleGame.lean`:

| Smell | `Search/DFS.lean` | `PebbleGame.lean` |
|---|---|---|
| `classical` (top-level) | 0 | 0 |
| `letI`/`haveI Fintype.ofFinite` | 0 | 0 |
| `@[nolint]` / `set_option linter` | 0 | 0 |
| `noncomputable def` | 1 (L749 — `reachClosure`) | 5 (L130, L1087, L1284, L1491, L1863 — `outList`, `tryReachPebble`, `tryAddEdge`, `runPebbleGame`, `reach`) |
| `change`/`show` (coax) | 0 | 0 |
| Multi-step `rw` (4+ args, one step) | 2 (L194, L200, L285) | 4 (L260, L413, L427, L440, L932) |
| `show … from rfl` | 0 | 0 |

Phase 9's "fully-computable workhorse + noncomputable math-layer
wrapper" pattern (the `-With` variant, see `DESIGN.md` *Pebble-game
style island*) accounts for **all 6 `noncomputable def` sites** —
each is the math-layer wrapper specialising a computable workhorse
to a noncomputable enumeration (`Finset.toList` / `Quot.out` /
`Relation.ReflTransGen`). The bucket-B audit on these should
confirm the wrappers are minimal (no body content beyond the
specialisation) and the workhorses stay computable.

- [ ] **B1:** `noncomputable def` audit. For each of the 6 Phase 9
  sites, confirm:
  - the `noncomputable` keyword is *forced* (try `def` and read the
    error — `Finset.toList`, `Classical.choice`-flavored
    `Quot.out`, or `Classical.decPred`-via-`Relation.ReflTransGen`);
  - the noncomputable body is a minimal one-liner around a
    computable workhorse, not duplicating logic;
  - the workhorse signature exposes everything callers need without
    going through the noncomputable wrapper.
  Documented disposition: each site to be marked *forced* or *vestigial*
  (latter unlikely given the pattern, but worth verifying).
- [ ] **B2:** Multi-step `rw` chain audit. 6 sites (3 in DFS.lean,
  3 in PebbleGame.lean). Inspect each for a missing fused lemma —
  usually a one-line mirror under `CombinatorialRigidity/Mathlib/`.
  Per `../CLEANUP.md` table row, the common pattern is "rw chain
  across multiple structural unfolds that should compose as one
  named lemma." Phase 9's chain candidates look mostly structural
  (DFS: `mapRel` + `length` + `length` + `ih`; PebbleGame:
  `Finset.sum_congr rfl h` + `Finset.sum_const` + `smul_eq_mul` +
  `mul_comm`) — probably not mirror-eligible, but verify.
- [ ] **B3:** `classical` / `haveI Fintype.ofFinite` clean-sweep
  audit. Phase 9 chose `[Fintype V] [DecidableEq V]` as the style
  island (architectural choice #2), so we'd expect zero such
  patterns — but verify nothing crept in during the long phase.
  Initial grep returned zero hits; mark trivially closed if a
  re-grep confirms.
- [ ] **B4:** Phase 9 file headers + section organisation review.
  Both new files run long (770 + 2500 LoC). Spot-check section
  organisation: are sections named consistently with the blueprint
  chapter structure? Are the section transitions documented in
  module docstrings? Any section over ~400 LoC that's a candidate
  for an internal split (no file-level split, just section
  reordering)?
- [ ] **B5:** `--` comment audit. Phase 9's long files almost
  certainly accumulated some narrative `--` comments that should
  either move to module-level docstrings (`/-! ... -/`) or be
  removed per the CLAUDE.md *no comments by default* rule. Quick
  grep + walk; remove anything explaining WHAT the code does (vs
  documenting a hidden WHY).

### Bucket C — Long-proof audit (Phase 9 surface)

Rank the top ~10 proofs in `Search/DFS.lean` + `PebbleGame.lean` by
body line count (per the crude `awk` ranking script in
`../CLEANUP.md` §C). Each proof gets four candidate questions per
the manual:
- **API extraction.** Self-contained sub-lemma other proofs would
  call separately?
- **Mathlib lemma we missed.** Run `lean_loogle` / `lean_leanfinder`
  on any 5--10+ line subblock.
- **Tactic substitution.** Could `grind only [...]` / `omega` /
  `fun_prop` collapse a multi-step `rw` chain? Use
  `lean_multi_attempt` to A/B-test without an edit-build cycle.
- **Definitional refactor.** Would a predicate reshape save the
  proof's manual unfolding?

- [ ] **C1:** Rank top ~10 proofs in `PebbleGame.lean` by body
  length. Expected hot spots (from Phase9.md):
  `tryAddEdgeWith_reachable` and `tryAddEdgeWith_underline`
  (five-case `tryAddEdgeWith.induct` dispatch — likely 50+ lines
  each), `tryAddEdgeWith_eq_none_imp_exists_witness` and
  `tryAddEdgeWith_isSome` (same induct shape plus DFS-completeness
  glue, likely 80+ lines each),
  `Reachable.pebOn_add_outOn_ge` (Invariant (3) substantive piece —
  the induction-step subset-decomposition logic).
- [ ] **C2:** Walk each of C1's top entries through the four
  questions. Particular interest: the `tryAddEdgeWith.induct` 5-case
  dispatch in `_reachable` / `_underline` / `_isSome` /
  `_eq_none_imp_exists_witness` is **the same shape repeated four
  times**, suggesting a possible cross-proof unification through a
  shared pattern lemma. Phase 7's *typeII-cores unification* is the
  analogous worked example.
- [ ] **C3:** Same ranking + walk for `Search/DFS.lean`. Expected
  hot spot: `reachableFindingAux_complete` (inner length-induction
  with two sub-cases, per Phase9.md *Completeness shape*).
- [ ] **C4:** `lean_multi_attempt` sweep on any 4+ step `rw` chain
  flagged in B2 — A/B against `grind`/`simp`/`omega` to see if a
  single tactic absorbs the chain.

### Bucket D — Project-organization compression

- [ ] **D1:** **Compress `notes/Phase9.md` from ~1459 LoC to ≤ 250 LoC.**
  This is the bulk of the round. Pattern: keep the closing
  *Architectural choices made up front* and *Hand-off / next phase*
  sections (already concise), compress *Current state* to a
  per-blueprint-node bulleted summary (the chapter dep-graph is the
  authoritative index, this section is the commit-narrative
  recap — most can be deleted now that the dep-graph is green),
  and reduce *Decisions made* per `notes/CLAUDE.md` *Sub-organize
  "Decisions made"* sub-organization rules: each decision ≤ 8 lines,
  pointers to FRICTION / TACTICS-* / DESIGN for cross-cutting
  lessons that have already been lifted. Expected output: clean
  one-screen-per-decision flat list under "Phase-local choices and
  proof techniques" + concise "Promoted to ..." pointer section +
  short "Cleanup pass summaries" placeholder.
- [ ] **D2:** Lift-on-promotion check across Phase9.md decisions.
  The CLAUDE.md threshold is "referenced in 2+ files or by 2+
  phases." Phase 9 already lifted: 5 FRICTION entries
  ([resolved] `induction _ using funName.induct`, [resolved]
  `rw [D.field_eq]` motive, [resolved] cons-pattern endpoint subst,
  [resolved] `ring` alpha-renamed sums, [resolved]
  `Finset.toList` noncomputable), 1 TACTICS-QUIRKS section (§ 19),
  1 DESIGN.md section (*Pebble-game style island* + *The `-With`
  variant pattern*). Are there others that should lift? Candidates:
  - The `match h : ... with | pat => ...` substitution shape
    (TACTICS-QUIRKS § 17) bit Phase 9 again in the `runPebbleGame_correct`
    body — already a § entry, but does Phase 9's use add a worked
    example worth appending?
  - The `Reachable k ℓ D` non-motive threading hypothesis pattern
    (introduced before `induction _ using ... generalizing D'`) —
    cross-cutting enough to lift to TACTICS-GOLF?
  - The unified additive identity pattern for state-machine moves
    (single `if-then-else` formula keyed on the move's piecewise
    behaviour, combined with case-analysis at the call site) —
    surfaced twice in Phase 9 (path reversal + arc insertion); is
    this a TACTICS-GOLF / DESIGN.md candidate?
- [ ] **D3:** `FRICTION.md` housekeeping. Phase 9 added 5 resolved
  entries that all have post-resolution indices (mirror files or
  TACTICS-QUIRKS § references). Per the CLAUDE.md *Filing rule for
  new entries*, "migrate to `FRICTION-archive.md` on the next
  housekeeping pass once their resolution is fully indexed." Move
  Phase 9's resolved entries to archive iff their indices are stable;
  leave any whose resolution needs further eyes.
- [ ] **D4:** Re-skim `../DESIGN.md` *Choices to revisit*. Phase 9
  resolved several decisions queued there:
  - `PartialOrientation V` representation (option (i) chosen,
    architectural-choice list);
  - matroidal-independence corollary placement (land in-phase, in
    `PebbleGame.lean`);
  - termination measure for `tryReachPebble` (resolved via the DFS
    warmup pattern).
  Update each entry inline; flip them to *resolved (Phase 9)* with
  a one-line pointer to the relevant Phase9.md decision section.
- [ ] **D5:** `ROADMAP.md` engineering-conventions re-skim. Does
  Phase 9 surface any new convention that should be documented
  there? Candidates: the `[Fintype V] [DecidableEq V]` style
  island for algorithm files (currently lives in DESIGN.md
  *Pebble-game style island*; should ROADMAP point at it from
  *Engineering conventions → Vertex types*?); the `-With` variant
  pattern (math/exec layer split for algorithms; DESIGN.md
  pin appears sufficient — verify).

## Blockers / open questions

- Round just opened; none currently. Will be populated as sweeps
  surface deferrals.

## Hand-off / next phase

Round in progress. Phase 9 main is fully closed; this round
addresses the post-closure hygiene. A1 (DFS chapter walk) closed;
A2 (pebble-game chapter walk) is the natural next task and carries
the inline carry-overs from A1 (stale `reachClosure` prose +
informational notes). Carry-overs queue under *Blockers* above as
they surface.

The accompanying **Phase 9-perf** pass opens in parallel
(`Phase9-perf.md`) per `../CLEANUP.md` *What a cleanup round is
not*; structural levers (module-system conversion of the two new
files) route through that pass.
