# Phase 10 + 11 cleanup round — work log

**Status:** in progress.

This is the inter-phase cleanup round covering **both Phase 10 and
Phase 11**. See `../CLEANUP.md` for the round-level operating manual:
when to run a round, the three audit categories (A blueprint-
divergence, B code-smell, C long-proof, D project-organization), and
the per-round workflow. The task list below is the round's "lemma
checklist" equivalent — populated up front per CLEANUP.md's *Sweep
first, fix later* + *Task list discipline* so a session that runs out
of time can hand off cleanly.

**Combined scope rationale.** No cleanup round ran between Phase 10
and Phase 11 — Phase 11 (witness extraction, a structural-edit phase)
opened immediately after Phase 10 closed and reshaped much of the
Phase 10 surface in place (Layer 3 absorbed the
`tryAddEdgeWith` / `runPebbleGameWith` `Option`-returning shape into
`Sum`; Layer 4b collapsed Phase 10's certificate-form
`runPebbleGameExec_correct` iff into the verdict's return type).
A separate Phase-10-cleanup round would have been an audit of code
that Phase 11 then rewrote; a single combined round is the right
unit, audits everything once at the current shape, and matches the
A/B-equivalent decision made for Phase 8-cleanup / Phase 9-cleanup
(scope to the phase's surface, not project-wide).

The accompanying **perf pass** opens in a parallel work log
(`Phase11-perf.md`) per `../CLEANUP.md` *What a cleanup round is
not*; structural levers (per-decl `@[expose]` audit on the Phase 11
file additions, fresh 4-run A/B baseline) route through that pass.

## Current state

Round open. Task checklist populated per *Task list discipline*; no
fixes have landed yet. Pre-sweep smell counts (Phase 10+11 surface
only — `CombinatorialRigidity/PebbleGame/*.lean`,
`CombinatorialRigidity/Search/DFS.lean`, `Main.lean`):

| Smell | DFS | Basic | Algorithm | Correctness | Exec | Examples | Main |
|---|---|---|---|---|---|---|---|
| `classical` (standalone) | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `noncomputable def` | 2 | 8 | 10 | 6 | 3 | 0 | 0 |
| `change` / `show` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `@[nolint …]` / `set_option linter` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Multi-step `rw [..., ..., ...]` (3+ args) | 3 | 5 | 0 | 0 | 1 | 0 | 0 |
| `show … from rfl` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

Phase 9-cleanup B4 audited the `noncomputable def` sites in `DFS.lean`
and the pre-Phase-11 `PebbleGame/*.lean`; Phase 11 reshape may have
added or removed sites — re-audit only the delta (Phase 10 additions
in `Exec.lean` / `Examples.lean` and Phase 11 reshape in `Basic.lean`
/ `Algorithm.lean` / `Correctness.lean`). Multi-step `rw` chains
likely break down to per-step structural rewrites with no missing
fused lemma (Phase 9-cleanup B7 saw the same pattern), but the
audit is the discharge.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Combined Phase 10+11 round, scoped to Phase 10+11 surface.**
  See *Combined scope rationale* above. Same A-D restrict-to-surface
  pattern as Phase 8-cleanup / Phase 9-cleanup; project-wide drift
  was discharged by Phase 7-cleanup and reconfirmed by Phase 8 /
  Phase 9 cleanup rounds.
- **Perf split-out.** Per `../CLEANUP.md` *What a cleanup round is
  not*, performance-tuning work (per-decl `@[expose]` audit, 4-run
  A/B baseline) routes through `Phase11-perf.md`, not this round.
  Refactors *surfaced by an A-D audit* (API extraction, fused-lemma
  mirror, cross-proof unification) are in-round per `../CLEANUP.md`
  *Workflow* rule 3 and *What a cleanup round is not*'s refactor
  carve-out.
- **Each fix as its own commit.** The per-commit friction review and
  build/lint gates apply normally (`../CombinatorialRigidity/CLAUDE.md`
  *Friction review*); cleanup commits look the same as forward-work
  commits.
- **No new phase queued at round close** by default. Phase 11's
  *Hand-off / next phase* listed three candidates (component pebble
  game; Henneberg-sequence extraction; benchmarks harness); the
  user picks at round close if any is ready to open.

## Task checklist

### Bucket A — Blueprint ↔ Lean divergence audit (Phase 10+11 surface)

Three chapters touched by Phase 10/11: `chapter/dfs.tex` (Phase 11
Layer 1 additions), `chapter/pebble-game.tex` (Phase 11 Layer 2-4b
reshape), `chapter/executable.tex` (Phase 10 + Phase 11 Layer 4b/5
reshape). `checkdecls` is on the per-commit gate path so we don't
need a separate "run checkdecls" task here.

- [ ] **A1:** `chapter/dfs.tex` ↔ `Search/DFS.lean` walk. Verify the
  Layer 1 additions `def:reachClosureComputable` +
  `lem:mem-reachClosureComputable` (lines 117+, *Reachability
  closure (computable)* subsection) match the Lean signatures.
  Check that the retired `def:reachClosure` /
  `lem:mem-reachClosure` predecessors are fully removed (no
  zombie `\lean{...}` pins); cross-reference Phase 9-cleanup A1
  finding ("planned `reachClosure` helper" mentions all repointed).
- [ ] **A2:** `chapter/pebble-game.tex` ↔ `PebbleGame/{Basic,
  Algorithm, Correctness}.lean` walk. Per Phase 11 Layer 2-4b
  blueprint reshape (recorded in `Phase11.md`'s *Current state*),
  walk: `def:workhorseWitness` + `lem:workhorseWitness-certifies`
  in *Completeness* (Layer 2); `def:tryAddEdge`,
  `def:runPebbleGame`, `thm:pebble-game-correct` restated against
  `Sum`-return / `hD` signature (Layer 3); `def:pebbleGameResult`
  + `thm:pebbleGameResult-isAccept-iff` in *User-facing verdict*
  (Layer 4); `cor:pebble-game-countMatroid-indep` restated. Check
  retired-node hygiene (`lem:pebble-game-tryAddEdgeWith-isSome`,
  `lem:pebble-game-tryAddEdge-iff-independent`,
  `lem:pebble-game-failure-witness`).
- [ ] **A3:** `chapter/executable.tex` ↔ `PebbleGame/Exec.lean` +
  `Main.lean` walk. Walk the Phase 10 nodes (`def:outListSorted`,
  `lem:mem-outListSorted`, `def:edgeListSorted`,
  `lem:mem-edgeListSorted`, `def:isSparse-decidable`,
  `def:isTight-decidable`, `def:isLaman-decidable`, *Worked
  examples* subsection, *CLI binary* subsection) at their current
  Phase 11 Layer 4b/5 restated shape (verdict-direct routing,
  `.isAccept` reductions, new output schema). Confirm
  `def:runPebbleGameExec` repointed at the verdict-returning form;
  `thm:runPebbleGameExec-correct` and `def:runPebbleGameExec-result`
  retired (collapsed into `def:runPebbleGameExec`).
- [ ] **A4:** Formalization-aside scan across all three chapters.
  Phase 11's *Architectural choices* list noted the structural
  reshape; each `\emph{}` / `\begin{remark}` aside should still
  hold under the verdict-bearing shape, with no orphan asides
  documenting the Phase-9-era `Option` return type. Apply
  CLEANUP.md §A's "first attempt is to shorten the Lean to retire
  the aside"; record any failed-shortening attempts with the
  residual rationale.

### Bucket B — Code-smell sweep (Phase 10+11 surface)

Pre-grep summary in *Current state* above. Phase 9-cleanup audited
`DFS.lean` and the pre-Phase-11 `PebbleGame/*.lean`; this sweep
re-audits the delta only (Phase 10 additions + Phase 11 reshape).

- [ ] **B1:** `classical` audit. Zero standalone hits in the
  Phase 10+11 surface (project default style island
  `[Fintype V] [DecidableEq V]` already provides the typeclasses).
  Confirm by comment-out + build on any remaining sites; expected
  to close as no-op.
- [ ] **B2:** `noncomputable def` audit (delta vs Phase 9-cleanup
  B4). Three categories to expect:
  - Phase 10 additions in `Exec.lean` (3 sites): the
    `runPebbleGameExec` wrapper + math-layer companion.
  - Phase 11 reshape in `Basic.lean` / `Algorithm.lean` /
    `Correctness.lean`: the `runPebbleGame` math-layer wrapper
    moved to verdict-bearing form (Layer 4b); the workhorse-level
    `runPebbleGameWith` stays computable; `PartialOrientation.reach`
    Layer 1 redefinition.
  For each: verify the `noncomputable` keyword is forced by a
  named driver (`Finset.toList`'s `Quot.out` / `Real.instRCLike` /
  similar) or vestigial.
- [ ] **B3:** Multi-step `rw [..., ..., ..., ...]` chain audit (9
  sites total: 3 in DFS, 5 in Basic, 1 in Exec). For each: is the
  chain a missing fused lemma (candidate for a project mirror), a
  per-step structural rewrite (Phase 9-cleanup B7's *kept as-is*
  pattern), or a candidate for `simp only` collapse? Expect most
  to be the second; surface any missing-mirror cases for in-round
  refactor.
- [ ] **B4:** `letI`/`haveI Fintype.ofFinite` audit. The style
  island already takes `[Fintype V] [DecidableEq V]` end-to-end
  (`../DESIGN.md` *Pebble-game style island*), so no inline bridge
  should be needed inside the algorithm files. Re-grep confirms.
  Expected closure: no edits.
- [ ] **B5:** `@[nolint …]` / `set_option linter …` audit. Pre-grep
  shows zero hits. Expected closure: no-op.

### Bucket C — Long-proof audit (Phase 10+11 surface)

- [ ] **C1:** Top-10 by body LoC across `PebbleGame/*.lean`,
  `Search/DFS.lean`, `Main.lean`. Phase 11 Layer 3 reshaped
  `tryAddEdgeWith` (case-5 inline witness construction) and
  `runPebbleGameWith` (fold over `Sum`); both likely sit near the
  top. The new `Algorithm.lean` is 1039 LoC — the case-5 body
  itself may be a candidate for sub-lemma extraction. Also expect:
  the Layer 4b `runPebbleGame.aux` / `runPebbleGameExec.aux`
  verdict-construction bodies; `runPebbleGame_edges_discharges`;
  case-3 / case-4 `tryAddEdgeWith_reachable` propagation.
- [ ] **C2:** Four-question walk over the C1 top sites (per
  `../CLEANUP.md` §C — API extraction, mathlib lemma we missed,
  tactic substitution, definitional refactor, cross-proof
  unification). Record candidates for in-round refactor; defer to
  follow-up phases only when the refactor is structurally large.
- [ ] **C3:** In-round refactor candidates land each as its own
  commit, per `../CLEANUP.md` *Workflow* rule 3.

### Bucket D — Project-organization compression

- [ ] **D1:** `notes/Phase11.md` compression. Currently 856 LoC vs
  the adaptive 350-450 budget for a substantive phase
  (`../notes/CLAUDE.md` *Soft length budget*). Phase 11 was a
  five-layer structural-edit phase with 6 forward-work commits + 2
  opener docs commits — substantive but not at the "20+ commits"
  scale that justifies the upper end. Compression candidates:
  - *Current state* runs ~150 LoC of per-layer narrative that
    re-tells what each layer commit's message + the *Layer plan*
    section already say. Collapse to a per-layer-pointer summary.
  - *Architectural choices made up front* is ~80 LoC of design
    rationale; some entries (e.g., the verdict-shape inductive
    declaration in TeX-style) duplicate `chapter/pebble-game.tex`
    *User-facing verdict* prose and can collapse to a pointer.
  - *Decisions made during this phase* is well-organized but a
    few entries (e.g., *Layer 4b: collapsed to maximal reshape*)
    duplicate the *Current state* narrative.
  Target: ~400 LoC.
- [ ] **D2:** `notes/Phase10.md` compression. Currently 546 LoC.
  Phase 10 was a shorter five-layer forward-work phase; adaptive
  budget allows ~250-350. *Current state* and *Architectural
  choices* duplicate each other in spots (e.g., the
  `[LinearOrder V]` and `Fact (ℓ < 2 * k)` decisions appear in
  both); collapse the *Current state* narrative to a per-layer
  pointer. Target: ~300 LoC.
- [ ] **D3:** FRICTION re-skim. Phase 10's *Promoted* section
  lifted three entries (TACTICS-QUIRKS § 22, § 23, DESIGN.md
  *One Decidable instance per project predicate*); Phase 11's
  *Promoted* lifted one (TACTICS-QUIRKS § 17 third bullet, the
  `match h:` quirk fix via `*.aux` helper). Verify each was a
  one-line pointer in the phase notes after lifting, and that the
  FRICTION/QUIRKS entries themselves carry the cross-references
  back. The two open Phase-11 promotion candidates flagged in
  Phase11.md *Promoted* parenthesis (*Strengthen past results to
  reduce duplication* and *Blueprint reshape in-place per Layer*)
  may be ripe for promotion now — assess on second-site evidence
  (whether the principle would also have applied to Phase 7 / 8 /
  9 / 10 in retrospect).
- [ ] **D4:** DESIGN.md *Choices to revisit* drift check. The
  active entries (`apnelson1/Matroid dependency` watch, `Promoting
  edgesIn upstream`, *Pebble-game style island* if any drift)
  should reflect Phase 10/11's reality. Phase 11's
  *Architectural choices* shouldn't have left any
  *Choices to revisit* candidate unresolved; verify.
- [ ] **D5:** No-residual-lifts audit. For each Phase 10 / 11
  *Promoted to* entry, verify the destination still carries the
  cross-reference back; verify the phase entry is a one-line
  pointer per CLAUDE.md *Lift on promotion*.

## Decisions made during this phase

### Phase-local choices and proof techniques

*(Empty — populate as fixes land.)*

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

*(Empty — populate as cross-cutting lessons surface.)*

### Cleanup pass summaries

*(Empty — populate as buckets close.)*

## Blockers / open questions

*(None at round open.)*

## Hand-off / next phase

To be written at round close. Default: hand off to whichever
follow-up direction the user picks from Phase 11's three candidates
(component pebble game / Henneberg-sequence extraction / benchmarks
harness); cleanup-round work is hygiene, not a phase dependency.
