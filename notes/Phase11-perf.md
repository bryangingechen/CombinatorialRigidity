# Phase 10 + 11 perf pass — work log

**Status:** in progress.

This is the post-Phase-10+11 perf pass running in parallel with the
combined `Phase11-cleanup.md` round per `../CLEANUP.md` *What a
cleanup round is not* (cleanup rounds do not measure performance;
perf passes have their own log + 4-run A/B protocol). See
`./PERFORMANCE.md` for the round-level operating manual: the
anatomy of a `lake build`, profiling switches, timing
reproducibility, A/B measurement protocol, and the standing
recommendations.

**Combined scope rationale.** Same as `Phase11-cleanup.md` —
Phase 11 reshaped much of the Phase 10 surface (Layer 3 absorbed
`tryAddEdgeWith` / `runPebbleGameWith`'s `Option`-return; Layer 4b
collapsed `runPebbleGameExec_correct` into the verdict's return
type), and a separate Phase-10-perf pass would measure code that
Phase 11 then reshaped. One combined pass audits the current
shape against the prior post-Phase-9-perf baseline.

## Summary

Pass open. Phase 9-perf F4.2 set the prior baseline (medians:
`Search/DFS.lean` 8.70 s; `PebbleGame.lean` ~15.4 s; project-total
10.04 s). Phase 10 split `PebbleGame.lean` into the
`PebbleGame/` subdirectory (Phase 10 Layer 1 onward;
`Basic.lean` + `Algorithm.lean` + `Correctness.lean`) and added
`Exec.lean` + `Examples.lean` + `Main.lean`. Phase 11 reshape
landed in-place across the same files (no new files; Layer 1
extended `Search/DFS.lean` by ~110 LoC). Headline pre-pass
expectation: this pass's structural lever is the **per-decl
`@[expose]` audit on the four Phase-10/11 files that started at
`@[expose] public section`** (Algorithm, Correctness, Exec,
Examples) — same F3.5 / Phase 9-perf F1 audit pattern. Basic and
DFS were narrowed during Phase 9-perf F1; verify Phase 11's reshape
didn't invalidate those dispositions, restore opt-ins if needed.

Headline numbers + dispositions will land here once F1 and F4
close.

## Pass overview

This pass is the natural follow-up to Phase 9-perf's F1 audit:
extend the per-decl `@[expose]` narrowing from the original two
Phase-9 files to the four files Phase 10 and Phase 11 introduced
or reshaped. Per `PERFORMANCE.md` *Lessons*: "`public section` is
opaque intra-module too" — the audit is informed by the same
intra-module elaboration-time-defeq triggers that surfaced in F3.5
and Phase 9-perf F1 (e.g., `@[simp] ... := rfl` always forces
`@[expose]`).

Secondary levers, all audit-only unless A/B demonstrates a win:

- **F2.** Phase 11 reshape's effect on `Basic.lean` / `DFS.lean`
  per-decl dispositions. Phase 9-perf F1.1 / F1.2 carried 5 + 3
  per-decl `@[expose]` opt-ins on those two files; Phase 11 Layer
  1 added `reachClosureComputable` + correctness lemmas to DFS
  (~110 LoC), Layer 1 + Layer 3 moved `reach`-closure machinery
  into Basic, and Layer 2 added `WorkhorseWitness`. Re-audit
  whether the existing opt-ins are still needed and whether new
  ones must be added.
- **F3.** `LinearRigidityMatroid.lean` module conversion follow-up.
  Phase 9-perf F3 (and Phase 8-perf F3.3 before it) carved LRM out
  as blocked on `apnelson1/Matroid`'s
  `Matroid.Representation.Map` being non-`module`. Re-check the
  upstream status at pass execution time; if `Map.lean` has
  converted, land LRM's conversion as a one-commit follow-up.
- **F4.** Baseline + post-pass measurements per the standard
  `PERFORMANCE.md` *Measurement protocol* (4-run, median-of-4,
  unique-content nudges, separate per target). Targets:
  `Search/DFS.lean`, `PebbleGame/Basic.lean`,
  `PebbleGame/Algorithm.lean`, `PebbleGame/Correctness.lean`,
  `PebbleGame/Exec.lean`, project-total. Per-file selection
  follows the "analysis-heavy or algorithm-heavy file" criterion
  in `PERFORMANCE.md` *Module system* / *Anatomy of a `lake build`*.

## Task checklist

### F1. Per-decl `@[expose]` audit on the four new/reshaped Phase 10+11 files

Pattern: F3.5 of Phase 8-perf and F1 of Phase 9-perf. For each
file currently at `@[expose] public section`, attempt
demotion → `public section` and observe what breaks (intra-file or
downstream); restore `@[expose]` on the per-decl sites whose bodies
are genuinely consumed. Document the trigger + disposition in the
file's row of an F1 table.

Current Phase 10+11 disposition (per `grep`):
- `PebbleGame/Basic.lean`: `@[expose] public section` — covered by
  Phase 9-perf F1.2 (3 per-decl opt-ins). Phase 11 reshape may
  have changed the set; F2 below re-audits.
- `PebbleGame/Algorithm.lean`: `@[expose] public section` (Phase 10
  + 11 surface) — un-audited.
- `PebbleGame/Correctness.lean`: `@[expose] public section` (Phase
  10 + 11 surface) — un-audited.
- `PebbleGame/Exec.lean`: `@[expose] public section` (Phase 10
  surface) — un-audited.
- `PebbleGame/Examples.lean`: `@[expose] public section` (Phase 10
  surface, `public meta import` for `#eval` access) — un-audited;
  may close trivially (no defs, only `#eval` lines).
- `Search/DFS.lean`: `public section` with 5 per-decl `@[expose]`
  opt-ins — covered by Phase 9-perf F1.1. Phase 11 Layer 1 added
  `reachClosureComputable` + correctness; F2 below re-audits.
- `Main.lean`: non-`module` by Phase 10 *Decisions* — not in audit
  scope.

- [ ] **F1.1.** `PebbleGame/Algorithm.lean` audit. Demote
  `@[expose] public section` → `public section`; restore
  `@[expose]` per-decl where build/lint requires it. Likely
  candidates: `tryAddEdgeWith`, `tryAddEdge`,
  `runPebbleGameWith`, `runPebbleGame` if any have `@[simp]
  := rfl` projection lemmas or intra-file pattern-match defeq
  consumers (Phase 11 Layer 4b's `runPebbleGame.aux` discharge
  bundle is a candidate). Append disposition row to PERFORMANCE.md
  F3.5 table.
- [ ] **F1.2.** `PebbleGame/Correctness.lean` audit. Same pattern.
  Layer 4b added `PebbleGameResult` inductive (auto-exposed
  constructors), `runPebbleGame_isAccept_iff` /
  `runPebbleGameExec_isAccept_iff` lemmas, and
  `WorkhorseWitness.certifies_against`. Mostly theorems, so
  expected to demote cleanly; verify.
- [ ] **F1.3.** `PebbleGame/Exec.lean` audit. Same pattern. Phase
  10 defs `outListSorted`, `edgeListSorted`,
  `runPebbleGameExec` may have intra-file `@[simp] := rfl`
  consumers; Layer 4b's verdict-returning `runPebbleGameExec` may
  need `@[expose]` if the three `Decidable` instances
  pattern-match its body. Disposition row.
- [ ] **F1.4.** `PebbleGame/Examples.lean` audit. Expected
  closure: trivial — file has no `def`s, only `#eval` commands
  that consume the Decidable instances at meta time. Demote to
  `public section` (no per-decl opt-ins); confirm `#eval`s still
  fire.
- [ ] **F1.5.** Update `./PERFORMANCE.md` *Granular `@[expose]` /
  `public` audit per file* with the F1.1–F1.4 dispositions
  (append four rows to the F3.5 table; extend the status preamble
  with the Phase 10+11-perf F1 closure paragraph).

### F2. Re-audit Phase 9-perf F1.1 / F1.2 dispositions under Phase 11 reshape

Phase 9-perf F1.1 ships 5 per-decl `@[expose]` opt-ins on DFS
(`DirectedWalk.{length, vertices, IsPath, arcsFinset,
reversedArcsFinset}`); F1.2 ships 3 opt-ins on Basic
(`PartialOrientation.{empty, reverse, addArc}`). Phase 11
extensions:

- DFS Layer 1 added `reachClosureComputable` + soundness +
  completeness + `DirectedWalk.toReflTransGen` bridge — ~110 LoC.
  Re-audit: do the new defs need `@[expose]`? Any new `@[simp]
  := rfl` projections that force exposure?
- Basic absorbed the reach-closure-on-orientations API
  (`reach`, `mem_reach`, `self_mem_reach`, `reach_closed`,
  `outOn_eq_zero_of_closed`, `outOn_reach_union_eq_zero`) from
  Correctness, plus added `WorkhorseWitness` (Layer 2). The
  Phase 9-perf F1.2 opt-ins on `empty` / `reverse` / `addArc` are
  still valid (no Phase 11 change to those defs); check whether
  the absorbed reach machinery needs new opt-ins.

- [ ] **F2.1.** DFS re-audit. Verify or extend the existing 5
  per-decl `@[expose]` opt-ins. Append disposition delta row to
  PERFORMANCE.md F3.5.
- [ ] **F2.2.** Basic re-audit. Same pattern; verify or extend
  the existing 3 opt-ins. Append disposition delta row.

### F3. `LinearRigidityMatroid.lean` module conversion follow-up

- [ ] **F3.1.** Re-check `.lake/packages/Matroid/Matroid/Representation/Map.lean`
  module status at pass execution time. Phase 9-perf F3.1
  recorded "still starts with `import …` (plain `import`, not
  `public import`)"; verify whether the next dep-bump has changed
  this.
- [ ] **F3.2.** If converted: land LRM's conversion. Else: defer
  to next `apnelson1/Matroid` dep-bump cron cycle.

### F4. Baseline + post-pass measurements

Per `./PERFORMANCE.md` *Measurement protocol*: per-target
unique-content nudge then `lake build <target>`, 4 trials,
median-of-4.

- [ ] **F4.1.** Baseline. 4-run A/B median on the Phase 10+11
  measurement targets at the current `@[expose] public section`
  configuration. Targets: `Search/DFS.lean`,
  `PebbleGame/Basic.lean`, `PebbleGame/Algorithm.lean`,
  `PebbleGame/Correctness.lean`, `PebbleGame/Exec.lean`,
  project-total (nudge `EdgesIn.lean`). Compare project-total
  against Phase 9-perf F4.2 (10.04 s) as a regression check —
  Phase 10 added one new module-converted file (`Exec.lean`) and
  one non-`module` file (`Main.lean`); Phase 11 extended several
  module files in-place. Expected: project-total flat or modest
  uptick (10–12 s); per-file medians on the four un-audited files
  at the original split-time numbers (1024 + 771 + 815 ≈ 2610
  LoC ≈ Phase 9-perf F4.1's PebbleGame.lean 14.43 s spread
  across three smaller files).
- [ ] **F4.2.** Post-F1 / F2 measurement. 4-run A/B median vs
  F4.1 baseline. Expected (per Phase 8-perf F3.5 + Phase 9-perf
  F1's track record): perf-neutral within the ±5 s noise band —
  the bookkeeping value (F3.5 table rows) is the deliverable, not
  a wall-clock win. If F4.2 lands within noise, document as
  *perf-neutral, bookkeeping pass* per the
  `PERFORMANCE.md` *Experiments that didn't pay* /
  *Recommendations* framing.
- [ ] **F4.3.** Promotion. Append the per-decl audit row to
  `PERFORMANCE.md` *Experiments that didn't pay* if F4.2 is
  noise-band-neutral; or to *Experiments that did pay* if a
  measurable win lands. Update the *Granular `@[expose]` /
  `public` audit per file* preamble with the Phase 10+11-perf F1
  closure paragraph.

## Decisions made during this phase

### Phase-local choices and proof techniques

*(Empty — populate as fixes / measurements land.)*

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

*(Empty — populate as cross-cutting lessons surface.)*

## Blockers / open questions

- **LRM conversion still likely blocked on upstream.** Carry-over
  from Phase 9-perf F3 / Phase 8-perf F3.3; resolve in F3.

## Hand-off / next phase

To be written at pass close. Default: hand off cleanly with no
mid-stream state; the next session picks up from the top-level
ROADMAP per the round-level *No follow-up phase queued by
default* convention.
