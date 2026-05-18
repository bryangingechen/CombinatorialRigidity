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

F4.1 baseline measured. Phase 9-perf F4.2 set the prior baseline
(medians: `Search/DFS.lean` 8.70 s; `PebbleGame.lean` ~15.4 s;
project-total 10.04 s). Phase 10 split `PebbleGame.lean` into the
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

Headline F1 dispositions will land once the audit closes.

### F4.1 baseline (4-run medians, current `@[expose] public section` / per-decl-opt-in mix)

Protocol per `./PERFORMANCE.md` *Measurement protocol*: per-target
unique-content nudge then `lake build <target>`, 4 trials,
median-of-4.

| Target | run-1 | run-2 | run-3 | run-4 | median |
|---|---|---|---|---|---|
| `Search/DFS.lean` (`CombinatorialRigidity.Search.DFS`) | 6.672 | 5.976 | 5.774 | 5.841 | **5.91** |
| `PebbleGame/Basic.lean` (`CombinatorialRigidity.PebbleGame.Basic`) | 11.052 | 6.443 | 5.938 | 6.400 | **6.42** |
| `PebbleGame/Algorithm.lean` (`CombinatorialRigidity.PebbleGame.Algorithm`) | 12.309 | 7.901 | 7.776 | 7.418 | **7.84** |
| `PebbleGame/Correctness.lean` (`CombinatorialRigidity.PebbleGame.Correctness`) | 11.844 | 6.599 | 6.214 | 5.808 | **6.41** |
| `PebbleGame/Exec.lean` (`CombinatorialRigidity.PebbleGame.Exec`) | 14.740 | 6.727 | 9.335 | 11.156 | **10.25** |
| project-total (`CombinatorialRigidity`, nudge `EdgesIn.lean`) | 12.186 | 6.466 | 6.422 | 5.569 | **6.44** |

The run-1 outlier on each target is the canonical cold-cache trial
(PERFORMANCE.md *Timing reproducibility*); the median excludes it
naturally. Project-total median 6.44 s sits comfortably under Phase
9-perf F4.2's 10.04 s anchor — no regression from Phase 10+11
forward work; the Phase 10 split + the Phase 11 in-place reshapes
land net-flat-to-mild-improvement on from-scratch wall-clock.

Per-file medians: DFS 5.91 s sits below Phase 9-perf F4.2's 8.70 s
(F1.1 narrowed config carried forward unchanged by Phase 11
reshape). Across the three `PebbleGame/` subdirectory files: Basic
6.42 s + Algorithm 7.84 s + Correctness 6.41 s = 20.67 s total
versus the pre-split PebbleGame.lean's 15.4 s Phase 9-perf F4.2
median; the splits run a bit longer in aggregate because each file
re-elaborates Basic's transitive imports independently, but each
sits well below the original at the per-file rebuild grain. Exec at
10.25 s reflects its Phase 10 mix of `Decidable` instance synthesis
+ Phase 11 verdict-shaped re-route.

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

- [x] **F1.1.** `PebbleGame/Algorithm.lean` audit. Demote
  `@[expose] public section` → `public section`; restore
  `@[expose]` per-decl where build/lint requires it. Likely
  candidates: `tryAddEdgeWith`, `tryAddEdge`,
  `runPebbleGameWith`, `runPebbleGame` if any have `@[simp]
  := rfl` projection lemmas or intra-file pattern-match defeq
  consumers (Phase 11 Layer 4b's `runPebbleGame.aux` discharge
  bundle is a candidate). Append disposition row to PERFORMANCE.md
  F3.5 table. *Done; demoted, **one** per-decl opt-in
  (`runPebbleGameWith`). Trigger: `rw [runPebbleGameWith] at h`
  (×2) inside `runPebbleGameWith_witness_bridges`'s edge-list
  induction in `Correctness.lean` (nil + cons preambles) — the
  `rw [defname]`-as-unfold pattern needs the body. The other
  workhorse-level defs (`tryReachPebbleWith`, `tryReachPebble`,
  `tryAddEdgeWith`, `tryAddEdge`) demote cleanly; downstream
  consumes them through `match` on the `Sum`-shaped return or
  through API lemmas, not by name-as-unfold. Disposition row
  appended to PERFORMANCE.md F3.5 table.*
- [x] **F1.2.** `PebbleGame/Correctness.lean` audit. Same pattern.
  Layer 4b added `PebbleGameResult` inductive (auto-exposed
  constructors), `runPebbleGame_isAccept_iff` /
  `runPebbleGameExec_isAccept_iff` lemmas, and
  `WorkhorseWitness.certifies_against`. Mostly theorems, so
  expected to demote cleanly; verify. *Done; demoted, **one**
  per-decl opt-in (`PebbleGameResult.isAccept`). Trigger:
  downstream `simp [..., PebbleGameResult.isAccept, ...]` in
  `Exec.lean` line 319 (inside `runPebbleGameExec_aux_isAccept`'s
  `cases s <;> simp [...]` proof) — the `@[simp] def` taxonomy
  needs the body for the `match`-arm reduction. Errors when
  demoted: *"Invalid simp theorem `PebbleGameResult.isAccept`:
  Expected a definition with an exposed body"* (×2) plus the
  unsolved `inl` / `inr` goals that the simp call would have
  closed. The other defs in the file (`runPebbleGame.aux`,
  `runPebbleGame`) demote cleanly: their intra-file consumers
  (`simp [runPebbleGame.aux, ...]` at L820, `unfold runPebbleGame`
  at L838 — both inside same-module proofs of
  `runPebbleGame_aux_isAccept` / `runPebbleGame_isAccept_iff`) work
  under `public section` (intra-module `simp [defname]` /
  `unfold defname` don't require `@[expose]`; only intra-module
  `@[simp] := rfl` projection lemmas and downstream consumption do).
  Disposition row appended to PERFORMANCE.md F3.5 table.*
- [x] **F1.3.** `PebbleGame/Exec.lean` audit. Same pattern. Phase
  10 defs `outListSorted`, `edgeListSorted`,
  `runPebbleGameExec` may have intra-file `@[simp] := rfl`
  consumers; Layer 4b's verdict-returning `runPebbleGameExec` may
  need `@[expose]` if the three `Decidable` instances
  pattern-match its body. Disposition row. *Done; demoted cleanly,
  **zero** per-decl opt-ins. The three `Decidable` instances
  (`instDecidableIsSparse`, `instDecidableIsTight`,
  `instDecidableIsLaman`) route through `decidable_of_iff`,
  consuming `runPebbleGameExec` as a value via its `.isAccept`
  projection paired with the proved iff
  `runPebbleGameExec_isAccept_iff` — no body-unfolding required.
  Intra-file `def` consumption is uniformly via intra-module
  `rw [outListSorted, …]` / `simp only [edgeListSorted, …]` /
  `unfold edgeListSorted` / `simp [runPebbleGameExec.aux, …]` /
  `unfold runPebbleGameExec`, all of which work under `public
  section`. Matches the F3.5 `MatroidIdentification.lean` /
  `LamanTheorem.lean` pattern. Disposition row appended to
  PERFORMANCE.md F3.5 table.*
- [x] **F1.4.** `PebbleGame/Examples.lean` audit. Expected
  closure: trivial — file has no `def`s, only `#eval` commands
  that consume the Decidable instances at meta time. Demote to
  `public section` (no per-decl opt-ins); confirm `#eval`s still
  fire. *Done; demoted, **three** per-decl opt-ins
  (`k4MinusE`, `moserSpindle`, `path5`). The pre-pass "no `def`s"
  expectation was wrong — the file ships four worked-example graph
  `def`s alongside the `#eval` lines, each paired with an intra-file
  `instance : DecidableRel _.Adj` built via `decidable_of_iff` against
  a body-mentioning iff bridge (`SimpleGraph.deleteEdges_adj.symm` for
  `k4MinusE`; `(SimpleGraph.fromEdgeSet_adj _).symm` for
  `moserSpindle` / `path5`). Without `@[expose]` on the graph def,
  the bridge iff has the wrong shape (LHS mentions
  `(⊤ : SimpleGraph (Fin 4)).Adj` etc., but Lean expects the
  def-level `k4MinusE.Adj`), and the dependent `#eval (decide …)`
  lines abort with the sorry-axiom guard. `k4`'s instance uses
  `inferInstanceAs (DecidableRel (⊤ : SimpleGraph (Fin 4)).Adj)`, so
  it routes directly through the existing `(⊤ : _).Adj` `Decidable`
  with no body unfolding — clean demotion, no opt-in. The
  `Finset (Sym2 _)` helper defs (`moserEdges`, `path5Edges`) also
  demote cleanly; consumed only inside the graph defs' (now
  `@[expose]`) bodies. All 11 `#eval` lines fire after the audit,
  producing the documented expected values (5 / true / 11 / true /
  6 / false / false / 4 / true / false / false). Pattern matches
  the F3.5 `Henneberg.lean` row: a `DecidableRel _.Adj` instance
  built via `decidable_of_iff` against a body-mentioning bridge
  iff forces `@[expose]` on the underlying graph def. Disposition
  row appended to PERFORMANCE.md F3.5 table.*
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

- [x] **F2.1.** DFS re-audit. Verify or extend the existing 5
  per-decl `@[expose]` opt-ins. Append disposition delta row to
  PERFORMANCE.md F3.5. *Done; the 5 Phase 9-perf F1.1 opt-ins
  (`DirectedWalk.{length, vertices, IsPath, arcsFinset,
  reversedArcsFinset}`) are all still required at the same trigger
  sites (verified by demoting each and observing the documented
  build failure). The Phase 11 Layer 1 addition
  `reachClosureComputable` was pre-pass marked `@[expose]` but
  **does not need it** — its consumers are intra-file
  `rw [reachClosureComputable]` (works under `public section` per
  the F1.2 intra-module pattern) and downstream API-only
  consumption (via the `mem_reachClosureComputable` iff,
  `self_mem_reachClosureComputable`, and
  `reachClosureComputable_closed`, all of which are lemmas not
  affected by exposure). Net delta: −1 opt-in
  (`reachClosureComputable`'s `@[expose]` dropped); the file
  ships at the same 5-opt-in shape Phase 9-perf F1.1 closed at.
  Disposition row appended to PERFORMANCE.md F3.5 table.*
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

- [x] **F4.1.** Baseline. 4-run A/B median on the Phase 10+11
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
  across three smaller files). *Done; medians 5.91 / 6.42 / 7.84
  / 6.41 / 10.25 / 6.44 s — see Summary §F4.1 baseline. Project-
  total runs well under the 10.04 s anchor (no regression); per-
  file picture matches the pre-pass shape.*
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

- **F1.1 — `PebbleGame/Algorithm.lean` per-decl `@[expose]` audit.**
  Demoted `@[expose] public section` → `public section`; one per-decl
  opt-in restored on `runPebbleGameWith`. Trigger is the
  `rw [runPebbleGameWith] at h` pattern (×2) inside
  `runPebbleGameWith_witness_bridges`'s edge-list induction in
  `Correctness.lean` — the `rw [defname]`-as-unfold idiom needs the
  body. The other workhorse-level defs in the file
  (`tryReachPebbleWith`, `tryReachPebble`, `tryAddEdgeWith`,
  `tryAddEdge`) and `TryReachPebbleResult.newOrient` demote cleanly:
  downstream `Correctness` / `Exec` consume them via `match` on the
  `Sum`-shaped return (Layer 3 / 4b reshape) or via API lemmas, not
  through name-as-unfold. Matches the F3.5 pattern (`@[simp] := rfl`
  / `rw [name]` / `unfold name` triggers exposure, opaque `match` /
  API-lemma consumption demotes cleanly).
- **F1.2 — `PebbleGame/Correctness.lean` per-decl `@[expose]` audit.**
  Demoted `@[expose] public section` → `public section`; one per-decl
  opt-in restored on `PebbleGameResult.isAccept`. Trigger is the
  downstream `simp [..., PebbleGameResult.isAccept, ...]` call in
  `Exec.lean`'s `runPebbleGameExec_aux_isAccept` proof (matches F3.5's
  `@[simp] def` taxonomy: the simp linter / elaborator needs the body
  for the `match`-arm reduction). The two large defs in the file
  (`runPebbleGame.aux`, `runPebbleGame`) demote cleanly even though
  their intra-file proofs use `simp [runPebbleGame.aux, ...]` (L820)
  and `unfold runPebbleGame` (L838) — intra-module `simp [defname]` /
  `unfold defname` works under `public section`; only downstream
  `simp [defname]` and intra-module `@[simp] := rfl` projection lemmas
  force exposure. Confirms the F3.5 / F1.1 pattern.
- **F1.3 — `PebbleGame/Exec.lean` per-decl `@[expose]` audit.**
  Demoted `@[expose] public section` → `public section`; **zero**
  per-decl opt-ins required. All four defs (`outListSorted`,
  `edgeListSorted`, `runPebbleGameExec.aux`, `runPebbleGameExec`) and
  the three `Decidable` instances demote cleanly. The three
  `Decidable` instances route through `decidable_of_iff`, consuming
  `runPebbleGameExec` as a value via its `.isAccept` projection
  paired with the proved iff `runPebbleGameExec_isAccept_iff` — no
  body-unfolding required at the instance site. Intra-file `def`
  consumption is uniformly intra-module `rw`/`simp [defname]`/`unfold
  defname` patterns, all of which work under `public section`.
  Downstream `Examples.lean` (`#eval (decide G.IsLaman)` etc.) and
  `Main.lean` (CLI) reduce through the compiled body without source-
  level `@[expose]`. Matches the F3.5 `MatroidIdentification.lean` /
  `LamanTheorem.lean` pattern (theorem-and-instance file with
  API-only def consumption demotes with zero per-decl opt-ins).
- **F2.1 — `Search/DFS.lean` per-decl `@[expose]` re-audit under
  Phase 11 Layer 1 extension.** The 5 Phase 9-perf F1.1 opt-ins
  (`DirectedWalk.{length, vertices, IsPath, arcsFinset,
  reversedArcsFinset}`) are all still required at the same trigger
  sites: `length` via `simp [DirectedWalk.length]` at
  `PebbleGame/Basic.lean:401`; `vertices` + `IsPath` via
  `rw [DirectedWalk.IsPath, DirectedWalk.vertices, …]` at
  `Basic.lean:403` (inside `head_ne_tail_of_pos`); `arcsFinset` +
  `reversedArcsFinset` via intra-file
  `@[simp] {arcs,reversedArcs}Finset_{nil,cons} … := rfl`. Verified
  by demoting each and observing the documented build failure. The
  Phase 11 Layer 1 forward-work addition `reachClosureComputable`
  was pre-pass marked `@[expose]` but does not need it — intra-file
  `rw [reachClosureComputable, Finset.mem_filter]` in
  `_sound` / `_complete` works under `public section` (matches the
  F1.2 `runPebbleGame.aux` / `runPebbleGame` intra-module pattern),
  and downstream `PebbleGame/{Basic,Algorithm}.lean` consume it via
  the `mem_reachClosureComputable` iff (rw'd through to
  `Relation.ReflTransGen`), `self_mem_reachClosureComputable`, and
  `reachClosureComputable_closed` — API-only, no body unfolding.
  The Phase 11 Layer 1 theorems `DirectedWalk.toReflTransGen`,
  `reachClosureComputable_sound` / `_complete`, and the lemmas
  `mem_reachClosureComputable` etc. are not `def`s and so unaffected
  by the `@[expose]` axis. Net delta from Phase 9-perf F1.1: −1
  opt-in (`reachClosureComputable`'s `@[expose]` dropped); the file
  ships at the same 5-opt-in shape Phase 9-perf F1.1 closed at.
  Matches the F1.3 `PebbleGame/Exec.lean` pattern: a Phase
  11-reshape / Phase 11-Layer-1 forward-work file with API-only
  intra-file def consumption demotes cleanly without adding new
  opt-ins.
- **F1.4 — `PebbleGame/Examples.lean` per-decl `@[expose]` audit.**
  Demoted `@[expose] public section` → `public section`; **three**
  per-decl opt-ins required on the graph defs `k4MinusE` /
  `moserSpindle` / `path5`. The pre-pass "no `def`s, trivial closure"
  expectation was wrong — the file ships four worked-example graph
  `def`s alongside its `#eval` lines, three of them paired with an
  intra-file `instance : DecidableRel _.Adj` built via
  `decidable_of_iff` against a body-mentioning iff bridge
  (`SimpleGraph.deleteEdges_adj.symm` for `k4MinusE`;
  `(SimpleGraph.fromEdgeSet_adj _).symm` for `moserSpindle` /
  `path5`). Without `@[expose]` on the graph def, Lean reports
  *"Application type mismatch … has type `… ↔ (⊤ : SimpleGraph
  (Fin 4)).Adj a b ∧ …` but is expected to have type `… ↔
  k4MinusE.Adj a b`"* and dependent `#eval (decide …)` lines abort
  with the sorry-axiom guard. `k4`'s instance uses
  `inferInstanceAs (DecidableRel (⊤ : SimpleGraph (Fin 4)).Adj)`,
  routing directly through the existing `(⊤ : _).Adj` `Decidable`
  with no body unfolding — clean demotion, no opt-in. The
  `Finset (Sym2 _)` helper defs (`moserEdges`, `path5Edges`) also
  demote cleanly: consumed only inside the graph defs' (now
  `@[expose]`) bodies, not by the iff-bridge instances directly.
  All 11 `#eval` lines fire after the audit, producing the
  documented expected values. Pattern matches the F3.5
  `Henneberg.lean` row (intra-file `instDecidableTypeIAdj` /
  `instDecidableTypeIIAdj` triggered `@[expose]` on `typeI` /
  `typeII`): a `DecidableRel _.Adj` instance built via
  `decidable_of_iff` against a body-mentioning bridge iff forces
  `@[expose]` on the underlying graph def.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

*(Empty — populate as cross-cutting lessons surface.)*

## Blockers / open questions

- **LRM conversion still likely blocked on upstream.** Carry-over
  from Phase 9-perf F3 / Phase 8-perf F3.3; resolve in F3.

## Hand-off / next phase

**Next concrete commit:** F2.2 re-audit of `PebbleGame/Basic.lean`'s
existing 3 per-decl `@[expose]` opt-ins
(`PartialOrientation.{empty, reverse, addArc}` from Phase 9-perf
F1.2) under Phase 11's reach-closure absorption (Layer 1 + Layer 3
moved `reach`, `mem_reach`, `self_mem_reach`, `reach_closed`,
`outOn_eq_zero_of_closed`, `outOn_reach_union_eq_zero` from
Correctness into Basic) + `WorkhorseWitness` addition (Layer 2).
Mechanic: verify each of the 3 existing opt-ins is still triggered
(try demoting each individually and confirm a build failure
surfaces at the documented trigger site — the intra-file
`@[simp] arcs_empty / arcs_reverse / arcs_addArc := rfl`
projections); then audit the Phase 11 additions for new exposure
triggers (likely candidates: `reach` if any `@[simp] := rfl`
projection or downstream body-unfold appears, or `WorkhorseWitness`
if any `match`-arm defeq downstream needs the body). Append
disposition delta row to `./PERFORMANCE.md` *F3.5 audit disposition*
table.

After F2.2, F4.2 post-pass measurement (4-run A/B vs F4.1 baseline)
closes the pass; F4.3 promotes the pass's net disposition to
PERFORMANCE.md's *Experiments that didn't pay* (expected, per the
F3.5 / Phase 9-perf F1 track record).

If the session must stop mid-stream, the F4.1 baseline anchor + the
F1.1 disposition for `Algorithm.lean` (`runPebbleGameWith` per-decl
`@[expose]` only) + the F1.2 disposition for `Correctness.lean`
(`PebbleGameResult.isAccept` per-decl `@[expose]` only) + the F1.3
disposition for `Exec.lean` (clean demotion, zero per-decl opt-ins)
+ the F1.4 disposition for `Examples.lean` (demoted, three per-decl
opt-ins on `k4MinusE` / `moserSpindle` / `path5`) + the F2.1
re-audit for `Search/DFS.lean` (net delta −1 from Phase 9-perf
F1.1: `reachClosureComputable`'s `@[expose]` dropped; the 5
`DirectedWalk` opt-ins all still required) are the persistent state
added so far; the next session can pick up at F2.2 from a clean
tree. Final hand-off paragraph will be rewritten at pass close; the
default close convention is *no follow-up phase queued* per
`../CLEANUP.md`.
