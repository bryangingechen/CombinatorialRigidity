# Phase 9 — perf pass (work log)

**Status:** ✓ closed.

This was the post-Phase-9 perf pass running in parallel with the
`Phase9-cleanup.md` round per `../CLEANUP.md` *What a cleanup round
is not* (cleanup rounds do not measure performance; perf passes
have their own log + 4-run A/B protocol). See `./PERFORMANCE.md`
for the round-level operating manual: the anatomy of a `lake build`,
profiling switches, timing reproducibility, A/B measurement
protocol, and the standing recommendations.

## Summary

Closed: F1 (per-decl `@[expose]` audit on the two new Phase 9
files), F2 (PebbleGame split-candidate audit, audit-only), F3
(LRM module-conversion re-check), F4 (baseline + post-pass 4-run
A/B medians). Both Phase 9 files now sit at `public section` with
5 + 3 per-decl `@[expose]` opt-ins. F1 is **perf-neutral** within
the ±5 s noise band across DFS / PebbleGame / project-total; the
deliverable is the two-row append to PERFORMANCE.md's F3.5
disposition table + the per-decl audit row in *Experiments that
didn't pay*. F2 audit recommends keeping `PebbleGame.lean` as a
single file (zero downstream-import surface to save). F3 LRM
conversion stays blocked on upstream `apnelson1/Matroid`'s
`Map.lean` being non-`module`; re-check on next dep-bump.

### F4.2 post-F1 (4-run medians, `public section` + per-decl `@[expose]` opt-ins)

| Target | run-1 | run-2 | run-3 | run-4 | median | Δ vs F4.1 |
|---|---|---|---|---|---|---|
| `Search/DFS.lean` | 23.24 | 7.57 | 8.64 | 8.76 | **8.70** | +0.57 |
| `PebbleGame.lean` (run-set 2/3 cache-warm median) | 16.64 / 15.92 | 14.12 / 13.17 | 13.79 / 15.85 | (run-1 cold: 28.20 / 24.85) | **~15.4** | +~1.0 |
| project-total | 31.45 | 10.20 | 9.88 | 8.19 | **10.04** | +1.07 |

All Δ within the ±5 s noise band per `./PERFORMANCE.md`
*Recommendations for future perf work* #1 — **F1 perf-neutral**.

The first PebbleGame 4-run after F1 landed (medians ~25 s) was a
cache-cold cascade — a prior project-wide `lake build` had just
finished, so the system page cache held mathlib `.olean`s but the
`PebbleGame.olean` slot was still cold across multiple consecutive
content nudges. Two follow-up 4-run trials with the page cache
fully warmed stabilised at 13.79–16.64 s, matching the F4.1
baseline shape and confirming F1 is genuinely neutral, not a
regression. The bookkeeping value (audit dispositions in §F1.1 +
§F1.2) is the primary deliverable, as the pass overview predicted.

### F1.1 disposition — `Search/DFS.lean`

| Def | Per-decl `@[expose]`? | Trigger when demoted |
|---|---|---|
| `DirectedWalk` (inductive) | n/a | constructors auto-exposed |
| `DirectedWalk.length` | yes | `simp [DirectedWalk.length]` in `PebbleGame.lean` line 391; demote error: *"Invalid simp theorem `DirectedWalk.length`: Expected a definition with an exposed body"* |
| `DirectedWalk.vertices` | yes | `rw [DirectedWalk.IsPath, DirectedWalk.vertices, …]` in `PebbleGame.lean` line 393 |
| `DirectedWalk.IsPath` | yes | `rw [DirectedWalk.IsPath, …]` in `PebbleGame.lean` line 393; demote error: *"Invalid rewrite argument: … `DirectedWalk.IsPath ?p` is a value of type Prop"* (i.e., body not exposed for `rw`) |
| `DirectedWalk.mapRel` | no | consumed opaquely (called as a function value); intra-file `@[simp]` lemmas (`mapRel_length`, `mapRel_vertices`) are proved by induction + `rw`, not `rfl` |
| `DirectedWalk.arcsFinset` | yes | intra-file `@[simp] arcsFinset_{nil,cons} … := rfl` (lines 245–249); demote error: *"Not a definitional equality: `(nil u).arcsFinset` is not definitionally equal to `∅`"* |
| `DirectedWalk.reversedArcsFinset` | yes | intra-file `@[simp] reversedArcsFinset_{nil,cons} … := rfl` (lines 251–256); same shape as `arcsFinset` |
| `DirectedWalk.dropUntilBundle` | no | the `Subtype`-bundled truncation: consumed by `reachableFindingAux` and `reachableFinding` as a value; downstream sees it through `IsPath` / endpoint witnesses, not body |
| `reachableFinding`, `reachableFindingAux` | no | the DFS body — consumed via the `Sum`-shaped result; soundness/completeness lemmas mediate all reasoning, no body access needed |
| `reachClosure` | no | only the `@[simp] mem_reachClosure` lemma is consumed downstream; the `Relation.ReflTransGen` body stays opaque |

The dominant trigger is the **`@[simp] ... := rfl` pattern**
(arcsFinset / reversedArcsFinset projections) and the **`simp [name]`
/ `rw [name]`-as-unfold** pattern (length / vertices / IsPath) — both
matching the F3.5 *Lessons* taxonomy in `./PERFORMANCE.md`.

### F1.2 disposition — `PebbleGame.lean`

| Def | Per-decl `@[expose]`? | Trigger when demoted |
|---|---|---|
| `PartialOrientation` (structure) | n/a | structure `mk` + field projections auto-exposed; `D.arcs` access is the projector, not a body unfold |
| `empty` | yes | intra-file `@[simp] arcs_empty : (empty …).arcs = ∅ := rfl` (line 101); demote error: *"Not a definitional equality: `empty.arcs` is not definitionally equal to `∅`"* |
| `reverse` | yes | intra-file `@[simp] arcs_reverse : (D.reverse p hp).arcs = (D.arcs \ p.arcsFinset) ∪ p.reversedArcsFinset := rfl` (line 315) |
| `addArc` | yes | intra-file `@[simp] arcs_addArc : (D.addArc u v …).arcs = insert (u, v) D.arcs := rfl` (line 644) |
| `outNbhd`, `outList`, `out`, `peb`, `spanArcs`, `span`, `boundaryArcs`, `outOn`, `pebOn`, `underline` | no | derived count defs; all consumed via named API lemmas (`mem_outNbhd`, `out_eq_card_filter_fst`, `span_eq_ncard_edgesIn`, etc.) which carry their own proofs, never via body unfold |
| `tryReachPebbleWith`, `tryAddEdgeWith`, `runPebbleGameWith` | no | computable workhorses; consumed by the noncomputable wrappers via call-site equation, not body |
| `tryReachPebble`, `tryAddEdge`, `runPebbleGame`, `reach` | no | noncomputable math-layer wrappers; downstream consumes via the correctness theorems (`runPebbleGame_correct`, `tryAddEdge_correct`, etc.), not body |
| `Reachable` (inductive) | n/a | constructors + recursor auto-exposed by the inductive declaration |
| `TryReachPebbleResult` (structure) | n/a | `mk` + field projections auto-exposed |

The trigger pattern is uniform: **the three `@[simp] D.<state-op>.arcs = … := rfl` projection lemmas** force `empty` / `reverse` / `addArc` to expose. No other def in the file has a `@[simp] := rfl` companion or a `simp [defName]` / `rw [defName]`-as-unfold call site, so the rest demote cleanly. Same F3.5 *Lessons* pattern as F1.1.

### F4.1 baseline (4-run medians, `@[expose] public section`)

Protocol per `./PERFORMANCE.md` *Measurement protocol*: per-target
unique-content nudge then `lake build <target>`, 4 trials,
median-of-4.

| Target | run-1 | run-2 | run-3 | run-4 | median |
|---|---|---|---|---|---|
| `Search/DFS.lean` (`CombinatorialRigidity.Search.DFS`) | 19.78 | 8.40 | 7.46 | 7.86 | **8.13** |
| `PebbleGame.lean` (`CombinatorialRigidity.PebbleGame`) | 22.59 | 13.28 | 13.99 | 14.87 | **14.43** |
| project-total (`CombinatorialRigidity`, nudge `EdgesIn.lean`) | 26.10 | 7.89 | 9.69 | 8.25 | **8.97** |

The run-1 outlier on each target is the canonical cold-cache trial
(PERFORMANCE.md *Timing reproducibility*); the median excludes it
naturally. Project-total median is within noise of Phase 8-perf
F3.6's 9.2 s headline, confirming no regression from the Phase 9
forward-work commits.

Phase 9 already shipped its two new files in `module` form
(`Search/DFS.lean` L7 `module`, `PebbleGame.lean` L7 `module`),
matching the Phase 8-perf F3.3 post-state — so the pass does not
repeat the project-wide F3.2 / F3.3 conversion. Both files
currently sit at the coarsest exposure level
(`@[expose] public section`); the natural perf lever is the
**F3.5-style per-decl `@[expose]` audit** that the post-Phase-8 perf
pass ran on the original 12 project files. Phase 9 added two
more — discharge them here.

## Pass overview

This pass is the natural follow-up to the Phase 8-perf F3.5 audit:
demote the two new Phase 9 files from `@[expose] public section` to
plain `public section`, restoring `@[expose]` per-decl only on the
defs whose bodies are genuinely consumed (downstream or intra-file
via `rfl`-proved `@[simp]` lemmas / pattern-match defeq /
`unfold`-style destructure). Per `PERFORMANCE.md` *Lessons*:
"`public section` is opaque intra-module too" — the audit is
informed by the same intra-module elaboration-time-defeq triggers
that surfaced during F3.5 (e.g., `@[simp] ... := rfl` always forces
`@[expose]`).

Secondary levers, all audit-only unless A/B demonstrates a win:

- **F2.** `PebbleGame.lean` internal split candidates. The file is
  2500 LoC across 13+ named sections (Reverse / AddArc /
  Reachability / TryReachPebble / TryAddEdge / RunPebbleGame /
  Soundness / Completeness / Correctness / Matroidal). Natural cut
  lines exist (e.g., between *Soundness* and *Completeness* at
  ~L1842/L1851), but the file has no downstream importers other
  than the terminal `CombinatorialRigidity.lean` entry point, so a
  split saves zero transitive-import surface for any consumer.
  Audit-only; the per-incremental-rebuild benefit of split files
  is the only motivation, and that's well within the noise band.
- **F3.** `LinearRigidityMatroid.lean` module conversion
  follow-up. Phase 8-perf F3.3 carved LRM out as blocked on
  `apnelson1/Matroid`'s `Matroid.Representation.Map` being
  non-`module`. Re-check the upstream status as part of this pass;
  if `Map.lean` has converted, land LRM's conversion as a
  one-commit follow-up. (Initial check at pass-open:
  `.lake/packages/Matroid/Matroid/Representation/Map.lean` still
  starts with `import`, not `public import`, so the block stands —
  re-check on dep-bump.)

## Task checklist

### F1. Per-decl `@[expose]` audit on the two new Phase 9 files

Pattern: F3.5 of Phase 8-perf. For each file, attempt
`@[expose] public section → public section` and observe what breaks
(intra-file or downstream); restore `@[expose]` on the per-decl
sites whose bodies are genuinely consumed. Document the trigger +
disposition in the file's row of an F1 table here.

- [x] **F1.1.** `Search/DFS.lean` audit. *Done; demoted to
  `public section` with 5 per-decl `@[expose]` opt-ins on
  `DirectedWalk.{length, vertices, IsPath, arcsFinset,
  reversedArcsFinset}`. See* §F1.1 disposition *below for
  triggers.* The DFS body (`reachableFinding`,
  `reachableFindingAux`, `dropUntilBundle`, `reachClosure`, the
  `mapRel` mapper) is consumed opaquely by `PebbleGame.lean` and
  did not need exposure.
- [x] **F1.2.** `PebbleGame.lean` audit. *Done; demoted to `public
  section` with 3 per-decl `@[expose]` opt-ins on the
  `PartialOrientation`-producing defs* `empty`, `reverse`,
  `addArc`. *See* §F1.2 disposition *below for triggers.* The
  derived count defs (`out`/`peb`/`span`/`outOn`/`pebOn`/
  `spanArcs`/`boundaryArcs`/`underline`/`outList`/`outNbhd`/
  `reach`), the algorithm workhorses (`tryReachPebbleWith`,
  `tryAddEdgeWith`, `runPebbleGameWith`) and their noncomputable
  math-layer wrappers, and the `Reachable` inductive +
  `TryReachPebbleResult` structure all stayed unexposed — they're
  consumed via the named API lemmas (`out_addArc_source`,
  `span_eq_ncard_edgesIn`, etc.) and the `Sum`-shaped
  `TryReachPebbleResult` accessors, never via body access.
- [x] **F1.3.** Update `./PERFORMANCE.md` *Granular `@[expose]` /
  `public` audit per file* with the F1.1 / F1.2 dispositions.
  *Done; two rows appended to the F3.5 disposition table, status
  preamble extended with the Phase 9-perf F1 closure paragraph,
  and a per-decl `@[expose]` audit row added to* Experiments that
  didn't pay.

### F2. `PebbleGame.lean` internal split candidates (audit-only)

- [x] **F2.1.** Section-level boundaries audit. *Done; current
  line numbers (PebbleGame.lean at 2489 LoC): L274 Reverse →
  L605 AddArc → L821 Reachability → L1036 TryReachPebble →
  L1219 TryAddEdge → L1472 RunPebbleGame → L1755 Soundness →
  L1863 Completeness → L2390 Correctness → L2464 Matroidal.
  Documented in PERFORMANCE.md* Split candidates ranked by
  leverage *item 5.*
- [x] **F2.2.** Single-downstream-consumer verification. *Done;
  `grep -rn "import.*PebbleGame"` over the project tree returns
  exactly one hit (`CombinatorialRigidity.lean`, the top-level
  entry point, `import`-statements only). Splits save zero
  transitive-import surface for any consumer.*
- [x] **F2.3.** Recommendation: keep as a single file. *Done;
  recorded in PERFORMANCE.md* Split candidates ranked by leverage
  *item 5. The file's section organisation already maps cleanly to
  the blueprint chapter, and F1.2's per-decl `@[expose]` audit is
  the cheaper lever for the same per-rebuild outcome.*

### F3. `LinearRigidityMatroid.lean` module conversion follow-up

- [x] **F3.1.** Re-check `.lake/packages/Matroid/Matroid/Representation/Map.lean`
  module status at pass execution time. *Done at session open:
  still starts with `import Mathlib.LinearAlgebra.FiniteDimensional.Defs`
  (plain `import`, not `public import`; no `module` marker) —
  block stands.*
- [x] **F3.2.** If converted: land LRM's conversion. *N/A — block
  stands; defer to next `apnelson1/Matroid` dep-bump cron cycle.*
- [x] **F3.3.** If converted, update PERFORMANCE.md *Module system*
  to remove the LRM carve-out paragraph. *N/A — block stands;
  LRM carve-out remains accurate.*

### F4. Baseline + post-pass measurements

Per `./PERFORMANCE.md` *Measurement protocol*:

- [x] **F4.1.** Baseline. 4-run A/B median on the two new Phase 9
  targets (`Search/DFS.lean`, `PebbleGame.lean`) at the current
  `@[expose] public section` configuration. Project-total baseline
  on top of Phase 8-perf F3.6's 9.2 s headline. *Done; medians
  8.13 / 14.43 / 8.97 s — see* Current state §F4.1 baseline.
- [x] **F4.2.** Post-F1 measurement. *Done; medians 8.70 / ~15.4 /
  10.04 s — Δ = +0.57 / +1.0 / +1.07 s vs F4.1 baseline. All three
  targets within the ±5 s noise band — F1 perf-neutral. See*
  Current state §F4.2 post-F1 *for the raw runs.*
- [x] **F4.3.** Promotion. *Done in the same commit as F1.3 —
  PERFORMANCE.md* Experiments that didn't pay *now lists the
  per-decl audit row; the F3.5 disposition table has two new
  rows; the F3.5 closure preamble notes the Phase 9-perf F1
  follow-up.*

## Blockers / open questions

- **LRM conversion still blocked on upstream.** Re-check at next
  `apnelson1/Matroid` dep-bump.

## Hand-off / next phase

Pass closed. Phase 9 main + closure landed in earlier sessions;
this perf pass + the parallel `Phase9-cleanup.md` round complete
the post-Phase-9 hygiene. The pass's F1 outcome was perf-neutral
(as predicted in the pass overview); the F1 disposition tables
augment the F3.5 reference in PERFORMANCE.md and extend the
audit's coverage to all 14 + 2 = 16 module-converted project files.

**Carry-overs to the next pass / round / phase:**

- **LRM module conversion (F3.2/F3.3).** Blocked on
  `apnelson1/Matroid` upstream; fires when `Matroid/Representation/
  Map.lean` flips to `module`. Defer to the next `apnelson1/Matroid`
  dep-bump cron cycle (`hopscotch/bump-mathlib`-style PR).
- **PebbleGame.lean structural split (F2).** Audit-only, perf-
  neutral by single-downstream-consumer analysis; revisit only
  if a downstream phase introduces a new consumer that would
  benefit from one half of the file (none currently planned).

**Next phase.** Whatever pulls in beyond Phase 9 — the deferred
*component pebble game* (Lee–Streinu §5, $O(n^2)$ speedup via
union pair-find) and the *Henneberg-sequence application*
(Lee–Streinu §6) are the natural next forward-mode chapters per
`../ROADMAP.md` *§9*. The project's perf baseline is now
8.13 / 14.43 / 8.97 s on the Phase 9 surface (DFS / PebbleGame /
project-total).
