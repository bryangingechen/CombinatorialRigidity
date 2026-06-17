# Build performance notes

A long-running log of build-time observations and profiling findings for
this project. Read this **before** you run a performance pass — most of the
"obvious" optimization ideas have been tried, and several were reverted as
either neutral or actively worse under measurement noise. The point of this
file is to save the next agent from re-litigating the same dead ends.

> **Scope.** This is project-specific. Cross-cutting tactical idioms live
> in `TACTICS-GOLF.md` (idioms) or `TACTICS-QUIRKS.md` (rescue);
> one-off API gaps live in `notes/FRICTION.md`. If a
> performance lesson generalizes ("always prefer X over Y in this
> codebase"), promote it to TACTICS-GOLF or TACTICS-QUIRKS and leave
> a one-line pointer here.

## TL;DR

- A from-scratch `lake build` of `Framework.lean`, `HennebergRigidity.lean`,
  `LamanTheorem.lean`, and `Laman.lean` runs at ~20–40 s each on most
  machines; the bulk is **import loading** (~25–27 s of shared overhead for
  the analysis-heavy files), not the per-file elaboration (5–19 s).
- `set_option profiler true` captures only ~25–30% of the elapsed time;
  the rest is process-level work Lean doesn't attribute per-declaration.
- Wall-clock measurements are **wildly noisy** (10–50 s for the same source,
  depending on lake's content-addressed cache + OS page cache). A/B
  comparing a single optimization candidate usually returns ambiguous
  results unless you run 4+ trials per side, and even then the noise
  often swallows the signal.
- **Module-system conversion is the project's largest measured win**
  (Phase 8-perf F3.2–F3.6): HR −36.5 s, RM −31.0 s, LRM −45.5 s,
  project-total −12.0 s vs F1.1 baseline, each 2–9× the ±5 s noise
  band. Mechanism in *Experiments that did pay* and *Module system*
  below. The other structural levers audited in the post-Phase-8
  round (Sparsity / Henneberg splits, MatroidIdentification split)
  individually landed perf-neutral.
- The **safe** local levers are: remove dead imports; replace bare `simp`
  with `simp only` when the rewrite set is fixed and small; extract a
  helper *only when* the duplication is ≥ ~3 lines × ≥ 2 sites *and* the
  helper's signature is short. Everything else lives in the noise band.

## Anatomy of a `lake build`

Three observable layers, descending order of cost:

1. **Imports.** Loading every transitively-imported `.olean` into the Lean
   server. For our analysis-heavy files (anything that ultimately pulls
   `Mathlib.Analysis.Normed.Module.FiniteDimension` /
   `…InnerProductSpace.PiL2`) this is ~25–27 s; for the combinatorial files
   (`Sparsity.lean`, `Laman.lean`) it's ~10–11 s. *Measure it directly* by
   creating a stub file with just the imports and running
   `lake env lean /path/to/stub.lean`; this skips elaboration and writing
   `.olean`, so the wall-clock is close to the import floor.

2. **Per-file elaboration.** What Lean spends *between* "imports loaded"
   and "writing the `.olean`". This is what your source code controls.
   Approximate budget (third cleanup pass measurements):
   - `Framework.lean`: ~6 s
   - `HennebergRigidity.lean`: ~19 s
   - `Laman.lean`: ~11 s
   - `LamanTheorem.lean`: ~5 s

3. **Per-file cleanup.** `.olean` serialization (~0.5–0.8 s for HR's
   file size), linting (~0.6–1.3 s with mathlib linters enabled), `.ilean`
   writing, IR generation for the runtime executable side. Mostly
   fixed overhead per declaration; not directly editable from proof
   source.

## Profiling

### File-level switches

Add at the top of a file (before `namespace`) to log per-declaration
elaboration times to stderr:

```lean
set_option profiler true
set_option profiler.threshold 0
```

- Default `profiler.threshold` is 100 ms — anything faster doesn't print.
  Set to `0` to see all declarations.
- The `cumulative profiling times: …` block at the end of the build
  summarizes time per *category* (`tactic execution`, `typeclass inference`,
  `linting`, `.olean serialization`, etc.) across the whole file.
- The Mathlib style linter warns about `set_option profiler` in committed
  code — keep these switches local to a measurement session and revert
  before commit.

### JSON profiler output

```lean
set_option trace.profiler true
set_option trace.profiler.output "/tmp/profile.json"
```

Writes a Chrome-tracing-compatible JSON file. *Caveat:* on this Lean
version (`v4.30.0-rc2`) the option didn't actually emit a file when set
file-locally inside the source; an `-D` command-line override may be
required. The `set_option profiler true` text output was enough for our
needs.

### Confidence check

The cumulative profiler numbers do **not** sum to the wall-clock build
time. For `HennebergRigidity.lean`, cumulative was ~5.3 s
(`typeclass inference 1.7 s`, `linting 1.25 s`, `tactic execution 1.0 s`,
`.olean serialization 0.7 s`, `simp 0.3 s`, type checking + elaboration
~0.3 s), but file build was ~19 s — about 14 s is process-level work
(instance resolution outside `Meta.synthInstance` accounting, IR/codegen,
linker startup, lake bookkeeping) that the profiler doesn't expose.
**Don't tune for the cumulative-profile bottleneck and expect it to move
the wall-clock proportionally** — they're different sums.

## Timing reproducibility

`lake build` caches at multiple layers, with surprising consequences:

- **`.olean` cache.** Touching a file's mtime doesn't invalidate; lake
  uses content hashes. Append a unique nudge comment (e.g.
  `echo "-- nudge $RANDOM" >> file.lean`) to force a real rebuild, then
  remove the nudge afterward.
- **Content-addressed replay.** If the *exact* file content has been built
  before, lake reports `Replayed` in milliseconds rather than rebuilding.
  Even adding+removing a trailing newline can flip between cached
  and uncached states.
- **OS page cache.** Even with a real rebuild, the kernel caches the
  `.olean` files of dependencies. The first build after a cold boot is
  *much* slower than the second. On this machine, repeated rebuilds of
  the same source returned 10–50 s. The third or fourth identical-content
  build is usually 2–3× faster than the first.

### Measurement protocol

For an honest A/B comparison:

```bash
# 1. With baseline source: 4+ runs back-to-back, each preceded by a
#    unique-content nudge.
for i in 1 2 3 4; do
  echo "-- nudge-$RANDOM-$i" >> file.lean
  { time lake build CombinatorialRigidity.X 2>&1 > /tmp/_out; } 2>&1 | grep real
  sed -i.bak "/^-- nudge-/d" file.lean
  rm file.lean.bak
done

# 2. Apply the change.

# 3. Repeat step 1.

# 4. Compare *medians*, not means — there's usually one cache-hit
#    outlier per sample that ruins the mean.
```

Even with this protocol, anything sub-5-second is likely noise. If your
candidate's median is within ~5 s of baseline, treat it as neutral.

## Module system

Mathlib (as of v4.30.0-rc2) is mid-conversion to Lean's new module
system: files start with `module`, declare `public import X` for re-exported
dependencies, and have `@[expose] public section` markers to make declarations
visible to importers. The downstream benefit is a smaller load surface —
files importing module M only need M's public interface, not its full
elaboration state.

**For this project, conversion landed in the post-Phase-8 perf pass
(F3.2–F3.6) and is the project's largest measured win** — see
*Experiments that did pay* above for the 4-run A/B headline. The
mechanic and per-file disposition tables live in *Granular `@[expose]`
/ `public` audit per file* below (F3.4 + F3.5 dispositions). One
file remains non-`module`: `LinearRigidityMatroid.lean`, blocked
on `apnelson1/Matroid`'s `Matroid.Representation.Map` being
non-`module` (~4 % of `apnelson1/Matroid` is converted as of
2026-05). A future one-commit follow-up can convert LRM when the
upstream lands.

**Molecular chain is non-`module` (Phase 17+).** The molecular /
body-bar files (`BodyBar/*.lean`, `Molecular/{Extensor, Meet,
RigidityMatrix, Deficiency}.lean`, `Molecular/Induction/`) were authored
non-`module`, so anything that must consume them stays non-`module`
too. Phase 21's `Molecular/AlgebraicInduction.lean` was authored
`module` (importing only the `module`-converted `RigidityMatrix` +
`Meet`), but the Theorem 5.5 capstone (`thm:theorem-55`) needs
`Graph.minimal_kdof_reduction` from the non-`module`
`Molecular/Induction.lean`. Per the same constraint that keeps LRM
non-`module`, `AlgebraicInduction.lean` was **demoted** to
non-`module` (drop `module`, `public import` → `import`, drop the
`@[expose] public section`) in the `thm:theorem-55` commit —
mechanical and warning-clean (non-`module` is the more permissive
mode; demotion cannot break compilation). Converting the whole
molecular chain to `module` is a future perf pass; re-promote
`AlgebraicInduction` then. **Pre-Phase-22b structure pass:**
`AlgebraicInduction.lean` and `Induction.lean` were each split into a 5-file
subdirectory (`AlgebraicInduction/`, `Induction/`); the sub-files all inherit
the non-`module` status (`notes/Phase22-structure.md`).

Constraint that drives ordering: a `module` file cannot import a
non-`module` file (build error: *"cannot import non-`module` X from
`module`"*); non-`module` files can freely import `module` files.
That's why F3.2 (mirrors) lands before F3.3 (project files): the
mirrors are leaves we control, and mathlib v4.30.0-rc2 is ~98.6 %
`module`-converted upstream.

Sample upstream pattern, in `Mathlib/Analysis/InnerProductSpace/PiL2.lean`:

```lean
/- copyright header -/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Normed.Lp.PiLp
…

/-! # title -/

@[expose] public section

/- declarations follow -/
```

## Experiments that *didn't* pay (third cleanup pass)

Each of these was tried in isolation with a 4-run A/B and reverted because
the trend was either flat or slightly worse:

| Change | What it touched | Verdict |
|---|---|---|
| `set p_ext … with hp_ext_def` → `let p_ext := …` | `typeI`/`typeII_isInfinitesimallyRigid_extend` (`HennebergRigidity.lean`) | Median ~36 s with `let` vs ~25 s with `set`. `set`'s named alias short-circuits more unification than `let`'s transparent binding. Reverted. |
| `change ⟪q - p a, …⟫ at hxa hxb hya hyb` (×4) → `simp only [hp_ext_def, Option.elim_none, Option.elim_some, …]` (×1) | Same two theorems' kernel-injectivity blocks | `lake env lean` median ~24 s with `simp` vs ~16 s with four `change`s. `change` does pure defeq; `simp` has to chase the lambda explicitly. Reverted. |
| Extract `kerRestrict` helper for the `LinearMap.funLeft … codRestrict …` builder duplicated in typeI/typeII | New private `def` near the top of `HennebergRigidity.lean`; two `let restrict := kerRestrict …` call sites | 4-run mean ~46 s vs ~30 s baseline. Suspected regression from the abstraction layer; in any case the duplication is only one identical 4-line block per move. Reverted. |
| `nlinarith [Nat.le_mul_self d]` → `have h_sq := Nat.le_mul_self d; have : (d+1)*(d+2) = d*d + 3*d + 2 := by ring; omega` | `top_fin_two_isGenericallyRigidInj` in `Framework.lean` | Saved 120 ms in the per-decl profile; file timing didn't move out of the noise band. Reverted; `nlinarith` is the more idiomatic one-liner for "linear-after-hinting-a-square" goals. |
| Replace `fun_prop` with an explicit `continuous_pi fun _ => continuous_pi fun e => continuous_rigidityMap_apply …` chain | `IsInfinitesimallyRigid.eventually` in `Framework.lean` | Within noise band (median ~24 s vs ~27 s baseline). Reverted — `fun_prop` is the project convention (cf. TACTICS-GOLF § 6). |
| Per-decl `@[expose]` audit (Phase 9-perf F1; Phase 10+11-perf F1 + F2) | `Search/DFS.lean`, `PebbleGame.lean` (Phase 9-perf F1; pre-Phase-10 split); `PebbleGame/{Algorithm, Correctness, Exec, Examples}.lean` (Phase 10+11-perf F1.1–F1.4 — the four Phase 10/11 files that shipped at `@[expose] public section`); `Search/DFS.lean` + `PebbleGame/Basic.lean` re-audited under Phase 11 reshape (Phase 10+11-perf F2.1 + F2.2). Demote `@[expose] public section` → `public section`, restore `@[expose]` on the defs whose bodies are genuinely consumed (`@[simp] := rfl` projections; downstream `simp [name]` / `rw [name]`-as-unfold call sites; `DecidableRel _.Adj` bridge-iff instances). Net opt-in counts post-pass: Algorithm 1 (`runPebbleGameWith`); Correctness 1 (`PebbleGameResult.isAccept`); Exec 0 (clean); Examples 3 (`k4MinusE`, `moserSpindle`, `path5`); DFS 5 (unchanged from Phase 9-perf F1.1); Basic 9 (`PartialOrientation.{empty, out, peb, spanArcs, span, pebOn, underline, reverse, addArc}` — Phase 10 split shipped at file-wide `@[expose]`; F2.2 narrows to per-decl). | Phase 9-perf F1: all three measured targets within ±5 s noise band: DFS 8.13 → 8.70 s (Δ +0.57); PebbleGame 14.43 → ~15.4 s (Δ +~1.0); project-total 8.97 → 10.04 s (Δ +1.07). See `Phase9-perf.md` §F4.1/§F4.2. Phase 10+11-perf F4: five of six per-target medians within ±5 s noise band: DFS 5.91 → 7.53 s (Δ +1.62); Basic 6.42 → 9.53 s (Δ +3.11); Correctness 6.41 → 7.37 s (Δ +0.96); Exec 10.25 → 6.81 s (Δ −3.44); project-total 6.44 → 7.27 s (Δ +0.83). Algorithm at 7.84 → 14.34 s (Δ +6.50) sits just past the band, but the F1/F2 audit changed zero proof bodies and zero algorithmic content (only the section-marker / per-decl-`@[expose]` shape shifted), so the most plausible reading is OS-level run-to-run drift between baseline and post-pass sessions (PERFORMANCE.md *Timing reproducibility* documents 10–50 s spreads on the same source). Project-total median sits well under the Phase 9-perf F4.2 anchor (10.04 s). See `Phase11-perf.md` §F4.1/§F4.2. **Kept** — the bookkeeping value (rows in the F3.5 audit-disposition table) is the deliverable, matching the F3.5 pattern itself: the headline win was in Phase 8-perf F3.2–F3.4 (module-system conversion + private-cleanup), not F3.5 / Phase 9-perf F1 / Phase 10+11-perf F1+F2 (per-decl narrowing). |

## Experiments that *did* pay (or are at least defensible)

- **Module-system conversion + narrowed exposure surface (Phase 8-perf
  F3.2–F3.6).** The largest single-pass perf win measured in the
  project's history. Post-pass 4-run A/B medians vs F1.1 baseline:
  `HennebergRigidity` 57.3 → 20.8 s (−36.5 s); `RigidityMatroid`
  53.7 → 22.7 s (−31.0 s); `LinearRigidityMatroid` 62.3 → 16.8 s
  (−45.5 s); project-total 21.2 → 9.2 s (−12.0 s). Each Δ is 2–9×
  the ±5 s noise band threshold. Mechanism: in the module system,
  importing module M loads only M's public interface (names +
  types of exposed declarations), not its full elaboration state
  (unexposed `def` bodies stay opaque to importers). The pass landed
  in five steps: (F3.2) convert 14 `Mathlib/` mirror files; (F3.3)
  convert 13 of 14 project files (`LinearRigidityMatroid.lean`
  carved out by upstream `apnelson1/Matroid` non-`module` dep);
  (F3.4) discharge the 4 + 3 transient `backward.privateInPublic`
  opt-ins; (F3.5) demote 11 of 12 `@[expose] public section` files
  to `public section` with 12 per-decl `@[expose]` opt-ins on the
  defs whose bodies are genuinely consumed (full disposition table:
  *F3.5 audit disposition* above); (F3.6) measurement. Full work
  log: `notes/Phase8-perf.md`. **The pre-pass perf estimate
  ("1–3 s per file, in the noise band", *Module system* below) was
  off by ~10×** — future module-system passes in mathlib-style
  projects should expect larger savings than the prior estimate
  predicted.
- **Remove dead imports.** `Framework.lean` previously imported
  `Mathlib.LinearAlgebra.Dimension.Finrank` and `…Dimension.Free`; both
  are transitively pulled in via `Mathlib.Analysis.InnerProductSpace.PiL2`
  /`Mathlib.Analysis.Normed.Module.FiniteDimension`. Dropping them
  doesn't measurably affect the wall-clock (no transitive change in load
  set) but they were dead code. Worth doing on instinct.
- **Earlier cleanup-pass wins** (see `notes/Phase5.md` *Cleanup pass
  summaries*) shipped genuine LoC reductions: the `inner_sub_perp_of_eq`,
  `injective_option_elim`, `exists_not_mem_span_singleton_dim_two`, and
  `kerRestrict`-precursor (inline-`restrict`-LinearMap → `LinearMap.funLeft
  + codRestrict`) extractions were all kept because they shortened multiple
  call sites and the abstraction was natural.

## Post-Phase-8 file-structure audit

The post-Phase-8 cleanup round's bucket E originally surveyed the
project's import graph and file sizes for split candidates as
audit-only findings. **Three of the highest-leverage candidates have
since landed as executed splits:** the `Sparsity.lean` /
`SparsityIComponents.lean` split in Phase 8-perf F1 (item 1 below),
the `Henneberg.lean` / `HennebergReverse.lean` split in Phase 8-perf
F2 (item 2), and the `PebbleGame.lean` / `PebbleGame/{Basic,
Algorithm, Correctness}.lean` subdirectory split landed
post-Phase-9-perf under the revised framework (item 5). The other
items are still recommendations.

The **pre-Phase-22b structure pass** (`notes/Phase22-structure.md`) added two
more subdirectory splits, on the over-cap molecular giants:
`Molecular/AlgebraicInduction.lean` (5918 LoC, 3.9× the soft cap) →
`AlgebraicInduction/` (5 files: `PanelLayer`/`Pinning`/`PanelHinge`/`GenericityDevice`/`CaseI`),
and `Molecular/Induction.lean` (4256 LoC, 2.8×) → `Induction/` (5 files:
`Operations`/`SplitOffDeficiency`/`ReducibleVertex`/`Contraction`/`ForestSurgery`). Both done
bottom-up with a linear import chain and the no-hub convention (the original is deleted; the
root aggregator imports the terminal leaf — cf. the deleted `PebbleGame.lean`). The splits are
pure semantics-preserving moves: no declaration renamed, so the blueprint `\lean{...}` pins are
by-name and `checkdecls` is unaffected. `AlgebraicInduction` is the active file for the
realization-layer phases (22b+), so factor 3 (incremental-rebuild) is the live driver there;
`Induction` is stable, split on the file-size/navigability axis (factor 2).

The snapshot below is the post-Phase-8 state (pre-PebbleGame split);
the import graph adds a `PebbleGame.Basic ← Algorithm ← Correctness`
chain consumed by `CombinatorialRigidity.lean` after the split.

### Import graph (project files, post-Phase-8 — pre-PebbleGame split)

```
EdgesIn  ──►  Sparsity  ──┬──►  Framework  ──┬──►  TrivialMotions  ──►  RigidityMatroid  ──┐
                          │                   │                                              │
                          │                   └──►  HennebergRigidity  ◄── Henneberg  ◄──┐  │
                          │                                                              │  │
                          ├──►  Laman  ──►  Henneberg                                    │  │
                          │                                                              │  │
                          └──►  CountMatroid  ──►  MatroidIdentification ◄──┴──┴──┴──────┘  │
                                                          │                                  │
                                                          └──►  LinearRigidityMatroid       │
                                                          
                          LamanTheorem  ◄──────────────────────────────────────────────────┘
```

(Linear-only project-internal arrows; transitive mathlib imports add
the analysis floor.) Each file's transitive downstream-importer set:

| File | LoC | Downstream importers (transitive) |
|---|---|---|
| `EdgesIn.lean` | 225 | 10 (all) |
| `Sparsity.lean` | 1620 | 10 (all) |
| `Framework.lean` | 376 | 6 |
| `Laman.lean` | 143 | 5 |
| `Henneberg.lean` | 647 | 4 |
| `TrivialMotions.lean` | 353 | 4 |
| `RigidityMatroid.lean` | 709 | 3 |
| `HennebergRigidity.lean` | 638 | 3 |
| `CountMatroid.lean` | 93 | 2 |
| `MatroidIdentification.lean` | 975 | 1 |
| `LamanTheorem.lean` | 199 | 0 (terminal) |
| `LinearRigidityMatroid.lean` | 232 | 0 (terminal) |

### Factors to weigh when ranking splits

A split is the right call when *any* of the following carries enough
weight; the audit is qualitative, not formula-driven.

1. **Downstream-consumer benefit.** A file with several downstream
   importers where a coherent block is consumed by only a subset:
   splitting carves the block off and saves transitive import surface
   for the other consumers. The highest-leverage axis when the
   consumer count is large and the analysis floor is heavy.
2. **File size against the ~1500-LoC mathlib soft cap.** Mathlib's
   per-file size convention treats ~1500 LoC as a soft cap, flagged
   at maintainer review rather than enforced by CI. Files materially
   over this threshold warrant a split on modularity grounds *even
   with a single downstream consumer*: the file is harder to
   navigate, search, and reason about as a unit; per-edit
   incremental rebuilds churn through unrelated halves; the
   blueprint chapter structure usually already suggests a cleaner
   subdivision.
3. **Incremental-rebuild speed during active development.** Even
   within a single-consumer transitive-import graph, splitting a
   large file lets the next agent iterate on one half without
   re-elaborating the other (and any of its downstream files). The
   benefit scales with file size and elaboration cost; for
   analysis-heavy or large algorithm files, per-edit savings can be
   substantial even when from-scratch wall-clock builds are flat.
   The 4-run A/B protocol above measures from-scratch builds — a
   perf-neutral A/B result does *not* falsify the rebuild-speed
   argument.
4. **Structural-clarity / blueprint-chapter mapping.** A file
   spanning multiple distinct blueprint chapters or subsystems is
   harder to navigate as one unit. Splits matching the blueprint
   structure (or `DESIGN.md`-documented boundaries) carry durable
   orientation value independent of build-time effects. Phase
   8-perf F1 + F2 (Sparsity / Henneberg) landed individually
   perf-neutral on from-scratch wall-clock but were retained on
   this axis — the forward / reverse boundary now lives at file
   scope, not just section-header level.

Costs to weigh against the benefits: split files multiply namespace
/ `variable` / `import` boilerplate (cf. F1's `SparsityIComponents`
gotcha — the new file needed its own `variable {V : Type*}`
redeclaration when `V` flowed in from the original file's section
variable); blueprint `\lean{...}` pins to moved declarations need
updating in the same commit (mechanical but not free); new files
need their own `module` markers + `@[expose]` discipline per
`CombinatorialRigidity/CLAUDE.md` *Module-system conversion*. Below
~700 LoC, single-file is usually cleaner unless there's a strong
downstream-import or blueprint-chapter argument.

### Mathlib subdirectory pattern

The mathlib idiom for a topic too large for one file is to convert
`Foo.lean` into a `Foo/` directory with files split inside, most
often in a `Defs.lean` / `Basic.lean` shape:

- `Foo/Defs.lean` — definitions, structures, basic typeclass
  instances. Other files in the subdirectory import from here.
- `Foo/Basic.lean` — the core API built on `Foo/Defs.lean`. The
  typical entry point downstream files import.
- `Foo/<subsystem>.lean` — specific subsystems
  (`Foo/Operations.lean`, `Foo/Lemmas.lean`,
  `Foo/Quotient.lean`, …), each importing `Foo/Basic.lean` (and
  any sibling subsystem files they need).

The original `Foo.lean` is usually deleted — downstream switches
from `import Foo` to `import Foo.Basic` (or to the specific
subsystem it needs). Keeping `Foo.lean` as a thin re-export hub
that just imports the new pieces is a less common pattern and is
not the mathlib default; the hub's per-file elaboration overhead
adds cost that downstream files don't otherwise pay.

Not every file warrants a separate `Defs.lean`: when most of the
content is a coherent API on top of a small definitional surface,
a single `Foo/Basic.lean` with the defs inlined is fine. Triggers
for the full `Defs.lean` + `Basic.lean` + … pattern: 3+ files
would emerge after the split; the `Defs.lean` boundary cleanly
isolates the definitional surface from the API; the file is large
enough (typically over the soft cap by a substantial margin) that
a single split into two flat files at the same level won't bring
both halves under it. For a single split that *does* bring both
halves under the cap, two flat files at the same directory level
(the project's `Sparsity.lean` / `SparsityIComponents.lean` pattern
from Phase 8-perf F1, or `Henneberg.lean` / `HennebergReverse.lean`
from F2) is simpler and is what the project's existing splits use.

### Split candidates ranked by leverage

1. **`Sparsity.lean` split (highest leverage).** Natural cut at line
   1267, splitting `Sparsity.lean` into:
   - **`SparsityBase`** (~1266 LoC): `IsSparse` / `IsTight` defs,
     monotonicity, global edge bound, low-degree-vertex, non-adjacent-
     pair-among-three-neighbors, `Iso` transport, the tight-subset
     lattice, matroidal-regime block closure, three-neighbor
     contradiction templates, per-pair tight-blocker (sparse form),
     flat-form Henneberg reverse decomposition.
   - **`SparsityIComponents`** (~354 LoC): matroidal-regime maximal
     I-blocks (`HasBlock`, `maxBlockSet`, `maxBlock`, `IsSparse.maxBlock_*`)
     and the augmentation lemma `IsSparse.exists_aug_of_lt_two_mul`.

   **The IComponents+Augmentation block has exactly one downstream
   consumer**, verified by a project-wide grep: `CountMatroid.lean`
   uses `IsSparse.exists_aug_of_lt_two_mul` once (line 77) for the
   matroidal-regime augmentation axiom. After the split:
   - `EdgesIn`, `Framework`, `Laman`, `Henneberg`, `HennebergRigidity`,
     `TrivialMotions`, `RigidityMatroid`, `LamanTheorem` (8 files)
     drop ~354 LoC of Phase-7 combinatorial machinery from their
     transitive import set.
   - `CountMatroid` (and downstream `MatroidIdentification`,
     `LinearRigidityMatroid`) imports both halves — same load as
     today.

   Expected savings: hard to predict without measurement. The 354 LoC
   moved are combinatorial / `Finset`-heavy (`maxBlock` is a
   `Finset.sup`-based construction), so per-file elaboration savings
   are modest. The TL;DR's "import loading is ~25–27 s of shared
   overhead" pertains mostly to the analysis floor, not the
   combinatorial subtree. Likely savings: 1–3 s per downstream file,
   well within the noise band; the structural-clarity gain (Phase-7
   matroid-side machinery sits in its own file, matching the chapter
   structure in `chapter/sparsity.tex` vs `chapter/count-matroid.tex`)
   may matter more than the wall-clock.

2. **`Henneberg.lean` split (medium leverage).** Natural cut at line
   444, splitting into:
   - **`HennebergForward`** (~400 LoC): adjacency unfolding, sparsity
     helpers, typeI/typeII move definitions, edge-set decomps, Laman
     preservation per move.
   - **`HennebergReverse`** (~200 LoC): iso constructors, flat-form
     Henneberg reverse decomposition (Phase 7 Commit 6), K₄-minus-edge
     example.

   `HennebergRigidity.lean` (which is large + analysis-heavy + reused
   by 3 downstream files) only needs the forward half. Splitting
   would shave ~200 LoC of Phase-3+7 reverse-decomp machinery off
   `HennebergRigidity`'s transitive import set (and indirectly its
   downstream files `MatroidIdentification`, `LinearRigidityMatroid`).
   But `MatroidIdentification` and `LamanTheorem` need both halves
   directly. Modest leverage.

3. **`MatroidIdentification.lean` split (low leverage).** Natural cut
   at line 776, splitting into:
   - **`MatroidIdentificationExtends`** (~745 LoC): typeI / typeII
     row-LI lift (extends lemmas).
   - **`MatroidIdentification`** (~200 LoC): `|E|`-induction,
     Lovász–Yemini iff, rigidity matroid instantiation.

   The only downstream importer is `LinearRigidityMatroid.lean`,
   which uses both halves. Splitting saves no transitive-import
   surface for downstream; the win is faster incremental rebuilds
   when iterating on the matroid-instantiation half without touching
   extends lemmas. Worth doing on style grounds, not perf.

4. **Skip: `RigidityMatroid.lean` (709 LoC), `HennebergRigidity.lean`
   (638 LoC).** Both have plausible internal cut lines (RigidityMatroid
   at L595 between rank/spanning machinery and Phase-6 easy-direction
   sparsity; HennebergRigidity at L273 between typeI and typeII
   rigidity preservation), but downstream files generally need both
   halves. Per-move file organization is cleaner but provides
   minimal transitive-import savings.

5. **`PebbleGame.lean` split (Phase 9-perf F2 audit + executed
   post-Phase-9-perf under revised framework).** The original
   2489-LoC file mapped cleanly onto 10+
   named sections — natural cut lines at L274 (Reverse) → L605
   (AddArc) → L821 (Reachability) → L1036 (TryReachPebble) → L1219
   (TryAddEdge) → L1472 (RunPebbleGame) → L1755 (Soundness) → L1863
   (Completeness) → L2390 (Correctness) → L2464 (Matroidal). The
   strongest pair of candidate splits is *Reachability + the four
   pebble-game invariants* (L821–L1014) carved out as a "core
   theory" file, or *Soundness + Completeness + Correctness*
   (L1755–L2453) carved out as a "correctness" file.

   **Single-downstream-consumer verification:** `PebbleGame.lean` is
   imported only by `CombinatorialRigidity.lean` (the top-level entry,
   `import`-statements only). Verified by `grep -rn "import.*PebbleGame"`
   over the project tree — exactly one hit. Splitting therefore saves
   **zero transitive-import surface** for any consumer; the only
   benefit is per-incremental-rebuild speed when iterating on one
   half without touching the other.

   **Recommendation under the original F2 framework: keep as a
   single file.** The Phase 9-perf F2 framework weighed only the
   downstream-import axis: splits without transitive-import savings
   fell into the "structural-clarity gain, perf-neutral" bucket, and
   the per-decl `@[expose]` audit (F1.2, above) was the cheaper
   lever for the same per-rebuild outcome (3 per-decl opt-ins
   demoted the section, narrowing exposure to just the three
   `PartialOrientation`-producing defs).

   **Executed under the revised framework (*Factors to weigh*
   above): three-way split into `PebbleGame/` subdirectory.** Three
   of the four framework factors recommended split: file size (2489
   LoC ≈ 66 % over the ~1500-LoC soft cap, factor 2); incremental-
   rebuild speed on the large analysis-heavy algorithm file (factor
   3); structural-clarity / blueprint-chapter mapping
   (`chapter/pebble-game.tex`'s 10+ named sections, factor 4). Only
   the downstream-import axis (factor 1) was perf-neutral.

   The split followed the *Mathlib subdirectory pattern* above:
   `PebbleGame.lean` → `PebbleGame/` directory with three files at
   the same level:

   | File | LoC | Contents |
   |---|---|---|
   | `PebbleGame/Basic.lean` | 1024 | `PartialOrientation` struct, `empty` / `reverse` / `addArc` operations + accounting lemmas, `Reachable k ℓ` inductive + four pebble-game invariants |
   | `PebbleGame/Algorithm.lean` | 771 | `TryReachPebble` + `TryAddEdge` + `RunPebbleGame` three-layer chain (computable workhorses + noncomputable math-layer wrappers) |
   | `PebbleGame/Correctness.lean` | 815 | Soundness + Completeness + Correctness iff + matroidal-independence corollary |

   All three files sit comfortably under the soft cap. Import
   chain: `Basic` ← `Algorithm` ← `Correctness`; top-level
   `CombinatorialRigidity.lean` imports `PebbleGame.Correctness`
   transitively. No `Defs.lean` carve-out — `PartialOrientation`'s
   definitional surface is tightly interleaved with the API and
   wouldn't split cleanly.

   **Section-marker disposition.** All three files use
   `@[expose] public section` (matching `Framework.lean`'s F3.5
   disposition, not the F1.2 narrowed `public section`-with-opt-ins
   shape the pre-split single file carried). The cascading
   exposure surface — once one downstream consumer needs body
   defeq, every transitively-referenced helper does — pointed at
   the file-wide marker as the cleaner equivalent. Trying the
   demote-and-restore pattern from F3.5 forced ≥ 9 per-decl
   opt-ins across Basic alone (`out`, `peb`, `span`, `outOn`,
   `pebOn`, `underline`, plus reverse/addArc/empty already in
   F1.2) and would have continued cascading into
   `TryReachPebbleResult.newOrient`, `tryAddEdgeWith`, `tryAddEdge`,
   `runPebbleGameWith`, `runPebbleGame` in Algorithm and likely
   more in Correctness. The file-wide `@[expose] public section`
   collapses that disposition table to a single per-file line; the
   future per-decl narrowing audit (if it lands) can re-explore.

   **Import surface narrowed per file.** Basic imports
   `Mathlib.Algebra.BigOperators.Group.Finset.{Basic, Order.Group.Finset}`,
   `Mathlib.Data.Finset.Basic`, `Mathlib.Data.Sym.Sym2`,
   `CombinatorialRigidity.Search.DFS`; Algorithm imports
   `Mathlib.Combinatorics.SimpleGraph.Finite` + Basic; Correctness
   imports `CombinatorialRigidity.{Sparsity, CountMatroid}` +
   Algorithm. The pre-split file pulled all of these into one
   import set; the split lets Basic and Algorithm skip
   `Sparsity` / `CountMatroid` (the heavier `SimpleGraph` /
   `(k, ℓ)`-count chain).

### Module-system conversion: now ripe

Mathlib `v4.30.0-rc2` (the project's current pin) is essentially
fully converted:

- Total `Mathlib/**/*.lean`: 8053 files. Files with `module` marker:
  7943 (~98.6 %).
- `Mathlib/Analysis`: 791 files, ~766 with `module` (~97 %).
- `Mathlib/Analysis/InnerProductSpace`: 52 files, **100 %** with
  `module`.
- `Mathlib/Combinatorics/SimpleGraph`: 73 files, 72 with `module`
  (~99 %).

This is a step-change from the earlier *Module system* assessment
("multi-file refactor, all transitive imports first"). Today the
upstream transitive-imports-first problem is solved by mathlib's own
conversion campaign — our 12 project files are the entire remaining
scope. Conversion is plausibly a one-session refactor:

1. Convert `Mathlib/` mirror files first (10 files; all import
   already-converted upstream mathlib).
2. Convert project files in topo order from `EdgesIn` outward.
3. Each file gets `module` + `public import` lines + an
   `@[expose] public section` marker per `Mathlib/Analysis/InnerProductSpace/PiL2.lean`.
4. Measure pre/post via 4-run A/B on the analysis-heavy targets
   (`HennebergRigidity.lean`, `RigidityMatroid.lean`,
   `LinearRigidityMatroid.lean`).

Recommendation: pick up as a dedicated perf pass alongside the
`Sparsity.lean` split, since both touch the import graph and a single
A/B campaign can measure their combined effect.

### Granular `@[expose]` / `public` audit per file

**Status (F3.5):** closed. Technical-debt half discharged in F3.4
(F3.4 disposition entries below); perf-lever half discharged in F3.5
(F3.5 disposition table below). All 12 module-converted project
files that started F3.3 at `@[expose] public section` were audited:
11 demoted to `public section`, 1 (`Framework.lean`) retained per
the F3.4 disposition. Per-decl `@[expose]` opt-ins were added on
exactly the 12 defs whose bodies are genuinely consumed (downstream
or intra-module via `rfl`-proved `@[simp]` lemmas, pattern-match
defeq, or `unfold` / projection-style destructure).

**Status (Phase 9-perf F1):** closed. Phase 9's two new files
(`Search/DFS.lean`, `PebbleGame.lean`) shipped at the coarsest
exposure level (`@[expose] public section`) matching the Phase
8-perf F3.3 post-state; the F1 audit ran the same demote-and-restore
pattern as F3.5 on the two files. Both demoted to `public section`;
5 + 3 per-decl `@[expose]` opt-ins added (rows appended to the
F3.5 table below). 4-run A/B post-pass (Phase9-perf F4.2 vs F4.1
baseline): all three measured targets within the ±5 s noise band —
**F1 perf-neutral**. The audit's value is bookkeeping (the
disposition rows extend the F3.5 reference for future
module-system audits), not a build-time win — matching the F3.5
pattern after Phase 8-perf's headline win was already booked in
F3.2–F3.4 (file conversion + private-cleanup), not F3.5 (per-decl
narrowing). See `Phase9-perf.md` §F4.1/§F4.2 for the raw timings.

**Status (Phase 10+11-perf F1 + F2):** closed. The Phase 10 split
of `PebbleGame.lean` into the `PebbleGame/` subdirectory (Phase
9-perf's *Split candidates ranked by leverage* item 5
*Section-marker disposition*) re-shipped the file-wide
`@[expose] public section` on `PebbleGame/{Basic, Algorithm,
Correctness}.lean` and added two more — `Exec.lean` and
`Examples.lean` — at the same coarse setting, pending the per-decl
narrowing audit deferred to this pass. F1.1–F1.4 audited the four
files Phase 10/11 introduced or reshaped at file-wide
`@[expose] public section` (Algorithm, Correctness, Exec, Examples);
F2.1 + F2.2 re-audited `Search/DFS.lean` and `PebbleGame/Basic.lean`
under the Phase 11 reshape (DFS gained `reachClosureComputable` +
correctness as Layer 1 forward-work; Basic absorbed the
reach-closure-on-orientations API plus added `WorkhorseWitness`
in Layer 2). All six files demoted to `public section`; net per-decl
opt-in counts: Algorithm 1, Correctness 1, Exec 0, Examples 3,
DFS 5 (unchanged from Phase 9-perf F1.1), Basic 9 (the post-split
file-wide marker narrowed to the predicted 9-opt-in cascade from
item 5's *Section-marker disposition* prediction, plus zero new
opt-ins on the Phase 11 Layer 1 + Layer 3 absorbed reach-closure
machinery or the Layer 2 `WorkhorseWitness` structure). All six
previously-file-wide files in the Phase 10+11 surface now sit at
`public section` with per-decl opt-ins documented in the F3.5
table rows added during F1.1–F1.4 + F2.1 + F2.2. 4-run A/B
post-pass (Phase 10+11-perf F4.2 vs F4.1 baseline): five of six
per-target medians within the ±5 s noise band; the Algorithm
outlier at Δ +6.50 s sits just past the band but the audit is
pure section-marker bookkeeping (no algorithmic change) and is
most plausibly OS-level drift between sessions (PERFORMANCE.md
*Timing reproducibility* documents 10–50 s spreads on the same
source); project-total median 7.27 s sits well under the Phase
9-perf F4.2 anchor (10.04 s) — **F1 + F2 perf-neutral within
run-to-run variance**. The audit's value is bookkeeping (the
disposition rows extend the F3.5 reference for future
module-system audits), not a build-time win — matching the F3.5 /
Phase 9-perf F1 precedent. See `Phase11-perf.md` §F4.1/§F4.2 for
the raw timings. `LinearRigidityMatroid.lean` remains the only
non-`module` project file: Phase 10+11-perf F3.1 re-checked
`.lake/packages/Matroid/Matroid/Representation/Map.lean` at pass
execution time and found it still on plain `import` (not `public
import`); F3.2 conversion is deferred to the next
`apnelson1/Matroid` dep-bump cycle per the standing recommendation.

The Phase 8-perf module-system conversion (F3.3) applied a uniform
`@[expose] public section` to all 9 + 13 project files, matching the
upstream `Mathlib/Analysis/InnerProductSpace/PiL2.lean` reference.
Per the Lean reference manual (*Modules and Visibility*, *Exposed
and Unexposed Definitions*), this is the **coarsest** of the three
visibility levels:

| Section style | What's exposed |
|---|---|
| `private` (no `public`) | nothing; private scope only |
| `public section` | constant *names* and *types*; **bodies stay private** (downstream can't unfold) |
| `@[expose] public section` | names, types, **and bodies** — downstream can `simp [name]`, `rfl` across, defeq-rely |

The blanket `@[expose] public section` exposes every `def` body in
every file, which defeats most of the module system's build-time and
API-evolution benefits — exposed bodies in module M force M's
importers to track M's elaboration state, not just its public
signature.

**Audit work (multi-session):**

1. For each project file's exposed `def`s / `instance`s, identify
   the downstream call-sites that genuinely require the body
   (signals: `simp [defName]`, `unfold defName`, `change <unfolded>`,
   `rfl` across the def, defeq-dependent elaboration, `@[fun_prop]`-
   like tactic resolution).
2. Demote files (or specific decls) that don't need exposure from
   `@[expose] public section` to `public section`, or from
   section-level to per-decl `@[expose] public def`.
3. Run a 4-run A/B per the protocol in *A/B measurement protocol*
   on the analysis-heavy targets (`HennebergRigidity.lean`,
   `RigidityMatroid.lean`, `LinearRigidityMatroid.lean`,
   `MatroidIdentification.lean`).

Realistic per-file expectations: predicates / structures (`IsSparse`,
`IsLaman`, `IsTight`, `IsInfinitesimallyRigid`) are usually consumed
opaquely via API lemmas — they're strong candidates to drop
`@[expose]`. Data definitions used by `simp` or `rfl` downstream
(`RigidityMap`, `edgeSetMatrix`, the Henneberg `typeI`/`typeII`
constructors) are weak candidates — exposed bodies are part of their
contract.

**F3.4 elimination disposition (resolved):**

- `Framework.lean` (4 sites): path (b) — `edgeRow`, `edgeRow_symm`,
  `continuous_rigidityMap_apply` were promoted from `private` to
  non-`private`. Path (a) was attempted first (demote
  `@[expose] public section` → `public section`) and failed: the
  `convert ... using 1` at `MatroidIdentification.lean` line 927
  closes via a defeq through `Sym2.lift ⟨edgeRow p, edgeRow_symm p⟩`
  in `RigidityMap`'s body, so `RigidityMap`'s body must stay
  exposed. With `@[expose] public section` retained,
  `RigidityMap`'s exposed body cannot reference `private` helpers —
  so the helpers had to lose `private`. `continuous_rigidityMap_apply`
  is `@[fun_prop]`-tagged and resolved by name across modules; the
  attribute-tagged-helper convention (mathlib's preference) is to
  ship it as non-`private` rather than via opt-in.
- `HennebergReverse.lean` (3 sites): path (a) — file demoted to
  `public section`. The iso constructors (`typeI_iso_of_two_neighbors`
  / `typeII_iso_of_three_neighbors`) and their internal helper
  `isoOfOptionSubtypeNe` are consumed downstream only as values
  (called for the iso, no body unfolding), so the demotion is
  net-zero for downstream and the `private` opt-ins drop out.

**F3.5 audit disposition (resolved):**

Per-file outcome of the broader audit. "Demoted" = section style
changed from `@[expose] public section` to `public section`. "Per-
decl `@[expose]`" lists the defs that required body-level exposure
after demotion. Trigger column records the error that surfaced when
the file was demoted without per-decl rescue (build error site +
shape), informing the per-decl picks.

| File | Section | Per-decl `@[expose]` | Trigger when demoted |
|---|---|---|---|
| `EdgesIn.lean` | demoted | `edgesIn` | `Sparsity.lean` destructures `G.edgesIn s x` as a Prop / `unfold edgesIn` |
| `Sparsity.lean` | demoted | `IsSparse`, `IsTight`, `IsTightOn` | `Laman.lean` `h.1`/`h.2` on `IsTight`; intra-file `Iff.rfl` of `IsLaman` ↔ unfolded `IsTight`; `SparsityIComponents` `unfold IsTightOn at ...` |
| `SparsityIComponents.lean` | demoted | (none) | downstream `CountMatroid` consumes only `IsSparse.exists_aug_of_lt_two_mul` (lemma, not def); intra-file `unfold maxBlock` works (intra-module name binding, not defeq) |
| `Laman.lean` | demoted | `IsLaman` | `top_fin_two_isLaman` proof's `refine ⟨_, _⟩` destructures `IsLaman` body; downstream `Henneberg` etc. similar |
| `Henneberg.lean` | demoted | `typeI`, `typeII` | intra-file `instDecidableTypeIAdj` / `instDecidableTypeIIAdj`'s `match`-arm defeq; Lean's error explicitly lists *"definitions were not unfolded because their definition is not exposed: typeI ↦ 10"* |
| `HennebergReverse.lean` | demoted (F3.4) | (none) | F3.4 already verified opaque consumption downstream |
| `Framework.lean` | retained | (file-wide) | F3.4 disposition; per-decl narrowing would still leave `RigidityMap` + `continuous_rigidityMap_apply` exposed, so file-wide marker is cleaner |
| `TrivialMotions.lean` | demoted | `translationMotion`, `infinitesimalRotation`, `trivialMotionFamily` | intra-file `@[simp] ... := rfl` lemmas (`translationMotion_apply`, `infinitesimalRotation_apply`, `trivialMotionFamily_inl/inr`) fail simp-NF check with *"Not a definitional equality"* — proof is `rfl` which needs body |
| `CountMatroid.lean` | demoted | `countMatroid` | intra-file `@[simp] countMatroid_E ... := rfl` |
| `HennebergRigidity.lean` | demoted | (none; no defs) | file ships only theorems / lemmas; clean demotion |
| `RigidityMatroid.lean` | demoted | `rigidityRow` | intra-file `@[simp] rigidityRow_apply ... := rfl` |
| `MatroidIdentification.lean` | demoted | (none) | the only def `SimpleGraph.rigidityMatroid` is consumed by `LinearRigidityMatroid` (non-`module`) — non-module files don't see the new opacity model, so no need to expose |
| `LamanTheorem.lean` | demoted | (none; no defs) | terminal file, theorems only; clean demotion |
| `Search/DFS.lean` (Phase 9-perf F1.1) | demoted | `DirectedWalk.{length, vertices, IsPath, arcsFinset, reversedArcsFinset}` | downstream `PebbleGame.lean` uses `simp [DirectedWalk.length]` / `rw [DirectedWalk.IsPath, DirectedWalk.vertices, …]` (the `head_ne_tail_of_pos` case-split); intra-file `@[simp] arcsFinset_{nil,cons} … := rfl` + `@[simp] reversedArcsFinset_{nil,cons} … := rfl` |
| `PebbleGame.lean` (Phase 9-perf F1.2) | demoted | `PartialOrientation.{empty, reverse, addArc}` | intra-file `@[simp] arcs_empty / arcs_reverse / arcs_addArc … := rfl` projection lemmas — same `@[simp] := rfl` taxonomy as `TrivialMotions` / `CountMatroid` / `RigidityMatroid` in F3.5 |
| `PebbleGame/Algorithm.lean` (Phase 11-perf F1.1) | demoted | `runPebbleGameWith` | downstream `Correctness.lean` uses `rw [runPebbleGameWith] at h` (×2) inside `runPebbleGameWith_witness_bridges`'s edge-list induction (nil + cons preambles) — `rw [defname]` as unfold needs the body. The other 4 defs (`tryReachPebbleWith`, `tryReachPebble`, `tryAddEdgeWith`, `tryAddEdge`, `runPebbleGame.aux`) demote cleanly; downstream consumes them through `match` on the `Sum`-shaped return or through API lemmas, not by name-as-unfold |
| `PebbleGame/Correctness.lean` (Phase 11-perf F1.2) | demoted | `PebbleGameResult.isAccept` | downstream `Exec.lean` uses `simp [..., PebbleGameResult.isAccept, ...]` (line 319, inside `runPebbleGameExec_aux_isAccept`'s `cases s <;> simp [...]` proof) — same `@[simp] def` taxonomy as `TrivialMotions` / `CountMatroid` / `RigidityMatroid` in F3.5 + `PartialOrientation.{empty,reverse,addArc}` in F1.2 of Phase 9-perf. The two large defs (`runPebbleGame.aux`, `runPebbleGame`) demote cleanly even though their intra-file proofs use `simp [runPebbleGame.aux, ...]` (L820) and `unfold runPebbleGame` (L838) — intra-module `simp [defname]` / `unfold defname` works under `public section`; only downstream `simp [defname]` and intra-module `@[simp] := rfl` projection lemmas force exposure |
| `PebbleGame/Exec.lean` (Phase 11-perf F1.3) | demoted | (none) | clean demotion. All four defs (`outListSorted`, `edgeListSorted`, `runPebbleGameExec.aux`, `runPebbleGameExec`) and the three `Decidable` instances demote cleanly. The intra-file consumers use `rw [outListSorted, …]` (`mem_outListSorted`), `simp only [edgeListSorted, …]` / `unfold edgeListSorted` (`mem_edgeListSorted` / `edgeListSorted_pairwise`), `simp [runPebbleGameExec.aux, …]` (`runPebbleGameExec_aux_isAccept`), and `unfold runPebbleGameExec` (`runPebbleGameExec_isAccept_iff`) — all intra-module `rw`/`simp [defname]`/`unfold defname` patterns, which work under `public section`. The three `Decidable` instances route through `decidable_of_iff` (passes `runPebbleGameExec` as a value to consume `.isAccept` via the proved iff, no body-unfolding required); the matroidal-regime `Fact (3 < 2 * 2)` plug-in and `inferInstanceAs` chain also don't need body exposure. Downstream `Examples.lean` (`#eval (decide G.IsLaman)` etc.) and `Main.lean` (CLI) reduce via the compiled body without needing `@[expose]` at the source level. Matches the F3.5 `MatroidIdentification.lean` / `LamanTheorem.lean` pattern: theorem-and-instance file with API-only intra-file def consumption demotes with zero per-decl opt-ins |
| `PebbleGame/Examples.lean` (Phase 11-perf F1.4) | demoted | `k4MinusE`, `moserSpindle`, `path5` | intra-file `instance : DecidableRel <graph>.Adj` consumers use `decidable_of_iff … SimpleGraph.deleteEdges_adj.symm` / `(SimpleGraph.fromEdgeSet_adj _).symm` to bridge from a body-mentioning iff (e.g. `(⊤ : SimpleGraph (Fin 4)).Adj a b ∧ s(a, b) ∉ {s(2, 3)}` for `k4MinusE`) to the def-level `<graph>.Adj a b`; the bridge needs the graph def's body. Without `@[expose]`, Lean reports *"Application type mismatch … `SimpleGraph.deleteEdges_adj.symm` has type … but is expected to have type … `↔ k4MinusE.Adj a b`"* (resp. `moserSpindle.Adj` / `path5.Adj`) and the dependent `#eval (decide …)` lines abort with the sorry-axiom guard. `k4` does **not** need the opt-in: its instance uses `inferInstanceAs (DecidableRel (⊤ : SimpleGraph (Fin 4)).Adj)`, which routes directly through the existing `(⊤ : _).Adj` `Decidable` instance with no body unfolding. The `Finset (Sym2 _)` helper defs (`moserEdges`, `path5Edges`) also demote cleanly — they're consumed only by name inside the graph defs' bodies (which are now `@[expose]`), not by the iff-bridge instances directly. Pre-pass note expected zero opt-ins ("trivial — no `def`s, only `#eval` commands"); audit invalidated that expectation because the four worked examples carry their own `def`-bound graphs with body-dependent `DecidableRel` instances. Pattern matches `Henneberg.lean`'s F3.5 row (intra-file `instDecidableTypeIAdj` / `instDecidableTypeIIAdj` triggered `@[expose]` on `typeI` / `typeII`): a `DecidableRel _.Adj` instance built via `decidable_of_iff` against a body-mentioning bridge iff forces `@[expose]` on the graph def |
| `Search/DFS.lean` (Phase 11-perf F2.1 re-audit) | demoted (unchanged) | `DirectedWalk.{length, vertices, IsPath, arcsFinset, reversedArcsFinset}` (unchanged from Phase 9-perf F1.1) | re-audit under Phase 11 Layer 1's ~110-LoC extension (`reachClosureComputable` + soundness/completeness + `DirectedWalk.toReflTransGen` bridge). The five Phase 9-perf F1.1 opt-ins are all still required at the same trigger sites: `length` via `simp [DirectedWalk.length]` at `PebbleGame/Basic.lean:401`; `vertices` + `IsPath` via `rw [DirectedWalk.IsPath, DirectedWalk.vertices, …]` at `Basic.lean:403` (inside `head_ne_tail_of_pos`); `arcsFinset` + `reversedArcsFinset` via intra-file `@[simp] {arcs,reversedArcs}Finset_{nil,cons} … := rfl`. The Layer 1 addition `reachClosureComputable` does **not** need `@[expose]` — its only consumers are (i) intra-file `rw [reachClosureComputable, Finset.mem_filter] at hw` (×2) inside `reachClosureComputable_sound` / `reachClosureComputable_complete` (intra-module `rw [defname]`-as-unfold works under `public section`; only downstream `rw [defname]` and intra-module `@[simp] := rfl` projection lemmas force exposure — matches the F1.2 disposition of `runPebbleGame.aux` / `runPebbleGame` in `Correctness.lean`), and (ii) downstream `PebbleGame/{Basic,Algorithm}.lean` via the `mem_reachClosureComputable` iff (rw'd through to `Relation.ReflTransGen`), `self_mem_reachClosureComputable`, and `reachClosureComputable_closed` — API-only consumption, no body-unfolding. The Layer 1 helper `DirectedWalk.toReflTransGen` and the membership lemmas `mem_reachClosureComputable` / `self_mem_reachClosureComputable` / `reachClosureComputable_closed` are theorems / lemmas (not `def`s), so they're unaffected by the `@[expose]` axis. Net delta from Phase 9-perf F1.1: zero opt-ins added, zero removed (the Phase 11 Layer 1 pre-pass `@[expose]` on `reachClosureComputable` was load-bearing-free and is dropped). Pattern matches `PebbleGame/Exec.lean`'s F1.3 disposition: a Phase 11-reshape / Phase 11-Layer-1 forward-work file with API-only intra-file def consumption can demote cleanly without adding new opt-ins |
| `PebbleGame/Basic.lean` (Phase 11-perf F2.2 audit) | demoted | `PartialOrientation.{empty, out, peb, spanArcs, span, pebOn, underline, reverse, addArc}` | post-Phase-10-split file-wide `@[expose] public section` (item 5 *Section-marker disposition*) narrowed to nine per-decl opt-ins. The pre-pass note citing "3 existing Phase 9-perf F1.2 opt-ins on `empty` / `reverse` / `addArc`" was a stale reference to the pre-split shape; item 5 collapsed the F1.2 narrowed shape to a file-wide marker pending a future per-decl audit (this F2.2). Triggers materialise almost exactly per item 5's prediction: `empty` / `reverse` / `addArc` via intra-file `@[simp] arcs_{empty,reverse,addArc} … := rfl` projections (same `@[simp] := rfl` taxonomy the pre-split F1.2 closed at); `out` / `peb` via downstream `Algorithm.lean` `:= rfl`-proved bridge haves `D.peb k _ = k - D.out _` (L171 inside `Reachable.reachable_newOrient_apply`, L490 / L500 inside `tryAddEdgeWith_correct`'s case1 / case2 — the *"definitions were not unfolded: out ↦ 2, peb ↦ 9"* note signals both at the same site); `pebOn` via downstream `rw [pebOn]` at Algorithm L400 (inside `tryAddEdgeWith`'s case5 witness-construction `h_split` proof); `spanArcs` / `span` / `underline` via downstream `Correctness.lean` `simp only [..., spanArcs, ...]` (L123 / L138 inside `image_spanArcs_eq_edgesIn`, L254 / L265 inside `sym2_mk_injOn_arcs`) / `rw [underline, ...]` (L135 inside `image_spanArcs_eq_edgesIn`'s `⊇`-inclusion) / `rw [span, ...]` (L152 inside `span_eq_ncard_edgesIn`, L274 inside `runPebbleGameWith_span_le`). `outOn` was on the pre-pass candidate list but does **not** need exposure: all its consumers route through API lemmas (`outOn_eq_zero_of_closed`, `outOn_reach_union_eq_zero`, `pebOn_add_span_add_outOn`), not by name-as-unfold; the pre-pass list was off-by-one. The Phase 11 Layer 1 / Layer 3 absorbed reach-closure machinery (`reach`, `mem_reach`, `self_mem_reach`, `reach_closed`, `outOn_eq_zero_of_closed`, `outOn_reach_union_eq_zero`) and the Layer 2 `WorkhorseWitness` structure both need **zero** new opt-ins: `reach` is consumed downstream as a value via the `mem_reach` iff against `Relation.ReflTransGen` and the closure lemmas (API-only); `WorkhorseWitness` is a structure (auto-exposed constructors / projections), and downstream Correctness consumes its fields by projection, not by body unfolding. Other Basic defs (`outNbhd`, `outList`, `boundaryArcs`, `outOn`, `reach`) demote cleanly. The audit narrows exposure from "every named def" (13 named `def`s plus 3 structures / inductives at file-wide `@[expose] public section`) to the 9 listed. Pattern matches the F1.1–F1.4 + F2.1 taxonomy: `@[simp] := rfl` projections and downstream `rw`/`simp [defname]`-as-unfold consumers force exposure; API-only consumption demotes cleanly |

Lessons:

- **`public section` is opaque intra-module too.** The dominant
  per-decl trigger wasn't downstream consumption — it was *intra-file*
  use sites that need a `def`'s body for elaboration-time defeq (the
  `match`/`rfl` patterns above). In the new module system,
  `public section` (no `@[expose]`) is close to `@[irreducible]`
  semantics for the def's body: visible by name within the file, but
  the body is not unfolded for defeq during elaboration.
- **Prop predicates are not all alike.** `IsSparse` / `IsTight` /
  `IsTightOn` / `IsLaman` had to expose because downstream code
  destructures via projection (`h.1`, `h.2`) or unfolds via
  `refine ⟨_, _⟩` or `Iff.rfl`. `EdgeSetRowIndependent` (in
  `RigidityMatroid.lean`) and `HasBlock` (in `SparsityIComponents.lean`)
  did *not* need exposure because downstream consumers go through
  API lemmas (`.mono`, `mem_maxBlock`, etc.) rather than body access.
  The mathlib-style discipline of "use the API, not the body" is
  what makes the latter demote cleanly.
- **`@[simp] ... := rfl` always needs `@[expose]`.** Any intra-file
  `rfl`-proved `@[simp]` projection lemma over a `def` forces that
  `def` to be `@[expose]`-tagged (the `@[simp]` linter runs a
  defeq normalization on the LHS at registration time). This shows
  up as *"Not a definitional equality"* with the *"definitions were
  not unfolded"* note.

## Molecular `CaseI.lean` perf recon (2026-06-15, Phase 22j design-pass)

> **Plan (B) LANDED (2026-06-15).** The file split below was executed across four slices (P1–P4,
> `notes/Phase22j-perf.md`): the 10,346-line `CaseI.lean` monolith is now the 5-file chain
> `GenericityDevice ← Coupling ← CaseI ← CaseII ← CaseIII ← Theorem55` (Coupling 1,349 / CaseI 2,187 /
> CaseII 1,223 / CaseIII 3,861 / Theorem55 1,899 LoC). Rename-free; full build/lint/axioms/`checkdecls`
> clean. `CaseIII.lean` (~2.5× cap) remains a clean second-round sub-split candidate. Plan (C) — the
> `RigidityMatrix.lean` / `ForestSurgery.lean` candidates — is assessed, not scheduled.

A ranked split/refactor plan for the molecular `AlgebraicInduction/`
giants, opened by the Phase-22j suppression-drop cleanup (the
`maxHeartbeats 3200000` + `linter.style.longLine false` drops above
`PanelHingeFramework.case_II_realization_all_k` turned out to be
refactors, not mechanical drops — `notes/Phase22j.md`). The recon
profiled the L6b producer, mapped `CaseI.lean`'s structure and its
real intra-file / import-graph edges, and surveyed the other
raised-budget decls. **All claims below were verified against the
landed source** (decl bodies + import edges, not prior prose) on
2026-06-15.

The recommendation splits into **(A) within-Phase-22j now** (the two
sanctioned suppression refactors) and **(B) a follow-up perf round**
(the larger file split, for the coordinator to put to the user).

### Profile of the L6b producer `case_II_realization_all_k`

The producer is `CaseI.lean:3744–4660` (~917 lines), a single
`theorem` carrying `set_option maxHeartbeats 3200000 in` (16×
default) + `set_option linter.style.longLine false in` (the :3727
suppression, `in`-scoped to this decl only). It has **zero intra-file
consumers** (referenced only in its own docstring — it is a leaf
producer the dispatch consumes in a later phase). Its body is a clean
linear sequence of ~16 numbered `-- ── Step N ──` blocks, each a
self-contained `have`, building a long dependent chain of locals
(`v,a,b,e_a,e_b,e₀,Gab,Q,q,q₀,N,FG,FGab,so,sn,…`).

**Cost profile** (`set_option profiler true` over the decl, reverted
after measurement; cumulative block for the file, dominated by this
decl since it was the only profiler-on declaration):
- `typeclass inference` **21 s** (the top category) — of which
  `CoeT` coercion inference alone is **~7.7 s across just 20 logged
  ≥50 ms hits** (the ℤ/ℕ casts `↑N`, `↑(screwDim 2 · )`, `↑finrank`
  re-elaborated through the rank-arithmetic blocks; many sub-50 ms
  hits uncounted). The standing comment's "repeated `ScrewSpace 2`
  typeclass elaboration is expensive" is confirmed.
- `tactic execution` **19 s** (~26 `rewriteSeq` ≥50 ms = 4.5 s;
  several `linarith`; one `tauto` at 578 ms).
- `simp` **2 s**.

**The cost is diffuse, not one hot block** — spread across the ~16
Steps as repeated typeclass re-elaboration of the heavy
`ScrewSpace 2` / `Module.Dual ℝ (α → ScrewSpace 2)` / `finrank`
stacks. A `maxHeartbeats` bisection (each tested with a real build,
reverted) pins the actual requirement:

| budget | result | first timeout site |
|---|---|---|
| 200000 (default) | FAIL | `whnf`/`isDefEq`/tactic-exec (3 sites; per `notes/Phase22j.md`) |
| 400000 (2×) | FAIL | `isDefEq` at **:4473** (the `set ro := fun i => FGab.panelRow Q.ends …` in the Brick-A call site) |
| 600000 (3×) | FAIL | `whnf` at **:4522** (the `hrank_lb_nat` ℤ/ℕ rank-cast `linarith`) |
| **800000 (4×)** | **PASS, clean** | — |

So the budget can be lowered from 3.2M → **800000 (4× default)
immediately, with zero proof change** — a free first win. The two
budget-defining sites are exactly the two extractable clusters below.

### Producer helper-split design (the heartbeats refactor)

The diffuse-cost finding sets expectations: extracting helpers will
**not** be a from-scratch wall-clock win (cf. the `kerRestrict`
revert and the *Experiments that didn't pay* table — helper
extraction routinely sits in the noise band). Its value is **(i)
bringing the per-helper budget under or near the default so the
3.2M / 800k whole-decl suppression goes away**, and (ii)
edit-friction / incremental-rebuild. The two budget-defining sites
are the only cleanly-extractable clusters; the geometric middle is
**not** extractable (see *Flagged* below).

The two timeout sites are both **pure ℤ/ℕ rank-arithmetic + one
abstract-brick call**, depending on a *small* set of locals — unlike
the geometric middle, which transitively needs ~15–20 locals (the
S4b net-negative trap, `notes/Phase22j.md`). Concretely:

- **Helper 1 — the rank-arithmetic cast bridge.** The `hrank_lb_nat`
  block (:4497–4522) and the `hrankge_int` block inside `hrank_eq_q'`
  (:4634–4653) run the *same* `Nat.cast_sub` / `push_cast [Nat.cast_sub h1V]`
  / `Int.toNat_of_nonneg` / `linarith [hNpD]` pattern verbatim, to
  bridge `screwDim 2 * (V(G).ncard − 1) − k` between its ℤ form (from
  Brick A) and its ℕ-`toNat` form (for the rank-polynomial transfer).
  This is a self-contained scalar lemma over `screwDim 2`,
  `V(G).ncard`, `k`, `N` with hypotheses `hk : 0 < k`,
  `h1V : 1 ≤ V(G).ncard`, `hNpD : (N:ℤ) + (screwDim 2 − 1) = screwDim 2 * (↑V − 1) − k`.
  Proposed signature (target file: `RigidityMatrix.lean`, beside the
  Brick-A bricks, since it is rigidity-free scalar plumbing — or
  `Deficiency.lean` if it should sit with the `bodyBarDim`/`deficiency`
  arithmetic):

  ```lean
  theorem toNat_screwDim_mul_pred_sub_eq {D V N : ℕ} {k : ℤ}
      (hk : 0 < k) (hV : 1 ≤ V) (hD : 1 ≤ D)
      (hNpD : (N : ℤ) + (D - 1) = D * ((V : ℤ) - 1) - k) :
      D * (V - 1) - k.toNat = N + (D - 1)
  ```

  with a companion `…_le` for the `k.toNat ≤ D * (V − 1)` side fact.
  Both `hrank_lb_nat` and `hrankge_int` then become one `rw`/`linarith`
  each. This removes the :4522 (600k) timeout site and most of the
  `CoeT` cost (the casts are the dominant typeclass load).

- **Helper 2 — the Brick-A call-site shape.** The :4473 (400k)
  `isDefEq` timeout is the `set rn`/`set ro` over the
  `FG.panelRow ends` / `FGab.panelRow Q.ends` lambdas feeding
  `le_finrank_span_rigidityRows_of_pinned_placement` (already
  TACTICS-QUIRKS §38 *Abstract-brick call-site*). This is **already
  factored** — Brick A is the helper. The residual cost is the
  defeq of the two opaque `ofNormals` families at the call. The
  honest lever here is **not** a new helper but feeding the brick
  through the §38 `set rn`/`set ro` fvars with an *explicit* `hbrick`
  type (already done) — and, if still over budget, `letI`-pinning the
  `Fintype sn`/`Fintype so` instances and `clear`-ing unused heavy
  locals before the call to shrink the `isDefEq` search. **Flag:** if
  after Helper 1 lands the brick call still needs > default budget,
  this is a §38-class defeq blowup, not a missing lemma — keep a
  local `set_option maxHeartbeats` *on the brick-call `have`* (a
  small, documented, localized budget) rather than the whole-decl 3.2M.

**Expected outcome of the helper-split:** the whole-decl budget drops
from 3.2M to either the default 200000 (if Helper 1 removes enough
`CoeT` load that the brick call also fits) or a small documented
local budget on the brick-call `have` only. Either way the 16×
suppression is replaced by a justified, localized one.

**Flagged, not forced (mandate ii):** the geometric middle of the
producer — the Step 12–15 cluster (`hFG_ea`/`hFG_eb`/`hrow_b_eq`/
`hrow_a_eq`/`he₀_rows_mem`/`hso_span`, :4029–4322, ~230 lines) — is
**not** cleanly extractable. Its dependency surface (verified) spans
`FG`, `FGab`, `q₀`, `q`, `Q` (with `Q.ends`, `Q.normal`), `Gab`,
`e_a/e_b/e₀`, `n_a/n_b`, `v/a/b`, `ends`, plus ~15 derived
hypotheses — a ~15–20-arg helper, the exact S4b net-negative trap
(`notes/Phase22j.md`). Leave it inline. If the producer must shrink
further, the right move is the *file* split (B) carrying the whole
producer to its own file, not sub-lemma extraction of the middle.

### Long-line reflow (the `linter.style.longLine` refactor)

Drop `set_option linter.style.longLine false in` (:3727) — it
`in`-scopes to the producer only. **Must land AFTER the helper-split**
(the split changes line numbers/counts). In the producer body
(:3744–4660) there are **72 over-length (>100-char) lines = 49
comment/divider + 23 genuine code lines** (the note's "~80" was a
slight over-count). The 49 comment/divider lines reflow trivially
(rewrap text; shorten the `─` section dividers). The 23 code lines
all break at natural delimiters — `rw [a, b, c]` chains split after a
`,`; `have … := by` breaks before `by`; lambdas break at the binder;
one is a `--` comment. None require restructuring a proof. (The
*other* `linter.style.longLine false` at :2473, on
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof`,
is a separate decl and out of 22j scope.)

### (A) Within Phase 22j now — buildable slices

In order (each gate: `lake build` warning-clean + `lake lint` +
producer axiom-clean):

1. **A0 (free, optional pre-step):** drop the budget 3.2M → 800000
   with no other change. Confirms the bisection and shrinks the
   suppression 16× → 4× immediately. Payoff: removes the most
   alarming magic number; zero risk.
2. **A1 — land Helper 1** (`toNat_screwDim_mul_pred_sub_eq` + `…_le`)
   in `RigidityMatrix.lean` (or `Deficiency.lean`), rewrite
   `hrank_lb_nat` (:4497) and `hrankge_int` (:4634) to call it, add
   its blueprint node if a `\lean{}` pin is wanted (scalar plumbing —
   likely no node). Re-bisect the producer budget; lower the
   `set_option` to the smallest passing value (target: default
   200000, else a small documented local budget on the brick-call
   `have`). Payoff: removes the :4522 timeout site + most `CoeT`
   cost; the whole-decl suppression shrinks or disappears.
3. **A2 — longLine reflow** of the producer's 72 long lines (49
   comment/divider + 23 code), then drop the :3727 suppression.
   **After A1** (line numbers shift). Payoff: removes the second
   suppression; pure readability.
4. **A3 — `CLEANUP.md` §C-note refresh** (coordinator-authored) for
   the slimmed producer.

### (B) Follow-up perf round — the `CaseI.lean` file split

`CaseI.lean` at **10,346 lines is the prime split candidate** (6.9×
the ~1500-LoC soft cap; next-largest molecular file is
`Induction/ForestSurgery.lean` at 3783). It is mis-named: it carries
*all five* KT cases plus the dispatch, not just Case I. Verified
internal structure (single `namespace`, no `section` markers — split
by decl ranges):

| Block | lines | content |
|---|---|---|
| Coupling / `extProj` / projection foundations | ~73–1360 | shared-seed coupling, `extProj`, projection-into-pinned-motions bridges |
| Case I + rank-polynomial machinery | ~1361–3519 | `case_I_realization`, the `exists_rankPolynomial_*` suite |
| Case II | ~3520–4660 | `case_II_placement_eq612`, `case_II_realization_all_k` (the L6b producer) |
| Claim 6.11 + Case III | ~4662–8498 | the largest coherent block (~3.8k LoC): `case_III_*`, `caseIIICandidate` |
| Theorem 5.5 base producers + cut-edge + dispatch | ~8500–10346 | `theorem_55_base_producer_*`, `case_cut_edge_realization`, `case_I_realization_{nonsimple,all_k}`, `case_I_dispatch` |

**Verified intra-file dependency DAG (no cycle):** foundations →
Case I → Case II → Case III → base producers → cut-edge → dispatch.
The two edges that matter: the Case III block uses
`case_II_placement_eq612` (a Case II decl, earlier — forward edge);
the base-producer block's `theorem_55_d3` (:8930) uses
`case_III_realization` (:8453, earlier — forward edge). `theorem_55_base`
itself is **upstream** in `Pinning.lean`, not in CaseI, so it adds no
within-file edge. No backward edge from a lower block into a higher
one — a clean forward chain.

**Leverage (per *Factors to weigh when ranking splits*):**
- *Factor 1 (downstream-consumer benefit): nil.* Verified —
  `CaseI.lean` is imported only by the top-level
  `CombinatorialRigidity.lean` aggregator (the AlgebraicInduction
  subdir is a linear chain `PanelLayer ← Pinning ← PanelHinge ←
  GenericityDevice ← CaseI`, and CaseI is the terminal leaf). A split
  saves **zero transitive-import surface** — exactly the
  `PebbleGame.lean` situation (item 5), which split anyway on factors
  2/3/4.
- *Factors 2 + 3 + 4: very high.* 6.9× the soft cap; the active
  realization-layer file (per-edit incremental rebuilds churn through
  10k lines of unrelated cases); and the block boundaries map
  one-to-one onto KT's case structure / the
  `algebraic-induction.tex` + `case-iii.tex` chapter split. This is
  the strongest factor-2/3/4 case in the project's history.

**Proposed split (mathlib subdirectory pattern, no `Defs.lean` —
the definitional surface is thin and interleaved):** convert
`CaseI.lean` → keep the `AlgebraicInduction/` directory, replace the
one file with a linear chain matching the DAG. Indicative target
(the exact cut lines get re-derived at execution against the
then-current file, since A1/A2 shift them):

| New file | ~LoC | from block |
|---|---|---|
| `AlgebraicInduction/Coupling.lean` | ~1300 | foundations (coupling + `extProj`) |
| `AlgebraicInduction/CaseI.lean` | ~2150 | Case I + rank-polynomial suite |
| `AlgebraicInduction/CaseII.lean` | ~1150 | Case II (the L6b producer) |
| `AlgebraicInduction/CaseIII.lean` | ~3850 | Claim 6.11 + Case III (still ~2.5× cap — could sub-split later) |
| `AlgebraicInduction/Theorem55.lean` | ~1850 | base producers + cut-edge + dispatch |

Import chain `GenericityDevice ← Coupling ← CaseI ← CaseII ← CaseIII
← Theorem55`; top-level aggregator imports `…Theorem55` (drop the
`…CaseI` import line). **Cost/risk (low):** the split is a pure
semantics-preserving move — **no decl renamed**, so all 50 blueprint
`\lean{…}` pins into CaseI's decls (verified count) stay valid by
name and `checkdecls` is unaffected (the pre-Phase-22b structure pass
established exactly this). Each new file inherits non-`module` status
(the molecular chain is non-`module`, *Module system* above). The
boilerplate cost is the usual per-file `namespace` / `variable {k}` /
`open scoped Graph` / `variable {α β}` redeclaration (cf. the F1
`SparsityIComponents` `variable {V}` gotcha). The `CaseIII.lean`
piece stays over the cap; a second-round sub-split (e.g. carve the
Claim-6.11 + `caseIIICandidate` device off the `case_III_*`
producers) is a clean follow-up.

**Recommendation:** B is a high-leverage follow-up worth doing, but
it is a multi-slice structural-edit round of its own (5 new files,
the aggregator edit, per-file boilerplate, a full re-build), distinct
from the 22j cleanup. Surface to the user as the perf round to open
after 22j closes — not folded into 22j. Do A (the two sanctioned
suppression refactors) within 22j first; A0/A1 also de-risk B by
shrinking the producer's budget before it moves files.

### (C) Other molecular split candidates (ranked, for the same round)

Surveyed the other raised-budget decls and next-largest files:

1. **`Induction/ForestSurgery.lean` (3783 LoC) — medium.** 2.5× cap,
   no raised budgets. Next-biggest after CaseI; a file-size/navigability
   split (factor 2), but it is in the *stable* Induction subtree (not
   active), so factor-3 (incremental-rebuild) leverage is low. Defer
   to a dedicated round.
2. **`RigidityMatrix.lean` (3380 LoC, two `maxHeartbeats 400000` at
   :3009 + :3187) — medium.** 2.25× cap and it *is* imported
   downstream (it owns Brick A + the panel-row API the whole
   molecular chain consumes), so a split *could* carry factor-1
   benefit — worth a dedicated downstream-import analysis. The two
   400k budgets are candidates for the same profile-then-localize
   treatment as the L6b producer, independently of any split.
3. **`Deficiency.lean` (2295) / `AlgebraicInduction/PanelLayer.lean`
   (2027) / `GenericityDevice.lean` (1950) / `Pinning.lean` (1751) —
   low.** Each modestly over the cap; no raised budgets;
   single-consumer chain. Style-grounds splits only — not worth a
   round on their own.
4. **The three other CaseI budgets (:9142 400k, :9528 800k, :9896
   800k)** — in the cut-edge / Case-I-nonsimple producers
   (`case_cut_edge_realization{,_gp}`, `case_I_realization_nonsimple`).
   Same diffuse-`CoeT` shape as L6b is likely; each could get the
   profile-then-Helper-1-then-localize treatment in the B round once
   those producers land in `CaseII.lean` / `Theorem55.lean`. Lower
   priority than the L6b 3.2M (the largest, most alarming budget).

## `ScrewSpace` carrier opacity — see `notes/ScrewSpaceCarrier-design.md`

The post-22k investigation into the `maxHeartbeats` cost of the `ScrewSpace`
carrier (the reducible-`abbrev` → diffuse-typeclass-re-elaboration story), the
opacity spike (verdict MIXED: ~5–60× mechanism win, prohibitive full-refactor
blast radius), the mathlib precedents (`Polynomial`/`Real`), and the
design-recon-first refactor plan have their own canonical home:
**`notes/ScrewSpaceCarrier-design.md`**. **The d=3 part landed as Phase 22l** (closed
2026-06-16): `abbrev ScrewSpace`→opaque `def`, dropping the molecular `maxHeartbeats`
count 3→1 (two former caps to default, `case_cut_edge_realization_gp` 600000→400000).
The general-`d` "part 2" is deferred to the Phase-23 design boundary. Dispatch records:
`notes/model-experiment.md` rows 167–170.

## Recommendations for future perf work

1. **Don't trust a single A/B run.** Run ≥ 4 trials per side and compare
   medians. If the medians are within ~5 s, declare neutral.
2. **Try the structural lever before micro-optimizing.** The
   project's three structural axes are: (a) **file splits**, driven
   primarily by the file-size / modularity / incremental-rebuild
   factors above — see *Factors to weigh when ranking splits* and
   *Mathlib subdirectory pattern* for the framework, *Split
   candidates ranked by leverage* for the current dispositions
   (the largest single-file open candidate, `PebbleGame.lean` at
   2489 LoC, landed as a three-way subdirectory split
   post-Phase-9-perf — item 5; `Sparsity.lean` at 1277 LoC is the
   next-biggest under the cap and not currently a split target);
   (b) **module-system conversion**, landed in Phase 8-perf
   F3.2–F3.5 with `LinearRigidityMatroid.lean` carved out until
   upstream `apnelson1/Matroid`'s `Map.lean` converts (re-check on
   next dep-bump); (c) **per-decl `@[expose]` narrowing**, landed
   in Phase 8-perf F3.5 + Phase 9-perf F1 across the original 16
   module-converted files (PebbleGame's three split files sit at
   file-wide `@[expose] public section` per item 5's
   disposition). Micro-optimizations (tactic swaps, helper
   extraction, simp-set narrowing) routinely sat in the ±5 s
   noise band (*Experiments that didn't pay*); the structural
   axes are where every project-scale wall-clock win has come
   from.
3. **The profiler is most useful as a sanity check, not a guide.** Use it
   to spot a single declaration taking > 100 ms or a `simp` ballooning, but
   don't expect the cumulative numbers to predict wall-clock movement.
4. **If you change a tactic, also delete its old-style scaffold.** A
   `simp only [...]` after a `change` that's now redundant; an unused
   `with hp_ext_def`; a `have h := h_orig` shadow. Small cosmetics, but
   they're the only things that *consistently* don't slow the build down.

## See also

- `notes/FRICTION.md` *[wontfix] `lake build` of Phase 5 files is
  import-floor-bound and timing-noisy* — short summary entry that points
  back to this file.
- `notes/Phase5.md` *Cleanup pass summaries* — the per-pass log of what
  shipped and what didn't.
- `TACTICS-GOLF.md` § 6 *`fun_prop` for continuity / differentiability* — the
  project's convention for continuity goals (don't unroll into explicit
  `Continuous.*` chains for perf reasons).
