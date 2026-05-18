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
| Per-decl `@[expose]` audit (Phase 9-perf F1) | `Search/DFS.lean`, `PebbleGame.lean` — demote `@[expose] public section` → `public section`, restore `@[expose]` on 5 + 3 defs whose bodies are genuinely consumed (`@[simp] := rfl` projections; `simp [name]` / `rw [name]`-as-unfold call sites) | All three measured targets within ±5 s noise band: DFS 8.13 → 8.70 s (Δ +0.57); PebbleGame 14.43 → ~15.4 s (Δ +~1.0); project-total 8.97 → 10.04 s (Δ +1.07). **Kept** — the bookkeeping value (rows in the F3.5 audit-disposition table) is the deliverable, matching the F3.5 pattern itself: the headline win was in F3.2–F3.4 (module-system conversion + private-cleanup), not F3.5 / F1 (per-decl narrowing). See `Phase9-perf.md` §F4.1/§F4.2. |

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
