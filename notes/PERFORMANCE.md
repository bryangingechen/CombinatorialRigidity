# Build performance notes

A long-running log of build-time observations and profiling findings for
this project. Read this **before** you run a performance pass — most of the
"obvious" optimization ideas have been tried, and several were reverted as
either neutral or actively worse under measurement noise. The point of this
file is to save the next agent from re-litigating the same dead ends.

> **Scope.** This is project-specific. Cross-cutting tactical idioms live
> in `TACTICS.md`; one-off API gaps live in `notes/FRICTION.md`. If a
> performance lesson generalizes ("always prefer X over Y in this
> codebase"), promote it to TACTICS and leave a one-line pointer here.

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
- The two **structural** levers (module-system conversion of the full
  archive dependency chain; splitting `Framework.lean`'s analysis-heavy
  half behind a thinner facade) are real options but multi-file. Defer
  until Phase 6+ has more downstream files to amortize the cost.
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

**For this project, conversion isn't a win yet.** A `module` file cannot
import a non-`module` file (build error: *"cannot import non-`module` X from
`module`"*). To convert `Framework.lean`, we'd need to convert all
transitive imports first: the four `Mathlib/…` mirror files plus
`EdgesIn.lean`, `Sparsity.lean`, `Laman.lean`, `Henneberg.lean`. The
downstream beneficiary today is `LamanTheorem.lean` only — a multi-file
refactor for one importer's load time. **Defer until Phase 6+ adds more
downstream files** (a `RigidityMatroid.lean` would double the beneficiary
count; that's the right moment to convert).

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
| Replace `fun_prop` with an explicit `continuous_pi fun _ => continuous_pi fun e => continuous_rigidityMap_apply …` chain | `IsInfinitesimallyRigid.eventually` in `Framework.lean` | Within noise band (median ~24 s vs ~27 s baseline). Reverted — `fun_prop` is the project convention (cf. TACTICS § 6). |

## Experiments that *did* pay (or are at least defensible)

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

## Recommendations for future perf work

1. **Don't trust a single A/B run.** Run ≥ 4 trials per side and compare
   medians. If the medians are within ~5 s, declare neutral.
2. **Try the structural lever before micro-optimizing.** Splitting the
   analysis-heavy half of `Framework.lean` behind a facade (so
   `Sparsity.lean`/`Laman.lean`/`Henneberg.lean` don't transitively load
   `FiniteDimension`) would shrink ~15 s off most builds. Module-system
   conversion is the other structural lever; see *Module system* above.
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
- `TACTICS.md` § 6 *`fun_prop` for continuity / differentiability* — the
  project's convention for continuity goals (don't unroll into explicit
  `Continuous.*` chains for perf reasons).
