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
- The two **structural** levers (module-system conversion of the full
  archive dependency chain; splitting `Framework.lean`'s analysis-heavy
  half behind a thinner facade) are real options but multi-file. The
  Phase-6 downstream additions (`TrivialMotions.lean`,
  `HennebergRigidity.lean`, `RigidityMatroid.lean`, `LamanTheorem.lean`)
  have now grown the beneficiary count enough that conversion would
  amortize; still unmeasured against the noise band — pick up as a
  dedicated perf pass.
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

**For this project, conversion is plausibly a win post-Phase-6, but
still unmeasured.** A `module` file cannot import a non-`module`
file (build error: *"cannot import non-`module` X from `module`"*).
To convert `Framework.lean`, we'd need to convert all transitive
imports first: the `Mathlib/…` mirror files plus `EdgesIn.lean`,
`Sparsity.lean`, `Laman.lean`, `Henneberg.lean`. After Phase 6, the
downstream beneficiaries are `TrivialMotions.lean`,
`HennebergRigidity.lean`, `RigidityMatroid.lean`, and
`LamanTheorem.lean` — four importers, enough to amortize. The
conversion remains a multi-file refactor and the gain is still
unmeasured against the build-time noise band (see *Headline lessons
from Phase 5*); pick up as a dedicated perf pass when the time
arrives.

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

## Post-Phase-8 file-structure audit (audit-only, no Lean changes)

The post-Phase-8 cleanup round's bucket E surveyed the project's import
graph and file sizes for split candidates. **Findings remain
recommendations, not executed splits** — splits change the public API
surface and warrant a dedicated structural-refactor pass with the 4-run
A/B protocol below.

### Import graph (project files, post-Phase-8)

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

### Open (next session): granular `@[expose]` / `public` audit per file

**Priority: do this next session.** The 4 + 3 per-declaration
`set_option backward.privateInPublic` lines remaining in
`Framework.lean` and `HennebergReverse.lean` are technical debt: the
option is a `backward.*` compat knob, and the Lean reference manual
explicitly directs users to *"locate and eventually eliminate these
references."* The principled elimination is the audit below — it's
the same work as the post-conversion perf lever, so the two should
land together.

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

**Concrete elimination targets (Framework.lean, 4 sites):**

- `edgeRow` — private `noncomputable def`, referenced from
  `RigidityMap`'s body. Two paths: (a) drop `@[expose]` from this
  file's section so `RigidityMap`'s body stops being exposed (then
  `edgeRow` stops being a public-scope reference); (b) make
  `edgeRow` itself non-`private`. Path (a) is preferred if
  downstream files don't `simp [RigidityMap]` / `unfold RigidityMap`.
- `edgeRow_symm` — private `theorem` referenced *as a term* in
  `RigidityMap`'s body (`Sym2.lift ⟨edgeRow p, edgeRow_symm p⟩`).
  Same disposition as `edgeRow`.
- `RigidityMap` — the consumer side of the above two. Eliminating
  the opt-ins on `edgeRow` / `edgeRow_symm` removes this one
  automatically.
- `continuous_rigidityMap_apply` — private `@[fun_prop]` theorem
  resolved by name from another file's `fun_prop` invocation
  (`RigidityMatroid.lean` line 274). Preferred fix: drop `private`
  — attribute-tagged helpers are usually better as plain public,
  since the tactic database stores the name anyway.

**Concrete elimination targets (HennebergReverse.lean, 3 sites):**

- `isoOfOptionSubtypeNe` — private `def` referenced from
  `typeI_iso_of_two_neighbors` / `typeII_iso_of_three_neighbors`'s
  bodies. Path (a) (demote `@[expose]`) is plausible since the
  `IsLaman.iso` / `IsLaman.exists_typeI_or_typeII_reverse` API
  downstream consumes these isos opaquely.
- `typeI_iso_of_two_neighbors`, `typeII_iso_of_three_neighbors` —
  consumer sides; eliminated automatically by path (a).

Cross-reference: as of this commit, 7 of 9 project files that
previously had file-scope `set_option backward.privateInPublic`
were cleaned (the option is unnecessary there — their `private`
decls participate only in proof bodies, which are always private).
The remaining 2 files retain mathlib-style per-declaration `set_option
… in` as a short-term bridge until the audit lands.

## Recommendations for future perf work

1. **Don't trust a single A/B run.** Run ≥ 4 trials per side and compare
   medians. If the medians are within ~5 s, declare neutral.
2. **Try the structural lever before micro-optimizing.** Splitting the
   analysis-heavy half of `Framework.lean` behind a facade (so
   `Sparsity.lean`/`Laman.lean`/`Henneberg.lean` don't transitively load
   `FiniteDimension`) would shrink ~15 s off most builds. Module-system
   conversion is the other structural lever; see *Module system* above
   (now ripe per the post-Phase-8 audit). The `Sparsity.lean` split
   above is the third structural lever, with a single-downstream-
   consumer audit confirming the cleanest possible cut line.
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
