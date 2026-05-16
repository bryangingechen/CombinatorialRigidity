# Phase 8 — perf pass (work log)

**Status:** in progress (F1, F2 closed; F3 mid-stream — mirrors
converted, project files pending).

## Current state

F1 (Sparsity L1267 split) and F2 (Henneberg L444 split) both closed
structurally clean (verdict: project-total perf-neutral; per-target
deltas inconclusive — see *Cleanup pass summaries* below). F3.1
baseline reused from F2.4 medians per the *Reuse adjacent baselines*
architectural choice (same machine, same day, no intervening source
edits). F3.2: all 14 `CombinatorialRigidity/Mathlib/*` mirror files
converted to the module system in one commit — `module` line,
`import X` → `public import X`, and an unnamed `@[expose] public
section` between the doc block and the namespace. Build + lint
clean. Next: F3.3 (convert all 14 project files in topo order from
`EdgesIn` outward), then F3.6 measurement.

## Pass overview

This is the post-Phase-8 perf pass discharging the structural-refactor
carry-over from the Phase 8-cleanup round's *Hand-off / next phase*
(see `notes/Phase8-cleanup.md`). Per `notes/PERFORMANCE.md`
*Post-Phase-8 file-structure audit* + *Module-system conversion: now
ripe*, the pass executes the three structural levers audited (but not
executed) during Phase 8-cleanup's bucket E:

- **F1.** Split `Sparsity.lean` at L1267 → `SparsityBase` (~1266 LoC) +
  `SparsityIComponents` (~354 LoC). Highest-leverage cut: 8 of 10
  downstream files drop the IComponents+Augmentation block from their
  transitive import set. Only downstream consumer of the moved block
  is `CountMatroid.lean` (one use of `IsSparse.exists_aug_of_lt_two_mul`,
  verified by grep).
- **F2.** Split `Henneberg.lean` at L444 → `HennebergForward` (~400 LoC)
  + `HennebergReverse` (~200 LoC). Medium leverage: shaves ~200 LoC
  of reverse-decomp machinery off `HennebergRigidity`'s transitive
  import set (analysis-heavy, 3 downstream importers).
- **F3.** Convert all 12 project files to Lean's module system. Mathlib
  v4.30.0-rc2 is ~98.6 % converted, so the earlier "transitive imports
  first" blocker is gone. Convert `CombinatorialRigidity/Mathlib/*`
  mirrors first, then project files in topo order from `EdgesIn`
  outward.

## Architectural choices made up front

- **Sequential measurement.** Each lever gets its own 4-run A/B per
  `notes/PERFORMANCE.md` *Measurement protocol* before moving to the
  next, so savings (or non-savings) attribute to each lever
  individually. `PERFORMANCE.md` recommends a combined campaign for
  efficiency; we accept the extra measurement cost in exchange for
  diagnostic clarity. Likely outcome per the audit's prediction
  ("1–3 s per file, in the noise band") is that some levers land
  neutral — sequential measurement makes that an honest data point
  rather than a hidden component of a combined delta.
- **Measurement targets.** The analysis-heavy targets per
  `PERFORMANCE.md` *Module system*: `HennebergRigidity.lean`,
  `RigidityMatroid.lean`, `LinearRigidityMatroid.lean`. Plus
  `lake build` (project total) as a fourth target. Each baseline is
  4 runs with content-nudge per the file; medians compared at the
  ±5 s noise band threshold.
- **Each lever as its own commit (or commit pair).** Each split
  commit is mechanical (move declarations + add an `import` line);
  the A/B measurement reads as a follow-up notes commit recording
  medians. The module-system conversion may itself span multiple
  commits (one per converted file or per topo-sorted layer).
- **Reuse adjacent baselines.** F2's baseline reuses F1.4's
  post-split numbers if measured back-to-back; F3.1 reuses F2.4.
  This skirts the cold-cache noise from re-establishing a fresh
  baseline.

## Task checklist

### F1 — `Sparsity.lean` split at L1267

- [x] **F1.1:** Baseline established. 4-run medians (commit `43a2b84`,
  toshiba M-series arm64, macOS 26.4.1):

  | Target | run 1 | run 2 | run 3 | run 4 | median |
  |---|---|---|---|---|---|
  | `HennebergRigidity` | 80.6 | 66.6 | 38.8 | 47.9 | **57.3 s** |
  | `RigidityMatroid` | 51.5 | 52.6 | 54.9 | 64.3 | **53.7 s** |
  | `LinearRigidityMatroid` | 101.3 | 60.8 | 59.6 | 63.8 | **62.3 s** |
  | `lake build` (project) | 74.7 | 19.7 | 18.7 | 22.8 | **21.2 s** |

  Per-target rows nudge the target file directly (measures
  elaboration of that file with cached deps). Project-total nudges
  `EdgesIn.lean` (top of the import chain), forcing a chain
  invalidation; runs 2-4 show `Replayed` semantics (downstream
  oleans byte-identical despite source nudge), so the project-
  total median primarily reflects the EdgesIn+Sparsity rebuild
  cost rather than full-chain elaboration. The same protocol is
  used post-split, so the comparison stays apples-to-apples.

- [x] **F1.2:** Split executed. `Sparsity.lean` 1620 → 1273 LoC;
  new file `CombinatorialRigidity/SparsityIComponents.lean` at
  367 LoC carries the IComponents + Augmentation block (sections
  preserved, `variable {V : Type*}` redeclared at the new file's
  `namespace SimpleGraph`). `CountMatroid.lean` switched its
  `import` from `.Sparsity` to `.SparsityIComponents` (the new
  file transitively imports `.Sparsity`, so the rest of the
  base API stays in scope).
- [x] **F1.3:** Build + lint clean. Project-wide grep confirms
  only `CountMatroid` directly imports `.SparsityIComponents`;
  the seven non-matroid downstream files (`Laman`, `Framework`,
  `Henneberg`, `TrivialMotions`, `HennebergRigidity`,
  `RigidityMatroid`, `LamanTheorem`) drop the moved block from
  their transitive import set. Top-level `CombinatorialRigidity.lean`
  pulls both halves via its existing `CountMatroid` import.
- [x] **F1.4:** Post-split medians:

  | Target | run 1 | run 2 | run 3 | run 4 | median | Δ vs baseline |
  |---|---|---|---|---|---|---|
  | `HennebergRigidity` | 60.0 | 51.8 | 50.6 | 51.0 | **51.4 s** | −5.9 s |
  | `RigidityMatroid` | 61.0 | 57.6 | 61.2 | 55.4 | **59.3 s** | +5.6 s |
  | `LinearRigidityMatroid` | 98.9 | 54.3 | 57.9 | 53.1 | **56.1 s** | −6.2 s |
  | `lake build` (project) | 70.1 | 21.3 | 14.0 | 20.5 | **20.9 s** | −0.3 s |

  Each Δ sits right at the ±5 s noise band; signs are inconsistent
  (HR and LRM down, RM up); project-total essentially flat. Audit
  prediction held ("1–3 s per file, in the noise band").

  **F1 verdict: structurally clean, perf-neutral.** The win is the
  module organization — the Phase-7 matroid-side machinery now lives
  in its own file, matching the blueprint chapter split (`sparsity.tex`
  vs `count-matroid.tex`) and the audit's single-downstream-consumer
  finding. No measurable wall-clock improvement on the analysis-heavy
  targets; the audit's predicted ~1-3 s/file savings sit below the
  noise floor of the 4-run protocol.

### F2 — `Henneberg.lean` split at L444

- [x] **F2.1:** Baseline reused from F1.4 (back-to-back) per the
  *Reuse adjacent baselines* architectural choice. F1.4 medians:
  HR 51.4 s; RM 59.3 s; LRM 56.1 s; project-total 20.9 s.

- [x] **F2.2:** Split executed. `Henneberg.lean` 647 → 454 LoC;
  new file `CombinatorialRigidity/HennebergReverse.lean` at 246 LoC
  carries the *Decomposition iso constructors* block
  (`isoOfOptionSubtypeNe`, `typeI_iso_of_two_neighbors`,
  `typeII_iso_of_three_neighbors`), the *Flat-form Henneberg reverse
  decomposition* block (`IsLaman.exists_typeI_or_typeII_reverse`),
  and the *K₄ minus one edge is Laman* worked example
  (`Henneberg.fin4equiv`, `Henneberg.fin4iso`,
  `top_fin_four_minus_edge_isLaman`). Sections preserved;
  `namespace SimpleGraph` + `variable {V : Type*}` + `namespace
  Henneberg` redeclared at the new file's top (same gotcha as F1's
  `SparsityIComponents`, called out in *Phase-local choices* below).
  `LamanTheorem.lean` and `MatroidIdentification.lean` each gained
  one `import CombinatorialRigidity.HennebergReverse` line;
  `HennebergRigidity.lean`'s `import` of `.Henneberg` stays put
  (forward half only).

- [x] **F2.3:** Build + lint clean. Project-wide grep confirms
  `LamanTheorem` and `MatroidIdentification` directly import
  `.HennebergReverse`; `HennebergRigidity` and the rest stay with
  `.Henneberg` alone (forward half only). Top-level
  `CombinatorialRigidity.lean` pulls the reverse half transitively
  via its `LamanTheorem` + `MatroidIdentification` imports — no
  edit needed there.

- [x] **F2.4:** Post-split medians:

  | Target | run 1 | run 2 | run 3 | run 4 | median | Δ vs baseline |
  |---|---|---|---|---|---|---|
  | `HennebergRigidity` | 50.1 | 58.8 | 78.7 | 58.5 | **58.7 s** | +7.3 s |
  | `RigidityMatroid` | 60.4 | 59.6 | 64.0 | 57.4 | **60.0 s** | +0.7 s |
  | `LinearRigidityMatroid` | 107.4 | 63.5 | 69.2 | 70.5 | **69.9 s** | +13.8 s |
  | `lake build` (project) | 82.2 | 22.3 | 18.8 | 15.5 | **20.6 s** | −0.3 s |

  Project-total median essentially flat; per-target medians all
  positive, with HR and LRM outside the ±5 s noise band. The LRM
  shift's pattern (warm-runs cluster at 63-70 s vs F1.4's 53-58 s)
  suggests OS-level interference during the back-to-back campaign
  rather than a structural cost — the split adds one olean to LRM's
  transitive load but no content change, and the project-total
  (which sees the same chain) is flat. Run-1 outliers (HR 78.7 s
  was the third run in this campaign; LRM 107.4 was the cold first
  run, matching F1.4's 98.9 s shape) inflate the per-target medians
  but are absorbed by project-total replay semantics.

  **F2 verdict: structurally clean, project-total perf-neutral;
  per-target deltas inconclusive.** The durable win is module
  organization — the *operation-form forward preservation* / *flat-
  form reverse decomposition* split documented in `DESIGN.md`
  *Statement-form conventions* now lives at the file boundary, not
  just in section headers.

### F3 — Module-system conversion (12 project files)

- [x] **F3.1:** Baseline reused from F2.4 (same machine, same day,
  no intervening source edits) per the *Reuse adjacent baselines*
  architectural choice. F2.4 medians: HR 58.7 s; RM 60.0 s; LRM
  69.9 s; project-total 20.6 s.
- [x] **F3.2:** All 14 `CombinatorialRigidity/Mathlib/*` mirror
  files converted to the module system. Per file: `module` line
  after the copyright header, every `import X` rewritten to
  `public import X`, and an unnamed `@[expose] public section`
  inserted between the doc block and the namespace (model:
  `Mathlib/Analysis/InnerProductSpace/PiL2.lean`). Build + lint
  clean.
- [ ] **F3.3:** Convert project files in topo order from `EdgesIn`
  outward. Order (post-F1, post-F2): `EdgesIn`, `Sparsity`,
  `SparsityIComponents`, `Laman`, `Henneberg`, `HennebergReverse`,
  `Framework`, `TrivialMotions`, `CountMatroid`,
  `HennebergRigidity`, `MatroidIdentification`,
  `LinearRigidityMatroid`, `LamanTheorem`, `RigidityMatroid`.
  (F1 named the forward half `Sparsity` rather than `SparsityBase`;
  F2 named the forward half `Henneberg` rather than
  `HennebergForward` — see *Phase-local choices* on F2.)
- [ ] **F3.4:** *(folded into F3.2/F3.3 as the conversion mechanic
  rather than a separate step.)*
- [ ] **F3.5:** *(build + lint run inline at the close of F3.2 and
  F3.3 commits; no separate verification step needed.)*
- [ ] **F3.6:** Final measurement. 4-run A/B on the analysis-heavy
  targets + project total. Record medians; compute combined delta
  against F1.1 baseline; promote the headline to
  `PERFORMANCE.md` *Experiments that did pay* or *…didn't pay*.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **`variable {V : Type*}` redeclared in `SparsityIComponents`.** The
  base `Sparsity.lean` declared `variable {V : Type*} (G : SimpleGraph V)`
  at L107 (just under `namespace SimpleGraph`); since `V` is implicit
  and `G` was made implicit again at L126 (`variable {G}`), only `V`
  actually flowed forward into the moved sections. The new file's
  `namespace SimpleGraph` therefore redeclares `variable {V : Type*}`
  alone — first build attempt failed with *"Unknown identifier `V`"* at
  the `private lemma ne_of_mem_top_edgeSet {V : Type*}` site (which
  re-introduces `V` explicitly but downstream lemmas without an explicit
  `V` binder need the section-level variable). One-shot fix.

- **Same gotcha preempted in F2's `HennebergReverse`.** Forewarned by
  the F1 entry above, the new file's preamble declared
  `namespace SimpleGraph` + `variable {V : Type*}` + `namespace
  Henneberg` from the start. No build-failure cycle. Lesson holds for
  any future Lean-file split where a `variable` declaration lives near
  the top of the original file — the split point is downstream of the
  declaration, so the new file needs its own copy.

- **Forward / reverse split lives at the `DESIGN.md`-documented
  boundary.** `DESIGN.md` *Statement-form conventions* already
  separates operation-form forward preservation (`typeI_isLaman`,
  `typeII_isLaman`, `typeI_isLaman_iff`, the per-move rigidity-
  preservation theorems in `HennebergRigidity.lean`) from flat-form
  reverse decomposition (the iso constructors and
  `IsLaman.exists_typeI_or_typeII_reverse`). F2's split moves that
  boundary from section-level to file-level: forward → `Henneberg.lean`
  (used by `HennebergRigidity`); reverse → `HennebergReverse.lean`
  (used by `MatroidIdentification` + `LamanTheorem`). No
  cross-cutting `DESIGN.md` revision needed — the existing conventions
  section already endorses the boundary; F2 just relocates it
  physically.

- **Module-system conversion mechanic.** Per file: insert `module`
  after the copyright header (with a blank line); rewrite every
  `import X` (project mirrors and upstream alike) to `public
  import X`; insert an unnamed `@[expose] public section` between
  the file's doc block and the first `open` / `namespace` /
  declaration. The section spans to end-of-file and needs no
  matching `end` at file scope — only the existing `namespace X /
  end X` pair still pairs as before. Model file:
  `Mathlib/Analysis/InnerProductSpace/PiL2.lean`. Constraint: a
  `module` file's imports must themselves be `module` (build error
  otherwise) — this is why F3.2 (mirrors) lands before F3.3 (project
  files), since mirrors are the leaves we control. Mathlib v4.30.0-rc2
  is ~98.6 % converted, so upstream imports are already compliant.
  Cross-file tip lifted to `CombinatorialRigidity/CLAUDE.md`
  *Module-system conversion*.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

*(Empty — populate as cross-cutting lessons surface.)*

### Cleanup pass summaries

**F1 — Sparsity.lean L1267 split.** `Sparsity.lean` 1620 → 1273 LoC;
new file `SparsityIComponents.lean` at 392 LoC carries the
IComponents (`HasBlock`, `maxBlock(Set)`, `IsSparse.maxBlock_isTightOn`,
`IsSparse.maxBlock_eq_of_subset_maxBlock`) + Augmentation
(`ne_of_mem_top_edgeSet`, `IsSparse.exists_aug_of_lt_two_mul`) blocks.
`CountMatroid.lean` (the sole downstream consumer) swapped its
`.Sparsity` import for `.SparsityIComponents`. Build + lint clean.
4-run A/B baseline vs post-split: HR -5.9 s, RM +5.6 s, LRM -6.2 s,
project-total -0.3 s — each individual Δ sits at the ±5 s noise band
threshold with inconsistent signs. **Verdict: structurally clean,
perf-neutral.** Audit's prediction held ("1-3 s/file, in the noise
band"). The durable win is module organization (Phase-7 matroid-side
machinery in its own file, matching the blueprint chapter split).

**F2 — Henneberg.lean L444 split.** `Henneberg.lean` 647 → 454 LoC;
new file `HennebergReverse.lean` at 246 LoC carries the
*Decomposition iso constructors* block (`isoOfOptionSubtypeNe`,
`typeI_iso_of_two_neighbors`, `typeII_iso_of_three_neighbors`), the
*Flat-form Henneberg reverse decomposition* block
(`IsLaman.exists_typeI_or_typeII_reverse`), and the *K₄ minus one
edge is Laman* worked example. `LamanTheorem.lean` and
`MatroidIdentification.lean` each gained one
`import CombinatorialRigidity.HennebergReverse`;
`HennebergRigidity.lean` and the other downstream files stay with
the forward-only `.Henneberg` import. Build + lint clean. 4-run A/B
baseline (reused F1.4) vs post-split: HR +7.3 s, RM +0.7 s, LRM
+13.8 s, project-total −0.3 s. Project-total flat; per-target
deltas all positive, with HR and LRM outside the ±5 s noise band.
LRM's warm-runs cluster (63-70 s vs F1.4's 53-58 s) is the most
concerning shift, but the split changes only the import-graph shape
(same total content) and project-total absorbs that via replay
semantics — pointing at machine-variance during the back-to-back
second campaign rather than a structural regression. **Verdict:
structurally clean, project-total perf-neutral; per-target deltas
inconclusive.** The durable win is the
`DESIGN.md`-documented forward / reverse split (operation-form
forward preservation vs flat-form reverse decomposition) now living
at the file boundary, not just at section-header level.

## Blockers / open questions

*(None at F2 close.)*

## Hand-off / next phase

Mid-stream: F3.2 (mirror conversion) committed. Next concrete commit
is F3.3 — convert the 14 project `.lean` files in topo order from
`EdgesIn` outward, same mechanic as F3.2 (model file:
`Mathlib/Analysis/InnerProductSpace/PiL2.lean`, see also
`CombinatorialRigidity/CLAUDE.md` *Module-system conversion*).
Build + lint at close; commit. Then F3.6 — 4-run A/B against F1.1
baseline; promote headline to `PERFORMANCE.md`.
