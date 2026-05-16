# Phase 8 — perf pass (work log)

**Status:** in progress (F1 closed; F2/F3 pending).

## Current state

F1 (Sparsity L1267 split) closed: `Sparsity.lean` 1620 → 1273 LoC;
`SparsityIComponents.lean` new at 392 LoC; `CountMatroid.lean` swapped
its import. Build + lint clean. 4-run A/B: each target's median moved
≤ 6 s with inconsistent signs across targets, project-total essentially
flat — the audit's "1-3 s/file, in the noise band" prediction held.
**Verdict: structurally clean, perf-neutral.** Next: F2 (Henneberg
L444 split), reusing F1.4's post-split numbers as F2.1's baseline
per the *Reuse adjacent baselines* architectural choice.

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

- [ ] **F2.1:** Baseline. Reuse F1.4 numbers if measured
  back-to-back; otherwise establish fresh.
- [ ] **F2.2:** Execute the split. Move the iso-constructor /
  flat-form reverse-decomp / K₄-minus-edge example block (lines
  444+ of `Henneberg.lean` — see `PERFORMANCE.md` *Split
  candidates …* §2) to
  `CombinatorialRigidity/HennebergReverse.lean`. Update
  `MatroidIdentification.lean` + `LamanTheorem.lean` (both need
  the reverse half) to import the new module.
- [ ] **F2.3:** Build + lint verification.
- [ ] **F2.4:** Post-split measurement. 4-run A/B; record medians.

### F3 — Module-system conversion (12 project files)

- [ ] **F3.1:** Baseline. Reuse F2.4 numbers if back-to-back.
- [ ] **F3.2:** Convert `CombinatorialRigidity/Mathlib/*` mirror
  files first (all import already-converted upstream mathlib).
- [ ] **F3.3:** Convert project files in topo order from `EdgesIn`
  outward. Order (assuming F1 + F2 landed): `EdgesIn`,
  `SparsityBase`, `SparsityIComponents`, `Laman`,
  `HennebergForward`, `HennebergReverse`, `Framework`,
  `TrivialMotions`, `CountMatroid`, `HennebergRigidity`,
  `MatroidIdentification`, `LinearRigidityMatroid`,
  `LamanTheorem`, `RigidityMatroid`.
- [ ] **F3.4:** Per file, add `module` + `public import` lines + an
  `@[expose] public section` marker per the reference pattern in
  `Mathlib/Analysis/InnerProductSpace/PiL2.lean`.
- [ ] **F3.5:** Build + lint verification.
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

## Blockers / open questions

*(None at F1 close.)*

## Hand-off / next phase

*(Written when the pass finishes.)*
