# Phase 8 — perf pass (work log)

**Status:** in progress.

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

- [ ] **F1.1:** Establish baseline. 4-run A/B per
  `PERFORMANCE.md` *Measurement protocol* on the three analysis-heavy
  targets + `lake build` project total. Record medians in this
  work log under *Decisions made → F1.1 baseline*.
- [ ] **F1.2:** Execute the split. Move the IComponents+Augmentation
  block (lines 1267+ of `Sparsity.lean` — see the split-line
  inventory in `PERFORMANCE.md` *Split candidates ranked by
  leverage* §1) to a new file
  `CombinatorialRigidity/SparsityIComponents.lean`. Add a header
  matching the project's file-header convention; update
  `CountMatroid.lean` to import the new module.
- [ ] **F1.3:** Verify everything still builds + lints clean.
  Project-wide grep for `import .*Sparsity` confirms only the
  expected consumers; update imports as needed.
- [ ] **F1.4:** Post-split measurement. 4-run A/B on the same
  targets. Record medians; flag whether each target's median
  moves out of the ±5 s noise band.

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

*(Empty — populate as F1 / F2 / F3 land.)*

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

*(Empty — populate as cross-cutting lessons surface.)*

### Cleanup pass summaries

*(Empty — populate as each lever closes.)*

## Blockers / open questions

*(None at pass open.)*

## Hand-off / next phase

*(Written when the pass finishes.)*
