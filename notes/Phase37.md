# Phase 37 — `Molecular/` fragility-zone tactic sweep (AUTOMATE-Z, post-program) (work log)

**Status:** in progress (opened 2026-07-22; the deferred slice 6 of
Phase 36 / AUTOMATE, spun off as its own phase per the user decision
2026-07-22).

Internals-only, **structural-edit style** — no new blueprint chapter, no
new mathematics. Every headline statement and its axiom profile is
unchanged; re-verify the `formalization.yaml` headlines at the three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`) at close
(Phase 36 precedent). PIN stays queued and is unaffected; this commit
opens AUTOMATE-Z ahead of it at the user's initiative (PIN remains the
next-queued phase).

## Current state

Next concrete commit: **slice Z1** (the ScrewSpace-carrier leaf files —
`GenericLift/` + the four `Molecule/*` ScrewSpace files), dispatched via
`/coordinate-phase 37`. Unlike AUTOMATE (Phase 36), which opened
recon-first, AUTOMATE-Z **inherits the settled automation policy** and
opens straight into the sweep: the `@[grind]`/`@[grind =]` annotation set
is already measured **∅** (a no-op under the project's `grind only`
idiom — TACTICS-GOLF §1 / DESIGN.md *Predicates are `def`s*), no custom
tactic cleared the built-ins-first bar, and the `rw→simp only` collapse
discriminator + the three defeq-fragility shapes are catalogued
(TACTICS-GOLF §7). So there is no commit-1 recon; commit 1 is slice Z1.
Nothing has been built yet.

**Read TACTICS-GOLF §7 before touching any file** — it is the go-in
reference (discriminator + the three revert-on-sight fragility shapes).

## Architectural choices made up front (inherited from AUTOMATE + the fragility floor)

1. **Default NO-GO under strict build-neutrality.** This is the zone the
   AUTOMATE build-neutral sweep deliberately left untouched: defeq-fragile
   (coordinate-phase playbook fragility floor). Most `rw`-chain and
   `change`/`show` candidates here are **expected to revert on sight** —
   see *Expected yield*. Landing even a modest number of collapses is a
   fine outcome; a well-documented **"NO-GO, near-zero collapses"** close
   is itself a legitimate result, not a failure.
2. **opus minimum on every slice.** This is the rung where sonnet has
   wedged (coordinate-phase fragility floor); no slice dispatches below
   opus.
3. **Strict per-file build-neutral gate, no attribute additions.** A
   change lands only if the affected file's 4-run median
   (`notes/PERFORMANCE.md` protocol) is neutral-or-better and the build is
   warning-clean. The gate is genuinely **per-file**: a proof-body-only
   tactic swap (`rw`→`simp only`, `unfold`→`grind only`) does not change
   the decl's *type*, so downstream oleans are untouched and no
   whole-downstream-closure measurement is needed (the AUTOMATE verdict-B
   whole-closure recipe was for global `@[grind]` attributes, and this
   phase adds **none** — annotation set is ∅).
4. **Revert on sight, never raise a cap.** The three catalogued fragility
   shapes (below) are reverted immediately, never fought with
   `maxHeartbeats` / `maxRecDepth` bumps (standing rule: those knobs are
   not touched).
5. **Closing-vs-goal-shaping is the primary filter** (TACTICS-GOLF §7),
   not file identity. Skim the line after a candidate `rw`-chain before
   testing it: if it feeds a term-mode `refine`/`exact`/positional `rw …
   at h`, it is goal-shaping and almost never collapses — skip without a
   build. Only *closing* chains (whole tactic body, or immediately
   followed only by a closer like `omega`) are worth a gate run.

## The fragility-zone re-inventory (2026-07-22, my grep)

Zone = `Molecular/AlgebraicInduction/` (incl. `CaseIII/` + `Relabel/` +
`Theorem55.lean`), `Molecular/RigidityMatrix/`, and the
ScrewSpace-carrier-touching files outside those dirs
(`GenericLift/{Hinge,Panel}Generic`, `Meet.lean`,
`Molecule/{Dictionary,Duality,ProjectiveInvariance,ScrewVelocity}`).

**Totals (my method):** **381** four-plus-arg `rw` chains + **114**
tactic-position `change`/`show` sites across 28 files (~39.9k LoC).
(Phase 36's slice-6 estimate was ~351 `rw`-chains + ~154 `change`/`show`;
the deltas are counting-method noise — my `rw` counter walks multi-line
bracket blocks and is depth-aware for nested brackets, so it catches a
few more; my `change`/`show` counter is tactic-position only, where a
liberal whole-word count reaches ~290 once term-mode `show` and prose
are included. The per-slice breakdown is the load-bearing artifact, not
the grand total.)

Per-file, grouped by slice (`rw4+` = four-plus-arg `rw` chains;
`c/s` = tactic-position `change`+`show`; `↓` = transitive downstream
modules, a proxy for how many files a *statement*-changing edit would
rebuild — near-0 here, confirming the per-file gate):

| Slice | File | rw4+ | c/s | LoC | ↓ |
|---|---|---:|---:|---:|---:|
| **Z1** | `GenericLift/HingeGeneric.lean` | 9 | 9 | 1038 | 0 |
| | `GenericLift/PanelGeneric.lean` | 4 | 6 | 518 | 0 |
| | `Molecule/Dictionary.lean` | 5 | 2 | 350 | 4 |
| | `Molecule/Duality.lean` | 2 | 0 | 175 | 3 |
| | `Molecule/ProjectiveInvariance.lean` | 2 | 0 | 269 | 4 |
| | `Molecule/ScrewVelocity.lean` | 22 | 2 | 600 | 5 |
| **Z2** | `RigidityMatrix/Basic.lean` (carrier) | 31 | 2 | 2474 | 26 |
| | `RigidityMatrix/Bricks.lean` | 7 | 0 | 638 | 25 |
| | `RigidityMatrix/Claim612.lean` | 15 | 1 | 1478 | 26 |
| | `RigidityMatrix/Concrete.lean` | 20 | 6 | 2895 | 16 |
| | `Meet.lean` | 24 | 5 | 1929 | 26 |
| **Z3** | `AlgebraicInduction/CaseI.lean` | 10 | 1 | 2053 | 17 |
| | `AlgebraicInduction/CaseII.lean` | 26 | 9 | 1229 | 16 |
| | `AlgebraicInduction/Coupling.lean` | 10 | 0 | 1342 | 18 |
| **Z4** | `AlgebraicInduction/PanelLayer.lean` | 29 | 13 | 2286 | 25 |
| | `AlgebraicInduction/Pinning.lean` | 16 | 6 | 1965 | 24 |
| | `AlgebraicInduction/GenericityDevice.lean` | 19 | 5 | 1967 | 19 |
| | `AlgebraicInduction/Theorem55.lean` | 11 | 12 | 3549 | 7 |
| | `AlgebraicInduction/PanelHinge.lean` | 2 | 0 | 1138 | 22 |
| | `AlgebraicInduction/Nonvacuity.lean` | 0 | 0 | 54 | 0 |
| **Z5** | `AlgebraicInduction/CaseIII/Candidate.lean` | 27 | 4 | 2263 | 15 |
| | `AlgebraicInduction/CaseIII/Realization.lean` | 19 | 10 | 2712 | 8 |
| | `AlgebraicInduction/CaseIII/Arms.lean` | 17 | 9 | 1039 | 14 |
| **Z6** | `CaseIII/Relabel/Chain.lean` | 16 | 0 | 1107 | 12 |
| | `CaseIII/Relabel/Arm.lean` | 13 | 0 | 1136 | 11 |
| | `CaseIII/Relabel/Basic.lean` | 11 | 9 | 1666 | 13 |
| | `CaseIII/Relabel/ChainColumn.lean` | 9 | 1 | 1599 | 10 |
| | `CaseIII/Relabel/ForkedArm.lean` | 5 | 2 | 386 | 9 |

Per-slice candidate totals: Z1 44/19, Z2 97/14, Z3 46/10, Z4 77/36,
Z5 63/23, Z6 54/12 (`rw4+`/`c/s`).

## Expected yield — honest NO-GO framing

Set the coordinator's expectation low, so the phase does not chase a
doomed goal. The AUTOMATE non-fragile sweep landed 66 collapses across
~4 slices but *reverted the three fragility shapes on sight* — and those
shapes are precisely what this zone is made of:

- **The carrier is an opaque `def` (Phase 22l).** `ScrewSpace K k` is an
  opaque `def`, and its `.val`/`.mk`/`equivExteriorPower` API routes
  every coercion through the `ScrewSpace_def` `rfl` bridge via `cast`/`▸`
  (`RigidityMatrix/Basic.lean`). The whole point of that refactor was to
  stop tactics whnf-reducing through the carrier at reducible/instance
  transparency (the old `maxHeartbeats 400000` cost). A `simp only`
  collapse that touches a `ScrewSpace.val`/`.mk` site is a prime
  candidate for the **heartbeat-timeout** (shape 2) and
  **projection-auto-reduction** (shape 1) fragility shapes — expect
  Z2 to be the highest-revert-rate slice, and treat it as the **pivot**.
- **Goal-shaping dominates the fragile files.** Much of the `rw`-chain
  count in `CaseIII/`, `PanelLayer`, `Pinning` is goal-shaping for a
  downstream term-mode consumer (extensor/join algebra), which the
  discriminator predicts will not collapse. So the *testable* (closing)
  fraction of the 381 is well under half.

**Realistic outcome:** a small number of genuine `unfold…;omega` /
closing-chain collapses in the leaf files (Z1) and the arithmetic
corners of the AlgInd files, and near-zero in the carrier cluster (Z2).
A close reporting **"NO-GO, ~single-digit collapses, N candidates
reverted across the three shapes"** is a complete, legitimate phase
result — the deliverable is a *measured* verdict on the zone, not a
collapse count.

## Slice plan (buildable, S=1 hand-off; ordered for cheap-signal-first + carrier-pivot)

Each slice is a coherent file cluster (the AUTOMATE pattern:
combinatorial-core / Jacobs / BodyBar / matroid-pebble). Ordering: Z1
first (cheapest per-file builds, fastest signal on whether the zone
yields *anything*), then the carrier pivot Z2 (if Z1+Z2 are ≈0, close
NO-GO early rather than grinding Z3–Z6), then the AlgInd/CaseIII bulk.

- [ ] **Z1 — ScrewSpace-carrier leaf files** (calibration). Files:
      `GenericLift/{HingeGeneric,PanelGeneric}`,
      `Molecule/{Dictionary,Duality,ProjectiveInvariance,ScrewVelocity}`.
      44 `rw4+` / 19 `c/s`. Smallest files, cheapest gates — the fastest
      read on whether any closing-chain collapse survives in the zone.
- [ ] **Z2 — RigidityMatrix carrier cluster + `Meet`** (pivot). Files:
      `RigidityMatrix/{Basic,Bricks,Claim612,Concrete}`, `Meet.lean`.
      97 `rw4+` / 14 `c/s`. The opaque-carrier defeq wall lives here;
      highest expected revert-rate. If Z1+Z2 land ≈0, the phase can close
      NO-GO on this evidence.
- [ ] **Z3 — AlgInd Cases I/II + Coupling.** Files:
      `AlgebraicInduction/{CaseI,CaseII,Coupling}`. 46 `rw4+` / 10 `c/s`.
- [ ] **Z4 — AlgInd panel / pinning / genericity / Theorem55.** Files:
      `AlgebraicInduction/{PanelLayer,Pinning,GenericityDevice,Theorem55,PanelHinge,Nonvacuity}`.
      77 `rw4+` / 36 `c/s`. `Theorem55.lean` (3549 LoC) is the most
      expensive per-file build in the zone — budget accordingly.
- [ ] **Z5 — CaseIII core.** Files:
      `CaseIII/{Candidate,Realization,Arms}`. 63 `rw4+` / 23 `c/s`.
      `Realization` (2712) + `Candidate` (2263) are large; extensor-join
      goal-shaping is heavy here — expect a low testable fraction.
- [ ] **Z6 — CaseIII Relabel.** Files:
      `CaseIII/Relabel/{Chain,Arm,Basic,ChainColumn,ForkedArm}`.
      54 `rw4+` / 12 `c/s`.
- [ ] **close** — re-verify `formalization.yaml` headlines at the three
      standard axioms (`#print axioms`); ROADMAP row → ✓; fold the
      measured zone verdict (collapses landed + candidates reverted per
      shape) into TACTICS-GOLF §7 if it refines the catalog.

## Per-slice gate (the S=1 hand-off every slice dispatch inherits)

1. **opus minimum** — never dispatch a slice below opus (fragility floor).
2. **Closing-vs-goal-shaping discriminator first** (TACTICS-GOLF §7):
   test only *closing* chains; skip goal-shaping candidates on sight
   without a build.
3. **Per-file 4-run-median build-neutral + warning-clean**
   (`notes/PERFORMANCE.md` protocol). Neutral-or-better or revert. No
   attribute additions (set is ∅), so the gate is per-file, not
   whole-closure.
4. **Revert on sight for the three fragility shapes** (TACTICS-GOLF §7),
   never raise a cap:
   - *structure-projection / carrier auto-reduction* — `simp only`
     iota/whnf-reduces a projection-of-constructor (or the opaque-carrier
     `cast`/`▸` bridge) redex before the lemma list matches; `h` reported
     unused, goal left reduced. `rw` does not reduce.
   - *heartbeat timeout* — `(deterministic) timeout at whnf` at default
     200000 under `simp only` where `rw` closes instantly (the carrier /
     dualMap / `span_range_rigidityRow` chains).
   - *max-recursion depth* — `simp only` throws "maximum recursion depth"
     where `rw`'s positional single-application closes (e.g. a
     `Finset.filter_filter` double-application).

## Blockers / open questions

- Is the zone admissible at all under strict build-neutrality, or does
  the opaque-carrier defeq wall make even a closing-shaped `simp only`
  swap fail the three shapes across the board? (Z1 + the Z2 pivot answer
  this; default NO-GO until the evidence says otherwise.)

## Hand-off / next phase

Next concrete commit is **slice Z1** (ScrewSpace-carrier leaf files),
dispatched via `/coordinate-phase 37` at opus-minimum under the per-slice
gate above. AUTOMATE-Z inherits the AUTOMATE policy (∅ annotations, no
custom tactic, the §7 discriminator + fragility catalog) — there is no
recon commit. When Phase 37 closes (GO with a collapse count, or a
documented NO-GO), the queued **PIN** phase is next to open.

## Decisions made during this phase

*(none yet — the first sweep slice populates this)*
