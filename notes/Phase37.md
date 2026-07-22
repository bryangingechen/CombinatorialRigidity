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

Next concrete commit: **slice Z4b** (Theorem55, deferred from Z4 — see *Hand-off*:
its 4-run median gate is ~8 builds × ~34 s user, and its closing candidates are all
carrier `supportExtensor`/`graph` chains, so it was split off to keep Z4 clean).
**Z1 + Z2 + Z3 + Z4 landed** (see *Decisions made*): **6 / 37 / 12 / 12
build-neutral closing collapses, 4 / 7 / 0 / 2 reverted.** **The zone is GO** — the
"carrier pivot ≈ 0" prior is doubly overturned, and Z3/Z4 confirm the non-carrier
yield holds across the AlgInd bulk (arithmetic/card/linear-map/span closing chains
collapse freely). The defeq wall is
confined to **chains that touch a raw carrier-coercion site** (raw
`supportExtensor`/`ScrewSpace.val` unfolds, BIDIR `dualMap`/`toDual` bridge pairs) —
*not* the carrier-cluster files, and *not* even carrier-*adjacent* chains routed
through **packaged** API, which collapse (Z2 `complementIso_toDual`; Z3
`LinearMap.dualMap_apply'`, `extProj_apply_*`): `simp only` matches the packaged
lemma before it has to whnf through the carrier. Z3's 0 reverts came from filtering
the fragile shapes **pre-build** (raw-carrier unfolds + permutation/swap loopers +
trailing-implicit-`rfl` residuals), not from their absence. Expect comparable
non-carrier yield in Z4–Z6.

**Read TACTICS-GOLF §7 before touching any file** — it is the go-in
reference (discriminator + the three revert-on-sight fragility shapes).
Two Z1/Z2 additions to fold into §7 at phase-close:
- **(Z1) trailing-`rfl` predictor** — a closing chain whose original ends
  in a trailing `rfl` (explicit *or* rw's implicit final `rfl`) almost
  always reverts: the `rfl` discharges a definitional residual `simp only`
  strands (sharpened instance of shape 1). Z2 confirmed the *implicit*
  form (Basic 1966, Meet 1418/1421 all closed via rw's implicit trailing
  `rfl` and reverted under shape 1).
- **(Z2) conditional-rewrite no-progress (candidate 4th shape)** — a chain
  `rw [condLemma, condLemma, …]` where `condLemma` (e.g.
  `Pi.single_eq_of_ne`) has its explicit `≠`/side hypothesis left implicit
  — positional `rw` creates the side goal, discharged by subsequent `·`
  bullets — throws **"simp made no progress"** under `simp only` (it can't
  fire the conditional without the hypothesis, and the bullets are then
  stranded). Revert (Concrete 1992/2132). Distinct from shapes 1–3.
- **(Z3) discriminator refinement — `have`-block-closing is NOT
  goal-shaping.** The §7 "follow ∈ {`have`,…} → goal-shaping, skip" rule
  over-excludes: a `rw` that is the **last tactic of a `have … := by`
  block** is a *closing* chain even though its following line is the next
  (sibling) `have`. Distinguish "`rw` feeds a `have` that shapes the current
  goal" from "`rw` closes a `have`-block whose successor is an independent
  sibling `have`" — the latter collapses. Caught the L1309 twin of
  CaseI L1165 (would have been a false exclusion, and it collapsed).
- **(Z4) positional-sequential no-progress (sibling of the conditional shape).**
  A closing chain where each positional `rw` *creates the shape the next lemma
  matches* — e.g. a def-unfold (`partitionConstant_eq_range_funLeft`) feeding a
  side-condition lemma (`LinearMap.finrank_range_of_inj (hinj)`) feeding a
  `finrank` lemma — reverts under `simp only`: simp fires its args all-at-once
  and never builds the intermediate goal shapes, so it reports *every*
  non-terminal arg unused and leaves unsolved goals. `rw`'s left-to-right
  single-application is essential. Revert (PanelLayer L1720). Distinct from the
  Z2 conditional shape (that fails to fire *one* conditional lemma; this fails
  the *ordering* of a whole chain).

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

- [x] **Z1 — ScrewSpace-carrier leaf files** (calibration). **Done
      2026-07-22: 6 collapses landed, 4 tested-and-reverted (all shape 1).**
      Landed (`rw→simp only`, per-file 4-run median neutral, warning-clean):
      `ProjectiveInvariance` `supportExtensor_mapExtensor_ne_zero` (dedup
      4→3), `Duality` `molecularOfCentres_mapExtensor_screwComplementIso`
      (dedup 7→6), `Dictionary` `exists_molecularVel_eq` (×2), `ScrewVelocity`
      `exists_crossProduct_eq` (×2, pure ℝ³ algebra). Reverted (shape 1,
      trailing-`rfl` definitional residual): `Duality` `screwComplementIso_
      lineExtensor`, `ScrewVelocity` `screwOmega_stdBiv`/`screwTau_stdBiv`,
      `PanelGeneric` `exists_independent_normalRow_of_le_finrank`'s swap arm.
      `HingeGeneric` surveyed: all 9 `rw4+` goal-shaping/carrier → skipped.
- [x] **Z2 — RigidityMatrix carrier cluster + `Meet`** (pivot). **Done
      2026-07-22: 37 collapses landed (16 dedup), 7 tested-and-reverted.**
      Files: `RigidityMatrix/{Basic,Bricks,Claim612,Concrete}`, `Meet.lean`.
      Per-file 4-run median build-neutral (all |Δ| ≤ 0.5 s) + `lake lint`
      clean. **Overturned the "carrier pivot ≈ 0" prior** — see *Decisions
      made* Z2 and *Current state*: the wall is raw-carrier-coercion chains,
      not the files.
- [x] **Z3 — AlgInd Cases I/II + Coupling.** **Done 2026-07-22: 12 collapses
      landed (CaseI 4, CaseII 4, Coupling 4; 4 dedup, 8 same-arg), 0 reverted.**
      Per-file 4-run median build-neutral (CaseI −1.1s, CaseII −0.3s, Coupling
      +0.1s user) + full `lake build`/`lake lint` green. See *Decisions made* Z3.
- [x] **Z4 — AlgInd panel / pinning / genericity** (Theorem55 split to Z4b).
      **Done 2026-07-22: 12 collapses landed (PanelLayer 5, Pinning 5,
      GenericityDevice 2; 3 dedup), 2 not-landed.** Per-file 4-run median
      build-neutral (user Δ: GenericityDevice +0.4s, Pinning +0.5s, PanelLayer
      +0.8s) + full `lake build` warning-clean + `lake lint` green. See
      *Decisions made* Z4. PanelHinge surveyed nil (sole candidate is a carrier
      `supportExtensor`×2 chain, shape-1 revert-on-sight); Nonvacuity 0 candidates.
- [ ] **Z4b — Theorem55.** `AlgebraicInduction/Theorem55.lean` (3549 LoC,
      11 `rw4+` / 12 `c/s`). Deferred from Z4: most expensive per-file build
      (~34 s user/build → ~8-build median gate), and its closing candidates are
      all carrier-adjacent (`case_I_h65_ofNormals_supportExtensor`,
      `toBodyHinge_graph`/`ofNormals_graph`; L854/863/866/914) — higher revert
      risk, worth its own gated commit. The one clean card chain (L943) is
      goal-shaping (feeds `omega`), not closing.
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

- **None open.** The admissibility question is settled **GO** across Z1–Z4
  (67 collapses landed, 13 reverted); the "near-zero carrier pivot" prior
  conflated *carrier-cluster files* with *carrier-touching chains*. Run
  Z4b–Z6 to completion under the unchanged per-slice gate (no close-early);
  expect comparable non-carrier yield.

## Hand-off / next phase

Next concrete commit is **slice Z4b** (Theorem55:
`AlgebraicInduction/Theorem55.lean`; 11 `rw4+` / 12 `c/s`), dispatched via
`/coordinate-phase 37` at opus-minimum under the per-slice gate above. Budget the
heavy 4-run median (~34 s user/build). The testable closing candidates are the
carrier-adjacent graph/supportExtensor chains L854 (`toBodyHinge_graph`/
`ofNormals_graph`, graph-field, likely collapses) and L863/866/914
(`case_I_h65_ofNormals_supportExtensor`, higher revert risk); L943 is goal-shaping.
Carry all **four** predictors in (trailing-`rfl`, incl. rw's *implicit* final
`rfl`; conditional-rewrite no-progress; the Z3 `have`-block-closing discriminator
refinement; and the Z4 positional-sequential no-progress shape — see
*Current state*).
Method that worked Z1–Z4 (reusable for Z4b–Z6): scan `rw4+` chains, exclude
BIDIR(`←`)/positional(`at h`)/goal-shaping-feeder (follow = `refine`/`exact`/
`simp`/`by_cases`/next-`rw`/`congr` — **but a `have`/`rcases` after a
`have`-block-*closing* `rw` is a sibling, not a consumer: that `rw` is closing,
test it**) plus raw-carrier `supportExtensor`/`ScrewSpace.val` unfolds and
permutation/swap loopers, all on sight; batch-convert the surviving *closing*
chains to `simp only` (drop exact-duplicate mentions up front = the dedup
collapse), build once, read diagnostics (errors → revert + record shape), then
per-file 4-run median. AUTOMATE-Z inherits the AUTOMATE policy (∅ annotations, no
custom tactic, the §7 discriminator + fragility catalog) — no recon commit. When
Phase 37 closes, the queued **PIN** phase is next to open. At close, fold the
trailing-`rfl` predictor, the conditional-rewrite-no-progress shape, the Z3
`have`-block-closing discriminator refinement, **and the Z4 positional-sequential
no-progress shape** into TACTICS-GOLF §7.

## Decisions made during this phase

### Z4 — AlgInd panel / pinning / genericity (2026-07-22): 12 collapses, 2 not-landed; Theorem55 → Z4b

- **GO, non-carrier yield holds across the AlgInd bulk.** 12 closing
  `rw→simp only` swaps landed (PanelLayer 5, Pinning 5, GenericityDevice 2;
  3 dedup — `sub_smul`, `Pi.add_apply`, `Graph.partitionDef` — 9 same-arg),
  each per-file 4-run median build-neutral (user Δ: GenericityDevice +0.4s,
  Pinning +0.5s, PanelLayer +0.8s, all ≪ ±5s), full `lake build` warning-clean
  + `lake lint` green. Arithmetic / card (`Nat.card_range_of_injective`) /
  span-union / `Pi`-algebra / packaged linear-equiv (`LinearEquiv.trans_apply`)
  closing chains collapse freely — the Z2/Z3 non-carrier pattern.
- **2 not-landed, both PanelLayer, neither a catalogued-shape failure.**
  L1720 `finrank_partitionConstant`: new **Z4 positional-sequential no-progress**
  shape (see *Current state* predictor) — simp only reports all of
  `partitionConstant_eq_range_funLeft`/`finrank_range_of_inj (hinj)`/
  `finrank_screwAssignment` unused → unsolved goals. L519 ker-chain: `simp only`
  widening tripped the 100-char limit (marginal, reverted per "don't force" —
  Z2 Concrete-1806 precedent).
- **Theorem55 → Z4b (deferred).** Most expensive per-file build; closing
  candidates all carrier-adjacent — split to its own gated commit (see
  *Hand-off*). PanelHinge surveyed nil (L639 = `toBodyHinge_supportExtensor`×2
  carrier chain closing via implicit trailing `rfl` on a meet-of-normals
  residual — shape-1 revert-on-sight); Nonvacuity 0 candidates.
- No new lemmas / API; annotation set stays ∅. Friction review: nil (pure
  tactic swaps + reverts).

### Z3 — AlgInd Cases I/II + Coupling (2026-07-22): 12 collapses, 0 reverted

- **GO, highest testable-fraction yield yet.** All 12 tested closing chains
  collapsed `rw→simp only` (CaseI 4, CaseII 4, Coupling 4; 4 dedup, 8 same-arg),
  each per-file 4-run median build-neutral (user Δ: CaseI −1.1s, CaseII −0.3s,
  Coupling +0.1s), full `lake build` + `lake lint` green. Even the flagged-risky
  chains landed: the packaged `LinearMap.dualMap_apply'` chain (CaseI L1165 +
  its L1309 twin), the `set`-order-sensitive cast chain (CaseI L936, despite the
  TACTICS-QUIRKS §43 order-warning — `simp only` handled it), the `norm_cast`-feeder
  cast chain (CaseII L1214), and the `extProj`/`if_pos`/`if_neg` unfold chains
  (Coupling L824/L829/L860/L884).
- **0 reverts ≠ no fragile shapes — they were filtered pre-build.** Excluded on
  sight: raw-carrier `supportExtensor` unfolds closing via implicit trailing `rfl`
  on a `panelSupportExtensor (fun i => q₀ …)` residual (CaseII L877/L882/L1131/L1136,
  shape 1 + trailing-`rfl` predictor), `hingeRow_swap`/`panelSupportExtensor_swap`
  permutation loopers (§7 looping trap), and BIDIR `←`/`at h` chains.
- **Discriminator refinement (Z3 predictor, promote to §7 at close):** a `rw`
  closing a `have … := by` block is a *closing* chain even though its next line is
  the sibling `have` — see *Current state* predictor (Z3). Caught L1309.
- No new lemmas / API; annotation set stays ∅. Friction review: nil.

### Z2 — RigidityMatrix carrier cluster + `Meet` (2026-07-22): 37 collapses, 7 reverted

- **GO, high yield — prior overturned.** 37 closing `rw→simp only` swaps
  landed (Bricks 3, Basic 15, Claim612 8, Concrete 6, Meet 5; 16 realized a
  §7 de-dup, the rest same-arg), each per-file 4-run median build-neutral
  (|Δ| ≤ 0.5 s user-time), full `lake build` + `lake lint` green. The
  defeq wall is **raw-carrier-coercion chains**, not the carrier-cluster
  *files*; the files' non-carrier arithmetic / linear-map / `Pi`-algebra /
  `finrank` closing chains collapse freely, and packaged-API carrier-adjacent
  chains (`complementIso_toDual`, `rigidityMatrixEdge_mul_columnOp`,
  `Module.Basis.toDual_eq_repr`, `screwSpace_finrank`) also collapse.
- **7 reverted, 3 mechanisms.** (1) trailing-implicit-`rfl` definitional
  residual (shape 1): Basic 1966 (`hingeRow_comp_columnOp_vanish_off`),
  Meet 1418/1421 (`Basis.repr_self`/`mul_one`, `basis_apply` over-reduce).
  (2) conditional-rewrite no-progress (new 4th shape): Concrete 1992/2132
  (`Pi.single_eq_of_ne` with implicit `≠`). (3) goal-shaping (simp normal
  form ≠ consumer's term): Meet 1194 (downstream type-mismatch). Plus
  Concrete 1806 not-landed (marginal cosmetic carrier-adjacent chain that
  tripped the 100-char limit on the `rw→simp only` widening — reverted per
  "don't force marginal", not a fragility failure).
- BIDIR `dualMap`/`toDual`/`map_add`-bridge pairs excluded on sight (§7
  looping trap) — the densest raw-carrier chains, never tested.
- No new lemmas / API; annotation set stays ∅. Friction review: nil (pure
  tactic swaps + reverts).

### Z1 — ScrewSpace-carrier leaf files (2026-07-22): 6 collapses, 4 reverted (all shape 1)

- **Leaf files DO admit build-neutral collapses; carrier/definitional
  chains do NOT.** 6 closing `rw→simp only` swaps landed
  (ProjectiveInvariance ×1 dedup, Duality ×1 dedup, Dictionary ×2,
  ScrewVelocity ×2 pure-algebra), each per-file 4-run-median neutral
  (user-time treatment ≤ baseline, all Δ < 0.4 s) and warning-clean; full
  `lake build` + `lake lint` green. Answers the phase's admissibility
  question for the *leaf* files: **GO, small yield.**
- **Trailing-`rfl` is a fourth revert-on-sight predictor (sharpens shape
  1).** All 4 reverts — Duality `screwComplementIso_lineExtensor`,
  ScrewVelocity `screwOmega_stdBiv`/`screwTau_stdBiv`, PanelGeneric
  `exists_independent_normalRow_of_le_finrank` — were closing chains whose
  original ends `rw […]` **then an explicit `rfl`**. `simp only` reproduces
  the rewrites but strands the final definitional residual (`cast`/
  `equivExteriorPower` bridge, or a `normalRow`/`omegaForm` unfold) that the
  `rfl` closed; goal left in the reduced-but-not-closed shape. Cheap
  syntactic tell for Z2+ — promote to TACTICS-GOLF §7 at phase-close.
- **`lean_multi_attempt` false-positive reconfirmed.** It reported
  `goals:[]` for the Duality `screwComplementIso_lineExtensor` collapse
  (and even for the *unchanged* rw, which the real proof follows with an
  explicit `rfl`); the real `lake build` failed. Multi-line closing chains:
  the build is the only gate (TACTICS-GOLF §7 caveat).
- No new lemmas / API; annotation set stays ∅. Friction review: nil (pure
  tactic swaps + reverts).
