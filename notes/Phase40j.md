# Phase 40j — PENCIL-X0 / SPLITOFF: splitting off a body of degree two at non-adjacent neighbours (work log)

**Status:** in progress (opened design-first 2026-09-28). STEPS' sixth group
(`notes/Phase40-design.md` §3 STEPS, the SPLITOFF entry). It lands the split-off step at a body `x`
of degree two whose neighbours `a ≁ b`, the one-body ear `a − x − b` on `V₁`: if `X₀` attains at
`G″ = G.splitOff (x 0) a b (e 0)` (`G` with `x` suppressed) and
`deficiencyMerged₃(G[V₁]; a, b) + 5 ≤ def₃(G[V₁])` (Step MC11's `δ ≥ 5`), then `X₀(G)` attains
((MC-31)). No new mathematics. Five nodes, all red; two builds B1–B2, possibly three. **Next: B1,
the general pieces** — see *Hand-off*.

## Current state

**Opened.** Five nodes in `main-component.tex`'s new §`sec:main-component-splitoff` (between
`sec:main-component-orbit` and `sec:main-component-statements`; the chapter preamble names it),
with statements from the spike's exact statements (40h's `lem:pencil-ear-data` and 40i's
precedent) and workbook labels from `ledger.py --brief`:
- `lem:pencil-curve-limit` — (MC-31)'s semicontinuity step, via (MC-2): the STEPS recon's tracked
  curve-limit lemma, re-compiled verbatim;
- `lem:pencil-splitoff-special-rank` — (MC-28), the rank `+ (D − 1)` at the special position;
- `lem:pencil-splitoff-flexes` — (MC-30)(i), with its proof's formulas 1–2, on the lifting
  system's kernel;
- `lem:pencil-splitoff-curve` — (MC-30)(ii): the line of flexes, the heights of `G` from an
  incident flex of `G′`, and the kernel's locality;
- `thm:pencil-x0-splitoff` — (MC-31), with (MC-30)(iv) and (MC-29)(a)(b); the unpinned remark after
  it records that (MC-31)'s bound within one for `δ ≤ 4` is not formalized (call 5).

No Lean has landed. The red nodes carry no `\lean{…}` yet, 40h's open convention: each build adds
its pins with `\leanok` (*Lemma checklist*). No other node changes: the three deficiency nodes the
theorem uses are already stated at general `D`. The three carrier-forced deviations
(*Architectural choices*) are recorded in the blueprint proofs.

**The spikes** (gitignored `scratch/40j/`, local to this checkout; builder pointers, not evidence),
re-run at this open with **`lake lean`** at `52706564`, identical to the coordinator's re-run:
- `S40jSplitOff.lean` (852 lines, the whole build): exit 0, no errors, no warnings, no `sorry`; its
  nine `#print axioms` lines are each `[propext, Classical.choice, Quot.sound]`.
- `S40jCurve.lean` (the design doc's appendix piece (3), verbatim): exit 0, one axioms line,
  standard.
- `S40jInst.lean` (the instance): exit 0, one axioms line (`c7_isX0Graph`), standard.
- **Satisfiability** (not landed). `C₇` with ear `6 − 0 − 1` (`x = ![0]`, `e = ![0, 1]`, `a = 6`,
  `b = 1`, `V₁ = V ∖ {0}`): (H) and every structural hypothesis, `¬ Adj 6 1` included,
  kernel-checked in the instance spike. `hδ` is measured (script not retained): `def₃(P₆) = 5`
  with merged value `0`, so `δ = 5` (the coordinator re-derived it by hand); also `def₃(C₇) = 1`,
  `def₃(C₆) = 0`. `h₁` at `C₆` would come from the landed `of_cycle`; not checked. A non-cycle
  instance, θ(1,1,6) at the middle body of its long path: `δ = 5`, measured only.
- **Faithfulness** (against (MC-31)): `of_splitOff` is its `δ ≥ 5` conclusion, "`X₀(G)` attains
  whenever `δ ≥ 5`". `hδ` is literally Step MC11's `δ ≥ 5` (call 2). (MC-31)'s `ℓ₀(G″) = 3 +
  def₂(G″)` is discharged inside the step by BRIDGE (`G″` simple as `a ≁ b`, nonempty, three
  members in every closed neighbourhood from the admissible picture `X₀(G″)` supplies). (H) is asked
  at `G` only, as in 40g–40i; nothing at `G″` beyond attainment, nothing at `G′`.

## Architectural choices made up front

- **The route** (the recon's verdict; the design doc's §3 STEPS, SPLITOFF entry). (MC-28) is a
  count of motion spaces at the special normals, not the ear rank law. (MC-29) needs one
  inequality, `def₃(G″) + 1 ≤ def₃(G)`, two landed lemmas composed. (MC-30)(i) is a dimension
  count on the lifting system's kernel against Jackson–Jordán at `G″`, FLAT at `G` and
  `def₂(G″) ≤ def₂(G)`. One `s` off a finite set, then a line of flexes `y₀ + t·w` of `G′` with
  `x`'s picture moved from the special point toward its generic one; the curve-limit lemma,
  main-ness along the picture line, and `Graph.x0Attains_of_exists`.
- **Three carrier-forced, proof-level deviations** (in the blueprint proofs; not new workbook
  claims):
  1. `G′` may have bodies of degree 1 (at `C₇`, `G′ = P₆`), so the workbook's `F(G′, q′)` is the
     lifting system's kernel at `G′`, not `L_{G′}`; ORBIT's `two_le_finrank_map_planeDiff`, which
     needs `G′` admissible, is not reused.
  2. The special point is not admissible, so `x0Attains_of_exists` cannot be applied there: the
     curve is necessary.
  3. The workbook's rational `P(t)` is the polynomial line `y₀ + t·w`, `P(t)` times a scalar
     nonzero at `t = 0`, so the design doc's "clear denominators by per-body rescaling" is not
     needed; main-ness along the curve is `G`'s main-picture polynomial restricted to the picture
     line, nonzero at `t = 1`, in place of the workbook's (★) with (MC-4)(b).
- **The coordinator's calls** (2026-09-28). The PI's session-start configuration was **"follow
  precedent"**: where a 40e–40i precedent answers a recon question, the coordinator applies it and
  records it as its call, citing the precedent; only a genuinely new question goes to the PI. These
  are the coordinator's calls, not PI decisions, so they are not in `notes/pencil/adjudications.md`.
  1. **No new mathematics: 40j opens directly**, with no workbook commit and no second reading (the
     40f/40g/40i precedent), checked against Step MC11 and (MC-79).
  2. **`hδ` in the merged form**, `(G.induce V₁).deficiencyMerged 3 a b + 5 ≤
     (G.induce V₁).deficiency 3`, by 40i's `hδ₂` precedent. It is literally Step MC11's `δ ≥ 5`:
     `pairDelta` unfolds to `deficiency − deficiencyMerged`,
     `deficiency_weldPair_eq_deficiencyMerged` gives `def₃(G′/ab)`, and `bodyBarDim 3 = 6`.
  3. **Placement: the recon's table**, not the strict "beside its definition" reading: the steps in
     a new `MainComponent/SplitOff.lean` importing `Orbit.lean`; the curve-limit lemma in
     `Bridge.lean`'s per-body rescaling section; the motion count and `mem_liftingSpace_oneEar` in
     `Ear.lean`; `span_supportExtensor_ofNormals_eq` in `Cut.lean`; the two kernel lemmas in
     `Carrier.lean`; `polynomial_eval_aeval` as a Mathlib mirror (call 8). Precedents: 40d put the
     general `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_smul` in `Bridge.lean`; 40g's
     PI-approved layout put general framework ear laws in `Ear.lean`; and the strict reading would
     edit fragile-zone files, one already past the ~1500-line tripwire (`GenericityDevice.lean`
     1 972, `RigidityMatrix/Basic.lean` 2 472, `Bricks.lean` 1 458 → ~1 498). This reading of PI
     decision 5's convention is the coordinator's; the PI may reverse it at the cost of moving a
     few declarations.
  4. **Pins by PI decision 4(b)'s first-consumer rule**, as the recon's §6 table. The recon refuted
     the expectation that SPLITOFF would pay the D5 pin debt: the spike uses none of `jointMotions`,
     `weldedRank`, `relScrews`, `pairDelta`, `weldPair` or `deficiencySep` (the coordinator's
     grep). The debt is re-homed to COVERAGE; the live sentences naming SPLITOFF as its first
     consumer are corrected (design doc §3 STEPS and §7, `notes/Phase40i.md` *Hand-off*).
  5. **Only (MC-31)'s `δ ≥ 5` conclusion is formalized.** Its bound within one for `δ ≤ 4` has no
     consumer on the route: by (MC-79)(v) a `k = 1` chain with `1 ≤ δ ≤ 4` is unusable, and
     `δ = 0` is ORBIT's `of_openEar_one`. A remark in the theorem node records it.
  6. **`hinj` and `hab` are kept**, for ear-data parity with `of_openEar_one`.
  7. **COVERAGE tracked items** (design doc, COVERAGE): a `[ ]` item for `hδ`'s supplier, and the
     "(H) at the split-off antecedent" sentence extended to ORBIT's and SPLITOFF's antecedents.
  8. **Mirror `polynomial_eval_aeval`** as `MvPolynomial.polynomial_eval_aeval` under
     `CombinatorialRigidity/Mathlib/Algebra/MvPolynomial/`; upstream-eligible, by the 40f
     Mathlib-mirror precedent. The builder picks the file.
  9. **A tracked cleanup-round item** (not a close gate): `span_supportExtensor_ofNormals_eq` could
     replace the orientation split inlined in `finrank_span_rigidityRows_ofNormals_congr`.
  10. **Builds: B1** the general pieces in their homes, with `lem:pencil-curve-limit` and the
      mirror; **B2** `SplitOff.lean` with the other four nodes. Two builds, possibly three. The
      node plan (labels, placement, `\uses`) is the recon's §6.
- **Blueprint placement.** The general lemmas before the step; the curve-limit lemma first, as the
  only one not about the split-off graph.

## Lemma checklist

Planned names from the spike; pins in **bold**, the other names helpers, unpinned. B1 lands three
of B2's pins unpinned (the motion count, `mem_liftingSpace_oneEar`, `ker_liftingMatrix_congr`);
B2 pins them with their nodes.

- [ ] **B1, the general pieces** (their homes by call 3):
  - `Bridge.lean`, section *Per-body rescaling of the normals*:
    **`PanelHingeFramework.finite_setOf_finrank_lt_of_curve`** → `lem:pencil-curve-limit`, with
    the mirror `MvPolynomial.polynomial_eval_aeval` (call 8; mathlib's
    `Mathlib/Algebra/MvPolynomial/Polynomial.lean`, home of `MvPolynomial.polynomial_eval_eval₂`,
    is the natural mirror path);
  - `Ear.lean`: `BodyHingeFramework.finrank_span_rigidityRows_eq_add_of_motions` and
    `Graph.mem_liftingSpace_oneEar` (after `Graph.mem_closedNbhd_induce_of_ear`);
  - `Cut.lean`: `span_supportExtensor_ofNormals_eq`;
  - `Carrier.lean`: `Graph.ker_liftingMatrix_congr`, `Graph.ker_liftingMatrix_le_of_le`.
- [ ] **B2, the step**, new `MainComponent/SplitOff.lean`:
  **`Graph.finrank_span_rigidityRows_splitOff_special`** (the graph form) and
  **`BodyHingeFramework.finrank_span_rigidityRows_eq_add_of_motions`** (the motion count) →
  `lem:pencil-splitoff-special-rank`; **`Graph.planeDiff_eq_zero_of_splitOff`** →
  `lem:pencil-splitoff-flexes`; **`exists_mem_forall_add_smul_eq_zero`** (the line),
  **`Graph.mem_liftingSpace_oneEar`** (the heights) and **`Graph.ker_liftingMatrix_congr`** (the
  locality) → `lem:pencil-splitoff-curve`; **`Graph.X0Attains.of_splitOff`** →
  `thm:pencil-x0-splitoff`.
- [ ] **The close** (docs and blueprint only): the end-to-end re-read of the new subsection; the
  exposition ledger (candidate: the special position and the curve back to an admissible picture);
  the headline axioms; the design doc's §3 STEPS, ROADMAP and `MolecularConjecture.md`; the public
  surfaces unchanged (the PI's standing call, recorded at 40f's close).

## Blockers / open questions

- None blocking B1.
- **Builder notes.** `Graph.ker_liftingMatrix_congr` uses `Graph.closedNbhd_subset_vertexSet`,
  which lives downstream in `Bridge.lean`: inline it in `Carrier.lean`, as 40i's B1 did. The
  mirror file is new unless the builder extends an existing one; import it where
  `Bridge.lean` sees it, and add any new file to the root import. Every new top-level name greps
  to no prior definition (this open's check, TACTICS-QUIRKS §65).

## Hand-off / next phase

**Next: B1, the general pieces (fresh builder).** Source: `scratch/40j/S40jSplitOff.lean`
(gitignored, local to this checkout; a builder pointer, not evidence), with `S40jCurve.lean` for
the curve-limit lemma. Target: `lem:pencil-curve-limit` green; the other B1 pieces land unpinned for
B2. Chores:
- **`lake lean` the spike first**, never `lake env lean` (`CombinatorialRigidity/CLAUDE.md` *Lean
  LSP MCP*); it is clean at this open, so judge lint by `lake lint`.
- **Placement** as the checklist (call 3). No fragile-zone file is touched; after B1, `Bridge.lean`
  is about 480 lines, `Ear.lean` about 1 210, `Cut.lean` and `Carrier.lean` about 1 050 each, all
  under the tripwire.
- **Pin and flip** `lem:pencil-curve-limit` with its bold name. Gates: `lake build`, `lake lint`,
  `blueprint/verify.sh`, `blueprint/lint.sh`, `notes/check-phase-note.py`.

**Then B2** (`SplitOff.lean`, importing `Orbit.lean`, added to the root import, with a module
docstring listing its statements, the `Cut.lean` pattern), **then the close.**

**Cleanup-round item** (call 9; the design doc's SPLITOFF entry): the orientation split in
`finrank_span_rigidityRows_ofNormals_congr`.

## Decisions made during this phase

- **2026-09-28 — opened design-first** from SPLITOFF's design recon (opus, read-only,
  compiler-checked). This commit re-ran the three spikes at `52706564` and got the coordinator's
  counts. The coordinator's calls are under *Architectural choices*. The attribution to
  Jackson–Jordán's splitting-off case (Claim 6.5, Case 1, in the report form EGRES TR-2006-06,
  pp. 15–16) was read in `.refs/` for this open; the blueprint cites the journal paper without a
  claim number.
