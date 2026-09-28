# Phase 40m — PENCIL-X0 / COVERAGE-CHAINS + THEOREM-S: chains, cuts, Theorem S and the covering theorem (work log)

**Status:** in progress (opened design-first 2026-09-28). COVERAGE's second and last sub-phase:
**CHAINS** (the maximal ear through bodies of degree two, chains, the cycle, and the cut-vertex and
bridge reductions, with (H) at every smaller graph) with **THEOREM-S** (Theorem S and the covering
theorem) folded in, by the PI's call (2026-09-28, `notes/pencil/adjudications.md`; plan
`notes/Phase40-design.md` §3 COVERAGE). Its close also closes COVERAGE: the general configuration
attains at every graph satisfying (H). No workbook change and no new mathematics. Eleven red nodes
to green in five builds, all transcriptions of complete sorry-free spikes. **Next: B1,
`CoverageChain.lean`** — see *Hand-off*. MOTIVES follows.

## Current state

**Opened; no Lean yet.** The eleven target nodes of `blueprint/src/chapter/main-component.tex`
§`sec:main-component-coverage` are red and unpinned; each build adds its nodes' `\lean{…}` and
`\leanok` (statement and proof). Which build greens each node:
- **CHAINS:** `def:pencil-x0-chain`, `lem:pencil-x0-chain-exists`, `lem:pencil-x0-cycle-reduces`
  (B1); `lem:pencil-x0-chain-standing` (B2); `lem:pencil-x0-cut-reduces` (B3).
- **THEOREM-S:** `def:pencil-x0-usable-chain`, `lem:pencil-x0-chain-reduces`,
  `lem:pencil-x0-planar-rigid-reduces`, `lem:pencil-x0-sparse-count` (B4);
  `thm:pencil-x0-theorem-s`, `thm:pencil-x0-coverage` (B5).
- `thm:pencil-x0-generic-attains` stays red (MOTIVES).

**The red-node consistency gate, run at this open.** All eleven nodes, statements and proofs, re-read
against the spikes. Every statement is the compiled statement's, every proof routes through the
Lean argument, and every `\uses` label exists and is live. THEOREM-S' six were re-confirmed against
`scratch/40m/Full.lean`. The 40l close checked them against S5, and the one call that changed (the
landed `partitionDef_induce_id_le_of_maximal`, which has no `hWV`) changes no statement. Three
CHAINS proofs get optional rewordings, each in the build that greens its node (checklist).

**The spikes** (gitignored `scratch/40m/`, local to this checkout; builder sources, not evidence;
**keep them**, and `scratch/40l/`). Run with `lake lean` at `e8a37f3e`; the coordinator's re-run
matched:
- `Chains.lean` (1 288 lines; imports `…MainComponent.Coverage`; B1–B3's source): exit 0, no
  warnings, no `sorry` (the word occurs only in comments); `#print axioms` standard on the five
  interface statements, `splitOff` and its four instances, `isChain_one` and `two_le_of_adj`;
  Batteries' `#lint` (14 linters) clean.
- `Full.lean` (1 844 lines; B4–B5's source): `Chains.lean`'s body, then S5's THEOREM-S half verbatim
  but for one edit. Exit 0, no `sorry`, 13 warnings, all in the THEOREM-S half (the fixes are listed
  under B4 and B5). Six axioms lines, all standard, among them `Graph.IsX0Graph.x0Attains` and
  `Graph.X0Attains.of_twoEdgeConnected`. S5's five statements restated verbatim as `example`s
  (lines 1807–1835) are each discharged.
- `Inst.lean`: 40l S6's `IsChain` instance (`K₄` with every edge subdivided twice, chain
  `0 − 4 − 5 − 1`) re-checked over this `Graph.IsChain`: exit 0, one long-line warning (S6's text).
  `gen.py` regenerates `Full.lean` and `Inst.lean` from `Chains.lean`.

## Architectural choices made up front

- **The route** (the recon's verdict; design doc §3 COVERAGE items 2–3). One core in the consumers'
  own format: the maximal ear `Graph.IsOpenEar.exists_maximal` (strong induction on `V₁.ncard`, by
  `IsOpenEar.symm` and `IsOpenEar.cons`) serves chain extraction and the cycle, and BRIDGE runs the
  same extension on a bridge ear with its two sides tracked. The cut arguments go through one gate,
  `Graph.Connected.induce_of_gate`. THEOREM-S is S5's text.
- **Layout: three new leaf modules** in `CombinatorialRigidity/Molecular/Molecule/Pencil/MainComponent/`,
  each added to the root import `CombinatorialRigidity.lean` directly after the
  `…MainComponent.Coverage` line, in order, by the build that creates it:
  `CoverageChain.lean` (imports `…MainComponent.Coverage`; about 740 lines),
  `CoverageCut.lean` (imports `…MainComponent.CoverageChain`; about 680),
  `CoverageTheoremS.lean` (imports `…MainComponent.CoverageCut` and
  `CombinatorialRigidity.Molecular.Induction.SparseDeficiency`; about 590).
- **MOTIVES' interface** (B5): `Graph.IsX0Graph.x0Attains` and `Graph.X0Attains.of_twoEdgeConnected`.

## Lemma checklist

Pins in **bold**. `C` is `scratch/40m/Chains.lean` and `F` is `scratch/40m/Full.lean`; ranges are
inclusive, include each declaration's docstring and exclude the spikes' own section headers. **Every build:** transcribe the listed lines
verbatim in the listed order, under the listed `/-! ## … -/` headers. Put the copyright header and a
module docstring listing the file's statements on a new file. Every declaration gets a docstring
(the spikes omit a few). Open the file with `open scoped Graph`, `namespace
CombinatorialRigidity.Molecular` and `variable {α β : Type*}`, and close it with `end
CombinatorialRigidity.Molecular`. Then the gates of `CombinatorialRigidity/CLAUDE.md` *Before each
commit*: a warning-free `lake build`, `lake lint`, `blueprint/verify.sh` and `blueprint/lint.sh`, and
a `#print axioms` check on each pin.

- [ ] **B1 → new `CoverageChain.lean`** (≈656 spike lines → ≈740). Sections, in order:
  `## Path sequences` ← C 13–65; `## Open ears` ← C 69–195, then C 618–648
  (`IsOpenEar.exists_eq_of_isLink_notMem`, `isLink_first`, `isLink_last`), then C 1114–1121
  (`IsOpenEar.ncard_lt`); `## The maximal ear` ← C 228–235
  (`Graph.Connected.vertexSet_subset_of_forall_adj`), then C 274–342; `## Chains` ← C 346–614;
  `## Plumbing for Theorem S` ← C 1196–1271. Root import: add
  `import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.CoverageChain`.
  - `def:pencil-x0-chain` ← **`Graph.IsChain`**;
  - `lem:pencil-x0-chain-exists` ← **`Graph.IsX0Graph.exists_isChain`**; reword the proof: drop the
    last clause ("and they are distinct, since otherwise their common body would be a cut vertex"),
    since the ends of the path are distinct by construction and the adjacent-ends case is the one
    refuted;
  - `lem:pencil-x0-cycle-reduces` ← **`Graph.IsX0Graph.x0Reduces_of_forall_degree_eq_two`**;
    reword the proof to follow `lem:pencil-x0-chain-exists`' argument: extend a path through a body
    as far as possible along bodies of degree two; as every body has degree two, it stops only when
    its ends are adjacent, and the path with that edge is closed under adjacency, hence all of `G`.
  - No warnings to fix.
- [ ] **B2 → new `CoverageCut.lean`** (≈339 → ≈390). `## Cut arguments` ← C 199–226, then
  C 237–270; `## The standing hypotheses at a chain's smaller graphs` ← C 650–702, then C 969–1112
  (`IsX0Graph.splitOff`), then C 1123–1194 (its four instances). Root import: add
  `import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.CoverageCut`.
  - `lem:pencil-x0-chain-standing` ← **`Graph.IsChain.isX0Graph_induce`,
    `Graph.IsX0Graph.splitOff`**; no rewording, no warnings.
- [ ] **B3 → `CoverageCut.lean`, continued** (≈262 → ≈290). `## BRIDGE` ← C 706–873, with its five
  helpers `bridge_gate_left`, `x0Below_induce_bridge_left`, `bridge_symm`, `bridge_cons` and
  `x0Reduces_of_bridgeEar` made `private`; `## CUT` ← C 877–965.
  - `lem:pencil-x0-cut-reduces` ← **`Graph.IsX0Graph.x0Reduces_of_not_twoEdgeConnected`,
    `Graph.IsX0Graph.x0Reduces_of_not_connected`**; reword the proof. (1): follow the two sides of the
    one edge leaving a set `V′`: an end of degree two extends into its own side, since its other edge
    is not that one. Drop "every edge of that path is a bridge". Say why each side is connected:
    its end is its only body with a neighbour outside it. (2): the side `C` may be any set closed
    under adjacency in `G − v`, as in the Lean, and each side is connected because `v` is its only
    body with a neighbour outside it. No warnings. **CHAINS' five nodes are then green.**
- [ ] **B4 → new `CoverageTheoremS.lean`** (≈310 → ≈350), with `variable {K : Type*} [Field K]`
  besides `{α β : Type*}`. F 1280–1287 (`Graph.ChainUsable`), then `variable [Finite α] [Finite β]`;
  `## The reductions at a usable chain and at a planar-rigid set` ← F 1293–1390;
  `## Counting bodies of degree two` ← F 1392–1522; `## The 4-cycle of a two-body chain` ←
  F 1524–1590. Root import: add
  `import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.CoverageTheoremS`.
  - `def:pencil-x0-usable-chain` ← **`Graph.ChainUsable`**;
  - `lem:pencil-x0-chain-reduces` ← **`Graph.IsChain.x0Reduces_of_chainUsable`**;
  - `lem:pencil-x0-planar-rigid-reduces` ← **`Graph.IsX0Graph.x0Reduces_of_deficiency_two_rigid`**;
  - `lem:pencil-x0-sparse-count` ← **`Graph.IsX0Graph.exists_degree_eq_two_notMem`,
    `Graph.IsX0Graph.partitionDef_three_induce_diff_nonpos`**.
  - **Warnings to fix** (`F` lines): 1340, `Graph.IsOpenEar.deficiency_induce_le` has the section
    variable `[Finite β]` unused (put `omit [Finite β] in` before it); 1459, 1462, 1472, 1481,
    `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (`two_mul_ncard_le_ncard_edgeSet`); in
    `partitionDef_three_induce_diff_nonpos`, 1498 `Set.insert_diff_singleton` →
    `Set.insert_sdiff_singleton`, 1499 `if_neg` → `ite_eq_right` (the same signature) with its
    `by simpa using hxX` → `by simp`, and 1503 `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` and
    `Set.mem_diff` → `Set.mem_sdiff`; 1525, the unused `hG` of
    `Graph.IsOpenEar.deficiency_three_induce_cycle` → `_hG` (its two callers in B5 unchanged).
- [ ] **B5 → `CoverageTheoremS.lean`, continued** (≈214 → ≈240). `## Theorem S and the covering
  theorem` ← F 1594–1805.
  - `thm:pencil-x0-theorem-s` ← **`Graph.IsX0Graph.exists_additiveCore`**;
  - `thm:pencil-x0-coverage` ← **`Graph.IsX0Graph.x0Reduces`, `Graph.IsX0Graph.x0Attains`,
    `Graph.X0Attains.of_twoEdgeConnected`**.
  - **Warnings to fix** (in `exists_additiveCore`): 1702 `Set.ncard_diff_singleton_of_mem` →
    `Set.ncard_sdiff_singleton_of_mem`; 1719, a line over 100 characters. **THEOREM-S' six nodes
    are then green.**
- [ ] **The close** (docs and blueprint), which also closes COVERAGE: the re-read of
  §`sec:main-component-coverage`; the headline axioms on the `formalization.yaml` main results and
  40m's pins, one `#print axioms` line each under `import CombinatorialRigidity` with `lake lean`
  after a full `lake build` (the 40k/40l method); the design doc, ROADMAP and
  `MolecularConjecture.md`; the exposition-ledger candidates. The public surfaces stay unchanged
  (the PI's standing call: they update when Phase 40 closes, at MOTIVES).

## Blockers / open questions

- **None.** The interface statements are S5's (witnessed verbatim in `Full.lean`), so THEOREM-S'
  calls are unchanged, and no REDUCE contract moves.

## Hand-off / next phase

**The next concrete step is B1** (checklist): a fresh builder given `scratch/40m/Chains.lean`
creates `CoverageChain.lean` from the listed lines, adds it to the root import, and pins and greens
`def:pencil-x0-chain`, `lem:pencil-x0-chain-exists` and `lem:pencil-x0-cycle-reduces` with the two
proof rewordings. B2 to B5 follow in order, each against the landed state of the one before, then
the close. **Then MOTIVES** (`X0Dist` and `X0Gen`), which closes Phase 40 and updates the public
surfaces; it opens as its own sub-phase and consumes `Graph.X0Attains.of_twoEdgeConnected`.

## Decisions made during this phase

- **2026-09-28 — opened design-first** from CHAINS' design recon (opus, read-only,
  compiler-checked), whose spikes prove S5's five plumbing statements, with S5's THEOREM-S half
  composing on top. The PI folded THEOREM-S into 40m: one open, B1–B5, one close (verbatim in
  `notes/pencil/adjudications.md`). The recon's flags, settled by precedent (the user's standing
  configuration), are the entries below.
- **File names.** `CoverageChain.lean`, `CoverageCut.lean`, `CoverageTheoremS.lean`, not the
  planned `Chains.lean`/`Cuts.lean`/`Cover.lean`. The first two would sit one letter from the landed
  step files `Chain.lean` and `Cut.lean`, whose theorems these files feed, and `Cover.lean` beside
  `Coverage.lean`. The `Coverage` prefix groups COVERAGE's files with their interface.
- **`exists_isChain` keeps `_hv`** (M4's `_hdeg` precedent), so the statement THEOREM-S calls is
  unchanged. `IsChain.isX0Graph_induce` and a few helpers drop unused `Finite` binders, which weakens
  only hypotheses; call sites are unaffected.
- **Placement.** The helpers stay in the new files (the 40l precedent), and the placement by
  definition is a tracked cleanup-round item (design doc §3 COVERAGE).
- **Reuse.** S5's `eq_or_eq_of_degree_eq_two` is dropped for the landed
  `Graph.isLink_eq_of_degree_eq_two`, and Phase 39's M1–M3 are not adopted (why: design doc §3
  COVERAGE *Lean reuse*).
- **Proof rewordings** land with the builds that green their nodes (B1, B3), not at the open.
