# Phase 40e — PENCIL-X0 / CUT/BRIDGE: cut vertices and bridges (work log)

**Status:** in progress (opened design-first 2026-09-26). STEPS' first group (`notes/Phase40-design.md`
§3 STEPS). It lands the standing hypotheses (H) in Lean and the CUT and BRIDGE steps, (MC-52) and
(MC-53): a cut vertex or a chain of bridges is a fibre product, so `X₀` attaining at both pieces
gives it at `G`. Build 1 landed (H), CUT and the single bridge; build 2 landed BRIDGE along a chain
of bridges of any length. **All nine nodes are green.** **The next concrete commit is 40e's close**
— see *Hand-off*.

## Current state

**Every node is green.** Nine nodes, with statements from `ledger.py --brief '(MC-52)' '(MC-53)'`
and the (H) header of `K-main.md`: seven in `main-component.tex` §`sec:main-component-cut`,
`lem:deficiency-cut-vertex` in `deficiency.tex`, `lem:block-rank-cut-vertex` in
`rigidity-matrix.tex`. The headline theorems are `Graph.X0Attains.of_cutVertex` (CUT) and
`Graph.X0Attains.of_bridgePath` (BRIDGE, any `k ≥ 0`), both `[propext, Classical.choice,
Quot.sound]`. The single bridge is BRIDGE at `k = 0`; build 1's separate `k = 0` declarations were
deleted (*Lemma checklist*). Two consumed laws gained pins on existing nodes in build 2: the pendant
rank law on `lem:block-rank-cut`, the Phase 39 pendant deficiency law
`Graph.deficiency_induce_union_singleton` on `lem:cut-edge-decomposition`.
**The next concrete commit is 40e's close** (*Hand-off*).

## Architectural choices made up front

The coordinator's adjudication (2026-09-26) of the STEPS pre-build recon (one opus pass; the verdicts
are in `notes/Phase40-design.md` §3 STEPS):

- **The step contract.** A step concludes `G.X0Attains K` from `Gᵢ.X0Attains K` at smaller graphs in
  the same `Graph α β`. It picks one picture generic for the pieces and main for `G`, chooses heights
  in one fibre (`MvPolynomial.exists_mem_eval_ne_zero₂`), and ends at `Graph.x0Attains_of_exists`.
  CUT and BRIDGE need nothing of the pieces beyond `X0Attains`; (H) at `G` gives its main-picture
  polynomial.
- **(H) is `Graph.IsX0Graph`** (simple, connected, degree `≥ 2`), the working name kept; `h3` follows.
- **BRIDGE for `k ≥ 1`: explicit path hypotheses**, not a chain structure. The chain type is
  designed at CHAIN's open, with its consumers (the ears, COVERAGE's chain detection).
- **The PI's decisions, verbatim** (2026-09-26; also `notes/pencil/adjudications.md`):

  ```adjudication
  PI decisions, 2026-09-26, on this recon's verdict (verbatim answers to the coordinator's questions):
  1. ORBIT risk: "After 40e opens+builds" — land 40e's open and its CUT/BRIDGE build first, then the read-only ORBIT recon (opus) before the next sub-phase opens.
  2. Grouping: "Accept" — 40e = CUT/BRIDGE; the six later groups go into the design doc as a provisional order, with letters minted only as each opens.
  3. Placement: "Deficiency/Bricks" — the cut-vertex deficiency laws in `Molecular/Deficiency.lean` and the rank identity in `Bricks.lean`, per the ROADMAP convention (a lemma lives with its definition), as FLAT did in 40c.
  4. CUT/BRIDGE faithfulness: "Let's formalize the if and leave only if as an explicit todo item."
  ```

## Lemma checklist

All landed with the standard axioms except the tracked last item.

- [x] **(H)**: `Graph.IsX0Graph` (+ `three_le_ncard_closedNbhd`) → `def:pencil-x0-standing`.
- [x] **Rank congruence** → `lem:pencil-rank-congr`; **restriction** → `lem:pencil-lifting-restrict`.
- [x] **Cut vertex** (build 1): deficiency (`Deficiency.lean`, pinning Phase 39's
  `partitionDef_split_of_vertexTwoCut`), rank (`Bricks.lean`), fibre, and CUT
  `Graph.X0Attains.of_cutVertex` → `lem:deficiency-cut-vertex`, `lem:block-rank-cut-vertex`,
  `lem:pencil-cut-fibre`, `thm:pencil-x0-cut`.
- [x] **Single bridge** (build 1, retired in build 2): `exists_dotProduct_eq_of_linearIndependent`,
  `Graph.exists_liftingRestrict_eq_of_bridge` and `Graph.X0Attains.of_bridge` were deleted once
  BRIDGE landed for every `k` — unpinned and unused; this line is their retirement record.
- [x] **The fibre lemma** (build 2): `pathVertex`, `Graph.exists_liftingRestrict_eq_of_bridgePath`
  → `lem:pencil-bridge-fibre`.
- [x] **BRIDGE** (build 2): `Graph.X0Attains.of_bridgePath`, with `pathVertex_cases` /
  `_eq_of_val_eq_succ` / `_rev` / `_mem_union_image_iff`, `Graph.cutEdges_union_image_of_bridgePath`
  and the two path telescopes → `thm:pencil-x0-bridge`; the pendant rank law
  `BodyHingeFramework.add_le_finrank_span_rigidityRows_induce_union_singleton` (`Bricks.lean`) →
  `lem:block-rank-cut`.
- [ ] **Tracked, not a close gate:** the "only if" halves of (MC-52)(iv) and (MC-53)(iv)
  (`notes/Phase40-design.md` §3 STEPS). They carry forward past the close as a tracked item, in the
  design doc, not as a 40e node.

## Blockers / open questions

- None.

## Hand-off / next phase

**Next: 40e's close**, one commit, running `PHASE-BOUNDARIES.md` *When this commit closes a phase*:

- Flip the ROADMAP Status row (`40e/CUTBRIDGE ✓`) and compress §40e to a closed-phase summary; the
  row's next item is the read-only ORBIT recon (below).
- Sync the user-facing status surfaces (`python3 notes/phasenote.py 40e --surfaces` lists them), with
  `formalization.yaml` aligned by `#print axioms` on the headline theorems
  `Graph.X0Attains.of_cutVertex` and `Graph.X0Attains.of_bridgePath`.
- Re-read `main-component.tex` §`sec:main-component-cut` end to end and write the
  `notes/BlueprintExposition.md` entry (the fibre lemma's gateway argument, which replaced the
  informal three-case proof, is the candidate hard node), then the project-organization review.
- Move the "only if" item to the design doc's STEPS tracking, so no open item strands under a
  closed phase.

**Then** the read-only ORBIT recon (opus) runs before the next group opens (PI decision 1).
`scratch/` still holds `S40eTracked.lean`'s `rigidContract_induce_simple` (CONTRACT-R) and the
curve-limit lemma (SPLITOFF), for those groups; the coordinator removes `scratch/` once 40e no
longer needs it. Gates for the close: `lake build`, `lake lint`, `blueprint/verify.sh`,
`blueprint/lint.sh`, `python3 notes/check-phase-note.py`.

## Decisions made during this phase

- **2026-09-26 — opened design-first from one opus recon.** The coordinator re-ran its three spike
  files: exit 0, no warnings, no `sorry`. The six tracked items are settled in
  `notes/Phase40-design.md` §3 STEPS, and the later groups are recorded there by code.
- **2026-09-26 — build 1: the spike transcribed.** Cut-vertex deficiency laws at the end of
  `Deficiency.lean`; the rank identity in `Bricks.lean`'s 2-cut section, shorter than the spike's via
  the private helpers `mem_sup_infinitesimalMotions_induce` and `rigidityRows_eq_union_induce`.
- **2026-09-26 — build 2's first half: the fibre lemma re-derived, not transcribed.** The informal
  proof splits on `k = 0, 1, ≥ 2`; extending `z₁` by the affine function witnessing its own condition
  at `a` (`V₁`'s unique gateway) works for every `k` with no admissibility. Blueprint prose rewritten.
- **2026-09-26 — build 2's second half: BRIDGE by one cut and a telescope.** A recon ruled out an
  `X0Attains` induction (a peeled body has no admissible picture). The theorem cuts once at the last
  bridge (`V₁ ∪ range x` against `V₂`) and telescopes over the prefixes `V₁ ∪ {x i | i < j}`, each
  left by the next path edge only; index arithmetic by value (`pathVertex_cases`, `omega`), the `V₂`
  side along the reversed path. Placement: the rank step in `Bricks.lean` (PI decision 3; 44
  downstream modules, ~6.5 min rebuilt), no `Deficiency.lean` edit (Phase 39's law already existed).
