# Phase 40g — PENCIL-X0 / CHAIN: the ear steps and the cycle (work log)

**Status:** in progress (opened design-first 2026-09-27). STEPS' third group (`notes/Phase40-design.md`
§3 STEPS). It lands the base of the `X₀` induction and its two unconditional ear steps: every
cycle attains (BASE, (MC-21)(a)'s base), and if `X₀(G[V₁])` attains, `X₀(G)` attains for an open
ear with `k ≥ 5` interior bodies, its ends possibly adjacent, or a closed ear with `k ≥ 2`
((MC-20)). The design recon's spike proves the whole group sorry-free; it lands in two build
commits (the coordinator's decision). Build 1, the rank and deficiency side, has landed (five of
fourteen nodes green). **Next: build 2, the steps** — see *Hand-off*.

## Current state

**Build 1 landed.** Fourteen nodes, with statements from the spike and `ledger.py --brief` on
(MC-16)–(MC-21), (MC-134) and (MC-177) (Steps MC10, MC13, MC20):
- `rigidity-matrix.tex` §`sec:molecular-rigidity-matrix-blocks`: `def:relative-screws` (green at
  the open: it pins the landed `BodyHingeFramework.relScrews` and `jointRows`, part of Phase 39's
  D5 debt), and, **green since build 1**, `lem:block-rank-two-cut` (four pins: B5′/B6′, then B5/B6
  as their induced corollaries), `lem:block-rank-path`, `lem:block-rank-ear`;
- `deficiency.tex`: `lem:deficiency-ear` (green since build 1);
- `main-component.tex`, the new §`sec:main-component-chain` (before the final statements
  subsection): six red lemmas, the three red theorems `thm:pencil-x0-cycle`,
  `thm:pencil-x0-open-ear`, `thm:pencil-x0-closed-ear`, and `rem:pencil-x0-ear-class`, which
  records that (MC-21)(a)'s class theorem is not stated (PI decision 4).

Build 1 landed the rank and deficiency side in `Bricks.lean`, `Cut.lean` and the new `Ear.lean`
(*Lemma checklist*). **The next concrete commit is build 2** (*Hand-off*): the nine
`main-component.tex` nodes.

**The spike** lives in the gitignored `scratch/40g/`, so it is local to this checkout:
`S40gFull.lean` (2 414 lines) is assembled by `python3 build.py S40gFull.lean S40gRank.lean
S40gDef.lean S40gGeom.lean S40gCert.lean StepA.lean … StepH.lean`, run in that directory; the parts
each import `…MainComponent.Contract`. `S40gAxioms.lean` is the full spike plus five
`#print axioms` lines; `S40gPrereq.lean` holds the step-contract prerequisites (design doc §3 STEPS).
**Since build 1 the assembled spike no longer compiles against the tree**: `S40gRank.lean`'s
`pathVertex_last`, `pathVertex_injective`, `rigidityRows_congr_isLink` and the two motion helpers
now exist in `CombinatorialRigidity.Molecular` (duplicate declarations). Check build 2's parts by
assembling only them, under `import …MainComponent.Ear` (*Hand-off*).
- **`lake lean scratch/40g/S40gFull.lean`** (the coordinator; re-run at `2350dbb0` at this open, ~16
  s): **exit 1, 6 errors, 323 warnings.** All six errors are in `pathVertex_last` (spike line 150)
  and `pathVertex_injective` (line 154), which bind `α` auto-implicitly after `end
  BodyHingeFramework` closed the section's `variable`s; each is a one-line binder fix. The
  warnings are lint debt: 67 "this tactic is never executed", 51 flexible `simp`, 27 unused
  bindings, 22 + 13 deprecated `if_neg`/`if_pos`, 20 long lines, 10 deprecated
  `Set.mem_setOf_eq`, 9 `show` as `change`, and a tail; the seven "declaration uses `sorry`"
  warnings are the error recovery.
- **`lake env lean S40gAxioms.lean`** (the coordinator; it skips the lakefile's options,
  TACTICS-QUIRKS §55): exit 0, 0 errors, 59 warnings, ~15 s, peak RSS 3.3 GB. `of_openEar`,
  `of_cycle`, `of_closedEar` and both instances each print `[propext, Classical.choice,
  Quot.sound]`. No `sorry`/`admit`/`axiom`/`maxHeartbeats` in the source.
- **Satisfiability (kernel-checked, not landed).** θ(1,2,6), a triangle with an open ear of five
  interior bodies on two adjacent bodies (`theta126_x0Attains'`: `of_cycle`, then `of_openEar`),
  and the bowtie, a triangle with a closed 2-ear (`bowtie_x0Attains'`), attain over every infinite
  field with no hypotheses; (H) is proved in Lean for both (spike lines 2 161–2 414). By hand, a
  square with a 5-ear joining opposite corners satisfies `of_openEar` with `a ≁ b`.
- **Faithfulness** (the coordinator, against Step MC10): the ear is `a − x₁ − ⋯ − x_k − b`, open iff
  `a ≠ b`, closed iff `a = b` with `k ≥ 2`; (MC-20) is the closed ear or the open ear with `k ≥ 5`.
  The Lean asks less of `G′` than the workbook ((H) at `G`, attainment at `G[V₁]`, no (H) at `G′`),
  so it is a stronger theorem. BASE's `k ≥ 1` is a cycle of length at least 3.

## Architectural choices made up front

- **The route** (the recon's verdict; design doc §3 STEPS, *CHAIN*):
  - **Rank.** B6′ glues ranks at a 2-cut whose sides are any two graphs partitioning the links
    (the landed B6 takes induced sides, and with `a ∼ b` the induced far side is the path plus `ab`). The path brick (MC-177)(i)(ii)
    holds both ways: rank `(D − 1)(k + 1)`, and `relScrews` is the span of the hinges. So the ear
    rank law, (MC-16) in rank form, holds at every adjacency and every `k`:
    `rank F = rank F[V₁] + (D − 1)(k + 1) + dim(ρ ⊔ Λ) − D`.
  - **Deficiency.** Only (MC-17)'s lower half, `def(G[V₁]) + k + 1 − D ≤ def(G)`, open or closed;
    `Graph.x0Attains_of_exists` supplies the upper rank bound.
  - **Open ear, `k ≥ 5`.** One picture off `G[V₁]`'s attainment polynomial, `G`'s main-picture
    polynomial and the span polynomial `Plam`; heights at a common non-root in `L_G(q)` of `G[V₁]`'s
    restricted attainment polynomial and `Rlam` (`exists_mem_eval_ne_zero₂`); six ear joins give
    `Λ = ⊤`. (MC-19)(b)'s "for any flag pair" becomes a witness inside the fibre: the height `1`
    at `x₂`, `x₃` and `0` elsewhere lies in `L_G(q)` at every admissible `q` (it needs `k ≥ 4`), and
    the hexagon certificate at a collapsed picture (`p_a = p_b`) makes `Plam` nonzero.
  - **BASE.** Every height on `V(G)` lifts (three points impose nothing); certificates for
    `n = 3..6`, and `n ≥ 7` collapses onto the hexagon; the edge `ab` is the path brick at `k = 0`.
  - **Closed ear.** `of_cutVertex` plus `of_cycle` on `G[{c} ∪ range x]`, reusing the ear's labels
    (closing edge `e 0`); no `β`-headroom, and `ChainData` is never needed.
  - Neither step-contract prerequisite is used (design doc §3 STEPS, the step contract).
- **The PI's decisions, verbatim** (2026-09-27; also `notes/pencil/adjudications.md`):

  ```adjudication
  PI decisions, 2026-09-27, on the CHAIN design recon's verdict (verbatim answers to the coordinator's questions):
  1. Placement — "Where should CHAIN's new declarations go? The recon's layout: the 2-cut generalization in RigidityMatrix/Bricks.lean; pathVertex lemmas + a three-point lemma in MainComponent/Cut.lean (922→~1010); the point-join/flat pieces in Flat.lean (692→~870); a new MainComponent/Ear.lean (~960: path brick, ear rank law, ear deficiency bound, certificates) and a new MainComponent/Chain.lean (~890: the three step theorems). Carrier.lean and Contract.lean untouched.": "As listed, B5/B6 in place (Recommended)" — the recon's layout; B5/B6 re-proved as corollaries of the new B5′/B6′ with unchanged statements and pins (40f precedent); Bricks stays near 1450 lines.
  2. Closed ear — "The closed ear (half of (MC-20)) is off (MC-89)'s route: COVERAGE never consumes it. Keep it as a named theorem?": "Named theorem (Recommended)" — keep Graph.X0Attains.of_closedEar (~130 lines, faithful to (MC-20), already spiked: of_cutVertex + of_cycle).
  3. BASE form — "How should BASE (a cycle attains) take its cycle?": "Edge + ear (Recommended)" — as spiked: 'edge ab plus the path a…b', the same explicit-path format as the ear steps. A CycleData adapter (~60 lines) lands later only if COVERAGE's cycle case produces CycleData.
  4. Scope — "The design doc's CHAIN scope lists items CHAIN never consumes: (MC-169), (MC-134)(b) at k ≤ 4, (MC-134)(c), (MC-19)(c), (MC-18)(b), exact (MC-17), and the A2/A3, jointMotions, weldedRank pins; also (MC-21)(a)'s class theorem, which dissolves into COVERAGE's strong induction. What happens to them?": "Move to first consumer (Recommended)" — re-home each item to SHORT or ORBIT, whichever consumes it first; leave (MC-21)(a)'s class theorem unstated (a remark records that it dissolves into COVERAGE).
  ```
- **The coordinator's decision: two build commits, by fresh opus builders, split at the spike's
  part boundary** (the recon's own alternative). Build 1 is `S40gRank.lean` + `S40gDef.lean` (spike
  lines 1–593): the rank and deficiency side, turning the three red `rigidity-matrix.tex` nodes and
  `lem:deficiency-ear` green. Build 2 is `S40gGeom.lean` + `S40gCert.lean` + `StepA`–`StepF` (lines
  594–2 160): the nine `main-component.tex` nodes. Two, because the spike is 2 414 lines with 323
  warnings of lint debt and build 1 re-proves B5/B6 in the fragile zone; 40f's single build of a
  ~1 500-line file took 362k tokens / 59 min.
- **Decision 4's two items with no consumer.** (MC-19)(c) and (MC-134)(c), the closed-ear span, are
  not in (MC-89)'s tree (Step MC20, Part I), and neither SHORT nor ORBIT consumes them; the design
  doc lists them as off the route (§2) rather than naming a consumer.

## Lemma checklist

Planned names from the spike. Pins in **bold**; the other names are helpers, unpinned.

- [x] **`BodyHingeFramework.relScrews`**, **`jointRows`** (landed, Phase 39 item 6) →
  `def:relative-screws`, green at the open.
- [x] **Build 1, `RigidityMatrix/Bricks.lean`** (1 364 lines, the fragile zone): the motion helpers
  `isInfinitesimalMotion_of_eqOn_of_isLink`, `mem_sup_infinitesimalMotions_of_isLink`; B5′
  **`inf_span_rigidityRows_of_twoCut_of_isLink`**, B6′
  **`finrank_span_rigidityRows_twoCut_eq_of_isLink`**; `rigidityRows_congr_isLink`,
  `infinitesimalMotions_congr_isLink`; B5 and B6 re-proved as corollaries, statements and pins
  unchanged (PI decision 1) → `lem:block-rank-two-cut`. *Landed* (1 443 lines): the two motion
  helpers replace B5/B6's private induced-side ones, a private `rigidityRows_eq_union_of_isLink`
  replaces `rigidityRows_eq_union_induce`, and the cut-vertex identity now runs on them;
  `infinitesimalMotions_congr_isLink` was dropped (no use; the hand-off's option).
- [x] **Build 1, `MainComponent/Cut.lean`**: `pathVertex_last`, `pathVertex_injective` (helpers).
  *Landed*, with `image_val_lt_eq_range` un-privated.
- [x] **Build 1, new `MainComponent/Ear.lean`**: the path brick
  **`BodyHingeFramework.le_finrank_span_rigidityRows_path`**, **`finrank_span_rigidityRows_path_le`**,
  **`span_range_le_relScrews_path`**, **`relScrews_path_le_span_range`** → `lem:block-rank-path`;
  the ear rank law **`BodyHingeFramework.finrank_span_rigidityRows_ear_eq`** → `lem:block-rank-ear`;
  **`Graph.deficiency_induce_add_le_of_ear`** (helper `ncard_range_le_of_fin`) →
  `lem:deficiency-ear`. *Landed*; the helper is inlined (`Finite.card_range_le`), and
  `Set.ncard_range_le` is a FRICTION mirror candidate.
- [ ] **Build 2, `Cut.lean`**: **`Graph.IsAdmissiblePicture.exists_dotProduct_of_ncard_closedNbhd_le_three`**
  → `lem:pencil-three-points`; `pathVertex_eq_x_iff`, `pathVertex_val_succ`, `pathVertex_shift`.
- [ ] **Build 2, `Flat.lean`**: **`pointJoin`**, **`flatScrewEquiv_pointJoin`**,
  **`linearIndependent_pointJoin_of_flat`** → `lem:pencil-join-flat`; `flatCoords`,
  `joinPicturePoly`, `joinHeightPoly` and their `eval` lemmas,
  **`exists_mvPolynomial_linearIndependent_pointJoin_picture`**, **`…_heights`** →
  `lem:pencil-join-independence-open`.
- [ ] **Build 2, `Ear.lean`**: **`Graph.earExtend_mem_liftingSpace`**,
  **`Graph.mem_liftingSpace_of_ear`**; `closedNbhd_ear_subset`, `ncard_closedNbhd_ear_le_three`,
  `mem_closedNbhd_induce_of_ear` → `lem:pencil-ear-fibre`; `certPt`, the four
  `linearIndependent_flat_*`, **`linearIndependent_pointJoin_cert{Triangle,Square,Pentagon,Hexagon}`**
  → `lem:pencil-chain-span-certificates`; **`span_supportExtensor_eq_top_of_linearIndependent`**,
  **`card_le_finrank_of_linearIndependent_pointJoin`**; `panelSupportExtensor_mem_span_ofNormals`,
  `screwComplementIso_pointJoin`, `ear_isLink_{first,mid,last}` → `lem:pencil-ear-hinge-span`.
- [ ] **Build 2, new `MainComponent/Chain.lean`**: **`Graph.X0Attains.of_cycle`**
  (`of_cycle_of_certificate`, `closedNbhd_cycle_subset`, `certPicture`, `certHeights`,
  `pencilConfigPoint_cert`) → `thm:pencil-x0-cycle`; **`Graph.X0Attains.of_openEar`** →
  `thm:pencil-x0-open-ear`; **`Graph.X0Attains.of_closedEar`** → `thm:pencil-x0-closed-ear`.
- [ ] **The close** (docs and blueprint only): the end-to-end re-read of the new subsection, the
  exposition ledger (a candidate: the witness inside the fibre that replaces (MC-19)(b)'s "for any
  flag pair"), the headline axioms, the design doc's §3 STEPS, ROADMAP; the public surfaces stay
  unchanged (the PI's standing call, recorded at 40f's close).
- **Not landed:** the instances (`StepG`, `StepH`) and `S40gPrereq.lean`.

## Blockers / open questions

- None. The spike compiles the whole group; what remains is transcription with the placement.

## Hand-off / next phase

**Next: build 2 — the steps (fresh opus builder).** Source: `scratch/40g/S40gGeom.lean`,
`S40gCert.lean` and `StepA`–`StepF.lean`, spike lines 594–2 160 (gitignored, local to this
checkout). Targets: the nine `main-component.tex` nodes of §`sec:main-component-chain`
(`lem:pencil-three-points` through `thm:pencil-x0-closed-ear`). Chores:
- **Check the parts first, without build 1's.** Assemble only build 2's parts under
  `import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Ear` (`build.py` hard-codes
  `…Contract`; edit its first part) and `lake lean` the result (TACTICS-QUIRKS §55): `S40gRank.lean`
  and `S40gDef.lean` now duplicate landed names. The spike's `image_val_lt_eq_range'` is the landed
  `image_val_lt_eq_range`, and `StepD.lean`'s `ncard_range_le_of_fin e` was not landed: use
  `rw [← Nat.card_coe_set_eq]; exact (Finite.card_range_le _).trans (by simp)`, as in
  `Graph.deficiency_induce_add_le_of_ear`, or land the FRICTION mirror candidate `Set.ncard_range_le`.
- **Placement** (the checklist's names and files): `Cut.lean`, `Flat.lean`, `Ear.lean`, and the new
  `Chain.lean` importing `…MainComponent.Ear`, with the root import after `Ear`.
- **Lint debt.** In build 1's share of the spike the "never executed" and unused-binding warnings
  were all error recovery from the two `α` binders; the real debt was the deprecated
  `if_pos`/`if_neg`/`dif_pos` (→ `ite_eq_left`/`ite_eq_right`/`dite_eq_left`), `Set.mem_setOf_eq`
  (→ `Set.mem_ofPred_eq`) and long lines. Judge by `lake build` and `lake lint`.
- **Fragile spots**, from the recon: the polynomial engine times out at `W = ScrewSpace K 2`
  (transcribe the spike's fix: named polynomial defs, `set`, explicit `(W := …)`);
  `LinearMap.linearIndependent_iff` at `flatScrewEquiv` times out (the spike uses
  `LinearIndependent.of_comp`); `λ` is a keyword (the spike's `Plam`, `Rlam`).
- **Docstrings, pins, gates** as for build 1: a module docstring for `Chain.lean`, one per
  declaration, pin and flip the nine nodes; `lake build`, `lake lint`, `blueprint/verify.sh`,
  `blueprint/lint.sh`, `notes/check-phase-note.py`.

**Then the close** (the checklist's last item).

## Decisions made during this phase

- **2026-09-27 — opened design-first from one opus recon** (read-only, 718k tokens / 176 tools /
  78 min). The coordinator re-ran its spike under both `lake env lean` and `lake lean` (*Current
  state*), checked its statements against Step MC10, and chose two build commits. The recon's
  verdict is in the design doc's §3 STEPS.
- **2026-09-27 — build 1 landed** (the rank and deficiency side, one fresh opus builder). The
  spike's proofs, with the binder fix, the deprecated names replaced and one `nlinarith` → `omega`.
  B5′/B6′ are stated over any two link-partitioning graphs; B5/B6 are now one-term corollaries and
  the cut-vertex identity runs on the general helpers, so the induced-side privates are gone. The
  2-cut layer's section docstring now records `def:relative-screws`/`lem:block-rank-two-cut` as its
  pins. FRICTION: the `Set.ncard_range_le` mirror candidate (deferred: its mirror file sits under
  `Framework.lean`) and one elaboration idiom.
