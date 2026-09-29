# Phase 40n — PENCIL-X0 / MOTIVES-DIST+BASE: the distinct statement, and the generic realization without a planar-rigid set (work log)

**Status:** in progress (opened design-first 2026-09-28). MOTIVES' first of three sub-phases (the
PI's call, 2026-09-28, `notes/pencil/adjudications.md`; plan `notes/Phase40-design.md` §3 MOTIVES):
**DIST+BASE**, then **EARS** and **REDUCE+CLOSE** by code. MOTIVES proves `X0Dist` and `X0Gen` by
route B, (MC-183)–(MC-189) in `notes/pencil/workbook/K-main-MC19.md`, second-read 2026-09-28. **M0
landed** (four nodes green), and so did **the second read** (no gap; BASE compiled sorry-free).
**Next: B1–B3 as one build** from `scratch/40n-read/BaseFull.lean`, by one fresh builder handed the
file — see *Hand-off*.

## Current state

**M0 landed** (four nodes green: `lem:pencil-x0-distinct-statement`,
`lem:pencil-feasible-hub-conditions`, `lem:pencil-three-bodies-no-rigid`,
`lem:pencil-x0-two-hubs-obstruction`, the last pinning both obstruction declarations). **The second
read landed** (2026-09-28, docs only): every claim confirmed, (MC-183), (MC-184), (MC-186) repaired in
place, (MC-188), (MC-189) added, and `lem:pencil-x0-planes-separate`, `lem:pencil-x0-conjunct-three`
(restated at (MC-189)'s weaker hypotheses, which the build lands) and `thm:pencil-x0-base-generic`
reworded. Otherwise `blueprint/src/chapter/main-component.tex` §`sec:main-component-statements`
stays as transcribed at open: the remaining ten new nodes and the rewritten
`thm:pencil-x0-generic-attains` are red and unpinned (the 40h/40l convention), with
`thm:pencil-conjecture` red in `pencil.tex`. Each build adds its nodes' `\lean{…}` and `\leanok`
(statement and proof). **Next concrete commit: B1–B3 in one build** from the sorry-free
`scratch/40n-read/BaseFull.lean` (see the checklist), which greens the four 40n nodes and closes 40n.
Which sub-phase greens each remaining node:
- **40n:** `def:pencil-two-ear-graph`, `lem:pencil-x0-planes-separate`,
  `lem:pencil-x0-conjunct-three`, `thm:pencil-x0-base-generic` (all in the one B1–B3 build).
- **EARS:** `lem:pencil-generic-steer`, `lem:pencil-generic-one-ear`,
  `lem:pencil-generic-pendant-triangle`.
- **REDUCE+CLOSE:** `lem:pencil-rigid-good-ear`, `thm:pencil-generic-step`,
  `thm:pencil-conditioned-pair-nonempty`, `thm:pencil-x0-generic-attains`, `thm:pencil-conjecture`.
- **Planned pins past 40n** (the spikes' names; EARS' steering names are its own): one-ear ←
  `Graph.IsOpenEar.hasGenericPencilRealization_of_one`, `…_of_isNondegPencilRealization`;
  pendant triangle ← `hasGenericPencilRealization_of_closedEar_two`; good ear ←
  `Graph.IsX0Graph.exists_oneEar_or_pendantTriangle`; generic step ←
  `hasGenericPencilRealization_of_IH`; nonempty pair ← `pencilPair_of_nonempty`; generic attains ←
  `x0Gen`; the conjecture ← `pencil_conjecture`, `pencilPair_of_nonempty`.

**The red-node consistency gate, run at this open.** Every node was written at this open from the
ledger's statements ((MC-9), (MC-12), (MC-13), (MC-123), (MC-127), (MC-129), (MC-157),
(MC-183)–(MC-187)) and the compiled spikes. Each proof routes through route B, and every `\uses`
label exists and is live. `thm:pencil-x0-generic-attains`' old proof (the fibre intersection at every
graph) is replaced, and its statement keeps COVERAGE's first sentence. The dep graph has no cycle:
the generic statement rests on `thm:pencil-conditioned-pair-nonempty`, and `thm:pencil-conjecture`
on both.

**The spikes** (gitignored, local to this checkout; builder sources, not evidence; **keep them**).
- **The second read's, `scratch/40n-read/`, at `8a0752d7`** (`lake lean`; the coordinator's re-run
  matched: exit 0, no `sorryAx` where none is listed):
  - `BaseFull.lean` (791 lines): **B1–B3 whole, sorry-free**, standard axioms on
    `exists_planes_separate`, `isNondeg_pencilConfig_of_planeDiff` and
    `hasGenericPencilRealization_of_forall_deficiency_two_ne_zero'` (the `[Fintype α]` form). Its
    parts: `PlanesSeparateFull.lean` (B1 and B2), `ConjThree.lean` ((MC-189)), `DefLeaf.lean`.
  - `GenBase.lean` (954 lines; **EARS' and REDUCE+CLOSE's source**): `BaseFull.lean` plus `Gen.lean`'s
    composition with the base discharged at the `[Finite α]` signature (l.792); exactly three
    `sorry`s, (MC-129) (l.803), (MC-127)(a) (l.822) and (MC-127)(b) (l.835).
  - `WitnessGen.lean` ((MC-188), EARS' T2 witness), `Landed.lean` (M0's pins and `K23.lean`'s
    witness shrinking), `GenHead.lean` (`Gen.lean` without the names M0 landed).
- **The opening recon's, `scratch/40n/`, at `c2b74e61`:** `OneEar.lean` (368 lines; EARS' Z1 source;
  still exit 0 at `8a0752d7`) and `Apex.lean` (24 lines). **`Gen.lean`, `K23.lean` and `Headline.lean`
  are stale at HEAD**: they redeclare names M0 landed and fail with "has already been declared". Use
  `GenBase.lean` in their place.

## Architectural choices made up front

- **Route B** ((MC-183)): the generic conjunct at a simple 2EC feasible graph is proved inside
  `Graph.pencil_reduction`'s induction, from `PencilPair` at every smaller graph; the landed cut arm
  covers the non-2EC graphs. `X0Gen` is a corollary of `pencilPair_of_nonempty`.
- **Both headlines** (PI): `pencil_conjecture := pencil_conjecture_of_X0 x0Dist x0Gen` and
  `pencilPair_of_nonempty`, landed at REDUCE+CLOSE. `pencil_conjecture_of_X0Gen` does not land (the
  coordinator's call: superseded at the close, no consumer).
- **`G_e`** (PI): `Graph.addTwoEar G u w := G.apex ↾ (Sum.inl '' E(G) ∪ {Sum.inr u, Sum.inr w})`,
  on `Option α` and `β ⊕ α`, importing `Matroid.Graph.Constructions.Sum`. No headroom anywhere.
- **Placement** (the PI's convention: general pieces beside their definitions, the steps in new files
  under `Molecule/Pencil/MainComponent/`), with one exception (the coordinator's call, *Decisions*):
  `Graph.addTwoEar` and its API go in the new `MainComponent/GenericBase.lean`, not `Bridge.lean`.
  The final assembly file is `MainComponent/Statements.lean` (not `Motives`, one letter from
  `Pencil/Motive.lean`).

## Lemma checklist

Pins in **bold**. **Every build:** the gates of `CombinatorialRigidity/CLAUDE.md` *Before each
commit*: a warning-free `lake build`, `lake lint`, `blueprint/verify.sh`, `blueprint/lint.sh`, and a
`#print axioms` check on each pin. New files get the copyright header and a module docstring listing
their statements; every declaration gets a docstring.

- [x] **M0** (sonnet-rated transcription; greens four nodes — landed): `x0Dist`
  (`MainComponent/Statements.lean`), `PencilNondegFeasible.hub_conditions` and the two-hubs
  obstruction (`Pencil/Motive.lean`, `MainComponent/Configuration.lean`),
  `Graph.noRigid_of_simple_of_ncard_eq_three` (`Induction/ReducibleVertex.lean`), verbatim from the
  opening recon's spikes.
- [x] **The second read of (MC-183)–(MC-187)** (a fresh read-only reader, 2026-09-28; verdict in
  Step MC19's route-B header; (MC-188), (MC-189) added; BASE compiled sorry-free).
- [ ] **B1–B3, one build** (one fresh builder handed `scratch/40n-read/BaseFull.lean`; transcription
  plus lint cleanup: the spike carries flexible-`simp` and deprecation warnings, and uses `[Fintype α]`
  where the pins below say so), all in the new `MainComponent/GenericBase.lean` (imports
  `Matroid.Graph.Constructions.Sum`; root import alphabetical among `MainComponent`):
  - **B1** → `def:pencil-two-ear-graph`: **`Graph.addTwoEar`** (← `Apex.lean` 13–15) and its API:
    simplicity (`apex_simple_iff` and restriction; no `u ≠ w`), the vertex set, the links, the closed
    neighbourhoods (each has at least three members, which needs `u ≠ w`), and the injection stated
    as **`finrank_ker_inf_planeDiff_le`**: `finrank (ker M_G(q) ⊓ ker (planeDiff u w)) ≤
    finrank ker M_{G_e}(extPicture q q_x)`, on the lifting systems' kernels, not into `L(G_e)`.
  - **B2** → `lem:pencil-x0-planes-separate`, (MC-184): `def₂(G_e) + 1 ≤ def₂(G)` (a representative
    labelling by Hilbert choice; `partitionDef_add_partitionDef_induce_id_le`,
    `one_le_partitionDef_induce_id`), then BRIDGE's equality at `G` and `G_e`, the new body fixed at
    one non-root. Target shape, **with `[Fintype α]`** (`mulVecLin` needs it): `∃ P : MvPolynomial
    (α × Fin 2) K, P ≠ 0 ∧ ∀ q, MvPolynomial.eval q P ≠ 0 → ∃ x ∈ LinearMap.ker
    ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin, planeDiff u w x ≠ 0`, under
    `G.Simple`, `∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard`, `∀ Y ⊆ V(G), 2 ≤ Y.ncard →
    (G.induce Y).deficiency 2 ≠ 0` and `u ≠ w` in `V(G)`.
  - **B3** → `lem:pencil-x0-conjunct-three` ((MC-189), at its weaker hypotheses: admissibility, every
    `|closedHubNbhd| ≤ 3`, `[Finite β]`; no (H), no feasibility) and `thm:pencil-x0-base-generic`:
    **`Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero`**, exactly
    `Gen.lean` 31–36 (`[Infinite K] [Finite α] [Finite β]`, `hG`, `hfeas`, `hS`; `GenBase.lean`
    l.792's wrapper over the `[Fintype α]` form). The spike takes every pair and every triple of
    distinct bodies, not only the hub ones; the new helpers are the determinant polynomial and the
    finite fibre intersection `exists_mem_forall_eval_ne_zero`.

## Blockers / open questions

- None. B1–B3 are no longer unspiked: the second read's `BaseFull.lean` is the build, less placement,
  docstrings and lint. Keeping `import Matroid.Graph.Constructions.Sum` out of `Bridge.lean` (see
  *Decisions*) leaves the new import's only downstream the new leaf file.

## Hand-off / next phase

1. **M0 — done**; **the second read — done** (see the checklist).
2. **Next: B1–B3 as one build**: dispatch one fresh builder, handed `scratch/40n-read/BaseFull.lean`,
   to land it in `MainComponent/GenericBase.lean` with the pins above, greening the four 40n nodes.
   That build closes 40n (phase-close checklist, `PHASE-BOUNDARIES.md`).
3. Then **EARS** opens by code (letter minted then): T1 (the reseed at given selectors), T2 (the
   witness `WitnessGen.lean` proves, (MC-188)), T3, Z1 from `OneEar.lean`, Z2; then REDUCE+CLOSE,
   both transcribing the assembly from `scratch/40n-read/GenBase.lean`.

## Decisions made during this phase

- **2026-09-28 — opened design-first** from MOTIVES' pre-build recon (opus, read-only,
  compiler-checked; verdict in the design doc §3 MOTIVES). The PI's three calls (the split, `G_e`,
  both headlines) are verbatim in `notes/pencil/adjudications.md`. Route B's claims were written as
  (MC-183)–(MC-187), awaiting a second read; the coordinator ruled out landing
  `pencil_conjecture_of_X0Gen`.
- **2026-09-28 — M0 landed**: `x0Dist`, `PencilNondegFeasible.hub_conditions`,
  `Graph.noRigid_of_simple_of_ncard_eq_three`, and the two-hubs obstruction (statement and
  configuration forms) transcribed verbatim from the compiler-checked spikes, at the coordinator's
  named placements. `K23.lean`'s witness-shrinking tail and `pencil_conjecture_of_X0Gen` do not
  land (unconsumed).
- **2026-09-28 — the second read** (opus, fresh, read-only; verdict in Step MC19's route-B header):
  no refutation, no gap; (MC-183), (MC-184), (MC-186) repaired in place, (MC-188) and (MC-189) added.
  It compiled BASE sorry-free, so B1–B3 land as one build from `BaseFull.lean` rather than three
  spiked builds. `lem:pencil-x0-conjunct-three` is restated at (MC-189)'s hypotheses so its pin will
  match.
- **2026-09-28 — `Graph.addTwoEar` in `GenericBase.lean`, not beside `embedEdges`** (the
  coordinator's call): this keeps `import Matroid.Graph.Constructions.Sum` out of `Bridge.lean`'s
  downstream import cone (`Cut.lean` onward), where a changed `simp` set would show only in a full
  build. It departs from the beside-their-definitions convention for that reason; the PI's `apex`
  construction stands.
