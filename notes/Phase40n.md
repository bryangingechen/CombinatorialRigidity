# Phase 40n — PENCIL-X0 / MOTIVES-DIST+BASE: the distinct statement, and the generic realization without a planar-rigid set (work log)

**Status:** B1–B3 landed (2026-09-28), and with them **all four 40n nodes are green and pinned** —
`def:pencil-two-ear-graph`, `lem:pencil-x0-planes-separate`, `lem:pencil-x0-conjunct-three`,
`thm:pencil-x0-base-generic`. **BASE is done. Next concrete task: the 40n phase-close**
(`PHASE-BOUNDARIES.md` *When this commit closes a phase*) — see *Hand-off*. MOTIVES' first of three
sub-phases (the PI's call, 2026-09-28, `notes/pencil/adjudications.md`; plan
`notes/Phase40-design.md` §3 MOTIVES): **DIST+BASE**, then **EARS** and **REDUCE+CLOSE** by code.
MOTIVES proves `X0Dist` and `X0Gen` by route B, (MC-183)–(MC-189) in
`notes/pencil/workbook/K-main-MC19.md`, second-read 2026-09-28. **M0 landed** (four nodes green),
so did **the second read** (no gap; BASE compiled sorry-free), and so did **B1–B3** (one build,
warning-free, in `MainComponent/GenericBase.lean`).

## Current state

**M0 landed** (four nodes green: `lem:pencil-x0-distinct-statement`,
`lem:pencil-feasible-hub-conditions`, `lem:pencil-three-bodies-no-rigid`,
`lem:pencil-x0-two-hubs-obstruction`, the last pinning both obstruction declarations). **The second
read landed** (2026-09-28, docs only): every claim confirmed, (MC-183), (MC-184), (MC-186) repaired in
place, (MC-188), (MC-189) added, and `lem:pencil-x0-planes-separate`, `lem:pencil-x0-conjunct-three`
(restated at (MC-189)'s weaker hypotheses, which the build lands) and `thm:pencil-x0-base-generic`
reworded. **B1–B3 landed** (2026-09-28): `MainComponent/GenericBase.lean` (transcribed from
`scratch/40n-read/BaseFull.lean` plus `GenBase.lean`'s `[Finite α]` wrapper), warning-free
(`lake build`, `lake lint`), wired into the root import (`CombinatorialRigidity.lean`) so
`checkdecls` sees it. All four 40n nodes are `\lean{…}` + `\leanok` (statement and proof):
`def:pencil-two-ear-graph` → `Graph.addTwoEar`; `lem:pencil-x0-planes-separate` →
`exists_planes_separate` (its statement dropped a spurious "is admissible" conjunct the Lean
conclusion never proves — the admissibility in `thm:pencil-x0-base-generic`'s proof comes from the
attaining polynomial, not this lemma); `lem:pencil-x0-conjunct-three` →
`isNondeg_pencilConfig_of_planeDiff`; `thm:pencil-x0-base-generic` →
`Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero` (the `[Finite α]`
wrapper; the pin, per the checklist). Otherwise `blueprint/src/chapter/main-component.tex`
§`sec:main-component-statements` stays as transcribed at open: the remaining ten new nodes and the
rewritten `thm:pencil-x0-generic-attains` are red and unpinned (the 40h/40l convention), with
`thm:pencil-conjecture` red in `pencil.tex`. **Next concrete task: the 40n phase-close**
(`PHASE-BOUNDARIES.md`), not a build — see *Hand-off*.
Which sub-phase greens each remaining node:
- **40n — done:** `def:pencil-two-ear-graph`, `lem:pencil-x0-planes-separate`,
  `lem:pencil-x0-conjunct-three`, `thm:pencil-x0-base-generic`.
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
- [x] **B1–B3, one build** (landed 2026-09-28: transcribed from `scratch/40n-read/BaseFull.lean`,
  plus lint cleanup — 20 missing docstrings added, 3 deprecated names repointed
  (`Set.mem_ofPred_eq`, `Set.insert_sdiff_singleton`, `Set.ncard_sdiff_singleton_of_mem`), the
  `haveI`→`have` style hit, one long module-title line wrapped, both flexible `simp`s converted to
  explicit `simp only [...]` sets (verified goal-for-goal via the Lean LSP MCP's `simp?`), and the
  two `unusedFintypeInType` hits `set_option`-suppressed with a one-line justification (`[Fintype α]`
  / `[Fintype ι]` are genuinely needed in the proof body but never re-mentioned in the type, so the
  linter's shallow type-only check can't see it) — all in the new `MainComponent/GenericBase.lean` (imports
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

- None. B1–B3 are landed and pinned; 40n's build work is complete. The next step is administrative
  (the phase-close checklist), not a build.

## Hand-off / next phase

1. **M0 — done**; **the second read — done**; **B1–B3 — done** (see the checklist): all four 40n
   nodes are green, pinned, and warning-free.
2. **Next: the 40n phase-close** (`PHASE-BOUNDARIES.md` *When this commit closes a phase*): flip +
   re-thin the ROADMAP Phase-40 row's 40n clause, compress this note to the closed-phase archive
   shape, sync the user-facing status surfaces (`formalization.yaml` incl. `#print axioms` on the
   four pins), and do the end-to-end blueprint-chapter re-read (the ten remaining red
   `sec:main-component-statements` nodes and `thm:pencil-conjecture` stay red — EARS' and
   REDUCE+CLOSE's work, not 40n's).
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
- **2026-09-28 — B1–B3 landed**: `GenericBase.lean` imports `Pencil/X0.lean` (for
  `linearIndepOn_triple_of_linearIndependent`, only reachable via `X0 → Pair2 → Steer`) and
  `MainComponent/CoverageTheoremS.lean` (everything else) — the same pair `Statements.lean` uses.
  Both flexible `simp`s needed a hand-verified `simp only` set (`FRICTION.md` *third instance* of the
  `<;>`-chain idiom); the linter's own "Try this" is a per-goal delta, not a drop-in replacement.
  `lem:pencil-x0-planes-separate` dropped
  a stale "is admissible" conjunct the landed lemma never proves (admissibility comes from the
  attaining polynomial, not this lemma) — caught re-checking the node against the declaration.
