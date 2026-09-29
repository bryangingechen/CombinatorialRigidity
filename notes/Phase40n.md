# Phase 40n — PENCIL-X0 / MOTIVES-DIST+BASE: the distinct statement, and the generic realization without a planar-rigid set (work log)

**Status:** in progress (opened design-first 2026-09-28). MOTIVES' first of three sub-phases (the
PI's call, 2026-09-28, `notes/pencil/adjudications.md`; plan `notes/Phase40-design.md` §3 MOTIVES):
**DIST+BASE**, then **EARS** and **REDUCE+CLOSE** by code. MOTIVES proves `X0Dist` and `X0Gen` by
route B, (MC-183)–(MC-187) in `notes/pencil/workbook/K-main-MC19.md`, awaiting a second read. **M0
landed** (the transcription build; four nodes green). This sub-phase now needs the second read,
then the generic realization at graphs with no planar-rigid set (B1–B3). **Next: the second read
of (MC-183)–(MC-187)**, before B1 — see *Hand-off*.

## Current state

**M0 landed** (four nodes green: `lem:pencil-x0-distinct-statement`,
`lem:pencil-feasible-hub-conditions`, `lem:pencil-three-bodies-no-rigid`,
`lem:pencil-x0-two-hubs-obstruction`, the last pinning both obstruction declarations). Otherwise
`blueprint/src/chapter/main-component.tex` §`sec:main-component-statements` stays as transcribed at
open: the remaining ten new nodes and the rewritten `thm:pencil-x0-generic-attains` are red and
unpinned (the 40h/40l convention), with `thm:pencil-conjecture` red in `pencil.tex`. Each build adds
its nodes' `\lean{…}` and `\leanok` (statement and proof). **Next concrete commit: the second read
of (MC-183)–(MC-187)** (a fresh read-only reader; see *Hand-off*), before B1. Which sub-phase greens
each remaining node:
- **40n:** `def:pencil-two-ear-graph` (B1); `lem:pencil-x0-planes-separate` (B2);
  `lem:pencil-x0-conjunct-three`, `thm:pencil-x0-base-generic` (B3).
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

**The spikes** (gitignored `scratch/40n/`, local to this checkout; builder sources, not evidence;
**keep them**, since EARS and REDUCE+CLOSE transcribe from them). Run with `lake lean` at `c2b74e61`;
the coordinator's re-run matched:
- `K23.lean` (142 lines): exit 0, no `sorry`, standard axioms on its three theorems.
- `Headline.lean`, `Dist.lean`: exit 0, standard axioms on `x0Dist`.
- `OneEar.lean` (368 lines; EARS' Z1 source): exit 0, standard axioms on
  `exists_mem_perp_pair_linearIndependent` and the one-ear extension, (MC-185).
- `Gen.lean` (249 lines; REDUCE+CLOSE's F1 source): exit 0, exactly four `sorry`s, the leaves BASE
  (line 31), (MC-129) (41), (MC-127)(a) (60) and (MC-127)(b) (73); `x0Dist`,
  `PencilNondegFeasible.hub_conditions` and `noRigid_of_simple_of_ncard_eq_three` are standard.
- `Apex.lean` (24 lines; B1's source): exit 0; it builds the Matroid package's
  `Matroid.Graph.Bipartite` and `Matroid.Graph.Constructions.Sum` (about 20 s).

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
  under `Molecule/Pencil/MainComponent/`): below, per item. The final assembly file is
  `MainComponent/Statements.lean` (not `Motives`, one letter from `Pencil/Motive.lean`).

## Lemma checklist

Pins in **bold**. **Every build:** the gates of `CombinatorialRigidity/CLAUDE.md` *Before each
commit*: a warning-free `lake build`, `lake lint`, `blueprint/verify.sh`, `blueprint/lint.sh`, and a
`#print axioms` check on each pin. New files get the copyright header and a module docstring listing
their statements; every declaration gets a docstring.

- [x] **M0** (sonnet-rated transcription; greens four nodes — landed).
  - **`CombinatorialRigidity.Molecular.x0Dist`** → `lem:pencil-x0-distinct-statement`, in the new
    `MainComponent/Statements.lean` (imports `…Pencil.X0` and `…MainComponent.CoverageTheoremS`;
    root import after `…MainComponent.SplitOff`, alphabetical), ← `scratch/40n/Headline.lean` 16–18:
    `theorem x0Dist [Finite α] [Finite β] [Infinite K] : X0Dist K α β`.
  - **`CombinatorialRigidity.Molecular.PencilNondegFeasible.hub_conditions`** →
    `lem:pencil-feasible-hub-conditions`, in `Pencil/Motive.lean` after
    `not_pencilNondegFeasible_of_triangle_two_hubs`, ← `Gen.lean` 89–106.
  - **`Graph.noRigid_of_simple_of_ncard_eq_three`** → `lem:pencil-three-bodies-no-rigid`, in
    `Molecular/Induction/ReducibleVertex.lean` (namespace `Graph`) after
    `not_simple_of_isMinimalKDof_of_ncard_two`, ← `Gen.lean` 108–138 (dropped the `Graph.` prefixes).
  - **`CombinatorialRigidity.Molecular.not_isNondegPencilRealization_of_two_hubs_three_common`**, in
    `Pencil/Motive.lean` beside the triangle lemma, ← `K23.lean` 21–62 (the spike left this one
    undocumented; wrote a fresh docstring); and
    **`…not_isNondeg_pencilConfigPoint_of_two_hubs_three_common`**, in
    `MainComponent/Configuration.lean` after `Graph.IsAdmissiblePicture.hasDistinctPencilRealization`,
    ← `K23.lean` 64–84 → `lem:pencil-x0-two-hubs-obstruction` (pins both declarations). `K23.lean`'s
    witness shrinking (89–138) and `pencil_conjecture_of_X0Gen` (`Headline.lean` 20–25) do not land:
    neither is consumed here, and the blueprint states the shrinking in prose.
- [ ] **The second read of (MC-183)–(MC-187)** (a fresh read-only reader, before B1; see *Hand-off*).
- [ ] **B1** → `def:pencil-two-ear-graph`. **`Graph.addTwoEar`** beside `Graph.embedEdges` in
  `MainComponent/Bridge.lean` (with `import Matroid.Graph.Constructions.Sum`), ← `Apex.lean` 13–15,
  and its API: simplicity, the vertex set, the closed neighbourhoods (each has at least three members),
  and (MC-184)'s first bullet, an injective linear map from the heights of `G` with equal planes at `u`
  and `w` into `L(G_e, (q, q_x))`. Unspiked beyond `Apex.lean`: B1 opens with a compiler-checked spike.
- [ ] **B2** → `lem:pencil-x0-planes-separate`, (MC-184), in the new `MainComponent/GenericBase.lean`:
  `def₂(G_e) + 1 ≤ def₂(G)` at a rigid-free `G` (partitions of `Option α` restricted to `α`, 40l's
  `one_le_partitionDef_induce_id`), then BRIDGE's `Graph.exists_mvPolynomial_finrank_liftingSpace_eq`
  at `G` and `G_e` with the `G` polynomial renamed along `some`. Target shape:
  `∃ P : MvPolynomial (α × Fin 2) K, P ≠ 0 ∧ ∀ q, MvPolynomial.eval q P ≠ 0 → ∃ x ∈ LinearMap.ker
  ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin, planeDiff u w x ≠ 0`, under `G.Simple`,
  `∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard`, `∀ Y ⊆ V(G), 2 ≤ Y.ncard → (G.induce Y).deficiency 2 ≠ 0`
  and `u ≠ w` in `V(G)`.
- [ ] **B3** → `lem:pencil-x0-conjunct-three` ((MC-12), via `exists_smul_eq_interpolant`) and
  `thm:pencil-x0-base-generic`, in `GenericBase.lean`: **`Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero`**,
  exactly `Gen.lean` 31–36 (`[Infinite K] [Finite α] [Finite β]`, `hG : G.IsX0Graph`,
  `hfeas : PencilNondegFeasible K G`, `hS : ∀ Y ⊆ V(G), 2 ≤ Y.ncard → (G.induce Y).deficiency 2 ≠ 0`).
  The general-position polynomial (hub triples non-collinear) and a finite form of
  `MvPolynomial.exists_mem_eval_ne_zero₂` (by induction on products) are new helpers. May split in
  two.

## Blockers / open questions

- **B1–B3 are new mathematics and unspiked** past their target statements; size 900–1400 lines (the
  recon's estimate). The risk is B2's partition transfer across the vertex-type change.
- **The second read** is a precondition for B1 (it reads (MC-184), B2's claim).

## Hand-off / next phase

1. **M0 — done**: the checklist above, landed verbatim from the spikes; four nodes green
   (`lem:pencil-x0-distinct-statement`, `lem:pencil-feasible-hub-conditions`,
   `lem:pencil-three-bodies-no-rigid`, `lem:pencil-x0-two-hubs-obstruction`).
2. **Next: the second read of (MC-183)–(MC-187)**: a fresh read-only reader, using the design doc's
   Appendix brief. It runs **before B1**, since BASE consumes (MC-184); the PI's text says "before
   40o's ear builds", and reading earlier satisfies it. It checks each claim against its citations and
   the landed definitions, and records its verdict in Step MC19's route-B header.
3. **B1–B3**, each opening with its own spike. After B3, 40n closes, and **EARS** opens by code
   (letter minted then): T1–T3, Z1 from `OneEar.lean`, Z2.

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
