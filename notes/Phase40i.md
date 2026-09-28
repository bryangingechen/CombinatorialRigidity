# Phase 40i — PENCIL-X0 / ORBIT: the open ears with one or two interior bodies at non-adjacent ends (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-28). ORBIT, STEPS' fifth
group (`notes/Phase40-design.md` §3 STEPS), proved the open-ear steps with one interior body, and
with two with no bound on the deficiency, both at non-adjacent ends and under
`deficiencyMerged₂(G[V₁]; a, b) + 2 ≤ def₂(G[V₁])`: if `X₀(G[V₁])` attains, `X₀(G)` attains for
`k = 1` when `def₃(G[V₁]) ≤ def₃(G)` ((MC-54) at `k = 1`), and for `k = 2` when `X₀` also attains
at `G` with its second interior body suppressed ((MC-176)). No new mathematics. **Next: STEPS'
SPLITOFF group, not yet opened** — see *Hand-off*.

## Current state

**Closed.** Three build commits (B1 `5ba25337`, B2 `b733f5fe`, B3 `b3dac673`), a coordinator
fixup (`6b266906`, one proof `\leanok`) and the close landed. The eight nodes are green:
- `main-component.tex` §`sec:main-component-orbit`: `lem:pencil-flag-genericity`,
  `lem:pencil-one-ear-incidence`, `lem:pencil-one-ear-base`, `thm:pencil-x0-open-ear-one`,
  `lem:pencil-insertion-two` and `thm:pencil-x0-open-ear-two-orbit`, with the unpinned remark after
  the two-body theorem (the exposition-ledger entry);
- `molecular-induction.tex`: `lem:splitoff-deficiency-merged`; `deficiency.tex`:
  `def:deficiency-merged` (green at the open).

The Lean is `Molecule/Pencil/MainComponent/Orbit.lean` (its module docstring lists the statements),
with pieces placed by PI decision 5's convention in `Carrier.lean`, `Flat.lean`, `Lines.lean`,
`Induction/Operations.lean` and `Induction/SplitOffDeficiency.lean`. The spikes (`scratch/40i/`,
gitignored and local to this checkout) are consumed.

**Headline axioms, re-verified at the close** on 28 declarations: the eighteen `formalization.yaml`
main results and the ten pins of the eight nodes. 27 are exactly
`[propext, Classical.choice, Quot.sound]`; `planeDiff`, a linear map built from
`LinearMap.funLeft`, is `[propext, Quot.sound]`, a subset. None uses `sorryAx`. *Measured, script
not retained*: one `#print axioms` line per declaration under `import CombinatorialRigidity`, run
with `lake lean` on the fully built tree (a full `lake build` first: 2 983 jobs, 0 warnings).

- **Satisfiability (not landed).** The structural hypotheses are kernel-checked in the recon's
  instance spike; the deficiencies are measured (script not retained). `k = 1` at the 8-cycle
  `4 0 5 2 7 3 6 1` with the chords `4–7`, `5–6` and ear `4 − 0 − 5`: `def₂(G[V₁]) = 2` with merged
  value `0`, and `def₃(G[V₁]) = def₃(G) = 0`; `h₁` by hand (`G[V₁]` is θ(1,2,2)). `k = 2` at `K₄`
  with every edge subdivided twice, ear `0 − 4 − 5 − 1`: (S) holds and `δ₂ = 3`; `h₁`, `h₂` from
  the workbook's certificates. At `K_{2,3}` (`δ₂ = 1`) the merged-deficiency hypothesis fails, and
  FLAT covers it.
- **Faithfulness** (against (MC-54), (MC-176)): `of_openEar_one` takes `hdef` for `δ = 0` (PI
  decision 4(a)) and `hδ₂` for `dim U ≥ 2`, sufficient by U2; `hnadj` holds in 𝒮 by (MC-79)(ii).
  `of_openEar_two_of_splitOff` asks attainment at `G[V₁]` and at
  `G.splitOff (x 1) (x 0) b (e 1)`, the workbook's `G₁` (its `x₂` suppressed). Both ask (H) at `G`
  only, as 40g's and 40h's do.

## Architectural choices made up front

- **The route** (the recon's verdict; as landed, the *ORBIT done* paragraph of
  `notes/Phase40-design.md` §3 STEPS): U2 and (MC-174) on the lifting system's kernel, one base
  lemma for both cells, and at `k = 2` (MC-173) in existence form with EARGEN's span transfer.
- **The coordinator's calls** (2026-09-28, under the PI's session-start "follow precedent"; not PI
  decisions, so not in `notes/pencil/adjudications.md`):
  1. no new mathematics, so 40i opened directly, with no workbook commit and no second reading
     (the 40f/40g precedent);
  2. `hδ₂` in both cells in the `deficiencyMerged` form (the design doc's ORBIT entry has the
     trace; COVERAGE supplies it);
  3. placement by PI decision 5's convention, the steps in a new `Orbit.lean`;
  4. pins by PI decision 4(b)'s first-consumer rule: only `deficiencyMerged` and
     `partitionDef_le_deficiencyMerged`, on a definition node;
  5. the nodes follow the spike's statements (40h's `lem:pencil-ear-data` precedent);
  6. three builds: the general pieces, the `k = 1` cell, the `k = 2` cell.
- **Blueprint placement.** In the new subsection, the general lemmas before the steps and `k = 1`
  before `k = 2`; the split-off bound after its label-reusing sibling; the definition after
  `lem:deficiency-ear-merge`.

## Lemma checklist

All landed with the standard axioms (*Current state*); pins in **bold**, the other names unpinned
helpers.

- [x] **B1** (`5ba25337`) — **`Graph.splitOff_deficiency_add_le_of_deficiencyMerged`** →
  `lem:splitoff-deficiency-merged` (`Induction/SplitOffDeficiency.lean`);
  **`planeDiff`**, **`Graph.two_le_finrank_map_planeDiff`** → `lem:pencil-flag-genericity`
  (`Carrier.lean`, with `planeDiff_apply`, `Graph.injective_liftingMatrix_ker_proj` and two
  admissibility helpers); `linearIndependent_pointJoin_pair` (`Lines.lean`),
  `linearIndependent_pencilConfigPoint_triple` and the seven `pointJoin` linearity lemmas
  (`Flat.lean`), and `Graph.splitOff_simple_of_not_adj` (`Operations.lean`).
- [x] **B2** (`b733f5fe`) — new `Orbit.lean`: **`exists_incidence`** →
  `lem:pencil-one-ear-incidence`; **`Graph.exists_oneEar_base`** → `lem:pencil-one-ear-base`;
  **`Graph.X0Attains.of_openEar_one`** → `thm:pencil-x0-open-ear-one`; `Graph.splitOff_oneEar`,
  `exists_dotProduct_eq_zero_ne_zero`, `incidencePoly`, `eval_incidencePoly`.
- [x] **B3** (`b3dac673`) — **`exists_insertion_two`** → `lem:pencil-insertion-two` (`Lines.lean`,
  with `exists_insertion_two_aux`);
  **`Graph.X0Attains.of_openEar_two_of_splitOff`** → `thm:pencil-x0-open-ear-two-orbit`;
  `splitOff_ear_two`, `splitOff_ear_two_simple` (`Orbit.lean`).
- [x] **The close** (docs and blueprint, with two Lean doc/import chores): the end-to-end re-read,
  the exposition ledger, the headline axioms, the design doc, ROADMAP and `MolecularConjecture.md`;
  the public surfaces left unchanged (the PI's standing call, recorded at 40f's close).

## Blockers / open questions

- **None for 40i.** The stale `Deficiency.lean` section docstring was repointed at the close.

## Hand-off / next phase

**40i is closed. The next concrete task is STEPS' SPLITOFF group**, (MC-28)–(MC-31), the next group
in the design doc's provisional grouping and its recorded order (`notes/Phase40-design.md` §3
STEPS; CONTRACT-A after it). It is not yet opened and has no letter. By the 40f–40i precedent its
first step is a compiler-checked design recon (opus) of (MC-28)–(MC-31); the group opens as the
next sub-phase after it. It is the first consumer of the `jointMotions`, `weldedRank` and remaining A2/A3 pins
(PI decision 4(b); design doc §7).

**Cleanup-round items.** 40h's four stay in the design doc's SHORT entry. 40i adds none: its files
are under the ~1500-line tripwire (`Orbit.lean` 1 099, `Lines.lean` 1 064, `Carrier.lean` 1 023),
and the one friction it resolved (the right-linear `pointJoin` lemmas) leaves an optional golf in
`exists_insertion_gain` (`notes/FRICTION.md`).

## Decisions made during this phase

- **2026-09-28 — the close.** The re-read clarified that the two-body step drops
  `thm:pencil-x0-open-ear-two`'s deficiency bound, named the incidence proof's non-root, made the
  two-body count's `s` an equality (as the Lean derives), and added the remark after the two-body
  theorem (the exposition-ledger entry). Two Lean chores: `Deficiency.lean`'s section docstring now
  cites `def:deficiency-merged` and lists the section's pinned and unpinned declarations;
  `Orbit.lean` drops its redundant `EarGen.lean` import (`Short.lean` brings it). The B3 checklist
  bolding is corrected to the open's plan (`splitOff_ear_two{,_simple}` unpinned).
- **B3** — `Orbit.lean` also imports `Short.lean`, for `induce_splitOff_ear` and
  `Graph.isLink_update_splitOff`; a recon helper inlined at its three use sites.
- **B2** — `EarGen.lean` was the least module supplying B2's identifiers (a `lake lean` probe); a
  recon helper inlined as a local `have`.
- **B1** — `Graph.closedNbhd_subset_vertexSet` (downstream in `Bridge.lean`) inlined at its one call
  site in `Carrier.lean`.
- **At the open** — `def:deficiency-merged` green: the Lean restricts the labeling supremum to
  `f u = f v`, the maximum over the partitions with `u`, `v` in one part; the cheapest witness is
  the one-part partition, of value `0`.
