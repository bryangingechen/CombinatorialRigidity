# Phase 40k — PENCIL-X0 / CONTRACT-A: contraction at an additive core (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-28). CONTRACT-A, STEPS'
seventh and last group (`notes/Phase40-design.md` §3 STEPS), proved the contraction step at a
rigid core whose planar deficiency adds: at an induced core `H = G[W]`, `W ⊊ V(G)`, `|W| ≥ 2`,
`def₃(H) = 0`, with no outside body adjacent to two core bodies, in a 2EC `G` satisfying (H), if
`def₂(H) + def₂(G/H) ≤ def₂(G)` and `X₀` attains at `H` and at `G/H`, then `X₀(G)` attains
((MC-71)). No new mathematics. **STEPS is done. Next: 40l = COVERAGE's REDUCE, opened 2026-09-28** —
see `notes/Phase40l.md`.

## Current state

**Closed.** Three build commits (B1 `b7e9a778`, the `Contract.lean` split; B2 `8499bb79`; B3
`b394aac3`) and the close landed. The five nodes of `main-component.tex`
§`sec:main-component-contract-additive` are green: `lem:pencil-rank-collineation`,
`lem:pencil-contract-kernel-bound`, `lem:pencil-contract-magnified-rank`,
`lem:pencil-contract-standing-rigid` and `thm:pencil-x0-contract-additive`, with one unpinned
remark after the theorem (the exposition-ledger entry, and CONTRACT-R as the case `def₂(H) = 0`).

The Lean is `Molecule/Pencil/MainComponent/ContractAdditive.lean` (368 lines; its module docstring
lists the statement), importing `ContractCurve.lean` (1 320 lines) only. `ContractCurve.lean` holds
the pieces shared with CONTRACT-R and CONTRACT-A's general pieces; `Contract.lean` (446 lines)
keeps the flat-core pieces and CONTRACT-R; the collineation lemma is in `Configuration.lean` (723
lines). The spikes (`scratch/40k/`, gitignored and local to this checkout) are consumed.

**Headline axioms, re-verified at the close** on 28 declarations: the eighteen `formalization.yaml`
main results, the six pins of the five nodes, and the four pins of `lem:pencil-contract-standing`,
whose statement the close edited. All 28 are exactly `[propext, Classical.choice, Quot.sound]`;
none uses `sorryAx`. *Measured, script not retained*: one `#print axioms` line per declaration
under `import CombinatorialRigidity`, run with `lake lean` on the fully built tree (a full
`lake build` first: 2 987 jobs, 0 warnings).

- **Satisfiability (not landed).** θ(1,3,4) on `Fin 7`, core `C₄` on `0–1–2–3` (`r = 0`), path
  `0–4–5–6–1`, so `G/H = C₄`: (H), 2EC, `hatt`, `def₃(G[W]) = 0` and `1 ≤ def₂(G[W])`
  kernel-checked in the recon's instance spike, so CONTRACT-R does not cover it; `hadd` measured
  (`def₂ = 2 / 1 / 1` for `G / H / G/H`; the recon's `measure.py`, not retained). A negative
  control fails `hadd`.
- **Faithfulness** (against (MC-71)): `of_additiveContract` is (MC-71) with its count in the `≤`
  form; `hdef3` is its "proper rigid set" and `hatt` its "`G/H` simple". (H) is asked at `G` only.

## Architectural choices made up front

- **The route** (the recon's verdict; as landed, the *CONTRACT-A done* paragraph of
  `notes/Phase40-design.md` §3 STEPS): two bounds on `ker M(0)` forcing its core heights onto
  `L_H(q)`, two open conditions in `ker M(0)`, and the core's rank by a collineation at the fixed
  picture; in place of (MC-68)(d)'s core-freeness and (MC-38)'s dominance (the proof-level
  departure, in the blueprint proof and the remark after it).
- **The coordinator's calls** (2026-09-28, under the PI's session-start "follow precedent"; not PI
  decisions, so not in `notes/pencil/adjudications.md`):
  1. no new mathematics, so 40k opened directly (the 40f/40g/40i/40j precedent);
  2. `hadd` in the `≤` form, the form (MC-87)(i)'s proof produces;
  3. `hdef3` kept, faithful to (MC-71); the compiled `of_additiveContract_weak` not adopted;
  4. `hatt` kept, for parity with CONTRACT-R (the PI-decision-2 todo stays open);
  5. option A: the general pieces to `ContractCurve.lean`, CONTRACT-R untouched (option B and the
     cheaper-diff sub-option are recorded in the design doc for the PI);
  6. the collineation lemma in `Configuration.lean`, a reading of PI decision 5 the PI may reverse;
  7. pins: CONTRACT-A pays none of the D5 debt, which passes to COVERAGE;
  8. (MC-67), (MC-68) and (MC-70) re-homed to the design doc's §2 *Not needed*;
  9. `lem:pencil-contract-limit` (2) lifted out of the flat setting (blueprint only);
  10. the subsection before `sec:main-component-statements`;
  11. the name `Graph.X0Attains.of_additiveContract`;
  12. the recon's four optional dedupes as cleanup-round items (*Hand-off*).
- **Blueprint placement.** The general lemmas before the step; the collineation lemma first, as the
  only one not about the contraction.

## Lemma checklist

All landed with the standard axioms (*Current state*); pins in **bold**, the other names unpinned
helpers.

- [x] **B1** (`b7e9a778`) — the split: `ContractCurve.lean` (importing `Cut.lean`) takes every
  piece CONTRACT-R shares, `Contract.lean` (importing `ContractCurve.lean` only) keeps
  `Graph.exists_core_plane`, the flat K3, the flat core rank, the `def₂` standing lemma and
  CONTRACT-R. `Graph.contractLimitMap_mem_liftingSpace` and
  `Graph.eq_zero_of_contractLimitMap_eq_zero` generalized in place to a plane hypothesis. No pin
  moved.
- [x] **B2** (`8499bb79`) — **`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv`**
  → `lem:pencil-rank-collineation` (`Configuration.lean`, pinned fully qualified);
  **`Graph.liftingRestrict_mem_liftingSpace_induce_of_contract`** and
  **`Graph.finrank_ker_contractLiftingMatrix_zero_add_three_le`** (with `contractCoreRestrict`) →
  `lem:pencil-contract-kernel-bound`; **`Graph.finrank_span_rigidityRows_induce_contractHeight_eq`**
  → `lem:pencil-contract-magnified-rank`; **`Graph.isX0Graph_induce_of_deficiency_eq_zero`** →
  `lem:pencil-contract-standing-rigid` (all three in `ContractCurve.lean`).
- [x] **B3** (`b394aac3`) — new `ContractAdditive.lean`: **`Graph.X0Attains.of_additiveContract`**
  → `thm:pencil-x0-contract-additive`.
- [x] **The close** (docs and blueprint, with one Lean docstring chore): the end-to-end re-read,
  the exposition ledger, the headline axioms, the design doc (STEPS done), ROADMAP and
  `MolecularConjecture.md`; the public surfaces left unchanged (the PI's standing call, recorded at
  40f's close: they update when Phase 40 closes).

## Blockers / open questions

- **None for 40k.**

## Hand-off / next phase

**40k is closed, and with it STEPS. The next concrete step moved to `notes/Phase40l.md`:** COVERAGE, the
structural half and the assembly, runs as three sub-phases (the PI's call, 2026-09-28), the first
REDUCE = 40l, opened design-first from a compiler-checked recon. The recon settled COVERAGE's
tracked supplier items, and the PI closed decision 2's `hatt` todo with `hatt` kept.

**Cleanup-round items** (call 12; the design doc's CONTRACT-A entry), in the recon's names (G1 the
collineation lemma, G4 the kernel bound, G5 the rigid-core standing lemma): the flat K3
(`finrank_ker_contractLiftingMatrix_zero_le`) as a corollary of G4; the `def₂` standing lemma as a
corollary of G5; `exists_core_plane`'s middle step via the new core-heights lemma;
`Graph.finrank_span_rigidityRows_ofNormals_smul_add_affineLifts` via G1. 40k's files are under the
~1500-line tripwire.

## Decisions made during this phase

- **2026-09-28 — the close.** The re-read restated `lem:pencil-contract-standing` so its `G/H`
  clauses no longer assume `def₂(H) = 0` (the Lean never did), and the step's proof now cites it
  directly; the remark after `thm:pencil-x0-contract-rigid` points at the new step; the remark
  after the step became the exposition-ledger entry, and the proof dropped the aside it covers. One
  Lean chore: three docstring sentences in `ContractCurve.lean` and `ContractAdditive.lean`.
- **B3** — `ContractAdditive.lean` imports `ContractCurve.lean` only, as `Contract.lean` does.
- **B2** — section placement per the coordinator's scope-pin: G1 beside
  `pointJoinFramework_comp_eq_mapSupport`, G2, G4 and G5 beside the B1 content they generalize.
- **B1** — `Contract.lean` imports `ContractCurve.lean` only (one-hop convention); the one live
  `TACTICS-QUIRKS.md` §38 file pointer and three prose mentions repointed.
- **At the open** — the spikes and `measure.py` re-run at `77f80d09` with `lake lean`, matching
  the coordinator's counts.
