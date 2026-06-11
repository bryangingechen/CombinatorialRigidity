# Phase 22i — the honest all-`k` Theorem 5.5 (work log)

**Status:** in progress (opened 2026-06-11 at the 22h close, per `notes/Phase22h.md`
*Hand-off*).

Discharges the five 22h carries {`h622`, `h65`, `hbase`, `hsplit`, `hcontract`} by restating
the realization motive at KT's strength — **genuine hinges** (the free-hinge carrier + panel
containment) and the **all-`k` induction** (KT's four-case `|V|`-recursion with IH (6.1) over
every dof) — then re-running the spine and building the KT cases the weak motive skipped.
**The motive design is canonical in `notes/Phase22-realization-design.md` §1.56** (motives
M1–M5, the reduction principle, the case-producer map (d), bridges B1/B2, verification items
V1–V10, the layer plan (h)) — point at it, don't duplicate. Structural-edit mode: no new
blueprint chapter; the existing `algebraic-induction/*` chapters restate per slice (the
statement-grep gate per `CLAUDE.md` *Structural-edit phases*).

## Current state

**Phase-open commit only.** §1.56 pins the motive (the honest bare motive moves to the
free-hinge `BodyHingeFramework` carrier with an `ExtensorInPanel` containment + the ℤ-cast
rank-deficiency equality; the generic motive keeps its `PanelHingeFramework` carrier with
only the rank form generalized; the reduction becomes the four-case all-`k` principle). No
Lean has been touched. **Next concrete step: the L0 signature pin** — a §1.57 design block
resolving V1 (the `ExtensorInPanel` form, against RigidityMatrix.lean's
homogeneous-incidence machinery), V10 (the B2 relative upper bound's route), and the exact
M2/M3/M4 statements + blueprint def-node dispositions; then L0's Lean (motives + bridges +
def-node flips) as the first build commit.

The phase-open red-node consistency gate was run on the five target nodes
(`lem:case-III-nested-rank-lower`, `lem:case-I-dispatch`, `def:genuine-hinge-realization`,
`def:rank-hypothesis`, `thm:theorem-55` + the green `thm:theorem-55-d3-instance`): each
statement and proof routes through the same 22i discharge plan §1.56 now details; no
live-route reference points at a superseded node (`blueprint/lint.sh` green, supersession
gate included).

## The carries table (the §1.55(b) structural fix for orphaned deferrals)

| Carry | Blueprint red node | Lean consumption site | Discharge sub-plan (§1.56) |
|---|---|---|---|
| `h622` (KT eq. (6.22), the nested-IH rank lower bound at the `k'`-dof `G_v`) | `lem:case-III-nested-rank-lower` (case-iii.tex) | `case_III_realization` (CaseI.lean:6750) and `theorem_55_d3` (:6817); consumed at the one W6b call inside `case_III_candidate_dispatch` | **L7**: replace the hypothesis by a derivation from the all-`k` IH at `G_v` — IH gives the generic realization at rank `D(m−1) − k'`; extract the rational rank-polynomial witness (V8); transfer to the given `(ends, q)` by the landed footnote-6 bridge (`lem:case-III-seed-rank-bridge`) |
| `h65` (the KT Lemma-6.5 vertex-removal arm of the Case-I dispatch) | `lem:case-I-dispatch` (case-i.tex) | `theorem_55_d3` (:6831), the negative branch of the L5c′ `by_cases` | **L8**: §1.54(a3) steps 1–2 — Claim 6.6 graph side (~2–3 commits) + the Π°-placement producer (own signature pin first); the dispatch itself landed in 22h. Claim 6.6 concludes inside the `k = 0` stratum, no all-`k` generality needed |
| `hbase` (the bare two-vertex base) | `def:genuine-hinge-realization` (panel-layer.tex; + `lem:theorem-55-base` as the rank engine) | `theorem_55_d3` (:6802), passed to `theorem_55_generic`'s `hbase` slot | **L3**: the `\|V\| = 2` trichotomy (KT p. 671: `E = ∅` / one edge / parallel pair, `k ∈ {D, 1, 0}`) + the graph-level Lemma-5.3 coincident-panel brick (two non-proportional extensors in a common panel, M1 pointwise form) re-aimed into Pinning.lean's `theorem_55_base` |
| `hsplit` (the bare no-rigid-subgraph branch) | `def:genuine-hinge-realization` | `theorem_55_d3` (:6804) | **L9 wiring, no new build**: G0 (`simple_of_isMinimalKDof_of_noRigid`) gives `G.Simple`; forgetful (M4) ∘ the GP Case-III producer |
| `hcontract` (the bare Case-I branch) | `def:genuine-hinge-realization` | `theorem_55_d3` (:6809) | **L5**: dispatch on `G.Simple` — simple → forgetful (M4) ∘ the 6.3/6.5 GP arm; non-simple → KT Lemma 6.2 (NEW: the coincident-panel splice; the parallel-pair subgraph + the Lemma-5.3 leg at the contraction panel + the eq. (6.3)–(6.5) rank addition; N6a re-aimed, V6) |

Beyond the carries, the all-`k` restructure itself adds the structural deliverables of
§1.56(c)/(e): the new reduction cases (Lemma 6.1 not-2-edge-connected; Lemma 6.8 `k > 0`
split), the motive restate of every producer, and the Thm-5.6 `d = 3` push (the `def > 0`
`prop:rigidity-matrix-prop11` feed).

## Layer plan (each layer opens with its own §1.57+ signature pin)

- [ ] **L0** — motives M1–M5 (`ExtensorInPanel`, `HasPanelRealization`, the
  `HasGenericFullRankRealization` rank-form restate, forgetful map) + bridges B1
  (rank ⟺ rigid at `def = 0`) / B2 (the relative deficiency upper bound) + the blueprint
  def-node flips (`def:genuine-hinge-realization` pinned + green).
- [ ] **L1** — the combinatorial bricks: the `|V| ≤ 2` trichotomy; the cut-edge
  decomposition (KT 3.6 `k = k₁ + k₂ + 1` + 3.3 sides; the `TwoEdgeConnected` predicate,
  V2); `rigidContract_isMinimalKDof` all-`k` (KT 3.5, V4); `exists_degree_eq_two`
  2EC-hypothesis restate (KT 4.6, V3); KT 4.8 (`G_v^{ab}` minimal `(k−1)`-dof at `k > 0`).
- [ ] **L2** — `minimal_kdof_reduction_all_k` (the four-case principle, §1.56(c)).
- [ ] **L3** — the base producer (`hbase` carry discharged).
- [ ] **L4** — Lemma 6.1, the cut-edge case (V5: the fixed-seed transversality route).
- [ ] **L5** — Lemma 6.2 (non-simple Case I, V6) + the 6.3/6.5 all-`k` restate of
  `case_I_realization` (`hcontract` carry discharged).
- [ ] **L6** — Lemma 6.8, the `k > 0` split (reuses `case_II_placement_eq612` = KT eqs.
  (6.13)–(6.17); the Lemma-5.2 shear transfer via the 22h W-suite, V7).
- [ ] **L7** — the Case-III rewire: `case_III_realization` restated, `h622` derived from
  the all-`k` IH (V8) (`h622` carry discharged).
- [ ] **L8** — the Lemma-6.5 arm: Claim 6.6 + the Π°-placement (§1.54(a3)) (`h65` carry
  discharged).
- [ ] **L9** — the spine + instance: `theorem_55_all_k`, `theorem_55_d3` restated with zero
  carries (`hsplit` discharged here), `theorem_55` deleted/re-pinned, blueprint restates.
- [ ] **L10** — Theorem 5.6 at `d = 3`: the deficiency-preserving spanning-strip brick +
  re-add edges + the `def > 0` `prop:rigidity-matrix-prop11` feed (V9: the homogeneous
  projective move).

## Blockers / open questions

- The ten verification items **V1–V10** (§1.56(g)) — each is gated to its layer's design
  pass, none blocks the L0 pin from starting. None is research-shaped; V8 (subfamily
  extraction at rank form) and V10 (the relative hub bound B2) are the two with real
  proof-shape uncertainty.

## Hand-off / next phase

**Smallest next forward commit: the L0 signature pin** — a §1.57 block in
`notes/Phase22-realization-design.md` resolving V1 + V10 and fixing the exact M1–M5/B1/B2
statements against the Lean (read RigidityMatrix.lean's homogeneous-incidence suite and the
hub-bound proof); no `.lean` edits in that commit. Then L0's build commit. At phase close:
Phase 23 (general `d`, KT Lemma 6.13) opens with its own recon (KT eqs. (6.46)–(6.67) vs the
`d = 3` Lean, §1.33 (C) reuse map) and adds the general-`d` row to
`notes/AlgebraicIndependence.md`.

## Decisions made during this phase

- **Phase-open (2026-06-11):** the §1.56 motive design pass — carrier split (honest bare on
  `BodyHingeFramework` + panels; generic stays on `PanelHingeFramework`), ℤ-cast
  rank-deficiency equality as the shared rank form, the four-case all-`k` reduction, KT
  pp. 669–679 re-verified against the PDF. Canonical: §1.56.
