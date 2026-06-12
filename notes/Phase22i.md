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

**L0e complete (pair-swap committed).** `def HasPanelRealization` moved from
`GenericityDevice.lean` to `PanelHinge.lean` (enabling the swap); `theorem_55_generic`'s
conditioned pair second slot swapped from `HasFullRankRealization k G` to `HasPanelRealization k n G`
(plumbing-only body change; `P :=` annotation updated); `theorem_55_d3`'s three genuine-hinge
callbacks (`hbase`/`hsplit`/`hcontract`) re-typed to `HasPanelRealization 2 n G`-shaped slots;
all IH-threading signatures in `case_I_realization` / `case_III_hsplit_producer` /
`case_III_realization` / `h65` updated; `thm:theorem-55-d3-instance` blueprint prose updated
(second-slot description + carried-family description). Build green (2764 jobs, zero warns);
`lake lint` clean; `blueprint/verify.sh` + `lint.sh` pass. L0 fully complete.

**L1 signature pin landed (§1.58).** V2 resolved (labeling-free `cutEdges` +
`TwoEdgeConnected`, connectivity included); V3 resolved (in-place all-`k` restates — the
landed swap proof needs only one re-routed contradiction; the `= 2` upgrade takes the V2
predicate); V4 resolved (mechanical). KT 3.6 pinned as a pure partition argument (no matroid
direct sum); the KT-4.8(ii) cluster decomposed (the reverse forest direction KT 4.2 is the
one new engine); KT-numbering corrected against the PDF (`splitOff_isMinimalKDof` =
KT 4.8(i), not 4.7). Sliced **L1a–L1j** with build order in §1.58(i). **Next concrete step:
the L1a build** (`cutEdges` + `TwoEdgeConnected` + the three bridges, Deficiency.lean +
the `def:cut-edges-2ec` blueprint node).

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

- [x] **L0** — motives M1–M5 + bridges B1/B2 + the blueprint def-node flips; signatures
  pinned in §1.57, sliced **L0a–L0e** (§1.57(e)):
  - [x] **L0a** — `ExtensorInPanel` + the `k = 2` meet-decomposition lemma (additive).
  - [x] **L0b** — the coannihilator complement brick + B1 (additive).
  - [x] **L0c** — the partition bricks + the relative hub + B2 (additive).
  - [x] **L0d** — `HasPanelRealization` (M2) + the forgetful map (M4) +
    `def:genuine-hinge-realization` pinned + green (`checkdecls`).
  - [x] **L0e** (M3-first) — M3 rank form + `n`; producer seams through B1; old forgetful
    deleted; `def:rank-hypothesis` re-prosed. Pair-swap sub-commit still pending.
  - [x] **L0e** (pair-swap) — swap `theorem_55_generic`/`theorem_55_d3` second slot to
    `HasPanelRealization k n G`; re-type three bare carries; update d3-instance prose.
- [ ] **L1** — the combinatorial bricks; signatures pinned in §1.58, sliced **L1a–L1j**
  (V2 predicate; the `|V| ≤ 2` trichotomy; V3/V4/G0 in-place all-`k` restates; the KT 3.6
  cut decomposition; KT 4.5(ii)/4.2/4.4-eq/4.7/4.3(ii)/4.8(ii)). Build order §1.58(i):
  L1a → {L1b, L1c, L1d, L1f, L1g} → L1e, L1h → L1i → L1j.
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

**Smallest next forward commit: the L1a build** — `cutEdges` + `TwoEdgeConnected` + the
three bridge lemmas (`cutEdges_eq_crossingEdges_cutLabeling`,
`twoEdgeConnected_of_isKDof_zero`, `two_le_degree_of_twoEdgeConnected`) in
`Molecular/Deficiency.lean`, per the §1.58(b) pin, plus the `def:cut-edges-2ec` blueprint
node (deficiency.tex). Then L1b–L1j per the §1.58(i) build order. L0 is fully complete; the
L1 signatures are pinned in §1.58.
At phase close:
Phase 23 (general `d`, KT Lemma 6.13) opens with its own recon (KT eqs. (6.46)–(6.67) vs the
`d = 3` Lean, §1.33 (C) reuse map) and adds the general-`d` row to
`notes/AlgebraicIndependence.md`.

## Decisions made during this phase

- **L1 signature pin (2026-06-11):** V2 → labeling-free `cutEdges` count, connectivity
  included (the disconnected Lemma-6.1 arm routes through the same ¬2EC case); V3 →
  in-place all-`k` (the landed swap proof needs one re-routed contradiction, no case
  split); V4 → mechanical. KT 3.6 by pure partition argument (refinement + straddle-free
  split — no matroid direct sum). KT 4.8(ii) decomposed: the reverse forest direction
  (KT 4.2) is the one new engine; 4.5(ii)/4.4-eq/4.7/4.3(ii)-rev ride on it. Numbering
  corrected against the PDF (`splitOff_isMinimalKDof` = KT 4.8(i)); the L2 floor flag
  recorded (conclude at `V(G).Nonempty`, base `1 ≤ ncard ≤ 2`). Canonical: §1.58.
- **Phase-open (2026-06-11):** the §1.56 motive design pass — carrier split (honest bare on
  `BodyHingeFramework` + panels; generic stays on `PanelHingeFramework`), ℤ-cast
  rank-deficiency equality as the shared rank form, the four-case all-`k` reduction, KT
  pp. 669–679 re-verified against the PDF. Canonical: §1.56.
- **L0 signature pin (2026-06-11):** V1 → pointwise `ExtensorInPanel` (coercion-fixed; meet
  lemma at `k = 2` only — its engine is the `Fin 4` duality suite, every M4 consumer is
  `d = 3`); V10 → B2 by relative re-derivation (the hub bound's all-`e` `hC` is an artifact;
  the real gap is the ambient `D·|V(G)ᶜ|`, closed by a complement-separating partition
  refinement — `finrank_partitionConstant` is already range-exact); M5 re-timed (weak-motive
  deletion = L9 invariant, L0 only de-spines it); two L9/L10 flags (`hD` tightens to
  `bodyBarDim n = screwDim 2`; `rigidityMatrix_prop11` keeps `reaim`). Canonical: §1.57.
- **L0a build (2026-06-11):** `ExtensorInPanel` in `RigidityMatrix.lean`; in `PanelLayer.lean`:
  `exists_two_perp_of_linearIndependent_normals` (rank-nullity on the `2×4` pairing map via
  `Matrix.of_apply` to unblock `mulVec`), `exists_extensor_eq_panelSupportExtensor` (double-
  annihilator via `Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff` + `(Submodule.
  mem_dualAnnihilator r).mp`, scalar absorption via `ιMulti (M := Fin 4 → ℝ).map_update_smul`),
  `extensorInPanel_panelSupportExtensor`. Ordering: the three lemmas placed *after*
  `panelSupportExtensor_join_eq_zero_of_eq_zero` (which they call). FRICTION §
  `ιMulti (M := …)` annotation added.
- **L0b build (2026-06-11):** in `GenericityDevice.lean` beside W2:
  `finrank_span_rigidityRows_add_finrank_infinitesimalMotions` (complement brick, stated with
  `Nat.card α` to avoid `[Fintype α]` in the signature; `rw [Nat.card_eq_fintype_card]` bridges
  to `finrank_screwAssignment`; `linarith` closes);
  `isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows` (B1; forward = W2;
  reverse uses the complement brick + `zify [h1]` / `linarith` to handle the Nat subtraction
  in `hcount`, then `isInfinitesimallyRigidOn_vertexSet_of_finrank_le`).
- **L0e pair-swap (2026-06-11):** `def HasPanelRealization` moved from `GenericityDevice.lean`
  to `PanelHinge.lean` (import constraint: `GenericityDevice` imports `PanelHinge`, not the
  reverse; M4 stays in GenericityDevice). `theorem_55_generic` second-slot type → `HasPanelRealization k n G`;
  `hbase`/`hsplit`/`hcontract` params in `theorem_55_generic` + `theorem_55_d3` updated;
  IH-threading signatures in `case_I_realization`, `case_III_hsplit_producer`,
  `case_III_realization`, `h65` updated. All `.2`-uses in bodies were `.1`-only extractions —
  zero proof changes. Build+lint+verify.sh all green.
- **L0e M3-first build (2026-06-11):** M3 gains `(k n : ℕ)` + rank conjunct
  `(finrank ℝ … : ℤ) = screwDim k * (ncard - 1) - G.deficiency n`. Root producer seam
  pattern (GenericityDevice / CaseI root producers): tactic-mode with W2 +
  `zify [h1] + exact_mod_cast`. Extract-site pattern (all functions obtaining rigidity from
  M3): B1.mpr via `rw [hdef, sub_zero]` + `zify [h1_in] ... exact_mod_cast`. ~16 functions
  in CaseI.lean updated. `hasPanelRealization_of_generic` (M4) drops `hdef` (rank direct
  transfer). `hasFullRankRealization_of_generic` deleted (no live consumers; design doc
  confirmed). Pair unswapped by design (§1.57(e) M3-first cut).
- **L0d build (2026-06-11):** M2 `HasPanelRealization` + M4 `hasPanelRealization_of_generic`
  placed in `GenericityDevice.lean` (not `PanelHinge.lean` per the design): M4 needs W2
  `finrank_span_rigidityRows_of_rigidOn`, which is in GenericityDevice; PanelHinge can't
  import it. Temporary M4 signature has `hdef : G.deficiency n = 0` to bridge from the
  pre-L0e `IsInfinitesimallyRigidOn` slot to M2's ℤ rank form (discharged at call sites by
  `hG.1 : G.IsKDof n 0`). Congr-arg pattern `congr_arg Subtype.val hsupp ▸ hp` threads the
  `ScrewSpace 2` → `ExteriorAlgebra ℝ _` coercion for `ExtensorInPanel` witnesses.
- **L0c build (2026-06-11):** five bricks. In `PanelLayer.lean` under `section Classical_L0c`
  (after `screwDim_mul_numParts_sub_le_finrank_partitionMotions`): range-exact bound via same
  rank-nullity route using `finrank_partitionConstant` (`D·|range f|` exact);
  `crossingEdges_complement_sep` + `range_complement_sep_card` as helpers (both need `open
  Classical in` before their docstring — parser restriction, FRICTION §); relative hub via
  normalization: `Set.Finite.exists_injOn_of_encard_le` gives injection `ι₀` from `f₀ '' VG`
  into `VG`; `if_pos` closes `g u = ι₀ (f₀ u)` directly as a term proof (set-binding is
  definitionally the if-expression); `sᶜ.ncard` vs `s.compl.ncard` bridge via `rfl` for
  `linarith` (FRICTION §). B2 placed in `GenericityDevice.lean` (needs L0b's complement
  brick; `PanelLayer` doesn't import it).
