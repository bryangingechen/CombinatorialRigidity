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

**L2 + L3a + L3b complete (`hbase` carry fully discharged at KT strength); L4 next.** L2 landed
`minimal_kdof_reduction_all_k` in `ForestSurgery.lean`; `thm:minimal-kdof-reduction-all-k` is green.
L3a landed the geometric brick (`exists_linearIndependent_extensor_pair_perp` etc.);
`lem:extensor-pair-in-panel` green. **L3b complete:** the trichotomy-dispatch
`theorem_55_base_producer` now concludes the §1.60(a) **strong pair**
`(G.Simple → HasGenericFullRankRealization 2 n G) ∧ HasPanelRealization 2 n G` — the L9 spine's
conditioned motive `Pc`. The GP conjunct's real arms landed: `theorem_55_base_producer_empty_gp`
(single-body/empty GP framework at an alg-indep seed, rank 0) and
`theorem_55_base_producer_single_edge_gp` (§1.60(e)'s genuine `def=1` GP realization at rank `D−1`
— `ofNormals` at an injective alg-indep seed that is a non-root of the GP polynomial, single hinge's
extensor forced nonzero by general position, single-row rank); the parallel-pair arm stays vacuous
by simplicity. `lem:theorem-55-base-producer` green at the strong-pair conclusion; the `.2` rewire of
`theorem_55_d3` + its `hbaseGP`-vacuity discharge are unchanged and still consume the bare conjunct.
**Four carries remain: `h622`, `h65`, `hsplit`, `hcontract`.** Next: **L4** (Lemma 6.1, the
cut-edge case, V5).
**L0 is fully complete** (motives M1–M5 live on the conditioned spine;
bridges B1/B2 landed; `def:genuine-hinge-realization` green — per-slice detail in the
layer plan below and §1.57). **The L1 signature pin is landed (§1.58):** V2 resolved
(labeling-free `cutEdges` + `TwoEdgeConnected`, connectivity included), V3 resolved
(in-place all-`k` restates), V4 resolved (mechanical); KT 3.6 pinned as a pure partition
argument (no matroid direct sum); the KT-4.8(ii) cluster decomposed (the reverse forest
direction KT 4.2 is the one new engine); KT numbering corrected against the PDF
(`splitOff_isMinimalKDof` = KT 4.8(i), not 4.7). L1 is sliced **L1a–L1j** with build
order in §1.58(i).

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
| `hbase` (the bare two-vertex base) | `def:genuine-hinge-realization` + `def:rank-hypothesis`; `lem:theorem-55-base-producer` green at the strong pair | `theorem_55_d3` rewired: `theorem_55_base_producer` supplies `.2`; `hbase` dropped from signature | **L3 complete**: the producer concludes the §1.60(a) strong pair `(G.Simple → HasGenericFullRankRealization) ∧ HasPanelRealization` (the L9-spine `Pc` motive); single-edge + empty GP arms built, parallel-pair vacuous by simplicity |
| `hsplit` (the bare no-rigid-subgraph branch) | `def:genuine-hinge-realization` | `theorem_55_d3` (:6804) | **L9 wiring, no new build**: G0 (`simple_of_isMinimalKDof_of_noRigid`) gives `G.Simple`; forgetful (M4) ∘ the GP Case-III producer |
| `hcontract` (the bare Case-I branch) | `def:genuine-hinge-realization` | `theorem_55_d3` (:6809) | **L5**: dispatch on `G.Simple` — simple → forgetful (M4) ∘ the 6.3/6.5 GP arm; non-simple → KT Lemma 6.2 (NEW: the coincident-panel splice; the parallel-pair subgraph + the Lemma-5.3 leg at the contraction panel + the eq. (6.3)–(6.5) rank addition; N6a re-aimed, V6) |

Beyond the carries, the all-`k` restructure itself adds the structural deliverables of
§1.56(c)/(e): the new reduction cases (Lemma 6.1 not-2-edge-connected; Lemma 6.8 `k > 0`
split), the motive restate of every producer, and the Thm-5.6 `d = 3` push (the `def > 0`
`prop:rigidity-matrix-prop11` feed).

## Layer plan (each layer opens with its own §1.57+ signature pin)

- [x] **L0** — motives M1–M5 + bridges B1/B2 + the blueprint def-node flips; signatures
  pinned in §1.57, sliced L0a–L0e (§1.57(e)), all landed: `ExtensorInPanel` + meet
  decomposition (L0a); complement brick + B1 (L0b); partition bricks + relative hub + B2
  (L0c); `HasPanelRealization`/M4 + `def:genuine-hinge-realization` green (L0d); M3 rank
  form + producer seams + the conditioned-pair swap to `HasPanelRealization k n G` (L0e).
  Per-slice detail: §1.57 + git history (commits fec8775…e68cc4a era).
- [x] **L1** — the combinatorial bricks; signatures pinned in §1.58, sliced L1a–L1j
  (build order §1.58(i)), all landed. Slice → main decls (detail: §1.58, the blueprint
  nodes named, git history):
  *L1a* `cutEdges`/`TwoEdgeConnected` + bridges (`def:cut-edges-2ec`); *L1b* the `|V| ≤ 2`
  trichotomy (`lem:two-vertex-trichotomy`); *L1c* in-place all-`k` restates of V3/V4/G0;
  *L1d* `partitionDef_{congr,comp_of_injOn,split_of_sides}`; *L1e* refinement bound +
  `deficiency_eq_of_cutEdges_ncard_le_one` + `exists_cut_decomposition_of_not_twoEdgeConnected`
  (`lem:cut-edge-decomposition`; all complete — commit 1f7cd32's "partial stub" message
  clause is wrong); *L1f* KT 4.5(ii) `indep_edgeSet_mulTilde_of_noRigid_of_pos` + base
  uniqueness (`lem:edge-set-indep-pos`); *L1g* the reverse acyclicity bricks
  (`lem:reverse-reroute-cycle-lift`/`lem:reverse-pendant-insert`); *L1h* KT 4.2(i)/(ii)
  `splitOff_indep_extend_of_fiber_{lt,subset}` (`lem:edge-splitting`); *L1i* KT 4.4-eq +
  4.7 all-`k` + 4.3(ii) both directions (`lem:removal-deficiency-strict`,
  `lem:splitoff-kdof-criterion`; `lem:case-III-claim-6-11-base` restated in place);
  *L1j* the commuting square `induce_insert_splitOff` + KT 4.8(ii)
  `splitOff_isMinimalKDof_of_pos` (`lem:reduction-step-pos`).
- [x] **L2** — `minimal_kdof_reduction_all_k` (the four-case principle, §1.56(c));
  signature pinned in §1.59; landed in `ForestSurgery.lean` + green
  `thm:minimal-kdof-reduction-all-k` node in `molecular-induction.tex` (2026-06-12).
- [x] **L3** — the base producer (`hbase` carry discharged); pinned §1.60, sliced L3a (the
  LI-extensor-pair-in-`n^⊥` construction) → L3b. **L3a landed**:
  `exists_linearIndependent_extensor_pair_perp` (PanelLayer.lean) + wedge-LI fact
  `linearIndependent_pair_extensor_of_li3` (Extensor.lean) + perp helper `exists_three_perp`
  (PanelLayer.lean); node `lem:extensor-pair-in-panel` green. **All three L3b bare arms landed**:
  `theorem_55_base_producer_{parallel_pair,empty,single_edge}` in CaseI.lean. **L3b dispatch +
  strong-pair GP conjunct landed**: trichotomy-dispatch `theorem_55_base_producer` now concludes the
  §1.60(a) strong pair `(G.Simple → HasGenericFullRankRealization) ∧ HasPanelRealization`; the GP arms
  `theorem_55_base_producer_{empty,single_edge}_gp` (CaseI.lean) build `ofNormals` at an injective
  alg-indep seed (non-root of the GP polynomial → general position + alg-independence); single-edge
  forces the lone extensor nonzero by GP, rank `D−1` via the single-row machinery; empty rank 0;
  parallel-pair vacuous by simplicity. The legacy-`hbase` `.2` rewire of `theorem_55_d3` is unchanged.
  `lem:theorem-55-base-producer{,-empty,-single,-parallel}` green at the strong-pair conclusion.
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

- The remaining verification items of **V1–V10** (§1.56(g)) — V1–V4 resolved by the
  L0/L1 pins; V5 (L4), V6 (L5), V7 (L6), V8 (L7), V9 (L10), V10 (resolved at L0) gate to
  their layer's design pass. V8 (subfamily extraction at rank form) is the one with real
  proof-shape uncertainty left.
- **V-base (L3, §1.60(g)): RESOLVED.** The wedge-LI fact `LI ![a,b,c] → LI ![a∧b, a∧c]` mirrored as
  `linearIndependent_pair_extensor_of_li3` (Extensor.lean). The single-hinge-row rank lemma (arm (ii))
  is `finrank_span_panelRow_edge` (Pinning.lean), reached via `span_panelRow_linking_eq_rigidityRows`
  + the subtype-to-single-edge `hrange` reduction. The single-edge GP arm reuses the standard
  `case_*` opening (`exists_generalPosition_polynomial` +
  `eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent` at an injective alg-indep seed) — no
  new GP single-edge lemma needed; the seed gives general position + alg-independence at once, and the
  rank closes by the same single-row machinery as the bare arm.

## Hand-off / next phase

**L0–L3 complete; the `hbase` carry is fully discharged at KT strength.** The trichotomy-dispatch
`theorem_55_base_producer` concludes the §1.60(a) strong pair
`(G.Simple → HasGenericFullRankRealization 2 n G) ∧ HasPanelRealization 2 n G` = the L9-spine `Pc`
motive; the GP arms (`theorem_55_base_producer_{empty,single_edge}_gp`) are built at an injective
alg-indep seed; the legacy-`hbase` `.2` rewire of `theorem_55_d3` is unchanged. Four carries remain:
`h622`, `h65`, `hsplit`, `hcontract`.

**Smallest next forward commit: open L4** (Lemma 6.1, the not-2-edge-connected / cut-edge reduction
case). Per the layer plan + §1.56(c)/(e): the new reduction case for the cut-edge branch of
`minimal_kdof_reduction_all_k`. **V5 (the fixed-seed transversality route)** gates to L4's design
pass — run the L4 signature pin (its own §1.57+ section) first, reading the target nodes
end-to-end (the red-node consistency gate). The L4 dep-graph node is the Lemma-6.1 cut-edge producer
(the cut-edge decomposition `exists_cut_decomposition_of_not_twoEdgeConnected` from L1e is the
combinatorial input). After L4: L5 (`hcontract`, Lemma 6.2 + the 6.3/6.5 all-`k` restate).

At phase close:
Phase 23 (general `d`, KT Lemma 6.13) opens with its own recon (KT eqs. (6.46)–(6.67) vs the
`d = 3` Lean, §1.33 (C) reuse map) and adds the general-`d` row to
`notes/AlgebraicIndependence.md`.

## Decisions made during this phase

(One-line verdicts; full proof-technique detail lives in the §1.56–§1.58 design sections,
the Lean docstrings, the FRICTION/TACTICS lifts, and git history.)

- **Phase-open (2026-06-11):** §1.56 motive design pass — carrier split (honest bare on
  `BodyHingeFramework` + panels; generic stays on `PanelHingeFramework`); canonical: §1.56.
- **L0 signature pin (2026-06-11):** V1 pointwise `ExtensorInPanel`; V10 via relative
  re-derivation; M5 deletion re-timed to L9; canonical: §1.57.
- **L1 signature pin (2026-06-11):** V2 labeling-free `cutEdges` (connectivity included);
  V3 in-place all-`k`; KT 3.6 as pure partition argument; 4.8(ii) cluster decomposed with
  KT 4.2 as the one new engine; KT numbering corrected vs the PDF; canonical: §1.58.
- **L0a–L0e builds (2026-06-11):** all per the §1.57 pins; M2/M4 placement and the M4
  temporary-`hdef` wrinkle resolved by L0e; `hasFullRankRealization_of_generic` deleted.
- **L1a–L1f builds (2026-06-12):** all per the §1.58 pins; notable deviations (each
  disclosed + benign): singleton-cut bridges moved to `Deficiency.lean` (L1a); `hne`
  dropped from `deficiency_of_edgeSet_empty` (L1b); `[Finite α] [Finite β]` honest
  couplings on the partition split and refinement bound (L1d/L1e); ℤ-subtraction statement
  form → TACTICS-QUIRKS §47 (L1d).
- **L1g (2026-06-12, opus after a sonnet BLOCK):** the reverse acyclicity bricks; the
  `concat_dropLast` + `reverse`-unify route (cleaner than the salvaged notes) → FRICTION
  reverse-cycle-lift entry pointing at the forward §29 idiom.
- **L1h (2026-06-12, opus after a sonnet BLOCK):** both edge-splitting arms, case-ii-first;
  the κ-assignment via `Finset.orderIsoOfFin` (has `.symm`); `_hdeg2` kept underscored for
  the shared pin signature.
- **L1i (2026-06-12, sonnet, resumed after a harness kill):** the 4.4-eq/4.7/4.3(ii)
  quartet; 4.3(ii) forward restated in place (explicit `hH`, one call site); the scoped
  `G - S` notation root cause → TACTICS-QUIRKS §48.
- **L1j (2026-06-12, sonnet):** commuting square + KT 4.8(ii) assembly per the §1.58(g)
  route; `IsKDof`/`IsMinimalKDof` non-reducibility vs `linarith` → TACTICS-GOLF §4 update.
- **L2 signature pin (2026-06-12):** floor flag implemented + the IH-`Nonempty`-guard
  consequence; four-case split verified verbatim vs KT p. 671 (`hcontract` without 2EC is
  paper-faithful); five-slot audit clean; legacy principle stays beside the new one
  (neither derivable from the other); canonical: §1.59.
- **L2 build (2026-06-12, sonnet):** per §1.59 — `minimal_kdof_reduction_all_k` one additive
  commit; `push_neg` → `push Not` (deprecation fix); `thm:minimal-kdof-reduction-all-k` green.
- **L3 signature pin (2026-06-12):** two carries-table/§1.56 corrections, both verified vs the
  landed Lean — (1) the slot is all-`k`/`Nonempty`/`ncard ≤ 2`, so the producer covers a real
  `ncard = 1` arm (the floor flag), not just `ncard = 2`; (2) `theorem_55_base` is the *rank
  engine*, not the producer — the deliverable is a NEW graph-level `theorem_55_base_producer`
  (trichotomy dispatch → parallel-pair `k=0` arm builds two LI extensors in `n^⊥`, feeds
  `theorem_55_base`, lifts via B1; single-edge arm via single-row-`≥` + B2-`≤`; empty arm rank 0).
  One new geometric brick (`exists_linearIndependent_extensor_pair_perp`); GP conjunct: parallel-pair
  excluded by simplicity (vacuity), single-edge GP does real work. Sliced L3a→L3b; blueprint mints
  one node `lem:theorem-55-base-producer`, no statement-grep ripple. Canonical: §1.60.
- **L3b parallel-pair arm (2026-06-12, opus):** `theorem_55_base_producer_parallel_pair` (the
  §1.60(b)(iii) arm, only geometrically-new part of the base producer), shrunk from the full
  producer to fit one sitting — coincident panels `n₀^⊥` (fixed `n₀ = Pi.single 0 1`), L3a brick's
  two LI extensors at the parallel pair, `theorem_55_base` → rigid on `{x,y}=V(G)`, B1 → M2 rank.
  Two benign deviations from §1.60: home is **CaseI.lean** not Pinning.lean (M2 + B1 are
  *downstream* of Pinning — Pinning can't conclude `HasPanelRealization`); **`hD` dropped** (arm
  fixed at `screwDim 2 = 6`). Takes `E(G)={e,f}` as a hypothesis (the trichotomy (iii) output) so
  every link is `e`/`f`. Node `lem:theorem-55-base-producer-parallel` green. No FRICTION (standard
  `if`-reduction + `LinearIndependent.ne_zero` idioms).
- **L3a build (2026-06-12, opus):** the geometric brick, three decls.
  `linearIndependent_pair_extensor_of_li3` (Extensor.lean): `LI ![a,b,c] → LI ![a∧b, a∧c]` via the
  two-subset join-to-isolate technique (left-join with `c`/`b` to kill the cross term; the surviving
  triple wedge nonzero by `extensor_ne_zero_iff_linearIndependent` on a reindex of `![a,b,c]`) —
  resolves the V-base wedge-LI flag, no mathlib basis API. `exists_three_perp` + the target
  `exists_linearIndependent_extensor_pair_perp` (PanelLayer.lean) mirror
  `exists_two_perp_of_linearIndependent_normals` (single-normal kernel, finrank ≥ 3) + the
  `⋀[ℝ]^2`-subtype LI transport idiom from `span_omitTwoExtensor_eq_top`. **Deviation (benign):
  dropped the pinned `hn : n ≠ 0`** — `n^⊥` is ≥3-dim even at `n=0`, so the construction needs no
  nonzero hypothesis; strengthens the lemma, the L3b producer instantiates at a chosen nonzero
  normal anyway. Node `lem:extensor-pair-in-panel` green. No FRICTION (reindex idioms already
  covered).
- **L3b empty + single-edge arms (2026-06-12, sonnet):** two standalone CaseI.lean lemmas
  beside the parallel-pair arm. **Empty arm:** all-zero-extensor framework; `finrank_bot`
  (not `Submodule.finrank_bot`) for rank 0; rank arithmetic via `hG.1` (the `IsMinimalKDof`
  deficiency equality, accessed directly); `hne : V(G).Nonempty` dropped (unused). **Single-edge
  arm:** one nonzero extensor `C ∈ n₀^⊥`; rank closed via `span_panelRow_linking_eq_rigidityRows`
  + `hrange` (subtype-to-single-edge range equality, using `i.val` not `(i : β × _ × _)`) +
  `conv_lhs => rw [hrange]` + `finrank_span_panelRow_edge`; arithmetic via
  `Nat.cast_sub (by decide : 1 ≤ screwDim 2)` + `push_cast`/`ring` (the `↑(n - 1)` cast wall).
  Per-link conjunct: `simp only [hFe]` to reduce `F.supportExtensor e'` before `exact hCin`
  (`(fun _ => n₀) u` beta-reduces but type mismatch blocked direct application). Both arms take
  `[DecidableEq β]` (the `if e' = e` branch in the single-edge framework). No FRICTION.
- **L3b dispatch + `hbase` `.2` rewire (2026-06-13, sonnet; 481fbee):** trichotomy-dispatch
  `theorem_55_base_producer` + the legacy `.2` rewire of `theorem_55_d3` (drops `hbase`, adds
  `hn : bodyBarDim n = screwDim 2`) landed; gates clean; `lem:theorem-55-base-producer` green.
  **Design deviation (caught by coordinator, §1.60(a)/(e) re-read):** the producer's GP conjunct
  landed at the weak `HasPanelRealization` (discharged `fun _ => hprod`) rather than the pinned
  `HasGenericFullRankRealization` — the single-edge genuine GP build + empty GP framework skipped.
  Root cause shared with the pre-commit hand-off, whose (A)/(B) already stated the weak type while
  (A)'s prose described the real GP work. Landed commit kept (the `.2` rewire is correct); corrective
  restate dispatched one rung up (opus). See *Current state* / *Hand-off*; model-experiment row 89.
- **L3b GP-conjunct restate (2026-06-13, opus):** restated `theorem_55_base_producer`'s conclusion to
  the §1.60(a) strong pair `(G.Simple → HasGenericFullRankRealization) ∧ HasPanelRealization`; built
  the two GP arms `theorem_55_base_producer_{empty,single_edge}_gp` (CaseI.lean). Both build
  `ofNormals` at an injective alg-indep seed that is a non-root of `exists_generalPosition_polynomial`
  (so the seed gives general position + alg-independence at once — the standard `case_*` opening, no
  new GP single-edge lemma). Single-edge: GP forces the lone extensor nonzero, rank `D−1` via
  `span_panelRow_linking_eq_rigidityRows` + `finrank_span_panelRow_edge` (the bare arm's single-row
  machinery). Empty: rank 0 (no links), GP/link-recording vacuous; the empty GP arm took the dispatch's
  `hne : V(G).Nonempty` (to pick the irrelevant constant selector body). The `.2` rewire of
  `theorem_55_d3` + `hbaseGP` vacuity unchanged. Blueprint: the `-empty`/`-single` nodes became group
  lemmas (comma-`\lean{}`) with the generic-companion prose; the dispatch node + `def:rank-hypothesis`
  `\uses`. Axiom-clean. One self-inflicted build cycle (a redundant re-`set` of `ends`) → FRICTION
  anti-pattern *Re-`set`ting an already-`set`-bound variable*.
