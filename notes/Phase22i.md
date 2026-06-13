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

**L2 + L3 + L4 + L5a-i + L5a-ii complete; four carries remain: `h622`, `h65`,
`hsplit`, `hcontract`.**
L2 landed `minimal_kdof_reduction_all_k`; L3 landed the base-producer strong pair
`(G.Simple → HasGenericFullRankRealization) ∧ HasPanelRealization` (`hbase` carry discharged).
**L4 fully complete (L4a + L4b)**: block-rank brick, bare-conjunct producer, deficiency-aware rank
polynomial extractor, and GP producer are all Lean-green; `lem:block-rank-cut`,
`lem:case-cut-edge-realization`, `lem:rank-polynomial-of-le-finrank`, and
`lem:case-cut-edge-realization-gp` are all green blueprint nodes.
**L5a-i complete**: `BodyHingeFramework.le_finrank_span_rigidityRows_of_splice` landed in
`RigidityMatrix.lean` (`section SpliceBrick`) ABSTRACT over `D` + the four interface hypotheses
(`hFH_le`, `hFH_ker`, `hFc_surv_le`, `hInj`), proving only the block-triangular rank-nullity;
`lem:rigidityRows-splice-rank-add` green.
**L5a-ii `hInj` discharge complete (the genuinely-new math, split out per §1.64(f))**: the brick's
`hInj` hypothesis — that `(extProj V(H)).dualMap` preserves the contraction's rigidity-row-span rank
at `def = k > 0` — landed as three lemmas in `CaseI.lean` beside the rigid Claim-6.4 versions:
`infinitesimalMotions_sup_range_extProj_eq_top_of_inter_eq_singleton` (the `Z ⊔ W = ⊤` core, proved
by an explicit `z = constant-S r-on-V(G)` decomposition — NO rank count, NO rigidity, the deficiency-
tolerant content of KT Lemma 5.1) → `BodyHingeFramework.injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton`
(the dual-API mirror of the rigid `injOn_extProj_dualMap_rigidityRows`, swapping in the rigidity-free
`Z ⊔ W = ⊤`) → `BodyHingeFramework.finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton`
(the direct `hInj`-form `finrank Sc = finrank (Sc.map D)`, via rank-nullity on `D|Sc`). Mints
`lem:extProj-preserves-rank-of-inter` (rigidity-matrix.tex, beside the splice brick). All three
axiom-clean; build+lint+blueprint-verify green. V6-a fully RESOLVED.
**L5a-ii producer complete**: `case_I_realization_nonsimple` (CaseI.lean) landed; `lem:case-I-realization-nonsimple` green.
**L5b-i fully complete (V6-b leaf RESOLVED, 2026-06-13, route 2 taken).** The two-sub-commit
split (shared core → completion) is done:
- Shared core: `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_relabel_eq` (CaseI.lean)
  carries the contraction IH's `D(|V|−1) − def` rank across the collapse-relabel selector swap
  as a finrank equality. Mints `lem:rank-transport-relabel-of-le-finrank`.
- Completion: `PanelHingeFramework.exists_rankPolynomial_of_IH_relabel_linking` (CaseI.lean,
  route 2 via `exists_rankPolynomial_of_le_finrank_linking`). Produces `N : ℕ` satisfying
  `(N : ℤ) = D(|sc|−1) − def` + a nonzero rational `Q` s.t. `N ≤ finrank (span Sc at q)` for
  non-root `q`. Mints `lem:rank-polynomial-IH-relabel` (rigidity-matrix.tex, green).
  All gates clean (build+lint+checkdecls; axiom-clean; `haveI : Loopless` pattern for `IsLink.ne`).

**Next: a design pass (§1.66) to resolve L5b-ii's `hFc_surv_le` route.** L5b-ii BLOCKED
(2026-06-13, sonnet; HEAD unchanged, tree clean) — the route-2 leaf gives the surviving-block
*rank* but NOT the splice brick's *containment* `hFc_surv_le : (span Fc.rigidityRows).map D ≤
(span F.rigidityRows).map D`, which holds at a collapse/degenerate placement (as the non-simple
producer used via `hingeRow_collapseTo_comp_extProj_eq`) but NOT at the GP builder's fresh generic
seed. Coordinator-verified (brick signature RigidityMatrix:3213; non-simple discharge route).
`P≈2` was optimistic. See *Hand-off* for the two candidate routes (route-1 `_proj` vs route-2
degenerate-seed, reusing the existing `degeneratePlacement` / `panelRow_collapseTo_comp_extProj_dualMap`
infra).
**The defect:** §1.63 stated the contraction leg as `induce ((V(G)∖V(H))∪{r})` framed as a *bare,
transversality-free* brick — but `rigidContract G H r = (G ＼ E(H)).map (collapseTo r V(H))` COLLAPSES V(H)→r
(same vertex set as `induce` but **keeps the relabelled crossing edges** `induce` drops), so the induce-leg
bound is strictly too weak and the IH realizes the *contraction* (minimal-`k`-dof by
`rigidContract_isMinimalKDof`), not the induce-leg. **§1.64's corrected route** (verified against the landed
Lean): the genuine (6.3)–(6.5) additivity at `def = k > 0` is the **block-triangular `≥`** (eq. 6.3,
elementary) + **Lemma 5.1** column-deletion (`finrank_pinnedMotions_add_screwDim`, general-rank, NO rigidity) —
**NOT** the full-rigidity-gated `injOn_extProj_dualMap_rigidityRows`/Claim-6.4 machinery (which is unavailable
at `k > 0`, since the contraction is then deficient, not rigid), and **NOT** a bare span split (the splice's
legs share the contracted body and have many crossing edges, so L4a's disjointness route does not transfer).
The brick is assembled from landed *rigidity-free* pieces — but the projected-image-rank step is genuinely
new linear algebra (a real brick, its own slice; §1.64(c) honesty flag). NO IH/motive change. L5 discharges
`hcontract` by a `by_cases G.Simple` dispatch (§1.63(a), unaffected): simple → forgetful M4 ∘ the
all-`k`-restated GP `case_I_realization` (6.5 sub-arm carried as `h65`, L8); non-simple → KT Lemma 6.2.
V6 RESOLVED (N6a dead infrastructure); **V6-a re-aimed** at the corrected brick (§1.64); **V6-b re-scoped**
(the simple all-`k` restate needs the brick's GP variant too — not mechanical, §1.64(f) L5b caveat).
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
| `hcontract` (the bare Case-I branch) | `def:genuine-hinge-realization` | `theorem_55_d3` (:6809) | **L5** (re-pinned §1.64): dispatch on `G.Simple` — simple → forgetful (M4) ∘ the 6.3/6.5 GP arm; non-simple → KT Lemma 6.2 (the coincident-panel splice). The eq. (6.3)–(6.5) rank addition is the **block-triangular `≥` + Lemma 5.1** column-deletion (`finrank_pinnedMotions_add_screwDim`, general-rank), assembled into a NEW general-rank shared-body brick `le_finrank_span_rigidityRows_of_splice` — NOT the rigidity-gated `injOn_extProj`/Claim-6.4 route (unavailable at `k>0`), NOT a bare span split. Re-cut L5a-i (brick) → L5a-ii (producer) → L5b; L5b further decomposed (§1.65) into L5b-i (the V6-b `def=k>0` projected rank-transport brick, `P≈3`) → L5b-ii (`case_I_realization_all_k`) → L5b-iii (dispatch) |

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
- [x] **L4a** — block-rank brick + bare-conjunct producer; both Lean-green; `lem:block-rank-cut`
  + `lem:case-cut-edge-realization` green. V5-a resolved. Canonical: §1.61(b)/(c).
- [x] **L4b-1** — `PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking` (GenericityDevice.lean),
  `lem:rank-polynomial-of-le-finrank` green. Two-swap copy of `exists_rankPolynomial_of_rigidOn_linking`:
  (i) W6e `exists_independent_panelRow_subfamily_of_le_finrank` replaces the rigid N7b-0; (ii) conclusion
  rephrased to `N ≤ finrank rigidityRows` via `finrank_span_eq_card` + `Submodule.finrank_mono`.
- [x] **L4b-2** — `case_cut_edge_realization_gp` (CaseI.lean), the GP producer. Lean-green, axiom-clean,
  build+lint clean. Blueprint: `lem:case-cut-edge-realization-gp` (molecular-induction.tex) green.
  Canonical: §1.62(d).
- [x] **L5a-re-pin** — §1.64: corrected §1.63(c)/(f). The contraction leg is `rigidContract` (collapse), not
  `induce`; the (6.3)–(6.5) additivity is the **block-triangular `≥` + Lemma 5.1** column-deletion
  (general-rank, `finrank_pinnedMotions_add_screwDim`), assembled into a NEW general-rank brick — NOT the
  rigidity-gated `injOn_extProj`/Claim-6.4 route (unavailable at `k>0`), NOT a bare span split. Honesty flag:
  buildable, NO IH/motive change, but the projected-image-rank step is genuinely-new math (its own slice).
  V6-a re-aimed; V6-b re-scoped (the simple all-`k` restate needs the brick's GP variant). Re-cut to three
  leaves. Canonical: §1.64.
- [ ] **L5** — Lemma 6.2 (non-simple Case I) + the 6.3 all-`k` restate of `case_I_realization`
  (`hcontract` carry discharged; the 6.5 sub-arm stays carried as `h65` → L8). Sliced **L5a-i** → **L5a-ii**
  → **L5b** (§1.64(f)):
  - [x] **L5a-i** — `BodyHingeFramework.le_finrank_span_rigidityRows_of_splice` (the general-rank shared-body
    block-triangular block-rank brick, RigidityMatrix.lean beside `le_finrank_span_rigidityRows_of_cut`). **The
    one genuinely-new math of L5** (rank-nullity of `(extProj V(H)).dualMap` ⊕ Lemma 5.1 column-deletion ⊕ the
    rigidity-free collapse row-correspondence). Mints `lem:rigidityRows-splice-rank-add`. V6-a RESOLVED. Key
    quirk: `letI` (not `haveI`) needed to shadow global `Submodule.addCommMonoid` with `AddCommGroup ↥S` — see
    FRICTION entry (`letI` vs `haveI` for `AddCommMonoid`/`AddCommGroup` instance diamond on submodules).
  - [x] **L5a-ii `hInj` discharge** — the genuinely-new column-deletion math, split out of the producer per
    §1.64(f)'s sanction. Three lemmas in `CaseI.lean` (beside the rigid Claim-6.4 versions):
    `infinitesimalMotions_sup_range_extProj_eq_top_of_inter_eq_singleton` (rigidity-free `Z ⊔ W = ⊤` via the
    explicit `z = const-S r-on-V(G)` decomposition) → `…injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton`
    → `…finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton` (the direct `hInj`-form). Mints
    `lem:extProj-preserves-rank-of-inter`. V6-a RESOLVED.
  - [x] **L5a-ii producer** — `case_I_realization_nonsimple` (CaseI.lean, beside `case_cut_edge_realization`):
    IH on the *contraction* `rigidContract G H r` + the L5a-i brick fed the discharged `hInj` + the three other
    interface hyps + B2 + coincident-panel extensors (`exists_linearIndependent_extensor_pair_perp`) +
    `isKDof_zero_of_parallel_pair`. Mints `lem:case-I-realization-nonsimple` (green, blueprint-verify clean).
    (The old bare `induce`-brick + producer 90e8d4a was built then reverted, superseded by this structure.)
  - [ ] **L5b** — the all-`k` GP restate `case_I_realization_all_k` + the `by_cases G.Simple` dispatch.
    **Decomposed §1.65 (2026-06-13) into three leaves**, the V6-b brick first:
    - [x] **L5b-i** — the **V6-b leaf** (`P≈3`, the genuinely-new math of L5b), sliced per §1.65(g):
      - [x] **shared core** — `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_relabel_eq` (CaseI.lean):
        the deficiency-aware relabel transport, carrying the contraction IH's `D(|V|−1) − def` rank across the
        collapse-relabel selector swap. Mints `lem:span-rigidityRows-eq-of-motions-eq` +
        `lem:rank-transport-relabel-of-le-finrank`.
      - [x] **completion** — `PanelHingeFramework.exists_rankPolynomial_of_IH_relabel_linking` (CaseI.lean,
        route 2: shared core → `exists_rankPolynomial_of_le_finrank_linking`). Produces `N : ℕ` with
        `(N : ℤ) = D(|sc|−1) − def` + nonzero rational `Q` s.t. `N ≤ finrank (span Sc at q)` for
        non-root `q`. Mints `lem:rank-polynomial-IH-relabel` (rigidity-matrix.tex, green).
    - [ ] **L5b-ii** — `case_I_realization_all_k` (the GP producer, the splice-brick analogue of L4b-2's
      `case_cut_edge_realization_gp`): assembly of landed pieces + the L5b-i leaf + the L5a-i splice brick + B2.
      **BLOCKED (2026-06-13) on the splice brick's `hFc_surv_le` containment** — the route-2 leaf gives
      the surviving-block rank but not the containment (holds at a collapse/degenerate placement, not the
      GP builder's generic seed). `P≈2` was optimistic; the real obstacle is the §1.65 core P≈3 difficulty.
      Awaiting the **§1.66 design pass** (route-1 `_proj` vs route-2 degenerate-seed) — see *Hand-off*.
      Then mints `lem:case-I-realization-all-k`.
    - [ ] **L5b-iii** — the `hcontract` slot-filler dispatch (`by_cases G.Simple`): plumbing (`P≈1`); the 6.5
      sub-arm stays red → L8. Updates `lem:case-I-dispatch`.
  V6 RESOLVED — N6a is dead infrastructure (deleted-motive-bound, `ofNormals`-bound); V4
  (`rigidContract_isMinimalKDof` all-`k`) confirmed already-landed; **V6-a re-aimed + V6-b re-scoped (§1.64)**.
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
  L0/L1 pins; V5 resolved at the L4 pin (§1.61), splitting into **V5-a** (the disjoint-block
  additivity route, resolved at L4a's build) and **V5-b** (the GP-conjunct seed question,
  **RESOLVED at the L4b design pass, §1.62** — see below); **V6 RESOLVED at the L5 pin (§1.63)** —
  N6a is dead infrastructure for the honest motive (deleted-`HasFullRankRealization`-bound,
  `ofNormals`-bound), so the non-simple Lemma-6.2 producer is built fresh on `BodyHingeFramework`, NOT
  re-aimed. **V6-a re-aimed at the corrected brick (L5a re-pin §1.64, 2026-06-13):** the §1.63(c) "bare,
  `induce`-leg, transversality-free" splice brick was WRONG (the contraction leg is `rigidContract`, a collapse
  that keeps crossing edges, not `induce`). §1.64 settled the corrected route: the (6.3)–(6.5) additivity is the
  **block-triangular `≥` + Lemma 5.1 column-deletion** (`finrank_pinnedMotions_add_screwDim`, **general-rank, no
  rigidity**), assembled into a NEW general-rank shared-body brick `le_finrank_span_rigidityRows_of_splice` from
  landed rigidity-free pieces — **NOT** the full-rigidity-gated `injOn_extProj_dualMap_rigidityRows`/Claim-6.4
  route (which is unavailable at `def = k > 0`, since the contraction is then deficient, not rigid), and **NOT**
  a bare span split (the splice legs share the contracted body + many crossing edges). V6-a now = the brick's
  exact correspondence-hypothesis form, resolves at the L5a-i build. **Honesty flag (§1.64(c)):** the route is
  buildable + needs NO IH/motive change, but the projected-image-rank step is genuinely-new linear algebra (a
  real brick, its own L5a-i slice — not a one-liner). **V6-b RESOLVED at the pin level (§1.65, 2026-06-13) —
  re-rated `P≈3`** (the §1.64(f) "GP variant, still buildable" wording understated it as `P≈2`): the *simple*
  all-`k` Case-I restate's surviving block needs a `def = k > 0` exterior-projected rank transport — the
  `_le_finrank` analogue of the rigid `rigidContract_exterior_rank_transport` +
  `exists_rankPolynomial_of_rigidOn_linking_set_proj` chain (both `hdef=0`-gated). No landed `_proj` tool is
  deficiency-aware, so this is a **real new brick** (L5b-i), with a **flagged open internal-route decision**
  (§1.65(c): route-1 `_proj` mirror vs route-2 pulled-back full-span + the landed L5a-ii `hInj`; both need a
  deficiency-aware relabel transport). No motive/IH change. Resolves (route + build) at L5b-i. V7 (L6), V8 (L7),
  V9 (L10), V10 (resolved at L0) gate to their layer's design pass.
- **V5-b RESOLVED (§1.62); V8 (L7) is the one item with real proof-shape uncertainty left.**
  V5-b's §1.61(d) framing (combine the two IH side seeds — Route GP-1 reseed vs GP-2 union) rested
  on a false premise: the project never combines IH seeds (the Case-I GP composer builds *one fresh
  combined seed* and transfers each leg's rank via a rational-rank-polynomial non-root), and the
  naive "disjoint-union alg-indep" fact is unsound anyway (mathlib's `AlgebraicIndependent.sumElim_iff`
  needs alg-indep over the adjoined field). The real question was **rank-lower-bound transfer for the
  *deficient* (non-rigid) sides**, resolved by the already-landed rigidity-free W6e extractor
  (`exists_independent_panelRow_subfamily_of_le_finrank`) + the seed-transfer engine. **Route GP-2
  viable, NO IH statement-level change** (decision-guard GP-1 escape NOT triggered); one new
  project-internal piece (the deficiency-aware extractor, L4b-1). The bare conjunct (L4a) was always
  transversality-free / seed-free.
- **V-base (L3, §1.60(g)): RESOLVED.** The wedge-LI fact `LI ![a,b,c] → LI ![a∧b, a∧c]` mirrored as
  `linearIndependent_pair_extensor_of_li3` (Extensor.lean). The single-hinge-row rank lemma (arm (ii))
  is `finrank_span_panelRow_edge` (Pinning.lean), reached via `span_panelRow_linking_eq_rigidityRows`
  + the subtype-to-single-edge `hrange` reduction. The single-edge GP arm reuses the standard
  `case_*` opening (`exists_generalPosition_polynomial` +
  `eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent` at an injective alg-indep seed) — no
  new GP single-edge lemma needed; the seed gives general position + alg-independence at once, and the
  rank closes by the same single-row machinery as the bare arm.

## Hand-off / next phase

**L0–L5a complete; four carries remain: `h622`, `h65`, `hsplit`, `hcontract`.**

L5a-ii is done: `case_I_realization_nonsimple` (CaseI.lean) + `lem:case-I-realization-nonsimple`
(case-i.tex) both green; blueprint-verify clean. V6-a fully RESOLVED; §1.64 canonical.

**L5b design-pass complete (§1.65, 2026-06-13, opus; tree clean, docs-only).** The row-104 BLOCK's
structural diagnosis was **re-verified against the landed source** (every load-bearing decl opened, not
trusted from prose) and is correct: `case_I_realization`'s surviving block routes through the rigid
`rigidContract_exterior_rank_transport` (CaseI:1682, `hdef=0` at :1684) +
`exists_rankPolynomial_of_rigidOn_linking_set_proj` (CaseI:1506), and the final rigid coupler
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set` (CaseI:1988) is doubly `0`-dof-gated
(hard `hdef=0` at :2013 + a full-`D(|sc|−1)` projected-rank demand at :2010). So the all-`k` simple restate
cannot thread the landed proof; it follows the **L4b-2 GP-builder pattern** (`case_cut_edge_realization_gp`,
CaseI:8108) with the L5a-i **splice** brick instead of the cut brick. §1.65 re-cut L5b into three leaves and
**re-rated the V6-b leaf `P≈3`** (a real new brick, not the §1.64(f) "GP variant" understatement that read
`P≈2`). **Flagged open decision (§1.65(c)):** the V6-b leaf's *internal* route — route-1 (`_proj` rank-transport
mirror of the rigid chain) vs route-2 (pulled-back full-span rank polynomial + the landed L5a-ii `hInj`) — is
left unpinned; both need a **deficiency-aware relabel-and-extract transport** as their irreducible new core (no
landed `_proj` extractor / `_proj` rank polynomial is deficiency-aware; `hasGenericRealization_transport_relabel`
is `hdef=0`-gated), and the route is best chosen at the build with the goal state open. Soft recommendation:
route 2 (smaller new surface, leans on the just-landed L5a-ii / L4b-1). No motive / IH change.

**L5b-i fully complete (2026-06-13, sonnet; both sub-commits landed).** Route 2 taken for the
completion: shared-core `finrank_span_rigidityRows_ofNormals_relabel_eq` → rank polynomial
`exists_rankPolynomial_of_IH_relabel_linking` via `exists_rankPolynomial_of_le_finrank_linking`
at the witness seed with `hN := le_refl`. The §1.65(c) flagged decision resolved in favour of
route 2 (no new `_proj` surface; `IsLink.ne` needs `haveI : Loopless` not hypothesis dot-access).
`lem:rank-polynomial-IH-relabel` green; all gates clean.

**L5b-ii BLOCKED on `hFc_surv_le` (2026-06-13, sonnet; HEAD unchanged, tree clean) — the route-2
leaf gives rank, not containment.** The splice brick (RigidityMatrix:3213) needs BOTH `hInj`
(rank preserved, landed L5a-ii) AND `hFc_surv_le : (span Fc.rigidityRows).map D ≤
(span F.rigidityRows).map D` (a span **containment**). The L5b-i route-2 polynomial
`exists_rankPolynomial_of_IH_relabel_linking` supplies only the surviving-block *rank* lower bound
at a *generic* seed — nothing about the containment. `hFc_surv_le` holds when Fc's hinge rows
correspond to F's, i.e. at a **collapse/degenerate** placement (the non-simple producer
`case_I_realization_nonsimple` discharged it via `hingeRow_collapseTo_comp_extProj_eq`), NOT at the
GP builder's fresh generic seed. So route-2's full-span-at-generic-seed and the producer's
containment-needs-collapse **conflict on the seed**. Coordinator-verified (brick signature; the
non-simple discharge route). The §1.65(c) route-2 soft-rec was the wrong tool for the producer; the
boundary pair (rows 107–108) validated route 2 as a *lemma* but neither member checked it against
the producer's `hFc_surv_le`.

**Smallest next forward commit: a design pass (§1.66)** to resolve the route + re-decompose L5b-ii.
Two candidate unblocks (BLOCKED-agent diagnosis, coordinator-verified): (1) **route-1 `_proj`** — a
deficiency-aware *projected* rank polynomial for the surviving block that ALSO yields
`(span Fc.rigidityRows).map D ≤ (span F.rigidityRows).map D` at the seed (~3 new GenericityDevice
lemmas, the `_proj` analogue of L4b-1); (2) **route-2 degenerate-seed** — reuse the EXISTING
collapse machinery (`degeneratePlacement` CaseI:907, `panelRow_collapseTo_comp_extProj_dualMap`
CaseI:940 — which already reconcile the differing endpoints under the degenerate placement) so the
degenerate placement discharges `hFc_surv_le`, then show the L5b-i polynomial `Q` is nonzero at
`degeneratePlacement r V(H) q₀` for generic `q₀` (the only genuinely-new piece; the rest is landed).
The design pass reads the existing degeneratePlacement infra, picks the route, decides whether the
L5b-i route-2 completion is reused (option 2) or superseded (option 1), and re-decomposes L5b-ii
with exact signatures. fable-mapped (→ opus sub). Canonical-to-be: §1.66.

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
- **L0a–L0e + L1a–L1j builds (2026-06-11/12; sonnet, with L1g/L1h opus after sonnet BLOCKs in the
  KT-4.2/WList zone):** all per the §1.57/§1.58 pins — motives M1–M5 + bridges B1/B2 + the
  conditioned-pair swap (L0, `hasFullRankRealization_of_generic` deleted); the combinatorial bricks
  `cutEdges`/`TwoEdgeConnected` + trichotomy + KT-3.6 partition + reverse-acyclicity + edge-splitting
  + commuting-square/4.8(ii) (L1). Promoted: FRICTION reverse-cycle-lift; TACTICS-QUIRKS §§47/48;
  TACTICS-GOLF §4. Per-slice detail: git + §1.57/§1.58.
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
- **L4 signature pin (2026-06-13):** Lemma 6.1 cut-edge case pinned; canonical: §1.61. V5 resolved — the
  closing `≤` is free (B2, landed, `V(G)`-relative); the substance is the lower bound `≥`, a NEW
  vertex-disjoint block-rank-addition brick (`BodyHingeFramework.le_finrank_span_rigidityRows_of_cut`, the
  disjoint-support refinement of the landed single-edge span split), the project's fixed-seed route in
  place of KT's isometry. KT Lemma 6.1 verified vs the PDF (p. 672); KT's disconnected/connected cases
  unify via the L1e `cutEdges.ncard ∈ {0,1}` arithmetic. One graph-level producer at `Pc` (no current
  consumer; wires at L9). Sliced L4a (brick + bare conjunct, transversality-free) → L4b (GP conjunct,
  gated on the V5-b seed-combination open sub-question — flagged to coordinator, may force an IH
  statement-level change).
- **L4a + L4b builds (2026-06-13; sonnet, opus micro-pass):** the cut-edge (Lemma 6.1) arm — the NEW
  vertex-disjoint block-rank brick `le_finrank_span_rigidityRows_of_cut` (RigidityMatrix) + bare producer
  `case_cut_edge_realization` (L4a, `lem:block-rank-cut` / `lem:case-cut-edge-realization` green);
  **V5-b RESOLVED (opus micro-pass, §1.62): Route GP-2, NO IH change**; the deficiency-aware rank-poly
  extractor `exists_rankPolynomial_of_le_finrank_linking` (L4b-1) + GP producer
  `case_cut_edge_realization_gp` (L4b-2 — **the GP-builder pattern L5b-ii mirrors with the splice brick**).
  Promoted: TACTICS-QUIRKS §§49–53. Per-slice detail: git + §1.61/§1.62.
- **L5 signature pin (2026-06-13):** the non-simple Case-I branch (KT Lemma 6.2) pinned; canonical: §1.63.
  KT 6.2 verified vs the PDF (pp. 673–674): `G' = G[{e,f}]` parallel-pair proper-rigid, Lemma-5.3 coincident-
  panel base `Π(a)=Π(b)`, splice at `Π(v*)=Π(a)=Π(b)`, eq. (6.3)–(6.5) block-triangular rank addition. **V6
  RESOLVED against a re-aim:** N6a `hasFullRankRealization_of_splice_of_supportExtensor` (GenericityDevice:915)
  concludes the M5-*deleted* `HasFullRankRealization` and is `ofNormals`/derived-hinge-bound — unusable for the
  free-hinge M2 motive at coincident panels — so L5a builds fresh on `BodyHingeFramework` in the landed L4a
  `case_cut_edge_realization` idiom, reusing `exists_extensor_in_two_panels` (works AT `n₁=n₂`) for the
  coincident-panel hinge. The `hcontract` slot is a `by_cases G.Simple` dispatch (§1.55(c) precedent, all-`k`):
  simple → M4-forgetful ∘ all-`k`-restated GP `case_I_realization` (6.5 sub-arm carried as `h65` → **L8, not
  L5**); non-simple → the Lemma-6.2 bare producer. V4 (`rigidContract_isMinimalKDof`) confirmed already all-`k`
  in tree. Sliced L5a (the bare producer + the NEW shared-body block-rank brick
  `le_finrank_span_rigidityRows_of_splice`, the only new math) → L5b (the all-`k` GP restate + dispatch). Adds
  V6-a/V6-b, both `buildable`; no research-shaped open question. Docs-only; no Lean/`.tex` edits.
- **L5a-i boundary pair — §1.63(c)/(f) splice brick is WRONG, brick reverted (2026-06-13):** a sonnet/opus
  boundary pair on the L5a-i brick caught a design error the §1.63 pin + my own scrutiny missed (opus
  duplicate BLOCKED with the diagnosis; sonnet primary's faithful-to-the-pin `induce`-brick, 90e8d4a,
  reverted). The pin stated the splice's contraction leg as `induce ((V∖V(H))∪{r})` — a *bare,
  transversality-free* brick — but `rigidContract` *collapses* V(H)→r (keeps the relabelled crossing edges
  `induce` drops), so the induce-leg rank `≠ D(|V|−2)−k` and the bound is too weak; the genuine (6.3)–(6.5)
  additivity is the `extProj`/Claim-6.4 *rigidity-gated* machinery (the landed `case_I_realization` route),
  not a bare span split. V6-a REOPENED; the L5a re-pin design-pass is next. **Experiment signal:** the
  boundary pair did exactly its job — opus caught a wrong-for-purpose green commit on master.
  Model-experiment rows 97 (primary) / 98 (duplicate).
- **L5a re-pin (2026-06-13, opus; §1.64):** corrected §1.63(c)/(f) — every load-bearing signature re-verified
  against the landed Lean. The contraction leg is `rigidContract` (collapse), not `induce`. The `def = k > 0`
  crux: the landed `injOn_extProj_dualMap_rigidityRows`/Claim-6.4 route is full-rigidity-gated and unavailable
  at `k>0` (contraction is then deficient); KT (6.4)/(6.5) instead use **Lemma 5.1** =
  `finrank_pinnedMotions_add_screwDim` (general-rank, no rigidity) + the elementary block-triangular `≥`. The
  new brick `le_finrank_span_rigidityRows_of_splice` assembles landed *rigidity-free* pieces (`extProj`
  row-vanishing, the collapse row-correspondence, the deficiency-aware `_of_le_finrank` extractor, Lemma 5.1).
  **Verdict: buildable, NO IH/motive change.** Honesty flag (§1.64(c)): the projected-image-rank step is
  genuinely-new linear algebra — a real brick (its own L5a-i slice), not a one-liner; no decision needs
  adjudication. L5b caveat (§1.64(f)): the simple all-`k` restate also needs the brick's GP variant (V6-b
  re-scoped, not mechanical). Re-cut to L5a-i (brick) → L5a-ii (producer) → L5b. Docs-only.
- **L5a-i build (2026-06-13, sonnet):** `BodyHingeFramework.le_finrank_span_rigidityRows_of_splice` in
  `RigidityMatrix.lean` (`section SpliceBrick`). Proof: `letI hSAG : AddCommGroup ↥S := S.addCommGroup`
  to shadow the global `S.addCommMonoid` instance (needed because `domRestrict`/`finrank_quotient_add_finrank`
  live in the Ring/AddCommGroup world, while submodule ops default to the Semiring/AddCommMonoid path — these
  two `AddCommMonoid ↥S` instances are NOT definitionally equal; `letI` shadows where `haveI` does not);
  then `(D.domRestrict S).ker.finrank_quotient_add_finrank` for quotient rank-nullity; `quotKerEquivRange` +
  `range_domRestrict` for the quotient ≅ image identification; `ker_domRestrict` + `finrank_map_subtype_eq` +
  `map_comap_subtype` for the kernel ≅ `S ⊓ ker D`; outer `linarith`. Brick is ABSTRACT over `D` + the four
  interface hyps incl. `hInj` (the genuinely-new content relocated to the next slice). Key quirk →
  TACTICS-QUIRKS §54. `lem:rigidityRows-splice-rank-add` (rigidity-matrix.tex) green.
- **L5a-ii `hInj` discharge (2026-06-13, opus):** the §1.64(c) genuinely-new column-deletion math, split out of
  the producer (§1.64(f) sanctioned splitting the rank-nullity / Lemma-5.1 halves). Three lemmas in `CaseI.lean`
  beside the rigid Claim-6.4 versions. The crux `infinitesimalMotions_sup_range_extProj_eq_top_of_inter_eq_singleton`
  proves the general-rank `Z ⊔ W = ⊤` by an **explicit decomposition, no rank count, no rigidity**: any `S` =
  `z + (S−z)` with `z a = if a ∈ V(G) then S r else S a` (a motion — constraints have both endpoints in `V(G)`
  where `z` is the constant `S r`) and `S − z` vanishing on `proj = {r} ∪ (proj∖V(G))`. The rigid sibling's count
  route (`finrank_pinnedMotionsOn_of_isInfinitesimallyRigidOn_...`) was NOT reusable (rigidity propagates `S r = 0`
  to all of `V(G)`, false at `def > 0`) — the explicit-`z` route sidesteps it. Then dual-API mirror →
  `injOn_…_of_inter_eq_singleton` (swap `Z ⊔ W = ⊤` input only), `hInj`-form via rank-nullity on `D|Sc`. Mints
  `lem:extProj-preserves-rank-of-inter`. Axiom-clean. V6-a fully RESOLVED. FRICTION: `disjoint_ker_iff_injOn`
  (not deprecated `disjoint_ker'`).
- **L5a-ii producer (2026-06-13, sonnet):** `case_I_realization_nonsimple` (CaseI.lean). Proof: `¬G.Simple` +
  looplessness → parallel pair `(e, f, a, b)`; `H' = G[{a,b}] ↾ {e,f}` with `V(H') = {a,b}`, `E(H') = {e,f}`;
  `isKDof_zero_of_parallel_pair` + ssubset proof from `|V(G)| ≥ 3` → `H'.IsProperRigidSubgraph`; IH on
  `G.rigidContract H' a`; `normal := Fc_normal ∘ collapseTo a V(H')` (coincident panels); LI extensors
  `Ce, Cf ∈ (normal a)^⊥` via `exists_linearIndependent_extensor_pair_perp`; assemble `F`/`FH`; four
  splice-brick hyps discharged (`hFH_le`: row inclusion; `hFH_ker`: `change`+`simp [dualMap_apply']`+
  `hingeRow_comp_extProj_eq_zero`; `hInj`: `finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton`
  + `rigidContract_vertexSet_inter_eq_singleton`; `hFc_surv_le`: `simp [dualMap_apply']+
  hingeRow_collapseTo_comp_extProj_eq`); B2 closes upper bound; arithmetic `D + (D(|V|−2)−k) = D(|V|−1)−k`.
  Key quirks: `set H'` with `hH'_def`; `simp only [ht_def]` to see through the `set`-defined `t` for
  `hlink.left_mem`; `change` (not `show`) for goals that differ up to definitional equality; `rw [hFcg,
  Graph.rigidContract, Graph.map_isLink]` to unpack contraction links in `hFc_surv_le`. Mints
  `lem:case-I-realization-nonsimple` (case-i.tex) green.
- **L5b design-pass (2026-06-13, opus; §1.65):** decomposed the BLOCKED all-`k` simple GP restate into three
  leaves (L5b-i V6-b brick → L5b-ii `case_I_realization_all_k` producer → L5b-iii dispatch); every load-bearing
  decl re-verified against the landed source (the BLOCK's diagnosis confirmed: `case_I_realization`'s surviving
  block + final coupler are `0`-dof-gated, CaseI:1682/:1506/:1988). Target shape = the **splice analogue of
  L4b-2's `case_cut_edge_realization_gp`** (NOT the rigid coupler). **V6-b re-rated `P≈3`** (a real new brick,
  the deficient `_le_finrank` reconstruction of the rigid U3a/U3b/U2-proj + rank-polynomial-proj chain — no
  landed `_proj` tool is deficiency-aware). **Flagged open decision (not forced):** the V6-b internal route
  (route-1 `_proj` mirror vs route-2 pulled-back full-span + the landed L5a-ii `hInj`) is left unpinned — both
  need a deficiency-aware relabel transport; resolve at the L5b-i build with the goal state open. No motive/IH
  change. Canonical: §1.65.
- **L5b-i shared core (2026-06-13, opus):** the deficiency-aware relabel transport
  `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_relabel_eq` (CaseI.lean) — the §1.65(g)-sanctioned
  sub-commit split of the `P≈3` V6-b leaf. The "exact rank invariant" §1.65(c) flagged as the real uncertainty
  is a plain finrank *equality* (the IH's `D(|V|−1) − def` value), carried rigidity-free across the
  collapse-relabel selector swap by the existing motion-space swap brick
  `infinitesimalMotions_ofNormals_eq_of_ends_swap` + two new RigidityMatrix helpers (`Φ = Z°` factoring +
  equal-motions⟹equal-rank). Axiom-clean; all gates green.
- **L5b-i completion (2026-06-13, sonnet):** **route 2** taken: shared core → `exists_rankPolynomial_of_le_finrank_linking`
  (L4b-1) at the witness `nrm` with `hN := le_refl`. `PanelHingeFramework.exists_rankPolynomial_of_IH_relabel_linking`
  (CaseI.lean) produces `N : ℕ` with `(N : ℤ) = D(|sc|−1)−def` + nonzero rational `Q` s.t. `N ≤ finrank
  (span Sc at q)` for non-root `q`. The `hne` (support extensor nonzero) comes from GP + `haveI : Loopless`
  (IsLink.ne needs the Loopless instance, not a hypothesis — writing `hloop.isLink_ne` fails). V6-b RESOLVED.
  Mints `lem:rank-polynomial-IH-relabel`. Axiom-clean; all gates clean.
