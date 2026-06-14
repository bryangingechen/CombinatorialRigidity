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

**L2–L5b-iii complete; three carries remain: `h622`, `h65`, `hsplit`. `hcontract` discharged.**
L2 landed `minimal_kdof_reduction_all_k`; L3 landed the base-producer strong pair
`(G.Simple → HasGenericFullRankRealization) ∧ HasPanelRealization` (`hbase` carry discharged).
**L4 fully complete (L4a + L4b)**: block-rank brick, bare-conjunct producer, deficiency-aware rank
polynomial extractor, and GP producer are all Lean-green; `lem:block-rank-cut`,
`lem:case-cut-edge-realization`, `lem:rank-polynomial-of-le-finrank`, and
`lem:case-cut-edge-realization-gp` are all green blueprint nodes.
**L5b-ii-a complete**: `BodyHingeFramework.exists_independent_panelRow_subfamily_of_le_finrank_proj`
(CaseI.lean, beside the rigid sibling) landed; the deficiency-aware `_proj` extractor, two-swap
mirror of the rigid sibling (W6e `_le_finrank` + rigidity-free `injOn` core). No blueprint node.
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

**L5b-ii route RESOLVED (§1.66 design pass, 2026-06-13, opus; docs-only, tree clean): route 1
(`_proj`-coupler mirror), NOT route 2.** The §1.66 pass opened the landed rigid `case_I_realization`
and found `hFc_surv_le` is a **DEAD END for the GP producer** — not a discharge gap but a *mechanism
mismatch*. `hFc_surv_le`'s load-bearing step (non-simple producer, CaseI:8792) needs `F`'s and `Fc`'s
**support extensors parallel on surviving edges**; the bare producer hand-builds `F` to copy `Fc`'s
extensors, but the GP conjunct forces `F = ofNormals G G.endsOf q₀` whose crossing-edge extensor
`panelSupportExtensor (q₀ u)(q₀ v)` (with `u ∈ V(H)∖{r}`) is generically NON-parallel to any
contraction `Fc`'s `panelSupportExtensor (q₀ r)(q₀ v)` — and the degenerate placement does NOT fix
this (route 2 unsound for the producer). **The rigid `case_I_realization` — the lemma being restated —
never uses the splice brick: it routes through the block-triangular row-counting coupler
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set` (CaseI:2119) on `F`'s OWN
exterior-projected rows.** So the all-`k` simple arm must mirror THAT (route 1), with the surviving-leg
input made deficiency-aware. Canonical: §1.66. **The landed L5b-i route-2 leaf
`exists_rankPolynomial_of_IH_relabel_linking` is SUPERSEDED (dead, no consumer — leave harmless,
delete-at-L5b-close); its shared core `finrank_span_rigidityRows_ofNormals_relabel_eq` is REUSED by
route 1.**
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
| `hcontract` (the bare Case-I branch) | `def:genuine-hinge-realization` | `theorem_55_d3` (:6809) | **L5** dispatch on `G.Simple` — non-simple (KT 6.2) → the landed `case_I_realization_nonsimple` (L5a-ii, bare motive, splice brick `le_finrank_span_rigidityRows_of_splice`); simple (KT 6.3) → `case_I_realization_all_k` (L5b, GP conjunct). **Route split by motive:** the splice brick + `hFc_surv_le` is the *bare* (non-simple) route only; the *GP* (simple) route CANNOT use it (§1.66 — `hFc_surv_le` needs `F`/`Fc` extensor parallelism, impossible for `F = ofNormals` on crossing edges), so L5b mirrors the LANDED rigid `case_I_realization`'s block-triangular row-counting coupler `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set` with a deficiency-aware surviving-leg (`def=k>0` `_proj` rank polynomial). The 6.5 sub-arm stays `h65` → L8. L5b-ii re-cut (§1.66) into L5b-ii-a (`_proj` extractor) → -b (`_proj` rank poly) → -c (deficient coupler restate) → -d (`case_I_realization_all_k`) → L5b-iii (dispatch) |

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
        route 2: shared core → `exists_rankPolynomial_of_le_finrank_linking`). Produces the surviving block's
        **full-span** rank for the splice brick. **SUPERSEDED by §1.66 route 1 (the splice brick is the wrong
        vehicle for the GP producer); no consumer in tree → delete-at-L5b-close candidate, harmless until then.**
        Its node `lem:rank-polynomial-IH-relabel` is a truthful statement (leave green). The shared core +
        `lem:rank-transport-relabel-of-le-finrank` SURVIVE (route 1 reuses them).
    - [ ] **L5b-ii** — `case_I_realization_all_k` via **route 1 (§1.66): mirror the LANDED rigid
      `case_I_realization`'s block-triangular row-counting coupler, NOT the splice brick.** Re-cut into four
      sub-leaves (§1.66(g)):
      - [x] **L5b-ii-a** — deficient `_proj` extractor `exists_independent_panelRow_subfamily_of_le_finrank_proj`
        (CaseI.lean:1311, beside the rigid sibling at :1259): the rigid extractor verbatim with two landed swaps —
        W6e `_le_finrank` for the un-projected source + `injOn_..._of_inter_eq_singleton` (L5a-ii) for the
        rigidity gate. No blueprint node (churn-prone `_proj` infra, like its rigid sibling). Build+lint clean.
      - [x] **L5b-ii-b** — deficient `_proj` rank polynomial `exists_rankPolynomial_of_IH_relabel_linking_set_proj`
        (CaseI.lean, beside the rigid `rigidContract_exterior_rank_transport_htransport`): mirrors that rigid
        chain at the deficient leg — landed shared core `finrank_span_rigidityRows_ofNormals_relabel_eq` gives the
        witness placement `nrm` (GP) + the exact deficient rank `N` (`(N:ℤ) = D(|sc|−1)−k'` via `hF'sc` +
        `hKmin.1`); L5b-ii-a `_proj` extractor (rank input `N`, `hinter` from `rigidContract_vertexSet_inter_eq_singleton`)
        gives the projected-collapsed independent subfamily; U2 `panelRow_collapseTo_comp_extProj_dualMap` carries it
        to `degeneratePlacement r V(H) nrm'`; the landed bounded packaging `exists_rankPolynomial_of_rigidOn_linking_set_proj`
        (generic in the projected family — reused, not re-derived) lifts the single-placement witness to the `Q`-non-root
        rank polynomial. Mints `lem:rank-polynomial-IH-relabel-proj` (rigidity-matrix.tex, green). The route-2 leaf
        `lem:rank-polynomial-IH-relabel` is now marked `superseded` in its blueprint title (inert, audit-trail only).
        All gates clean (build+lint+blueprint-verify; axiom-clean).
      - [x] **L5b-ii-c** — deficiency-aware coupler restate
        `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof` (CaseI.lean, after the
        rigid coupler). Lower bound: `hunion` LI + `Fintype.ofFinite` + `finrank_span_eq_card`;
        upper bound: B2 (`finrank_span_rigidityRows_add_deficiency_le`) via `supportExtensor_ne_zero_of_isGeneralPosition`
        + `hne_G`; `le_antisymm` closes. Two new hypotheses vs the `= 0` coupler: `hn` (B2) + `hne_G` (extensor nonzero).
        `set_option linter.style.longLine false in` guards the 102-char name. Build+lint clean.
      - [x] **L5b-ii-d** — `case_I_realization_all_k` (CaseI.lean:9272): assembly mirroring the rigid
        `case_I_realization` body — H-leg at `k'=0` (IH gives generic realization, rigidity extracted from
        `hQHrank` with `hKDof`-rewrite), contraction leg at `k'=k` (IH gives `hQcf`), L5b-ii-b
        `exists_rankPolynomial_of_IH_relabel_linking_set_proj` produces `Qc`, L5b-ii-c
        `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof` assembles. Restates
        `lem:case-I-realization` in blueprint to `\lean{...case_I_realization_all_k}` with all-`k` statement
        prose (`\uses` updated: `lem:claim-6-4` → `lem:rank-polynomial-IH-relabel-proj`). Build+lint+blueprint-
        verify clean; statement-grep gate passed.
    - [x] **L5b-iii** — `case_I_dispatch` (CaseI.lean): `by_cases G.Simple` → non-simple `case_I_realization_nonsimple`; simple → inner `by_cases` on `∃ H r, ... (G.rigidContract H r).Simple` → 6.3 arm `case_I_realization_all_k` + M4 forgetful; 6.5 arm `h65` (stays red → L8). Updates `lem:case-I-dispatch` (`\lean{}`, no `\leanok`). Build+lint+checkdecls clean.
  V6 RESOLVED — N6a is dead infrastructure (deleted-motive-bound, `ofNormals`-bound); V4
  (`rigidContract_isMinimalKDof` all-`k`) confirmed already-landed; **V6-a re-aimed + V6-b re-scoped (§1.64)**.
- [ ] **L6** — Lemma 6.8, the `k > 0` split (`hsplitPos`); signature pinned §1.67, sliced **L6a** (the
  deficient eq.-(6.12) placement brick `case_II_placement_eq612_kdof`, the W6e swap of the rigid
  `case_II_placement_eq612`) → **L6b** (the producer `case_II_realization_all_k`, mints `lem:case-II-realization`
  at the `k>0` content). V7 RESOLVED (W-suite transfers wholesale; L6 simpler than `k=0` Case III — no `h622`,
  no Claim-6.11/6.12). Two residual build-time checks (§1.67(d)): (b1) `G_v^{ab}` simple from `hnoRigid`;
  (b2) `case_II_placement_eq612`'s `Gv` = `splitOff` (not `removeVertex`).
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
  deficiency-aware, so this is a **real new brick** (L5b-i). **The internal-route decision §1.65(c) flagged is now
  RESOLVED (§1.66): route 1 (`_proj` mirror), NOT route 2.** §1.66 found `hFc_surv_le` (route 2's splice brick) is a
  DEAD END for the GP producer (mechanism mismatch — `F = ofNormals` cannot match `Fc`'s collapsed extensors on
  crossing edges); the GP arm must mirror the LANDED rigid `case_I_realization`'s row-counting coupler, surviving-leg
  made deficiency-aware. The route-2 L5b-i leaf is superseded/dead (the shared core survives). No motive/IH change.
  V7 (L6), V8 (L7), V9 (L10), V10 (resolved at L0) gate to their layer's design pass.
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

**L0–L5b-iii complete; three carries remain: `h622`, `h65`, `hsplit`. `hcontract` discharged.**

`case_I_dispatch` (CaseI.lean:9362) landed; `lem:case-I-dispatch` has `\lean{}` (no `\leanok` — `h65` untracked);
build+lint+checkdecls clean. The 6.5 sub-arm stays `h65` → L8.

**L6 signature pin landed (§1.67):** V7 RESOLVED — the W-suite (`t=0` certify-then-rebase +
`exists_shear_linearIndependent_pair` + `caseIIICandidate_exists_good_shear`) transfers wholesale (rank-driven,
not rigidity-driven), and L6 is **strictly simpler** than the `k=0` Case III (the deficient `(k−1)`-dof IH
already supplies the full target rank `D(|V|−1)−k`, so NO Claim-6.11/6.12 redundant-row machinery, NO `h622`).
The one reuse delta: `case_II_placement_eq612` is built at a *rigid* IH, so its OLD-block step needs the
deficiency-aware swap (`_of_rigidOn_linking` → `_of_le_finrank` at rank `N := D(|V(Gv)|−1)−(k−1)`). No motive/IH
change. L6 sliced **L6a** (the deficient placement brick) → **L6b** (the producer).

**Smallest next forward commit: L6a** — `PanelHingeFramework.case_II_placement_eq612_kdof` (CaseI.lean, beside
`case_II_placement_eq612`): the rigid eq.-(6.12)–(6.17) brick's body verbatim with two swaps — W6e
`exists_independent_panelRow_subfamily_of_le_finrank` for the OLD block + the `k−1`-lowered count arithmetic. No
blueprint node (churn-prone `_kdof` infra, like the L5b-ii-a `_proj` sibling). `P≈2`. Build order + the L6b
producer signature: §1.67(a)/(e).

At phase close: Phase 23 (general `d`, KT Lemma 6.13) opens with its own recon and adds the general-`d` row to
`notes/AlgebraicIndependence.md`.

## Decisions made during this phase

(One-line verdicts; full proof-technique detail in §1.56–§1.66 design sections, docstrings, git.)

- **Phase-open + L0 pin (2026-06-11):** §1.56 motive design — carrier split (bare on `BodyHingeFramework`,
  generic on `PanelHingeFramework`); V1/V10 resolved; M5 deletion timed to L9. Canonical: §1.56/§1.57.
- **L1 pin (2026-06-11):** V2 labeling-free `cutEdges`; V3 in-place all-`k`; KT 3.6 partition; 4.8(ii)
  cluster decomposed (KT 4.2 is the one new engine); KT numbering corrected vs PDF. Canonical: §1.58.
- **L0+L1 builds (2026-06-11/12; sonnet + opus L1g/L1h):** motives + bridges + conditioned-pair swap (L0);
  combinatorial bricks L1a–L1j per §1.57/§1.58. Promoted: FRICTION; TACTICS-QUIRKS §§47/48; TACTICS-GOLF §4.
- **L2 build (2026-06-12, sonnet):** `minimal_kdof_reduction_all_k` per §1.59; `push Not` deprecation fix.
- **L3 builds (2026-06-12/13; opus + sonnet):** `theorem_55_base_producer` strong pair per §1.60 —
  three bare arms + GP conjunct (`_empty_gp`, `_single_edge_gp`). Geometric brick `exists_linearIndependent_extensor_pair_perp`
  (PanelLayer); `lem:theorem-55-base-producer` + companions green. `hbase` carry discharged.
- **L4 builds (2026-06-13; sonnet + opus):** cut-edge arm per §1.61/§1.62 — brick + bare producer (L4a);
  rank-poly extractor `exists_rankPolynomial_of_le_finrank_linking` + GP producer (L4b). V5-b Route GP-2.
  Promoted: TACTICS-QUIRKS §§49–53.
- **L5 signature pin (2026-06-13):** non-simple Case I (KT Lemma 6.2) pinned; canonical: §1.63. `hcontract`
  is `by_cases G.Simple` dispatch; N6a unusable; L5a fresh on `BodyHingeFramework`. Added V6-a/V6-b.
- **L5a-i boundary pair — §1.63(c)/(f) splice brick WRONG, reverted (2026-06-13):** pin stated
  contraction leg as `induce` but `rigidContract` *collapses* V(H)→r (keeps crossing edges); induce-leg
  rank wrong; additivity is Lemma-5.1 + block-triangular (no rigidity gate). Canonical: §1.64.
  Model-experiment rows 97/98.
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
- **L5a-i build (2026-06-13, sonnet):** `BodyHingeFramework.le_finrank_span_rigidityRows_of_splice`
  (`RigidityMatrix.lean`, `section SpliceBrick`). `letI` (not `haveI`) to shadow `AddCommMonoid ↥S` with
  `AddCommGroup ↥S` for `domRestrict`/`finrank_quotient_add_finrank` (TACTICS-QUIRKS §54).
  `lem:rigidityRows-splice-rank-add` green.
- **L5a-ii `hInj` discharge (2026-06-13, opus):** three lemmas in `CaseI.lean` (beside rigid Claim-6.4). Crux
  `infinitesimalMotions_sup_range_extProj_eq_top_of_inter_eq_singleton`: `Z ⊔ W = ⊤` by explicit `z a = if a ∈
  V(G) then S r else S a` decomposition — no rank count, no rigidity (the rigid sibling's count route is
  `0`-dof-gated). Then dual-API mirror → `injOn`, then rank-nullity → `hInj`-form. `lem:extProj-preserves-rank-of-inter`.
  V6-a fully RESOLVED. FRICTION: `disjoint_ker_iff_injOn`.
- **L5a-ii producer (2026-06-13, sonnet):** `case_I_realization_nonsimple` (CaseI.lean). `¬G.Simple` →
  parallel pair `H'`; IH on `rigidContract`; coincident-panel `normal`; four splice-brick hyps; B2 upper bound;
  key quirks: `set H'`/`hH'_def`; `change` not `show`; `rw [hFcg, rigidContract, map_isLink]` for `hFc_surv_le`.
  `lem:case-I-realization-nonsimple` green.
- **L5b design-pass (2026-06-13, opus; §1.65):** decomposed BLOCKED all-`k` simple GP restate → L5b-i
  (V6-b brick) + L5b-ii (producer) + L5b-iii (dispatch). V6-b re-rated `P≈3`. Internal route left unpinned
  (§1.65(c)). Canonical: §1.65.
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
  (IsLink.ne needs the Loopless instance, not a hypothesis — writing `hloop.isLink_ne` fails).
  **Note (§1.66): this leaf is the FULL-span rank for the splice brick — SUPERSEDED by route 1 (the splice brick
  is the wrong vehicle for the GP producer), now dead with no consumer.** Its shared core survives. Mints
  `lem:rank-polynomial-IH-relabel`. Axiom-clean; all gates clean.
- **L5b-ii route resolution (2026-06-13, opus; §1.66):** `hFc_surv_le` dead end for GP producer (mechanism
  mismatch: support-extensor parallelism needed, `F = ofNormals` cannot give it on crossing edges). Rigid
  `case_I_realization` routes through the coupler, not the splice brick; all-`k` simple arm mirrors that (route 1).
  Three new decls; no motive/IH change. Route-2 leaf superseded, leave harmless. Canonical: §1.66.
- **L5b-ii-a build (2026-06-13, sonnet):** `BodyHingeFramework.exists_independent_panelRow_subfamily_of_le_finrank_proj`
  (CaseI.lean). Two-swap mirror of the rigid extractor: W6e `_le_finrank` replaces `_rigidOn_linking` (dropping
  `hnev`/`hrig`/`hr`, adding `hN`); `injOn_..._of_inter_eq_singleton` (L5a-ii) replaces `injOn_..._rigidityRows`
  (dropping `hrig`/`hr`). No blueprint node. Build+lint+axiom-clean.
- **L5b-ii-b build (2026-06-13):** `PanelHingeFramework.exists_rankPolynomial_of_IH_relabel_linking_set_proj`
  (CaseI.lean) — the deficient-leg mirror of `rigidContract_exterior_rank_transport_htransport` then
  `exists_rankPolynomial_of_rigidOn_linking_set_proj`. Shared core (placement `nrm` + rank `N`, `(N:ℤ)=D(|sc|−1)−k'`)
  → L5b-ii-a `_proj` extractor → U2 → landed bounded packaging (reused, generic in the projected family). Took
  `[DecidableEq β]` (forced by `IsMinimalKDof`); ℤ count via `Nat.cast_sub` on `1 ≤ |sc|`. `set N` ordering trap
  avoided per TACTICS-QUIRKS §43. Mints `lem:rank-polynomial-IH-relabel-proj`; route-2 leaf
  `lem:rank-polynomial-IH-relabel` marked `superseded`. V6-b RESOLVED (route-1 form). Canonical: §1.66(e)/(g).
- **L5b-ii-c build (2026-06-13, sonnet):** `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof`
  (CaseI.lean). Mechanical arithmetic restate of the rigid coupler with `hdef=0`→`G.deficiency n = k'`. Final step
  diverges from rigid: lower bound via `Fintype.ofFinite` + `finrank_span_eq_card` + `Submodule.finrank_mono`; upper
  bound via B2 + `supportExtensor_ne_zero_of_isGeneralPosition` (`hne_G` gives endpoint-different); `le_antisymm`
  closes. Two new hypotheses: `hn : bodyBarDim n = screwDim k` (B2) + `hne_G` (extensor nonzero).
  `set_option linter.style.longLine false in` guards the 102-char name (only ASCII chars in name, so the linter fires
  where older long-name theorems with non-ASCII args escape). `hcard` ℤ arithmetic: ℕ `hkey` (`← Nat.mul_add`) cast
  via `exact_mod_cast`; `push_cast [Nat.cast_add]` to split `↑(a + b)` → `↑a + ↑b` for `linarith`. `zify` on
  `hcard` (with `1 ≤ V(G).ncard`) normalizes `↑(ncard - 1)` to `↑ncard - 1` for the lower-bound `linarith`.
- **L5b-iii dispatch (2026-06-13, sonnet):** `case_I_dispatch` (CaseI.lean:9362). `by_cases G.Simple`: non-simple
  → `case_I_realization_nonsimple`; simple → inner `by_cases ∃ H r, ... (G.rigidContract H r).Simple` → 6.3 arm
  `case_I_realization_all_k` + `hasPanelRealization_of_generic` (M4); 6.5 arm `h65`. `haveI hloop` from
  `loopless_of_isMinimalKDof` for M4's `[G.Loopless]` instance. `hcontract` carry discharged; `h65` stays → L8.
  `lem:case-I-dispatch` gets `\lean{}` (no `\leanok` — `h65` untracked load-bearing hypothesis). Axiom-clean.
- **L6 signature pin (2026-06-13, opus; §1.67):** `case_II_realization_all_k` (`hsplitPos`) pinned against the
  settled §1.56(c) all-`k` IH. V7 RESOLVED: the W-suite (`t=0` certify-then-rebase, shear lemmas,
  `caseIIICandidate_exists_good_shear`) is rank-driven so it transfers wholesale; L6 is strictly simpler than
  `k=0` Case III (deficient IH supplies the full rank `D(|V|−1)−k` — no `h622`, no Claim-6.11/6.12). One reuse
  delta: deficiency-aware `case_II_placement_eq612_kdof` (W6e swap, L5b-ii-a precedent). No motive/IH change.
  Sliced L6a (brick) → L6b (producer). Two residual build checks (§1.67(d)). Docs-only.
