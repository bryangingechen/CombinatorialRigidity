# Phase 22k — completing the honest all-`k` Theorem 5.5 (Case III, spine) + Thm 5.6 `d=3` (work log)

**Status:** ✓ Complete (closed 2026-06-16 on the L10d blueprint flip).

22k completes the honest all-`k` Theorem 5.5 the 22i→22j→22k arc set up: the three remaining
22h carries (`h622`, `h65`, `hsplit`) + Theorem 5.6 at `d = 3`. 22i delivered the all-`k`
genuine-hinge motive + the reduction-case producers (L0–L6, `hbase`/`hcontract` discharged);
22j landed the shared span-transport "pinned placement" rank brick
(`le_finrank_span_rigidityRows_of_pinned_placement` = **Brick A**, design §1.68) that **22k's
Case III consumes**. The design basis is the **L7–L10 layer plan + the §1.56 carries table**,
archived in `notes/Phase22i.md` *Hand-off / next phase* + its *Layer plan* / *carries table*
sections; this note transcribes them, with the carries-table "Lean consumption site" column
**re-located into the post-22j-perf 5-file chain** (`GenericityDevice ← Coupling ← CaseI ←
CaseII ← CaseIII ← Theorem55`, under `Molecular/AlgebraicInduction/`).

Structural-edit mode: no new blueprint chapter; the existing `algebraic-induction/*` chapters
restate per slice (the statement-grep gate, `CLAUDE.md` *Structural-edit phases*). The motive
design is canonical in `notes/Phase22-realization-design.md` §1.56 — point at it, don't duplicate.

## Current state

**✓ All layers L7–L10 complete.** Katoh–Tanigawa's Theorem 5.5 and Theorem 5.6 are now formalized at
`d = 3` at full KT strength. The three remaining 22h carries (`h622`/`h65`/`hsplit`) are discharged,
leaving a zero-carry Theorem-5.5 spine (`theorem_55_all_k`, `theorem_55_d3`); Theorem 5.6 at `d = 3`
(`rankHypothesis_of_theorem_55_d3`) lifts the minimal-`0`-dof realization to arbitrary deficiency
(strip → realize → re-add edges), completing the analytic half of KT Proposition 1.1
(`rigidityMatrix_prop11`, green). L10d (this close): flipped `prop:rigidity-matrix-prop11` red→green and
minted `thm:theorem-55-6-d3`. **Next phase: Phase 23** (Case III general `d`, KT Lemma 6.13).

## Layer plan (L7–L10; each layer opens with its own §1.69+ signature pin)

Transcribed from `notes/Phase22i.md` *Layer plan* (the L7–L10 entries) + the §1.56 carries table
+ §1.67. The 22i layers L0–L6 are closed (archived in `notes/Phase22i.md`); 22k is L7–L10.

- [x] **L7** ✓ — the Case-III rewire: `case_III_realization` restated, `h622` *derived* from the
  all-`k` IH (V8) — `h622` carry discharged. **L7a ✓** `exists_rankPolynomial_of_IH_linking` +
  `finrank_span_rigidityRows_ofNormals_eq`. **L7b ✓** `case_III_realization` restate + `h622lb`
  discharge + thin wrapper `case_III_realization_0dof` (Flag F1); discharge then **extracted** as
  the standalone `case_III_nested_rank_lower` so the node pins to a real decl. Blueprint nodes:
  `lem:case-III-nested-rank-lower` (green-and-pinned), `lem:case-III` / `thm:theorem-55-d3-instance` (restated).
- [x] **L8** ✓ — the Lemma-6.5 arm: KT Claim 6.6 graph side + the Π°-placement producer; `h65`
  carry discharged at the 0-dof spine. **L8a ✓** all Claim 6.6 graph-side pieces (Leaf-1 assembly
  `exists_degree_two_removeVertex_of_no_simple_contraction`, `Contraction.lean`). **L8b ✓**
  de-privatize `linearIndependent_normals_of_algebraicIndependent`. **L8c-1 ✓** the `hnewpin` brick
  `exists_independent_pinned_two_edge_span_full` (`Pinning.lean`). **L8c-2 ✓** the producer
  `PanelHingeFramework.case_I_realization_h65` (Theorem55.lean) — geometric blocks extracted as the
  `case_I_h65_*` helpers + the general `normalsJoin_pair_linearIndependent_of_triLI` /
  `triLI_subpairs` (PanelLayer.lean); witness via the combined `Sum.elim` block →
  `isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows` → the genericity-transfer keystone
  `hasGenericFullRankRealization_of_rigidOn_ofNormals` (no separate rank-poly transfer needed, both
  0-dof). Wiring: dropped `theorem_55_d3`'s 0-dof `h65` carry. Node `lem:case-I-dispatch` flipped
  green (re-pinned to `case_I_realization_h65`). `set_option maxHeartbeats 800000` (4×).
- [x] **L9** ✓ — the zero-carry spine + instance: `theorem_55_all_k`, `theorem_55_d3` restated
  with **zero carries**; new lemma `deficiency_eq_zero_of_simple_rigid_no_simpleContraction`
  (Contraction.lean) discharges the all-`k` `h65` arm; `hsplit` discharged by G0 + M4 wiring.
  Blueprint nodes `thm:theorem-55` + `thm:theorem-55-d3-instance` green.
- [x] **L10** ✓ — Theorem 5.6 at `d = 3`: the deficiency-preserving spanning-strip brick +
  re-add edges (rank only grows) + the `def > 0` `prop:rigidity-matrix-prop11` feed.
  **§1.71: V9 free; sliced L10a–L10d.** The `def = 0` feed already landed in 22h
  (`rankHypothesis_deficiency_of_theorem_55_d3`). Sub-layers (each its own build):
  - [x] **L10a** ✓ — `Graph.exists_isMinimalKDof_spanning_subgraph` (NEW, Deficiency.lean). Built
    via a **finite minimum** (`Set.exists_min_image` over deficiency-preserving edge subsets), NOT a
    WF recursion; flag (i) dissolved — the no-deletable-edge ⟺ `IsMinimalKDof` step is the
    contrapositive of minimality of `|F₀|`, routed through the existing rank-equality⟹base⟹def-equality
    engine. `\uses`-only brick, mints no node. Build + lint clean, axiom-clean.
  - [x] **L10b** ✓ — `theorem_55_minimalKDof_k` (Theorem55.lean). Flag (ii) RESOLVED FREE:
    identical callbacks to `theorem_55_all_k`; only change is `k G hG …` in place of `0 G hG …`.
    Build + lint clean, warning-clean.
  - [x] **L10c** ✓ — `PanelHingeFramework.rankHypothesis_of_theorem_55_d3` (Theorem55.lean tail):
    strip → `theorem_55_minimalKDof_k` → `reaimSub` re-add → `withGraph` monotonicity `hgen` →
    `rigidityMatrix_prop11`, + a `|V|=1` single-body case. Micro-bricks `reaimSub` /
    `reaimSub_withGraph_infinitesimalMotions` (the `def>0` `reaim` variant). Build + lint + warning-clean.
  - [x] **L10d** ✓ — blueprint (2026-06-16, opus, docs-only): flipped `prop:rigidity-matrix-prop11`
    red→green (`\leanok` on statement + proof; proof re-routed onto `thm:theorem-55` +
    `lem:motions-mono-of-graph-le` as the honest `hgen` discharge, the dead "Red:" paragraph dropped) +
    minted `thm:theorem-55-6-d3` (pinned to `rankHypothesis_of_theorem_55_d3` + the `def=0` feed
    `rankHypothesis_deficiency_of_theorem_55_d3`). To avoid a dep-graph cycle the prop↔Thm-5.6 edge
    runs one way: Thm-5.6's *proof* `\uses` the prop (the producer calls the rank bridge), the prop
    `\uses` only `thm:theorem-55` + monotonicity. Stale "stays red"/"modulo carries" prose fixed in
    `algebraic-induction.tex` + `intro.tex`. checkdecls + lint.sh + verify.sh green.

**Beyond the carries**, the all-`k` restructure adds the structural deliverables of §1.56(c)/(e)
— but those (the new reduction cases, the motive restate of every producer) landed in 22i; 22k's
new structural work is only the Thm-5.6 `d=3` push (L10).

## The carries table (relocated to the post-22j-perf 5-file chain)

The §1.55(b) structural fix for orphaned deferrals. **Lean consumption sites re-located** from
the stale `CaseI.lean:6750/:6817/…` refs of `notes/Phase22i.md` into the new
`Molecular/AlgebraicInduction/` chain (the 22j-perf round split the 10,346-line `CaseI.lean`
monolith into `GenericityDevice ← Coupling ← CaseI ← CaseII ← CaseIII ← Theorem55`; rename-free,
so the decl names are unchanged — only the file:line moved).

| Carry | Blueprint red node | Lean consumption site (post-22j-perf chain) | Discharge sub-plan (§1.56) |
|---|---|---|---|
| `h622` (KT eq. (6.22), the nested-IH rank lower bound at the `k'`-dof `G_v`) | `lem:case-III-nested-rank-lower` (case-iii.tex) | **DISCHARGED (22k L7)**: `case_III_realization` carries the all-`k` IH; the `h622lb` slot is filled by the standalone `case_III_nested_rank_lower`; `theorem_55_d3` calls thin wrapper `case_III_realization_0dof` (Flag F1). `lem:case-III-nested-rank-lower` green-and-pinned. | **L7 complete** (22k): all-`k` IH at `G_v` → `exists_rankPolynomial_of_IH_linking` → footnote-6 non-root → arithmetic; discharge extracted as `case_III_nested_rank_lower`. |
| `h65` (the KT Lemma-6.5 vertex-removal arm of the Case-I dispatch) | `lem:case-I-dispatch` (case-i.tex; now green, re-pinned to `case_I_realization_h65`) | **DISCHARGED**: 0-dof form **L8c-2**; all-`k` form **L9** via `deficiency_eq_zero_of_simple_rigid_no_simpleContraction` (Contraction.lean) — k>0 + all contractions non-simple → carrier construction forces `def(G)=0`, contradicts k>0; so the arm is vacuous and the k>0 hcontract branch calls `case_I_realization_all_k` or `case_I_realization_nonsimple` only. | **L8 + L9 COMPLETE**: L8 built the Claim-6.6 graph side + Π°-producer; L9's new lemma closes the all-`k` spine vacuously. |
| `hbase` (the bare two-vertex base) | `def:genuine-hinge-realization` + `def:rank-hypothesis`; `lem:theorem-55-base-producer` green at the strong pair | **DISCHARGED (22i L3)**: `theorem_55_base_producer` (`Theorem55.lean:436`) supplies `.2`; `hbase` dropped from the `theorem_55_d3` signature (`Theorem55.lean:498` comment) | **L3 complete** (22i): the producer concludes the §1.60(a) strong pair `(G.Simple → HasGenericFullRankRealization) ∧ HasPanelRealization` |
| `hsplit` (the bare no-rigid-subgraph branch) | `def:genuine-hinge-realization` (via `lem:case-III`) | **DISCHARGED (22k L9)**: `theorem_55_all_k`'s `hsplitZero` slot: G0 → `G.Simple`; forgetful M4 ∘ `case_III_realization`; `hsplitPos` slot analogously. Zero new build. | **L9 complete** (22k): wiring via `simple_of_isMinimalKDof_of_noRigid` + `hasPanelRealization_of_generic` |
| `hcontract` (the bare Case-I branch) | `def:genuine-hinge-realization` | **DISCHARGED (22i L5)**: signature hyp of `theorem_55_d3` (`Theorem55.lean:494`) now wired through the `by_cases G.Simple` dispatch `case_I_dispatch` (`Theorem55.lean:1863`) → non-simple `case_I_realization_nonsimple` / simple `case_I_realization_all_k`; the negative-contraction sub-arm stays `h65` → L8 | **L5 complete** (22i) — split by motive; the 6.5 sub-arm stays `h65` → L8 |

## Blockers / open questions

- **None — phase complete.** All layers L7–L10 landed; both §1.71 build-time flags resolved favorably
  (i: L10a strip brick, no separate micro-pin; ii: L10b `theorem_55_minimalKDof_k`, near-free wrapper).
  Two non-blocking Lean cleanups seed a later post-22k cleanup round (NOT this phase): (1) the
  `theorem_55_all_k` / `theorem_55_minimalKDof_k` callback-map duplication (collapse the former to a
  `k=0` corollary of the latter); (2) `reaimSub` / `reaim` could share a helper.

## Hand-off / next phase

**22k closed 2026-06-16 (L10d).** Deliverable met: Katoh–Tanigawa's Theorem 5.5 and Theorem 5.6 are
formalized at `d = 3` at full KT strength, and the analytic half of KT Proposition 1.1
(`rigidityMatrix_prop11`) is green. Tree clean, all gates green (build + lint + `verify.sh`).

**Next phase: Phase 23 — Case III general `d`** (KT Lemma 6.13) → Thm 5.5 complete → Thm 5.6 →
Conjecture 1.2. Open it with its own recon (KT eqs. (6.46)–(6.67) vs the `d=3` Lean), per the program
map (`notes/MolecularConjecture.md` *Opening the next phase*); the general-`d` reuse map is
`notes/Phase22-realization-design.md` §1.33 (C). The first concrete commit is the Phase-23 opening (a
design/recon pass, not a build): create `notes/Phase23.md`, add the general-`d` row to
`notes/AlgebraicIndependence.md`, and scope the Lemma-6.13 layer plan.

Two non-blocking Lean cleanups seed a later post-22k cleanup round (see *Blockers*).

## Decisions made during this phase

(One-line verdicts; full proof-technique detail in §1.56–§1.71 design sections, docstrings, git.)

- **L10d blueprint flip — 22k closed (2026-06-16, opus, docs-only):** flipped
  `prop:rigidity-matrix-prop11` red→green and minted `thm:theorem-55-6-d3` (KT Theorem 5.6 at `d=3`),
  pinned to `rankHypothesis_of_theorem_55_d3` (L10c, `def>0`) + `rankHypothesis_deficiency_of_theorem_55_d3`
  (22h, `def=0`). The prop's proof re-routes its `hgen` discharge onto `thm:theorem-55` +
  `lem:motions-mono-of-graph-le` (the honest realize-subgraph-then-re-add argument); the dep-graph
  prop↔Thm-5.6 edge is one-way (Thm-5.6's proof `\uses` the prop, not vice versa) to keep the graph
  acyclic — a mutual `\uses` blew plastex's `ancestors` recursion. Stale "stays red"/"modulo carries"
  prose corrected in `algebraic-induction.tex` + `intro.tex`; phase-close surfaces synced. All gates green.
- **L10c `def>0` prop11 producer landed (2026-06-16, opus, salvaged-interrupted + coordinator-reflowed):**
  `rankHypothesis_of_theorem_55_d3` + micro-bricks `reaimSub` / `reaimSub_withGraph_infinitesimalMotions`
  (the `def>0` `reaim` variant, keyed on `G'`-links), Theorem55.lean tail. The §1.71(c) route: strip
  (`exists_isMinimalKDof_spanning_subgraph`) → `theorem_55_minimalKDof_k` → `reaimSub` to `G` → `hgen`
  from `withGraph` monotonicity → `rigidityMatrix_prop11`; `hC` from GP. Plus a `|V|=1` single-body case
  (`def=0`, `rankHypothesis_zero_iff`). One justified `linter.unusedDecidableInType` suppression
  (DecidableEq used by the strip, not in the conclusion type). Salvaged from the dispatch the user
  interrupted (complete + green as written); coordinator reflowed one long line + verified
  build/lint/warning-clean/sorry-free.
- **L10b general-`k` re-expose landed (2026-06-16, sonnet, clean):** `theorem_55_minimalKDof_k`
  (Theorem55.lean, after `theorem_55_all_k`). **Flag (ii) RESOLVED FREE** — identical callbacks to
  `theorem_55_all_k`; only change is final application `k G hG …` replacing `0 G hG …`. All producers
  are genuinely `{k : ℤ}` (`theorem_55_base_producer`, `case_cut_edge_realization*`, `case_I_realization_all_k`,
  `case_II_realization_all_k`); `k=0`-only producers (`case_I_dispatch`, `case_III_realization`) are
  gated by the induction principle's own `k=0` guard, not assumed in the general spine. No blueprint
  `\lean{}` pin yet (L10d). Build + lint + warning-clean.
- **L10a strip brick landed (2026-06-16, opus, clean):** `exists_isMinimalKDof_spanning_subgraph`
  (Deficiency.lean). Built via a **finite minimum** over deficiency-preserving edge subsets
  (`Set.exists_min_image`, finite by `[Finite β]`), NOT the design's WF edge-deletion recursion.
  **Flag (i) dissolved:** no standalone no-deletable-edge ⟺ `IsMinimalKDof` matroid micro-pin was
  needed — the fiber-meeting minimality is the contrapositive of `|F₀|`-minimality, routed through
  the near-clone `eq_of_isMinimalKDof_of_le_of_vertexSet_eq_of_isKDof`'s rank-equality⟹base⟹
  def-equality engine (`isBase_ncard_add_deficiency_eq` + `matroidMG_restrict_mulTilde` +
  `deficiency_le_deficiency_of_le_vertexSet_eq` for the `≥` bound). Stays in the `restrict` idiom
  (`G ↾ F`, `restrict_self`, `restrict_restrict`) — no `deleteEdges`. Build + lint + axiom-clean.
- **L10 design pass landed (2026-06-16, opus, docs-only; §1.71):** Thm 5.6 at `d=3` sliced
  L10a–L10d with exact signatures. **V9 RESOLVED FREE** — the homogeneous projective move's brick
  `exists_extensor_in_two_panels` (PanelLayer.lean:631, no transversality) is already landed, and the
  rank lower bound is the already-green `lem:motions-mono-of-graph-le`; the `def=0` prose's bundling
  of the projective move into the lower bound was over-careful (`withGraph` monotonicity is
  unconditional). Two build-time flags (clause (ii), flagged not forced): (i) the strip brick's
  no-deletable-edge ⟺ `IsMinimalKDof` matroid step (P≈3.5); (ii) **load-bearing** — `theorem_55_all_k`
  is exposed at `IsMinimalKDof n 0` but the `def>0` feed needs a `k>0`-dof minimal graph, so L10b must
  confirm the all-`k` re-expose before L10c. Verified against landed source per clause (i). Next: L10a.
- **§1.56(e) cleanup landed (2026-06-16, sonnet, clean):** deleted orphaned legacy spines
  `theorem_55` + `theorem_55_generic` (PanelHinge.lean); re-pinned `thm:theorem-55` to
  `theorem_55_all_k` only; updated prose in 6 files. No callers confirmed before deletion.
- **L9 zero-carry spine landed (2026-06-16, sonnet, clean):** `theorem_55_all_k` +
  `theorem_55_d3` placed at END of Theorem55.lean (after all producers). New lemma
  `deficiency_eq_zero_of_simple_rigid_no_simpleContraction` (Contraction.lean) handles the k>0
  all-contractions-non-simple arm via carrier construction steps 1–4a (which don't use k=0) +
  `deficiency_le_deficiency_of_le_vertexSet_eq` — forcing k=0 by contradiction, so the arm is
  vacuous. Blueprint `\cref{def:simple-of-isMinimalKDof-noRigid}` typo fixed to
  `\cref{lem:simple-minimal-noRigid}`. All gates green (build + lint + verify.sh).
- **L8c-2 producer + wiring + node flip landed (2026-06-16, opus, clean):**
  `PanelHingeFramework.case_I_realization_h65` (`Theorem55.lean`). Architecture is the recovered-WIP
  route but with the witness assembled via the **genericity-transfer keystone** (combined `Sum.elim`
  NEW+OLD block → `isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows` →
  `hasGenericFullRankRealization_of_rigidOn_ofNormals`) instead of B2+antisymmetry+manual `⟨Q,…⟩` — this
  is what cleared the `whnf` blowup that the monolithic B2/manual-assembly form hit even at 6M
  heartbeats. **The §38 fix that mattered: decomposition (per the escalation) PLUS routing the final
  assembly through the keystone** — extracting helpers alone was not enough; the manual `∃`-witness
  assembly was the dominant `whnf` cost. Geometric blocks extracted as `case_I_h65_{extensor_pair_LI,
  old_vanish,old_span,ofNormals_supportExtensor}` (private, Theorem55) + general
  `normalsJoin_pair_linearIndependent_of_triLI` / `triLI_subpairs` (PanelLayer). Producer fits at
  `maxHeartbeats 800000` (4×). Wiring dropped `theorem_55_d3`'s 0-dof `h65`; node `lem:case-I-dispatch`
  re-pinned to `case_I_realization_h65` + green. Build + lint + axiom-clean (propext/choice/Quot.sound).
- **L8c-1 `hnewpin` brick landed (2026-06-15, opus, clean):**
  `exists_independent_pinned_two_edge_span_full` in **`Pinning.lean`** (the §1.70(i.1) finrank chain:
  per-edge pinned subfamilies span `r(p(eₐ))`/`r(p(e_b))`, `finrank_sup_add_finrank_inf_eq` +
  `dualAnnihilator_sup_eq` give `finrank(sup) = D`, `exists_fun_fin_finrank_span_eq` extracts the
  `Fin D` LI subfamily, un-pinned rows are rigidity rows by `panelRow_mem_rigidityRows_of_link`).
  **Two §1.70(i.1) pin corrections (both forced by landed source, no math change):** (1) file is
  `Pinning.lean` not `RigidityMatrix.lean` — the brick's `panelRow`/per-edge deps are downstream of
  RigidityMatrix, so RigidityMatrix placement is a circular import; (2) signature gains
  `hlink_a`/`hlink_b` link hyps the pin omitted (the producer supplies them). `hnew_span` `whnf`
  timeout over coerced subtype index → destructure + `_of_link` (FRICTION §38-family *Recurred 22k*).
  Build + lint + axiom-clean.
- **L8a (KT Claim 6.6 graph side) — all landed 2026-06-15 (opus/sonnet); detail in git + design §1.70(c′)/(c″).**
  The bricks (`Deficiency.lean`/`Contraction.lean`): `exists_maximal_isProperRigidSubgraph` →
  `exists_maximal_induced_isProperRigidSubgraph` (induced-saturated, the (c′) loop-case fix);
  `deficiency_le_deficiency_of_le_vertexSet_eq` (def antitone, L8a-0); `map_not_simple` /
  `rigidContract_not_simple` + `exists_isLink_pair_of_rigidContract_not_simple` (+ aux
  `collapseTo_eq_imp_mem_of_ne`, the shared-`v` extraction); `eq_of_isMinimalKDof_of_le_of_vertexSet_eq_of_isKDof`
  (the (c″) minimality→equality brick, near-clone of `edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two`);
  and the Leaf-1 assembly `exists_degree_two_removeVertex_of_no_simple_contraction` (`addEdge`-twice
  carrier, `removeVertex_deficiency_ge`, maximality forces `V(G'')=V(G)`). Two design-settles (§1.70(c′)
  loop-case → induced `G'`; §1.70(c″) carrier + minimality brick). Lessons promoted to FRICTION/TACTICS-QUIRKS
  §4 (the `map`-simplicity looplessness trap; the subst-direction `rcases … with ⟨h,_⟩ + rw [← h]` trap).
- **L8 signature pin (2026-06-15, design §1.70, opus):** `h65` discharges via KT Claim 6.6 (graph
  side, NEW combinatorics) + the Π°-placement producer (geometric side, the L6 Case-II template:
  Brick A + B2, NEW block = the two `v`-edges spanning the full `D`). **Both `h65` shapes reconcile
  to one producer**: Claim 6.6 FORCES `k = 0` (its hypotheses make `G` 0-dof, verified against KT
  pp. 676–677), so `theorem_55_d3:516`'s 0-dof `h65` discharges with its own `k=0` IH (the nested
  `G−v` is also 0-dof — UNLIKE L7's `k'`-dof Case III, so L8 does **not** force the all-`k` spine);
  `case_I_dispatch:1867`'s all-`k` `h65` is L9's to drop. Landed `removeVertex_deficiency_ge`
  (SplitOffDeficiency:405) IS KT Lemma 4.4 at the exact direction Claim 6.6 needs (the §1.54(a3)-era
  "none surfaced" is superseded). One privacy fix: de-privatize CaseIII's `linearIndependent_normals_of_algebraicIndependent`.
  V11 RESOLVED — buildable, no motive/IH change, no user adjudication. Two P≈3 build-time leaves
  flagged (Leaf-1 contraction-non-simplicity unpacking; Leaf-2 Lemma-5.3-at-distinct-endpoints
  `hnewpin`). Slice: L8a graph side → L8b privacy → L8c producer + wiring + node flip.
- **L7b — `case_III_realization` restate + `h622` discharge (2026-06-15, sonnet; warning-bearing →
  coordinator-repaired):** dropped `h622` carry; added `hn : bodyBarDim n = screwDim 2`; upgraded
  `hIH` to all-`k` form. `h622lb` discharged via `splitOff_removeVertex_minimalKDof` + all-`k` IH +
  `exists_rankPolynomial_of_IH_linking` + footnote-6 non-root + arithmetic. Thin wrapper
  `case_III_realization_0dof` keeps `theorem_55_d3` building (Flag F1) until L9. Came in
  warning-bearing (5 `longLine`, false "all clean" attestation); coordinator follow-up `5b6cf9a` reflowed them.
- **L7 extraction + hanging-pin gate (2026-06-15, coordinator):** L7b folded the `h622lb` discharge
  inline, leaving `lem:case-III-nested-rank-lower` `\leanok` with **no `\lean{}` pin** (uncheckable
  green). Extracted the discharge as the standalone `PanelHingeFramework.case_III_nested_rank_lower`
  (`5492158`, `|V(Gab)| ≥ 2` form — drops the 4th-vertex `c`); node now pinned + checkdecls-verified.
  Added a **hanging-pin gate to `blueprint/lint.sh`** (`52c3175`, check 4: statement `\leanok` w/o
  `\lean{}`); audit confirmed it was the only such node (358/358 others clean). Promoted to:
  blueprint/CLAUDE.md *Static checks before commit*.
- **L7a — the V8-a non-relabel rank-poly brick (2026-06-15, opus, clean):** `exists_rankPolynomial_of_IH_linking`
  + `finrank_span_rigidityRows_ofNormals_eq` (`CaseI.lean`). §1.69(c) resolved favorably (relabel
  core specialized cleanly to `f = id`). Zero friction; gates clean, axiom-clean.
- **L7 signature pin (2026-06-15, design §1.69, opus):** `case_III_realization` restates to carry
  the all-`k` IH (drop `h622`); `h622lb` is *derived* — IH at `G_v` (`k' ≤ D−2`) gives rank
  `D(m−1)−k'`, transferred to the given `(ends, q)` by the **landed deficiency-aware rank-polynomial
  idiom** (§1.62, `exists_rankPolynomial_of_le_finrank_linking` + footnote-6 non-root), NOT the
  `def=0`-only seed-rank bridge. V8 RESOLVED to buildable; the one new brick is **V8-a** (L7a,
  `exists_rankPolynomial_of_IH_linking`, the non-relabel/`f=id` mirror of the landed relabel
  rank-poly, P≈3). L7 forces the `hsplitZero` spine slot to be all-`k`-conditioned (`theorem_55_all_k`,
  L9) — `theorem_55_d3`'s `k=0` IH cannot supply the `k'>0` nested instance. No motive change; no user
  adjudication. **Finding:** the blueprint prose of `lem:case-III-nested-rank-lower` cites the seed
  bridge for the rank transfer — wrong for `def>0`; fix to the rank-polynomial extractor at the L7b flip.
- **L8b — de-privatize the triple-LI bridge (2026-06-15, haiku, clean):** promote
  `linearIndependent_normals_of_algebraicIndependent` from `private` in `CaseIII.lean` to public so
  the L8c producer can call it. The lemma is the mathematical bridge for the Π°-placement construction
  (the geometric side of KT Claim 6.6 / Lemma 5.3): given algebraically-independent coefficients and
  three distinct indices, the three rows of the Plücker matrix are linearly independent over ℝ.
  No-op restructuring; gates clean, warning-clean. **Ordering constraint:** L8c needs this lemma
  public before it can build the producer; L8a's graph-side pieces are independent of this change.
- **Phase-open (2026-06-15):** opened 22k from the 22i L7–L10 design basis; transcribed the
  carries table with consumption sites re-located into the post-22j-perf 5-file chain
  (`AlgebraicInduction/{GenericityDevice,Coupling,CaseI,CaseII,CaseIII,Theorem55}.lean`).
  Red-node consistency gate run on the L7–L10 targets (`lem:case-III-nested-rank-lower`,
  `lem:case-III-seed-rank-bridge`, `lem:case-I-dispatch`, `def:genuine-hinge-realization`,
  `thm:theorem-55`, `thm:theorem-55-d3-instance`, `lem:case-III`, `prop:rigidity-matrix-prop11`):
  each statement+proof routes through the same argument the carries table claims; no live-route
  `\uses`/proof-step at a superseded node (`blueprint/lint.sh` green). One finding: blueprint
  prose mis-attributes the `h65`/all-`k` discharge to 22i (now 22k) at three sites — recorded in
  *Blockers*, deferred to an L7/L8 restate commit (not fixed in the phase-open).
