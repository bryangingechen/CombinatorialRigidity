# Phase 23c — Case III general `d`: the redundancy-carry re-architecture + chain-dispatch completion (work log)

**Status:** open (opened 2026-06-21 at a user-adjudicated clean-break close of 23b). The integer **Phase 23
stays in progress**; ENTRY + ASSEMBLY remain later sub-phases (codes; the cross-phase plan + the
detailed route history live in `notes/Phase23-design.md`, program map `notes/MolecularConjecture.md`).

**What 23c picks up.** 23b (CHAIN) landed the CHAIN bricks (CHAIN-1/3/4, OD-7, CHAIN-2a, the `hρGv`
algebraic core + chain-induction + perp + slot machinery — all axiom-clean) but **could not reach** the
`hρGv` Case-III chain arm + `chainData_dispatch` (CHAIN-2c-iii) + CHAIN-5, because the arm's `hρGv` slot ran
into a hard core: the **member-mapping wall**, now decisively characterized as **intrinsic to KT's argument**
(not a Lean artifact — design §(o‴)(I.8.18)–(I.8.20), 2026-06-21). The **(A)-feasibility recon is DONE**
(design §(o‴)(I.8.21), 2026-06-21): (A) escapes the wall but requires a rank-certification re-architecture
(below the contract/motive). The user adjudicated the fork → **OPEN OPTION (A), de-risk-first**.

**The architecture is SETTLED (do not re-litigate); the cert + carrier + abstract-LA layer are all LANDED.**
The forked rank cert `case_III_rank_certification_chain` (`Candidate.lean:1922`, axiom-clean) consumes corner
data `(W, hWS, hWcard, ι/hιcard, g, hg, hLI)`, wires `finrank_span_rigidityRows_ge_of_corner` to the target
`D(|V(G)|−1)` via `finrank W + D = D·m_v` (`Nat.mul_succ`), **NO `hρGv` slot** — selector-agnostic, reads off
the corner block, so the `±r` row enters as a member of `g`, never the collapsed fixed-member row. The de-risk
spike (basis-free block-rank-additivity `Submodule.finrank_add_card_le_of_linearIndependent_mkQ` + its carrier
`finrank_span_rigidityRows_ge_of_corner`) landed POSITIVE — the `ScrewSpace`/§38 friction did not bite. The
SHARED tail `case_III_realization_of_rank`, the carrier packaging `exists_le_finrank_span_rigidityRows_eq_card_
of_injective_map`, both `hLI` halves + the corner-assembly `linearIndependent_mkQ_corner_of_gate`, the (α)
column bridge `funLeft_dualMap_comp_single` + the base-side `−ρ₀` column fact
`funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy` (at `vtx(i-1)` — NOT the discriminator's
`hrCol`-at-`vᵢ`, see BLOCKED below), and the off-slot row bridge
`hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link` are all in tree (axiom-clean). Detail:
design §(o‴)(I.8.18)–(I.8.24)(4.8); the *Decisions made* below.

**RESOLVED (2026-06-22): the `±r`-row sourcing closes via the DIRECT genuine reproduced-slot `e_b`-row — the
graph-endpoints-vs-overridden-support DECOUPLING grounds BOTH `hg` and `hrCol` with no `hρGv` (design
§I.8.24(4.9)).** The corrected leaves LANDED (axiom-clean, build/lint warning-clean): the `±r` row is the
candidate's reproduced hinge `e_b` read off its own GENUINE `G`-link `hingeRow u vᵢ ρ₀` (oriented with the
re-inserted body `vᵢ` as head). Because `caseIIICandidate.graph = G` keeps `e_b`'s genuine link while overriding
only its support panel, ONE object grounds both: membership reads the overridden panel (`ρ₀ ⊥` it = `hρe₀`,
NEVER `hρGv` — the M₃ `hvb_row` mechanism), and the `single vᵢ` column reads the graph link (`hingeRow_swap` +
`hingeRow_comp_single_tail` = `−ρ₀`, the discriminator's `hrCol`). The (4.8) two-object mismatch is gone — the
prior relabel-image / filtered-group attempts landed on the candidate fresh pair (which OMITS `vᵢ`) and read `0`.

> **Orientation for the next agent.** The arm `case_III_arm_realization_chain` is LANDED (wiring only); the
> `±r`-row seam stays CLOSED. **Do NOT** re-attempt the four dead route families (§I.8.18–(I.8.20)), re-litigate
> the fork, or revive the relabel-image `±r` route. The next concrete commit is **CHAIN-2c-iii
> `chainData_dispatch`** — which discharges the arm's corner-data hypotheses `(W,hWS,hWcard,ι,hιcard,g,hg,hLI)` +
> count facts `(hVone,hVcard)` from the `ChainData` interior split, routing `2 ≤ i < d` through the chain arm
> and the `d=3` floor (`i=2`) on the landed `case_III_arm_realization` engine. See *Hand-off*.

## Current state

**The arm `case_III_arm_realization_chain` is LANDED (`Relabel.lean`, axiom-clean, build/lint warning-clean);
next is CHAIN-2c-iii `chainData_dispatch`.** The arm is **pure wiring** of two landed bricks at one candidate
framework `F₀ = caseIIICandidate G ends q e_a e_b (q(a,·)) n' (q(b,·)) 0`: the `±r` block-rank-additivity cert
`case_III_rank_certification_chain` (for the candidate rank lower bound `hrank`, NO `hρGv`) → the route-agnostic
SHARED tail `case_III_realization_of_rank` (W6e–W6f + GAP-2/GAP-3). It carries the `±r` block decomposition's
corner data `(W,hWS,hWcard,ι,hιcard,g,hg,hLI)` + count facts `(hVone,hVcard)` as **explicit hypotheses** (the
project's standing "carry the undischarged crux as `h…`, never a `sorry`" idiom) — the dispatch discharges them
next. So the arm itself is new-math-free: the cert is selector-agnostic (NO `hρGv` slot, the member-mapping wall
is out of it), the `±r` row enters as a member of the corner block `g`. The four dead route families
(§I.8.18–(I.8.20)) stay exhausted; **do not re-attempt.**

The `±r`-row sourcing leaves stay landed in `Candidate.lean`: the genuine reproduced-slot row's `hg` membership
(`hingeRow_mem_caseIIICandidate_rigidityRows_reproduced`) + its `hrCol` column-at-`vᵢ` value
(`reproducedSlot_pmR_acolumn_eq`); the dispatch feeds these into the arm's `hg`/`hLI` corner. The high-level (A)
architecture is fully realized at the arm level. Full audit: design §(o‴)(I.8.24)(4.9).

**Relabel.lean is 4947 lines (past the ~1500 tripwire).** The arm landed cleanly without a split, but the file
is now well over the soft cap — a `Relabel/` split is overdue and should be done before (or alongside) the
dispatch build, which will add more chain-arm-consuming machinery. Flag carried to *Hand-off*.

**Landed (all axiom-clean), the arm now closed:** the arm `case_III_arm_realization_chain` (`Relabel.lean`,
the cert→tail composition over `F₀`, corner data + count facts as explicit hypotheses); the cert
`case_III_rank_certification_chain` (NO `hρGv`); carrier W-packaging
`exists_le_finrank_span_rigidityRows_eq_card_of_injective_map`; both `hLI` halves
(`linearIndependent_mkQ_panelRow_of_edge`, `notMem_span_mkQ_pmR_row_of_gate`) + assembly
`linearIndependent_mkQ_corner_of_gate`; the (α) column bridge `funLeft_dualMap_comp_single`; the off-slot row
bridge `hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link`; the per-member genuine transport
`chainData_bottom_relabel`; the SHARED tail `case_III_realization_of_rank`; the off-slot GROUP leaf
`funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` (serves the genuine off-slot `hWS` bottom family); the
`±r` corner sourcing `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`hg`) +
`reproducedSlot_pmR_acolumn_eq` (`hrCol`). **NOT the `±r` sourcing (superseded, revive only if a later dispatch
step needs them):** the base-side `hrCol` leaf `funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy`
(reads `vtx(i-1)`); T-2 `chainData_candidateRow_edgeGrouped_transport_comb`.

**Next: CHAIN-2c-iii `chainData_dispatch`.** Discharge the arm's corner-data hypotheses
`(W,hWS,hWcard,ι,hιcard,g,hg,hLI)` + count facts `(hVone,hVcard)` from the `ChainData` interior split: at an
interior `2 ≤ i < d`, build the relabel-image base block `W` (carrier leaf over the chain bottom family
`chainData_bottom_relabel`), the corner `g = Sum.elim (D−1 fresh panel rows) (±r row)` with `hg` (GROUP leaf +
the genuine reproduced-slot membership) and `hLI` (`linearIndependent_mkQ_corner_of_gate`, `hrCol` from
`reproducedSlot_pmR_acolumn_eq`), then call `case_III_arm_realization_chain`; the `d=3` floor (`i=2`) routes to
the landed `case_III_arm_realization` engine. Relabel.lean (4947 lines) — split overdue (see *Current state*).

## What 23b delivered (the foundation 23c builds on)

All axiom-clean; full inventory + verdicts in `notes/Phase23b.md` *Landed-leaf inventory* + design
§(o‴)(I.6)/(I.8). Headlines:
- **CHAIN-1** (`RigidityMatrix/Basic.lean`) — the eq.-6.62 row-correspondence swap + `ιc`-block augment +
  `columnOp` (the LI-side column op; *not* a span-membership identity — F4).
- **CHAIN-3** (`Meet`/`MeetHodge.lean`) — the `⋀^{d−1}W`-is-a-line duality.
- **CHAIN-4** (`Claim612.lean`) — the `Fin (d+1)` incidence + Claim-6.12 discriminator capstone
  `exists_complementIso_ne_zero_of_homogeneousIncidence_gen` (takes ONE `r`).
- **OD-7** — the four reduction producers (`hbase_k`/`hcut_k`/`hcontract_k`/`hforget_k`) + M4, all general-`k`.
- **CHAIN-2a** — `chainData_split_w6b_gates` + `chainData_split_realization`.
- **CHAIN-2c-i/ii** — the `ChainData` record + accessors; `shiftPerm`/`shiftEdgePerm` + graph-iso; the
  `hwmem` genuine-row brick `chainData_bottom_relabel`; the **(6.66) telescope**
  `wstep_foldl_hingeRow_telescope` + LEAVES 1–4 (the composed moves — KT-faithful *output*); the per-edge
  perp leaves + STEP-2 transport; and `chainData_relabel_arm_hρGv` (a **correct carried-hypothesis lemma**
  whose `hφ@endsσρ` slot is the wall).

**Salvageable vs orphan-candidate (decide at the architecture-settle).** The telescope + LEAVES 1–4 (the
composed moves) and the perp sub-tree have **KT-faithful output** and are likely reusable under (A); the
**seed-advancing fold spine** (slot core `chainData_freshEdge_slot_mem`, fold
`shiftBodyListAsc_foldl_mem_span_rigidityRows`, the gate `:1201`, `chainData_relabel_arm_hρGv`) is the
**orphan-candidate** (dead-for-the-fixed-member-route, but its fate is the architecture decision's to make —
do NOT delete until 23c settles the route). The ROUTE-α leaf 1 `shiftEndsAdv` + `_zero`/`_succ` + T-1/T-2 are
already orphaned (confirm-and-delete at the settle commit). `d=3` M₃ (`i=2`) is **zero-regression** — no
`hφ` slot, no fold — and must stay green throughout.

## Remaining work in Phase 23 (after the arm settles)

1. **The forked general-`d` chain cert + arm** (§I.8.24) → the `±r`-based engine, NO `hρGv`. d=3 keeps the
   landed engine. **Cert + tail + carrier + both `hLI` halves + assembly + (α) bridge + off-slot row
   bridge + `chainData_bottom_relabel` + the `±r` corner sourcing (`hg` + `hrCol`) + the ARM
   `case_III_arm_realization_chain` ✓ ALL LANDED** (2026-06-22, axiom-clean; names in *Current state*). The
   chain arm is pure cert→tail wiring with corner data carried as explicit hypotheses.
2. **CHAIN-2c-iii `chainData_dispatch`** (replaces `case_III_candidate_dispatch`; the general-`k` dispatch;
   routes interior `2 ≤ i < d` through the chain arm, d=3 floor on the landed engine).
3. **CHAIN-5** — wire the dispatch into the spine to discharge `hdispatch`.
4. **ENTRY** — reshape `Graph.exists_chain_data_of_noRigid` (`Reduction.lean:383`) to the `G.ChainData n`
   producer `exists_chainData_of_noRigid` (KT Lemma 4.6 chain + Lemma 4.8 split-off, general `d`); lift the
   `6 ≤ bodyBarDim n` floor; resolve the chain/cycle dichotomy (OD-1, KT Lemma 4.6 / Lemma 5.4). Consumer:
   `case_III_hsplit_producer_all_k` (`Arms.lean:777`). The CHAIN↔ENTRY `G.ChainData n` contract is **frozen**
   (design §"CHAIN↔ENTRY contract", C.0–C.6; no motive/IH change; `d=3` zero-regression).
5. **ASSEMBLY** — compose the honest general-`d` Theorem 5.5, re-green `prop:rigidity-matrix-prop11` + `hub`,
   derive Thm 5.6, state Conjecture 1.2.

**Contract/motive note.** The wall is machinery *below* the contract — no C.0–C.6/motive change is forced by
it. §I.8.21 confirmed: option (A)'s rank-cert re-architecture re-shapes `case_III_rank_certification` +
`case_III_arm_realization` only — it does **not** touch the dispatch's `hdispatch` consume-shape (C.3), the
`ChainData` record (C.1), or the 0-dof motive/IH (the dispatch threads one `ρ₀` either way).

## Blueprint-clarity obligation (carried from 23b — owner-flagged)

The `lem:case-III` general-`d` node's exposition must materialize KT's index-shift isos (6.54–6.56) + ±r chain
(6.66) explicitly (the Lean economizes; the prose must not), and — per this session's `BlueprintExposition.md`
sharpening — present the redundancy-carry as **whole-matrix bookkeeping with `r` abstract and the member
moving**, flagging the fixed-functional-transport shape as the trap. Written at phase-close once the arm is
`sorry`-free.

## Hand-off / next phase

**The arm cert→tail SPINE `case_III_arm_realization_chain` is LANDED (it carries the WHOLE corner data
`(W,hWS,hWcard,ι,hιcard,g,hg,hLI)` + `(hVone,hVcard)` as explicit hypotheses — a thin cert→tail composition,
NOT the corner-data assembly).** The next concrete commit is the **corner-data ASSEMBLY producer — the
seam-resolution end-to-end integration test** (coordinator re-pointed 2026-06-22; the arm over-shrank past the
assembly): construct the candidate `caseIIICandidate G …`, ASSEMBLE `(g,hg,hLI)` from the landed leaves —
`hg`'s `±r` row via `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced`, `hLI` via
`linearIndependent_mkQ_corner_of_gate` with `hrCol` from `reproducedSlot_pmR_acolumn_eq` — taking the dispatch's
RAW outputs (`hρe₀`/`hgate`/`hsupp`/`hindep`/`hW` + the bottom family `f`/`hf`/`hS` for `W`/`hWS`) as hypotheses,
and call the spine. **This is the integration that CONFIRMS the corrected `±r` leaf actually feeds the cert's
`hg` and the corrected `hrCol` feeds `hLI`** (all parametric over `caseIIICandidate G`; low-risk but the one
end-to-end check the seam's 4× mis-pin history warrants isolating *before* the dispatch's production complexity).
THEN CHAIN-2c-iii `chainData_dispatch` produces the raw outputs (A-1 at the interior split → `hρe₀`/`hgate`; the
bottom family) + routes interior `2 ≤ i < d`, `d=3` floor (`i=2`) → the landed `case_III_arm_realization` engine.
All the corner-data leaves are in tree (names below).

**Build order:**
1. **CHAIN-2c-iii `chainData_dispatch`** (`Relabel.lean` or a fresh `Relabel/` file post-split — see below;
   `case_III_candidate_dispatch` at `Realization.lean:268` is the d=3 template; `case_III_arm_realization_M3`
   `:2638` is the per-`i` construct-candidate + corner-data template). At an interior `2 ≤ i < d` of a
   `cd : G.ChainData n`, assemble the arm's corner data over the candidate-`i` split and call
   `case_III_arm_realization_chain`:
   - **`hWS`/`hWcard`** ← carrier leaf `exists_le_finrank_span_rigidityRows_eq_card_of_injective_map` (at
     `L = (funLeft (shiftPerm i.castSucc)⁻¹).dualMap`, `f` = the chain bottom family, `hS` =
     `chainData_bottom_relabel`).
   - **`g`** = `Sum.elim (D−1 fresh-hinge panel rows) (±r row)`; **`hg`** off-slot family ← GROUP leaf
     `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate`, `±r` row = `hingeRow u vᵢ ρ₀` ←
     `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`hlink` = `e_r`'s genuine `G`-link with `vᵢ` head,
     `hperp` = the dispatch's `hρe₀` at the reproduced slot, `t=0`).
   - **`hLI`** ← `linearIndependent_mkQ_corner_of_gate`, `hrCol` from `reproducedSlot_pmR_acolumn_eq` (the SAME
     `±r` object's `−ρ₀`-at-`vᵢ` column), `hsupp`/`hgate` the candidate hinge's support + the dispatch's gate.
   - The split-tuple facts (`hvVc,…,hgab,hdef`) + `(hVone,hVcard)` ← the `ChainData` interior accessors.
   **Flag:** `Relabel.lean` is **4947 lines** (past the ~1500 tripwire) — a `Relabel/` split is overdue and
   should land before/alongside this dispatch build.
2. **CHAIN-5** — wire the dispatch into the spine to discharge `hdispatch` → orphan confirm-and-delete (the
   `hφ`-spine; LEAF 1–4 STAYS). **Cost band ~3–5 commits.** Audit: design §(o‴)(I.8.24)(4)/(4.9).

## Decisions made during this phase

- **Chain arm `case_III_arm_realization_chain` LANDED (2026-06-22, opus) — pure cert→tail wiring, corner data
  as explicit hypotheses (the dispatch's job to discharge).** `Relabel.lean` (before the final `end`): composes
  the `±r` block-rank cert `case_III_rank_certification_chain` (→ `hrank`, NO `hρGv`) with the route-agnostic
  SHARED tail `case_III_realization_of_rank` over one framework `F₀ = caseIIICandidate G ends q e_a e_b (q(a,·))
  n' (q(b,·)) 0`. The `±r` block decomposition's corner data `(W,hWS,hWcard,ι,hιcard,g,hg,hLI)` + count facts
  `(hVone,hVcard)` enter as `h…` hypotheses (CHAIN-2c-iii `chainData_dispatch` discharges them from the
  `ChainData` interior split). So the arm carries no new math: the cert is selector-agnostic (NO `hρGv`, the
  member-mapping wall is out of it), the `±r` row is a member of corner block `g`. 2-step term proof, zero
  friction. Axiom-clean (`propext`/`Classical.choice`/`Quot.sound`), build/lint warning-clean. This realizes the
  §I.8.24(4) "arm assembly" leaf, leaving the dispatch (which builds the corner data per `i`) as the next step.
- **`±r`-row sourcing RESOLVED + LANDED — the DIRECT genuine reproduced-slot `e_b`-row; the
  graph-endpoints-vs-overridden-support DECOUPLING grounds BOTH `hg` and `hrCol`, no `hρGv` (2026-06-22, opus;
  adjudicated by an adversarial recon pair + source verification, then BUILT clean).** The `±r` corner row is
  NOT a relabel-image / filtered-group object (those land on the candidate fresh pair, which OMITS `vᵢ`, and
  read `0` at `single vᵢ` — the (4.8) defect). It is the candidate's reproduced hinge `e_b` read off its own
  GENUINE `G`-link `hingeRow u vᵢ ρ₀` (`vᵢ` the head). `caseIIICandidate.graph = G` keeps the genuine link
  while overriding only the support panel, so ONE object grounds both: `hg` reads the overridden panel
  (`ρ₀ ⊥` it = `hρe₀`, the M₃ `hvb_row :2866` mechanism, NEVER `hρGv`), `hrCol` reads the graph link at
  `single vᵢ` (`hingeRow_swap` + `hingeRow_comp_single_tail` = `−ρ₀`). Two leaves in `Candidate.lean` (after
  `linearIndependent_mkQ_corner_of_gate`): `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`hg`) +
  `reproducedSlot_pmR_acolumn_eq` (`hrCol`); both axiom-clean (`propext`/`Classical.choice`/`Quot.sound`),
  build/lint warning-clean. Satisfiability gate passes (the same object is the cert's `g`-corner member, the
  discriminator's `rRow`, and the `−ρ₀` column). Full audit: design §(o‴)(I.8.24)(4.9).
- **Mis-targeted reproduced-slot GROUP leaf DELETED (2026-06-22).**
  `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate_reproduced` (`b675317`): its `hcollapse` (filtered group
  = single row) is unsatisfiable, AND it was stated over `G.removeVertex vᵢ` (the cert is over the full `G`).
  Grep-confirmed consumed nowhere before deleting. The off-slot GROUP leaf
  `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` is KEPT (it correctly serves the genuine off-slot `hWS`
  bottom family). The base-side `hrCol` leaf `funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy`
  (reads `vtx(i-1)`) and T-2 are NOT the `±r` sourcing — the genuine `e_b`-row route supersedes them.
- **`ofNormals → caseIIICandidate` row-routing bridge LANDED (2026-06-21) — the previously-missing
  `caseIIICandidate ↔ ofNormals` row bridge the §I.8.24(4.6) Hand-off named; the chain arm's `hg`/`hWS` row
  routing is now a wire, not a re-derivation.** Two decls: the framework-general primitive
  `BodyHingeFramework.hingeRow_mem_rigidityRows_of_supportExtensor_eq` (`RigidityMatrix/Basic.lean`) —
  `F₂.graph.IsLink e u v` + `r ∈ F₁.hingeRowBlock e` + `F₁.supportExtensor e = F₂.supportExtensor e ⟹
  hingeRow u v r ∈ F₂.rigidityRows` (the hinge-row block depends only on the support extensor, so the same `r`
  is a block row of `F₂`); and its arm-consumable instantiation
  `PanelHingeFramework.hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link` (`Candidate.lean`, after
  `caseIIICandidate_supportExtensor_of_ne`) — a genuine *seed* `ofNormals G ends q` row at any off-`{e_c,e_r}`
  edge is a *candidate* `caseIIICandidate` rigidity row. This is the bridge the chain arm routes its chain-leaf
  memberships through (`chainData_bottom_relabel` produces `ofNormals (G−vᵢ)` rows; the cert is over
  `caseIIICandidate`). The `d=3` `M₃` arm did this inline at the `panelRow` level (`hFG₀_eq_panelRow`); this is
  its `hingeRow`-level, framework-general sibling for the cycle relabel. Both axiom-clean
  (`propext`/`Classical.choice`/`Quot.sound`), build/lint clean; one-line term proofs. Resolves the recurrence of
  FRICTION `[idiom] Equal supportExtensor ⟹ equal hingeRowBlock` — the fused row-level form now exists.
- **Pre-arm-build corrections pass (2026-06-21, docs-only; §I.8.24(4.6)) — TWO errors in the "pure assembly"
  framing fixed before the arm build.** Verified against the import DAG + the landed cert/leaf/template bodies:
  (1) **the chain arm goes in `Relabel.lean`, NOT `Arms.lean`** — `Arms ⊂ Relabel ⊂ Realization`, and the arm
  consumes the chain-relabel leaves `chainData_bottom_relabel`/`funLeft_dualMap_interior_group_acolumn_eq_neg_
  baseRedundancy` (downstream of `Arms.lean`), so it cannot compile there; (2) **the arm is NOT a thin
  instantiation** — the cert is over `caseIIICandidate`, there is no `caseIIICandidate ↔ ofNormals` bridge in
  tree, and the chain leaves produce `ofNormals` membership, so the arm must CONSTRUCT its candidate as a
  `caseIIICandidate` and route the chain-leaf memberships in via the off-the-two-slots seed-coincidence
  (`caseIIICandidate_supportExtensor_of_ne`) — genuine ~200-line arm-internal wiring (the `M₃` arm is the
  template), the same kind the engine + SHARED tail already do. Re-pointed the *Hand-off* + *Orientation* to a
  scope-to-fit split (the (α) `hrCol`-at-`caseIIICandidate` sub-leaf + the candidate `±r`-row `hg` membership
  first, then the arm). No motive/IH/contract change; wall stays gone. Relabel.lean (4776 lines) likely forces a
  `Relabel/` split at the arm build — flagged.
- **`hLI` corner assembly COLLAPSED into one consume-leaf `linearIndependent_mkQ_corner_of_gate`
  (2026-06-21) — the chain arm's `hLI` obligation is now a one-line application (§I.8.24(4.3)).**
  `BodyHingeFramework.linearIndependent_mkQ_corner_of_gate` (`Candidate.lean`, after
  `notMem_span_mkQ_pmR_row_of_gate`): a 3-line term composition of the three landed abstract leaves —
  (a) `linearIndependent_mkQ_panelRow_of_edge` ⊕ (b) `notMem_span_mkQ_pmR_row_of_gate` fed into the
  append-one criterion `Submodule.linearIndependent_mkQ_sumElim_unit_of_notMem_span` — producing the
  exact `LinearIndependent ℝ (W.mkQ ∘ Sum.elim (panel rows) (fun _ : Unit => rRow))` shape
  `case_III_rank_certification_chain` consumes for its `g = Sum.elim … ` corner block over `s ⊕ Unit`.
  Abstract over the candidate framework `F` (no relabel transport, no `ChainData`); the arm supplies
  the concrete `hindep`/`hW`/`hsupp`/`hgate`/`hrCol`. Axiom-clean (`propext`/`Classical.choice`/
  `Quot.sound`), build/lint clean; no proof friction (term-mode composition, zero build iterations).
- **(α) candidate-transported `hrCol` leaf `funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy`
  LANDED (2026-06-21) — the chain arm's (α) NOT-yet-isolated step is now a standalone consume-leaf
  (§I.8.24(4.5)(α)).** `Graph.ChainData.…` (`CaseIII/Relabel.lean`, after
  `interior_group_acolumn_eq_neg_baseRedundancy`): the relabel image
  `(funLeft (shiftPerm ⟨i,_⟩).symm).dualMap` of the base interior edge-`i`-group, read at the candidate
  base body `vtx (i−1)`'s screw column, equals `−ρ₀` (`2 ≤ i < d`). The proof composes the two LANDED
  pieces — `funLeft_dualMap_comp_single` (column-naturality: the candidate column at `vtx (i−1)` is the
  base group's column at `σ.symm (vtx (i−1)) = shiftPerm ⟨i,_⟩ (vtx (i−1)) = vtx i`,
  `shiftPerm_apply_interior`) then `interior_group_acolumn_eq_neg_baseRedundancy` (the base `−ρ₀` value
  at `vtx i`, eq. (6.66)). This is exactly the `hrCol` arg `notMem_span_mkQ_pmR_row_of_gate` consumes; the
  member MOVES (the row is the relabel image) while `ρ₀` stays fixed — KT's (6.66) wall-escape. With (α)
  isolated, the chain arm's only remaining genuinely-new content is (β) the chain bottom family `f`/`hf`
  (partly the 2c-iii dispatch's job). Axiom-clean (`propext`/`Classical.choice`/`Quot.sound`), build/lint
  clean. FRICTION `[idiom]` (the `Fin.ext (by omega)` → `simp only [Fin.mk.injEq]; omega` sibling of
  entry 110's `Fin.mk`-atomization).
- **(α) column-naturality bridge `funLeft_dualMap_comp_single` LANDED (2026-06-21) — the first of the chain arm's
  two NOT-yet-isolated arm-internal steps, now a standalone consume-leaf (§I.8.24(4.5)(α)).** For
  `σ : Equiv.Perm α`, `((funLeft σ).dualMap φ).comp (single w) = φ.comp (single (σ.symm w))`: reading the relabel
  image of any functional at body `w`'s screw column = reading the original at body `σ⁻¹ w`'s column. Bridges the
  LANDED base-side `±r` identity `interior_group_acolumn_eq_neg_baseRedundancy` (`−ρ₀` at the base body) to the
  candidate-side `hrCol` the (b) leaf `notMem_span_mkQ_pmR_row_of_gate` wants (the candidate `±r` row is the relabel
  image `(funLeft (shiftPerm i.castSucc)⁻¹).dualMap` of the base group). The general-`φ` (whole degree-2 group, not
  one `hingeRow`) + `σ⁻¹`-on-the-column form distinguishes it from `hingeRow_funLeft_dualMap` (endpoints, forward
  `ρ`, no bijectivity). `RigidityMatrix/Basic.lean`, after `hingeRow_funLeft_dualMap`; axiom-clean, build/lint clean.
  FRICTION `[idiom]` (the `Pi.single_eq_of_ne` side-goal needs the `Equiv.apply_symm_apply` round-trip, not
  `assumption`); sibling of the `funLeft`/`dualMap` relabel-transport cluster.
- **(b) crux `notMem_span_mkQ_pmR_row_of_gate` LANDED (2026-06-21) — the chain arm's ONE genuinely-new leaf, exactly
  at the §I.8.24(4.1) pinned signature.** KT 2011 (6.65): the `±r` row's class mod the base block `W` ∉ the
  candidate panel rows' span. Proof: contradiction; `in span ⟹ rRow − y ∈ W` (`Set.range_comp`+`← Submodule.map_span`
  pull a representative, `Submodule.Quotient.eq`); the single-column map `T = (single vᵢ).dualMap` sends W→0 (`hW`),
  rRow→−ρ₀ (`hrCol`), each panel row→`annihRow(C(e)) ∈ (span C(e))^⊥` (the `span_panelRow_comp_single_of_edge`
  column form, reused as an equality); so `−ρ₀ ∈ (span C(e))^⊥`, hence `ρ₀(C(e))=0`, and `hsupp` rewrites to
  contradict `hgate`. No new math; all ingredients in tree. With (a)+(b)+append-one all landed, the arm's `hLI` is
  pure wiring. Axiom-clean (`propext`/`Classical.choice`/`Quot.sound`), build/lint clean. FRICTION `[idiom]` (the
  `↑i`-subtype-`.2.1`-annotation metavar trap — destructure `⟨⟨i,hi⟩,rfl⟩`; covered by the existing entry).
- **Chain-arm leaf decomposition design-pass (2026-06-21, docs-only) — `case_III_arm_realization_chain` broken
  into named sub-leaves with exact signatures + build order, (b) ISOLATED as its own standalone lemma.** Verified
  against the LANDED bodies (chain cert `:1770`, engine `:310`, shared tail `:63`, M₃ template `:2537`, the (a)/
  append-one/carrier/`±r`-identity consume-leaves, A-1's `hcombGv` `:439–445`, the dispatch's `hgate`-into-arm
  `:439–441/501`): the arm's ONLY genuinely-new content is `(W,hWS,hWcard,hg,hLI)`, and within it the (b)
  `±r`-row half — pinned as `BodyHingeFramework.notMem_span_mkQ_pmR_row_of_gate` (KT (6.65), follows cleanly from
  the `−ρ₀` column identity + `hgate`, no motive/new-math). Two arm-internal steps flagged NOT-yet-isolated
  (clause ii): (α) the candidate-transported `hrCol` bridge, (β) the chain bottom family `f`/`hf` — both
  member-MOVING buildable, factor-into-leaves a build call. Design §(o‴)(I.8.24)(4); *Hand-off* re-pointed to (b).
- **`hLI` corner obligation (a) — panel-rows-LI-mod-`W` — landed (2026-06-21), closing the last
  abstract-LA piece of the chain arm's `hLI`.** Two decls: the abstract mirror
  `Submodule.linearIndependent_mkQ_of_comp` (`Mathlib/LinearAlgebra/Dimension/Constructions.lean`, beside the
  append-one criterion) — `W ≤ ker T` + `LinearIndependent (T ∘ f)` ⟹ `LinearIndependent (W.mkQ ∘ f)`, via
  `LinearIndependent.of_comp (W.liftQ T hW)` + `liftQ_mkQ` (~6 lines); and its carrier instantiation
  `BodyHingeFramework.linearIndependent_mkQ_panelRow_of_edge` (`Candidate.lean`, after the `hWS` packaging leaf) at
  `T = (single v).dualMap` — the candidate fresh hinge `e`'s `D−1` panel rows (pinned-LI via
  `linearIndependent_panelRow_comp_single_of_edge`) are LI mod a base `W` whose rows vanish off `v`'s screw column
  (`hW : ∀ φ ∈ W, φ ∘ₗ single v = 0`, KT 2011 (6.16)'s block-triangular column split). With (b)'s append-one mirror
  already landed, BOTH `hLI` abstract halves are now consume-leaves; the arm supplies only the concrete `hW`/`hindep`
  + the (b) `notMem_span` discriminator. Axiom-clean (`propext`/`Classical.choice`/`Quot.sound`), build/lint clean.
  FRICTION `[mirrored]` entry; the dual to the append-one criterion.
- **Carrier `hWS`/`hWcard` packaging leaf `exists_le_finrank_span_rigidityRows_eq_card_of_injective_map` landed
  (2026-06-21), closing the §I.8.24(3) "one residual not-yet-in-tree piece" (the relabel-image base block as a
  PACKAGED SUBSPACE).** `BodyHingeFramework.exists_le_finrank_span_rigidityRows_eq_card_of_injective_map`
  (`Candidate.lean`, after `finrank_span_rigidityRows_ge_of_corner`): an LI base family `f : ιb → Module.Dual ℝ
  (α → ScrewSpace k)` + an injective `L` + `∀ j, L (f j) ∈ span F.rigidityRows` ⟹ `∃ W ≤ span F.rigidityRows,
  finrank W = |ιb|`. A direct `exact` of the mirror `Submodule.exists_le_finrank_eq_card_of_injective_map` on the
  rigidity-row carrier (`ScrewSpace` never unfolded). So the chain arm's `hWS`/`hWcard` corner obligation is now a
  consume-landed-brick step (apply at `L = (funLeft (shiftPerm)⁻¹).dualMap`, `f` = the bottom family `w`, `hS` =
  `chainData_bottom_relabel`'s span-level transport); the genuinely-new part left is supplying `f`/`hf`/`hS` against
  the concrete chain data. Axiom-clean (`propext`/`Classical.choice`/`Quot.sound`), build/lint clean; no friction
  (one-line wrapper). With this, ALL of the chain cert's corner-data infrastructure leaves are in tree — the arm is
  pure carrier wiring (no remaining abstract-LA or carrier-friction sub-risk).
- **`hLI` corner-LI abstract step `linearIndependent_mkQ_sumElim_unit_of_notMem_span` mirrored (2026-06-21),
  closing the arm's abstract-LA sub-risk.** The append-one LI-MOD-`W` criterion (mirror,
  `Mathlib/LinearAlgebra/Dimension/Constructions.lean`, beside the block-rank-additivity lemma it feeds): a family
  `f` LI mod `W` augmented by one extra `x` with `W.mkQ x ∉ span (range (W.mkQ ∘ f))` keeps `W.mkQ ∘ Sum.elim f
  (fun _ : Unit => x)` LI. This is the abstract core of `case_III_arm_realization_chain`'s `hLI` obligation for the
  `Sum.elim (D−1 panel rows) (±r row)` corner (KT 2011 (6.65): `Mᵢ` full-rank mod base `⟺ r ∉ rowspace r(Lᵢ)`).
  Push `W.mkQ` through `Sum.elim` (funext+`cases`) → `LinearIndependent.sum_type` + `of_subsingleton` (the singleton
  block) + `disjoint_span_singleton'` (disjointness). Axiom-clean, build/lint clean. So the arm now only has to
  discharge (a) panel rows LI mod `W` + (b) `±r` class ∉ their span against the CONCRETE `g` (the genuinely-new
  wiring) — the abstract append-one step is landed. FRICTION `[mirrored]` entry; sibling of the non-quotient
  `linearIndependent_sumElim_unit_iff`.
- **SHARED W6a–W6f tail `case_III_realization_of_rank` FACTORED OUT (2026-06-21), zero-regression.** Extracted
  the rank-to-realization tail of `case_III_arm_realization` (`Arms.lean`) — the part depending only on the
  candidate rank bound `hrank` + split/seed data, not on the certification route (W6e re-extract → W6f good-`t`
  shear → GAP-3 → GAP-2) — into a standalone lemma taking `hrank` as a hypothesis. The d=3 engine now derives
  `hrank` via `case_III_rank_certification` and delegates (`exact case_III_realization_of_rank …`); M₂/M₃ +
  dispatch untouched. Build/lint/axiom-clean (`propext`/`Classical.choice`/`Quot.sound`). This realizes the
  §I.8.24(3) "SHARED arm-realization tail … lifts verbatim" REUSE brick, so `case_III_arm_realization_chain`
  produces only the corner data + `hrank` and reuses the tail (no ~180-line W6a–W6f copy). Friction: factoring
  `caseIIICandidate` into the `hrank` *signature* re-exposed its `[DecidableEq β]` requirement that `classical`
  was covering in the engine body (FRICTION `[idiom]` `Matroid.Union`-`DecidableEq`-in-signature entry).
- **FIRST build `case_III_rank_certification_chain` LANDED (2026-06-21), §I.8.24(1) type-checks in Lean.**
  The forked general-`d` Case-III rank cert (`Candidate.lean`, after `finrank_span_rigidityRows_ge_of_corner`),
  axiom-clean, build/lint clean. It is a *re-statement consuming landed bricks*: takes the corner data
  `(W, hWS, hWcard : finrank W = D(m_v−1), ι/hιcard : |ι| = D, g, hg, hLI)` as hypotheses (the project's
  explicit-`h…`-hypothesis idiom — the chain ARM discharges them next), applies
  `finrank_span_rigidityRows_ge_of_corner`, and closes the count `finrank W + D = D·m_v = D(|V(G)|−1)` via
  `Nat.mul_succ` (needs `hVone : 1 ≤ |V(Gv)|` + `hVcard`). **NO `hρGv` slot** — the cert is selector-agnostic and
  reads off the corner block, so KT's `±r` row enters as a member of `g`, never the collapsed fixed-member row.
  Confirms (A) escapes the wall in Lean, not just on paper.
- **`hWS` base-block-as-subspace packaging leaf landed (2026-06-21), closing the FIRST-build sub-risk
  §I.8.24(3).** `Submodule.exists_le_finrank_eq_card_of_injective_map` (mirror,
  `Mathlib/LinearAlgebra/Dimension/Constructions.lean`): `f` LI + `L` injective + `∀ i, L (f i) ∈ S` ⟹ a
  `W' ≤ S` with `finrank W' = |ι|` (image span; `LinearIndependent.map'` along injective `L` +
  `finrank_span_eq_card` + `span_le`, a 3-line term proof). Axiom-clean, build/lint clean. Instantiated at
  `L = (funLeft (shiftPerm)⁻¹).dualMap` it packages the relabel-image base block as the chain cert's `W` with
  `finrank W = D(m_v−1)` — so the cert's `hWS` is now a consume-landed-brick step, not a wall. Next: the cert
  itself, whose only genuinely-new content is the `hLI` discriminator-mod-`W` reduction.
- **Opened at a user-adjudicated clean-break close of 23b (2026-06-21).** 23b's CHAIN target (the chain
  dispatch) was not reached — the `hρGv`-seam is a hard core (the member-mapping wall, intrinsic to KT). 23b
  closes on its delivered bricks + the decisive hard-core characterization; the arm/dispatch re-architecture
  carries to 23c, whose first move is an architectural decision, not a build. Rationale: design
  §(o‴)(I.8.18)–(I.8.20); the d=3-is-degenerate / read-the-source-early lessons (`DESIGN.md`, model-exp
  Findings 2026-06-21).
- **Option (A) de-risk spike landed POSITIVE (2026-06-21).** The §I.8.21(2b)(α) hardest + cost-unknown leaf —
  basis-free block-rank-additivity — is axiom-clean and the `ScrewSpace`/§38-defeq friction did NOT bite.
  `Submodule.finrank_add_card_le_of_linearIndependent_mkQ` (mirror) proves `W ≤ S` + `g`-in-`S` +
  `W.mkQ ∘ g` LI ⟹ `finrank W + |ι| ≤ finrank S` in ~10 lines off the *existing* `finrank_map_mkQ` +
  `finrank_span_eq_card` (no new LA machinery); `finrank_span_rigidityRows_ge_of_corner` (`Candidate.lean`)
  instantiates it on `Module.Dual ℝ (α → ScrewSpace k)` by `inferInstance`, never unfolding the carrier. So
  the basis-free API carries KT's `rank Mᵢ + rank(base∖row)` (6.64–6.65); the STOP-and-escalate-to-`Matrix`
  branch is closed. Next: re-pointed to (2b)(γ) by the §I.8.22 pin recon (below).
- **(2b)(β)/(2b)(γ) de-risk recons → both settled, subsumed by §I.8.24 (§I.8.22/§I.8.23, 2026-06-21).** (2b)(β):
  the landed cert already realizes KT's `Mᵢ + base` inline (`(sn ⊕ Unit) ⊕ ιb`), the wall is its `hρGv` slot, not
  a missing `Mᵢ` corner. (2b)(γ): the (6.66) `±r` ℝ^D-identity is POSITIVE + already built (LEAF 1–4, axiom-clean,
  `interior_group_acolumn_eq_neg_baseRedundancy = −ρ₀` member-free). Detail: design §(o‴)(I.8.22)/(I.8.23).
- **§(I.8.24) cert-re-shape design-pass → (A) ESCAPES THE WALL; the §I.8.22-vs-§I.8.23 tension RESOLVES
  FAVORABLY (2026-06-21, docs-only).** Settled per-hypothesis against the landed de-risk-leaf signature +
  §I.8.20(e): the de-risk leaf's `hWS`/`hg` are the BUILDABLE relabel-IMAGE inclusion (member-moving) + genuine
  candidate rows, `hLI` the discriminator at the FIXED `ρ₀` + the `±r` value — NONE smuggles a fixed-member
  dependency. The KEY: the cert is selector-AGNOSTIC (parametric in `(G,Gv,ends,q)`, same selector both sides,
  `hFvle` direct `:1551`); the relabel lives in the ARM's arguments (M₃ instantiates the engine `:2624`); the
  wall is ONLY the landed cert's COLLAPSED `Unit` row (`hingeRow v a ρ`, needing `hρGv` `:1606`), which the
  re-shape replaces with KT's genuine candidate-edge row. Pinned: FORK — d=3 keeps the landed engine,
  general-`d` gets `case_III_rank_certification_chain` + `_arm_realization_chain`. FIRST build =
  `case_III_rank_certification_chain` (sub-risk: package the relabel-image base block as a subspace `W` with
  `finrank W = D(m_v−1)`, `LinearIndependent.map'` route). ~5–9c. Detail: design §(o‴)(I.8.24).
