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

**BLOCKED (2026-06-21): the `±r`-row sourcing seam does NOT close from the landed leaves — a VERIFIED
column-index/object mismatch between the `hg` route and the `hrCol` route (design §I.8.24(4.8)).** Assembling
the arm exposes that **no single `±r`-row object grounds BOTH the cert's `hg` AND the discriminator's `hrCol`**
from what is in tree. The re-inserted body is `vᵢ = vtx i` (the candidate hinge `e_a` links `vtx i — vtx(i+1)`,
so the discriminator reads `hrCol` at `single (vtx i)`), but the landed `hrCol` leaf
`funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy` reads `−ρ₀` at `single (vtx(i-1))` — the WRONG
body — for the FILTERED edge-`i` group, which (a) does NOT collapse to a single row (so the reproduced-slot
leaf's `hcollapse` is unsatisfiable) and (b) relabels its endpoints to the candidate fresh pair (so the off-slot
GROUP leaf's `htransport` is unsatisfiable). The full-combination single row (via T-2) IS a clean genuine row
`hingeRow (vtx 0)(vtx 1) ρ` with a valid `hg`, but reads `0` at `single (vtx i)`, not `−ρ₀`. **This is the
clause-(ii) FLAG-DON'T-FORCE stop** (a 4th pin on this seam would be a confident-wrong one). Full diagnosis +
the corrected leaf signature + the named open decision: design §(o‴)(I.8.24)(4.8).

> **Orientation for the next agent.** The high-level architecture is still sound (the cert is selector-agnostic,
> NO `hρGv` slot; cert + carrier + abstract-LA + both `hLI` halves all landed). **Do NOT** re-attempt the four
> dead route families (§(o‴)(I.8.18)–(I.8.20)) or re-litigate the fork. But the `±r`-row `hg`/`hrCol` sourcing
> is **not yet closed** (§I.8.24(4.8)) — the (4.7) "both `hg` leaves landed, arm is pure wiring" claim was
> OVERSTATED: the reproduced-slot leaf's `hcollapse` input is unbuilt. The next concrete commit is **the
> corrected `±r`-row sourcing**: a `vtx i`-column `hrCol` leaf (reading the re-inserted body, not `vtx(i-1)`) +
> a single-reproduced-row `hg` for `hingeRow (vtx i)(vtx(i-1)) ρ₀` (incident to `vᵢ`, the M₃ `hvb_row` `:2866`
> route generalized to the cycle), gated on the OPEN DECISION `hingeRow (vtx i)(vtx(i-1)) ρ₀ ∈ span (candidate
> rows)` — the substantive KT-(6.66) step the current leaves miss (the same math the dead `hρGv`-spine attacked,
> §I.8.0–I.8.3). Signature + fate-of-leaves: §I.8.24(4.8) + *Hand-off*.

## Current state

**BLOCKED on the `±r`-row sourcing (§I.8.24(4.8)) — the cert's `g`-corner `±r` row cannot satisfy BOTH `hg`
AND `hrCol` from the landed leaves; the next leaf is the CORRECTED `±r` sourcing, gated on an open decision.**
The high-level (A) architecture is sound (cert is selector-agnostic, NO `hρGv` slot; the member-mapping wall is
out of the cert). The four dead route families (§I.8.18–(I.8.20)) stay exhausted; **do not re-attempt.** What
the arm-build exposed: the re-inserted body is `vᵢ = vtx i`; the discriminator
`notMem_span_mkQ_pmR_row_of_gate` reads `hrCol` at `single (vtx i)`; but the landed `hrCol` leaf
`funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy` reads `−ρ₀` at `single (vtx(i-1))` (wrong body)
for the FILTERED edge-`i` group — whose `hg` is unsatisfiable (no collapse to a single row; relabelled endpoints
= the fresh pair). The full-combination single row (T-2) has a clean `hg` but reads `0` at `vtx i`. Full audit:
design §(o‴)(I.8.18)–(I.8.24)(4.8).

**Landed (all axiom-clean), still usable:** the cert `case_III_rank_certification_chain` (NO `hρGv`); carrier
W-packaging `exists_le_finrank_span_rigidityRows_eq_card_of_injective_map`; both `hLI` halves
(`linearIndependent_mkQ_panelRow_of_edge`, `notMem_span_mkQ_pmR_row_of_gate`) + assembly
`linearIndependent_mkQ_corner_of_gate`; the (α) column bridge `funLeft_dualMap_comp_single`; the off-slot row
bridge `hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link`; the per-member genuine transport
`chainData_bottom_relabel`; the SHARED tail `case_III_realization_of_rank`; the off-slot GROUP leaf
`funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` (serves the genuine off-slot `hWS` bottom family — its
correct use). **Landed but mis-aimed for the `±r` corner:** the `hrCol` leaf
`funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy` (reads `vtx(i-1)`, not the re-inserted `vtx i`);
the reproduced-slot `±r`-row leaf `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate_reproduced` (its
`hcollapse` input is unbuilt for the filtered group). **Orphaned:** T-2
`chainData_candidateRow_edgeGrouped_transport_comb` (the full-combination single-row transport — revive only if
the corrected sourcing routes through it).

**Next: the corrected `±r`-row sourcing (NOT the arm yet).** A `vtx i`-column `hrCol` leaf (reading the
re-inserted body) + a single-reproduced-row `hg` for `hingeRow (vtx i)(vtx(i-1)) ρ₀` (incident to `vᵢ`,
generalizing the M₃ `hvb_row` `:2866` reproduced-row route), gated on the OPEN DECISION
`hingeRow (vtx i)(vtx(i-1)) ρ₀ ∈ span (candidate rows)` — the substantive KT-(6.66) step (the same math the dead
`hρGv`-spine §I.8.0–I.8.3 attacked). Signature in *Hand-off* + design §I.8.24(4.8). Relabel.lean (~4830 lines,
past the ~1500 tripwire) likely forces a `Relabel/` split when the arm finally builds — flag at that build.

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
   bridge + `chainData_bottom_relabel` ✓ ALL LANDED** (2026-06-21, axiom-clean; names in *Current state*).
   **BLOCKED:** the `±r`-row sourcing — no single object grounds BOTH `hg` AND `hrCol`-at-`vᵢ` from the
   landed leaves (§I.8.24(4.8), VERIFIED). The corrected `vtx i`-column `hrCol` + single-reproduced-row `hg`
   (gated on the open decision) is the next leaf. Then the arm: *Hand-off*.
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

**BLOCKED (§I.8.24(4.8)); the next concrete commit is the CORRECTED `±r`-row sourcing, gated on an open
decision — NOT `case_III_arm_realization_chain` yet.** The (4.7) "both `hg` leaves landed, arm is pure wiring"
claim was overstated; the reproduced-slot leaf's `hcollapse` is unsatisfiable for the filtered group, and the
landed `hrCol` leaf reads the wrong body (`vtx(i-1)` not the re-inserted `vtx i`). Full diagnosis: design
§I.8.24(4.8).

**Build order (revised):**
1. **The CORRECTED `±r`-row sourcing** (`Relabel.lean`). Two coupled leaves:
   - a `vtx i`-column `hrCol` leaf — reading the `±r` row's column at the re-inserted body `single (vtx i)`
     (the candidate-hinge tail the discriminator pins), NOT the landed `vtx(i-1)` of
     `funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy`. Candidate shape:
     `(hingeRow (vtx i)(vtx(i-1)) ρ₀).comp (single (vtx i)) = ρ₀` (sign reconciled vs the discriminator's `−ρ₀`).
   - a single-reproduced-row `hg`: `hingeRow (vtx i)(vtx(i-1)) ρ₀ ∈ span (caseIIICandidate … e_a e_b …)`
     rigidityRows, via `caseIIICandidate_supportExtensor_reproduced` + `hperp` (the reproduced slot `e_b` links
     `{vtx i, vtx(i-1)}`, incident to `vᵢ`). This generalizes the M₃ engine's own `hvb_row` reproduced-row build
     (`Relabel.lean:2866`) to the cycle.
   - **OPEN DECISION (gates both):** `hingeRow (vtx i)(vtx(i-1)) ρ₀ ∈ span (candidate rows)` — does the
     transported redundancy land on the `{vtx i, vtx(i-1)}` edge (the reproduced slot, incident to `vᵢ`), NOT the
     `{vtx(i-1), vtx(i+1)}` fresh pair the filtered-group relabel produces? This is the substantive KT-(6.66)
     step the current leaves miss (the same math the dead `hρGv`-spine §I.8.0–I.8.3 attacked: `hingeRow vᵢ₋₁
     vᵢ₊₁ ρ₀ ∈ span (G−vᵢ)`). Resolve before committing the leaf.
   - **Fate of leaves:** GROUP leaf RETAINED (genuine off-slot `hWS` family); reproduced-slot leaf (`b675317`)
     RETAINED but re-aim its `hcollapse` to the single reproduced row or supersede; `hrCol` leaf RETAINED as the
     base-side `vtx(i-1)` fact (not the discriminator's `hrCol`); T-2 REVIVE only if the corrected sourcing
     routes through it (route (a) shows the full row reads `0` at `vtx i`).
2. **Then `case_III_arm_realization_chain`** (`Relabel.lean`, NOT `Arms.lean` — import DAG `Arms ⊂ Relabel ⊂
   Realization`; M₃ `:2691` is the construct-candidate + corner-data template). Builds `caseIIICandidate (G−vᵢ)
   endsσρ qρ e_a e_b …`, assembles `(W,hWS,hWcard,g,hg,hLI)` — **`hWS`/`hWcard`** ← carrier leaf
   `exists_le_finrank_span_rigidityRows_eq_card_of_injective_map`; **`hg`** off-slot family ← GROUP leaf, `±r`
   row ← the corrected single-reproduced-row `hg`; **`hLI`** ← `linearIndependent_mkQ_corner_of_gate` with
   `hrCol` from the corrected `vtx i`-column leaf — then `case_III_rank_certification_chain` for `hrank` +
   `exact case_III_realization_of_rank …`.
3. **Then:** 2c-iii `chainData_dispatch` (interior `2 ≤ i < d`, d=3 floor on the engine) → CHAIN-5 wire-up →
   orphan confirm-and-delete (the `hφ`-spine; LEAF 1–4 STAYS). **Cost band ~4–7 commits** (the corrected
   sourcing + open-decision resolution adds ~1–2). Audit: design §(o‴)(I.8.24)(4)/(4.7)/(4.8).

## Decisions made during this phase

- **BLOCKED — the `±r`-row sourcing does NOT close from the landed leaves; column-index/object mismatch
  between `hg` and `hrCol` (2026-06-21, opus docs-only design-settle; VERIFIED against the landed bodies).**
  Assembling `case_III_arm_realization_chain` exposed that no single `±r`-row object grounds BOTH the cert's
  `hg` AND the discriminator's `hrCol`. Re-inserted body `vᵢ = vtx i` (candidate hinge `e_a` links
  `vtx i—vtx(i+1)`, discriminator reads `hrCol` at `single (vtx i)`); but the landed `hrCol` leaf reads `−ρ₀`
  at `single (vtx(i-1))` (wrong body) for the FILTERED edge-`i` group — whose `hg` is unsatisfiable (no
  collapse to a single row → reproduced-slot `hcollapse` dead; relabelled endpoints = the fresh pair → off-slot
  `htransport` dead). The full-combination single row (T-2) `hingeRow (vtx 0)(vtx 1) ρ` has a clean `hg` but
  reads `0` at `vtx i`. **FLAG-DON'T-FORCE stop** (a 4th pin would be confident-wrong). FIX = a CORRECTED `vtx
  i`-column `hrCol` leaf + a single-reproduced-row `hg` for `hingeRow (vtx i)(vtx(i-1)) ρ₀` (incident to `vᵢ`,
  the M₃ `hvb_row :2866` route), gated on the OPEN DECISION `hingeRow (vtx i)(vtx(i-1)) ρ₀ ∈ span (candidate
  rows)` (the KT-(6.66) step the current leaves miss). Full diagnosis + signatures + leaf-fates: design
  §(o‴)(I.8.24)(4.8). Supersedes the (4.7) "arm is pure wiring" framing.
- **Reproduced-slot `±r`-row `hg` leaf LANDED (2026-06-21) — pinned by §I.8.24(4.7), but its `hcollapse` input
  is UNBUILT (see BLOCKED above); the "all corner-data leaves in tree" claim was overstated.**
  `PanelHingeFramework.funLeft_dualMap_pmR_group_mem_span_caseIIICandidate_reproduced` (`Relabel.lean:2212`):
  takes `hcollapse` (relabel image = the reproduced-edge tag `hingeRow (endsσρ e_r).1 (endsσρ e_r).2 ρ₀`) +
  `hperp` + `hlink` as hypotheses, proves the tag is a candidate rigidity row at the reproduced slot `e_r` via
  `mem_hingeRowBlock_iff` + `caseIIICandidate_supportExtensor_reproduced`. Axiom-clean, build/lint clean. BUT
  §I.8.24(4.8) shows the filtered edge-`i` group does NOT collapse to a single row, so `hcollapse` is
  unsatisfiable for it — the leaf must be re-aimed at a single reproduced row or superseded by the corrected
  sourcing.
- **The off-slot GROUP leaf is mis-targeted for the `±r` row (VERIFIED 2026-06-21; commit 2b22d59).** A-1's
  `±r`-group's `(shiftPerm i.castSucc)⁻¹`-image endpoints are the candidate fresh pair `{vᵢ₋₁, vᵢ₊₁}`, so the
  GROUP leaf's off-slot `htransport` is unsatisfiable for it. GROUP leaf KEPT for the off-slot `hWS` bottom
  family. (The (4.7) follow-on "→ reproduced-slot leaf is the correct `hg`" is SUPERSEDED — the reproduced
  leaf's `hcollapse` is itself unsatisfiable for the filtered group; see the BLOCKED entry + §I.8.24(4.8).)
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
