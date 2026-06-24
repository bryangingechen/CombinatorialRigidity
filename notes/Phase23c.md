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

> **Orientation for the next agent.** The arm `case_III_arm_realization_chain` AND the corner-data ASSEMBLY
> producer `case_III_arm_corner_assembly` (the seam-resolution end-to-end integration) are BOTH LANDED; the
> `±r`-row seam stays CLOSED — the assembly CONFIRMS the corrected `±r` leaf feeds the cert's `hg` and the
> corrected `hrCol` feeds `hLI`. **Do NOT** re-attempt the four dead route families (§I.8.18–(I.8.20)),
> re-litigate the fork, or revive the relabel-image `±r` route. The next concrete commit is **CHAIN-2c-iii
> `chainData_dispatch`** — which PRODUCES the assembly's raw inputs (`hgate`/`hρe₀` from A-1 at the interior
> split; `W`/`hWS`/`hWcard`/`hW` from the chain bottom family via the carrier leaf + relabel-image off-`v`
> vanishing) from the `ChainData` interior split, routing `2 ≤ i < d` through `case_III_arm_corner_assembly`
> and the `d=3` floor (`i=2`) on the landed `case_III_arm_realization` engine. See *Hand-off*.

## Current state

**The dispatch's interior-split-tuple `ChainData` accessors are LANDED (`Induction/Operations.lean`,
axiom-clean, build/lint warning-clean); next is the rest of CHAIN-2c-iii `chainData_dispatch` (the
discriminator + base-block construction + arm routing).** At an interior chain index `i` (`0 < i`)
the dispatch reads the arm split tuple `(v, a, b, e_a, e_b) = (vtx i.castSucc, vtx i.succ,
vtx (i−1).castSucc, edge i, edge (i−1))` over `Gv = G.removeVertex v`; the combinatorial split facts
the arms (`case_III_arm_corner_assembly` / the d=3 `case_III_arm_realization`) require are now direct
`ChainData` accessors: the two link facts (`isLink_succ_edge`/`isLink_pred_edge`, pre-existing), the
`heab` distinctness (`pred_edge_ne`, pre-existing), the `(v,a)`/`(v,b)` distinctnesses
(`castSucc_ne_succ`/`castSucc_ne_pred_castSucc`, NEW), the three `Gv`-membership facts
(`notMem_/succ_mem_/pred_castSucc_mem_vertexSet_removeVertex_castSucc`, NEW = the arm's
`hvVc`/`haVc`/`hbVc`), and the edge partition `isLink_eq_succ_or_pred_or_removeVertex` (NEW = the
arm's `hsplitG`). The corner-data ASSEMBLY producer `case_III_arm_corner_assembly`
(`Relabel/ForkedArm.lean`, axiom-clean) + the arm spine `case_III_arm_realization_chain` stay landed.
That assembly is the seam-resolution end-to-end
integration test the hand-off named: at the candidate `F₀ = caseIIICandidate G ends q e_a e_b (q(a,·)) n'
(q(b,·)) 0` it *constructs* the `±r` corner block `g = Sum.elim (D−1 fresh-hinge `e_a` panel rows) (±r row)`
over `ι = ↥s ⊕ Unit` (`Fintype.card = (D−1)+1 = D`) and feeds it to the arm spine
`case_III_arm_realization_chain`. It **CONFIRMS the corrected `±r` leaf feeds the cert's `hg` and the corrected
`hrCol` feeds `hLI`**: the panel rows come from `exists_independent_panelRow_subfamily_of_edge` at `e_a` (each a
candidate rigidity row via `panelRow_mem_rigidityRows_of_link` at the direct `G`-link `e_a=va`); the `±r` row is
`hingeRow b v ρ₀` (genuine reproduced-slot `e_b`-row, head `v`) with `hg` from
`hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`hperp = hρe₀`, `t=0`, NEVER `hρGv`) and the discriminator
via `linearIndependent_mkQ_corner_of_gate` (`hrCol` from `reproducedSlot_pmR_acolumn_eq`, `b≠v`). It takes the
dispatch's RAW outputs (`hgate`/`hρe₀` discriminator; `W`/`hWS`/`hWcard`/`hW` base-block — the spine's own
`W`-corner shape) as explicit hypotheses; the dispatch produces them next. The four dead route families
(§I.8.18–(I.8.20)) stay exhausted; **do not re-attempt.**

The arm spine `case_III_arm_realization_chain` (the cert→tail wiring) + the `±r`-row sourcing leaves all stay
landed. The high-level (A) architecture is fully realized end-to-end at the arm + assembly level: the seam is
proven to close in Lean, not just on paper. Full audit: design §(o‴)(I.8.24)(4.9).

**The `Relabel/` split is DONE (2026-06-23, build/lint/axiom-clean).** The over-cap
`CaseIII/Relabel.lean` (5066 lines) is split into a 5-file `CaseIII/Relabel/` subdirectory — a pure
mechanical, semantics-preserving cut along the existing section headers (no decl renamed → blueprint
`\lean{}` pins / `checkdecls` unaffected; the three terminal decls re-verified axiom-clean). The
chain (each file imports its predecessor, terminating at `ForkedArm` which `CaseIII/Realization`
now imports): `Relabel/Basic` (~1645 — the M₃ relabel apparatus + `wstep`/`shiftBody*` defs),
`Relabel/Chain` (~969 — the ascending seed-advancing chain + `chainData_bottom_relabel` +
`case_III_bottom_relabel` + acolumn bridges + candidate-perp incidence), `Relabel/Arm` (~1044 —
the M₃ arm `case_III_arm_realization_M3` + `i=3` de-risks + the `wstep` telescope),
`Relabel/ChainColumn` (~1283 — the eq.~(6.44) chain-induction column machinery + interior-group
`−ρ₀` reading + `chainData_relabel_arm_hρGv`), `Relabel/ForkedArm` (~219 — the forked general-`d`
arm `case_III_arm_realization_chain` + the corner-data assembly `case_III_arm_corner_assembly`). The
dispatch build can now add chain-arm-consuming machinery without re-tripping the cap.

**Landed (all axiom-clean), the arm + assembly now closed:** the corner-data ASSEMBLY producer
`case_III_arm_corner_assembly` (`Relabel/ForkedArm.lean`, constructs `g`/`hg`/`hLI`/`hιcard` and calls the spine); the arm
spine `case_III_arm_realization_chain` (the cert→tail composition over `F₀`, corner data + count facts as
explicit hypotheses); the cert `case_III_rank_certification_chain` (NO `hρGv`); carrier W-packaging
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

**Next: CHAIN-2c-iii `chainData_dispatch` — DECOMPOSED into 5 ranked commit-sized leaves** (design
§(o‴)(I.8.24)(4.10), 2026-06-23). The dispatch is a **discriminator-pick + Fin-case ROUTER** over two
ALREADY-LANDED arm routes — `chainData_split_realization` (the OLD engine, for base `i=1` + d=3 floor,
zero-regression) and `case_III_arm_corner_assembly` (for interior `2 ≤ i < d`) — plus the production of the
corner-assembly's RAW inputs (the HARD CORE = LEAF-4). **LEAF-2 is LANDED** (2026-06-23, axiom-clean,
build/lint warning-clean): the concrete-`W` carrier variant
`BodyHingeFramework.span_relabelImage_le_and_finrank_and_acolumn_vanish` (`Candidate.lean`, beside the
existential leaf) — `W := span (range ((funLeft σ).dualMap ∘ f))` concretely, with the third corner datum
`hW : ∀ φ ∈ W, φ ∘ₗ single v = 0` (the new content, a `span_induction` routing each generator through the (α)
bridge `funLeft_dualMap_comp_single` + `hvanish` at `σ.symm v`); `hWS`/`hWcard` reuse the existential leaf's
content. **LEAF-1 is LANDED** (2026-06-23, axiom-clean, build/lint warning-clean): the interior-candidate
relabel-image selector/seed `ChainData.candidateEnds` / `candidateSeed` (`Induction/Operations.lean`, beside
the sibling interior-split accessors) — the two `def`s the dispatch feeds `case_III_arm_corner_assembly`,
matching `chainData_bottom_relabel`'s target framework verbatim (`endsσρ = ρ.symm ∘ ends₀ ∘ σ`, `qρ = q ∘ ρ`
on the body coordinate), each with its `rfl` `@[simp]` computation lemma; `candidateSeed` is generic in the
fibre type `γ` so it carries no `ScrewSpace`/`k` dependency. **LEAF-3 is BLOCKED on a FROZEN-CONTRACT
decision** (the discriminator-index gap, design §I.8.24(4.11), 2026-06-23): the two LANDED discriminators are
`Fin (k+1)`-indexed but the chain candidate is `i : Fin cd.d`, and these align only if `cd.d = k+1` — which
KT §6.4.2 makes structural (`d` candidates = `d` panels, `D = (d+1 choose 2) = screwDim k` ⟹ `d = k+1`) but
which the C.1 record (free `d`, `hd : 1 ≤ d` only) / C.3 dispatch contract do NOT carry. Recommended fix =
option (a): add `d_eq : cd.d = k+1` to `ChainData`/dispatch (~1 commit, d=3 zero-regression by `3=2+1`);
awaiting coordinator/user adjudication (a vs b; (c) ruled out by KT). Full options + estimates in §I.8.24(4.11)
+ *Hand-off* below. Once decided, LEAF-3 (discriminator plumbing) → LEAF-4 (hard core, the `hS` disjunction) →
LEAF-5 (router) → CHAIN-5 proceed as pinned. Home for the dispatch: a fresh `Relabel/Dispatch.lean` importing
`Relabel/ForkedArm`; the `Relabel/` split is DONE so it lands without re-tripping the cap.

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

1. **The forked general-`d` chain cert + arm + corner assembly** (§I.8.24) → the `±r`-based engine, NO `hρGv`.
   d=3 keeps the landed engine. **Cert + tail + carrier + both `hLI` halves + assembly + (α) bridge + off-slot
   row bridge + `chainData_bottom_relabel` + the `±r` corner sourcing (`hg` + `hrCol`) + the ARM spine
   `case_III_arm_realization_chain` + the corner-data ASSEMBLY producer `case_III_arm_corner_assembly` ✓ ALL
   LANDED** (2026-06-22, axiom-clean; names in *Current state*). The seam is proven to close end-to-end in Lean.
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

**CHAIN-2c-iii `chainData_dispatch` is DECOMPOSED into 5 commit-sized leaves (design §(o‴)(I.8.24)(4.10),
source-verified 2026-06-23 against the LANDED bodies after the `Relabel/` split).** The dispatch is NOT a
from-scratch composer: it is a **discriminator-pick + Fin-case ROUTER** over two ALREADY-LANDED arm routes —
the OLD engine via `chainData_split_realization` (`Realization.lean:954`, for the base candidate `i=1` + the
d=3 floor, zero-regression) and the option-(A) `case_III_arm_corner_assembly` (for interior `2 ≤ i < d`) —
PLUS the production of the corner-assembly's RAW inputs for the interior route. **The HARD CORE is LEAF-4**
(the interior base-block `W`/`hWS`/`hWcard`/`hW` production + the `hS` disjunction routing) — a build MUST NOT
peel the easy leaves and defer it.

**One design decision RESOLVED + LANDED (below the contract/motive — did NOT need coordinator/user).** The
`W`/`hW` threading: `case_III_arm_corner_assembly` takes `hW` on a *specific* `W`, but the landed carrier leaf
`exists_le_finrank_span_rigidityRows_eq_card_of_injective_map` returns an **existential** `W` (opaque — `hW`
unprovable on it). Resolution: the dispatch sets `W := span (range (L ∘ f))` CONCRETELY via a new concrete-`W`
carrier leaf (LEAF-2). This is a return-shape mismatch, not a motive change. **LEAF-2 is LANDED** (2026-06-23,
axiom-clean, build/lint warning-clean): `BodyHingeFramework.span_relabelImage_le_and_finrank_and_acolumn_vanish`
(`Candidate.lean`, immediately after the existential leaf). The signature matched the recon exactly;
`hWS`/`hWcard` reused the existential leaf's body (`span_le` + `finrank_span_eq_card` of the image family along
the injective dual map of the surjective `funLeft σ` via `dualMap_injective_of_surjective` +
`funLeft_surjective_of_injective`), and `hW` is a `Submodule.span_induction` whose `mem` case rewrites each
generator `(funLeft σ).dualMap (f j)` through the (α) bridge `funLeft_dualMap_comp_single` then closes with
`hvanish j`, the `zero`/`add`/`smul` cases distributing `· ∘ₗ single v` over the linear structure. The
`hvanish`-at-`σ.symm v` direction was FORCED by the bridge exactly as recon'd (the (4.8)-class column-index
trap). The concrete `σ` is the consumer's free choice (build-time latitude: instantiate at `σ = shiftPerm
i.castSucc` so `σ.symm` matches `chainData_bottom_relabel`'s relabel — a `.symm`-placement detail at LEAF-4,
not a wall).

**The LEAF-3 frozen-contract decision is RESOLVED → option (a) (2026-06-23, user-approved; a diverse-lens recon
pair + coordinator KT-PDF-verification confirmed `d=k+1` is structural; design §I.8.24(4.11)).** A build BLOCKED
here originally: the discriminator-index gap is NOT build-time `Fin` arithmetic — it is a frozen-contract change. Both LANDED
discriminators (`exists_chainData_discriminator_pick` `Realization.lean:1144`, capstone
`exists_complementIso_ne_zero_of_homogeneousIncidence_gen` `Claim612.lean:1462`) are `Fin (k+1)`-indexed
(panel `u : Fin (k+1)` off `cand : Fin (k+1) → α`); the chain candidate the assembly's `hgate` lands at is
`i : Fin cd.d`. KT §6.4.2 (verified, eqs. 6.46–6.67): `d` candidates = `d` panels = SAME index set, and
`D = (d+1 choose 2) = screwDim k = (k+2 choose 2)` ⟹ **`d = k+1` is structural** — candidate-`i` IS selected
by the panel discriminator, no `cd.d`-free selector exists (the `±r` redundancy is shared, eq. 6.66). But
`ChainData.d` is a free `ℕ` (`hd : 1 ≤ d` only) and the C.3 dispatch contract carries no `cd.d = k+1` — so the
gap needs a contract field/hypothesis. **Recommended option (a): add `d_eq : cd.d = k+1` to `ChainData` (C.1)
or the dispatch (C.3)** (~1 commit, structurally faithful, d=3 zero-regression by `3=2+1`, ENTRY later proves
`d=k+1` from Lemma 4.6); options (b) re-index discriminators over `Fin cd.d` (~3–5 commits, re-opens green
CHAIN-4, still needs `d=k+1`) and (c) separate selector (NOT available — ruled out by KT) in §I.8.24(4.11).
**Seed-reconciliation is NOT the blocker** — `candidateSeed` transport is the LANDED relabel-image machinery
(routine, no wall), downstream of the index gap.

**NEXT COMMIT (option a, the contract field): add `d_eq : d = n` to the `ChainData` RECORD** (`Operations.lean`,
the chain length = the dof-regime index `n`). Stated `d = n`, **not** `d = k+1`, because `n` is a record
parameter and `k` is not — `d = k+1` then follows at use sites from the ambient `hn : bodyBarDim n = screwDim k`
(⟹ `n = k+1`, a `Nat.choose`-injectivity step; mirror/derive as needed). It is a **constructive RECORD field**
(set at construction), NOT a dispatch hypothesis — the recon's refinement (the ENTRY extractor BUILDS the chain
to length `k+1`, so `d_eq` is *set, not proved-after-the-fact*; sidesteps the 392/394 satisfiability trap). Fix
every `ChainData` construction site (grep; the d=3 extractor `Graph.exists_chain_data_of_noRigid`,
`Reduction.lean:383`, supplies `3 = n` — zero-regression at the d=3/k=2 regime where `n=3`); build green.
**THEN** LEAF-1/LEAF-2 stay LANDED; LEAF-3 unblocks (`u : Fin (k+1)` ↔ `i : Fin cd.d` by transport across
`d_eq`+`hn`); LEAF-4 (hard core) → LEAF-5 (router) → CHAIN-5 proceed as pinned. **Watch the two downstream
risks** (design §I.8.24(4.11)): the ENTRY KT-4.6 chain-extraction leaf (23d, genuinely-new) and the eq-6.66
`±r`-across-all-interiors step (lands in LEAF-4/CHAIN bookkeeping).

**Build order (ranked EASIEST→HARDEST; full signatures + per-leaf risk in design §(o‴)(I.8.24)(4.10)):**
0. Open `Relabel/Dispatch.lean` (importing `Relabel/ForkedArm`; the `Relabel/` split is DONE — do NOT grow
   `Realization.lean`). The leaves split across `Candidate.lean` (LEAF-2 ✓), `Induction/Operations.lean`
   (LEAF-1 ✓), + `Relabel/Dispatch.lean` (rest).
1. ~~**LEAF-2 (EASY-MODERATE)** — the concrete-`W` carrier variant.~~ ✓ **LANDED** 2026-06-23
   (`Candidate.lean`, `BodyHingeFramework.span_relabelImage_le_and_finrank_and_acolumn_vanish`, axiom-clean).
2. ~~**LEAF-1 (EASIEST)** — the interior-split `endsσρ`/`qρ` candidate framework `def`s.~~ ✓ **LANDED**
   2026-06-23 (`Induction/Operations.lean`, `ChainData.candidateEnds` / `candidateSeed` + their `rfl` `@[simp]`
   `_apply` lemmas, axiom-clean). The two `def`s mirror `chainData_bottom_relabel`'s target framework
   verbatim (`candidateEnds i ends₀ = ρ.symm ∘ ends₀ ∘ σ`, `candidateSeed i q = q ∘ ρ` on the body
   coordinate, `(ρ, σ) = (shiftPerm i.castSucc, shiftEdgePerm i)`), so LEAF-4 can chain them; `candidateSeed`
   is generic in the fibre type `γ`, carrying no `ScrewSpace`/`k` dependency. **NOT in LEAF-1** (these depend
   on the discriminator's `n'` / the split-realization general-position context, so they are LEAF-3/LEAF-4
   plumbing, built inline at the dispatch like the d=3 `case_III_candidate_dispatch` /
   `chainData_split_realization` do): the override-selector facts `hends_ea/eb` (`Function.update` of
   `candidateEnds` at the two re-inserted hinges, `Realization.lean:444`/`1067` pattern), `hends_Gv`/`hne_Gv`
   (off-slot link-recording + general-position support nonvanishing, verbatim from
   `chainData_split_realization:1079–1092`), `hVone`/`hVcard` (the `removeVertex` ncard rewrites), `hLn`/`hgab`
   (the seed pairwise-LI + transversal-LI from the split realization's `IsGeneralPosition`).
3. **LEAF-3 (BLOCKED — frozen-contract decision, design §I.8.24(4.11))** — fire `chainData_split_w6b_gates`
   (→ `ρ₀`/`w`) + `exists_chainData_discriminator_pick` ONCE off the shared base; expose `hgate`/`hρe₀` at
   the matched interior candidate `i`. The panel-`u : Fin (k+1)`↔candidate-`i : Fin cd.d` match is NOT `Fin`
   arithmetic — it needs `cd.d = k+1` (KT-structural; the discriminator is `Fin (k+1)`-indexed, `cd.d` is a
   free `ℕ`). **Coordinator/user must adjudicate the contract change (recommended (a): add `d_eq : cd.d = k+1`
   to `ChainData`/dispatch) before LEAF-3 can land.** Once decided, the wiring is the d=3 template
   `case_III_candidate_dispatch:435–501` + `chainData_split_realization`'s `htrans` slot, re-aimed at the
   assembly's `hgate`/`hρe₀`.
4. **LEAF-4 (THE HARD CORE)** — the interior base-block `W` production: `f := w`, `L := (funLeft (shiftPerm
   i.castSucc)⁻¹).dualMap`, `hS` = the per-member case-split over `hwmem` (genuine → off-slot GROUP leaf
   `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` + row-routing bridge; block-tag → reproduced-slot
   membership) routing `chainData_bottom_relabel`'s images into `caseIIICandidate.rigidityRows`, `hvanish` =
   base-rows-over-old-bodies; apply LEAF-2; `exact case_III_arm_corner_assembly …`. THE §(4.4)(β) flag made
   concrete; the composer the last two dispatches scoped AWAY from.
5. **LEAF-5 (MODERATE)** — `chainData_dispatch` proper: the router. CASE on candidate `i`: base `i=1` + d=3
   floor → `chainData_split_realization` (zero-regression); interior `2 ≤ i < d` → LEAF-4. Latitude: the
   routing predicate + the C.4 `d=3` zero-regression adapter.
6. **CHAIN-5** — wire `chainData_dispatch` into `case_III_realization_all_k`'s `hdispatch` via the C.4 4-tuple
   adapter → orphan confirm-and-delete (the `hφ`-spine; LEAF 1–4 STAYS). **Cost band ~5–7 commits** (the
   decomposition refined the prior ~3–5 by isolating the threading leaf + the hard-core composer). Audit:
   design §(o‴)(I.8.24)(4)/(4.9)/(4.10).

**`d=3` floor / interior routing.** The dispatch's two arm routes are both landed; interior `2 ≤ i < d` →
`case_III_arm_corner_assembly` (NO `hρGv`); the d=3 floor (`i=2`) + base candidate `i=1` → the landed engine
via `chainData_split_realization` (zero-regression, C.4). The split-tuple/count facts are the LANDED
`ChainData` accessors (`Operations.lean:1392–1462`: the `removeVertex` memberships + `castSucc_ne_*` +
`isLink_*` + `isLink_eq_succ_or_pred_or_removeVertex`). The panel rows + `±r` corner are ASSEMBLED inside
`case_III_arm_corner_assembly` (the dispatch no longer builds `g`/`hg`/`hLI`).

**Phase boundary — close 23c at CHAIN-5, open 23d = ENTRY.** Discharging `hdispatch` completes the CHAIN
layer end-to-end for general `d`, which is exactly 23c's titled scope (the redundancy-carry re-architecture
+ chain-dispatch completion). On that commit run the phase-close checklist (`PHASE-BOUNDARIES.md` *When this
commit closes a phase*) — including archiving 23c's `model-experiment.md` rows + *Findings* to the archive —
and **mint 23d = ENTRY** (the next stable code; `notes/Phase23d.md`, no umbrella note): reshape
`Graph.exists_chain_data_of_noRigid` (`Reduction.lean:383`) into the `G.ChainData n` producer
`exists_chainData_of_noRigid` (KT Lemma 4.6 chain + 4.8 split-off, general `d`; lift the `6 ≤ bodyBarDim n`
floor; resolve the OD-1 chain/cycle dichotomy) — item 4 of *Remaining work in Phase 23* above. The
CHAIN↔ENTRY `ChainData` contract (C.0–C.6) is **frozen**, so 23d opens against a settled interface; ASSEMBLY
follows as 23e. Do **not** fold ENTRY into 23c — it is a distinct layer (KT §4) with its own recon.

## Decisions made during this phase

### Promoted to DESIGN / ledger / Findings (cross-cutting lessons from this phase)
- *A conditional leaf is progress only if its hypothesis is dischargeable for the **actual consumer** — a
  satisfiability check, not just signature/decl-existence (the project-side root cause of the two
  mis-targeted `±r`-row leaves)* → `DESIGN.md` *Constructibility recon …* (the satisfiability corollary).
- *Where KT's "member moves" (6.62) lands: the redundant `±r` row on the candidate's reproduced hinge slot,
  the graph-endpoints-vs-overridden-support decoupling* → `notes/BlueprintExposition.md` (`lem:case-III general-d`).
- *A diverse-lens recon PAIR (constructive + adversarial-refute) resolves a recurring-mis-pin design seam
  where single reads fail* → model-exp *Findings* 2026-06-22.

### Landed-leaf ledger — one-line verdicts

*Full prose audit in git history + design §(o‴)(I.8.18)–(I.8.24); the live inventory the next dispatch
needs is in* Current state *above (`Landed (all axiom-clean)…`). All landed leaves are axiom-clean
(`propext`/`Classical.choice`/`Quot.sound`), build/lint warning-clean. Compressed at 2026-06-22 per
`notes/CLAUDE.md` *Forward-weighted note* (settled per-leaf landing prose → verdicts).*

- **Architecture (2026-06-21, §I.8.18–I.8.24).** Opened at a clean-break 23b close; the `hρGv` member-mapping
  wall is **intrinsic to KT** (§I.8.18–I.8.20), so option **(A)** re-shapes the rank cert to KT's `±r`/`Mᵢ`-block
  form, escaping it. §I.8.21 (A)-feasibility; §I.8.22 (2b)(β) + §I.8.23 (2b)(γ) de-risks **POSITIVE**; §I.8.24
  cert-re-shape verdict = **(A) escapes the wall** (the §I.8.22-vs-§I.8.23 tension reconciles: the cert is
  selector-agnostic, the wall was only the collapsed-`Unit`-row `hρGv` sourcing). `d=3` keeps the landed engine,
  zero-regression. The four dead route families stay exhausted — **do NOT re-attempt** (see *Orientation* top).
- **Cert + tail + carrier (§I.8.24(1)/(3)).** `case_III_rank_certification_chain` (NO `hρGv`, selector-agnostic,
  block-rank shape); SHARED tail `case_III_realization_of_rank` (factored from `case_III_arm_realization`,
  `hrank`-parametric, d=3 engine delegates, zero-regression); block-rank-additivity
  `Submodule.finrank_add_card_le_of_linearIndependent_mkQ` + carrier `finrank_span_rigidityRows_ge_of_corner`;
  W-packaging `exists_le_finrank_span_rigidityRows_eq_card_of_injective_map` +
  `Submodule.exists_le_finrank_eq_card_of_injective_map`.
- **`hLI` (§I.8.24(3)/(4.1)/(4.3)).** Abstract halves `Submodule.linearIndependent_mkQ_of_comp` +
  `linearIndependent_mkQ_sumElim_unit_of_notMem_span`; carrier `linearIndependent_mkQ_panelRow_of_edge`; the (b)
  crux `notMem_span_mkQ_pmR_row_of_gate` (KT (6.65), the one genuinely-new leaf); corner assembly
  `linearIndependent_mkQ_corner_of_gate`.
- **(α) column transport (§I.8.24(4.5)(α)).** Bridge `funLeft_dualMap_comp_single` + application
  `funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy` (candidate `hrCol = −ρ₀` at `vtx(i-1)`,
  composing the 23b base value `interior_group_acolumn_eq_neg_baseRedundancy`, KT (6.66)).
- **Row-routing bridge (§I.8.24(4.6)).** `hingeRow_mem_rigidityRows_of_supportExtensor_eq` (framework-general) +
  `hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link` (the caseIIICandidate↔ofNormals seam, via
  `caseIIICandidate_supportExtensor_of_ne`). Pre-arm corrections (§I.8.24(4.6)): the chain arm goes in
  the `Relabel/` chain (now `Relabel/ForkedArm.lean`, not `Arms.lean`) and CONSTRUCTS its `caseIIICandidate` — not a thin instantiation.
- **±r-row sourcing RESOLVED (2026-06-22, §I.8.24(4.9)).** The DIRECT genuine reproduced-slot `e_b`-row grounds
  BOTH `hg` (`hingeRow_mem_caseIIICandidate_rigidityRows_reproduced`, `hperp = hρe₀`, the M₃ `hvb_row :2866`
  mechanism, NEVER `hρGv`) and `hrCol` (`reproducedSlot_pmR_acolumn_eq`, `= −ρ₀` via `hingeRow_swap` +
  `hingeRow_comp_single_tail`) via the **graph-endpoints-vs-overridden-support decoupling**
  (`caseIIICandidate.graph = G` keeps the genuine link, overrides only the support panel). Adjudicated by a
  diverse-lens recon pair + source verification, then built clean; the (4.8) two-object mismatch is gone (the
  relabel-image / filtered-group attempts landed on the fresh pair, which OMITS `vᵢ`, reading `0`).
- **Arm + assembly (§I.8.24(4)/(4.9)).** Arm spine `case_III_arm_realization_chain` (cert→tail wiring, corner
  data `(W,hWS,hWcard,ι,hιcard,g,hg,hLI)` + count facts as hypotheses); corner-data ASSEMBLY producer
  `case_III_arm_corner_assembly` (constructs `g = Sum.elim (D−1 `e_a`-panel rows via
  `exists_independent_panelRow_subfamily_of_edge` + `panelRow_mem_rigidityRows_of_link`) (±r row)` over
  `ι = ↥s ⊕ Unit` at `F₀`; takes the dispatch's raw `hgate`/`hρe₀` + `W`/`hWS`/`hWcard`/`hW` as hyps). The seam
  closes end-to-end in Lean.
- **Superseded / deleted.** Mis-targeted reproduced-slot GROUP leaf
  `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate_reproduced` (`b675317`) **DELETED** (unsatisfiable
  `hcollapse`; stated over `G−vᵢ` not full `G`; grep-confirmed consumed nowhere). The off-slot GROUP leaf
  `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` is **KEPT** (serves the genuine off-slot `hWS` family).
  NOT the `±r` sourcing (revive only if a later dispatch needs them): the base-side `hrCol` leaf
  `funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy` (reads `vtx(i-1)`), T-2
  `chainData_candidateRow_edgeGrouped_transport_comb`.
- **`Relabel/` split (2026-06-23).** The over-cap `CaseIII/Relabel.lean` (5066 lines, 3.4× the ~1500
  soft cap) → a 5-file `CaseIII/Relabel/` subdirectory (`Basic`/`Chain`/`Arm`/`ChainColumn`/`ForkedArm`,
  each importing its predecessor; cut along the file's own `##`/`###` section headers). Pure
  mechanical, semantics-preserving — Lean forbids forward intra-file references, so every decl
  boundary is a valid cut; no decl renamed (blueprint `\lean{}` pins / `checkdecls` unaffected), the
  three terminal decls (`case_III_arm_realization_M3`/`_chain`/`_corner_assembly`) re-verified
  axiom-clean. The sole importer `CaseIII/Realization` switched `import …CaseIII.Relabel` → `…Relabel.ForkedArm`;
  three stale `Relabel.lean` file-path doc pointers in `Induction/Operations.lean` repointed. Done
  before the dispatch build so it can grow chain-arm machinery without re-tripping the cap.
- **Dispatch interior-split accessors (2026-06-23).** Six new `ChainData` accessors in
  `Induction/Operations.lean` packaging the interior split tuple `(v,a,b,e_a,e_b) = (vtx i.castSucc,
  vtx i.succ, vtx (i−1).castSucc, edge i, edge (i−1))` over `Gv = G − v` in the arm shape: the two
  distinctnesses `castSucc_ne_succ`/`castSucc_ne_pred_castSucc` (`v≠a`/`v≠b`, off `vtx_ne`), the three
  `Gv`-membership facts `{notMem_,succ_mem_,pred_castSucc_mem_}vertexSet_removeVertex_castSucc`
  (`hvVc`/`haVc`/`hbVc`, off `vtx_mem` + `Graph.vertexSet_removeVertex`), and the edge partition
  `isLink_eq_succ_or_pred_or_removeVertex` (`hsplitG` = every `G`-edge is `edge i` / `edge (i−1)` /
  a `Gv`-link, off `deg_two_split`, the d=3 dispatch's `hsplitG` generalized). The split-tuple half of
  CHAIN-2c-iii's inputs; the dispatch's remaining work is the discriminator + base-block construction
  + arm routing.
- **Dispatch LEAF-2: the concrete-`W` carrier (2026-06-23).**
  `BodyHingeFramework.span_relabelImage_le_and_finrank_and_acolumn_vanish` (`Candidate.lean`, after the
  existential leaf, axiom-clean). The concrete-`W` variant of
  `exists_le_finrank_span_rigidityRows_eq_card_of_injective_map`: fixes `L = (funLeft σ).dualMap`, returns
  `W = span (range (L ∘ f))` with the third corner datum `hW : ∀ φ ∈ W, φ ∘ₗ single v = 0`. `hWS`/`hWcard`
  reuse the existential body; `hW` is the new content — a `span_induction` routing each generator through
  the (α) bridge `funLeft_dualMap_comp_single` + `hvanish` at `σ.symm v` (the column-index direction FORCED
  by the bridge, (4.8)-class trap). Resolves the `W`/`hW` threading decision (return-shape mismatch, not a
  motive change); unblocks LEAF-4's `hW`.
- **Dispatch LEAF-1: the interior-candidate relabel-image selector/seed (2026-06-23).** Two `ChainData`
  accessors in `Induction/Operations.lean` (beside the sibling interior-split accessors): `candidateEnds i
  ends₀ = fun e => (ρ.symm (ends₀ (σ e)).1, ρ.symm (ends₀ (σ e)).2)` and `candidateSeed i q = fun p => q (ρ
  p.1, p.2)`, `(ρ, σ) = (shiftPerm i.castSucc, shiftEdgePerm i)`, each with a `rfl` `@[simp]` `_apply` lemma.
  They are `chainData_bottom_relabel`'s target framework named as `def`s, so LEAF-4's `hS` case-split routes
  its image rows into them by `rfl`. `candidateSeed` is generic in the fibre type `γ` (no `ScrewSpace`/`k`
  dep, so it lives upstream in `Induction/`); the unused `[DecidableEq β]` on its `_apply` lemma is dropped
  with `omit … in`. Pure bookkeeping, no new math; the override (`hends_ea/eb`) + general-position
  (`hLn`/`hgab`/`hne_Gv`) facts depend on LEAF-3's `n'`/split-realization context and are built inline there.
