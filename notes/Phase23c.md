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

> **Orientation for the next agent.** The (A) architecture is built end-to-end through the arm + corner-data
> assembly (`case_III_arm_realization_chain` + `case_III_arm_corner_assembly`, both LANDED; the `±r`-row seam
> stays CLOSED). The general-`d` dispatch **CHAIN-2c-iii `chainData_dispatch` is DECOMPOSED into 5 ranked
> leaves** (design §I.8.24(4.10)). LANDED so far: the `Relabel/` 5-file split; LEAF-1 (interior-candidate
> framework defs `candidateEnds`/`candidateSeed`); LEAF-2 (concrete-`W` carrier
> `span_relabelImage_le_and_finrank_and_acolumn_vanish`); the **option-(a) contract field `d_eq : d = n`** on
> the `ChainData` record + its `cd.d = k+1` bridge `d_eq_kAdd` — which CLOSES the frozen-contract
> discriminator-index gap (KT-structural `d = k+1`; see *Decisions made* + DESIGN.md *Frozen contracts must
> encode the invariants relating their parameters*); the selector `candidateVtx` + `candidateVtx_injective`;
> the panel↔candidate match `candidateVtx_succ_eq` (`candidateVtx i = vtx i.succ` at interior `i`); and the
> composed `Fin (k+1)` panel selector `candidatePanel` + `candidatePanel_injective` + `candidatePanel_apply`
> (`Realization.lean` — the `cand`/`hcand` input the discriminator takes directly). **So the
> discriminator-index plumbing is COMPLETE end-to-end (record-local AND the `Fin (k+1)`-composed `cand`).**
>
> **The `hgate`/`hρe₀` sourcing is RESOLVED (design §I.8.24(4.12), source-verified 2026-06-23) and SPLITS
> across LEAF-3 and LEAF-4 — the (4.10) sketch that put the interior `hρe₀` inside LEAF-3 was wrong.**
> `hgate` is LANDED-and-direct (`exists_chainData_discriminator_pick` returns it at `cand u = vtx i.succ` via
> `candidateVtx_succ_eq`; the only gate-side bookkeeping is the base-vs-`candidateSeed` `shiftPerm`-image
> reconciliation, buildable). **The matched-INTERIOR `hρe₀` at the SHARED base `ρ₀` is a GENUINELY-NEW leaf**
> — KT eq-6.66 (the second-`Mᵢ`-row-is-`±r` fact), NOT a transport of the base annihilation and NOT a
> per-candidate W6b firing (the interior split's IH-generic realization is NOT in the dispatch's scope —
> only the BASE `v₁`-split's is, `Arms.lean:910–913`; per-interior W6b is the §(o″) Route-A dead end).
> **It is machinery BELOW the contract (the cert is `hρGv`-free + `ρ₀`-agnostic) → NOT BLOCKED**, but it is
> THE conjecture-crux leaf (the §I.8.3-P2 heir, the redundancy-carry seam) the next steps must NOT scope
> away from. **Next commits:** (LEAF-3, now that `candidatePanel`/`candidatePanel_injective` give the
> `cand`/`hcand` input) fire `chainData_split_w6b_gates` + the discriminator at the **BASE split** ONCE
> (fed `candidatePanel hn`) → shared `ρ₀`, base `(v₀v₂)` annihilation, matched `i`/`hgate`/`n'`, W6b base
> bundle; then
> (LEAF-4 / standalone) the genuinely-new `baseRedundancy_perp_interior_reproduced_panel` to GET the interior
> `hρe₀`, build `W`, `exact case_III_arm_corner_assembly`; then LEAF-5 (router) → CHAIN-5. **Do NOT**
> re-attempt the four dead route families (§I.8.18–(I.8.20)), re-litigate the fork, revive the relabel-image
> `±r` route, or source the interior `hρe₀` by firing W6b at the interior split (unsatisfiable `hsplitGP`).
> See *Current state* + *Hand-off* + design §I.8.24(4.12).

## Current state

**The discriminator-index plumbing is COMPLETE end-to-end (2026-06-23).** The last piece — the
composed `Fin (k+1)` panel selector `Graph.ChainData.candidatePanel` + `candidatePanel_injective` +
`candidatePanel_apply` (`CaseIII/Realization.lean`, after `d_eq_kAdd`; build/lint/axiom-clean,
warning-clean) — is the actual `cand : Fin (k+1) → α` / `hcand` input the Claim-6.12 panel
discriminator `exists_chainData_discriminator_pick` takes:
`candidatePanel cd hn := candidateVtx ∘ Fin.cast (cd.d_eq_kAdd hn).symm`, `_injective` =
`candidateVtx_injective.comp (Fin.cast_injective _)`, `_apply` = the `rfl` unfold to
`candidateVtx (Fin.cast … u)`. Full plumbing inventory + the §56-trap `_root_.…` note in *Decisions
made* (the "Dispatch discriminator-index plumbing" bullet). So the discriminator's `u : Fin (k+1)`
maps to the chain candidate `i := Fin.cast (cd.d_eq_kAdd hn).symm u : Fin cd.d`, and
`candidatePanel_apply` + `candidateVtx_succ_eq` (interior) / `candidateVtx_zero` (base) turn the gate
at `candidatePanel hn u` into the arm's gate at `vtx i.succ`.

**NEXT: the discriminator-firing producer (LEAF-3 proper) — but it produces ONLY `(matched i, ρ₀, hgate,
n', base bundle)`, NOT the interior `hρe₀` (design §I.8.24(4.12)).** Now that the composed `cand`/`hcand`
input is landed (`candidatePanel hn` + `candidatePanel_injective hn`), fire `chainData_split_w6b_gates`
(→ `ρ₀`/`w`/base `(v₀v₂)` annihilation + the eq-6.52 `λ`-grouped `(ab)`-witness) +
`exists_chainData_discriminator_pick` (fed `candidatePanel hn` for `cand`, `candidatePanel_injective hn`
for `hcand`) ONCE at the **BASE split**, split on the matched `i := Fin.cast (cd.d_eq_kAdd hn).symm u`
(interior `0 < i` → `candidatePanel_apply` + `candidateVtx_succ_eq`; base `i = 0` → d=3-floor route via
`chainData_split_realization`, where the interior `hρe₀` leaf is NOT needed). **`hgate` lands directly**
at `candidatePanel hn u = vtx i.succ` (gate-side caveat: the discriminator runs against the BASE seed
`q`, the consumer uses `candidateSeed i q`, so a `shiftPerm`-image seed reconciliation is needed —
buildable bookkeeping on the LANDED `candidateSeed`/`shiftPerm` simp set, not a wall). **The
matched-INTERIOR `hρe₀` is a GENUINELY-NEW leaf** `baseRedundancy_perp_interior_reproduced_panel`
(KT eq-6.66; the SHARED base `ρ₀` annihilates the interior `(vtx i.succ, vtx (i−1).castSucc)`
reproduced-slot panel), produced in **LEAF-4** from LEAF-3's base `ρ₀`/`λ`-witness bundle + `cd.deg_two`
— NOT here, and NOT by a per-interior W6b firing (`hsplitGP` unavailable for interior splits; only the
base `v₁`-split's IH realization is in scope, `Arms.lean:910–913`). Both `candidatePanel` and
`d_eq_kAdd` stay declared `_root_.Graph.ChainData.…` (the TACTICS-QUIRKS § 56 trap — a bare
`Graph.`-prefixed decl inside `namespace …Molecular` would create a `…Molecular.Graph` sub-namespace
that breaks downstream `V(·)`/`E(·)` parsing).

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
fibre type `γ` so it carries no `ScrewSpace`/`k` dependency. **The LEAF-3 frozen-contract field is LANDED**
(2026-06-23, build/lint/axiom-clean): the `d_eq : d = n` field on the `ChainData` RECORD
(`Induction/Operations.lean`, right after `hd`) — option (a), the discriminator-index gap resolution. Stated
`d = n` (the record parameter), **not** `d = k+1` (`k` is not a record parameter); `n = k+1` is recovered at
use sites from the ambient `bodyBarDim n = screwDim k` (`Nat.choose`-injectivity). Purely additive — there are
**no** `ChainData` value constructions yet (`exists_chain_data_of_noRigid` still returns the OLD fixed 4-tuple,
a 23d/ENTRY obligation), so nothing to fix downstream; full project green. The ENTRY extractor will *set*
`d_eq` at construction (KT Lemma 4.6 builds the chain to length `n` — set, not proved-after-the-fact). **LEAF-3
proper now unblocks**: fire `chainData_split_w6b_gates` + `exists_chainData_discriminator_pick` off the shared
base; the panel-`u : Fin (k+1)` ↔ candidate-`i : Fin cd.d` match transports across `d_eq` + `n = k+1`. Then
LEAF-4 (hard core, the `hS` disjunction) → LEAF-5 (router) → CHAIN-5 proceed as pinned. Home for the dispatch:
a fresh `Relabel/Dispatch.lean` importing `Relabel/ForkedArm`; the `Relabel/` split is DONE so it lands without
re-tripping the cap.

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
   routes interior `2 ≤ i < d` through the chain arm, d=3 floor on the landed engine). **Includes the
   GENUINELY-NEW interior-`hρe₀` leaf `baseRedundancy_perp_interior_reproduced_panel` (KT eq-6.66, the
   conjecture-crux redundancy-carry seam; LEAF-4, not LEAF-3 — design §I.8.24(4.12)); NOT BLOCKED but the
   hard core the dispatch build must not scope away from.**
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

**The contract field `d_eq : d = n` is LANDED** (option a; 2026-06-23, build/lint/axiom-clean; added to the
`ChainData` RECORD in `Operations.lean`, right after `hd`). Stated `d = n` (the record parameter), **not**
`d = k+1` (`k` is not a record parameter — `n = k+1` follows at use sites from the ambient
`hn : bodyBarDim n = screwDim k`, a `Nat.choose`-injectivity step). It is a **constructive RECORD field** (set
at construction by the ENTRY extractor — KT Lemma 4.6 builds the chain to length `n`, so `d_eq` is *set, not
proved-after-the-fact*; sidesteps the satisfiability trap). Purely additive — there are **no** `ChainData` value
constructions yet (`exists_chain_data_of_noRigid` still returns the OLD fixed 4-tuple, a 23d/ENTRY obligation),
so no construction site needed fixing; full project green.

**The `cd.d = k + 1` bridge `Graph.ChainData.d_eq_kAdd` is LANDED** (the `d_eq`-companion that converts
the record field `d_eq : d = n` into the `Fin (k+1)`-vs-`Fin cd.d` index identity, via `n = k+1` from
`hn`; `CaseIII/Realization.lean`, axiom-clean). **The LEAF-3 candidate selector `candidateVtx`
(`Fin cd.d → α`) + `candidateVtx_injective` are LANDED** (`Induction/Operations.lean`, axiom-clean): the
panel→vertex map (`Π₀ = Π(v₀)`, `Πᵢ = Π(v_{i+1})`, eq. 6.67) named record-locally + proved injective,
the `Function.Injective cand` half of the discriminator's `cand : Fin (k+1) → α` input. **The composed
`Fin (k+1)` panel selector `Graph.ChainData.candidatePanel` (+ `candidatePanel_injective` +
`candidatePanel_apply`) is LANDED** (`CaseIII/Realization.lean`, right after `d_eq_kAdd`, axiom-clean):
`candidatePanel cd hn := candidateVtx ∘ Fin.cast (cd.d_eq_kAdd hn).symm`, the actual `cand : Fin (k+1) → α`
the discriminator takes, with `candidatePanel_injective` the `hcand` half and `candidatePanel_apply` the
`rfl` unfold to `candidateVtx (Fin.cast … u)`. So the §I.8.24(4.11) discriminator-index gap is now closed
end-to-end (field + bridge + record-local selector + the composed `cand`/`hcand`).
**NEXT COMMIT: LEAF-3 proper, which produces `(matched i, ρ₀, hgate, n', base bundle)` — NOT the interior
`hρe₀` (design §I.8.24(4.12), source-verified 2026-06-23; the prior "expose `hgate`/`hρe₀` together here"
was wrong).** Feed `candidatePanel hn` for `cand` and `candidatePanel_injective hn` for the discriminator's
`hcand`, fire `chainData_split_w6b_gates` (→ shared `ρ₀`/`w` +
the base `(v₀v₂)` annihilation) + `exists_chainData_discriminator_pick` ONCE at the **BASE split**; get
`hgate` at the matched candidate `candidatePanel hn u = vtx i.succ` (the panel-`u : Fin (k+1)` ↔
candidate-`i : Fin cd.d` match via `candidatePanel_apply` + `candidateVtx_succ_eq`). Wiring template: the d=3 `case_III_candidate_dispatch:435–501`
+ `chainData_split_realization`'s `htrans` slot. **Gate-side caveat:** the discriminator runs against the
BASE seed `q`; the consumer `case_III_arm_corner_assembly` uses `candidateSeed i q` — a `shiftPerm`-image seed
reconciliation is needed (buildable bookkeeping on the LANDED `candidateSeed`/`shiftPerm` simp set, the
(4.11) "member-fixed extensor-relabelled" shape, NOT the wall). **THEN** LEAF-4 produces the
GENUINELY-NEW interior `hρe₀` leaf `baseRedundancy_perp_interior_reproduced_panel` (KT eq-6.66: the shared
base `ρ₀` ⊥ the interior `(vtx i.succ, vtx (i−1).castSucc)` reproduced-slot panel) from LEAF-3's base
`ρ₀`/`λ`-witness bundle + `cd.deg_two`, builds `W`, `exact case_III_arm_corner_assembly` → LEAF-5 (router)
→ CHAIN-5. **Watch the two downstream risks** (design §I.8.24(4.11)/(4.12)): the ENTRY KT-4.6
chain-extraction leaf (23d, genuinely-new), and — the conjecture-crux — the interior-`hρe₀` leaf itself
(the §I.8.3-P2 heir, the redundancy-carry seam; NOT BLOCKED, but THE hard core of LEAF-4, do NOT scope
away from it, and do NOT try to source it by firing W6b at the interior split — `hsplitGP` unavailable).
**Route-verification flag (coordinator, 2026-06-23):** the recon's INGREDIENT pin for the interior-`hρe₀`
leaf cited `redundancy_panel_carry` as "LANDED" — it is NOT (landed row 268, DELETED as an orphan row 271:
`hcol`/`hrest` unsuppliable at the chain step, the §(o‴)-rejected 4×-mis-pin trap). The landed chain-carry is
`interior_group_eq_baseRedundancy` (+ the d=3 `candidateRow_ac_eq_neg`). The structural verdict stands
(source-verified), but the leaf's INTERNAL route is not yet independently verified — give the interior-`hρe₀`
leaf a DEDICATED route recon (likely a diverse-lens pair, this seam's track record) at the LEAF-4 boundary,
diffing the route against the §(o‴)/row-271 orphan verdict, BEFORE a build burns on it. Does NOT block the
LEAF-3 producer (it doesn't touch this route). See design §I.8.24(4.12) *COORDINATOR ROUTE-VERIFICATION FLAG*.

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
3. **The contract field `d_eq : d = n`** (option a, the discriminator-index gap fix). ✓ **LANDED** 2026-06-23
   (`Induction/Operations.lean`, the `ChainData` RECORD, right after `hd`; build/lint/axiom-clean). Purely
   additive — no `ChainData` value constructions exist yet, so nothing downstream to fix.
   **The `cd.d = k + 1` bridge `Graph.ChainData.d_eq_kAdd`** (the `d_eq`-companion that makes the field
   usable: `d_eq : d = n` + `hn : bodyBarDim n = screwDim k` ⟹ `cd.d = k + 1`). ✓ **LANDED** 2026-06-23
   (`CaseIII/Realization.lean`, before `chainData_split_realization`; build/lint/axiom-clean,
   warning-clean; declared `_root_.Graph.ChainData.d_eq_kAdd` to dodge the § 56 sub-namespace trap).
   **The LEAF-3 panel→vertex selector `candidateVtx` + `candidateVtx_injective`** (the `k`-free half of
   the discriminator's `cand : Fin (k+1) → α` input: the eq-6.67 panel→vertex map `Π₀=Π(v₀)`,
   `Πᵢ=Π(v_{i+1})`, named record-locally + proved injective). ✓ **LANDED** 2026-06-23
   (`Induction/Operations.lean`, after `candidateSeed`; build/lint/axiom-clean, warning-clean). The
   `Fin (k+1)` transport happens via `candidatePanel`, below.
   **The LEAF-3 panel↔candidate match `candidateVtx_succ_eq`** (`candidateVtx i = vtx i.succ` at
   interior `0 < i`, the `rfl`-level `Fin` bridge routing the discriminator's panel `u` to the chain
   arm's successor neighbour). ✓ **LANDED** 2026-06-23 (`Induction/Operations.lean`, after
   `candidateVtx_injective`; build/lint/axiom-clean, warning-clean; `candidateVtx_succ` + `Fin.succ_mk`,
   not `@[simp]`).
   **The composed `Fin (k+1)` panel selector `candidatePanel` + `candidatePanel_injective` +
   `candidatePanel_apply`** (`candidatePanel cd hn := candidateVtx ∘ Fin.cast (cd.d_eq_kAdd hn).symm`,
   the actual `cand`/`hcand` input the discriminator takes; `candidatePanel_apply` the `rfl` unfold to
   `candidateVtx (Fin.cast … u)`). ✓ **LANDED** 2026-06-23 (`CaseIII/Realization.lean`, right after
   `d_eq_kAdd`; build/lint/axiom-clean, warning-clean; `_root_.Graph.ChainData.…` for the §56 trap;
   `candidatePanel_apply` not `@[simp]`). So the **discriminator-index plumbing is now COMPLETE
   end-to-end** (field `d_eq` + bridge `d_eq_kAdd` + record-local selector
   `candidateVtx`/`candidateVtx_injective` + match `candidateVtx_succ_eq` + composed
   `candidatePanel`/`candidatePanel_injective`).
   **The discriminator-firing producer (NEXT) — produces `(matched i, ρ₀, hgate, n', base bundle)`, NOT
   the interior `hρe₀` (design §I.8.24(4.12)).** Feed `candidatePanel hn` for `cand`,
   `candidatePanel_injective hn` for `hcand`, fire `chainData_split_w6b_gates`
   (→ shared `ρ₀`/`w` + base `(v₀v₂)` annihilation + the eq-6.52 `λ`-grouped `(ab)`-witness) +
   `exists_chainData_discriminator_pick` ONCE at the **BASE split**; split on the matched
   `i := Fin.cast (cd.d_eq_kAdd hn).symm u` (interior `0 < i` → `candidatePanel_apply` +
   `candidateVtx_succ_eq` turn the gate at `candidatePanel hn u` into the gate at `vtx i.succ`; base
   `i=0` → the d=3-floor / base route via `candidateVtx_zero` + `chainData_split_realization`, where the
   interior `hρe₀` leaf is NOT needed). Expose `hgate` at the
   matched candidate `i`; **the gate-side caveat is the base-`q`-vs-`candidateSeed` `shiftPerm`-image
   reconciliation** (buildable). Wiring template: the d=3 `case_III_candidate_dispatch:435–501` +
   `chainData_split_realization`'s `htrans` slot, re-aimed at the assembly's `hgate`.
4. **LEAF-4 (THE HARD CORE)** — TWO genuinely-new pieces, do NOT peel one and defer the other:
   (i) **the interior-`hρe₀` leaf** `baseRedundancy_perp_interior_reproduced_panel` (KT eq-6.66, the
   conjecture-crux redundancy-carry seam; the §I.8.3-P2 heir): from LEAF-3's base `ρ₀`/`λ`-witness bundle +
   `cd.deg_two`, prove the shared base `ρ₀` annihilates the interior `(vtx i.succ, vtx (i−1).castSucc)`
   reproduced-slot panel — the bridge from the LANDED `candidateRow_ac_eq_neg`/`interior_group_*` chain-carry
   to the `ρ₀ (panelSupportExtensor …) = 0` panel-annihilation shape; NOT a transport of base `hρe₀`, NOT a
   per-interior W6b firing (`hsplitGP` unavailable). (ii) **the base block `W`**: `f := w`,
   `L := (funLeft (shiftPerm i.castSucc)⁻¹).dualMap`, `hS` = the per-member case-split over `hwmem`
   (genuine → off-slot GROUP leaf `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` + row-routing bridge;
   block-tag → reproduced-slot membership) routing `chainData_bottom_relabel`'s images into
   `caseIIICandidate.rigidityRows`, `hvanish` = base-rows-over-old-bodies; apply LEAF-2. Then `exact
   case_III_arm_corner_assembly … hgate hρe₀ hWS hWcard hW hdef`. THE §(4.4)(β) flag + the §I.8.24(4.12)
   crux made concrete; the composer the last two dispatches scoped AWAY from.
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
  accessors `candidateEnds`/`candidateSeed` (`Induction/Operations.lean`, beside the interior-split
  accessors) = `chainData_bottom_relabel`'s target framework named as `def`s (`(ρ,σ) = (shiftPerm
  i.castSucc, shiftEdgePerm i)`), each with a `rfl` `@[simp]` `_apply`; `candidateSeed` generic in the
  fibre `γ` (no `ScrewSpace`/`k` dep). So LEAF-4's `hS` routes its image rows into them by `rfl`. Pure
  bookkeeping. The override (`hends_ea/eb`) + general-position (`hLn`/`hgab`/`hne_Gv`) facts depend on
  LEAF-3's `n'`/split-realization context, built inline there.
- **Dispatch discriminator-index plumbing — option (a), COMPLETE end-to-end (2026-06-23, five
  axiom-clean adders closing §I.8.24(4.11)).** The `Fin (k+1)`-indexed discriminators vs the `i : Fin
  cd.d` chain candidate align only via `d = k+1` (KT §6.4.2-structural); these five pieces close it
  below the dispatch:
  - **field `d_eq : d = n`** on the `ChainData` RECORD (`Operations.lean`, after `hd`) — stated against
    the record parameter `n` (`k` not one; `n = k+1` recovered at use from `bodyBarDim n = screwDim k`);
    purely additive (no value constructions exist; ENTRY *sets* it from KT Lemma 4.6).
  - **bridge `Graph.ChainData.d_eq_kAdd`** (`CaseIII/Realization.lean`) — `d_eq` + `hn` ⟹ `cd.d = k+1`;
    pure `ℕ`-arith (clear the `/2` to `n(n+1)=(k+2)(k+1)`, `nlinarith`). Declared `_root_.…` to dodge
    the §56 sub-namespace trap (a bare `Graph.…` inside `namespace …Molecular` breaks `V(·)`/`E(·)`).
  - **selector `candidateVtx` + `candidateVtx_injective`** (`Operations.lean`) — the eq-6.67 panel→vertex
    map (`Π₀=Π(v₀)`, `Πᵢ=Π(v_{i+1})`) + the `Function.Injective cand` half; `k`-free.
  - **match `candidateVtx_succ_eq`** (`Operations.lean`, after `candidateVtx_injective`) — `candidateVtx i
    = vtx i.succ` at interior `0 < (i:ℕ)`, the `rfl`-level `Fin` bridge (`candidateVtx_succ`+`Fin.succ_mk`,
    not `@[simp]`) routing the discriminator's panel `u` to the chain arm's successor neighbour.
  - **composed selector `candidatePanel` + `candidatePanel_injective` + `candidatePanel_apply`**
    (`CaseIII/Realization.lean`, after `d_eq_kAdd`) — `candidatePanel cd hn := candidateVtx ∘
    Fin.cast (cd.d_eq_kAdd hn).symm`, the actual `cand : Fin (k+1) → α` the discriminator takes, with
    `_injective` (`candidateVtx_injective.comp (Fin.cast_injective _)`) the `hcand` half and `_apply`
    the `rfl` unfold to `candidateVtx (Fin.cast … u)`. `_root_.…` for the §56 trap; `_apply` not
    `@[simp]`. So gate at `candidatePanel hn u` ⟹ gate at `vtx i.succ` (interior, via `_apply` +
    `candidateVtx_succ_eq`) / `vtx 0` (base `i=0`, via `candidateVtx_zero`, floor route). NEXT = the
    discriminator-firing producer (fed `candidatePanel hn`/`candidatePanel_injective hn`).
- **`hgate`/`hρe₀` sourcing RESOLVED — design pass, NOT BLOCKED (2026-06-23, docs-only; design
  §I.8.24(4.12), source-verified against the LANDED bodies + KT eqs. 6.64–6.67).** `hgate` is LANDED-direct
  (`exists_chainData_discriminator_pick` at `cand u = vtx i.succ`; only the base-`q`-vs-`candidateSeed`
  `shiftPerm`-image reconciliation remains, buildable). The matched-INTERIOR `hρe₀` at the SHARED base `ρ₀`
  is a **GENUINELY-NEW leaf** `baseRedundancy_perp_interior_reproduced_panel` (KT eq-6.66) — NOT a transport
  of base `hρe₀`, NOT a per-interior W6b firing (interior `hsplitGP` not in scope; only the base `v₁`-split's
  is, `Arms.lean:910–913` — the §(o″) Route-A dead end). Machinery below the contract (cert `hρGv`-free +
  `ρ₀`-agnostic) so no motive/IH/C-change; but it is THE conjecture-crux (the §I.8.3-P2 heir). **Corrected
  LEAF-3/4 boundary:** LEAF-3 produces `(matched i, ρ₀, hgate, n', base bundle)`; the interior `hρe₀` lands
  in LEAF-4 — the (4.10) sketch that put it in LEAF-3 was wrong. The landed `interior_group_acolumn_eq_neg_
  baseRedundancy` is the near-miss but WRONG-SHAPE (a `−ρ₀` column value, not a panel annihilation).
