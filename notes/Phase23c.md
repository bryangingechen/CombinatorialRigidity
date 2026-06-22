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
column bridge + `hrCol` `funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy`, and the off-slot row
bridge `hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link` are all in tree (axiom-clean). Detail:
design §(o‴)(I.8.18)–(I.8.24); the *Decisions made* below.

**The reproduced-slot `±r`-row `hg` leaf LANDED (2026-06-21); the ONE open arm leaf is now the arm itself.**
The verified arm-build diagnosis (the off-slot GROUP leaf is mis-targeted for the `±r` row, §I.8.24(4.7)) is
discharged by the genuinely-new reproduced-slot leaf
`funLeft_dualMap_pmR_group_mem_span_caseIIICandidate_reproduced` (`Relabel.lean`, after the GROUP leaf;
axiom-clean): the `±r`-group's relabel image collapses to the reproduced-edge tag
`hingeRow (endsσρ e_r).1 (endsσρ e_r).2 ρ₀` at the candidate fresh pair, and that tag is a genuine
candidate rigidity row at the **reproduced slot `e_r`** because `ρ₀ ⊥ panelSupportExtensor (n_u + t•n') n_r`
(the dispatch's `hρe₀`, via `mem_hingeRowBlock_iff` + `caseIIICandidate_supportExtensor_reproduced`). It
takes the collapse (`hcollapse`) + the perp (`hperp`) + the candidate `e_r`-link (`hlink`) as hypotheses the
arm discharges — the cycle generalization of the M₃ arm's `:2756` length-1 mechanism.

> **Orientation for the next agent.** The architecture is settled (the `±r`-as-genuine-candidate-edge fork
> escapes the member-mapping wall; cert + carrier + abstract-LA + BOTH `hg` leaves [off-slot GROUP +
> reproduced-slot] all landed). **Do NOT** re-attempt the four dead route families (§(o‴)(I.8.18)–(I.8.20)) or
> re-litigate the fork. The next concrete commit is **`case_III_arm_realization_chain`** (`Relabel.lean`, NOT
> `Arms.lean` — import DAG; M₃ `:2638` is the construct-candidate + corner-data template): it constructs the
> `caseIIICandidate (G − vᵢ) endsσρ qρ e_c e_r …`, assembles the cert's corner data `(W, hWS, hWcard, g, hg,
> hLI)` from the landed leaves — `hg` for the `±r` row from the reproduced-slot leaf, for the off-slot bottom
> family from the GROUP leaf — and applies `case_III_rank_certification_chain` + `case_III_realization_of_rank`.
> Both `hg` leaves are kept: the off-slot GROUP leaf serves the genuine off-slot bottom-family members of the
> W-block, the reproduced-slot leaf serves the `±r` corner row. Build order + the cert's six slots in *Hand-off*.

## Current state

**(A) is OPEN; ALL the chain cert's corner-data infrastructure leaves are now in tree — the next leaf is
`case_III_arm_realization_chain` itself.** The member-mapping wall (KT carries a *moving* redundant row, eq.
(6.62)) is escaped by (A): the cert carries the redundancy as the abstract `±r` value, entering `g` as a
genuine candidate-edge member, **NO `hρGv` slot**. `d=3` keeps the landed engine verbatim. The four dead route
families (§I.8.18–(I.8.20)) are exhausted; **do not re-attempt.** Full audit: design §(o‴)(I.8.18)–(I.8.24).

**Landed (all axiom-clean):** the cert `case_III_rank_certification_chain`; carrier W-packaging
`exists_le_finrank_span_rigidityRows_eq_card_of_injective_map`; both `hLI` halves
(`linearIndependent_mkQ_panelRow_of_edge`, `notMem_span_mkQ_pmR_row_of_gate`) + assembly
`linearIndependent_mkQ_corner_of_gate`; the (α) column bridge `funLeft_dualMap_comp_single` + `hrCol`
`funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy`; the off-slot row bridge
`hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link`; the per-member genuine transport
`chainData_bottom_relabel`; the SHARED tail `case_III_realization_of_rank`; the off-slot GROUP leaf
`funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` (serves the W-block off-slot bottom family); and the
reproduced-slot `±r`-row leaf `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate_reproduced` (the `±r`
corner row's `hg`).

**Next: `case_III_arm_realization_chain` (the arm).** With both `hg` leaves landed, the arm's only remaining
content is the construct-candidate + corner-data wiring (M₃ `:2638` template; in `Relabel.lean`): build the
`caseIIICandidate`, assemble `(W, hWS, hWcard, g, hg, hLI)` from the landed leaves, apply the cert + the shared
tail. Build order + the six cert slots in *Hand-off*. Relabel.lean (now ~4830 lines, past the ~1500 tripwire)
likely forces a `Relabel/` split at the arm build — flag at that build.

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
   landed engine. **Cert + tail + carrier + both `hLI` halves + assembly + (α) bridge/`hrCol` + off-slot row
   bridge + `chainData_bottom_relabel` ✓ ALL LANDED** (2026-06-21, axiom-clean; names in *Current state*).
   **OPEN:** the `±r`-row `hg` member — the landed off-slot GROUP leaf is mis-targeted (it lands on the
   reproduced slot `e_r`, the wrap branch, VERIFIED). Next leaf + the arm: *Hand-off*.
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

**Both `hg` leaves landed; the next concrete commit is `case_III_arm_realization_chain` (the arm).** All of the
chain cert's corner-data infrastructure leaves are now in tree — the arm is the construct-candidate + corner-data
wiring (no remaining abstract-LA or genuinely-new-leaf sub-risk).

**Build order:**
1. **`case_III_arm_realization_chain`** (`Relabel.lean`, NOT `Arms.lean` — import DAG `Arms ⊂ Relabel ⊂
   Realization`, the arm consumes the chain-relabel leaves; M₃ `:2638` is the construct-candidate + corner-data
   template). The arm builds `caseIIICandidate (G−vᵢ) endsσρ qρ e_c e_r …`, assembles `(W,hWS,hWcard,g,hg,hLI)`,
   applies `case_III_rank_certification_chain` for `hrank`, then `exact case_III_realization_of_rank …`. The cert
   slots: **`hWS`/`hWcard`** ← carrier leaf `exists_le_finrank_span_rigidityRows_eq_card_of_injective_map` at
   `L = (funLeft (shiftPerm)⁻¹).dualMap`, `f` = the bottom family (a HYPOTHESIS the arm takes, ≡ engine's
   `w`/`hwcard`/`hw`), `hS` = `chainData_bottom_relabel`'s OFF-SLOT genuine members; **`hg`** for panel rows ←
   `panelRow_mem_rigidityRows`, for the off-slot bottom family ← the GROUP leaf
   `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate`, for the `±r` corner row ← the reproduced-slot leaf
   `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate_reproduced` (the arm supplies its `hcollapse` from A-1's
   `±r` identity + the wrap-branch relabel, `hperp` from the dispatch's `hρe₀`, `hlink` from the candidate
   `e_r`-link); **`hLI`** ← one-line `linearIndependent_mkQ_corner_of_gate` (`hrCol` = the landed
   `funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy = −ρ₀`, `hsupp`/`hgate`/`hW`/`hindep`
   arm-supplied). Relabel.lean is ~4830 lines (past the ~1500 tripwire) — the arm likely forces a `Relabel/`
   split; flag at build.
2. **Then:** 2c-iii `chainData_dispatch` (interior `2 ≤ i < d`, d=3 floor on the engine) → CHAIN-5 wire-up →
   orphan confirm-and-delete (the `hφ`-spine; LEAF 1–4 STAYS). **Cost band ~3–6 commits.** Audit:
   design §(o‴)(I.8.24)(4)/(4.7).

## Decisions made during this phase

- **Reproduced-slot `±r`-row `hg` leaf LANDED (2026-06-21) — the genuinely-new leaf the §I.8.24(4.7) arm-build
  diagnosis pinned; ALL chain-cert corner-data leaves now in tree.**
  `PanelHingeFramework.funLeft_dualMap_pmR_group_mem_span_caseIIICandidate_reproduced` (`Relabel.lean`, after the
  off-slot GROUP leaf): the `±r`-group's relabel image (`hcollapse` collapses it to the reproduced-edge tag
  `hingeRow (endsσρ e_r).1 (endsσρ e_r).2 ρ₀` at the candidate fresh pair) is a candidate rigidity row at the
  **reproduced slot `e_r`**, via `Submodule.subset_span ⟨e_r, …, ρ₀, …, rfl⟩` — the block membership reduces by
  `mem_hingeRowBlock_iff` + `caseIIICandidate_supportExtensor_reproduced` to `hperp` (the dispatch's `hρe₀`,
  `ρ₀ ⊥ panelSupportExtensor (n_u + t•n') n_r`), the `e_r`-link by `caseIIICandidate_graph` from `hlink`. The
  cycle generalization of the M₃ arm's `:2756` length-1 reproduced-slot mechanism. Takes `hcollapse`/`hperp`/
  `hlink` as hypotheses the arm discharges (NOT the off-slot `htransport`, unsatisfiable for the `±r`-group).
  Axiom-clean (`propext`/`Classical.choice`/`Quot.sound`), build/lint clean; no friction (a 5-line
  `rw`/`subset_span` mirroring `hingeRow_mem_rigidityRows_of_supportExtensor_eq` + the M₃ `hvb_row` pattern).
- **VERIFIED + RESOLVED: the off-slot GROUP leaf was mis-targeted for the `±r` row; the reproduced-slot leaf
  (above) is the correct `hg` (2026-06-21).** A-1's `±r`-group sits on the chain link `edge i`(`vᵢ—vᵢ₊₁`); its
  `(shiftPerm i.castSucc)⁻¹`-image endpoints are the candidate fresh pair `{vᵢ₋₁, vᵢ₊₁}` = the **reproduced slot
  `e_r`** (`chainData_bottom_relabel`'s `Or.inr` wrap branch), NOT an off-slot survivor — so the GROUP leaf's
  `htransport` is unsatisfiable for it. The GROUP leaf is KEPT (it serves the off-slot genuine bottom-family
  members of the `hWS` W-block); the `±r` corner row goes through the reproduced-slot leaf. Diagnosis trace in
  git (commit 2b22d59 + the landed leaf docstring).
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
