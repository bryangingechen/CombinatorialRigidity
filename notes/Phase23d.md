# Phase 23d — Case III general `d`: the CHAIN rank-certification reconsideration (work log)

**Status:** in progress (opened 2026-06-24 at a user-adjudicated clean-break close of 23c, at the
member-mapping-wall phase STOP). The integer **Phase 23 stays in progress**; 23d is the **third
CHAIN-layer sub-phase** (CHAIN spans 23b + 23c + 23d — the layer "split on contact", design §3).
ENTRY + ASSEMBLY remain later sub-phases (codes; the cross-phase plan + route history live in
`notes/Phase23-design.md`, program map `notes/MolecularConjecture.md`).

**What 23d picks up.** 23c built option (A) — the forked general-`d` `±r`-block rank-cert engine (no
`hρGv`) — end-to-end through the arm + corner-data assembly, and **closed the interior-`hρe₀`
conjecture-crux** (`baseRedundancy_perp_interior_reproduced_panel`, the redundancy-carry seam; sound,
axiom-clean, in tree). But 23c **stopped at the rank-certification half** of LEAF-4 step (ii): the
general-`d` interior rank cert is blocked by the **`hρGv` member-mapping wall** (§I.8.18–20, intrinsic to
KT), with **all three escape routes refuted** — (A) static-`W` re-shape, (B′) operated-frame block-rank,
(A′) re-derive-in-the-operated-frame — and a **primary-source KT-§6.4.2 recon confirming there is NO
missed KT route** ((B′)/(A′) *are* KT's own rank-count, kernel-dead). The `±r`-corner reformulation
escapes the wall at the ROW/membership level but NOT in the general-`d` RANK CERTIFICATION. So the
**rank-cert LAYER is the open re-design**; the carrier/motive/contract above it are untouched.

**All landed leaves stay in tree (sound, reusable under a re-architected rank cert).** The full landed
inventory — the forked cert `case_III_rank_certification_chain`, the carrier + concrete-`W` leaf
(LEAF-2), the discriminator-index plumbing (LEAF-1 + `candidatePanel…`), LEAF-3
(`exists_shared_redundancy_and_matched_candidate`), the per-member router (LEAF-4 (c), genuine branch
sound), the corner cert (`±r` via `hρe₀`), and the closed interior-`hρe₀` crux — is the
**`notes/Phase23c.md` *Landed-leaf ledger* + *Decisions made***; 23d does not duplicate it. `d=3` stays
fully green and zero-regression throughout.

## Current state

**Next concrete step = the A1 §I.8.21(α) FEASIBILITY RECON — a read-only compiler-checked SPIKE, NOT a
build** (the dispatch-ready spec is the *A1 dispatch kit* below). The single question: *does a
matrix-level block-rank-additivity lemma compose with the `±r` corner WITHOUT materialising the
fixed-member `hφ` membership that forces the wall?* Then:
- **A1 = FEASIBLE** → build **A2** (the §I.8.21(α) matrix-level block-rank-additivity infra), then wire it
  into `case_III_rank_certification_chain` / `case_III_arm_realization` and complete `chainData_dispatch`
  (CHAIN-2c-iii) + CHAIN-5.
- **A1 = INFEASIBLE** → fall to **(C)** land the general-`d` Theorem 5.5 conditional on the rank-cert
  obligation as an explicit top-level `h…` hypothesis (documenting the wall as the frontier), or **(D)** a
  broader reconsideration / external input.

**Do NOT** (settled this phase + at the 23c STOP): re-attempt the four dead route families
(§I.8.18–I.8.20); re-litigate the (A)-vs-ENTRY fork; re-attempt (A)/(B′)/(A′); re-hunt for a "missed KT
route" (the §(4.21) source recon settled there is none); or blind-build the §I.8.21(α) infra before A1's
verdict.

**Parallel-safe alternative (NOT the chosen next step, available if you want green-node momentum while the
rank cert soaks):** open **ENTRY** as its own sub-phase — it is independent of the blocked rank cert (the
CHAIN↔ENTRY contract is frozen). See *Remaining work* item 4.

## The A1 dispatch kit — the §I.8.21(α) feasibility recon (the first dispatch)

**Shape: a read-only COMPILER-CHECKED SPIKE** (un-named for a synchronous return; opus under OPUS-ONLY) — a
route-COMPOSITION question in the defeq-fragile cert zone, NOT a faithfulness question (faithfulness is
settled by §(4.21)), so it goes to the kernel, not a prose design-pass. Dispatch a tailored recon prompt
(per `coordinate-phase` rescue §6), NOT the routine build prompt.

**The question (the deliverable's core):** *Can a MATRIX-LEVEL block-rank-additivity lemma
`rank R(G,pᵢ) ≥ rank Mᵢ + rank R(G₁,q₁)` — formalizing KT's "submatrix containment" (6.61) as a
rank-preserving block embedding induced by the index-shift iso `ρᵢ` + the column op `Φ` — be stated and
COMPOSED with the `±r` corner cert WITHOUT materialising the fixed-member `hφ` row membership that forces
the wall?*

**Deliverable:** FEASIBLE-VIA-LEMMA-X (+ the exact lemma statement + the kernel-checked residual of
composing it with the `±r` corner + confirmation it never forms the `hφ` membership) /
INFEASIBLE-BECAUSE-Y (+ where it re-incurs the wall).

**Context to hand the spike (all verified during 23c):**
- **The gap is LOCALIZED.** KT's union-dimension finish (6.67, "at least one `Mᵢ` is full rank") is
  ALREADY LANDED as **CHAIN-4** (`exists_complementIso_ne_zero_of_homogeneousIncidence_gen`,
  `Claim612.lean`) + the extensor-independence (KT Lemma 2.1) as **CHAIN-3** (`Meet`/`MeetHodge.lean`). So
  the ONLY missing piece is the per-`Mᵢ` block-rank-ADDITIVITY (the matrix-level
  `rank ≥ rank Mᵢ + rank R(G₁,q₁)`).
- **The precedent + the exact gap.** The §(4.18) de-risk LANDED a GENERIC block-rank lemma
  `Submodule.finrank_add_card_le_of_linearIndependent_mkQ` (`Matroid/Constructions/…`), but it consumes a
  SCALAR fixed-member membership (`hWS : W ≤ span F₀.rigidityRows` + `hW`) at the single rank-cert use site
  (`Candidate.lean:1606–1611`) — that membership is what forces the wall (§(4.18)). The new lemma must
  instead carry the WHOLE base matrix `R(G₁,q₁)` as a BLOCK (a rank-preserving embedding), never forming a
  per-row membership. Read these two decls first.
- **The model.** The d=3 engine `case_III_rank_certification` (`Candidate.lean:1508`) certifies in the
  OPERATED frame (`Φ = columnOp hva`, `Pv` off-`v` projection, `case_III_full_family_restriction`,
  `linearIndependent_sum_restriction_block` `RigidityMatrix/Basic.lean:1189`); KT's (6.62) submatrix
  containment is the relabel `(funLeft (shiftPerm i.castSucc)⁻¹).dualMap`. The matrix-level lemma must turn
  "the relabel embeds `R(G₁,q₁)` as a sub-block of `R(G,pᵢ)`" into a `finrank`/`rank` additivity.
- **mathlib survey** for the abstract piece: `Matrix.rank`/block-triangular, `LinearMap.rank` of a block
  map, rank-additivity over an injective/relabel map, `Submodule.finrank_sup`/`_add` — find or state the
  right rank-preserving-block-embedding lemma.

**Design-pass clauses (mandatory in the recon prompt):** (i) verify every load-bearing claim against the
LANDED bodies (the d=3 cert, CHAIN-3/4, the generic block-rank lemma + its use site), not prior prose;
(ii) FLAG-DON'T-FORCE — an honest "INFEASIBLE because the matrix-level embedding STILL needs a per-member
membership at step Z" (→ option (C)/(D)) beats a forced feasible plan; (iii) trace the actual objects (the
column op `Φ`'s action, the relabel embedding's image, the `D·m_v` count, where `±r`'s `ℝ^D` identity
enters 6.67) to ground.

## Remaining work in Phase 23

1. **The general-`d` rank certification** (the 23d core) — re-architect `case_III_rank_certification_chain`
   / `case_III_arm_realization` per the A1 verdict (A2 build, or (C) honest-conditional). The corner cert
   (`±r` via `hρe₀`), the carrier, both `hLI` halves, the (α) bridge, the off-slot row bridge, the arm
   spine `case_III_arm_realization_chain`, and the corner-data assembly `case_III_arm_corner_assembly` are
   ALL LANDED and reusable (`notes/Phase23c.md` ledger). The interior `hρe₀` half of LEAF-4 step (ii) is
   CLOSED. The OPEN piece is the `hWS`/rank-certification half.
2. **CHAIN-2c-iii `chainData_dispatch`** — the general-`k` dispatch (a discriminator-pick + Fin-case ROUTER
   over the two landed arm routes: the OLD engine via `chainData_split_realization` for the base candidate
   `i=1` + the d=3 floor; the option-(A) `case_III_arm_corner_assembly` for interior `2 ≤ i < d`). Blocked
   only on item 1's rank cert; LEAF-1/2/3 + the discriminator-index plumbing + the genuine-branch router are
   landed.
3. **CHAIN-5** — wire the dispatch into the spine to discharge `hdispatch`.
4. **ENTRY** *(parallel-safe; own sub-phase when minted)* — reshape `Graph.exists_chain_data_of_noRigid`
   (`Reduction.lean:383`) to the `G.ChainData n` producer `exists_chainData_of_noRigid` (KT Lemma 4.6 chain
   + Lemma 4.8 split-off, general `d`); lift the `6 ≤ bodyBarDim n` floor; resolve the chain/cycle
   dichotomy (OD-1, KT Lemma 4.6 / Lemma 5.4). Consumer: `case_III_hsplit_producer_all_k`
   (`Arms.lean:777`). The CHAIN↔ENTRY `G.ChainData n` contract is **frozen** (below).
5. **ASSEMBLY** — compose the honest general-`d` Theorem 5.5, re-green `prop:rigidity-matrix-prop11` +
   `hub`, derive Thm 5.6, state Conjecture 1.2.

**Contract/motive note.** The wall is machinery *below* the contract — no C.0–C.6/motive change is forced
by it (§I.8.21 confirmed). The rank-cert re-architecture re-shapes `case_III_rank_certification` +
`case_III_arm_realization` only — it does **not** touch the dispatch's `hdispatch` consume-shape (C.3), the
`ChainData` record (C.1), or the 0-dof motive/IH (the dispatch threads one `ρ₀` either way).

## CHAIN↔ENTRY chain-data contract (frozen)

The `G.ChainData n` contract (the length-`d` chain record) is **frozen** — design `notes/Phase23-design.md`
§"CHAIN↔ENTRY contract", C.0–C.6; no motive/IH change; `d=3` zero-regression. The dispatch's input shape is
the chain extractor's output shape, so ENTRY can be built independently against this frozen contract.

## Blueprint-clarity obligation (carried from 23b/23c — owner-flagged)

The `lem:case-III` general-`d` node's exposition must materialize KT's index-shift isos (6.54–6.56) + ±r
chain (6.66) explicitly (the Lean economizes; the prose must not), and present the redundancy-carry as
**whole-matrix bookkeeping with `r` abstract and the member moving**, flagging the fixed-functional-transport
shape as the trap (the §(4.21) source-recon framing). Written at phase-close once the arm is `sorry`-free.
Ledger entry: `notes/BlueprintExposition.md` (`lem:case-III general-d`).

## Blockers / open questions

- **The `hρGv` member-mapping wall (intrinsic to KT) blocks the general-`d` interior rank cert.** All three
  escape routes (A/B′/A′) are refuted (design §I.8.24(4.17)–(4.20), four kernel spikes); the KT-§6.4.2
  source recon (§(4.21), primary-PDF, HIGH confidence) confirms there is NO missed KT route. The open
  question A1 resolves: can a matrix-level block-rank-additivity lemma (KT's submatrix containment 6.61 as a
  rank-preserving block embedding) certify the rank WITHOUT the fixed-member `hφ` membership? FEASIBLE → A2;
  INFEASIBLE → (C)/(D).

## Hand-off / next phase

**Next concrete commit-equivalent: dispatch the A1 §I.8.21(α) feasibility recon** (read-only spike; the *A1
dispatch kit* above is the dispatch-ready spec). It returns FEASIBLE-VIA-LEMMA-X / INFEASIBLE-BECAUSE-Y; its
verdict selects 23d's build path (A2 / (C) / (D)). The recon is the smallest move that resolves the central
uncertainty; do not build the §I.8.21(α) infra before its verdict.

## Decisions made during this phase

*(Fresh at open. The inherited landed-leaf inventory + the wall-characterization verdicts + the
cross-cutting lessons of building option (A) are the settled archive in `notes/Phase23c.md` *Decisions
made* + *Landed-leaf ledger*; 23d does not duplicate them. New 23d decisions land here.)*

- **Opened 2026-06-24 at a clean-break close of 23c (user-adjudicated), at the member-mapping-wall phase
  STOP.** 23c's chosen architecture (option (A), the `±r`-block engine) is conclusively refuted at the
  rank-cert level; the redundancy-carry re-architecture half succeeded (interior `hρe₀` closed). 23d =
  the rank-certification reconsideration (A1 recon → A2 build / (C) honest-conditional / (D) reconsider),
  still within the CHAIN layer (CHAIN now spans 23b+23c+23d). ENTRY/ASSEMBLY get later letters. Structural
  precedent: the 23b→23c clean-break close at this same wall.
