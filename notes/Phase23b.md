# Phase 23b — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality [CHAIN] (work log)

**Status:** open. CLOSED: CHAIN-1/3/4 + OD-7 (the four-producer tail, all general-`k`) + CHAIN-2a + the
CHAIN-2c-ii foundation. The `hρGv` route is **LOCKED = Route W (option a′)**, the `hwmem` slot is LANDED
(`chainData_bottom_relabel`), and the arm's algebraic core + chain-induction (LEAVES 1–4) + seed bridge (P3)
+ slot core + per-edge perp are all LANDED axiom-clean. The arm's perp slot needed the edge-grouped
redundancy at the CANDIDATE framework, which A-1 supplies only at the BASE (row-352 gap); the i=3
edge-alignment **DE-RISK RAN (row 353, `i3_candidateBlock_transport_deRisk`)** → the genuinely-new
candidate-level edge-grouped transport decomposes into 3 buildable TRANSPORT sub-leaves T-1/T-2/T-3 (clean
bijective re-index, NO re-grouping, NO new math); **T-1 `…_transport_blocks` LANDED axiom-clean**.
~2–4 commits left to the arm (T-2/T-3 then arm assembly); then **CHAIN-2c-iii** `chainData_dispatch`
closes 23b green-modulo `hdispatch` (**CHAIN-5 → front of 23c**).

**23b CLOSE BOUNDARY (LOCKED 2026-06-19):** close 23b when `chainData_dispatch` (2c-iii) lands — CHAIN-5 →
front of 23c=ENTRY, 23b closes green-modulo `hdispatch`. The integer Phase 23 stays **in progress** (ENTRY /
ASSEMBLY remain). (Sub-phase codes-until-open: `CARRIER`=23a closed, `CHAIN`=23b, `ENTRY`/`ASSEMBLY`
code-only.)

**Orientation.** The **23b (CHAIN layer)** rolling state + hand-off. Cross-phase plan + the detailed
leaf-level recon arcs live in `notes/Phase23-design.md` (§"CHAIN"; the live `hρGv` arc is §(o‴)(I.6)/(I.8));
program map `notes/MolecularConjecture.md`. Superseded route-history (clean-relabel refutation, the FIX-FORK,
the engine-slot adjudication, the pre-GAP-FOUND "arm converges" framing) is in design §(o‴) + git, **not**
re-narrated here.

## Current state

**NEXT STEP (single authoritative) — build the remaining 2 transport sub-leaves (T-2/T-3), then the
arm.** The transport leaf `chainData_candidateRow_edgeGrouped_transport` decomposes into 3 buildable
sub-leaves T-1/T-2/T-3 (signatures in design §(o‴)(I.8.10)). **T-1 LANDED** (axiom-clean): the de-risked
block half — the all-`i`/`∀ j` lift of the anchor `i3_candidateBlock_transport_deRisk`. Remaining: T-2
(relabel `hcomb`) + T-3 (the `G`-links) → the arm `chainData_relabel_arm` (M₃ template re-indexed,
~1–2c) → CHAIN-2c-iii `chainData_dispatch` → 23b closes green-modulo `hdispatch`. ~2–4 commits left, no
motive/IH/contract change.

**SMALLEST NEXT COMMIT = T-2 `chainData_candidateRow_edgeGrouped_transport_comb`** (relabel of `hcomb`):
carry A-1's base combination identity `hingeRow (ab) ρ = ∑ⱼ cGv j • hingeRow (uvGv j)(vvGv j)(rvGv j)`
across the `(funLeft (shiftPerm i.castSucc).symm).dualMap` relabel to the candidate orientation
`hingeRow (vᵢ₋₁)(vᵢ₊₁) ρ₀ = ∑ⱼ cGv j • hingeRow (relabelled endpoints)(rvGv j)`, EXACTLY as
`chainData_bottom_relabel` (`Relabel.lean:1939`) carries genuine rows (the `dualMap` is linear,
distributes over `∑` + `•`). Then T-3 (the candidate `G`-links by `removeVertex_isLink` + the graph-iso).
Exact signatures: design §(o‴)(I.8.10).

**T-1 LANDED (`chainData_candidateRow_edgeGrouped_transport_blocks`, `Relabel.lean:4422`, axiom-clean).**
The de-risked block half — `fun j => cd.i3_candidateBlock_transport_deRisk i (evGv j) (hrv j)`, a pure
per-summand replay of the anchor. Carries each A-1 base block membership `rvGv j ∈ (base).hingeRowBlock
(evGv j)` to the candidate `Fva = ofNormals (G−vᵢ) endsσρ qρ` at the bijective re-index `(shiftEdgePerm
i).symm (evGv j)`. NO new math (the anchor already general-`i`/general-edge).

**ROW-352→353 GAP RESOLVED (the gap, why the arm did not converge from landed pieces, and the de-risk that
unblocked it).** The `hρGv` perp sub-slot `chainData_freshEdge_perp_of_baseRedundancy` (`Relabel.lean:4311`)
consumes its edge-grouped data through THREE hyps: `hlink`/`hcomb` (framework-free) + `hrv : ∀ j, rv j ∈
Fva.hingeRowBlock (ev j)` at the **CANDIDATE** framework — the ONLY framework-bound one. A-1
`exists_candidateRow_bottomRows_of_rigidOn` (`Candidate.lean:439–445`) supplies the edge-grouped redundancy
ONLY at the **BASE** `ofNormals Gv ends q` (Gv = G−v₁); NO landed lemma transported the per-summand block
memberships (grep-confirmed: candidate-level `hrv` was only ever a hypothesis). This was the rows-288/291
LEVEL-MISMATCH redux. **De-risk verdict (row 353):** the candidate block at ANY edge `f` equals the base
block at `shiftEdgePerm i f` (`ofNormals_supportExtensor_relabel_perm` for arbitrary `f`; `supportExtensor`
graph-independent), so A-1's base `hrv` at `evGv j` is exactly the candidate `hrv` at
`(shiftEdgePerm i).symm (evGv j)` — a bijective re-index of the SAME summands. The chain induction LEAVES
1–4 are framework-free and group by FILTERING `ev j = cd.edge ⟨i⟩` (non-chain summands vanish via the
degree-2 closure), so A-1's arbitrary `evGv j` are harmless. All OTHER engine slots DO converge from landed
pieces (`hwmem ← chainData_bottom_relabel`; seed ← P3 LANDED; `hρe₀` / discriminator / removeVertex
bookkeeping per the d=3 M₃ template).

**FLAGGED SUBTLETY — RESOLVED (Q2-with-a-twist, design §(o‴)(I.8.10)).** "A-1's base summand edges `evGv j`
are ARBITRARY `G−v₁`-links, NOT `shiftEdgePerm`-images" — the de-risk found this is a **NON-ISSUE**: the
block correspondence holds for arbitrary edges, so the bijective re-index suffices; no re-grouping into a
`shiftEdgePerm`-image basis is needed. Q3 (the feared genuinely-new re-grouping argument) does NOT arise.

**Standing context (settled; full detail in the design doc).** (1) *Architectural:* metric-using Hodge
leaves live in `MeetHodge.lean`, never metric-free `Meet.lean` (a `PiL2` import → `whnf` timeout) —
TACTICS-QUIRKS § 59. (2) *Orientation:* the arm-engine is already general-`k`; CHAIN replaced only the d=3
dispatch + its `⋀²ℝ⁴` discriminator with the `d`-candidate chain + `⋀^{d−1}` duality finish. (3) *Contract
(SETTLED):* the CHAIN↔ENTRY `G.ChainData n` shape is frozen — three lockstep decls (ENTRY extractor /
producer `…hcand` / CHAIN-5 `hdispatch`), no motive/IH change (C.6), `d=3` zero-regression (design
§"CHAIN↔ENTRY contract").

**Route β — LOCKED** (user-adjudicated, row 242): ONE `v₁`-base + the uniform `Fin (k+1)` relabel arm; route
B is **within** β. (Blueprint-clarity obligation: *Hand-off* CHAIN-2c bullet + design §(o″).) The arm engine
`case_III_arm_realization` (`Arms.lean:72`) binds `hwmem` (`:96`) and `hρGv` (`:91`) at the
**removeVertex-level** `ofNormals Gv ends q` (`Gv = G−vᵢ`, `ends` relabelled, `q = qρ`, `(a,b)=(vᵢ₊₁,vᵢ₋₁)`;
KT-faithful, confirmed vs `chainData_bottom_relabel`'s output type `Relabel.lean:1960–1972`). d=3 M₃ `i=2`
cycle is the single-swap involution (zero-regression); `case_III_candidate_dispatch` stays green until
CHAIN-5/ENTRY wrap it (C.4).

## Landed-leaf inventory (the arm assembly references these names)

One-line LANDED verdicts (file, axiom-clean; detail = git + Lean docstrings + design §(o‴)(I.6)/(I.8)):

- **`chainData_bottom_relabel`** (`Relabel.lean`) — the genuine-row `hwmem` leaf; per-member
  `(shiftPerm i.castSucc)⁻¹` cycle transport of the base bottom-row disjunction to the candidate arm.
- **`chainData_freshEdge_slot_mem`** (`Relabel.lean`) — LEAF 5 `hρGv`-slot core; lifts the `i=3` gate to the
  concrete fold framework, peeling the slot row `hingeRow vᵢ₋₁ vᵢ₊₁ ρ₀` off the fold output minus the
  surviving rows. Takes an abstract per-edge `hperp`.
- **`chainData_freshEdge_perp_of_baseRedundancy`** (`Relabel.lean`) — witness-free per-edge perp: for every
  deeper interior surviving edge (`2 ≤ s < d`), `ρ₀ ⊥ Fva.supportExtensor (edge s)` from the *candidate*-framework
  edge-grouped base redundancy. Consumes the redundancy (`hlink`/`hcomb`/`hrv`) at the CANDIDATE framework — the
  level the transport leaf T-1/T-2/T-3 supplies from A-1's BASE output. Mechanism = LEAF 4's `group = −ρ₀` +
  `edgeGroup_acolumn_mem_block` + `mem_hingeRowBlock_iff`.
- **`i3_candidateBlock_transport_deRisk`** (`Relabel.lean`, row 353) — the edge-alignment de-risk anchor: the
  candidate framework's `hingeRowBlock` at an ARBITRARY edge `f` = the base framework's block at
  `shiftEdgePerm i f`, so a base block membership transports to the candidate block at `(shiftEdgePerm i).symm
  f`. The load-bearing fact T-1 is the all-`i` lift of. Confirms Q2-with-a-twist (clean bijective re-index, no
  re-grouping).
- **`chainData_candidateRow_edgeGrouped_transport_blocks`** (`Relabel.lean`, T-1, row 355) — the de-risked
  block half of the transport leaf: the all-`i`/`∀ j` lift of the anchor. Carries A-1's per-summand base
  block memberships `rvGv j ∈ (base).hingeRowBlock (evGv j)` to the candidate `Fva = ofNormals (G−vᵢ) endsσρ
  qρ` at the bijective re-index `(shiftEdgePerm i).symm (evGv j)`. Proof = `fun j => cd.i3_candidateBlock_
  transport_deRisk i (evGv j) (hrv j)` (pure per-summand replay; no new math).
- **`chainData_freshEdge_perp_of_witness`** (`Relabel.lean`) — per-vertex form (STANDS; the arm threads the
  base-redundancy lemma above, not this).
- **Chain-induction LEAVES 1–4** (`Relabel.lean`, the eq-(6.44) regroup off the single base redundancy):
  `interiorGroup_acolumn_adjacency` (step kernel, deg-2 column cancellation) + `anchor_group_acolumn_eq_baseRedundancy`
  (base case `P(2)` at `vtx 2`, degree-ONE in `G−v₁`) + `interior_group_eq_baseRedundancy` (`Nat.le_induction`;
  every interior edge-group's tail column = the anchor's; `hcol ∀a` replaced by endpoint id `hab₁`/`hab₂` —
  jointly contradictory with `hcomb` for `r̂≠0`) + `interior_group_acolumn_eq_neg_baseRedundancy` (consumer
  reading: tail column `= −ρ₀`). Plus the framework-free primitives `hingeRow_comp_single_endpoint_flip` +
  `edgeGroup_comp_single_endpoint_flip`, `edgeIndexedCombination_comp_single_{off,eq_incident}`.
- **P3 seed bridge `shiftSeedAdv_eq_funLeft_shiftPerm`** (+ helper `shiftSeedAdv_eq_prod_shiftSeedSwap`,
  `Relabel.lean`) — the fold seed `shiftSeedAdv q (i−1)` = engine seed `qρ` (KT eq. 6.56).
- **LEAF-ρ1 algebraic core `wstep_foldl_hingeRow_telescope`** (+ helpers `wstep_hingeRow_off`/`_frontier`,
  `Relabel.lean`) — the general-`i` closed form of the W9a `wstep` foldl = `(∑_{s<m} hingeRow wₛ wₛ₊₁ ρ₀) +
  hingeRow w_m w_{m+2} ρ₀` (`m=i−1`, KT eq. 6.66); + its membership corollary `wstep_foldl_freshEdge_slot_mem`.
  **P1 LANDED:** both restated over `Set.InjOn w (Set.Iic (m+2))` (the dead `Function.Injective (ℕ→α)` is
  `False` over `[Finite α]`); the arm supplies `hinj` from `cd.vtx_inj` via `Set.InjOn.mono`.
- **LEAF-ρ2 `shiftBodyListAsc_relabel_foldl_hingeRow`** + the G1 bridges
  `shiftPerm_eq_prod_map_swap_shiftBodyListAsc` (`Operations.lean`) / `wstep_foldl_funLeft_eq` (`Relabel.lean`) —
  the relabel-only ascending foldl = inverse-cycle relabelled hinge row.
- **A-1 `exists_candidateRow_bottomRows_of_rigidOn`** (`Candidate.lean`) + `chainData_split_w6b_gates`
  (`Realization.lean`) — the W6b producer outputs the eq-(6.52) `λ`-grouped `(ab)`-edge witness `lamAB`/`rab`
  AND (after the a′-i signature change) the candidate row `hρGv` in **edge-grouped** form (via
  `exists_edgeIndexed_combination_of_mem_span_rigidityRows`, `Basic.lean`). **At the BASE `G−v₁` only** (the
  row-352 gap). The `(b,a)` branch negates `rab → −rab` (W8 sign-swap).
- **A-2 carrier `candidate_perp_two_incident_panels`** (+ the `supportExtensor`-perp form
  `candidate_perp_two_incident_supportExtensors`, `Relabel.lean`) — the interior-vertex eq-(6.44) perp carry:
  the common candidate `r̂ := ∑λab•rab` ⊥ both incident chain-edge panels (⊥ `C_c` direct; ⊥ `C_d` via
  `candidateRow_ac_eq_neg` `rAC=−r̂`).
- **A-3 `freshEdge_surviving_row_mem_of_witness`** (`Relabel.lean`) — the single-vertex composition feeding the
  A-1 witness through A-2 to discharge `freshEdge_surviving_row_mem`'s `hperp` for real.
- **`panelCorrespondence_supportExtensor`** + **`candidate_supportExtensor_perp_of_base`** (`Relabel.lean`) —
  option-(a′) panel-correspondence transport identity (general-`i`): candidate-`i`.`supportExtensor (edge s)`
  = `v₁`-base.`supportExtensor (shiftEdgePerm i (edge s))`, and the perp transports across it
  (`rw [panelCorrespondence_supportExtensor]; exact hperp`). **The per-summand transport the row-352 leaf
  threads.** + `edgeGroup_acolumn_mem_block` (column-in-block core).
- **The W9a fold** (`seedAdvance_wstep_hstep` + `wstep_foldl_mem_span_rigidityRows` +
  `shiftBodyListAsc_foldl_mem_span_rigidityRows`); **seed half** `seedShift_inv_cancel` / `seedShift_off_cycle`;
  the inverse-cycle action lemmas (4 `shiftPerm_inv_*` + 7 `shiftEdgePerm_inv_*`); `ofNormals_supportExtensor_relabel_perm`
  (the `hsupp_of` foundation); `removeVertex_genuine_shiftRelabel` (the genuine-link transport crux);
  `blockRow_relabel_perm`; `rigidityRow_relabel_{off_cycle,to_genuine}`. `ChainData` + accessors
  (`Operations.lean`); **2c-i** `exists_chainData_discriminator_pick`; **2c-ii-α** `ChainData.shiftPerm` (KT
  6.54); **2c-ii-graphiso** `splitOff_isLink_shiftRelabel_iff` + `shiftEdgePerm`.

**Orphan / confirm-and-delete (`git grep` zero callers at the delete commit):**
- **STAND (Route W building blocks, NOT delete):** `freshEdge_surviving_row_mem_of_witness` (A-2) /
  `candidate_perp_two_incident_*` / `panelCorrespondence_supportExtensor` / `candidate_supportExtensor_perp_of_base`;
  `freshEdge_surviving_row_mem` (the perp-half builder); the telescope
  (`wstep_foldl_hingeRow_telescope` / `_freshEdge_slot_mem`); the `acolumn_..._sup_...` crux; A-1/A-2/`_of_witness`;
  `candidateRow_ac_eq_neg` (Leaf B re-consumes it).
- **Orphaned-for-the-arm (confirm-and-delete at the arm-build commit):** the split→split
  `rigidityRow_chainData_relabel` / `rigidityRow_relabel_perm` (rows 288/291, wrong graph level, §(o‴)(I.5));
  the candidate→base T-W9a fold `shiftBodyList_foldr_…` (wrong orientation, H.10); the two block bricks
  `rigidityRow_relabel_to_block{,_swap}` (the assembly inlined the wrap-block); `ofNormals_relabel_perm` + the
  binary `…comp…` (docstring-referenced — sync on delete); the per-`i`-W6b `chainData_split_realization`/`_w6b_gates`
  (Fix B; re-check at 2c-iii). **DELETED 2026-06-19:** the 5-decl W9b per-body chain (§(o‴)(I.1), machine-refuted).

**FIX-FORK SETTLED (§(o‴)(H), 2026-06-19, adversarially verified (H.10)) — corrected Fix A buildable:** keep
the shared `ρ₀`, transport memberships **base→candidate** (relabel `(shiftPerm i)⁻¹`, seed advancing). Fix B
(per-`i` re-seed) INFEASIBLE (breaks KT's single-`r` existence). The genuine-row `hwmem` transport is a
removeVertex-level **per-row case-split** (NOT the split→split graph-iso, NOT a W9a span fold which needs
*literal* rows). The landed candidate→base T-W9a/W9b folds are orphaned-for-the-arm (`wstep` non-invertible).
Full reasoning + KT deciding lines = design §(o‴)(H)/(H.10).

## CHAIN leaf checklist

Exact signatures + dependency order in `notes/Phase23-design.md` §"CHAIN"(c)/(l)/(m)/(n)/(o)/(o′)/(o″)/(o‴).

- [x] **CHAIN-3 — `⋀^{d−1}(ℝ^{d+1})` duality bricks + Hodge panel-meet membership** (`Meet.lean` +
      `MeetHodge.lean`). **CLOSED 2026-06-17** (route = `⋀^{d−1}W`-is-a-line, NOT the withdrawn d=3-only `Φ̃`;
      the OD-8 route-α chain h-0…h-4 on the join=meet duality `extensor_join_proportional_complementIso_meet`).
      Detail: design §"CHAIN"(f)/(g)/(h) + git.
      - [~] **Cleanup-round candidate (forward, low-priority):** revert the lifted `wedgeFixedLeft` block +
        `inf_range_wedgeFixedLeft` (ambient `{d}`, served the withdrawn `Φ̃` route) to `Fin 4` — the d=3
        lemmas stay GREEN, **do NOT touch**. (Cleanup item (2), the `finrank_toDualPerp_pair_eq` factoring,
        is DONE 2026-06-20.)
- [x] **CHAIN-1 — the `d`-fold candidate machinery** (`RigidityMatrix/Basic.lean`). **CLOSED 2026-06-18.**
      Graph-free over `ScrewSpace k`: the eq.-6.62 row-correspondence swap + the `ιc`-block augment.
- [x] **CHAIN-4 — the `Fin (d+1)` incidence + Claim-6.12 discriminator** (`RigidityMatrix/Claim612.lean`).
      **CLOSED 2026-06-18** (4a–4d landed; consumes CHAIN-3; OD-4 RESOLVED). Capstone =
      `exists_complementIso_ne_zero_of_homogeneousIncidence_gen`.
- [ ] **CHAIN-2 — the `Fin d`-indexed candidate-reduction layer (eqs. 6.59–6.67)** (`CaseIII/`). Zeroth leaf
      (`G.ChainData n` record + accessors) + **CHAIN-2a** (`chainData_split_w6b_gates` + `chainData_split_realization`)
      **LANDED/CLOSED 2026-06-18.** Remaining: **CHAIN-2c — the single-base `Fin (k+1)` family dispatch** (route
      β): ONE base, ONE `ρ₀`, ONE discriminator → `fin_cases u`; eq. (6.66) absorbed. **2c-i** LANDED. **2c-ii**
      (the genuinely-new relabel arm — KT's `ρᵢ` is a `(i−1)`-cycle): foundation LANDED; FIX-FORK SETTLED
      (corrected Fix A). The arm `chainData_relabel_arm`'s every algebraic prerequisite is LANDED; the
      **row-352 GAP** (candidate-vs-base level mismatch for the perp slot's `hrv`) is **DE-RISKED (row 353,
      `i3_candidateBlock_transport_deRisk`)**: the genuinely-new candidate-level edge-grouped transport
      `chainData_candidateRow_edgeGrouped_transport` decomposes into 3 buildable TRANSPORT sub-leaves
      T-1/T-2/T-3 (no re-grouping, no new math). **T-1 LANDED** (`…_transport_blocks`, axiom-clean). →
      **NEXT** = T-2 per *Current state*; then T-3; then the arm; then **2c-iii** `chainData_dispatch`. d=3
      M₃ = `i=2` involution.
- [ ] **CHAIN-5 — the `d`-chain dispatch assembly** (`CaseIII/Realization.lean`). **→ MOVED TO 23c** (boundary
      LOCKED 2026-06-19; gated on ENTRY's extractor reshape, lands at the front of 23c=ENTRY — 23b closes
      green-modulo `hdispatch`). Replace `case_III_candidate_dispatch`; feed the (general-`k`) arm closers.
      **Signature FROZEN** by the CHAIN↔ENTRY contract (C.3): `hdispatch` consumes a `G.ChainData n` record +
      the `splitOff (vtx 1)(vtx 0)(vtx 2) e₀` deficiency-0 fact + the IH-generic base realization. Keep the
      `d=3` dispatch as a `k=2`/length-3 wrapper (C.4 zero-regression).
- [x] **CHAIN tail — lift the four 23a-carried producers (OD-7 fold). CLOSED 2026-06-18.** All four producers
      (`hbase_k`/`hcut_k`/`hcontract_k`/`hforget_k`) + both M4 halves general-`k`; the one genuinely-new piece
      was LEAF-0 `linearIndependent_normals_of_algebraicIndependent_triple`. Detail: design §(k) + git.

## Blockers / open questions

The OD resolutions (full text in `notes/Phase23-design.md` §"CHAIN"(e)/(g)):

- **OD-8 — RESOLVED 2026-06-17** (route α, `complementIso` = the O(n)-natural Hodge `⋆`; β rejected). §"CHAIN"(h).
- **OD-6 — DECIDED:** five leaves within ONE sub-phase 23b (the arm engine is already general-`k`).
- **OD-7 — DECIDED + CLOSED:** the four 23a producers folded into CHAIN's tail; all general-`k`.
- **OD-4 — RESOLVED 2026-06-18:** existence/homogeneous route, alg-independence NOT forced — the eq.-(6.67)
  D-span runs off `span_omitTwoExtensor_eq_top` (linear independence of `d+1` homogeneous vectors, via Lemma
  2.1, not KT's affine points). §(i).
- **(b) producer-shape — SETTLED 2026-06-17:** the `G.ChainData n` interface frozen, no motive/IH change (C.6),
  `d=3` zero-regression wrapper (C.4: chain `v₀v₁v₂v₃ = b—v—a—c`). §"CHAIN↔ENTRY contract".
- **OD-1 (still open — ENTRY's to resolve at build, C.5).** KT Lemma 5.4 short-cycle base is a real branch of
  the general-`d` chain entry (unlike `d=3`'s inline triangle floor); whether the dispatch assumes the chain
  branch (ENTRY discharging the cycle branch) is invariant for CHAIN-5's signature.

## Hand-off / next phase

**The single authoritative next-step is in *Current state* above:** finish the candidate-level
edge-grouped transport leaf `chainData_candidateRow_edgeGrouped_transport`'s remaining 2 sub-leaves —
**T-1** `…_transport_blocks` LANDED (the de-risked all-`i` lift of `i3_candidateBlock_transport_deRisk`);
**T-2** `…_transport_comb` (the SMALLEST NEXT COMMIT; relabel `hcomb`), **T-3** `…_transport_links` (the
`G`-links) → wire the arm `chainData_relabel_arm` (`refine case_III_arm_realization`, M₃ template
re-indexed, ~1–2c) → **2c-iii** `chainData_dispatch` (replaces `case_III_candidate_dispatch`) →
**CHAIN-5** (in 23c). Net ~2–4 commits left to the arm. **No motive/IH/contract change** anywhere in this
chain; **no genuinely-new-math fork** (the i=3 de-risk verdict). d=3 M₃ = `i=2` involution
(zero-regression). Exact sub-leaf signatures in design §(o‴)(I.8.10).

**ENTRY obligation — PINNED (signature frozen; minted/built when its turn comes).** ENTRY reshapes
`Graph.exists_chain_data_of_noRigid` (`Reduction.lean:383`) from the fixed `v,a,b,c` 4-tuple to the
`G.ChainData n` producer `exists_chainData_of_noRigid` (contract C.2 — KT Lemma 4.6 chain + Lemma 4.8
split-off minimality at general `d`), and lifts the `6 ≤ bodyBarDim n` floor to the general chain-length
floor. The chain/cycle dichotomy (OD-1, KT Lemma 4.6 / Lemma 5.4) is **ENTRY's to resolve at build** (C.5).
**The producer `case_III_hsplit_producer_all_k` (`Arms.lean:777`) is the chain extractor's only consumer**
(Arms.lean:828–857) — its `hcand` slot is the third lockstep decl (C.0).

**Green-modulo boundary CHAIN hands downstream** (design §"CHAIN"(d)): CHAIN constructs the general-`k`
`chainData_dispatch` (against the frozen `ChainData` contract) and lifts the four producers (OD-7); **CHAIN-5
wires it into the spine to discharge `hdispatch` in 23c** (gated on ENTRY's extractor), so 23b hands
`hdispatch` downstream green-modulo. **ASSEMBLY** composes the honest general-`d` Theorem 5.5, re-greens
`prop:rigidity-matrix-prop11` + `hub`, derives Thm 5.6, states Conjecture 1.2.

**Blueprint-clarity obligation (owner-flagged 2026-06-18 — "absolutely clear").** Route β **absorbs** KT's
explicit index-shift isos (6.54–6.56) + ±r chain (6.66) into the Lean `shiftPerm` relabel arm — so the
`lem:case-III` general-`d` node's prose MUST materialize them explicitly (§(o)/§(o′) pin the four ordered
points): (1) single-`v₁`-base construction; (2) the index-shift iso `ρᵢ` (the `(i−1)`-cycle) + "exactly the
same framework" via it; (3) the single redundancy `r` (eq. 6.52) carried ±-ly across the `d` panels (eq.
6.66); (4) the (6.67) discriminator (Lemma 2.1 on the `d+1` points). The Lean economizes; the exposition must
not. Tracked in BlueprintExposition (`lem:case-III` general-`d`, extending the d=3 `lem:case-III-claim612-eq644`);
written as the arm/CHAIN-5 land + at phase-close.

## Decisions made during this phase

(Settled entries are one-line verdicts: decision + Lean name. Proof techniques live in git + `notes/FRICTION.md`
+ the design doc §"CHAIN"(f)/(g)/(h) + §"CHAIN↔ENTRY contract". The forward detail — route to close the open
leaves — is in *Current state* / *Hand-off* above. The opening recon's decisions — OD-6/OD-7 resolved, OD-4 +
(b) flagged — live in design §"CHAIN"(e); the chain-data contract in §"CHAIN↔ENTRY contract".)

### Phase-local choices and proof techniques

- **Opened on a leaf-level recon, not a build** — found the arm-engine already general-`k`, only the dispatch
  `d=3`; surfaced flag (b) → §"CHAIN"(a)–(e).
- **CHAIN↔ENTRY chain-data contract settled** — `G.ChainData n` structure + producer/`hdispatch` signatures;
  no motive/IH change (clause ii) → §"CHAIN↔ENTRY contract" C.0–C.6.
- **CHAIN-3-finish recon: the `⋀^{d−1}W`-is-a-line route, NOT the d=3 `Φ̃` route**
  (`finrank_sup_range_wedgeFixedLeft` / `extensor_toDual_extensor_eq_zero_of_perp` withdrawn, kept green as the
  d=3 wrapper) → §"CHAIN"(f) (+ *Coordinator KT-route check*).
- **OD-8 RESOLVED: route α (`complementIso` O(n)-equivariance, the Hodge `⋆`); β rejected** (the withdrawn
  `dim Φ̃` count) → §"CHAIN"(h).
- **OD-4 RESOLVED 2026-06-18: existence/homogeneous route, alg-independence NOT forced** (overturns "forced").
  The eq.-(6.67) D-span runs off `span_omitTwoExtensor_eq_top` (linear independence of `d+1` homogeneous
  vectors, via Lemma 2.1) — never KT's affine points. Source-verified vs KT p.698; the row #106 cross-product
  construction is dead. CHAIN-4 decomposed 4a–4d → §"CHAIN"(i)/(j).
- **CHAIN-2 decomposition (recon 2026-06-18) — overturns §(c)'s framing.** The
  `caseIIICandidate`/`case_III_old_new_blocks`/`case_III_rank_certification` chain is already general-`k` (the
  only `d=3`-pin in `CaseIII/` is the dispatch = CHAIN-5). CHAIN-2 = the `Fin d`-indexed reduction *layer* (2a /
  2b / 2c) → §"CHAIN"(l).
- **CHAIN-2a design-pass + CLOSED 2026-06-18 — VERDICT: re-index, gates threaded from above.** The per-`i`
  reduction is a `case_III_arm_realization` re-index, not from-scratch gate construction; the gate family is
  carried as hypotheses and supplied by two general-`k` producers (W6b + CHAIN-4d discriminator). Two
  axiom-clean leaves: `chainData_split_w6b_gates` + `chainData_split_realization`; the transversal half stays
  `htrans` (CHAIN-2c fills via the discriminator). → §"CHAIN"(m).
- **CHAIN-2b/2c design-pass 2026-06-18 — VERDICT: single-base `Fin (k+1)` dispatch (route β), ±r chain absorbed
  (no separate 2b lemma).** Route β LOCKED (user-adjudicated, row 242). § design (n).
- **The bottom-family-transport recon trail** (route B per-body W9b fold → telescoping pass ruled it dead →
  pair recon refuted the forward whole-relabel → §(o‴)(H) corrected Fix A) lives in design §(o)–(o‴)(H.10) +
  git; the live verdict is in *Current state* (FIX-FORK SETTLED).
- **FIX-FORK SETTLED 2026-06-19 (§(o‴)(H)/(H.10)) — corrected Fix A; Fix B INFEASIBLE.** Keep the shared `ρ₀`,
  invert to `(shiftPerm i)⁻¹` (cancels the seed, matches KT (6.62)); Fix B breaks KT's single-`r` existence.
  Re-author the transport base→candidate directly (re-fold opposite order, seed advancing) — the landed
  candidate→base T-W9a/W9b folds are orphaned-for-the-arm. No motive/IH/spine change.
- **W9b per-body chain DELETED 2026-06-19 (§(o‴)(I.1)).** Removed the 5-decl dead cluster from `Relabel.lean`
  (`git grep` zero callers); §(o‴)(I.1) showed the per-body block transport cannot terminate at the chain
  interior. Build green + lint clean. Kept `candidateRow_ac_eq_neg` (Leaf B re-consumes it).
- **2c-ii-arm `hwmem` transport bricks all LANDED 2026-06-19/20 (axiom-clean).** The genuine-row `hwmem`
  disjunct is a removeVertex-level per-row case-split (generalizing `case_III_bottom_relabel`, NOT a split
  graph-iso, NOT a W9b fold; §(o‴)(I.5)/(I.6)). Landed: 3 genuine-row branches, both block-orientation bricks,
  the `hsupp_of` foundation `ofNormals_supportExtensor_relabel_perm`, the make-or-break
  `removeVertex_genuine_shiftRelabel`, the per-member assembly `chainData_bottom_relabel`, the `hρGv` G1
  bridges, LEAF-ρ2. Lessons → TACTICS-QUIRKS §38 / GOLF §20 / FRICTION idioms.
- **`hρGv` algebraic core + chain-induction LANDED 2026-06-20 (all axiom-clean; detail = §(o‴)(I.7.10)/(I.8) +
  git + Lean docstrings):** LEAF-ρ1 closed-form telescope `wstep_foldl_hingeRow_telescope` (an EXACT closed-form
  sum, KT eq. 6.66) + the membership corollary `wstep_foldl_freshEdge_slot_mem`; **P1** finite-range restatement
  over `Set.InjOn w (Set.Iic (m+2))`; the P2 two-edge column crux `acolumn_mem_hingeRowBlock_sup_of_span_rigidityRows`
  + the general-`i` surviving-row builder `freshEdge_surviving_row_mem`; A-2 carrier
  `candidate_perp_two_incident_{panels,supportExtensors}` (Route A — the perp from the eq-6.52 `r̂`, NOT
  arbitrary `ρ₀`; the refuted generic-`ρ₀` isolated implication `ρ₀_perp_interior_chain_edge` lived in the
  vacuous `=⊤` sup); A-1 W6b witness re-thread; A-3 single-vertex composition
  `freshEdge_surviving_row_mem_of_witness`.
- **`hρGv` Route W LOCKED via the i=3 de-risk fork (2026-06-20).** The all-`i`-lift de-risk
  `i3_freshEdge_interior_acolumn_sup_deRisk` (axiom-clean) RAN → at honest `i=3` the interior `vtx 1` is
  GENUINELY degree-2 in `Fva = G−vtx 3` (both edges survive), so the column lands in the **sup** `block(e0)⊔block(e1)`,
  NOT a single block — the d=3 M₃ single-block route does NOT generalize → **Route W (per-vertex witness, KT eq.
  6.66) FORCED** → option (a′) (re-derive at base `G₁`, transport the perp to `G−vᵢ`). The panel-correspondence
  de-risk + `panelCorrespondence_supportExtensor` + `candidate_supportExtensor_perp_of_base` made (a′)
  buildable. §(o‴)(I.8.7)/(I.8.8).
- **Chain-induction design-settle + LEAVES 1–4 LANDED 2026-06-20 (axiom-clean).** A recon pair (rows 339–341)
  refuted the leaf-2 per-vertex `group = ±ρ₀` pin → the genuine KT-6.66 mechanism is an eq-(6.44) chain
  induction off the *single* base redundancy (`candidateRow_ac_eq_neg` gives only per-vertex adjacency
  `(ac)-group = −(ab)-group`; KT's `±r` is a chain of `d−2` cancellations anchored at the head). Pinned 5-leaf
  plan (anchor `v₂`); LEAVES 1–4 + the witness-free `chainData_freshEdge_perp_of_baseRedundancy` landed.
  Corrective: `hcol ∀a` is jointly contradictory with `hcomb` for `r̂≠0` → replaced by endpoint id; the deeper
  step derives column-vanishing internally. §(o‴)(I.8.9-SETTLE).
- **ARM CONVERGENCE RECON 2026-06-20 (row 352) → GAP-FOUND.** The 5 deferring leaf-5 slices hid a level
  mismatch: the perp sub-slot needs the edge-grouped redundancy at the CANDIDATE framework, but A-1 supplies it
  only at the BASE — no landed transport. Verdict: the arm does NOT converge from landed pieces; the
  genuinely-new leaf is `chainData_candidateRow_edgeGrouped_transport` (TRANSPORT, no contract change), gated
  on the flagged i=3 edge-alignment de-risk. Detail → design §(o‴)(I.8).
- **i=3 EDGE-ALIGNMENT DE-RISK 2026-06-21 (row 353) → Q2-with-a-twist; transport leaf decomposed
  (`i3_candidateBlock_transport_deRisk`, axiom-clean).** The candidate block at ANY edge `f` = the base block
  at `shiftEdgePerm i f` (`ofNormals_supportExtensor_relabel_perm` for arbitrary `f`; `supportExtensor`
  graph-independent), so A-1's base `hrv` at `evGv j` transports to the candidate `hrv` at
  `(shiftEdgePerm i).symm (evGv j)` — a clean BIJECTIVE re-index, NOT a re-grouping. The flagged
  non-alignment is a NON-ISSUE (chain induction filters by `ev j = edge ⟨i⟩`; non-chain summands vanish via
  `deg_two_split`). NO genuinely-new-math fork (Q3 does not arise). Transport leaf → 3 buildable TRANSPORT
  sub-leaves T-1/T-2/T-3 (signatures design §(o‴)(I.8.10)); ~3–5c to the arm. NO motive/IH/contract change.
- **T-1 LANDED 2026-06-21 (`chainData_candidateRow_edgeGrouped_transport_blocks`, axiom-clean).** The
  de-risked block half of the transport leaf: a pure `∀ j`/all-`i` lift of `i3_candidateBlock_transport_deRisk`
  (`fun j => cd.i3_candidateBlock_transport_deRisk i (evGv j) (hrv j)`). No new math — the anchor was already
  general-`i`/general-edge, so T-1 is the `∀ j`-quantified instantiation against the candidate framework
  `Fva`. NEXT = T-2 (relabel `hcomb`). No friction logged (one-line application).
- **CHAIN-3 cleanup item (2) DONE 2026-06-20 — `finrank_toDualPerp_pair_eq` factored** (`MeetHodge.lean`,
  axiom-clean): the byte-identical ~55-line `finrank {n}^⊥ = k` metric transport (duplicated between (h-3)/(h-4))
  dropped to one shared helper (~110 lines of duplication removed).

### Landed CHAIN-1/3/4/OD-7 bricks (all CLOSED 2026-06-18, axiom-clean; canonical homes = git + design §(f)/(h)/(i)/(j)/(k) + the BlueprintExposition CHAIN-3 entry)

One-line verdicts (closed forward sequence, nothing downstream leans on the internals): **CHAIN-1**
(`Basic.lean`) the eq.-6.62 row-swap + `ιc`-block augment, graph-free over `ScrewSpace k`. **CHAIN-3**
(`Meet`/`MeetHodge.lean`) the `⋀^{d−1}W`-is-a-line duality. **CHAIN-4** (`Claim612.lean`) the discriminator (4d's
`MeetHodge` import did NOT regress the `⋀²ℝ⁴` proofs; 4b stays its own green body). **OD-7** (the four producers
+ both M4 halves general-`k`): verbatim numeral passes (§58 idiom) except LEAF-0
`linearIndependent_normals_of_algebraicIndependent_triple` (genuinely-new); the M4-forget reach-in routes
solely through CHAIN-3 (h-4) + `extensor_update_smul`.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *Match the list recursor to which end the fold's base case sits on: a `foldl`/accumulating fold anchored at
  index 0 inducts with `List.reverseRec`; a `foldr` anchored at the tail wants `cons` + `generalizing`* →
  TACTICS-GOLF § 20 / FRICTION [idiom] *A `List.foldl` whose induction base case lives at index `0`…*.
- *Referencing a `CombinatorialRigidity.Molecular`-namespace lemma from inside a `_root_.Graph.ChainData` decl
  needs its full path including the inner `BodyHingeFramework` namespace* → FRICTION [idiom] *Referencing a
  `CombinatorialRigidity.Molecular`-namespace lemma from inside a `_root_.Graph.ChainData` decl…*.
- *Feeding a partial proof-bearing-index family into a `ℕ → _` total-function-consuming fold: package via `dite`
  + a `dif_pos` `_eq` lemma, then `simp only` (not `rw`) the per-step resolutions* → FRICTION [idiom] *Feeding a
  partial proof-bearing-index family into a `ℕ → _` total-function-consuming fold…*.
- *Composing two `(funLeft σ).dualMap` relabel transports: both contravariant, so the chain is `← comp_apply` →
  `dualMap_comp_dualMap` → `← funLeft_comp`; the `foldl` recurrence (`wstep_foldl_funLeft_eq`) reverses the order,
  landing on the inverse product `funLeft ⇑(∏ swap)⁻¹`* → FRICTION [idiom] *Composing two `(funLeft σ).dualMap`
  relabel transports…*.
- *Recovering the other endpoint of a `Graph.IsLink` from a same-edge / same-left-endpoint pair: use
  `IsLink.right_unique`, not `eq_and_eq_or_eq_and_eq` + disjunct elimination* → FRICTION [idiom] *Recovering the
  other endpoint of a `Graph.IsLink`…*.
- *`rcases … with rfl` / `subst` fails when the equation's subject is a function application (`σ e = edge 0`) —
  name the eq and `rw … at` the link instead* → FRICTION [idiom] *`rcases hmem with rfl | …` / `subst` fails…*.
- *A finite-`i`-cycle permutation over an indexed family `vtx : Fin n → α` as `Equiv.Perm α`: `List.formPerm
  (List.ofFn …)`; `Nodup` via `nodup_ofFn`, action lemmas via `formPerm_apply_lt_getElem` + `Nat.mod_self`* →
  FRICTION [idiom] *A `Fin n → α` indexed-family cycle as an `Equiv.Perm`…*.
- *Dropping the involution from a `ρ = Equiv.swap`-relabel transport to a general `Equiv.Perm ρ`: the `ρ`/`ρ.symm`
  placement is forced — `qρ` keeps forward `ρ`, `endsσρ` + the motion `S∘ρ.symm` flip to `.symm`* → FRICTION
  [idiom] *Dropping the involution from a `ρ = Equiv.swap`-relabel transport…*.
- *`rw [hidx]` on a `getElem` index `l[k]`/`l[k]'h` trips "motive is not type correct" — re-apply the indexing
  lemma at the new index, don't rewrite the index in place* → TACTICS-QUIRKS § 61 (+ variant).
- *A `Fin d`-index relabel proof: destructure `m = m'+1` early so `m-1` reduces to `m'` by `rfl`, and bridge
  `(i.castSucc:ℕ)` to `(i:ℕ)` in `omega` args with `simp only [Fin.val_castSucc]`* → FRICTION [idiom] *A `Fin d`-index
  relabel proof over general `d`…*.
- *`Fin d`-index arithmetic at general `d` (no `+1`): guard `0 < (i:ℕ)` + build `⟨(i:ℕ)-1, _⟩` rather than carry
  `[NeZero d]`* → FRICTION [idiom] *`Fin d`-index arithmetic (general `d`): guard `0 < (i:ℕ)`…*.
- *Index a `Fin`-parametrized `def` by its *minimal* validity bound, not the looser step-/cycle-level bound* →
  FRICTION [idiom] *Index a `Fin`-parametrized `def` by its minimal validity bound…*.
- *Lifting a `Fin (k+2)`-point-family lemma to general `k` may need `[NeZero k]` (the statement is genuinely false
  at `k=0`)* → FRICTION [idiom] *Lifting a `Fin (k+2)`-point-family lemma to general `k`…*.
- *`map_update_smul` on `ExteriorAlgebra.ιMulti` at general grade: `(M := Fin (d+1) → ℝ)` annotation + the `have …`
  term form + `Function.update_eq_self`* → FRICTION [idiom] *`ExteriorAlgebra.ιMulti ℝ n` needs `(M := ...)`…*.
- *The `⧸` quotient notation needs a direct `import Mathlib.LinearAlgebra.Quotient.Basic` even when `Submodule.mkQ`
  resolves by name* → TACTICS-QUIRKS § 60 / FRICTION [mirrored] *`linearIndependent_sumElim_block_swap`…* (Gotcha).
- *To use the mirrored `Finset.univ_orderEmbOfFin` on a `powersetCard` `default` index, surface `↑default = univ`
  with a `rfl`-`have` first* → FRICTION [idiom] *To use the mirrored `Finset.univ_orderEmbOfFin` on a
  `powersetCard`…*.
- *A `-/` inside a docstring word (`grade-/ambient`) closes the doc comment early* → TACTICS-QUIRKS § 57.
- *After lifting an in-place numeral-pinned `def` to implicit `{d}`, a numeral consumer's `omega` mis-atomizes the
  `(d:=3)`-vs-numeral elaborations — use `linarith` / `simpa using h`* → TACTICS-QUIRKS § 58 / FRICTION [idiom]
  *Generalizing an in-place numeral-pinned `def`…*.
- *`Set.powersetCard.compl` inside a hypothesis leaves the target cardinality `m` a stuck metavariable — pin
  `(m := …)` explicitly* → FRICTION [idiom] *`Set.powersetCard.compl` inside a hypothesis…*.
- *`set b := e` folds `e` out of the goal too, so a later `rw`/`simp only [lib_lemma]` whose LHS pattern mentions
  `e` silently fails — drop the `set`* → TACTICS-QUIRKS § 43 (goal-side / library-lemma variant).
- *A `h ▸ t` cast to specialize a `Graph.IsLink` at a `set`-bound vertex fails — fold the goal first with
  `rw [← hX, h]`* → TACTICS-QUIRKS § 43 (`▸`-cast corollary) / FRICTION [idiom] *`h ▸` to specialize a
  `Graph.IsLink` at a `set`-bound vertex…*.
- *A new `InnerProductSpace`/`EuclideanSpace` import poisons a pre-existing exterior-algebra proof to a `whnf`
  timeout — keep the bridge in a `Mathlib/` mirror, house metric-using leaves downstream* → TACTICS-QUIRKS § 59 /
  FRICTION [mirrored] *`EuclideanSpace.inner_eq_basisFun_toDual`…*.
- *`induction h using Submodule.span_induction` fails on an applied membership subject (`n j`) — hoist a
  `∀ y ∈ span, …` helper, induct on the bound `y`* → FRICTION [idiom] *`induction h using Submodule.span_induction`
  fails …*.
- *`EuclideanSpace.equiv` is a `ContinuousLinearEquiv`, not a `LinearEquiv` — round-trips need the
  `ContinuousLinearEquiv.*` forms* → FRICTION [idiom] *`EuclideanSpace.equiv` is a `ContinuousLinearEquiv`…*.
- *Re-orienting a proportionality `c • x = y` into `c⁻¹ • y = x` — use `inv_smul_eq_iff₀ hcne` on the goal, not
  `rw [← hc, smul_smul]`* → TACTICS-GOLF § 19.
- *Recovering a permuted-incidence `Fin n` wrapper from a general `_gen` lemma — feed `_gen` the reordered indexed
  family (`n ∘ ![…]`, LI via `hn.comp _ (by decide)`)* → FRICTION [idiom] *Recovering a permuted-incidence `Fin n`
  wrapper…*.
- *Pushing a functional through `c • x` on an `abbrev`'d carrier (`ScrewSpace k = ⋀^k …`): `rw [map_smul]`
  mis-fires — close with `exact (r.map_smul c _).trans …`* → TACTICS-GOLF § 19 (companion) / FRICTION [idiom]
  *Pushing a functional through a `c • x` on an `abbrev`'d carrier…*.
- *`ChainData.vtx_ne` against a `Fin (d+1)` variable index — prove `≠` via `congrArg Fin.val (vtx_inj ·)`* →
  FRICTION [idiom] *`ChainData.vtx_ne` against a `Fin (d+1)` variable index…*.
- *`hingeRow u v` (a `def`) isn't seen as a bundled map by `map_sum`/injectivity — `rw [hingeRow_eq_dualMap]`
  first* → FRICTION [idiom] *`hingeRow u v` isn't seen as a bundled map…*.
- *A leading `|>.proj` after `∈` has the wrong precedence; `2−1≠sub_self`* → FRICTION [idiom] *A leading `|>.proj`
  …* (sibling note).
- *A standalone `⨅ i ∈ s, ker (proj i)` term needs an explicit `Submodule …` ascription, else `InfSet Type` synth
  failure* → FRICTION [idiom] *A standalone `⨅ i ∈ s, ker (proj i)` term needs an explicit `Submodule …`…*.
