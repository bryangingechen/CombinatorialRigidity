# Phase 23b — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality [CHAIN] (work log)

**Status:** open. CLOSED: CHAIN-1/3/4 + OD-7 (four-producer tail, general-`k`) + CHAIN-2a + the CHAIN-2c-ii
foundation. The `hρGv` algebraic core + chain-induction (LEAVES 1–4) + seed bridge (P3) + slot core + per-edge
perp leaf + STEP-2 scalar perp transport + the STEP 1∘STEP 2 composition `chainData_freshEdge_slot_perp` +
the pre-assembled engine `hρGv` slot `chainData_relabel_arm_hρGv` are all LANDED axiom-clean.
**`chainData_relabel_arm_hρGv` is a CORRECT lemma** (producing `hingeRow vᵢ₊₁ vᵢ₋₁ (−ρ₀) ∈ span (ofNormals
(G−vᵢ) endsσρ qρ)` from A-1's base data + a carried `hφ`@`endsσρ` hyp) — its `hφ`@`endsσρ` slot is the
member-mapping wall (the `hφ` seam). **ROUTE α (per-step selector fold) is INFEASIBLE (§(o‴)(I.8.15)); its
source-production REPLACEMENT was SCOPED (§(o‴)(I.8.16)), the user-approved B1 spike RAN + BLOCKED
(§(o‴)(I.8.17)), and BOTH local fold re-shapes are now ADJUDICATED DEAD (§(o‴)(I.8.18)) — ALL LOCAL `hφ`-seam
routes EXHAUSTED.** The slot core demands `hφ` at the artifact framework `(endsσρ, q)` (relabelled selector +
un-advanced base seed, `Relabel.lean:4671`, re-confirmed against the landed engine/slot-core/A-1 bodies) for
which no KT geometry / rigidity fact exists — a Lean-MODELLING choice (the seed-advancing materialized fold;
KT eqs. 6.60→6.64 use a whole-matrix column-op reframe with TWO frameworks, never this hybrid). The remaining
route is an ASSEMBLY-level re-write of the eq.-(6.60→6.64) realization to KT's whole-matrix form (machinery
BELOW the contract — NO C.0–C.6 / motive change forced) → **USER SCOPE CALL** (A: open the assembly-level
recon, RECOMMENDED; B: carry `hφ@endsσρ` to ENTRY, LIKELY-DEAD; see *Current state*). Once the seam settles +
the arm shell → **CHAIN-2c-iii** `chainData_dispatch` closes 23b green-modulo `hdispatch` (**CHAIN-5 → front
of 23c**). **T-1/T-2 + the orphaned ROUTE-α leaf 1 `shiftEndsAdv`/`_zero`/`_succ` ARE ORPHANED** (confirm-and-
delete at the re-architecture-settle commit).

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

**`hρGv` `hφ`-SEAM — BOTH local fold re-shapes ADJUDICATED DEAD; the unblock is a KT-faithful ASSEMBLY-level
re-write (machinery BELOW the contract) → USER SCOPE CALL, not a contract sign-off (design §(o‴)(I.8.18),
2026-06-21).** The re-architecture design-pass confirmed the artifact premise against the LANDED source (three
levels: the engine `case_III_arm_realization` binds all slots at ONE `(Gv,ends,q)` and `hwmem` forces
`(endsσρ,qρ)`; the slot core `chainData_freshEdge_slot_mem` takes one `ends`, consuming `hφ`@`(ends,q)` and
concluding@`(ends,qρ)`, so hitting the engine's `(endsσρ,qρ)` pins `hφ`@`(endsσρ,q)`; A-1 produces@`(ends,q)`
with the member tied to `(ends e₀)`). So `(endsσρ,q)` — relabelled selector + UN-advanced base seed — is a
genuine Lean-FOLD artifact, NEITHER base `(ends₀,q)` (A-1's output) NOR engine `(endsσρ,qρ)` (conclusion), and
NO KT geometry corresponds to it.

**THE VERDICT (§(o‴)(I.8.18)):** the artifact is a Lean-MODELLING CHOICE — the Lean models KT's row-correspondence
(6.62) as a SEED-ADVANCING FOLD over `d−1` materialized intermediate `ofNormals` frameworks, whereas KT (eqs.
6.60→6.64, pp. 696–697, read end-to-end) has exactly TWO frameworks (`R(G₁,q₁)` and `R(G,pᵢ)`) and reaches its
result by COLUMN OPERATIONS turning `R(G,pᵢ)` into one that CONTAINS `R(G₁,q₁)` as a submatrix, then carrying
the redundancy by in-matrix ROW OPERATIONS — never forming a `(relabelled-selector, un-advanced-seed)` hybrid.
Both local directions are DEAD: **(1)** advance selector+seed in lockstep — DEAD: the per-step gate
(`Relabel.lean:1201`)'s `hends'_off` window `{edge(s+1),edge(s+2)}` cannot accumulate to the cycle `shiftEdgePerm
i` (which moves `edge 0`/`e₀`, both load-bearing surviving links of `G−vᵢ`, outside the window; no
adjacent-swap factorization), and a NON-gate per-step fold degenerates to (2)'s whole-relabel transport.
**(2)** consume `hφ` at `(endsσρ,qρ)` or `(ends₀,q)` directly — DEAD: `(endsσρ,qρ)` has no fixed-member source
(the only landed transport `chainData_bottom_relabel` is the relabel-IMAGE map, which MOVES the member off
`hingeRow v₀ v₂ ρ₀` to `hingeRow v₀ v₁ ρ₀` — the member-mapping wall), and `(ends₀,q)`-start→`(endsσρ,qρ)`-end
requires a selector-advancing fold = direction (1). (The perp half escapes because it transports a graph-free
SCALAR `=0`; `hφ` is a span membership of a FIXED functional — no member-free transport.)

**THE UNBLOCK — an ASSEMBLY-level re-write of the eq.-(6.60→6.64) Lean realization to KT's whole-matrix shape**
(exhibit `R(G₁,q₁)`'s span as a sub-span of `R(G,pᵢ)`'s via the column-op identity, carry the redundancy by
in-matrix row operations, so `hφ` is consumed at the BASE `(ends₀,q)` directly). **This is machinery BELOW the
CHAIN↔ENTRY contract** — the slot core / fold / engine-slot-binding sit beneath the dispatch (C.3) and the
`ChainData` record (C.1), so **NO contract clause (C.0–C.6) and NO motive/IH change is forced** (the I.8.16
"C.0 third lockstep decl" delta was for the now-DEAD source-production fix B1/3b; the whole-matrix re-write
doesn't produce `hφ@endsσρ` at all, so that delta evaporates). It IS a genuinely-new realization architecture,
NOT a next-leaf and NOT pre-dischargeable in docs (cost UNKNOWN — it re-touches the genuinely-new `hφ`-spine;
a recon-first multi-leaf sub-phase, not a 3–5c build). **The user decision is a SCOPE CALL, not a contract
sign-off:** (A) open an ASSEMBLY-level recon to re-shape the realization to KT's whole-matrix form (RECOMMENDED
— the only route that dissolves the artifact at its root), or (B) carry `hφ@endsσρ` as a hypothesis to
arm/dispatch/ENTRY (LIKELY-DEAD: confronts the same wall there, member-bridge likely circular — I.8.12 ROUTE β
/ I.8.15 B3). Every prior LOCAL route is dead: ROUTE α infeasible (I.8.15), transport T-1/T-2/B1 = the
member-mapping wall, source-production A-1 re-thread = B1 does not close (I.8.17), and now BOTH local fold
re-shapes (I.8.18). `chainData_relabel_arm_hρGv` stays a CORRECT carried-hypothesis lemma; the ROUTE-α leaf 1
`shiftEndsAdv` + `_zero`/`_succ` (`Relabel.lean:1731`) + T-1/T-2 are ORPHANED (confirm-and-delete at the
re-architecture-settle commit); `d=3` M₃ unaffected (`i=2`, no `hφ` slot). Once the seam settles + the arm
shell lands (`refine case_III_arm_realization` at `Gv=G−vᵢ`, `endsσρ`, `qρ`, `(a,b)=(vᵢ₊₁,vᵢ₋₁)`, `ρ:=−ρ₀`;
`hwmem ← chainData_bottom_relabel`) → **CHAIN-2c-iii** `chainData_dispatch`.

**ROUTE α STAYS INFEASIBLE (design §(o‴)(I.8.15), 2026-06-21 — OPTION B, Lean-grounded; the per-step selector
fold is the wrong tool).** The membership fold's per-step gate (`Relabel.lean:1201`, `hends'_off`) permits each
step to move the selector ONLY at `edge(s+1)`/`edge(s+2)`, so the accumulated selector can differ from `ends₀`
ONLY on `{edge 1,…,edge i}`. But `shiftEdgePerm i` (the `(i+2)`-CYCLE `formPerm [edge 0, e₀, edge i, edge 1, …,
edge(i−1)]`) moves `edge 0`/`e₀` (both outside that set), has NO adjacent-swap factorization, and the
discrepancy is load-bearing on `G−vᵢ` (`edge 0` survives there). ROUTE α was a category error (reaching a cycle
by adjacent transpositions). All 5 ROUTE-α leaves abandoned.

**Why the row-354 T-1/T-2/T-3 plan was MIS-TARGETED (the 2nd level/shape mismatch; design §(o‴)(I.8.11)).**
The consumer `chainData_freshEdge_perp_of_baseRedundancy` (`Relabel.lean:4311`) pins THREE hyps at
INCOMPATIBLE levels: `hcomb` framework-free with RHS HARDCODED `hingeRow (vtx 0)(vtx 2) ρ₀` (BASE vertices,
feeding LEAF-4 whose `ab₁/ab₂ = vtx 0/vtx 2` is rigid) AND `hrv` at the CANDIDATE framework. Feeding the
re-indexed family (T-1/T-2): T-1's `hrv` matches, but T-2's `hcomb` LHS becomes `hingeRow (σ.symm v₀)(σ.symm
v₂) ρ₀ = hingeRow v₀ v₁ ρ₀` (Lean-verified `σ.symm v₀ = v₀`, `σ.symm v₂ = v₁` ∀ `i ≥ 2`) ≠ the consumer's
`hingeRow v₀ v₂ ρ₀`. Feeding un-relabelled: `hcomb`/`hlink` match but `hrv` wants candidate-block at the SAME
edge, which `ofNormals_supportExtensor_relabel_perm` relates only to base-block at the DIFFERENT edge `σ_e f`.
So neither feeds the consumer. KT-source check (eqs. 6.62/6.66/6.67, p.696–698): KT works ENTIRELY at the base
`(G₁,q₁) = G−v₁`; the candidate enters only via the row-correspondence iso `ρᵢ`, never as a separate
`ofNormals (G−vᵢ)` framework — vindicating STEP 1's base-index call.

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
- **`chainData_freshEdge_perp_of_baseRedundancy`** (`Relabel.lean:4311`) — witness-free per-edge perp: for any
  surviving edge (`2 ≤ s < d`), `ρ₀ ⊥ Fva.supportExtensor (edge s)` from the edge-grouped base redundancy.
  Consumes `hlink`/`hcomb` (framework-free, RHS hardcoded `hingeRow (vtx 0)(vtx 2) ρ₀`) + `hrv` at the framework
  `Fva = ofNormals (G−vᵢ) ends qρ` (free `ends`/`qρ`). Mechanism = LEAF 4's `group = −ρ₀` +
  `edgeGroup_acolumn_mem_block` + `mem_hingeRowBlock_iff`. **CORRECT call site (design §(o‴)(I.8.11)) = base
  index `i := ⟨1⟩`** (then `Fva` = base `G−v₁`, A-1's output feeds it DIRECTLY — STEP 1 of the corrected route).
- **`chainData_freshEdge_perp_transport_base_to_candidate`** (`Relabel.lean`, STEP 2, LANDED 2026-06-21,
  axiom-clean) — the single-scalar per-edge perp transport: a base perp at `(if s=0 then e₀ else edge(s+1))`
  (arbitrary graph `Gb`) → the candidate framework's perp at `edge s` (the relabelled `endsσρ`/`qρ` forms).
  `ofNormals_supportExtensor_relabel_perm` (the support-extensor coincidence) + the `shiftEdgePerm` edge action
  (interior `s≥1` / head `s=0`) + supportExtensor graph-independence.
- **`chainData_freshEdge_slot_perp`** (`Relabel.lean`, STEP 1∘STEP 2 composition, LANDED 2026-06-21,
  axiom-clean) — the exact `hperp s` shape `chainData_freshEdge_slot_mem` consumes. From A-1's base data
  (`hlink`/`hrv`/`hcomb`/`hdeg1`/`hρe₀`, all at the BASE `G−v₁`) it produces the candidate-`i` perp
  `ρ₀ ⊥ Fva.supportExtensor (edge s)` for any surviving `s+1<i`: STEP 1 at base index `⟨1⟩` (interior `s≥1`)
  or `hρe₀` (head `s=0`) → STEP 2. The single call the arm's `hρGv` slot makes for the whole perp obligation.
- **`chainData_relabel_arm_hρGv`** (`Relabel.lean`, STEP 3 `hρGv` slot, LANDED 2026-06-21, axiom-clean) —
  the pre-assembled engine `hρGv` slot at candidate `i`: `hingeRow vᵢ₊₁ vᵢ₋₁ (−ρ₀) ∈ span (ofNormals (G−vᵢ)
  endsσρ qρ)`, exactly `case_III_arm_realization`'s `hρGv` (M₃ sign `−ρ₀`). Composes `hingeRow_swap` → slot
  core `chainData_freshEdge_slot_mem` → P3 seed bridge → `chainData_freshEdge_slot_perp` per surviving edge.
  **GATES ON THE `hφ` SEAM:** takes the base redundancy `hφ` at the RELABELLED `endsσρ` base (the slot core's
  one-selector framing) + the perp data at the UN-relabelled `ends₀`. A correct lemma, NOT vacuous — but its
  `hφ`@`endsσρ` slot is the member-mapping wall (design §(o‴)(I.8.12)). The shell does NOT supply `hφ`@`endsσρ`
  by transport — there is no clean leaf, and **ROUTE α (the per-step fold to re-architect the slot core onto
  `hφ`@`ends₀`) is INFEASIBLE** (§(o‴)(I.8.15)); the route is under user/coordinator adjudication.
- **`i3_candidateBlock_transport_deRisk`** (`Relabel.lean:4383`) + **`ofNormals_supportExtensor_relabel_perm`**
  (`Relabel.lean:63`) — STAND: the support-extensor relabel identity `candidate.supp f = base.supp (shiftEdgePerm
  i f)`. STEP 2 reuses this identity ONCE (applied to a single perp), so it stays load-bearing; only its
  all-`i`/`∀ j` *family*-lift (T-1) is orphaned.
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
- **Orphaned-for-the-arm (confirm-and-delete at the arm-build commit):** **the ROUTE-α leaf 1**
  `Graph.ChainData.shiftEndsAdv` + `shiftEndsAdv_zero`/`shiftEndsAdv_succ` (`Relabel.lean:1731`) — the
  abandoned per-step selector accumulator (ROUTE α INFEASIBLE, §(o‴)(I.8.15); the per-step fold can't reach the
  cycle edge relabel, so this def has no consumer). **T-1/T-2**
  `chainData_candidateRow_edgeGrouped_transport_{blocks,comb}` (`Relabel.lean:4427`/`:4464`) — the row-354
  family-transport plan, MIS-TARGETED vs the consumer (design §(o‴)(I.8.11); the corrected route transports a
  single scalar perp, never the family). T-3 (`…_transport_links`) was never built → MOOTED. (The anchor
  `i3_candidateBlock_transport_deRisk` + `ofNormals_supportExtensor_relabel_perm` STAND — STEP 2 reuses them.)
  The split→split `rigidityRow_chainData_relabel` / `rigidityRow_relabel_perm` (rows 288/291, wrong graph level,
  §(o‴)(I.5)); the candidate→base T-W9a fold `shiftBodyList_foldr_…` (wrong orientation, H.10); the two block
  bricks `rigidityRow_relabel_to_block{,_swap}` (the assembly inlined the wrap-block); `ofNormals_relabel_perm`
  + the binary `…comp…` (docstring-referenced — sync on delete); the per-`i`-W6b
  `chainData_split_realization`/`_w6b_gates` (Fix B; re-check at 2c-iii). **DELETED 2026-06-19:** the 5-decl W9b
  per-body chain (§(o‴)(I.1), machine-refuted).

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
      (the genuinely-new relabel arm — KT's `ρᵢ` is a `(i−1)`-cycle): foundation LANDED; FIX-FORK SETTLED. The
      perp slot was ROUTE-SETTLED (STEP-1-at-base + STEP-2 scalar transport, both LANDED; T-1/T-2 ORPHANED).
      **The `hρGv` slot `chainData_relabel_arm_hρGv` LANDED but exposed the `hφ` SEAM** — its slot core wants
      the base redundancy at the artifact `(endsσρ, q)`, A-1 gives it at the base `(ends₀, q)`. **ALL LOCAL
      ROUTES DEAD:** ROUTE α infeasible (§(o‴)(I.8.15)); the `hφ`-at-source B1 spike BLOCKED (§(o‴)(I.8.16/17));
      and BOTH local fold re-shapes adjudicated DEAD (§(o‴)(I.8.18) — (1) selector+seed lockstep blocked by the
      gate's edge window; (2) `hφ` at `(endsσρ,qρ)`/`(ends₀,q)` directly = the member-mapping wall / direction
      (1)). **The artifact `(endsσρ,q)` is a Lean-MODELLING choice** (seed-advancing materialized fold; KT eqs.
      6.60→6.64 use a whole-matrix column-op reframe). **The unblock = an ASSEMBLY-level re-write to KT's
      whole-matrix shape, machinery BELOW the contract (NO C.0–C.6 / motive change forced; the I.8.16 C.0
      delta evaporates with the dead source-production fix).** **NEXT = USER SCOPE CALL** (A: open the
      assembly-level recon, RECOMMENDED; B: carry `hφ@endsσρ` to ENTRY, LIKELY-DEAD — see *Current state* /
      *Hand-off*). Then arm shell + **2c-iii** `chainData_dispatch`. d=3 M₃ = `i=2` (no `hφ` slot, no general
      fold) — zero-regression unaffected.
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

**The single authoritative next-step is in *Current state* above: BOTH local fold re-shapes of the `hφ`-seam
are ADJUDICATED DEAD (design §(o‴)(I.8.18)); the unblock is a KT-faithful ASSEMBLY-level re-write of the
eq.-(6.60→6.64) realization — machinery BELOW the contract → USER SCOPE CALL (A: open the assembly-level
recon, RECOMMENDED; or B: carry `hφ@endsσρ` to ENTRY, LIKELY-DEAD).** The §(I.8.18) design-pass re-confirmed
the artifact premise against the LANDED engine / slot-core / A-1 bodies (not inherited): the slot core / arm
demands `hφ` at the **artifact framework `(endsσρ, q)`** (relabelled selector + un-advanced BASE seed,
`Relabel.lean:4671`), forced by the engine's single-`(Gv,ends,q)` slot-binding (`hwmem` pins `(endsσρ,qρ)`)
× the slot core's one-`ends` parametricity. KT (eqs. 6.60→6.64, pp. 696–697) NEVER forms this hybrid — it
column-operates `R(G,pᵢ)` to CONTAIN `R(G₁,q₁)` as a submatrix and carries the redundancy by in-matrix row
ops; the Lean's `(endsσρ,q)` is the start state of its SEED-ADVANCING materialized FOLD (a Lean-modelling
choice). **Direction (1)** (selector+seed lockstep) DEAD: the per-step gate's `{edge(s+1),edge(s+2)}` window
can't accumulate to the `edge 0`/`e₀`-moving cycle `shiftEdgePerm i`. **Direction (2)** (consume `hφ` at
`(endsσρ,qρ)` / `(ends₀,q)` directly) DEAD: the only landed transport moves the member (the member-mapping
wall), and `(ends₀,q)`-start→`(endsσρ,qρ)`-end = direction (1). EVERY local route is now exhausted (ROUTE α
infeasible §(o‴)(I.8.15); transport T-1/T-2/B1 = the wall §(o‴)(I.8.12); A-1 re-thread B1 = does not close
§(o‴)(I.8.17); both fold re-shapes §(o‴)(I.8.18)). **The remaining route is an ASSEMBLY-level re-shape of the
eq.-(6.60→6.64) realization to KT's whole-matrix form** (`hφ` consumed at the base `(ends₀,q)` directly).
**NO contract clause (C.0–C.6) and NO motive/IH change is forced** — the slot core / fold / engine-slot-binding
are infrastructure beneath the dispatch (C.3) and the `ChainData` record (C.1); the I.8.16 "C.0 third lockstep
decl" delta was for the now-DEAD source-production fix and evaporates. It IS genuinely-new realization
architecture (cost UNKNOWN, recon-first multi-leaf sub-phase, NOT a 3–5c build), so the user decision is a
**SCOPE CALL** (A vs B), NOT a contract sign-off. `chainData_relabel_arm_hρGv` stays a CORRECT
carried-hypothesis lemma; the ROUTE-α leaf 1 `shiftEndsAdv`/`_zero`/`_succ` (`Relabel.lean:1731`) + T-1/T-2 are
ORPHANED (confirm-and-delete at the re-architecture-settle commit); d=3 M₃ unaffected (`i=2`, no `hφ` slot).
Once the seam settles + the arm shell lands (`refine case_III_arm_realization` at `Gv=G−vᵢ`, `endsσρ`, `qρ`,
`(a,b)=(vᵢ₊₁,vᵢ₋₁)`, `ρ:=−ρ₀`; `hwmem ← chainData_bottom_relabel`, the M₃-template discriminator/removeVertex
slots) → **2c-iii** `chainData_dispatch` (replaces `case_III_candidate_dispatch`) → **CHAIN-5** (in 23c).
Audit trail: design §(o‴)(I.8.18) (both fold re-shapes DEAD + KT whole-matrix cross-check + scope call A/B),
(I.8.17) (B1 BLOCKED + artifact root cause), (I.8.15)/(I.8.16) (ROUTE α + A-1-scope, both dead), (I.8.12) (the
member-mapping wall).

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
- **PERP-SLOT route SETTLED + LANDED 2026-06-21 (axiom-clean; rows 352–360, design §(o‴)(I.8.10)/(I.8.11)).**
  The 2nd level/shape mismatch (the perp slot wanted the redundancy at a framework A-1 gives only at the base):
  the row-354 T-1/T-2/T-3 *family* transport was MIS-TARGETED (re-indexed breaks `hcomb`: `σ.symm v₂ = v₁ ≠ v₂`;
  un-relabelled breaks `hrv`). CORRECT route (KT works entirely at the base): the LANDED perp leaf
  `chainData_freshEdge_perp_of_baseRedundancy` at base index `⟨1⟩` (STEP 1, no transport) + ONE scalar perp
  transport `chainData_freshEdge_perp_transport_base_to_candidate` (STEP 2, base@`edge(s+1)` → candidate@`edge s`,
  via `ofNormals_supportExtensor_relabel_perm` — support extensors are graph-independent) composed as
  `chainData_freshEdge_slot_perp`. T-1/T-2 ORPHANED; the anchor `i3_candidateBlock_transport_deRisk` +
  `ofNormals_supportExtensor_relabel_perm` STAND. The `hρGv` slot `chainData_relabel_arm_hρGv` then assembled
  (`hingeRow_swap` → slot core → P3 → the perp composition). Friction: `show … from hid` for an omega side-goal
  over `↑(⟨(i:ℕ),_⟩ : Fin (cd.d+1))` (TACTICS-QUIRKS § 63).
- **`hφ`-SEAM ROUTE TRAIL — ALL LOCAL ROUTES DEAD (design §(o‴)(I.8.12)–(I.8.17); one-line verdicts, full
  Lean-grounded arcs in the design doc + git).** The slot core demands `hφ` at the artifact `(endsσρ,q)`, A-1
  gives `(ends₀,q)` (the member-mapping wall). ROUTE α (per-step selector fold) INFEASIBLE — the gate
  (`Relabel.lean:1201`) can't accumulate to the cycle `shiftEdgePerm i` (I.8.12/I.8.15); `hφ`-at-source
  (re-thread the W6b producer to output `hφ@endsσρ`, the 3b shape) SCOPED feasible-but-contract-touching
  (I.8.16) then its B1 span re-derivation spike BLOCKED (I.8.17). The live verdict is the I.8.18 entry below.
- **SLOT-CORE/ASSEMBLY RE-ARCHITECTURE ADJUDICATION 2026-06-21 (design §(o‴)(I.8.18); Lean-grounded, docs-only)
  — VERDICT: BOTH local fold re-shapes DEAD; the unblock is a KT-faithful ASSEMBLY-level re-write, machinery
  BELOW the contract → USER SCOPE CALL (A: assembly recon RECOMMENDED; B: carry to ENTRY, LIKELY-DEAD).**
  Re-confirmed the artifact premise against the LANDED engine/slot-core/A-1 (the engine's single-`(Gv,ends,q)`
  slot-binding × the slot core's one-`ends` parametricity force `hφ`@`(endsσρ,q)`). (1) selector+seed lockstep
  — DEAD (gate's `{edge(s+1),edge(s+2)}` window ≠ the `edge 0`/`e₀`-moving cycle `shiftEdgePerm i`); (2) `hφ` at
  `(endsσρ,qρ)`/`(ends₀,q)` directly — DEAD (the member-mapping wall / = (1)). KT eqs. 6.60→6.64 use a
  whole-matrix column-op reframe (TWO frameworks, never the hybrid); the artifact is the Lean's seed-advancing
  materialized fold. The re-architecture forces NO C.0–C.6 / motive change (infra below dispatch C.3 + record
  C.1; the I.8.16 C.0 delta evaporates).
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
- *`omega` can't use `hid : (i:ℕ)<m` on a side-goal over `↑(⟨(i:ℕ),_⟩ : Fin (m+1))` — it atomizes
  `Fin.val (Fin.mk …)` distinctly from `(i:ℕ)`; force the defeq with `show … from hid`* → TACTICS-QUIRKS § 63
  / FRICTION [idiom] *`omega` can't use `hid : (i:ℕ) < m` to close a side-goal over `↑(⟨(i:ℕ),_⟩…)`…*.
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
