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
> away from. **LEAF-3 proper is now LANDED** (the discriminator-firing producer
> `exists_shared_redundancy_and_matched_candidate`, 2026-06-24, axiom-clean) — it fires
> `chainData_split_w6b_gates` + the discriminator at the **BASE split** ONCE → shared `ρ₀`, base `(ab)`
> annihilation, matched candidate `i`/`hgate`/`n'`, W6b base bundle (`w`/`hw`/`hwmem`/`λ`-witness).
> **LEAF-4 step (i′) the WIDENING is now LANDED too** (2026-06-24): `chainData_split_w6b_gates` re-exposes
> the W6b producer's edge-grouped `G_v`-row form (KT eq-6.66, previously discarded as `_hedgeGv`) — the
> all-edge data step (i) regroups at the degree-2 vertex.
> **THE CONJECTURE-CRUX LEAF IS LANDED (2026-06-24, axiom-clean, build/lint/warning-clean):
> `Graph.ChainData.baseRedundancy_perp_interior_reproduced_panel`** (`Relabel/ForkedArm.lean`, right
> before `interior_hρe₀_of_splice_perp`). The eq-6.66 redundancy carry to the spliced candidate edge —
> `ρ₀ ⊥ panelSupportExtensor (q(vtx (i+1),·)) (q(vtx i,·))` for `2 ≤ (i:ℕ) < cd.d` — is exactly the
> `hsplice` the LANDED bridge consumes, so the interior-`hρe₀` leaf is now closed end-to-end (crux +
> bridge). **The whole (A)-vs-(B) carry framing was a non-problem.** The carry "across `vᵢ`" needs NO
> inductive chain / per-vertex witness producer / Grassmann–Cayley meet: the LANDED value-read
> `interior_group_acolumn_eq_neg_baseRedundancy` (framework-free, the `edge i`-group's `vtx i`-column =
> `−ρ₀`) fires at the candidate index `i` itself (it only needs `2 ≤ i < d`, never `G − vᵢ`), and
> `edgeGroup_acolumn_mem_block` puts that column in `(ofNormals Gw ends q).hingeRowBlock (edge i)` for
> the base framework (the block reads only `ends`/`q` — the GRAPH is irrelevant, so the `vᵢ`-incidence
> that excluded `edge i` from `G − vᵢ`'s framework is a non-issue when reading the BASE panel). Then
> `−ρ₀ ∈ block ⟹ ρ₀ ∈ block ⟹ ρ₀ ⊥ panelSupportExtensor` (`ofNormals_supportExtensor_eq_panel_of_ends`).
> A clean replay of `chainData_freshEdge_perp_of_baseRedundancy` one index deeper. **ORPHAN-CONFIRMED:
> `baseRedundancy_group_acolumn_perp` (b23e50e) + the per-step column subtree are OFF the path — the crux
> never touches them; confirm-and-delete at LEAF-5/CHAIN-5 cleanup.**
>
> **PHASE STOP — a FUNDAMENTAL RECONSIDERATION is needed (surfaced to the user 2026-06-24). ALL THREE routes
> (A, B′, A′) for the general-`d` interior-`hρGv` rank certification are REFUTED; the `hρGv` member-mapping
> wall (§I.8.18–20, intrinsic to KT) is unavoidable (design §I.8.24(4.17)–(4.20), four spikes,
> kernel-confirmed).** The interior `hρe₀` half of LEAF-4 step (ii) is CLOSED (crux + bridge). The
> `hWS`/rank-certification half is BLOCKED: §(4.18) the static-`W` re-shape (A) is impossible (`hWS ∧ hWcard ∧
> hW` can't coexist — the redundancy carry is a row THROUGH `vᵢ`); §(4.19) the operated-frame block-rank (B′)
> can't separate the non-pure-`vᵢ` `±r` corner from the base; §(4.20) (A′) re-derive-in-the-operated-frame
> reduces (kernel PROBE 1) to `chainData_relabel_arm_hρGv`'s `hφ` slot = the member-fixed base redundancy in
> `span(endsσρ)`, which the only relabel transport provably MOVES off-member (PROBES 2–3: `vtx2↦vtx1`, and the
> moved member = the fixed one forces `ρ₀=0`) — it IS the member-mapping wall, no framework-free escape (`hφ`
> is a span MEMBERSHIP, not the `hρe₀`-style annihilation that dissolved). **The W9a *generalization* is
> LANDED; the wall is ONLY the `hφ` slot.** The `±r`-corner reformulation escapes `hρGv` at the ROW/membership
> level (`hg`/`hLI` via `hρe₀`, LANDED, sound) but NOT in the general-`d` RANK CERT. **The KT-§6.4.2
> source recon (§(4.21), primary-PDF, HIGH confidence) UPHELD + SHARPENED the STOP:** KT's paper certifies the
> rank by whole-matrix bookkeeping with the member MOVING (block rank-additivity 6.64–6.65 + union-dimension
> 6.67; `r` carried `=±r` via 6.66), NOT row-membership — but KT's "member moves" is realized IN LEAN exactly
> as the relabel-image submatrix containment (6.62), which IS the wall (KT hides it as a one-line "not
> difficult to see"). So there is **NO missed KT route** — (B′)/(A′) ARE KT's rank-count, kernel-dead. **NEXT =
> a fresh-session DESIGN+BUILD of the genuinely-new §I.8.21(α) abstract block-rank-additivity-over-a-relabel
> infra** (cost-unknown): formalize KT's "submatrix containment" (6.61) as a MATRIX-LEVEL rank-preserving block
> embedding (induced by `ρᵢ` + the column op), reading `±r` (6.66) off as a covector identity in `ℝ^D`, so the
> rank is counted the way KT counts it on paper — NEVER materialising a fixed-member row membership (the
> §(4.18) de-risk's generic block-rank lemma consumes a scalar `hWS`/`hW` membership at `Candidate.lean:1606`,
> which is what forces the wall; the new lemma carries the whole base matrix as a BLOCK). **Alternatively (user
> decision)** pause the crux step and advance ENTRY (23d) / other phases. **ALL LANDED leaves stay in tree**
> (sound; reusable). **Do NOT** re-attempt the four dead route families (§I.8.18–(I.8.20)), re-litigate the
> fork, re-attempt (A)/(B′)/(A′), or re-hunt for a "missed KT route" (the recon settled there is none). See
> *Current state* + *Hand-off* + design §I.8.24(4.17)–(4.21).

## Current state

**LEAF-4 step (ii)'s per-member `hS` router is LANDED (2026-06-24, axiom-clean, build/lint/warning-clean):
`Graph.ChainData.bottomRelabel_image_mem_span_caseIIICandidate`** (`Relabel/ForkedArm.lean`, right after
`interior_hρe₀_of_splice_perp`). This is the §(4.4)(β) hard part of LEAF-4 (c) — the substantive
per-member case-split feeding LEAF-2's `hS`. It takes one `chainData_bottom_relabel`-output disjunction
(the relabel image `(funLeft (shiftPerm i.castSucc).symm).dualMap φ` is a genuine rigidity row of the
seed framework `ofNormals (G − vᵢ) endsσρ qρ`, OR the reproduced-slot block tag
`hingeRow (vtx i.succ) (vtx (i−1).castSucc) ρ'` with `ρ' ⊥` the candidate fresh pair's panel) and routes
it into `span (caseIIICandidate G endsσρ qρ e_a e_b (qρ(a,·)) n' (qρ(b,·)) 0).rigidityRows`: the genuine
branch destructures the rigidity-row membership, takes the surviving link's edge off both `vᵢ`-incident
candidate slots `{e_a, e_b}` (via the dispatch-supplied `heab_off`), transfers the block membership
across the graph (`ofNormals` support is graph-independent: `toBodyHinge_supportExtensor` +
`ofNormals_normal`/`_ends`), and `Submodule.subset_span`'s through
`hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link` — this GENUINE branch is sound + reusable.
The REPRODUCED branch is **MIS-TARGETED** (design §I.8.24(4.17), spike-confirmed 2026-06-24): it routes the
wrap-edge tag `hingeRow (vtx i.succ) (vtx (i−1).castSucc) ρ'` (endpoints OMIT `vᵢ`) through
`hingeRow_mem_caseIIICandidate_rigidityRows_reproduced`, which forces the carried
`hG_eb_cand : G.IsLink e_b (vtx i.succ) (vtx (i−1).castSucc)` — UNSATISFIABLE, it contradicts the consumer's
required `hG_eb : G.IsLink e_b v b` (`v = vtx i.castSucc ≠ vtx i.succ`; `IsLink.right_unique` + `vtx_inj`).
The leaf type-checks only because `hG_eb_cand` is a carried hypothesis; it cannot be wired. **So LEAF-4 step
(ii)'s `hWS` is BLOCKED AS SHAPED.** Both `±r`-corner wall-escape routes are now REFUTED: §(4.18) option (A)
(static-`W` re-shape) is INFEASIBLE (no `W` satisfies `hWS ∧ hWcard ∧ hW`; the redundancy carry is a row
THROUGH `vᵢ`); §(4.19) option (B′) (operated-frame block-rank) is INFEASIBLE (the `±r` corner's surviving
discriminator `single a`=`−ρ₀` is uncontrolled in the base, and the `±r` corner is not pure-`vᵢ`-column so it
can't join the d=3 separator); §(4.20) option (A′) (re-derive in the operated frame, producing `hρGv`
generically) is INFEASIBLE — it reduces (kernel PROBE 1) to `chainData_relabel_arm_hρGv`'s `hφ` slot = the
member-fixed base redundancy in `span(endsσρ)`, which the only relabel transport provably MOVES off-member
(it IS the member-mapping wall; no framework-free escape — `hφ` is a span membership, not the `hρe₀`-style
annihilation). **All four spikes converge: the `±r`-corner reformulation escapes `hρGv` at the ROW/membership
level but NOT in the general-`d` RANK CERTIFICATION; the member-mapping wall is unavoidable.** The KT-§6.4.2
source recon (§(4.21)) UPHELD + SHARPENED this: KT's paper counts the rank by whole-matrix block-additivity
with the member MOVING (NOT row-membership), but that "member moves" is realized in Lean as the relabel-image
submatrix containment = the wall, so there is **NO missed KT route**. **Next = a fresh-session DESIGN+BUILD of
the genuinely-new §I.8.21(α) abstract block-rank-additivity-over-a-relabel infra** (matrix-level submatrix
containment 6.61, `±r` as an `ℝ^D` covector identity 6.66 — never a fixed-member row membership; cost-unknown),
**or** (user decision) pause the crux step and advance ENTRY/ASSEMBLY. See the top-of-note *Next commit* block +
*Hand-off* + design §I.8.24(4.17)–(4.21). The router's reproduced branch is dead (do NOT patch in place); the
genuine branch survives; the corner cert (`±r` via `hρe₀`) is sound + `W`-independent; ALL LANDED leaves stay
in tree (reusable under a re-architected rank cert).

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

**LEAF-3 proper is LANDED (2026-06-24, axiom-clean, build/lint/warning-clean): the discriminator-firing
producer `PanelHingeFramework.exists_shared_redundancy_and_matched_candidate`** (`CaseIII/Realization.lean`,
after `exists_chainData_discriminator_pick`). It takes the base split `(v, a, b, cd.e₀)` + the W6b
prerequisites (`hav`/`hbv`/`hba`/`haG`/`hbG`/`he₀`/`h622lb`/`hdef_Gab`/`hsplitGP`) — the same shape
`chainData_split_realization` / the frozen dispatch contract carry — and (i) fires
`chainData_split_w6b_gates` ONCE → the shared `ρ₀ ≠ 0`, the base `(ab)` annihilation
`ρ₀(panelSupportExtensor (q(a,·)) (q(b,·))) = 0`, the bottom family `w`/`hw`/`hwmem`, the eq-6.52
`λ`-grouped `(ab)`-witness `ρ₀ = Σ λ • rab`, and the seed alg-indep `AlgebraicIndependent ℚ q`; (ii) fires
`exists_chainData_discriminator_pick` off the same `q`/`ρ₀`, fed `cd.candidatePanel hn` /
`cd.candidatePanel_injective hn` → the matched candidate `i := Fin.cast (cd.d_eq_kAdd hn).symm u`, the
transversal `n'`, and the gate `ρ₀(panelSupportExtensor (q(cd.candidateVtx i,·)) n') ≠ 0` (the
`candidatePanel_apply` bridge rewrites `candidatePanel hn u` → `candidateVtx i`). The matched `i` is
**arbitrary** (no interiority claim — the discriminator may pick the base panel at `u=0`); the LEAF-5
router case-splits on `(i : ℕ)`. **Supporting additive change:** `chainData_split_w6b_gates` gained an
output conjunct `AlgebraicIndependent ℚ q` (already in scope from `hsplitGP`; the discriminator-pick
prerequisite — the only landed-lemma touch, its one consumer `chainData_split_realization` took a `_`
binder).

**LEAF-4 step (i′) — the WIDENING — is LANDED (2026-06-24, axiom-clean, build/lint/warning-clean).**
`chainData_split_w6b_gates` now ALSO emits the **edge-grouped `G_v`-row form** of the candidate (KT
eq-6.66): an existential `(nGv, cGv, evGv, uvGv, vvGv, rvGv)` with each summand a `(G−v)`-link
(`(G.removeVertex v).IsLink (evGv j) (uvGv j) (vvGv j)`) + a block row (`rvGv j ∈ hingeRowBlock (evGv j)`)
and `hingeRow a b ρ = ∑ⱼ cGv j • hingeRow (uvGv j) (vvGv j) (rvGv j)`. This was ALREADY computed inside the
W6b producer `exists_candidateRow_bottomRows_of_rigidOn` (`Candidate.lean:439–445`) but discarded by the
wrapper (`_hedgeGv`); the widening re-exposes it through both chain-order normalization branches (the `(b,a)`
branch via `hingeRow_swap a b (-ρ)` + `neg_neg`). Purely additive (no motive/IH/contract change); the two
consumers `chainData_split_realization` + `exists_shared_redundancy_and_matched_candidate` took a `_` binder.
This is the all-edge eq-6.52/6.66 data the interior-`hρe₀` leaf regroups at the degree-2 vertex.

**LEAF-4 step (i) column-projection component — the GENERAL-`i` INTERIOR DEGREE-2 COLUMN-SUP
PROJECTION `Graph.ChainData.freshEdge_interior_acolumn_sup` — is LANDED (2026-06-24, axiom-clean,
build/lint/warning-clean).** `Relabel/Arm.lean`, right after the d=3 de-risk gate
`i3_freshEdge_interior_acolumn_sup_deRisk` it generalizes. At a candidate `i : Fin (cd.d+1)` and a
*genuinely-surviving* interior chain vertex `vtx (s+1)` (the strict boundary `s + 2 < (i:ℕ)`, so
BOTH neighbours `vtx s`, `vtx (s+2)` survive `removeVertex (vtx i)`), a span member
`φ ∈ span Fva.rigidityRows` has its `vtx (s+1)`-column landing in the **two-edge sup**
`block (edge s) ⊔ block (edge (s+1))`. A direct application of the framework-level primitive
`acolumn_mem_hingeRowBlock_sup_of_span_rigidityRows`, degree-2 closure from the chain helper
`shiftBody_deg_two`, distinctnesses from `vtx_ne`. **The `s + 2 < i` boundary is load-bearing** (NOT
`s + 1 < i`): at `i = s + 2` the successor neighbour is removed and `vtx (s+1)` is degree-ONE (the
d=3-base / `M₃` single-block situation). This is the column-projection brick the interior-`hρe₀`
leaf's eq-6.52 regrouping at the degree-2 vertex `vᵢ` threads through. Zero blast radius (no live
caller yet).

**LEAF-4 step (i) sub-step (1) regrouping column-algebra core — the POSITIVE INTERIOR DEGREE-2
TWO-GROUP COLUMN DECOMPOSITION `Graph.ChainData.interiorGroup_acolumn_two_group_decomp` — is LANDED
(2026-06-24, axiom-clean, build/lint/warning-clean).** `Relabel/ChainColumn.lean`, right after the
conditional `= −` sibling `interiorGroup_acolumn_adjacency` it complements. The *unconditional*
structural identity: at an interior degree-2 chain vertex `a = vtx i.castSucc` (`0 < i`), the
`vᵢ`-column of the full edge-indexed combination `g = ∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` (each
summand a genuine `G`-link `evⱼ`) is the *sum* of its two incident chain-edge groups' `vᵢ`-columns —
NO `hcol = 0` premise (its sibling needs vanishing to conclude `= −`; this one is the raw split). It
isolates exactly the two-group structure `candidate_perp_two_incident_supportExtensors` consumes,
with that consumer's `grest` supplied as the **zero** functional (non-incident summands carry no
`vᵢ`-column, `hingeRow_comp_single_off`). This is the column-algebra heart of §I.8.24(4.15)
sub-step (1)'s regrouping of the LANDED widening's flat all-edge form (`chainData_split_w6b_gates`'s
`G_v`-row conjunct, KT eq-6.66) at the degree-2 split vertex `vᵢ`: it lets the carry's per-step
`candidate_perp_two_incident_supportExtensors` call construct its `hcol`/`hrest` from the flat
widening rather than assume them. Proof is a clean replay of `interiorGroup_acolumn_adjacency`'s
index-set manipulation (`_eq_incident` + `deg_two_split` + `edge_inj` filter-congr) without the
vanishing hypothesis. Zero blast radius (no live caller yet).

**LEAF-4 step (i) the PER-STEP SINGLE-VERTEX CARRY LEMMA is LANDED (2026-06-24, axiom-clean,
build/lint/warning-clean) — the genuinely-new annihilation-level content the anti-shrink note blessed.**
`Graph.ChainData.baseRedundancy_group_acolumn_mem_inf` + its `supportExtensor`-perp restatement
`baseRedundancy_group_acolumn_perp` (`Relabel/ChainColumn.lean`, right after
`interiorGroup_acolumn_two_group_decomp`). At an interior degree-2 chain vertex `a = vtx i.castSucc`
(`0 < i`, `deg_two`) **off the candidate row's two endpoints** `ab₁`/`ab₂` (`hne₁`/`hne₂`), given the flat
widening's `G_v`-row form `∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ) = hingeRow ab₁ ab₂ ρ₀` (`hcomb`) with
per-summand `G`-links + block memberships, the `edge i`-group's `a`-column lies in
`block (edge i) ⊓ block (edge (i−1))` (equivalently ⊥ BOTH incident panels). `hcol` is **derived internally**
(`a ∉ {ab₁,ab₂}` ⟹ `(hingeRow ab₁ ab₂ ρ₀).col@a = 0`, via `hingeRow_comp_single_off`), then LEAF 1
`interiorGroup_acolumn_adjacency` + the block-membership core `edgeGroup_acolumn_mem_block` put the column in
both blocks. **NO column-value read.** **CAVEAT (design §I.8.24(4.16), 2026-06-24): this is a GROUP-COLUMN perp,
NOT a `ρ₀`-perp** — the object annihilating the panel is the `edge i`-group's `vᵢ`-column, not `ρ₀` (Lean-confirmed
type-mismatch). It is correct + axiom-clean but **OFF the carry's critical path**: tying it to `ρ₀` needs
`group column = −ρ₀` = the forbidden value read. The carry's actual per-step is the 23b
`candidate_perp_two_incident_supportExtensors` (a genuine `ρ₀`-perp); see the FLAGGED route decision below. Zero
blast radius (no live caller yet).

**THE RELABEL BRIDGE IS LANDED + THE ROUTE-A-vs-B FORK IS DISSOLVED (2026-06-24, spike-salvage,
axiom-clean, build/lint/warning-clean).** A compiler-checked spike (design §I.8.24(4.13)) mapped the
interior-`hρe₀` seam at the kernel level and isolated the genuinely-new crux. THREE bridge lemmas landed in
`Relabel/ForkedArm.lean` (right after `case_III_arm_realization_chain`):
1. **`Graph.ChainData.reproduced_panel_eq_splice_panel`** — the consumer's reproduced panel
   `panelSupportExtensor (qρ(vtx i.succ,·)) (qρ(vtx (i−1).castSucc,·))` at candidate `i`'s relabelled seed
   `qρ = q ∘ shiftPerm i.castSucc` (`2 ≤ i`) EQUALS the BASE-seed panel of the spliced chain edge `edge i`,
   `panelSupportExtensor (q(vtx (i+1),·)) (q(vtx i,·))`. Pure `shiftPerm`/`vtx` algebra (off-cycle fix +
   interior successor), the cycle generalization of the d=3 `M₃` `hqρv`/`hqρc`.
2. **`Graph.ChainData.interior_hρe₀_of_splice_perp`** — the consumer's `hρe₀` produced from the SINGLE crux
   hypothesis `hsplice : ρ₀ ⊥ (base-seed `edge i` splice panel)` via (1) (a one-`rw` wrapper). This is the
   interior-`hρe₀` leaf reduced to the crux, in the project's no-`sorry` carry-the-crux-as-`h…` idiom.
3. **`PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends`** — the projection bridge
   `Fva.supportExtensor f = panelSupportExtensor (qρ(x,·)) (qρ(y,·))` when `endsσρ f = (x,y)`, so Route A's
   surviving-edge perp outputs (`ρ₀ ⊥ Fva.supportExtensor (edge s)`) read in the `panelSupportExtensor` form
   the crux speaks.

**THE CONJECTURE-CRUX LEAF `baseRedundancy_perp_interior_reproduced_panel` IS LANDED (2026-06-24, axiom-clean,
build/lint/warning-clean; `Relabel/ForkedArm.lean`, right before `interior_hρe₀_of_splice_perp`).** Conclusion
`ρ₀ ⊥ panelSupportExtensor (q(vtx (i+1),·)) (q(vtx i,·))` for `2 ≤ (i:ℕ) < cd.d` = EXACTLY the bridge's
`hsplice`, so the interior-`hρe₀` leaf is closed end-to-end (crux + the LANDED bridge). **The eq-6.66 carry
"across `vᵢ`" needed NO new argument** — it is the LANDED framework-free value-read fired one index deeper than
the surviving-edge leaf dared: (1) `interior_group_acolumn_eq_neg_baseRedundancy` (framework-free) gives the
`edge i`-group's `vtx i`-column = `−ρ₀` at the candidate index `i` itself (it needs only `2 ≤ i < d`, never
`G − vᵢ`); (2) `edgeGroup_acolumn_mem_block` puts that column in `(ofNormals Gw ends q).hingeRowBlock (edge i)`
(the block reads only `ends`/`q` — GRAPH-irrelevant, so the `vᵢ`-incidence that excluded `edge i` from
`G − vᵢ`'s framework is a non-issue when reading the BASE panel `q` directly); (3) `−ρ₀ ∈ block ⟹ ρ₀ ∈ block
⟹ ρ₀ ⊥ panelSupportExtensor` (`ofNormals_supportExtensor_eq_panel_of_ends` + `hends_i`). A clean replay of
`chainData_freshEdge_perp_of_baseRedundancy`'s body. The carried inputs (`hcomb`/`hlink`/`hrv`/`hends_i`/`hdeg1`)
are the LEAF-3 base bundle + widening outputs (no-`sorry` carry-the-inputs idiom). d=3 floor needs none of it
(`i = 2` = base split, `hρe₀` = LEAF-3's base annihilation, zero-regression).

**ORPHAN-CONFIRMED (confirm-and-delete at LEAF-5/CHAIN-5 cleanup): `baseRedundancy_group_acolumn_perp` (b23e50e)
+ the per-step column subtree** — the crux never touches them (it reads `−ρ₀` directly via the value-read, not a
group column); they are off the path. The four dead route families (§I.8.18–(I.8.20)) stay exhausted.

**Gate-side caveat (also LEAF-4):** the discriminator runs against the BASE seed `q`; the consumer uses the
relabelled `qρ = q ∘ shiftPerm i.castSucc`. The relabel bridge (1) handles exactly this seed reconciliation on
the `hρe₀` slot — the dispatch's remaining `shiftPerm`-image bookkeeping is the LANDED `candidateSeed`/
`shiftPerm` simp set. Both `candidatePanel` and `d_eq_kAdd` stay declared `_root_.Graph.ChainData.…`
(TACTICS-QUIRKS § 56 trap — a bare `Graph.`-prefixed decl inside `namespace …Molecular` would create a
`…Molecular.Graph` sub-namespace that breaks downstream `V(·)`/`E(·)` parsing).

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
(the interior base-block `W`/`hWS`/`hWcard`/`hW` production + the interior `hρe₀`) — a build MUST NOT
peel the easy leaves and defer it.

**LEAF-4's interior `hρe₀` leaf is CLOSED end-to-end (2026-06-24): the conjecture-crux
`baseRedundancy_perp_interior_reproduced_panel` is LANDED** (`Relabel/ForkedArm.lean`, before
`interior_hρe₀_of_splice_perp`; axiom-clean, build/lint/warning-clean). Its conclusion
`ρ₀ ⊥ panelSupportExtensor (q(vtx (i+1),·)) (q(vtx i,·))` (`2 ≤ (i:ℕ) < cd.d`) = the bridge's `hsplice`, so
`interior_hρe₀_of_splice_perp` (LANDED) wraps it into the consumer's `hρe₀` by one `rw`. The carry needed NO
inductive chain / per-vertex witness / meet — it is the LANDED framework-free value-read
(`interior_group_acolumn_eq_neg_baseRedundancy` = `−ρ₀` at the candidate index `i` + `edgeGroup_acolumn_mem_block`
in the GRAPH-irrelevant base framework's block) fired one index deeper than the surviving-edge leaf; the FORK
was a non-problem (see *Current state*). d=3 floor needs none of it.

**LEAF-4 step (ii)'s rank-cert half is BLOCKED, ALL THREE routes (A, B′, A′) are REFUTED, and 23c needs a
FUNDAMENTAL RECONSIDERATION — a PHASE STOP surfaced to the user 2026-06-24 (design §I.8.24(4.17)–(4.20), four
spikes, kernel-confirmed).** §(4.17): the router `bottomRelabel_image_mem_span_caseIIICandidate` (2878600)'s
reproduced branch is mis-targeted (the wrap-edge tag, endpoints OMIT `vᵢ`, forces the UNSATISFIABLE
`hG_eb_cand`). §(4.18): option (A) (static-`W` re-shape) is INFEASIBLE — no `W` satisfies `hWS` ∧ `hWcard` ∧
`hW` (REQUIRED by the corner `hLI` `notMem_span_mkQ_pmR_row_of_gate`) simultaneously, the redundancy carry
being a row THROUGH `vᵢ`. §(4.19): option (B′) (operated-frame block-rank) is INFEASIBLE — the genuine `±r`
corner is NOT pure-`vᵢ`-column under the column op (`ρ₀(S u − S a) ≠ 0`) so it can't join the d=3 separator
`linearIndependent_sum_restriction_block`, and its surviving discriminator `single a` is uncontrolled in the
base. §(4.20): option (A′) (re-derive in the operated frame, `hρGv` generically) is INFEASIBLE — it reduces
(kernel PROBE 1) to `chainData_relabel_arm_hρGv`'s `hφ` slot = the member-fixed base redundancy `hingeRow v₀v₂
ρ₀` in `span(endsσρ)`, and the only relabel transport `(funLeft (shiftPerm)⁻¹).dualMap` provably MOVES the
member (PROBE 2 `vtx2↦vtx1`; PROBE 3 the moved member = the fixed one forces `ρ₀=0`) — it IS the member-mapping
wall (§I.8.18–20, intrinsic). **The W9a *generalization* is LANDED** (`chainData_freshEdge_slot_mem` +
`wstep_foldl_freshEdge_slot_mem`); the wall is ONLY the `hφ` slot. **No framework-free escape** — `hφ` is a
span MEMBERSHIP, not the `hρe₀`-style annihilation that dissolved (the decisive structural difference). **The
convergence:** the `±r`-corner reformulation escapes `hρGv` at the ROW/membership level (`hg`/`hLI` via
`hρe₀`, LANDED, sound, `W`-independent) but NOT in the general-`d` RANK CERTIFICATION; the member-mapping wall
is unavoidable. **The KT-§6.4.2 source recon (§(4.21), primary-PDF, HIGH confidence) UPHELD + SHARPENED this:**
KT's paper counts the rank by whole-matrix block-additivity (6.64–6.65) + union-dimension (6.67) with the
member MOVING (6.62/6.66) — NOT row-membership — but that "member moves" is realized in Lean as the
relabel-image submatrix containment, which IS the wall (KT hides it as a one-line "not difficult to see"). So
(B′)/(A′) ARE KT's rank-count, and there is **NO missed KT route**. **NEXT = a fresh-session DESIGN+BUILD of
the genuinely-new §I.8.21(α) abstract block-rank-additivity-over-a-relabel infra** (cost-unknown): formalize
KT's "submatrix containment" (6.61) as a MATRIX-LEVEL rank-preserving block embedding (induced by `ρᵢ` + the
column op), reading `±r` (6.66) off as an `ℝ^D` covector identity — so the rank is counted as KT counts it on
paper, NEVER materialising a fixed-member row membership (the §(4.18) de-risk's generic block-rank lemma
consumes a scalar `hWS`/`hW` at `Candidate.lean:1606`, which forces the wall; the new lemma carries the whole
base matrix as a BLOCK). **Or** (user decision) pause the crux step and advance ENTRY (23d) / other phases.
**All LANDED leaves (cert/carrier/LEAF-2/router, the corner cert, the closed interior `hρe₀`) stay in tree**
(sound; reusable under a re-architected rank cert);
the rank-certification LAYER is the open re-design.

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
**LEAF-3 proper is LANDED** (2026-06-24, axiom-clean): the discriminator-firing producer
`PanelHingeFramework.exists_shared_redundancy_and_matched_candidate` (`Realization.lean`, after
`exists_chainData_discriminator_pick`). It produces `(matched i, ρ₀, hgate, n', base bundle)` — NOT the
interior `hρe₀`. Fed `candidatePanel hn`/`candidatePanel_injective hn`, it fires
`chainData_split_w6b_gates` + `exists_chainData_discriminator_pick` ONCE at the **BASE split** → shared
`ρ₀`/`w`/`hw`/`hwmem`/`λ`-witness + base `(ab)` annihilation, and the gate at the matched candidate
`candidatePanel hn u = candidateVtx i` (`candidatePanel_apply` bridge; `i` arbitrary, no interiority
claim). Additive support: `chainData_split_w6b_gates` re-exposes `AlgebraicIndependent ℚ q` (one consumer,
`chainData_split_realization`, took a `_` binder). **LEAF-4 step (i′) the WIDENING is LANDED** (2026-06-24,
axiom-clean): `chainData_split_w6b_gates` now also emits the **edge-grouped `G_v`-row form** (KT eq-6.66,
the existential `(nGv,cGv,evGv,uvGv,vvGv,rvGv)` + per-summand `(G−v)`-link/block membership +
`hingeRow a b ρ = ∑ⱼ cGv j • hingeRow …`), re-exposing the W6b producer's internally-computed form
(`Candidate.lean:439–445`, previously discarded as `_hedgeGv`); both consumers took a `_` binder.
**LEAF-4 step (i) column-sup projection is LANDED** (2026-06-24, axiom-clean):
`Graph.ChainData.freshEdge_interior_acolumn_sup` (`Relabel/Arm.lean`) — the `vᵢ`-column → two-block-sup
step of the regrouping (`φ ∘ single (vtx (s+1)) ∈ block (edge s) ⊔ block (edge (s+1))` at a
genuinely-surviving interior vertex, strict `s + 2 < (i:ℕ)`), the general-`i` lift of the d=3 gate
`i3_freshEdge_interior_acolumn_sup_deRisk`. **LEAF-4 step (i) sub-step (1) regrouping column-core is LANDED**
(2026-06-24, axiom-clean): `Graph.ChainData.interiorGroup_acolumn_two_group_decomp` (`Relabel/ChainColumn.lean`,
beside `interiorGroup_acolumn_adjacency`) — the POSITIVE two-group column split (`g.comp (single vᵢ) =
(group(edge i)).comp (single vᵢ) + (group(edge (i−1))).comp (single vᵢ)`, NO `hcol = 0` premise, the
unconditional sibling of the `= −` adjacency form), the column-algebra that lets the carry's per-step
`candidate_perp_two_incident_supportExtensors` call build its `hcol`/`hrest` (with `grest = 0`) from the flat
widening form rather than assume them. **The conjecture-crux leaf `baseRedundancy_perp_interior_reproduced_panel`
is LANDED (2026-06-24); see the top-of-note block + *Current state* for the verdict.** The eq-6.66 carry needed
no chain-carry body — the obsolete `baseRedundancy_perp_chain_edge` inductive route (and the per-step
column lemmas `baseRedundancy_group_acolumn_mem_inf`/`_perp`, `freshEdge_interior_acolumn_sup`,
`interiorGroup_acolumn_two_group_decomp`) is ORPHANED (the crux fires the framework-free value read directly,
one index deeper). **LEAF-4 (c)'s per-member `hS` router LANDED but its REPRODUCED branch is
MIS-TARGETED** (`bottomRelabel_image_mem_span_caseIIICandidate`, 2026-06-24; the GENUINE branch is reusable,
the reproduced branch carries the unsatisfiable `hG_eb_cand`; see *Current state* + design §I.8.24(4.17)).
**NEXT = a FUNDAMENTAL RECONSIDERATION (a phase STOP, NOT a build)** — ALL THREE routes (A, B′, A′) for the
general-`d` interior-`hρGv` rank cert are REFUTED (§I.8.24(4.18) static-`W` impossible; §(4.19) operated-frame
block-rank can't separate the non-pure-`vᵢ` `±r` corner; §(4.20) the general-`d` W9a reduces to the
member-fixed `hφ` slot that the relabel provably moves — the member-mapping wall, no framework-free escape
since `hφ` is a span membership). The four spikes converge: the `±r`-corner escapes `hρGv` at the
ROW/membership level but NOT in the general-`d` RANK CERT; the wall (§I.8.18–20, intrinsic) is unavoidable.
**The KT-§6.4.2 source recon (§(4.21)) UPHELD + SHARPENED this** — KT's paper counts the rank by whole-matrix
block-additivity with the member MOVING, but that is realized in Lean as the relabel-image submatrix
containment = the wall, so there is NO missed KT route. **Next = a fresh-session DESIGN+BUILD of the
genuinely-new §I.8.21(α) abstract block-rank-additivity-over-a-relabel infra** (matrix-level submatrix
containment 6.61, `±r` as an `ℝ^D` covector identity 6.66, never a fixed-member row membership; cost-unknown),
**or** (user decision) pause the crux step + advance ENTRY/ASSEMBLY. See the top-of-note *Next commit* block +
*Hand-off* + design §I.8.24(4.17)–(4.21). **Do NOT** re-attempt the four dead route families (§I.8.18–(I.8.20)),
re-hunt for a "missed KT route" (the recon settled there is none), revive the
`interior_group_*` column subtree, fire W6b per-interior-split (`hsplitGP` unavailable), re-attempt
(A)/(B′)/(A′) (all refuted), or patch the router's reproduced branch in place. **Downstream risk to watch** (design §I.8.24):
the ENTRY KT-4.6 chain-extraction leaf (23d, genuinely-new).

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
   **The discriminator-firing producer `exists_shared_redundancy_and_matched_candidate` — produces
   `(matched i, ρ₀, hgate, n', base bundle)`, NOT the interior `hρe₀`.** ✓ **LANDED** 2026-06-24
   (`CaseIII/Realization.lean`, after `exists_chainData_discriminator_pick`; build/lint/axiom-clean,
   warning-clean). Takes the base split `(v,a,b,cd.e₀)` + the W6b prerequisites (the same shape
   `chainData_split_realization` / the frozen contract carry); fires `chainData_split_w6b_gates`
   (→ shared `ρ₀`/`w`/`hw`/`hwmem` + base `(ab)` annihilation + eq-6.52 `λ`-witness + `AlgebraicIndependent
   ℚ q`) + `exists_chainData_discriminator_pick` (fed `candidatePanel hn`/`candidatePanel_injective hn`)
   ONCE at the BASE split; exposes `hgate` at the matched candidate `i := Fin.cast (cd.d_eq_kAdd hn).symm u`
   via the `candidatePanel_apply` bridge (`candidatePanel hn u → candidateVtx i`). The matched `i` is
   **arbitrary** (no interiority claim — LEAF-5 router case-splits). **Additive support change:**
   `chainData_split_w6b_gates` gained an output conjunct `AlgebraicIndependent ℚ q` (already in scope from
   `hsplitGP`, the discriminator prerequisite; its one consumer `chainData_split_realization` took a `_`
   binder). The gate-side `candidateSeed` `shiftPerm`-image reconciliation is deferred to LEAF-4 (buildable).
4. **LEAF-4 (THE CONJECTURE CRUX) — interior-`hρe₀` leaf CLOSED end-to-end (crux + bridge).** THREE pieces:
   (i′) the LEAF-3 widening ✓ LANDED (`chainData_split_w6b_gates` emits the edge-grouped `G_v`-row form, KT
   eq-6.66); (i) the interior-`hρe₀` leaf ✓ LANDED via the conjecture-crux
   `baseRedundancy_perp_interior_reproduced_panel` (`Relabel/ForkedArm.lean`, axiom-clean, 2026-06-24) + the
   LANDED bridge `interior_hρe₀_of_splice_perp` — the eq-6.66 carry fired the framework-free value read one
   index deeper (NO chain-carry body; the `baseRedundancy_perp_chain_edge` route + the per-step column lemmas are
   ORPHANED, see top-of-note); (ii) **the base block `W` (the remaining LEAF-4 piece)**: `f := w`,
   `L := (funLeft (shiftPerm i.castSucc).symm).dualMap`. The `hS` per-member router ✓ LANDED (2026-06-24,
   `bottomRelabel_image_mem_span_caseIIICandidate`, `Relabel/ForkedArm.lean`): one
   `chainData_bottom_relabel` image-disjunction (genuine → off-slot row-routing bridge
   `hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link`; block-tag → reproduced-slot membership)
   routed into `caseIIICandidate.rigidityRows` span. **NEXT** = the `W` producer wrapping it (per-member
   `chainData_bottom_relabel` → this router; `hrec`/`he₀rec` from the LEAF-3 `ends`-recording;
   `hvanish` = base-rows-over-old-bodies vanish at `single (shiftPerm i.castSucc (vtx i.castSucc))`; apply
   LEAF-2) → `W`/`hWS`/`hWcard`/`hW`; then derive `hρe₀` from the LANDED crux + bridge, and
   `exact case_III_arm_corner_assembly … hgate hρe₀ hWS hWcard hW hdef`.
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
- **23c's general-`d` interior-`hρGv` rank cert is EXHAUSTED — ALL THREE routes (A, B′, A′) REFUTED; the
  member-mapping wall (§I.8.18–20, intrinsic to KT) is unavoidable; 23c needs a FUNDAMENTAL RECONSIDERATION
  (design §I.8.24(4.17)–(4.21), four spikes + a KT source recon, 2026-06-24; a phase STOP).** §(4.17): the router's
  reproduced branch mis-targeted (wrap-edge tag, endpoints OMIT `vᵢ`, → unsatisfiable `hG_eb_cand`). §(4.18):
  (A) static-`W` re-shape INFEASIBLE (no `W` satisfies `hWS ∧ hWcard ∧ hW`; the carry is a row THROUGH `vᵢ`).
  §(4.19): (B′) operated-frame block-rank INFEASIBLE (the `±r` corner isn't pure-`vᵢ`-column, can't join the
  d=3 separator). §(4.20): (A′) re-derive-in-operated-frame INFEASIBLE — reduces (kernel) to
  `chainData_relabel_arm_hρGv`'s `hφ` slot (the member-fixed base redundancy in `span(endsσρ)`), which the only
  relabel transport provably MOVES off-member; the W9a *generalization* is LANDED, the wall is ONLY the `hφ`
  slot, no framework-free escape (`hφ` is a span MEMBERSHIP, not the `hρe₀`-style annihilation). **The
  convergence:** the `±r`-corner reformulation escapes `hρGv` at the ROW/membership level (`hg`/`hLI` via
  `hρe₀`, LANDED, sound) but NOT in the general-`d` RANK CERTIFICATION. §(4.21) the KT-§6.4.2 SOURCE RECON
  (primary-PDF, HIGH confidence) UPHELD + SHARPENED the STOP: KT's paper counts the rank by whole-matrix
  block-additivity with the member MOVING (6.62/6.66), NOT row-membership — but that "member moves" is realized
  in Lean as the relabel-image submatrix containment = the wall, so there is NO missed KT route. **Decision
  (user, 2026-06-24 — a phase STOP):** the sharpened path is a fresh-session DESIGN+BUILD of the genuinely-new
  §I.8.21(α) abstract block-rank-additivity-over-a-relabel infra (matrix-level submatrix containment 6.61, `±r`
  as an `ℝ^D` covector identity 6.66, never a fixed-member membership; cost-unknown), OR pause the crux step +
  advance ENTRY (23d)/ASSEMBLY. *Cross-cutting lesson (→ DESIGN.md at phase-close):* an architecture's "wall
  escaped" claim can hold at one
  layer (the corner: `±r` row membership/LI) while the wall reappears unchanged in a deferred-as-bookkeeping
  layer (the rank cert: the member-fixed `hφ` membership) — re-audit the DEFERRED obligations of a "wall
  escaped" architecture before declaring the wall gone; and the spike-and-land that dissolves an *annihilation*
  mis-pin (`hρe₀`) does NOT transfer to a *membership* obligation (`hφ`) — the structural kind of the goal
  decides whether a framework-free escape can exist.
- *Where KT's "member moves" (6.62) lands: the redundant `±r` row on the candidate's reproduced hinge slot,
  the graph-endpoints-vs-overridden-support decoupling* → `notes/BlueprintExposition.md` (`lem:case-III general-d`).
- *A diverse-lens recon PAIR (constructive + adversarial-refute) resolves a recurring-mis-pin design seam
  where single reads fail* → model-exp *Findings* 2026-06-22.
- **LEAF-4 conjecture-crux RESOLVED + LANDED (2026-06-24, spike-and-land; axiom-clean).**
  `baseRedundancy_perp_interior_reproduced_panel` closes the eq-6.66 carry to the spliced candidate edge by
  firing the LANDED framework-free value-read (`interior_group_acolumn_eq_neg_baseRedundancy` = `−ρ₀` at the
  candidate index `i` + `edgeGroup_acolumn_mem_block` in the base framework's block) one index deeper than the
  surviving-edge leaf — NO inductive chain / per-vertex witness / meet. The entire (A)-vs-(B) carry framing was a
  non-problem; the prior `candidate_perp_two_incident`/`baseRedundancy_group_acolumn_perp` per-step machinery is
  ORPHANED (the crux never touches it). *Cross-cutting lesson:* **a leaf that "looks framework-bound" (excluded
  from `G − vᵢ` because the panel is `vᵢ`-incident) can be panel-only** — `hingeRowBlock` reads only `ends`/`q`,
  so deleting the body never gates a BASE-seed panel read; the wall-vs-escape mis-pins (3–4×) all came from
  reading the splice panel through a framework instead of off the seed directly. → candidate for `DESIGN.md`
  (write at phase-close).

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
  cd.d` chain candidate align only via `d = k+1` (KT §6.4.2-structural). The five pieces (all settled,
  consumed by the LEAF-3 producer above): the `ChainData` field `d_eq : d = n` + the bridge
  `d_eq_kAdd` (`d_eq`+`hn` ⟹ `cd.d=k+1`) + the record-local selector `candidateVtx`/`candidateVtx_injective`
  (eq-6.67) + the match `candidateVtx_succ_eq` (`candidateVtx i = vtx i.succ` at interior `i`) + the composed
  `Fin (k+1)` selector `candidatePanel`/`candidatePanel_injective`/`candidatePanel_apply`
  (`= candidateVtx ∘ Fin.cast d_eq_kAdd.symm`, the `cand`/`hcand` input). `d_eq_kAdd`/`candidatePanel`
  declared `_root_.Graph.ChainData.…` (the §56 sub-namespace trap); `candidateVtx_succ_eq`/`candidatePanel_apply`
  not `@[simp]`.
- **Dispatch LEAF-3 proper: the discriminator-firing producer (2026-06-24, axiom-clean).**
  `PanelHingeFramework.exists_shared_redundancy_and_matched_candidate` (`CaseIII/Realization.lean`, after
  `exists_chainData_discriminator_pick`): takes the base split `(v,a,b,cd.e₀)` + W6b prerequisites, fires
  `chainData_split_w6b_gates` ONCE (→ shared `ρ₀ ≠ 0` + base `(ab)` annihilation + `w`/`hw`/`hwmem` +
  eq-6.52 `λ`-witness + `AlgebraicIndependent ℚ q`) + `exists_chainData_discriminator_pick`
  (fed `candidatePanel hn`/`candidatePanel_injective hn`) → matched candidate
  `i := Fin.cast (cd.d_eq_kAdd hn).symm u`, `n'`, gate at `candidateVtx i` (via the `candidatePanel_apply`
  bridge). `i` arbitrary (no interiority; LEAF-5 routes). Additive: `chainData_split_w6b_gates` re-exposes
  `AlgebraicIndependent ℚ q` (the only landed-lemma touch; one consumer `chainData_split_realization` took
  a `_` binder). NEXT = LEAF-4 (interior `hρe₀` + base block `W` + `exact case_III_arm_corner_assembly`).
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
- **LEAF-4 interior-`hρe₀` route RE-ROUTED (2026-06-24, diverse-lens recon pair; design §I.8.24(4.13)).**
  §(4.12)'s pinned `interior_group_eq_baseRedundancy` route is WRONG-SHAPE (column value). Corrected: the
  live `candidate_perp_two_incident_supportExtensors` (eq-6.44 two-edge perp carry, annihilation-level) +
  the `panelCorrespondence_supportExtensor` seed-relabel transport, fed the eq-6.52 ALL-edge redundancy (a
  below-contract LEAF-3 widening — `candidate_perp_two_incident`'s `hcol` needs the full combination, not
  the (ab)-block λ-witness). SOUND (KT eq-6.66), not a wall, no motive/IH change; build-time de-risk = the
  incident-panel→shortcut-panel transport. Full route + revised build order in design §I.8.24(4.13).
- **LEAF-4 step (i′) the WIDENING (2026-06-24, axiom-clean, build/lint/warning-clean).**
  `chainData_split_w6b_gates` (`CaseIII/Realization.lean`) gained an output conjunct = the **edge-grouped
  `G_v`-row form** of the candidate (KT eq-6.66): the existential `(nGv, cGv, evGv, uvGv, vvGv, rvGv)` with
  per-summand `(G−v)`-link + block membership + `hingeRow a b ρ = ∑ⱼ cGv j • hingeRow (uvGv j) (vvGv j)
  (rvGv j)`. This was ALREADY computed inside the W6b producer
  `exists_candidateRow_bottomRows_of_rigidOn` (`Candidate.lean:439–445`) but discarded by the wrapper as
  `_hedgeGv`; the widening re-exposes it through both chain-order branches (the `(b,a)` branch via
  `hingeRow_swap a b (-ρ)` + `neg_neg`). Purely additive — both consumers (`chainData_split_realization`,
  `exists_shared_redundancy_and_matched_candidate`) took a `_` binder; no motive/IH/contract change. The
  all-edge eq-6.52/6.66 data step (i) regroups at the interior degree-2 vertex.
- **LEAF-4 step (i) column-sup projection (2026-06-24, axiom-clean, build/lint/warning-clean).**
  `Graph.ChainData.freshEdge_interior_acolumn_sup` (`Relabel/Arm.lean`, after the d=3 gate
  `i3_freshEdge_interior_acolumn_sup_deRisk` it generalizes): at a candidate `i : Fin (cd.d+1)` and a
  genuinely-surviving interior chain vertex `vtx (s+1)` (strict `s + 2 < (i:ℕ)`, so both neighbours
  `vtx s`/`vtx (s+2)` survive `removeVertex (vtx i)`), a span member `φ ∈ span Fva.rigidityRows` has its
  `vtx (s+1)`-column in the **two-edge sup** `block (edge s) ⊔ block (edge (s+1))`. Direct application of
  `acolumn_mem_hingeRowBlock_sup_of_span_rigidityRows`; degree-2 closure off `shiftBody_deg_two`,
  distinctnesses off `vtx_ne`. The `s + 2 < i` boundary is load-bearing (at `i = s+2` the successor is
  removed → degree-ONE, the d3-base/`M₃` one-edge case). The `vᵢ`-column → two-block-sup step of the
  interior-`hρe₀` regrouping; zero blast radius (no live caller). Build note: `s + 1 < i` is WRONG — it
  permits `i = s+2` where `vtx (s+2) = vtx i` is removed (caught by an `omega`-fail on `s + 2 ≠ (i:ℕ)`).
- **LEAF-4 step (i) sub-step (1) regrouping column-core (2026-06-24, axiom-clean, build/lint/warning-clean).**
  `Graph.ChainData.interiorGroup_acolumn_two_group_decomp` (`Relabel/ChainColumn.lean`, beside the conditional
  `interiorGroup_acolumn_adjacency`): the POSITIVE two-group column split `g.comp (single vᵢ) =
  (group(edge i)).comp (single vᵢ) + (group(edge (i−1))).comp (single vᵢ)` at an interior degree-2 vertex
  (`0 < i`), with NO `hcol = 0` premise (the unconditional sibling of the `= −` adjacency form). The
  column-algebra that lets the carry's per-step `candidate_perp_two_incident_supportExtensors` build its
  `hcol`/`hrest` (with `grest = 0`) from the flat widening rather than assume them. Proof = clean replay of the
  adjacency lemma's `_eq_incident` + `deg_two_split` + `edge_inj` filter-congr, sans the vanishing hypothesis;
  zero blast radius.
- **LEAF-4 step (i) per-step single-vertex carry (2026-06-24, axiom-clean, build/lint/warning-clean).**
  `Graph.ChainData.baseRedundancy_group_acolumn_mem_inf` + `_perp` (`Relabel/ChainColumn.lean`, after
  `interiorGroup_acolumn_two_group_decomp`): the genuinely-new ANNIHILATION step of the corrected route
  (the anti-shrink-blessed shrink). At an interior degree-2 vertex `a = vtx i.castSucc` (`0 < i`) **off** the
  candidate row's endpoints `ab₁`/`ab₂`, given the flat widening `∑ⱼ cⱼ • hingeRow … = hingeRow ab₁ ab₂ ρ₀`,
  the `edge i`-group's `a`-column lies in `block (edge i) ⊓ block (edge (i−1))` (`_perp` = the dual
  `supportExtensor`-perp pair). `hcol` is DERIVED internally (`a ∉ {ab₁,ab₂}` ⟹ column `= 0`,
  `hingeRow_comp_single_off`) → LEAF 1 `interiorGroup_acolumn_adjacency` + `edgeGroup_acolumn_mem_block`. This
  IS `candidate_perp_two_incident_supportExtensors`'s conclusion (`grest = 0`) from the flat widening; **NO
  column-value read** (distinct from the forbidden `interior_group_*` value subtree). Zero blast radius.
  (SUPERSEDED by the relabel-bridge salvage below: now likely an ORPHAN-CANDIDATE off the critical path —
  group-column annihilation, not the `ρ₀`-perp the crux needs; leave in tree, decide at the crux build.)
- **LEAF-4 interior-`hρe₀` DECOMPOSE+SETTLE + diverse-lens recon PAIR (2026-06-24, docs-only; design
  §I.8.24(4.15), CONVERGED, coordinator-adjudicated).** Sub-step (1) eq-6.52 REGROUPING = **SATISFIABLE** (the
  LANDED widening's flat all-edge form, partitioned at the degree-2 vertex by `deg_two`, per-step `hcol` =
  `freshEdge_interior_acolumn_sup`, feeds `candidate_perp_two_incident_supportExtensors`; precedent
  `freshEdge_surviving_row_mem_of_witness`). Sub-step (2): Route A (degree-1 neighbour-column) **KILLED** — the
  neighbour `b = vtx (i−1).castSucc` is itself an interior chain vertex, degree-2 in `G` (`deg_two`;
  `caseIIICandidate.graph = G`), so its column → two-block SUP; the shortcut `(a,b)` isn't a graph edge (it is
  `e_b`'s OVERRIDDEN support in `F₀`, verified `ForkedArm.lean:200–202` → `Candidate.lean:1975`). **CORRECTED
  ROUTE (now REFINED by the relabel-bridge salvage below):** the shortcut `(a,b)` panel is, under the cycle
  relabel, the base-seed `edge i` splice panel — so the carry's FINAL step is the LANDED relabel bridge
  `interior_hρe₀_of_splice_perp`, and the genuinely-new content collapses to the single splice perp
  `baseRedundancy_perp_interior_reproduced_panel` (`ρ₀ ⊥ base-seed `edge i` panel`, KT eq-6.66), fed Route A's
  surviving-edge perps as inputs. Route B (`Meet.lean` meet identity) = FALLBACK. Below the contract.
  The pair fired because the seam had been mis-pinned 3× (§(4.12) column-shape, §(4.13)/(4.14)-A wrong-panel);
  the diverse-lens convergence + coordinator source-verification (the consumer's `hρe₀` panel) is what made the
  re-route sound.
- **LEAF-4 relabel bridge LANDED + fork DISSOLVED (2026-06-24, spike-salvage, axiom-clean,
  build/lint/warning-clean; design §I.8.24(4.13)).** A kernel-level spike mapped the interior-`hρe₀` seam and
  landed three bridge lemmas in `Relabel/ForkedArm.lean`: `Graph.ChainData.reproduced_panel_eq_splice_panel`
  (the consumer's reproduced `(a,b)` panel at `qρ = q ∘ shiftPerm i.castSucc` = the base-seed `edge i` splice
  panel `panelSupportExtensor (q(vtx (i+1),·)) (q(vtx i,·))`, pure `shiftPerm`/`vtx` algebra, the cycle
  generalization of M₃'s `hqρv`/`hqρc`); `Graph.ChainData.interior_hρe₀_of_splice_perp` (the consumer's `hρe₀`
  from the single crux `hsplice : ρ₀ ⊥ (base-seed `edge i` splice panel)`, one `rw`); and
  `PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends` (Route A's `supportExtensor`-output ↔
  `panelSupportExtensor` projection bridge). **The Route-A-vs-B fork is dissolved — both reduce to the SAME
  splice-perp crux** `baseRedundancy_perp_interior_reproduced_panel = ρ₀ ⊥ (base-seed `edge i` splice panel)`
  (KT eq-6.66, the carry across the spliced body `vᵢ`), the NEXT focused commit. Kernel-confirmed: the splice
  panel is `vᵢ`-incident, never a surviving edge, so it is NOT directly a Route-A output nor reachable by the
  M₃ G4d-i acolumn step off the candidate row (lands `edge (i±1)`); Route A
  (`chainData_freshEdge_perp_of_baseRedundancy`) supplies the SURVIVING-edge perps (`2 ≤ s`, `s+1 < i`) as
  INPUTS to the carry, not as `hsplice`. ORPHAN-CANDIDATE: `baseRedundancy_group_acolumn_perp` (b23e50e) is
  likely off the critical path now (group-column, not `ρ₀`-perp); leave in tree, decide at the crux build.
- **LEAF-4 (c) per-member `hS` router LANDED (2026-06-24, axiom-clean, build/lint/warning-clean).**
  `Graph.ChainData.bottomRelabel_image_mem_span_caseIIICandidate` (`Relabel/ForkedArm.lean`, after
  `interior_hρe₀_of_splice_perp`): the §(4.4)(β) hard part — one `chainData_bottom_relabel`-output disjunction
  (genuine seed row of `ofNormals (G − vᵢ) endsσρ qρ` OR reproduced-slot block tag
  `hingeRow (vtx i.succ) (vtx (i−1).castSucc) ρ'`) routed into `span (caseIIICandidate G endsσρ qρ e_a e_b
  (qρ(a,·)) n' (qρ(b,·)) 0).rigidityRows`. Genuine: destructure the rigidity-row, the surviving link is
  off-slot (dispatch-supplied `heab_off`), transfer the block across the graph (`ofNormals` support is
  graph-independent), `Submodule.subset_span` via `hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link`.
  Reproduced: `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` at `e_b`'s genuine `(a,b)` link
  (`hG_eb_cand`, `t = 0` ⟹ `hperp = hρ'`). The off-slot/`e_b`-link conditions are explicit hyps the `W`
  producer discharges from the interior split tuple. NO `hρGv`, no new LA — pure assembly of landed leaves;
  the per-member `hS` input LEAF-2's `span_relabelImage_le_and_finrank_and_acolumn_vanish` takes. The
  remaining LEAF-4 step (ii) = the `W` producer (this router + `hvanish` + LEAF-2) + the assembly call.
