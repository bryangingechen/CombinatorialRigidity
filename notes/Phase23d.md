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

**✅ USER CHOSE ROUTE A. THE A1+A2 DE-RISK IS LANDED + GATE-VERIFIED (2026-06-24,
`CombinatorialRigidity/Molecular/RigidityMatrix/Concrete.lean`, build+lint+warning-clean,
`#print axioms`-clean).** The next concrete step (the de-risk's recommendation in design §(4.30)) is
**A3 — the matrix block-additivity-as-inequality lemma** (`rank (column-opped R(G,pᵢ)) ≥ rank Mᵢ +
rank(bottom block)`), the genuinely-new piece. The de-risk's verdict: **the opacity composition is
CLEAN — no `maxHeartbeats`/`whnf` blow-up** (the file builds in ~6s, full project 24s; the §(4.30)
ONE-residual concern is RESOLVED).

**What landed (A1 + A2, all axiom-clean):**
- **A1 — the concrete matrix `BodyHingeFramework.rigidityMatrix`**: `R(G,p)` as a literal
  `Matrix (β × Fin (D−1)) (Fin (finrank ℝ (Dual ℝ (α → ScrewSpace k)))) ℝ` — the `(e,j)`-row is the
  `dualCoordEquiv`-coordinate vector of `hingeRow (ends e).1 (ends e).2 (blockBasis hgp e j)`, with
  `blockBasis` a basis of the `(D−1)`-dim hinge-row block. The `(edge,j)↔hingeRow` correspondence is
  `rigidityMatrix_row` (`rfl`). KT's `(D−1)|E| × D|V|` matrix made literal.
- **A2 — the rank bridge**: `Matrix.rank_of_dualCoord` (carrier-AGNOSTIC: any fin-dim `M`, any finite
  dual family — `(Matrix.of (dualCoordEquiv ∘ w)).rank = finrank (span (range w))`, via the
  mathlib-landed `Matrix.rank_eq_finrank_span_row` + `Submodule.span_image` + `LinearEquiv.finrank_map_eq`),
  its rigidity specialization `rigidityMatrix_rank`, and the **clause-(iii) capstone**
  `rigidityMatrix_rank_eq_finrank_span_rigidityRows`: `(rigidityMatrix ends hgp).rank =
  finrank (span F.rigidityRows)` — lands on the HONEST `HasGenericFullRankRealization` target
  (`PanelHinge.lean:1035` = literally `finrank (span rigidityRows) = …`), NOT a weaker matrix fact. The
  A1→target link is `span_range_rigidityRowFun` (`span (range rigidityRowFun) = span rigidityRows`,
  needs a link-recording `ends` + general-position `hgp`).
- **The opacity finding (the de-risk's point):** `dualCoordEquiv` is built from
  `Module.finBasis`/`Basis.equivFun` and the bridge runs entirely through the `Basis`/`LinearEquiv`
  boundary — the opaque `ScrewSpace` (Phase 22l) is **never unfolded** (no `ScrewSpace_def`, no `whnf`
  over `↥(⋀^k …)`). `Matrix.rank_eq_finrank_span_row` fires through the opaque carrier with zero detour.

**Sharpened A3–A6 leaf count (post-de-risk, replacing §(4.30)'s ≈9–14 estimate):** A1+A2 came in at
**~2 effective leaves** (the carrier-agnostic bridge + the rigidity specialization + the spanning
identity, one ~265-line file, no friction). The de-risk being clean means A2-type bridges are cheap.
Revised band **≈7–11 leaves**: **A3** matrix block-additivity-as-inequality (`Matrix.det_fromBlocks_zero₂₁`
+ the project's `Rank.lean` submatrix-det witnesses; the genuinely-new piece, ~2–3 leaves, MEDIUM–HIGH);
**A4** the entrywise (6.61) column-op realized on the matrix (`Matrix.rank_mul_eq_right_of_isUnit_det`;
~2–3 leaves, MEDIUM — laborious but mechanical); **A5** re-aim the gate/union-dim cert at the `D×D` minor
(content LANDED: `interior_group_eq_baseRedundancy`, `omitTwoExtensor_linearIndependent`; ~1–2 leaves,
LOW–MEDIUM re-wrap); **A6** dispatch+spine (~1–2, MEDIUM). A4 is now the cost outlier (A2's cheapness
shifts weight to the column-op entrywise proof).

*(Historical — the base-block reconsideration that closed before route A was chosen. Both route-4
variants refuted: 4-bare (`hseedrank`, §(4.28)); 4-splitOff (`hWS`, §(4.29)). The §(4.29) spike's three
sub-questions, retained for the wall characterization:)*

The §(4.29) spike settled the three sub-questions decisively:
- **Q1 (rank `hseedrank_ss`): WALL-FREE, verified end-to-end sorry-free + warning-clean.** The splitOff↔
  splitOff SET-image equality at the NON-involutive cycle `σ = shiftPerm i.castSucc` builds cleanly (two
  probe theorems, ~40 LoC, since reverted). The `d=3` `hσσ`/`hρρ` are NOT load-bearing (artifacts of the
  symmetric statement). `⊇` = landed `rigidityRow_chainData_relabel`; `⊆` = landed `rigidityRow_relabel_perm`
  at the inverse iso (`splitOff_isLink_shiftRelabel_iff.symm`) + the dualMap-comp identity; finrank via
  `LinearEquiv.funCongrLeft`/`.dualMap` + `LinearEquiv.finrank_map_eq`. The dual-map layer is involution-free
  (`hingeRow_funLeft_dualMap`, "No involution needed").
- **Q2 (containment `hWS`): WALLS.** The cert needs the FULL `W = span Fss.rigidityRows ≤ span(candidate)`,
  but `Fss` includes the FRESH `e₀'` short-circuit row (link `vᵢ₊₁`–`vᵢ₋₁`, non-redundant), which is NOT a
  `caseIIICandidate` row: the off-slot bridge needs `e₀' ∈ E(G)` (false, `caseIIICandidate.graph = G`), and
  the difference-collapse through `vᵢ` needs `ρ' ⊥ C(vᵢ₊₁, n')` (the OVERRIDDEN candidate `edge i` slot),
  which the discriminator gate `ρ₀ ⊥̸ C(vᵢ₊₁, n')` generically violates.
- **Q3: moot** (the cert demands the full `W`; Q2 blocks it).

**The load-bearing finding: the wall is the discriminator-gate condition `ρ₀ ⊥̸ C(vᵢ₊₁, n')`, intrinsic to
the `caseIIICandidate` slot-OVERRIDE architecture — NOT to any one base-block choice.** It re-surfaces as
`hρGv` (option A §(4.18)–(4.24)), `hS` (route B §(4.26)), `hseedrank` (4-bare §(4.28)), `hWS` (4-splitOff
§(4.29)). Q1 being clean while Q2 walls is the diagnostic: the relabel/rank machinery generalizes fine; the
block is one layer above the seed — the candidate's `edge i` override meeting the discriminator. **No further
base-block re-targeting escapes it.** NEW LEAF 2 `exists_seed_base_block` (LANDED 057a86e) stays a sound
lemma with an unsatisfiable `hseedrank` for the bare seed — a dead conditional, left as-is (harmless, no
caller).

---

**⚠️ HISTORY — ROUTE B WAS BLOCKED AT THE INTERIOR `hS` (design §I.8.24(4.26)); route 4 (above) is the
wall-free escape.** A read-only compiler-checked dispatch recon found that the interior arm's `hS` slot
(route-B LEAF-B2's
*universal* per-genuine-row transport into the `caseIIICandidate` span) cannot be discharged: a base genuine
row at the **wrap edge `edge i`** maps under the cycle relabel to the reproduced-slot `(a,b)`-block tag
`hingeRow (vtx (i+1)) (vtx (i−1)) ρ'`, and that tag is **NOT** in the candidate span — the routing lemma
`bottomRelabel_rigidityRows_mem_span_caseIIICandidate` requires `hG_eb_cand : G.IsLink e_b (vtx (i+1)) (vtx
(i−1))`, which is **provably false** (`edge (i−1)` links `vtx i`–`vtx (i−1)`, not `vtx (i+1)`–`vtx (i−1)`;
kernel-checked). This is exactly the member-mapping wall §(4.18)–(4.24) re-introduced by LEAF-B2's
individual-row `hS` (the project's OWN `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` docstring,
`Chain.lean:491–499`, names the collapsed tag as the wall, NOT a base-block row — it is the independent `±r`
corner row, transported by option A only as a GROUP). **All the route-B leaves below DID land and are sound
in isolation; what fails is their COMPOSITION at the interior `hS`.** Resolution = a phase-direction decision
(design §(4.26): re-target the base block to the seed framework `ofNormals (G − vᵢ) endsρ qρ`, OR fall back
to option A's landed group transport `case_III_arm_corner_assembly` for the interior arm). The d=3 line stays
fully green (its `i=2` wrap edge collapses to the genuine `case_III_bottom_relabel` swap, no general-`d` wall).

**Below: the (now-CONDITIONAL) route-B claims as they were landed — accurate as leaf-level facts, but the
"rank cert CLOSED end-to-end" / "residual risk RESOLVED" framing is SUPERSEDED by §(4.26).** The unconditional
crux composition (route B, design §I.8.24(4.25)) and its carried hypothesis LEAF-B1 are LANDED (below). After
the rank cert hit the member-mapping wall
(kernel-confirmed 5× for the
*existing* architecture: §(4.18) static-W, §(4.20) member-mapping, §(4.21) KT primary-source, §(4.23)
row-operation, §(4.24) geometry-aware-transport linearity + the A1 concede), a user-directed faithful
re-architecture pass found the escape: an **architectural inversion faithful to KT (6.64)**. Every prior
wall forced the base REDUNDANT row into the base block `W` (→ through-`vᵢ`, breaks `hW`) or transported it
as a covector (→ linearity-moved). KT does NEITHER: the bottom block is `R(G₁∖(v₀v₂)ᵢ*, q₁)` — base with
the redundant row DELETED (still rank `D(|V|−2)`) — and the redundant row's reproduction sits in the CORNER
`Mᵢ`. **Route B follows KT:** `W` = GENUINE rows ONLY (off-`vᵢ`, where the transport provably WORKS; card
`D(|V|−2)`); corner = `D−1` fresh panel rows + the `±r` row (`hρe₀`-sourced, never `hρGv`). The §(4.24)
linearity impossibility does NOT apply (route B never transports the redundant row — it's a direct corner
row); the §(4.19)/(4.23) `htopvanish` scissors does NOT apply (the chain cert needs the corner only
independent-mod-`W`, not pure-`vᵢ`). Q1 (the reproduction is a provable column equality) + Q2 (the bound
assembles for the genuine-only block: Q2-B span-preserved on deleting the redundant row, Q2-C genuine
transport, Q2-D genuine satisfies `hW`) are kernel-spiked sorry-free + axiom-clean. It is a **light
rank-cert REFORMULATION, not a `Matrix` rebuild** — the one rework is LEAF-2 / the `W`-production
(genuine-only basis instead of the full family).

**LEAF-B1 IS LANDED + DE-RISKED (2026-06-24, route-B build OPEN).** The structural-twin risk (the genuine-link
data may not survive a bare basis-extraction, possibly needing a motive strengthening) is **RESOLVED — no
strengthening needed**: the link/block data is recovered **for free** from set-membership in `F.rigidityRows`.
Landed in `RigidityMatrix/Basic.lean` (axiom-clean, warning/lint-clean), CONSTRUCTED not hypothesized:
- **`exists_genuine_linearIndependent_basis_of_rigidityRows_diff`** (LEAF-B1) — for any framework `F` and
  redundant member `rhat`, an LI family `f : Fin (finrank (span (rigidityRows ∖ {rhat}))) → Dual` with each
  `f i ∈ F.rigidityRows` (genuine, carries link data), each `f i ≠ rhat` (redundant EXCLUDED), and
  `span (range f) = span (rigidityRows ∖ {rhat})`. Kernel = mathlib `Submodule.exists_fun_fin_finrank_span_eq`.
- **`span_rigidityRows_diff_singleton_eq_of_mem_span`** (the satisfiability fact §(4.18) flagged, = Q2-B) —
  deleting the redundant row preserves the span when `rhat ∈ span (rigidityRows ∖ {rhat})` (the
  `exists_redundant_panelRow_ab_decomposition` content), so the genuine basis has card = the full base rank
  `D(|V|−2)`. The consumer composes this + the IH `finrank = D(|V|−2)` to fix the family's cardinality.

Salvage judged: Q1-A (±r column equality) SKIPPED (thin instantiation of the landed `interior_group_eq_baseRedundancy`);
Q2-C SKIPPED (thin wrapper of `rigidityRow_relabel_to_genuine`); Q2-D SKIPPED (the chosen LEAF-B2 path via
`span_relabelImage_le_and_finrank_and_acolumn_vanish` takes per-member `hvanish` = `hingeRow_comp_single_off`,
NOT a span-form `hW`, so Q2-D's span lemma would be an orphan).

**LEAF-B2 IS LANDED (2026-06-24, axiom-clean, build/lint/warning-clean).**
`BodyHingeFramework.exists_genuine_relabelImage_base_block` (`CaseIII/Candidate.lean`, after LEAF-2): the
genuine-only `W` producer. Takes a base framework `Fbase`, the redundant `rhat` (+ `hrhat : rhat ∈ span
(rigidityRows ∖ {rhat})`), the IH `finrank (span Fbase.rigidityRows) = N`, and the per-genuine-row transport
`hS`/`hvanish` stated **universally over `Fbase.rigidityRows`** (NOT per the basis — every genuine base row
transports + vanishes off `σ.symm v`); returns `W ≤ span Fcand.rigidityRows`, `finrank W = N`, `hW : ∀φ∈W,
φ∘single v = 0`. Body = compose LEAF-B1 (genuine basis `f`, `f i ∈ Fbase.rigidityRows`) → LEAF-2 at `Fcand`
(discharging `hS`/`hvanish` per member from the universal facts) → card via `Fintype.card_fin` +
`span_rigidityRows_diff_singleton_eq_of_mem_span hrhat` + the IH. Pure 3-lemma composition, NO `hρGv`, no
new LA. **Residual-risk RESOLVED at the signature level:** the universal `hvanish`-off-`σ.symm v` is
dischargeable because LEAF-4 instantiates `σ = (shiftPerm i.castSucc)⁻¹` (matching `chainData_bottom_relabel`'s
`(funLeft (shiftPerm i.castSucc).symm).dualMap`), so `σ.symm v = shiftPerm i.castSucc vᵢ = vtx 1` — the body
the base framework `G − vtx 1` REMOVES; every genuine base row (a `G − vtx 1` link) is off it
(`hingeRow_comp_single_off`). (The hand-off's loose "`σ = shiftPerm i.castSucc`" was the wrong direction;
`funLeft_dualMap_comp_single` forces `σ.symm v`, and the relabel is the INVERSE cycle — pinned below.)

**THE LEAF-4 `hvanish` HALF IS LANDED (2026-06-24, axiom-clean, build/lint/warning-clean).**
`PanelHingeFramework.ofNormals_removeVertex_rigidityRow_comp_single_self` (`CaseIII/Candidate.lean`,
just before LEAF-B2): EVERY rigidity row of `ofNormals (G.removeVertex v) ends q` annihilates body
`v`'s screw column `single v` — each row is `hingeRow x y r` at a `(G − v)`-link, whose endpoints both
survive removal (`x ≠ v`, `y ≠ v`, `removeVertex_isLink`), so `v` is off both and the row contributes
`0` (`hingeRow_comp_single_off`). This is LEAF-B2's universal `hvanish`-off-`σ.symm vᵢ` slot at the cycle
relabel `σ = (shiftPerm i.castSucc)⁻¹` (where `σ.symm vᵢ = vtx 1`, the removed base body), discharged for
the WHOLE `G − vtx 1` family with no per-member case-split. The `hvanish` half of LEAF-4 is now a
one-lemma call; **the substantive remaining LEAF-4 piece is the `hS` router** (genuine vs block-tag).

**THE LEAF-4 `hS`-ROUTER HALF IS LANDED (2026-06-24, axiom-clean, build/lint/warning-clean) — THE
RESIDUAL RISK IS RESOLVED.** `Graph.ChainData.bottomRelabel_rigidityRows_mem_span_caseIIICandidate`
(`CaseIII/Relabel/ForkedArm.lean`, just before `case_III_arm_corner_assembly`): for the chain
dispatch's base framework `Fbase = (ofNormals (G − vtx 1) ends₀ q).toBodyHinge`, EVERY rigidity row
`φ` transports under `(funLeft (shiftPerm i.castSucc).symm).dualMap` into the candidate
`caseIIICandidate G endsσρ qρ e_a e_b (qρ(vtx i.succ,·)) n' (qρ(vtx (i−1).castSucc,·)) 0`'s
rigidity-row span — exactly LEAF-B2's universal `hS` slot at `σ = (shiftPerm i.castSucc)⁻¹`. Body =
pure 2-lemma composition: feed `φ ∈ Fbase.rigidityRows` as `Or.inl hφ` to
`chainData_bottom_relabel` (→ the candidate-`i` seed disjunction), then
`bottomRelabel_image_mem_span_caseIIICandidate` (→ candidate span). The residual-risk question is
answered: the genuine base rows ALL go through the cert-SOUND genuine branch — `Or.inl` never forces
the §(4.17)-dead block-tag path (that path only fires on the candidate's own reproduced slot, supplied
by `hG_eb_cand` at the genuine `(a, b)` candidate link, never on a base-row image). NO `hρGv`, no new
LA, no narrowing of LEAF-B2's `hS` slot needed. The hypotheses (`hrec`/`he₀rec`, `hG_eb_cand`/`heab_off`)
are exactly the dispatch's interior-split data.

**THE `case_III_arm_corner_assembly` CALL IS LANDED (2026-06-24, axiom-clean, build/lint/warning-clean)
— LEAF-4 IS COMPLETE.** `PanelHingeFramework.case_III_arm_corner_assembly_via_leafB2`
(`CaseIII/Relabel/ForkedArm.lean`, after `case_III_arm_corner_assembly`): the producer that folds the
base-block `W`-production into the corner-data assembly. It has the same RAW interface as
`case_III_arm_corner_assembly` *minus* the opaque `(W, hWS, hWcard, hW)` block, *plus* the route-B
LEAF-B2 inputs (`Fbase`, `σ`, `rhat`, `hrhat`, `hIH : finrank (span Fbase.rigidityRows) =
D·(|V(Gv)|−1)`, and the universal `hS`/`hvanish` over `Fbase.rigidityRows`). Body = pure 2-step
composition: `obtain ⟨W, hWS, hWcard, hW⟩ := Fbase.exists_genuine_relabelImage_base_block F₀ hrhat
hIH hS hvanish` (LEAF-B2 at `Fcand = F₀ = caseIIICandidate G ends q e_a e_b (q(a,·)) n' (q(b,·)) 0`,
the assembly's own candidate, so no relabel-form alignment is needed here), then `exact …
case_III_arm_corner_assembly … hWS hWcard hW …`. NO `hρGv`, no new LA, no friction — it typechecked on
the first LSP pass. The framework-alignment bookkeeping the hand-off flagged dissolves at this layer:
LEAF-B2's `Fcand` is *chosen* to be the assembly's candidate, so the dispatch threads the `endsσρ`/`qρ`
form only when it discharges the universal `hS` from `bottomRelabel_rigidityRows_mem_span_caseIIICandidate`
(the router's candidate IS the `endsσρ`/`qρ` form). **The remaining work is CHAIN-2c-iii `chainData_dispatch`**
(item 2 below): the general-`k` router that reads the `ChainData` interior split, fires LEAF-3
(`exists_shared_redundancy_and_matched_candidate`) once, and feeds the interior matched `i` into this
producer with `Fbase = ofNormals (G − vtx 1) ends₀ q`, `σ = (shiftPerm i.castSucc)⁻¹`, `hS`/`hvanish`
from the two landed universal lemmas, `hrhat`/`hIH` from the W6b bundle / IH.

**THE INTERIOR-`hρe₀` PRODUCER IS LANDED (2026-06-24, axiom-clean, build/lint/warning-clean).**
`Graph.ChainData.interior_hρe₀_of_widening` (`CaseIII/Relabel/ForkedArm.lean`, just after
`interior_hρe₀_of_splice_perp`): the single interior-`hρe₀` call site the dispatch's interior arm
will use. It produces `case_III_arm_corner_assembly_via_leafB2`'s `hρe₀` slot
`ρ₀ ⊥ panelSupportExtensor (qρ(a,·)) (qρ(b,·))` (at the relabelled seed `qρ = q ∘ shiftPerm
i.castSucc`) from the **single** W6b edge-grouped widening bundle (`hcomb : hingeRow (vtx 0) (vtx 2)
ρ₀ = ∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` re-anchored to the spliced edge's endpoints, + `hlink`/`hrv`/
`hends_i`/`hdeg1`). Body = pure composition `interior_hρe₀_of_splice_perp ∘
baseRedundancy_perp_interior_reproduced_panel` (the conjecture-crux + the cycle-relabel bridge) — no
intermediate `hsplice` threading. Both composed leaves were landed-but-unused in 23c; this commit
gives them their consumer. NO `hρGv`, no new LA — typechecked on the first LSP pass.

**THE LEAF-3 WIDENING IS LANDED (2026-06-24, axiom-clean, build/lint/warning-clean) — THE ONE
UN-LANDED INTERIOR-ARM GAP IS CLOSED.** `exists_shared_redundancy_and_matched_candidate`
(`CaseIII/Realization.lean`) now re-exposes the **W6b edge-grouped `G_v`-row widening bundle** of
`hingeRow a b ρ₀` (KT eq. (6.66)) — the `∃ nGv cGv evGv uvGv vvGv rvGv, …` block that
`chainData_split_w6b_gates` already computes (its second-to-last `∃` conjunct, `Realization.lean`)
but LEAF-3 previously discarded as `_hedgeGv`. The change is a pure widening of LEAF-3's output
existential: bind `hedgeGv` instead of `_`, add the bundle conjunct (verbatim from the W6b producer's
shape, at `Gw = G − v`, `ends`, `q`, candidate row `hingeRow a b ρ₀`), thread it through the
`refine`. NO proof reasoning — the value flows straight from the W6b call; LEAF-3 had no callers yet
(the dispatch isn't built), so the type widening is caller-safe. This is exactly the bundle
`interior_hρe₀_of_widening` consumes (its `hlink`/`hrv`/`hcomb`), so the dispatch's interior arm now
reads `hρe₀` off LEAF-3's output directly — no re-fire of W6b, no further LEAF-3 surgery.

**THE INTERIOR-`hρe₀` BUNDLE RE-ANCHORING IS LANDED (2026-06-24, axiom-clean,
build/lint/warning-clean) — THE DISPATCH'S INTERIOR-`hρe₀` IS NOW A ONE-CALL READ-OFF.**
`Graph.ChainData.interior_hρe₀_of_baseWidening` (`CaseIII/Relabel/ForkedArm.lean`, just after
`interior_hρe₀_of_widening`): folds LEAF-3's `hedgeGv` bundle — taken in its **native LEAF-3
existential shape** (`∃ nGv cGv evGv uvGv vvGv rvGv, hlink ∧ hrv ∧ hcomb`, over `Gw = G − vtx 1`,
`hcomb` anchored at `hingeRow (vtx 0) (vtx 2) ρ₀`) — plus `hends_i` (the `ends`-recording of the
matched chain edge `edge i`) straight into `interior_hρe₀_of_widening`, producing the consumer's
`hρe₀` slot. The three re-anchorings the hand-off flagged are discharged internally: the per-summand
`G − vtx 1`-link is a `G`-link (`removeVertex_isLink.mp`); `hcomb` is the bundle's `.symm`; and
**`hdeg1`** — a summand incident to the anchor `vtx 2` uses `edge 2` — falls out of `deg_two` at
`vtx 2` (valid since `3 ≤ d`) ruling in `{edge 1, edge 2}`, then `edge 1` (the `link` field's
`vtx 1`-incident edge) being excluded by `removeVertex_isLink`'s `≠ vtx 1` endpoint conditions. So
the dispatch threads LEAF-3's `hedgeGv` + `hends_i` and reads `hρe₀` off in one call — no manual
re-anchoring at the dispatch. NO `hρGv`, no new LA.

**THE INTERIOR-SPLIT `heab_off` ACCESSOR IS LANDED (2026-06-24, axiom-clean, build/lint/warning-clean)
— THE DISPATCH'S OFF-SLOT INPUT IS NOW A ONE-CALL `ChainData` READ-OFF.**
`Graph.ChainData.removeVertex_isLink_edge_succ_pred_off` (`Induction/Operations.lean`, in the
interior-vertex split-data section beside `isLink_eq_succ_or_pred_or_removeVertex`): for an interior
chain index `i` (`0 < i`), EVERY link of `Gv = G.removeVertex (vtx i.castSucc)` uses an edge distinct
from both split-body chain edges `edge i` (= `e_a`) and `edge (i−1)` (= `e_b`) — both chain edges are
incident to the removed split body `v = vtx i.castSucc` (`isLink_succ_edge`/`isLink_pred_edge`), but a
`Gv`-link has both endpoints `≠ v` (`removeVertex_isLink`), so the endpoint-matching
`eq_and_eq_or_eq_and_eq` forces a contradiction. This is exactly the `heab_off` input the dispatch
feeds the per-member `hS` router `bottomRelabel_image_mem_span_caseIIICandidate` /
`bottomRelabel_rigidityRows_mem_span_caseIIICandidate` (and via the latter, LEAF-B2's universal `hS`).
NO `hρGv`, no new LA — a 3-step combinatorial setup leaf in the established interior-split idiom.

**Plan (⚠️ the route-B leaves all landed but DON'T compose at the interior `hS` — design §(4.26); a
phase-direction decision is owed before the dispatch):** ✅
LEAF-B1 (crux) → ✅ LEAF-B2 (genuine-only `W` producer) → ✅ LEAF-4 `hvanish` + `hS` router → ✅ the
`case_III_arm_corner_assembly` call (`case_III_arm_corner_assembly_via_leafB2`) → ✅ the
interior-`hρe₀` producer (`interior_hρe₀_of_widening`) → ✅ the LEAF-3 widening (the interior-arm
gap) → ✅ the interior-`hρe₀` bundle re-anchoring (`interior_hρe₀_of_baseWidening`, the dispatch's
one-call `hρe₀` read-off) → ✅ the interior-split `heab_off` accessor
(`removeVertex_isLink_edge_succ_pred_off`); LEAF-3 + the corner producer are landed. ⚠️ **BLOCKED:**
the dispatch's interior `hS` (LEAF-B2's universal per-genuine-row transport) is UNSATISFIABLE — the
wrap-edge `edge i` rows relabel to the dead `(a,b)`-block tag, NOT a candidate-span member (§(4.26)).
Remaining = adjudicate §(4.26) (option-A group transport vs. seed-framework base block), then build the
interior arm against the chosen route + CHAIN-5, then ENTRY + ASSEMBLY (parallel-safe).
**Route A** (full concrete `Matrix`; KT transfers literally but heavy) and **option A's landed group
transport** (`case_III_arm_corner_assembly` + `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate`, which
already lands the wrap edge as the `±r` corner GROUP) are the live fallbacks now that LEAF-B2's individual-row
`hS` has walled at the interior arm. **(C)** (honest-conditional) is the fallback-of-the-fallback.

**Do NOT** re-attempt the dead route families (§I.8.18–I.8.20) / (A)/(B′)/(A′); re-run the A1 / matrix-level
/ geometry-aware feasibility spikes (the *existing-architecture* wall is kernel-confirmed 5× — route B
escapes by re-architecture, not by re-attempting those); or re-hunt for a "missed KT route" (§(4.21): none).

## The A1 §I.8.21(α) feasibility recon — DONE (verdict INFEASIBLE)

Resolved 2026-06-24 by a read-only compiler-checked spike + a construct-or-concede resume (opus /
OPUS-ONLY, agentId `a8d70da3d32f07ca3`). **VERDICT: INFEASIBLE** — the full verdict, the unsound-FEASIBLE
first pass, the two sorry-free `concede_*` kernel re-derivations, and the no-feasible-route-in-hand
finding for the §I.8.21(α) matrix-level infra are in **design §I.8.24(4.22)**. The *Current state* above
carries the live consequence (route B + the LEAF-B2 next step). Do not re-run the spike.

## Remaining work in Phase 23

1. **The general-`d` rank certification — route B (§(4.25)), the 23d core.** The cert
   `case_III_rank_certification_chain` is already wall-free (block-additivity, no `hρGv`). ✅ **LEAF-B1
   LANDED** (`exists_genuine_linearIndependent_basis_of_rigidityRows_diff` + `span_rigidityRows_diff_singleton_eq_of_mem_span`,
   `RigidityMatrix/Basic.lean`) — the genuine-only base block source. ✅ **LEAF-B2 LANDED**
   (`exists_genuine_relabelImage_base_block`, `CaseIII/Candidate.lean`) — the genuine-only `W` producer:
   composes LEAF-B1 + LEAF-2 + the card satisfiability fact, taking the per-genuine-row transport `hS`/`hvanish`
   universally over `Fbase.rigidityRows`. ✅ **LEAF-4 `hvanish` half LANDED**
   (`PanelHingeFramework.ofNormals_removeVertex_rigidityRow_comp_single_self`, `CaseIII/Candidate.lean`) —
   every `ofNormals (G − v)` rigidity row vanishes off `v`'s column, discharging LEAF-B2's universal
   `hvanish`-off-`σ.symm vᵢ = vtx 1` for the whole family. ✅ **LEAF-4 `hS`-router half LANDED**
   (`Graph.ChainData.bottomRelabel_rigidityRows_mem_span_caseIIICandidate`,
   `CaseIII/Relabel/ForkedArm.lean`) — the lemma is sorry-free + axiom-clean, BUT ⚠️ it consumes an
   `hG_eb_cand` premise that is **UNSATISFIABLE for the interior dispatch** (design §(4.26)): the wrap-edge
   `edge i` base rows go through `chainData_bottom_relabel`'s `Or.inr` (the `(a,b)`-block tag), and routing
   that tag needs `G.IsLink e_b (vtx (i+1)) (vtx (i−1))`, which is false. The "residual risk RESOLVED via
   `Or.inl`" claim was WRONG (it covers only the genuine-branch rows, not the wrap-edge `Or.inr` rows).
   ✅ **The `case_III_arm_corner_assembly` call LANDED** (`case_III_arm_corner_assembly_via_leafB2`,
   `CaseIII/Relabel/ForkedArm.lean`) — folds the base-block `W`-production (LEAF-B2 at the assembly's own
   candidate `F₀`) into `case_III_arm_corner_assembly`, replacing its opaque `(W, hWS, hWcard, hW)` block
   with the LEAF-B2 inputs; the producer is sound, but its **interior `hS` premise is unsatisfiable** (above).
   The carrier, both `hLI` halves, the (α) bridge, the off-slot row bridge, the arm spine, the
   corner-data assembly, and **LEAF-B3** (corner producer: the `±r` via `hρe₀`, the panel rows,
   `linearIndependent_mkQ_corner_of_gate`) all stay LANDED (`notes/Phase23c.md` ledger). The interior
   `hρe₀` is CLOSED. ⚠️ The rank cert is closed only as a CONDITIONAL composition — the interior `hS`
   carries the §(4.26) obstruction. OPEN: adjudicate §(4.26), then the dispatch (item 2) + CHAIN-5.
2. **CHAIN-2c-iii `chainData_dispatch`** — the general-`k` dispatch (a discriminator-pick + Fin-case ROUTER
   over the two landed arm routes: the OLD engine via `chainData_split_realization` for the base candidate
   `i=1` + the d=3 floor; the option-(A) `case_III_arm_corner_assembly_via_leafB2` for interior `2 ≤ i < d`,
   feeding `Fbase = ofNormals (G − vtx 1) ends₀ q`, `σ = (shiftPerm i.castSucc)⁻¹`, `hS`/`hvanish` from the
   two landed universal lemmas, `hrhat`/`hIH` from the W6b bundle / IH, and `hρe₀` from the landed
   `interior_hρe₀_of_widening` fed the W6b widening bundle). ⚠️ Item 1's rank cert is CONDITIONALLY closed —
   the interior `hS` is UNSATISFIABLE as architected (§(4.26)); a phase-direction decision is owed.
   LEAF-1/2/3 + the discriminator-index plumbing + the genuine-branch router + the interior-arm producer
   + the interior-`hρe₀` producer all landed (sound in isolation). **The interior-`hρe₀` sub-gap is CLOSED: LEAF-3
   (`exists_shared_redundancy_and_matched_candidate`) re-exposes the W6b edge-grouped widening bundle
   (`hedgeGv`), and `interior_hρe₀_of_baseWidening` (2026-06-24) folds that bundle + `hends_i`
   straight into `interior_hρe₀_of_widening` (the `hdeg1`/`G`-link/`.symm` re-anchorings discharged
   internally)** — so the dispatch reads `hρe₀` off LEAF-3's output in one call, supplying only
   `hends_i`. ✅ **The interior-split off-slot input is now a `ChainData` read-off:**
   `Graph.ChainData.removeVertex_isLink_edge_succ_pred_off` (`Induction/Operations.lean`) supplies the
   `hS` router's `heab_off` (`∀ e x y, Gv.IsLink e x y → e ≠ edge i ∧ e ≠ edge (i−1)`) directly from
   the chain accessors. ⚠️ **BLOCKED at the interior `hS`** (design §(4.26)): not a wiring gap — the
   interior `hS` premise `hG_eb_cand` is provably false for the wrap-edge rows. Owed: adjudicate §(4.26)
   (option-A group transport vs. seed-framework base block), then the chosen interior arm + the base/`d=3`
   arm via `chainData_split_realization` (with its `htrans`) + the `ends`-orientation override (GAP 2).
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

- **⚠️ PHASE-DIRECTION DECISION OWED (user): route A (full `Matrix`) vs honest-conditional (C). ROUTE A
  NOW SCOPED — VERDICT: FEASIBLE BUT HEAVY (design §(4.30), 2026-06-24).** The seed/genuine base-block
  reconsideration is closed to all dual-space routes (§(4.29): the wall = the `caseIIICandidate` slot-override
  meeting the discriminator gate, invariant under base-block re-targeting — 4 wall appearances). The route-A
  scoping recon (§(4.30)) resolves the doc's internal A-vs-refuted-matrix tension **decisively**:
  - **Route A is a GENUINELY-DIFFERENT, FEASIBLE path — NOT the §(4.22)/(4.23) refuted work.** Those refuted
    option (i): an abstract `finrank`/`Submodule` block-rank lemma over the EXISTING dual-space span — it
    LANDED as `finrank_add_card_le_of_linearIndependent_mkQ` and IS the chain cert's kernel, walling on the
    span MEMBERSHIP. Route A is option (ii): a from-scratch concrete mathlib `Matrix R(G,p)` (rows `(edge,j)`,
    cols `α × Fin D`), rank = `Matrix.rank`, KT's (6.61) column op = an explicit unit-det right-multiply,
    (6.64) = a literal block-triangular matrix-rank fact. §(4.24)'s "explicit-`Matrix` = the §I.8.21(α) infra,
    no route" was imprecise (it imagined a `Matrix` *transport* still bottoming in the span-membership cert).
  - **Route A DOES dissolve the gate wall (confirmed, not hoped).** The wall is NOT the gate `ρ₀(C)≠0` (that
    is the SOUND, LANDED corner cert `notMem_span_mkQ_pmR_row_of_gate`); the wall is that the dual-space cert
    expresses KT's (6.61) submatrix-containment as a span MEMBERSHIP into the OVERRIDDEN candidate, which the
    wrap row (through `{vᵢ₊₁,vᵢ}` = the overridden `e_c=edge i` slot) cannot clear. In a literal `Matrix`,
    (6.61) containment is an entrywise column-op EQUALITY (`Matrix.rank_mul_eq_right_of_isUnit_det`, confirmed
    in mathlib); the wrap row is a literal matrix row transformed in place; its `±r` value is a literal entry
    computation (`interior_group_eq_baseRedundancy`, landed). No membership is formed.
  - **But route A is HEAVY: a dedicated sub-phase, ≈9–14 leaves** (A1 the `Matrix` def; A2 the
    `Matrix.rank`↔`finrank(span rigidityRows)` bridge via the LANDED-in-mathlib `Matrix.rank_eq_finrank_span_row`;
    A3 matrix block-additivity-as-inequality [genuinely-new]; A4 the entrywise (6.61) column-op [genuinely-new];
    A5 re-aim the gate/union-dim cert at the `D×D` minor [mostly landed re-wrap]; A6 dispatch+spine). The
    project has NO existing `Matrix` rigidity infra (kernel-confirmed) — A1–A4 are from scratch. NOT a light
    reformulation. So the user's call is **A-vs-(C) on COST, not feasibility.**
  - **Clause-(iii) bridge is real:** `Matrix.rank (R Q) = finrank (span Q.rigidityRows)` (A2) connects to the
    honest `HasGenericFullRankRealization` (`PanelHinge.lean:1035` = literally `finrank(span rigidityRows) =
    D·(|V|−1) − def`), NOT a weaker matrix fact.
  - **Flag-don't-force residual:** the one unsettled item is the CONSTANT FACTOR on A1/A2 — whether the
    `ScrewSpace`-opacity coordinate iso + the entrywise column-op compose without a `maxHeartbeats`/`whnf`
    blow-up at general `d` (the Phase-22l concern). A 1–2-day spike building A1+A2 at `d=3` (reverted) would
    sharpen the leaf count; it would NOT change the FEASIBLE verdict. Recommended de-risk IF the user leans
    toward A. **This is a user decision (A vs C); §(4.30) is the cost data the decision needs.**

### History (route B blocked; route 4 escapes)

- **⚠️ HISTORY — the interior dispatch's `hS` was UNSATISFIABLE as route-B LEAF-B2 is architected (design
  §(4.26)); route 4 (above) is the wall-free escape.** The route-B leaves all landed and are sound in
  isolation, but they do NOT compose at the interior arm: LEAF-B2's *universal* `hS` (every genuine base
  rigidity row's relabel image ∈ the `caseIIICandidate` span) is reasserted on the **wrap-edge `edge i`**
  rows, whose relabel image is the reproduced-slot tag `hingeRow (vtx (i+1)) (vtx (i−1)) ρ'` — and that tag
  is NOT in the candidate span (the routing lemma demands `G.IsLink e_b (vtx (i+1)) (vtx (i−1))`, **provably
  false**; `edge (i−1)` links `vtx i`–`vtx (i−1)`). This is the member-mapping wall §(4.18)–(4.24)
  re-introduced by demanding *individual*-row transport: the project's own
  `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` (`Chain.lean:491–499`) already documents the
  collapsed tag as the wall (the independent `±r` corner row, transported by option A only as a GROUP). The
  `hS` *router* `bottomRelabel_rigidityRows_mem_span_caseIIICandidate` IS sorry-free/axiom-clean — its bug is
  the **`hG_eb_cand` premise is unsatisfiable for the interior dispatch** (the deferred-hypothesis-unsat trap,
  DESIGN.md *Constructibility recon*; the same shape as the §(4.22) false-FEASIBLE). The `Or.inl`-feed
  "residual risk RESOLVED" claim was wrong: it only covers the genuine-branch rows; the wrap-edge rows go
  through `Or.inr` (the block tag).
- **Resolution = the SEED-FRAMEWORK re-architecture (route 4); SCOPED 2026-06-24, design §(4.27).** The
  option-A "cheapest exit" (route the interior arm through the engine `case_III_arm_corner_assembly` + the
  landed group transport) was investigated and **does NOT escape wall-free**: the engine route takes `hρGv`
  as a hypothesis, which at general interior `i` for the shared `ρ₀` is the member-mapping wall; and the
  group transport handles only the `±r` CORNER row, not the bottom-block `W`. The real wall-free route is
  (4): take `W := span (ofNormals (G − vᵢ) endsρ qρ).rigidityRows` (the candidate's own SEED rows). Its
  `hWS` (off-slot bridge) and `hW` (off-`vᵢ` vanishing) close mechanically WITH NO `hS`/`hρGv`
  (kernel-verified, probe `probe3_seed_W`); the entire residual is `hWcard = hseedrank` = the candidate seed
  rank `D·(|Gv|−1)`, which IS the relabel rank-iso from the base (the `d=3` `rigidityRows_ofNormals_relabel`
  is `hρGv`-free), NOT `hρGv`. **One new leaf** (general-`d` relabel SET-image equality) de-risks it; see
  §(4.27) for the full cost estimate (≈ 2 new leaves + dispatch + CHAIN-5).
- **LANDED + still valid (sound in isolation, reusable under either resolution):** LEAF-B1
  (`exists_genuine_linearIndependent_basis_of_rigidityRows_diff` + the satisfiability fact), LEAF-B2
  (`exists_genuine_relabelImage_base_block` — the producer is sound; only its *universal `hS` premise* is
  unsatisfiable for the interior dispatch), the `hvanish` lemma
  (`ofNormals_removeVertex_rigidityRow_comp_single_self`), the `hS` router
  (`bottomRelabel_rigidityRows_mem_span_caseIIICandidate` — sound, but consumes an unsatisfiable
  `hG_eb_cand`), `case_III_arm_corner_assembly_via_leafB2` (sound producer, unsatisfiable interior `hS`),
  the interior-`hρe₀` chain (`interior_hρe₀_of_widening` / `_of_baseWidening` — these DO discharge cleanly,
  verified in the spike), and `removeVertex_isLink_edge_succ_pred_off`. The interior `hgate`/`hρe₀`/`hvanish`
  slots were all verified mechanically dischargeable in the spike; the SOLE blocker is the interior `hS`.

## Hand-off / next phase

**⚠️ THE SEED/GENUINE BASE-BLOCK RECONSIDERATION IS CLOSED TO ALL ROUTES IN HAND — PHASE-DIRECTION DECISION
OWED (user): route A (full `Matrix`) vs honest-conditional (C).** A read-only verify-first spike (design
§(4.29), 2026-06-24, tree clean) settled route 4-splitOff: **Q1 (the splitOff↔splitOff relabel rank-iso)
is WALL-FREE and verified sorry-free**, but **Q2 (the splitOff seed's fresh `e₀'` short-circuit row ∈
candidate span) WALLS** — the difference-collapse through `vᵢ` needs `ρ' ⊥ C(vᵢ₊₁, n')` (the OVERRIDDEN
candidate `edge i` slot), which the discriminator gate generically violates. With 4-bare (§(4.28)) and
4-splitOff (§(4.29)) both refuted, and the option-A/route-B variants before them, **every seed/genuine
base-block route is closed**. The wall is the gate condition `ρ₀ ⊥̸ C(vᵢ₊₁, n')`, **intrinsic to the
`caseIIICandidate` slot-OVERRIDE architecture, not to any base-block choice** — no further re-targeting
escapes it (the load-bearing finding; design §(4.29)).

**✅ USER CHOSE ROUTE A; THE A1+A2 DE-RISK IS LANDED + GATE-VERIFIED (2026-06-24,
`Molecular/RigidityMatrix/Concrete.lean`).** The opacity composition is CLEAN — the §(4.30) de-risk's
one residual is RESOLVED (no `maxHeartbeats`/`whnf` blow-up; the bridge runs through the `Basis`/`LinearEquiv`
boundary, never unfolding opaque `ScrewSpace`). A1 (`rigidityMatrix` + `rigidityMatrix_row`), A2
(`Matrix.rank_of_dualCoord` carrier-agnostic + `rigidityMatrix_rank` + the clause-(iii) capstone
`rigidityMatrix_rank_eq_finrank_span_rigidityRows` landing on the honest `finrank (span rigidityRows)`),
and the spanning link `span_range_rigidityRowFun` all landed axiom-clean. See *Current state* for the
inventory + the sharpened A3–A6 leaf count.

**NEXT CONCRETE COMMIT = A3, the matrix block-additivity-as-inequality lemma.** State and prove
`rank (column-opped R(G,pᵢ)) ≥ rank Mᵢ + rank (bottom block R(G₁∖row, q₁))` at the `Matrix` level — KT
(6.64)'s block-triangular additivity, the genuinely-new piece. Build it from `Matrix.det_fromBlocks_zero₂₁`
(block-triangular det, mathlib-confirmed) + the project's `Rank.lean` submatrix-det witnesses
(`exists_submatrix_det_ne_zero_of_linearIndependent_rows`) — a full-rank `D×D` corner minor + the IH's
bottom-block rank. This is route A's analog of the landed `finrank_add_card_le_of_linearIndependent_mkQ`,
re-done over `Matrix.rank`. After A3: A4 (the entrywise (6.61) column-op via
`Matrix.rank_mul_eq_right_of_isUnit_det` — now the cost outlier), A5 (re-aim the gate/union-dim cert at the
`D×D` minor — content landed), A6 (dispatch+spine), then ENTRY + ASSEMBLY (parallel-safe).

**The route-A build should open as its own sub-phase** at the next phase-open (the A1+A2 de-risk
confirms route A on track; the A3–A6 layer plan is in *Current state* + §(4.30)). Route (C)
(honest-conditional) is no longer the plan — the documented fallback only if route A later walls.

**Reusable across either route (LANDED, sound in isolation):** the Q1 relabel rank-iso is a clean ~40-LoC
result reusing only landed bricks (`rigidityRow_chainData_relabel`, `rigidityRow_relabel_perm`,
`splitOff_isLink_shiftRelabel_iff`, `LinearEquiv.finrank_map_eq`) — bankable if any route needs the
candidate splitOff seed's rank. The route-B leaf inventory (LEAF-B1/B2, the `hvanish` lemma, the `hS`
router, `case_III_arm_corner_assembly_via_leafB2`, `interior_hρe₀_of_widening`/`_of_baseWidening`,
`removeVertex_isLink_edge_succ_pred_off`, LEAF-3, LEAF-B3) stays sound in isolation; the interior
`hgate`/`hρe₀`/`hvanish`/`heab_off` slot discharges are all spike-verified mechanical. NEW LEAF 2
`exists_seed_base_block` (LANDED 057a86e) is a dead conditional (unsatisfiable `hseedrank` for the bare
seed it hardcodes) — left as-is, harmless, no caller. ENTRY + ASSEMBLY remain parallel-safe later sub-phases.

## Decisions made during this phase

*(Fresh at open. The inherited landed-leaf inventory + the wall-characterization verdicts + the
cross-cutting lessons of building option (A) are the settled archive in `notes/Phase23c.md` *Decisions
made* + *Landed-leaf ledger*; 23d does not duplicate them. New 23d decisions land here.)*

- **A1+A2 DE-RISK LANDED + GATE-VERIFIED — the opacity composition is CLEAN (2026-06-24,
  `Molecular/RigidityMatrix/Concrete.lean`, build+lint+warning+axiom-clean).** A1 (`rigidityMatrix` =
  the literal `Matrix (β × Fin (D−1)) (Fin (finrank …)) ℝ` + the `(edge,j)↔hingeRow` accessor
  `rigidityMatrix_row`); A2 (`Matrix.rank_of_dualCoord` carrier-agnostic, `rigidityMatrix_rank`, and the
  clause-(iii) capstone `rigidityMatrix_rank_eq_finrank_span_rigidityRows` = the honest
  `finrank (span rigidityRows)`, via `span_range_rigidityRowFun`). The §(4.30) residual is RESOLVED: the
  bridge runs through `Module.finBasis`/`Basis.equivFun`/`LinearEquiv.finrank_map_eq` — opaque `ScrewSpace`
  is NEVER unfolded; `Matrix.rank_eq_finrank_span_row` fires with zero detour (file ~6s, full project 24s).
  Sharpened cost: A1+A2 ≈2 effective leaves; revised band ≈7–11 (A4 the column-op now the outlier). Lesson
  (the A2 bridge being carrier-agnostic is WHY opacity is a non-issue) → Findings.
- **Route A CHOSEN by the user (2026-06-24), with cost data in hand.** After the genuine-row base-block
  family closed (4 wall appearances, §(4.18)–(4.29)) and route A was scoped FEASIBLE-but-HEAVY (§(4.30),
  ~9–14-leaf sub-phase), the user chose route A (the honest unconditional `Matrix`-model Theorem 5.5) over
  the cheap honest-conditional (C). Execution: the A1+A2 `d=3` de-risk LANDED (above); next is A3
  (matrix block-additivity), then open the route-A build as its own sub-phase. (C) demoted to documented
  fallback. Lesson (the 4-wall saga + the verify-first wins) → Findings (model-experiment).
- **Route A (full `Matrix`) SCOPED — FEASIBLE BUT HEAVY; it is a genuinely-different path, NOT the
  refuted §(4.22)/(4.23) work (2026-06-24, design §(4.30), read-only recon, tree clean).** Resolves the
  doc's A-vs-refuted-matrix tension: §(4.22)/(4.23) refuted option (i) (abstract span-block-rank — landed
  as `finrank_add_card_le_of_linearIndependent_mkQ`, walls on span MEMBERSHIP); route A is option (ii) (a
  literal mathlib `Matrix R(G,p)`). It DOES dissolve the wall — KT's (6.61) submatrix-containment is an
  entrywise column-op equality (`Matrix.rank_mul_eq_right_of_isUnit_det`, mathlib-confirmed), never a
  membership; the bridge `Matrix.rank = finrank(span rigidityRows)` lands on the honest target. COST: a
  dedicated sub-phase ≈9–14 leaves (A3 matrix block-additivity + A4 the (6.61) column-op are genuinely-new;
  no existing `Matrix` rigidity infra). So A-vs-(C) is a COST decision. Flag: the A1/A2 `ScrewSpace`-opacity
  constant factor is the one unsettled item (a `d=3` spike would sharpen it, not flip feasibility).
- **Route 4-splitOff WALLS (Q2); the seed/genuine base-block reconsideration is CLOSED to all routes in
  hand (2026-06-24, design §(4.29), verify-first spike, tree clean).** Q1 (relabel rank-iso) verified
  WALL-FREE + sorry-free (involution NOT load-bearing); Q2 (`hWS` for the splitOff seed's fresh `e₀'` row)
  WALLS by the discriminator-gate condition `ρ₀ ⊥̸ C(vᵢ₊₁, n')`. The load-bearing finding: that gate is
  intrinsic to the `caseIIICandidate` slot-OVERRIDE, invariant under base-block re-targeting (4th wall
  appearance) — so no seed/genuine `W ≤ span(candidate)` route escapes. Decision → route A (`Matrix`) vs (C),
  user's call. Lesson (Q1-clean/Q2-walls is the diagnostic: relabel machinery generalizes, the block is the
  candidate override one layer up) → design §(4.29).
- **Opened 2026-06-24 at a clean-break close of 23c (user-adjudicated), at the member-mapping-wall phase
  STOP.** 23c's chosen architecture (option (A), the `±r`-block engine) is conclusively refuted at the
  rank-cert level; the redundancy-carry re-architecture half succeeded (interior `hρe₀` closed). 23d =
  the rank-certification reconsideration (A1 recon → A2 build / (C) honest-conditional / (D) reconsider),
  still within the CHAIN layer (CHAIN now spans 23b+23c+23d). ENTRY/ASSEMBLY get later letters. Structural
  precedent: the 23b→23c clean-break close at this same wall.
- **A1 §I.8.21(α) feasibility = INFEASIBLE (2026-06-24, design §(4.22)).** A read-only compiler-checked
  spike first returned FEASIBLE; coordinator scrutiny found it unsound — it verified the static-`W` cert
  `case_III_rank_certification_chain` COMPOSES (corner data carried as hypotheses) and re-confirmed the
  already-known row-membership escape, but never confronted that those hypotheses are unsatisfiable for the
  real interior carry (the exact "deferred-hypothesis unsatisfiable for the consumer" trap, DESIGN.md
  *Constructibility recon*). A construct-or-concede resume CONCEDED, building two sorry-free `concede_*`
  kernel re-derivations of §(4.17)/(4.18) for the actual dispatch slot. The §I.8.21(α) matrix-level infra
  has no feasible route in hand (operated-frame variants refuted by §(4.19)/(4.20)). Lesson promoted to
  Findings (model-experiment) + the satisfiability corollary already in DESIGN.md.
- **Matrix-level rework = INFEASIBLE; the wall is intrinsic to KT, 4× kernel-confirmed (2026-06-24, design
  §(4.23)).** User authorized one more swing (the user's "happy to rework landed material"): does KT's
  rank-preserving ROW-OPERATION handling of the redundant row (vs the project's span membership) escape the
  wall? A read-only design+spike (after the coordinator read KT §6.4.2 eqs. 6.60–6.67 from the primary PDF)
  DISPROVED it at the kernel: KT's row operation `r̂ = Σλ rⱼ` IS the `G_v`-row part `wGv ∈ span(R(G_v,q))` —
  documented in the project's OWN Phase-22g `exists_redundant_panelRow_ab_decomposition` (`Candidate.lean:191`,
  `:230`). The "scissors": the pure-`vᵢ` corner satisfies `htopvanish` but needs `hρGv` to enter the span;
  the `hρe₀`-corner enters the span but isn't pure-`vᵢ`; they differ by exactly `hingeRow a b ρ₀` = the wall.
  Decision: the unconditional crux is closed to all routes in hand → option (C) + ENTRY. (D) needs a
  genuinely-new idea. Lesson → Findings (model-experiment).
- **Geometry-aware transport = RELOCATES-TO-WALL (2026-06-24, design §(4.24)); the transport layer is
  confirmed CORRECT, nothing to rework.** User insight (sharp): replace the transport with one that
  "remembers the geometry" so the base redundancy transports faithfully. A scoping recon found the project's
  transport ALREADY does this (`shiftPerm`=KT's ρᵢ 6.54, `qρ`=config relation 6.59,
  `rigidityRow_relabel_to_genuine` absorbs KT's per-edge reproduction as the abstract `hsupp` — the exact
  abstraction hoped for; it works for genuine rows). The redundant row is closed by a LINEARITY IMPOSSIBILITY
  (SPIKE 3): any linear `T` sends `Σcⱼ·gⱼ` to `Σcⱼ·T(gⱼ)`, so the decomposed route lands the redundant row at
  its `ρᵢ`-image (moved member), never the fixed `hφ` — the redundant row has no genuine edge to anchor the
  reproduction to. 5th kernel confirmation. The ONLY escape is a non-linear/explicit-`Matrix` model = the
  §I.8.21(α) infra (no route in hand). → option (C) + ENTRY. Lesson → Findings.
- **Route B WORKS — the unconditional crux is RESOLVABLE via an architectural inversion faithful to KT
  (6.64) (2026-06-24, design §(4.25)); SUPERSEDES the (C)-only recommendation.** User-directed: tackle the
  faithful re-architecture, don't skip the step (and the user's epistemic point — KT's validity IS a route).
  All 5 prior walls forced the redundant row into the base block `W`; KT (6.64) deletes it from the bottom
  block and puts its reproduction in the CORNER. Route B: `W` = GENUINE rows only (off-`vᵢ`, transport works,
  rank `D(|V|−2)`); corner = panel rows + the `±r` row (`hρe₀`, never `hρGv`). §(4.24) linearity impossibility
  doesn't apply (redundant row not transported); §(4.19)/(4.23) `htopvanish` doesn't apply (chain cert needs
  corner only independent-mod-`W`). Q1/Q2 kernel-spiked sorry-free + axiom-clean (CONSTRUCTED Q2-B/C/D, the
  satisfiability §(4.18) called impossible *for the redundant-including block*). A LIGHT rank-cert
  reformulation (rework LEAF-2's `W`-production to a genuine basis), NOT a `Matrix` rebuild. The one carried
  hypothesis = **LEAF-B1** (genuine-basis extraction), being de-risked by construction. → route-B build (plan
  in *Hand-off*); route A / (C) are fallbacks. Lesson (the re-architecture escape + scoping a user's idea) →
  Findings.
- **LEAF-B2 LANDED — the genuine-only `W` producer (2026-06-24, axiom-clean, build/lint/warning-clean).**
  `BodyHingeFramework.exists_genuine_relabelImage_base_block` (`CaseIII/Candidate.lean`, after LEAF-2):
  compose LEAF-B1 (genuine basis `f`) → LEAF-2 (`span_relabelImage_le_and_finrank_and_acolumn_vanish` at the
  candidate framework) → card via `Fintype.card_fin` + `span_rigidityRows_diff_singleton_eq_of_mem_span hrhat`
  + the IH. The design call: state `hS`/`hvanish` **universally over `Fbase.rigidityRows`** (not per the
  specific basis) — every genuine base row transports + vanishes off `σ.symm v` — so LEAF-B1's `f i ∈
  Fbase.rigidityRows` instantiates them by `fun j => h_ (hmem j)`. Pure 3-lemma composition, NO `hρGv`, no new
  LA, no friction. **Pinned a design slip:** the hand-off's loose "`σ = shiftPerm i.castSucc`" was the wrong
  perm direction — `funLeft_dualMap_comp_single` forces `hvanish` at `σ.symm v`, and the relabel is the INVERSE
  cycle `σ = (shiftPerm i.castSucc)⁻¹`, so `σ.symm vᵢ = shiftPerm i.castSucc vᵢ = vtx 1` (the removed base
  body) — which is exactly why the universal `hvanish` is satisfiable (the §(4.25) residual risk, resolved at
  the signature level, not deferred to a build that might surface a non-vanishing member).
- **LEAF-4 `hvanish` half LANDED — the off-`v` vanishing of a `removeVertex v` framework's whole rigidity-row
  family (2026-06-24, axiom-clean, build/lint/warning-clean).**
  `PanelHingeFramework.ofNormals_removeVertex_rigidityRow_comp_single_self` (`CaseIII/Candidate.lean`, before
  LEAF-B2): every `φ ∈ (ofNormals (G − v) ends q).rigidityRows` annihilates `single v` — destructure `φ =
  hingeRow x y r` at a `(G − v)`-link, `removeVertex_isLink` gives `x,y ≠ v`, close with
  `hingeRow_comp_single_off`. This discharges LEAF-B2's *universal* `hvanish`-off-`σ.symm vᵢ` slot for the
  WHOLE family (no per-member split) at `v = vtx 1 = σ.symm vᵢ`, the body the base `G − vtx 1` removes. The
  `.graph`-unfold idiom (`rw [toBodyHinge_graph, ofNormals_graph, removeVertex_isLink]`) is the established
  pattern of `chainData_bottom_relabel` / `bottomRelabel_image_mem_span_caseIIICandidate` — no new friction.
  The substantive remaining LEAF-4 piece is now the `hS` router only.
- **LEAF-4 `hS`-router half LANDED — ⚠️ "residual risk RESOLVED" was WRONG (corrected 2026-06-24, design
  §(4.26)).** `Graph.ChainData.bottomRelabel_rigidityRows_mem_span_caseIIICandidate`
  (`CaseIII/Relabel/ForkedArm.lean`): the lemma is sorry-free/axiom-clean and feeds `φ ∈ Fbase.rigidityRows`
  as `Or.inl` to `chainData_bottom_relabel`. **The error:** the dispatch recon proved this only covers the
  genuine-branch (`Or.inl`) rows — the **wrap-edge `edge i`** base rows go through `Or.inr` (the `(a,b)`-block
  tag), which the router routes via an `hG_eb_cand : G.IsLink e_b (vtx (i+1)) (vtx (i−1))` premise that is
  **provably false** (`edge (i−1)` links `vtx i`–`vtx (i−1)`). So the universal `hS` is UNSATISFIABLE; the
  "every genuine base row goes through the sound branch" claim missed that the wrap edge is a genuine base
  edge whose image is the tag. The lemma stays in tree (sound), but its premise can't be met at the
  interior dispatch. → BLOCKED, §(4.26).
- **The `case_III_arm_corner_assembly` call LANDED — ⚠️ "rank cert CLOSED" was OVERSTATED (corrected
  2026-06-24, design §(4.26)): closed only CONDITIONALLY — the interior `hS` is unsatisfiable (above).**
  `PanelHingeFramework.case_III_arm_corner_assembly_via_leafB2`
  (`CaseIII/Relabel/ForkedArm.lean`, after `case_III_arm_corner_assembly`): the "rest of LEAF-4" producer,
  with the same RAW interface as `case_III_arm_corner_assembly` *minus* its opaque `(W, hWS, hWcard, hW)`
  block, *plus* the LEAF-B2 inputs (`Fbase`, `σ`, `rhat`, `hrhat`, `hIH`, universal `hS`/`hvanish`). Body =
  pure 2-step composition: `obtain` from `exists_genuine_relabelImage_base_block` (LEAF-B2) at
  `Fcand = F₀` (the assembly's *own* candidate), then `exact` into `case_III_arm_corner_assembly`. **The
  design call that dissolved the flagged framework-alignment work:** choose LEAF-B2's `Fcand` to BE the
  assembly's candidate — then `hWS` already lands in the right span, and the `endsσρ`/`qρ` alignment is
  pushed down into the dispatch's `hS` discharge (the only place the relabeled form appears). Typechecked
  first LSP pass, no friction.
- **The interior-`hρe₀` producer LANDED (2026-06-24, axiom-clean, build/lint/warning-clean).**
  `Graph.ChainData.interior_hρe₀_of_widening` (`CaseIII/Relabel/ForkedArm.lean`, after
  `interior_hρe₀_of_splice_perp`): produces `case_III_arm_corner_assembly_via_leafB2`'s `hρe₀` slot at the
  matched interior candidate `i` (`2 ≤ i`) from the W6b edge-grouped widening bundle. Body = pure
  composition `interior_hρe₀_of_splice_perp ∘ baseRedundancy_perp_interior_reproduced_panel` (the
  conjecture-crux + the cycle-relabel bridge), both landed-but-unused in 23c — this commit gives them
  their single consumer, so the dispatch threads the widening bundle once and reads off `hρe₀` directly.
  NO `hρGv`, no new LA, no friction (typechecked first LSP pass).
- **The LEAF-3 widening LANDED — the interior-arm leaf gap is closed (2026-06-24, axiom-clean,
  build/lint/warning-clean).** `exists_shared_redundancy_and_matched_candidate`
  (`CaseIII/Realization.lean`) now re-exposes the W6b edge-grouped `G_v`-row widening bundle
  (`hedgeGv`: `∃ nGv cGv evGv uvGv vvGv rvGv, hlink ∧ hrv ∧ hcomb`, KT eq. (6.66)) that
  `interior_hρe₀_of_widening` consumes. `chainData_split_w6b_gates` already computes it (its
  second-to-last `∃` conjunct); LEAF-3 had bound it as `_hedgeGv` and discarded it. The fix is a pure
  output widening: bind `hedgeGv`, add the conjunct (verbatim from the W6b shape, at `Gw = G − v`,
  candidate row `hingeRow a b ρ₀`), thread through the `refine`. NO proof reasoning, NO friction (the
  value flows straight from the W6b call); caller-safe (LEAF-3 has no callers yet). So the dispatch's
  interior arm now reads `hρe₀` off LEAF-3 directly — owing only the bundle re-anchoring to the
  interior edge's `(vtx 0, vtx 2)` + the `Fin cd.d` router index/relabel alignment.
- **The interior-`hρe₀` bundle re-anchoring LANDED — the dispatch's `hρe₀` is now a one-call read-off
  (2026-06-24, axiom-clean, build/lint/warning-clean).** `Graph.ChainData.interior_hρe₀_of_baseWidening`
  (`CaseIII/Relabel/ForkedArm.lean`, after `interior_hρe₀_of_widening`): takes LEAF-3's `hedgeGv` bundle
  in its **native existential shape** (over `Gw = G − vtx 1`, `hcomb` at `hingeRow (vtx 0) (vtx 2) ρ₀`)
  + `hends_i`, folds it straight into `interior_hρe₀_of_widening`. The three re-anchorings the hand-off
  flagged are internal: `G − vtx 1`-link → `G`-link (`removeVertex_isLink.mp`); `hcomb` is `.symm`;
  **`hdeg1`** = `deg_two` at `vtx 2` (valid since `3 ≤ d`) gives `{edge 1, edge 2}`, and `edge 1` (the
  `link`-field `vtx 1`-incident edge) is excluded by `removeVertex_isLink`'s `≠ vtx 1` endpoints, so
  `edge 2`. The `0 < (↑⟨2,_⟩)` arg to `deg_two` needed the `show 0 < (2:ℕ) by omega` defeq-force
  (TACTICS-QUIRKS § 63, applied — not new friction). So the dispatch supplies only `hends_i`; no manual
  re-anchoring. NO `hρGv`, no new LA.
- **The interior-split `heab_off` accessor LANDED — the dispatch's off-slot `hS`-router input is now a
  `ChainData` read-off (2026-06-24, axiom-clean, build/lint/warning-clean).**
  `Graph.ChainData.removeVertex_isLink_edge_succ_pred_off` (`Induction/Operations.lean`, beside
  `isLink_eq_succ_or_pred_or_removeVertex` in the interior-vertex split-data section): for interior `i`
  (`0 < i`), every `Gv = G.removeVertex (vtx i.castSucc)` link uses an edge `≠ edge i` (`= e_a`) and
  `≠ edge (i−1)` (`= e_b`). Both chain edges are incident to the removed body `v` (`isLink_succ_edge`/
  `isLink_pred_edge`), but a `Gv`-link has both endpoints `≠ v` (`removeVertex_isLink`), so the
  endpoint match `eq_and_eq_or_eq_and_eq` forces a contradiction. This is the `heab_off` input the
  dispatch feeds the per-member `hS` router `bottomRelabel_image_mem_span_caseIIICandidate` /
  `bottomRelabel_rigidityRows_mem_span_caseIIICandidate` (and via the latter, LEAF-B2's universal `hS`).
  A 3-step combinatorial-setup leaf in the established interior-split idiom — NO `hρGv`, no new LA, no
  friction. Homed in `Operations.lean` (the `ChainData` definition's file) per the where-it-lives rule.
- **⚠️ DISPATCH RECON — route-B interior `hS` is UNSATISFIABLE; BLOCKED on a phase decision (2026-06-24,
  read-only compiler-checked spike, opus, design §(4.26)).** Built the `chainData_dispatch` `Fin cd.d`
  router skeleton, fired LEAF-3, and verified slot-by-slot: the interior arm's `hgate`/`hρe₀`/`hvanish`/
  `heab_off`/`hrec`/`hrhat`/`hIH` are all mechanically dischargeable (the `hρe₀` chain
  `interior_hρe₀_of_baseWidening` discharges cleanly), BUT the interior **`hS`** is not — the wrap-edge
  `edge i` base rows relabel (via `chainData_bottom_relabel`'s `Or.inr`) to the `(a,b)`-block tag
  `hingeRow (vtx (i+1)) (vtx (i−1)) ρ'`, NOT in the candidate span (kernel-checked: the router's
  `hG_eb_cand : G.IsLink e_b (vtx (i+1)) (vtx (i−1))` contradicts `isLink_pred_edge`). The project's own
  `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` docstring names this as the wall (the `±r` GROUP, not
  a base-block row). Root cause: LEAF-B2's *individual*-row universal `hS` re-introduces the member-mapping
  wall §(4.18)–(4.24); KT (6.62)'s bottom block lives in the SEED framework `ofNormals (G − vᵢ) endsρ qρ`,
  NOT the corner-overridden `caseIIICandidate`. Resolution (coordinator's call): option-A landed group
  transport (`case_III_arm_corner_assembly`) vs. seed-framework base block re-architecture. GAP 2 (smaller):
  the `ends`-orientation pins (`hends_i`/`hends_ea`/`he₀rec`) need a `Function.update` override since LEAF-3's
  `ends = Q.ends` is only orientation-free. Lesson (deferred-hypothesis-unsat composing landed-sound leaves)
  → already in DESIGN.md *Constructibility recon*; the §(4.26) entry is the full kernel trace.
- **ROUTE-4 NEW LEAF 2 LANDED — the wall-free seed-`W` producer (2026-06-24, build/lint/warning-clean).**
  `PanelHingeFramework.exists_seed_base_block` (`CaseIII/Candidate.lean`, after LEAF-B2): the bottom-block
  `W`-producer that escapes the route-B interior-`hS` wall by taking `W := span (ofNormals (G − vᵢ) endsρ
  qρ).rigidityRows` (the candidate's OWN seed rows) instead of transporting a base family. `hWS` (off-slot
  bridge `hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link`, edges `≠ e_a,e_b` from `heab_off`)
  and `hW` (`ofNormals_removeVertex_rigidityRow_comp_single_self` via `span_induction`) close mechanically,
  NO `hS`/`hρGv`; `hWcard` ⟵ the `hseedrank` hypothesis. `hseedrank` is the genuinely-true candidate-seed
  rank (KT 6.62), NOT unsatisfiable like route B's `hG_eb_cand` — NEW LEAF 1 will discharge it. The body is
  the kernel-verified `probe3_seed_W` from the §(4.27) scoping recon, banked as a real lemma. NEXT = NEW
  LEAF 1 (the relabel rank-iso, make-or-break).
