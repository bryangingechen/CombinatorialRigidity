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

**⚠️ ROUTE 4-BARE BLOCKED (design §I.8.24(4.28), 2026-06-24) — the make-or-break NEW LEAF 1 is PROVABLY
FALSE for the BARE seed; the §(4.27) scoping verdict erred (bare vs splitOff).** A make-or-break build of
NEW LEAF 1 (the general-`d` relabel SET-image equality discharging `exists_seed_base_block`'s `hseedrank`)
found, kernel-confirmed against the landed bricks, that `hseedrank` for the BARE candidate seed
`ofNormals (G − vᵢ) endsρ qρ` is UNSATISFIABLE: the base wrap edge `edge i` (link `vtx i`–`vtx (i+1)`, a
genuine `G − vtx 1` row) relabels under `σ = shiftPerm i.castSucc` to the pair `(vtx (i−1), vtx (i+1))` —
the `Or.inr` WRAP branch of the landed `removeVertex_genuine_shiftRelabel` (`Relabel/Chain.lean:249`), NOT a
genuine `G − vᵢ` link — and there is **no `G`-edge** on `(vtx (i−1), vtx (i+1))` (the interior `deg_two`
closure), so `R(G − vᵢ)` is MISSING that row and the relabel is not a row-set bijection; finrank is not
preserved. The landed `d=3` `rigidityRows_ofNormals_relabel` (`Relabel/Basic.lean:648`) is stated for
**splitOff** frameworks (`ofNormals (G.splitOff …) …`), where the fresh short-circuit edge `e₀` ABSORBS the
wrap-edge image — exactly what the bare seed lacks. This is the **wrap-edge member-mapping wall a THIRD time**
(route B's `hS` §(4.26); now route 4-bare's `hseedrank`); route 4 *moved* the wall from `hS` to `hseedrank`,
did not escape it. **NEW LEAF 2 `exists_seed_base_block` (LANDED 057a86e) is sound as a lemma but its
`hseedrank` hypothesis is UNSATISFIABLE for the bare seed it hardcodes** — a dead conditional unless
re-targeted. **The viable variant is route 4-SPLITOFF** (LEAF-1 unblock-1): re-target `W` to the candidate
**splitOff** seed `ofNormals (G.splitOff vᵢ … e₀') endsρ qρ` (wrap-absorbing) + re-state the rank cert's
`W ≤ span(candidate)` (handle the `e₀'` short-circuit row) — a genuine rank-cert re-statement, viability
UNVERIFIED (the §(4.27) scoping already erred once on bare-vs-splitOff). **PHASE-DIRECTION DECISION PENDING
(user):** route 4-splitOff (verify-first vs build) vs the deeper fallback (route A full `Matrix` /
honest-conditional (C)). Below: the (now-DEAD-for-bare) LEAF-2 description, retained as the splitOff
re-target's starting point.

**[SUPERSEDED — route 4-bare] NEW LEAF 2 (`exists_seed_base_block`, LANDED 057a86e):** It takes `W :=` the candidate's OWN seed framework
`ofNormals (G − vᵢ) endsρ qρ`'s rigidity-row span, and discharges the three cert obligations with **NO
`hS`, NO `hρGv`**: `hWS` (off-slot bridge — every seed `(G−vᵢ)`-row is a candidate row, edge `≠ e_a,e_b`),
`hW` (off-`vᵢ` vanishing — every seed row is a `(G−vᵢ)`-link), and `hWcard` reduced to the single hypothesis
`hseedrank : finrank (span R(G−vᵢ, q∘σ)) = D·(|Gv|−1)` (the candidate seed's rigidity rank). `hseedrank` is
the genuinely-true relabel rank-iso (KT 6.62) that **NEW LEAF 1** (`rigidityRows_ofNormals_relabel`
general-`d`, the make-or-break de-risk) will discharge — it is NOT an unsatisfiable hypothesis like route B's
`hG_eb_cand`. **NEXT: NEW LEAF 1.** Banking LEAF 2 now (with `hseedrank` as a hypothesis) protects the
kernel-verified seed-`W` reduction from context loss; LEAF 1 carries the residual risk (the cycle-perm
`σσ=id` / splitOff-vs-removeVertex bookkeeping — design §(4.27)).

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

- **⚠️ NEW LEAF 1 BLOCKED — route 4-bare's `hseedrank` is PROVABLY FALSE (design §(4.28), 2026-06-24); a
  PHASE-DIRECTION DECISION is owed.** The make-or-break build confirmed (kernel-checked vs the landed bricks)
  that `hseedrank : finrank (span R(G − vᵢ, q∘σ)) = D·(|Gv|−1)` for the BARE seed is unsatisfiable: the base
  wrap edge `edge i` relabels to the non-chain pair `(vtx (i−1), vtx (i+1))` (the `Or.inr` WRAP branch of the
  landed `removeVertex_genuine_shiftRelabel`, `Relabel/Chain.lean:249`), which has no `G − vᵢ` row, so the
  bare seed is MISSING the wrap-edge image and its rank `< D·(|Gv|−1)`. The "`funLeft σ` linear-iso preserves
  finrank" fallback FAILS for the bare seed: `funLeft σ` preserves the finrank of the *image* span, but the
  bare-seed span ≠ that image span (the image lands the wrap edge on `(vtx(i−1),vtx(i+1))`, absent from the
  bare seed). The landed `d=3` `rigidityRows_ofNormals_relabel` (`Relabel/Basic.lean:648`) is for **splitOff**
  frameworks, where the fresh `e₀` short-circuit edge ABSORBS the wrap-edge image — the bare seed lacks it.
  **So NEW LEAF 2 `exists_seed_base_block` (LANDED 057a86e) is a sound lemma with an UNSATISFIABLE `hseedrank`
  for the bare seed it hardcodes** (the satisfiability trap a THIRD time — route B's `hS`, now route 4-bare's
  `hseedrank`). **Candidate fix = route 4-SPLITOFF:** re-target `W` to the candidate splitOff seed
  `ofNormals (G.splitOff vᵢ … e₀') endsρ qρ` (wrap-absorbing) + re-state the rank cert's `W ≤ span(candidate)`
  to handle the `e₀'` short-circuit row — a genuine rank-cert re-statement, **viability UNVERIFIED** (the
  §(4.27) scoping already erred once on bare-vs-splitOff, so a verify-first spike is prudent). The deeper
  fallback is route A (full `Matrix`) / honest-conditional (C). **This is a user decision** — surfaced.

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

**⚠️ ROUTE 4-BARE BLOCKED (design §(4.28)) — PHASE-DIRECTION DECISION PENDING (user).** The make-or-break
NEW LEAF 1 build found route 4-bare's `hseedrank` PROVABLY FALSE for the bare seed (the wrap edge `edge i`
relabels to a non-chain pair `(vtx(i−1),vtx(i+1))` absent from `R(G − vᵢ)`; the `d=3` relabel iso is
splitOff-only). NEW LEAF 2 `exists_seed_base_block` (LANDED 057a86e) is sound but its `hseedrank` is
unsatisfiable for the bare seed it hardcodes. **Do NOT build NEW LEAF 1 against the bare seed** — it cannot
be proved. The candidate fix is **route 4-SPLITOFF** (re-target `W` to the candidate splitOff seed
`ofNormals (G.splitOff vᵢ … e₀') endsρ qρ`, wrap-absorbing, + a rank-cert re-statement), **viability
UNVERIFIED**; the deeper fallback is route A (`Matrix`) / honest-conditional (C). The next concrete step
awaits the user's direction (route 4-splitOff verify-first vs build vs deeper fallback). See *Blockers* +
design §(4.28). **The pre-decision route-4 build plan below is SUPERSEDED for the bare seed** (kept as the
splitOff re-target's starting point — LEAF 2's `hWS`/`hW` shape and the slot discharges carry over; only the
seed framework + the rank source change).

**[SUPERSEDED for bare seed] The route-4 build plan (design §(4.27)):**
1. **✅ NEW LEAF 2 — the seed-`W` producer (LANDED 2026-06-24):** `PanelHingeFramework.exists_seed_base_block`
   (`CaseIII/Candidate.lean`, after LEAF-B2). `W := candidate seed span`; `hWS` (off-slot bridge) / `hW`
   (off-`vᵢ` vanishing) close mechanically, NO `hS`/`hρGv`; `hWcard` ⟵ the hypothesis `hseedrank`. Replaces
   `case_III_arm_corner_assembly_via_leafB2` for the interior arm.
2. **NEW LEAF 1 — general-`d` `rigidityRows_ofNormals_relabel`** (NEXT, the de-risk target): the chain
   generalization of the LANDED `d=3` SET-image equality `R(relabelled seed) = (funLeft σ).dualMap '' R(base
   seed)` (`Relabel/Basic.lean:648`, `hρGv`-FREE) from the single swap to `shiftPerm i.castSucc` /
   `shiftEdgePerm i`, giving `hseedrank` from the base IH. Bricks landed
   (`ofNormals_supportExtensor_relabel_perm`, `blockRow_relabel_perm`, `rigidityRow_relabel_to_genuine`,
   `chainData_bottom_relabel`); MEDIUM risk — the `d=3` proof uses involution facts `hσσ`/`hρρ` that FAIL
   for a cycle, and the bare `removeVertex` vs splitOff bookkeeping needs care (the candidate seed is bare
   `G − vᵢ`, but the `d=3` SET-equality is stated for splitOff frameworks; bridging needs the redundant
   `e₀`-row deletion). If it walls → BLOCKED, coordinator adjudicates the deeper reconsideration (route A
   `Matrix` / honest-conditional (C)).
3. **the `chainData_dispatch` `Fin cd.d` router** (interior arm via LEAF 2 + the LANDED group transport
   `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` for the `±r` corner) + the `ends`-orientation
   override (GAP 2) + **CHAIN-5**.

**Once LEAF 1 lands,** the rest of the dispatch wiring is in place: the `Fin cd.d` case-split fires
LEAF-3 once at the base `v₁`-split and routes `i < 2` → `chainData_split_realization` (base/`d=3`,
owes only `htrans`), `2 ≤ i` → the chosen interior producer. The interior `hgate`
(`shiftPerm_apply_vtx_off` off-cycle + `candidateVtx_succ_eq`), `hρe₀` (`interior_hρe₀_of_baseWidening`
fed LEAF-3's `hedgeGv` + `hends_i`), `hvanish` (`shiftPerm_vtx_top` → `ofNormals_removeVertex_…`), and
`heab_off` (`removeVertex_isLink_edge_succ_pred_off`) discharges are all spike-verified mechanical and
reusable under either route. NOTE the `hends_i`/`hends_ea`/`hends_eb`/`he₀rec` slots need an `ends`-orientation
override (LEAF-3's `ends = Q.ends` is only orientation-free `hends'`; cf. `chainData_split_realization`'s
`ends₁` `Function.update`) — additional wiring, GAP 2 in the spike.

Route-B leaf inventory (all LANDED, sound in isolation, COMPOSITION blocked at interior `hS`): LEAF-B1,
LEAF-B2, the `hvanish` lemma, the `hS` router, `case_III_arm_corner_assembly_via_leafB2`,
`interior_hρe₀_of_widening` / `_of_baseWidening`, `removeVertex_isLink_edge_succ_pred_off`, LEAF-3, LEAF-B3.
Remaining = adjudicate §(4.26), then build the interior arm against the chosen route + CHAIN-5, then
ENTRY + ASSEMBLY (parallel-safe).

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
