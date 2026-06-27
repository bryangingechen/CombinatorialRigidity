# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress. Opened 2026-06-26 as the *fifth* CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d +
23e + 23f). 23e landed the KT-faithful A3-transposed rank certificate + its LA scaffolding axiom-clean
(`notes/Phase23e.md`); 23f builds the **geometry arm** that *constructs* the cert's block data from the
IH-fed `cGv` widening, then the candidate-matching gate bridge and the general-`k` chain dispatch + CHAIN-5.
**Phase 23 stays in progress.** The authoritative recon is `notes/Phase23-design.md` §(4.54) (the re-pointed
hand-off, the three-leaf geometry-arm plan, the framework-vs-arm split, the both-block coupling). Program map:
`notes/MolecularConjecture.md`.

## Current state

**αE1 + αE2 + αE3 LANDED (axiom-clean). Next concrete commit = αE4** — the augmented wrapper
`case_III_arm_realization_aug` (`ForkedArm.lean`, the clone of the LANDED
`case_III_arm_realization_rowOp` `:315` with `rigidityMatrixEdge→rigidityMatrixEdgeAug` + the `±r`
corner row sourced from the `inr ()` slot, KEEPING `(re,hre,L₀,hM'eq,hB,hA=leaf(iii),hD)`; B1/B2
build `Lrow`/reduce `hblock` in-body; fires the LANDED αE3 cert; the ⚑ `hblock`-`fromBlocks A 0 C D`
crux over the augmented `⊕ Unit` index is the one residual). αE3 added `theorem
PanelHingeFramework.case_III_rank_certification_aug` to `Candidate.lean` (after
`case_III_rank_certification_zero₁₂` `:2446`): the augmented clone with
`rigidityMatrixEdge→rigidityMatrixEdgeAug`, `Lrow`/`re` carrying the `⊕ Unit` row index, ADD
`(rRow, hr : rRow ∈ span F₀.rigidityRows)`, KEEP `(Lrow,hLrow,U,hU,re,en,A,C,D,hblock=fromBlocks A 0
C D,hA,hD)`; body fires the LANDED αE2 engine `finrank_span_rigidityRows_ge_of_aug_submatrix_
fromBlocks_zero₁₂` then the same `hVcard`/`hVone` count tail. **The §(4.66) "no row op" plan was CORRECTED
2026-06-27 (design §(4.66.F/G), source-confirmed + spike-checked): route (α)'s augmented matrix is
correct + needed (the genuine `ρ₀` corner row no `rigidityMatrixEdge` index can carry), but it does
NOT remove the row op — `Lrow` is STILL mandatory to zero the corner's off-`v` `B` block, because the
interior bottom has v-incident `e_b`-fill rows making `C = toBlocks₂₁ ≠ 0` (the settled §(4.62), which
§(4.66) contradicted). So the backbone is `Rank.lean:622` (`_zero₁₂`, with `Lrow`), NOT `:528`
(`_zero₂₁`).** αE1 added `def BodyHingeFramework.rigidityMatrixEdgeAug` + `theorem
rigidityMatrixEdgeAug_rank_le_finrank_span` to `Concrete.lean` (after
`rigidityMatrixEdge_rank_eq_finrank_span_rigidityRows`). αE2 added the engine `theorem
BodyHingeFramework.finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂` (right after the
edge `_zero₁₂` engine `…_of_edge_submatrix_fromBlocks_zero₁₂` `:1042`): the augmented clone with
matrix `rigidityMatrixEdge→rigidityMatrixEdgeAug ends hgp rRow`, row index `(({e//…}×Fin(D−1)))⊕Unit`,
ADDING `(rRow, hr : rRow ∈ span rigidityRows)`, KEEPING `(Lrow,hLrow,U,hU,re,en,hblock=fromBlocks A 0 C
D,hA,hD)`. Body fires the LANDED backbone `Rank.lean:622` on `rigidityMatrixEdgeAug` then `.trans` the
αE1 *inequality* (the edge engine's final `rwa` of the *equality* becomes a `.trans` — augmenting can
only fail to add rank). The `[Fintype α][DecidableEq α][DecidableEq β][Finite β][Fintype {e//…}]`
instances αE1 dropped ARE present here (the backbone + αE1's `_rank_le` need them). Then αE3 (augmented
cert) → αE4 (augmented wrapper = the landed `_rowOp` wrapper with
`rigidityMatrixEdge→rigidityMatrixEdgeAug` + the `±r` corner row from the `inr` slot, KEEPING
`(Lrow,L₀,hB,hA=leaf(iii),hD)`; the ⚑ `hblock`-`fromBlocks A 0 C D` crux) → αE5 (delete ONLY the
`(e_b,j₀)`/`hred` machinery, KEEP B1/B2/BOT-3′/leaf(i)/(iii)) → αE6 → αD1–αD7 (dispatch). Full plan +
exact signatures: design §(4.66.G) (supersedes §(4.66.D) on `Lrow`).

**HEADLINE (verified — see §(4.66.A) + the §(4.66.F) CORRECTION).** The genuine `hingeRow a b ρ₀`
row CANNOT be a re-key of `re` into `rigidityMatrixEdge` — that matrix's row index `{e//e∈E}×Fin(D−1)`
forces every row to be a `blockBasisOn` read (no index reads `ρ₀`, = §(4.65.B-3)). The buildable
realization is an **AUGMENTED matrix** with a `⊕ Unit` row carrying the genuine functional (the
literal-`Matrix` mirror of the dual-space chain cert's `g`-member). The augmented matrix fixes the
`ρ₀`-row SOURCING (the §(4.65)-refuted `(e_b,j₀)`/`hred` problem dissolves). **CORRECTION (§(4.66.F),
2026-06-27): it does NOT remove the row op.** A `Lrow` is STILL needed to zero the corner's off-`v`
`B` block (`B≠0`: the `±r` row reads `a,b ≠ v`; the column op only zeros off-`v` for the `e_a`-panel
rows). HA = leaf (iii) operated `(A−L₀C).row` (NOT bare `corner_hA'_of_gate`); HB/`L₀`/B1/B2/BOT-3′ all
STAY. The `Rank.lean` backbone is `rank_ge_…_zero₁₂` (`:622`, `_zero₁₂`, with `Lrow`), `M`-generic,
fires on `augM` unchanged. Spike (`SpikeAlphaE4.lean`, 3 probes — both engine shapes compose at the
rank level; `…_toBlocks₂₁_eq_zero` needs `hbot` both-≠-v) built sorry-free, deleted before commit.

**Reuses (route-(α)-stable, verified row-family-agnostic by reading the signatures):**
`rank_ge_…_zero₁₂` + `rank_of_coordEquiv` (`Rank.lean`/`Concrete.lean`), the realization tail
`case_III_realization_of_rank` (consumes only `hrank`), D1 `interior_hsplitGP`, HD, `corner_hA'_of_gate`
(`Concrete.lean:620`), `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`Candidate.lean:2133`),
`span_range_rigidityRowFunEdge`, the column op `U` + `columnSplit` + the `toBlocks₂₁/₂₂` family (on the
`inl` sub-block), and the uniform-`blockBasisOn` BOTTOM (BOT-1/2-free/R1/HD). **Both gates ground to
discriminator outputs:** `ρ₀ (panelSupportExtensor (q(a,·))(q(b,·))) = 0` (`:1511`, the membership
`hperp`) and `ρ₀ (panelSupportExtensor (q(candidateVtx i,·)) n') ≠ 0` (`:1535`, the LI gate `hρe₀`) —
DIFFERENT extensors, jointly satisfiable (§(4.66.C)). **DELETES ONLY the `(e_b,j₀)`-collision
machinery** (BOT-2′ / the avoiding-engine / D2 / `cornerRowInjection` family — the bits that handled
the `(e_b,j₀)` corner-row sourcing route (α)'s augmented `inr` slot replaces). **CORRECTION (§(4.66.F)):
B1/B2/BOT-3′/leaf(i)/leaf(iii) STAY — they discharge the still-required row op `Lrow` (the corner off-`v`
`B`-zeroing).** NO `blockBasisOn`-def / motive / frozen-contract change. Tree clean; `d=3` fully green;
D1/HD + RE injection in tree axiom-clean.

**⚑ The ONE residual not yet compiler-locked** (flagged, §(4.66.E/F)): αE4's `hblock = fromBlocks A 0 C D`
decomposition of `Lrow * augM * U` (the `_zero₁₂`, top-right zero, via `Lrow`) — NOT producible from the
column op alone (§(4.66.F)). The spike verified the rank bound + both engine shapes compose, NOT the full
`Lrow`-`fromBlocks` assembly over the augmented `⊕ Unit` index. It is the landed B2
`rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂` reduction applied to `augM` — a bounded
matrix-bookkeeping re-state, NOT new math. STOP and re-flag at αE4-build if the landed bricks do not cover
the augmented index.

**Landed leaves now ORPHANED by route (α)** (sound Lean, αE5 delete; design §(4.66.F/G)). **ONLY the
`(e_b,j₀)`-collision machinery** — BOT-2′, the avoiding-engine, D2, the `cornerRowInjection` family (the
`±r`-as-`(e_b,j₀)`-index host) — is orphaned (route (α)'s augmented `inr` slot replaces it). **The row-op
apparatus B1/B2/BOT-3′/leaf(i)/leaf(iii) + `finScrewDimSplitCorner` STAYS** (the row op is mandatory;
leaf (iii) reads its `em₁` from `finScrewDimSplitCorner`). The `_rowOp` wrapper is the αE4 BASE (matrix
swapped to `rigidityMatrixEdgeAug`), not deleted. **Route-(α)-REUSED (in tree, axiom-clean):** D1
`interior_hsplitGP`, HD, the uniform-`blockBasisOn` bottom (BOT-1/2-free/R1), the `Rank.lean` `_zero₁₂`
backbone + column op + row op (B1/B2), leaf (iii), `hingeRow_mem_…reproduced`. The cert's card target is unchanged:
`card m₁ + card m₂ = D·(|V(G)|−1) ≤ (D−1)·|E(G)|` (an inequality; no isostatic-tightness forced).
`d=3` stays fully green (zero-regression, hard constraint).

## Architectural choices made up front (inherited from 23e / the frozen contract)

- **Cert is consumed, not re-derived.** The 23e cert chain is axiom-clean and SATISFIABLE; 23f only
  *produces* its block data. Build `hblock`/`hA` against the literal `Lrow * M * U` product, NOT the
  component leaves in isolation (the §(4.46)/(4.54) lesson — compiler-check the FULL composition before
  declaring "remaining = assembly"; two leaves were elided when this was skipped).
- **The `±r` corner row reads `ρ₀` directly (route (α); §(4.66.A)), but the row op is STILL needed
  (CORRECTED §(4.66.F)).** The augmented matrix's `inr ()` row IS the genuine `hingeRow a b ρ₀`, which fixes
  the `ρ₀`-row SOURCING (§(4.65)). But the corner's off-`v` `B` block is nonzero (the row reads `a,b ≠ v`),
  so the row op `Lrow` is STILL mandatory to zero it — and the interior bottom's v-incident `e_b`-fill rows
  make `C = toBlocks₂₁ ≠ 0`, so the shape is `_zero₁₂` (`fromBlocks A 0 C D`, top-right zero, via `Lrow`),
  NOT `_zero₂₁` (the column op alone gives `_zero₂₁`/bottom-left zero, which is unavailable). 23e's "zeroing
  `B` and mutating `A→A'` are ONE row op" framing STANDS; route (α) only makes the row op simpler (it no
  longer converts `blockBasisOn(e_b,j₀)`→`ρ₀`). HA = leaf (iii) operated `(A−L₀C).row`; the `fromBlocks A 0 C
  D` is the B2 reduction applied to `augM` (αE4's ⚑ residual).
- **`d=3` zero-regression via the cert FORK.** `d=3` keeps the `_matrix`/M₃ path; only the general-`d` arm
  routes through `case_III_rank_certification_zero₁₂`. Do NOT unify the two.
- **Below the CHAIN↔ENTRY contract + the motive/IH.** The geometry arm + dispatch are below C.3/C.1 and the
  0-dof motive. The frozen interface (C.0–C.6) + the sanctioned C.3 `hIH` addition stay valid.

## Lemma checklist

**The LIVE forward plan is item (4) — route (α)'s αE1–αD7 (design §(4.66.G), CORRECTED §(4.66.F)).** Items
(i)–(HMEQ) below record what landed. **CORRECTION §(4.66.F): route (α) KEEPS the row-op apparatus**
(B1/B2/BOT-3′/leaf(i)/leaf(iii)/`finScrewDimSplitCorner` discharge the still-required `Lrow`; the `_rowOp`
wrapper + `_zero₁₂` cert + edge-engine are the αE2–αE4 BASE, matrix-swapped to `rigidityMatrixEdgeAug`).
ONLY the `(e_b,j₀)`-collision machinery (BOT-2/2′, avoiding-engine, D2, `cornerRowInjection` proper, leaves
(ii)/(iv)) is orphaned (αE5 delete). HA/HB/3c are via leaf (iii)/BOT-3′/αD1 (NOT dissolved). HD + the bottom
selection (BOT-1/R1) + HMEQ are route-(α)-REUSED.

- [x] **(i)** `matrix_eq_mul_of_dual_row_comb` (`Concrete.lean`) — `cGv`→`w` `B=L₀·D` core (superseded for HB by BOT-3′; kept for explicit-weight consumers).
- [x] **(ii)/(iv)** `reindex_rowOp_isUnit_det` / `reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂` (`Rank.lean`) — the BIJECTION unit-det + `hblock` bridges. SUPERSEDED by B1/B2 (strict injection, §(4.55)); zero-caller orphans, kept as the bijection special case.
- [x] **(iii)** `corner_hA_zero₁₂_of_gate` (`Concrete.lean:657`) — operated-corner `hA` (`ρ₀`-`hAeq` + gate). **KEPT (CORRECTED §(4.66.F))** — route (α) STILL row-ops (the `_zero₁₂` shape), so leaf (iii)'s operated `(A−L₀C).row` IS αD3's HA (NOT the bare `corner_hA'_of_gate`).
- [x] **(recon §(4.55))** `re` shape = STRICT INJECTION (`card m₁+card m₂ ≤ card p`, an inequality; no bijection in general). (ii)/(iv) bijection-only don't serve; B1/B2 subsume them.
- [x] **(B1)/(B2)** `exists_rowOp_of_strictInjection` / `rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂` (`Rank.lean`) — strict-injection unit-det `Lrow` (+ off-image vanishing) + the entrywise `hblock` reducer to `fromBlocks (A−L₀C) 0 C D` (no `Equiv` middle index). Subsume (ii)/(iv).
- [x] **wrapper SKELETON** `case_III_arm_realization_rowOp` (`ForkedArm.lean`) — takes `(re,hre,L₀,hM'eq,hB,hA,hD)`, builds `Lrow`/`U`/`en`/`hblock` in-body, fires the cert (`A` slot = OPERATED `A−L₀C`; `C` free — `_zero₁₂` clears the §(4.41) wall), runs the realization tail. §(4.56) spike: composes sorry-free. OWED: the 5 carried hyps (RE done; HMEQ/HB/HA/HD below).
- [x] **(BOT-3′)** `matrix_eq_mul_of_span_mem` (`Concrete.lean`) — route-(b) HB: recovers `L₀` from `hmem : φ i ∈ span(range χ)` (span-membership sibling of leaf (i)). Subsumes the dissolved BOT-3 `μ`-match.
- [x] **(BOT-1)** `span_range_hingeRow_crossFramework_eq_rigidityRows` (`Basic.lean`) — abstract cross-framework span SET-identity (candidate a-shifted family spans `span R(Gab).rigidityRows`, finrank `card m₂`). NOT instantiable over full `E(G)` (`e_a`'s a-shift → `(a,a)` self-loop breaks `hlink₁`, §(4.60.B)); the dispatch uses R1 instead. Stays in tree as the unrestricted form.
- [x] **(R1)** `..._crossFramework_eq_rigidityRows_of_off` + `hingeRow_self` (`@[simp]`, `hingeRow a a = 0`) (`Basic.lean`) — the restricted-edge variant (matching over genuine edges `{e // P e}`; `hoff` zeroes the `e_a` row) discharging the bridge's full-`p` `hspan_id`.
- [x] **(BOT-2)** the FREE basis-pick: `exists_finCard_linearIndependent_selection` (`Rank.lean` engine) + `bottom_selection_of_crossFramework_span` (`Concrete.lean` bridge → `(re,hbot2,hbot1,hrank)`; `hbot1` tautology, `hrank` = `finrank_span_eq_card`). SUPERSEDED for the wrapper by BOT-2′ (the free pick can hit `(e_b,j₀)`, §(4.61)); kept.
- [x] **(avoiding engine)** `exists_finCard_linearIndependent_selection_avoiding` (`Rank.lean`) — exclusion-steered companion: a redundant index `i₀` (`hred`) ⟹ an LI `Fin N`-selection AVOIDING `i₀`.
- [x] **(BOT-2′)** `bottom_selection_of_crossFramework_span_avoiding` (`Concrete.lean`) — EXCLUSION-steered bridge: BOT-2 + excluded `p₀=(e_b,j₀)` + redundancy `hred` → `(re,hbot2,hbot1,hrank)` PLUS `havoid : ∀ i, re i ≠ p₀`. Resolves the §(4.61) `(e_b,j₀)` tension.
- [x] **(RE) the strict row injection `re`/`hre`** — COMPLETE. Corner half (`cornerRowInjection`/`_injective`/`finScrewDimSplitCorner`, 460c0e3) + the `Sum.elim` assembly `cornerRowInjection_sumElim_injective` (`Concrete.lean` A5d): `re := Sum.elim (corner ∘ finScrewDimSplitCorner) bottom`, `hre` via `Function.Injective.sumElim` (`hdisj`: `Sum.inl` panel by `hbot_ne_ea`, `±r` slot by `havoid`). The `hdisj` inputs + the bottom's `(hspan_id via R1, hfr, hbot2_all, hred)` are carried hyps the dispatch discharges. HMEQ = mathlib `fromBlocks_toBlocks.symm`.
- [→] **(HA) via leaf (iii) (CORRECTED §(4.66.F) — NOT dissolved)**: route (α) STILL row-ops, so the cert's
  `hA` is the OPERATED `(A−L₀C).row`, discharged by leaf (iii) `corner_hA_zero₁₂_of_gate` (`:657`, KEPT) — which
  reads the operated corner as the `coordEquiv`-matrix of `[blockBasisOn(e_a,·); ρ₀]` (`em₁ := finScrewDimSplit
  Corner`) and closes via the bare `corner_hA'_of_gate` (`:620`) + the gate `hρe₀`. αD3. FLAG (§(4.66.F.iii)):
  whether the augmented `inr`-row's pin-already-`ρ₀` lets `hA` skip the `A−L₀C` mutation is the one sub-leaf
  needing the αD-dispatch entry geometry — do NOT assume it; default to leaf (iii)'s operated `hAeq`.
- [x] **(HD) the `Sum.elim`-`re` mixed-bottom block row-LI** (this commit) —
  `linearIndependent_toBlocks₂₂_row_sumElim_mixedBottom_of_finrank_eq` (`Concrete.lean`, right after BOT-2′):
  the wrapper's exact `hD : LinearIndependent ℝ D.row` for `re = Sum.elim (cornerRowInjection ∘ split) bottom`,
  a thin restatement of `…_mixedBottom_of_finrank_eq` (`w`-FREE, §(4.57.A)) with `re (Sum.inr i) = bottom i`
  defeq-reducing the producer's `hbot2`/`hbot1`/`hrank` to BOT-2′'s bottom-only outputs. Axiom-clean
  (`propext`/`Classical.choice`/`Quot.sound`). The dispatch feeds `hrank`'s `card m₂` from the split-off
  framework's def-`0` full-rank realization (`hsplitGP` via `splitOff_isMinimalKDof`, the C.3 `hIH` add).
- [x] **(HMEQ) CLOSES at the wrapper-fire** (§(4.64.A), kernel-confirmed) — `hM'eq =
  (Matrix.fromBlocks_toBlocks M').symm` with `M' := (R(F)*Uᵀ).submatrix re (columnSplit v).symm` and
  `A/B/C/D := M'.toBlocks₁₁/₁₂/₂₁/₂₂`. NO new lemma, NO sorry; pins `A/B/C/D` to ONE `M'` (the §(4.58.C)
  single-`D` concern fully discharged). HD likewise closes with `exact hD` (the §(4.63) defeq verified
  end-to-end). So owed at the fire reduces to HA(D7)/HB(D6)/the BOT-2′ inputs(D3–D4)/`?L₀`.
- [→] **(HB) via BOT-3′/leaf (i) (CORRECTED §(4.66.F) — NOT dissolved)**: the corner's off-`v` `B` block is
  nonzero (the `±r` row reads `a,b ≠ v`), so the cert STILL needs `hB : B = L₀·D` to zero it by the row op
  `Lrow`. BOT-3′ `matrix_eq_mul_of_span_mem` + leaf (i) `matrix_eq_mul_of_dual_row_comb` are KEPT (the
  `cGv`-widening `L₀` recovery, §(4.62.Q2): the genuine row `hingeRow a b ρ₀ = ∑ cGv·(Gv-rows)`). αD6.
- [→] **(3c) candidate-matching gate bridge → αD1** (route (α)): the `hρe₀` gate (`F.supportExtensor e_a` ↔
  `panelSupportExtensor (q(candidateVtx i)) n'` via `caseIIICandidate_supportExtensor_candidate`
  (`Candidate.lean:960`) + `candidateVtx_succ_eq` (`Operations.lean:2824`, `rfl`-level) + the `d=k+1`
  `ChainData` fact) is still needed — packaged in αD1's genuine-row bundle off the discriminator (`:1535`),
  NOT dissolved. §(4.66.D) αD1; verified against ground §(4.66.C).
- [~] **(4) the realization arm + dispatch — route (α), Layer plan = design §(4.66.G) (CORRECTED §(4.66.F)).**
  **αE1** (the augmented edge matrix `rigidityMatrixEdgeAug` + its `rank_le_finrank_span` bound) ✓ LANDED
  axiom-clean (`Concrete.lean`, after `rigidityMatrixEdge_rank_eq_finrank_span_rigidityRows`). **αE2**
  (the augmented engine `finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂`, `_zero₁₂`, WITH
  `Lrow`) ✓ LANDED axiom-clean (`Concrete.lean`, after the edge `_zero₁₂` engine `:1042`; body fires the
  backbone `Rank.lean:622` then `.trans` αE1). **αE3** augmented cert (`case_III_rank_certification_aug`, sibling
  of `case_III_rank_certification_zero₁₂` `:2446`, ADD `(rRow,hr)`, KEEP `(Lrow,…,hblock=fromBlocks A 0 C D,hA,hD)`,
  body fires αE2) ✓ LANDED axiom-clean (`Candidate.lean`, after `case_III_rank_certification_zero₁₂`). Then
  **αE4** augmented wrapper (`case_III_arm_realization_aug` = the LANDED `case_III_arm_realization_rowOp` with
  `rigidityMatrixEdge→rigidityMatrixEdgeAug` + `±r` from the `inr` slot, KEEPING `(L₀,hB,hA=leaf(iii),Lrow)`;
  the ⚑ `hblock` crux) → **αE5** delete ONLY the `(e_b,j₀)` machinery (KEEP B1/B2/BOT-3′/leaf(i)/(iii)) / **αE6**
  → **αD1–αD7** dispatch (αD1 = the genuine-row membership+gate bundle off the discriminator; αD2 = the reused
  `blockBasisOn` bottom; αD3 = leaf (iii) operated `hA`; αD4 = `hblock`/`hB` (the `_zero₁₂`-via-`Lrow`); αD5 fire;
  αD6 router; αD7 CHAIN-5, separable LAST). The §(4.64.B) D1–D8 opaque-basis plan is SUPERSEDED (D4 `hred`
  refuted, §(4.65)). D1 `interior_hsplitGP` ✓ LANDED (reused by αD2); D2 `bottom_selection_ne_corner_edge`
  ✓ LANDED but DISSOLVES under route (α) (deletable at αE5). Full exact signatures: §(4.66.G).

## Blockers / open questions

- **C.3 `hIH`-on-consume-shape addition — APPROVED** (user-adjudicated 2026-06-26, session #36; the actual
  contract reshape lands at D8/CHAIN-5 with `chainData_dispatch`). The interior arm needs the INTERIOR-split
  `hsplitGP` (`G.splitOff vᵢ …`), derivable only from `hIH` via `splitOff_isMinimalKDof` — D1
  `interior_hsplitGP` (the standalone leaf that consumes `hIH`) ✓ LANDED; the C.3 dispatch consume-shape gets
  the `hIH` field added when `chainData_dispatch` is wired (a one-field addition touching the C.0
  producer/consumer/ENTRY lockstep trio, NOT a motive/IH-strength change). Context: design §(4.43) *THE ONE
  INTERFACE OBLIGATION* + §C.3.
- **The `(e_b, j₀)` `hred` — RESOLVED + Layer-planned (route (α), design §(4.65)+§(4.66.A/F/G)).** `hred` for
  the literal opaque-basis `(e_b, j₀)` row was REFUTED (§(4.65.A/B): `blockBasisOn` opaque `Concrete.lean:510`;
  `ρ₀ ∈ hingeRowBlock e₀` of the splitoff ≠ `hingeRowBlock e_b` of the candidate). Route (α) re-shapes the `±r`
  row to the genuine `hingeRow a b ρ₀` via an **augmented matrix** (§(4.66.A); the `re`-rekey shape §(4.65.E)
  sketched is not buildable — no `rigidityMatrixEdge` index reads `ρ₀`). This DELETES ONLY the `(e_b,j₀)`-collision
  machinery (BOT-2′ / avoiding-engine / D2 / `cornerRowInjection` proper / leaves (ii)/(iv)). **CORRECTION
  (§(4.66.F)): the row-op apparatus B1/B2/BOT-3′/leaf(i)/leaf(iii) STAYS — the row op `Lrow` is STILL mandatory
  (the corner off-`v` `B`-zeroing; the backbone is `_zero₁₂`, NOT `_zero₂₁`).** Route (β) (§(4.18)–(4.30) walled
  `mkQ`) rejected. NO `blockBasisOn`-def / motive / contract change. The buildable Layer plan is §(4.66.G) (αE2 next).
- **⚑ The αE4 `hblock`-`fromBlocks A 0 C D` decomposition is the one residual** not compiler-locked — the
  `_zero₁₂` (top-right zero) shape via the row op `Lrow` (NOT producible from the column op alone, §(4.66.F)).
  Spike verified both engine shapes compose at the rank level + the gates, NOT the full `Lrow`-`fromBlocks`
  assembly over the augmented `⊕ Unit` index. It is the landed B2 `rowOp_strictInjection_submatrix_eq_fromBlocks
  _zero₁₂` reduction applied to `augM` — bounded matrix-bookkeeping, NOT new math; STOP and re-flag at αE4-build
  if the landed bricks do not cover the augmented index. Design §(4.66.F).
- **GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive) — orthogonal to the cert;
  tracked separately, lands with 23f/the spine.
- **Cleanup folded into αE5 (route (α), CORRECTED §(4.66.F)):** ONLY the `(e_b,j₀)`-collision leaves (BOT-2′,
  avoiding-engine, D2, `cornerRowInjection` proper, leaves (ii)/(iv)) are orphaned and get deleted (or
  `@[deprecated]`) — no blueprint pins, so no `\lean{...}` restate needed (§17 per-slice gate checked). B1/B2/
  BOT-3′/leaf(i)/leaf(iii)/`finScrewDimSplitCorner` STAY (they discharge the still-required row op); the
  `_zero₁₂` cert + `_rowOp` wrapper + edge-engine are the αE2–αE4 BASE (matrix swap), not retired.
- **Downstream (23g+):** ENTRY's `exists_chain_data_of_noRigid` reshape + floor lift + OD-1, then ASSEMBLY.
  The frozen contract (C.5/C.6) is invariant; none touches 23e's cert. ENTRY is parallel-safe.

## Hand-off / next phase

**Route (α) CHOSEN (user-adjudicated 2026-06-27); the Layer plan was CORRECTED 2026-06-27 (design
§(4.66.F/G), source-confirmed + spike-checked). αE1 + αE2 + αE3 LANDED; next concrete commit = αE4.**
D4's `hred` for the opaque-basis `(e_b, j₀)` row was REFUTED (compiler-checked, §(4.65.A/B)); the fix
re-shapes the `±r` corner row to read the genuine `hingeRow a b ρ₀` (KT eq. (6.66)) via an AUGMENTED
matrix (§(4.66.A) — NOT a `re`-rekey into `rigidityMatrixEdge`, which has no index reading `ρ₀`). αE1
landed the augmented edge matrix + its rank bound (`rigidityMatrixEdgeAug` +
`rigidityMatrixEdgeAug_rank_le_finrank_span`). αE2 landed the augmented engine
`finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂` (`Concrete.lean`, after the edge
`_zero₁₂` engine `:1042`; body fires the backbone `Rank.lean:622` on `rigidityMatrixEdgeAug` then
`.trans` αE1's inequality, KEEPING `(Lrow,hLrow,U,hU,re,en,hblock=fromBlocks A 0 C D,hA,hD)` + ADDING
`(rRow, hr : rRow ∈ span rigidityRows)`). αE3 (THIS COMMIT) landed the augmented cert
`case_III_rank_certification_aug` (`Candidate.lean`, after `case_III_rank_certification_zero₁₂`
`:2446`, axiom-clean — standard triple): the clone with `rigidityMatrixEdge→rigidityMatrixEdgeAug`,
`Lrow`/`re` carrying the `⊕ Unit` row index, ADD `(rRow, hr)`, KEEP `(Lrow,hLrow,U,hU,re,en,A,C,D,
hblock=fromBlocks A 0 C D,hA,hD)`; body fires αE2 then the same `hVcard`/`hVone` count tail. NO
friction (clone of αE2's clone shape; first-try compile after long-line wrapping).
**CORRECTION: route (α) does NOT remove the row op `Lrow` — it is STILL mandatory** (zeros the corner
off-`v` `B` block; the interior bottom's v-incident `e_b`-fill rows make `C=toBlocks₂₁≠0`, so the
backbone is `_zero₁₂`/`Rank.lean:622` WITH `Lrow`, NOT `_zero₂₁`/`:528`; the settled §(4.62), which
§(4.66) contradicted). The augmented matrix fixes only the `ρ₀`-row sourcing.

**αE4 (NEXT, `ForkedArm.lean`) — the augmented wrapper.** `theorem case_III_arm_realization_aug` =
the clone of the LANDED `case_III_arm_realization_rowOp` (`ForkedArm.lean:315`) with the matrix
swapped `rigidityMatrixEdge → rigidityMatrixEdgeAug` + the `±r` corner row sourced from the `inr ()`
slot, KEEPING `(re, hre, L₀, hM'eq, hB, hA = leaf(iii) operated, hD)`; B1/B2 still build `Lrow`
in-body and B2 reduces `hblock`; the body fires the LANDED αE3 cert. **The ⚑ residual** (the one
not-yet-compiler-locked piece, §(4.66.E/F)): re-derive `hM'eq`/`hB`/`hblock = fromBlocks A 0 C D` for
the augmented matrix — the `inl` sub-block via the landed `submatrix_columnOp_*` family, the `inr`
row's reads via the genuine functional — i.e. the landed B2 `rowOp_strictInjection_submatrix_eq_
fromBlocks_zero₁₂` reduction applied to `augM` (bounded matrix-bookkeeping, NOT new math; STOP and
re-flag at αE4-build if the landed bricks do not cover the augmented `⊕ Unit` index). The
§(4.66.F.iii) flag (leaf (iii) operated `hA` vs bare `corner_hA'_of_gate`) is resolved here. Then αE5
(delete ONLY the `(e_b,j₀)` machinery; KEEP B1/B2/BOT-3′/leaf(i)/(iii)) / αE6 → αD1–αD7 (dispatch).
Full exact signatures: **design §(4.66.G)** (supersedes §(4.66.D) on `Lrow`); keep/delete map: §(4.66.F).

**Prior-commit landings (reused under route (α); build-state green):** D1 `interior_hsplitGP`
(`Realization.lean`, the interior split-off's IH-fed def-0 realization — feeds αD2's bottom `hrank`)
and HD `linearIndependent_toBlocks₂₂_row_…mixedBottom` (the bottom row-LI) remain LANDED axiom-clean.
D2 `bottom_selection_ne_corner_edge` is LANDED but DISSOLVES under route (α) (deletable at αE5 — it
only guarded against the `±r` slot reusing edge `e_b` inside the bottom index, gone now). The full
in-tree list (cite directly) is below; the §(4.64.B) D1–D8 opaque-basis dispatch is SUPERSEDED by
§(4.66.D) (D4 `hred` refuted, §(4.65)).

**CHAIN-5 is SEPARABLE** (the C.0 lockstep reshape of `hdispatch`/`hcand` to the frozen `ChainData`
record + `d=3` zero-regression adapter is plumbing AROUND a firing dispatch) — scope it LAST (αD7). On
the dispatch landing, the CHAIN layer closes and ENTRY (**23g**) opens; ASSEMBLY is **23h**.

**Cardinalities ground by stated facts (design §(4.57.C)/§(4.66.C)):** `card m₁ + card m₂ = D + D·(|V(Gv)|−1)
= D·(|V(G)|−1)` (the cert target, unchanged); `card m₂ = D·(|V(Gv)|−1) = D·(|V(Gab)|−1) = finrank (span
R(Gab).rigidityRows)` (`vertexSet_splitOff` = `rfl`, def-0 rigid identity). `e_a` is the corner (∈ `m₁`); the
augmented `±r` row (the genuine `hingeRow a b ρ₀`) is the corner's `inr ()` slot, pin-`v` column `−ρ₀` (nonzero,
expected in `m₁`); its off-`v` `B` content ≠ 0 (needs `Lrow`). **The bottom `m₂` is the `mixedBottom` (NOT
all pin-zero, §(4.62)): the `Gv` rows ARE pin-zero, but the v-incident `e_b`-fill rows (mandatory for the
full-rank `card m₂` count) read NONZERO at the pin — so `C = toBlocks₂₁ ≠ 0`, which is why the cert is the
`_zero₁₂` (top-right zero, via `Lrow`), not the `_zero₂₁` (bottom-left zero) shape.**

**In-tree, axiom-clean — the route-(α)-REUSED subset (cite directly):**
- **D1** `PanelHingeFramework.interior_hsplitGP` (`Realization.lean`, after `case_III_nested_rank_lower`) — the
  interior split-off's IH-fed def-0 realization (feeds αD2's bottom `hrank`). Sig: `(cd : G.ChainData n) (i)
  (hi : 0 < i) (hD3 : 3 ≤ bodyBarDim n) (hV4 : 4 ≤ |V(G)|) (hSimple) (hG : IsMinimalKDof n 0) (hnoRigid) (hIH :
  (k':ℤ)+Nonempty shape) : HasGenericFullRankRealization k n (G.splitOff (vtx i.castSucc)(vtx i.succ)(vtx
  ⟨i−1,_⟩.castSucc) cd.e₀)`. Body = the `Arms.lean:894`–911 chain-arm route at `Gab` (`splitOff_isMinimalKDof`
  + `splitOff_simple_of_noRigid_of_card` + `splitOff_vertexSet_ncard_lt`, then IH GP `.1`). Consumes the C.3
  `hIH` add.
- **HD** `BodyHingeFramework.linearIndependent_toBlocks₂₂_row_sumElim_mixedBottom_of_finrank_eq` (`Concrete.lean`,
  after BOT-2′) — the bottom-block `hD`; a thin defeq restatement of `…_mixedBottom_of_finrank_eq` over the
  `Sum.elim`-`re` (reusable for αD2's bottom; the `inr` corner slot is the genuine row, not the old `±r` index).
- `corner_hA'_of_gate` (`Concrete.lean:620`) — the bare `[blockBasisOn(e_a,·); ρ₀]`-LI iff `hρe₀`, the abstract
  fact leaf (iii) `corner_hA_zero₁₂_of_gate` (`:657`, KEPT) rests on; αD3's HA is leaf (iii)'s OPERATED `(A−L₀C).row`,
  NOT the bare form (§(4.66.F.iii)).
- `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`Candidate.lean:2133`) — the genuine `±r` row's
  `span rigidityRows` membership, consuming `hperp` (spike PROBE A, sorry-free); `span_range_rigidityRowFunEdge`
  (`Concrete.lean:766`) + `Matrix.rank_of_coordEquiv` (`Concrete.lean:99`) — αE1's `inl`-row membership + rank bridge.
- The 23e cert BACKBONE `Matrix.rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` (`Rank.lean:622`, `M`-generic,
  fires on `augM` unchanged); the column op `U` (`prodColumnOpEquiv`/`columnOp`) + `columnSplit` + the
  `submatrix_columnOp_…toBlocks₂₁_eq_zero` / `…toBlocks₂₂_eq_mixedBottom` family + the operated-entry bricks
  `…_apply_corner`/`_apply_eB_off_pin`/`_apply_off_pin`/`_apply_pin_zero` (apply to `augM*U`'s `inl` sub-block).
- The discriminator `exists_shared_redundancy_and_matched_candidate` (`Realization.lean:1481`) — produces the
  genuine row's two gates (`hperp` `:1511`, `hρe₀` `:1535`) + the W6b `cGv` widening; `chainData_split_w6b_gates`.
- The realization TAIL `case_III_realization_of_rank` (`Arms.lean:63`, consumes only `hrank`); `interior_hρe₀_of_baseWidening`
  (`ForkedArm.lean:669`, the gate the dual-space chain route reads — the genuine-row precedent).
- The bottom-arc spanning leaves (reused for αD2's `blockBasisOn` bottom): BOT-1/BOT-2-free/R1 (`Basic.lean`/
  `Concrete.lean`/`Rank.lean`) + `hingeRow_self` (`@[simp]`).

**In-tree but DELETED at αE5 (CORRECTED §(4.66.F) — ONLY the `(e_b,j₀)`-collision machinery; SOUND Lean, no
producer):** BOT-2′ `bottom_selection_of_crossFramework_span_avoiding`, the avoiding-engine
`exists_finCard_linearIndependent_selection_avoiding`, D2 `bottom_selection_ne_corner_edge`, the
`cornerRowInjection` proper (`+_injective`/`_sumElim_injective` — the `±r`-as-`(e_b,j₀)`-index host route (α)'s
`inr` slot replaces). Plus leaves (ii)/(iv) (`reindex_rowOp_isUnit_det`/`reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂`
— already zero-caller bijection orphans). **KEPT (REVERSING the earlier "delete B1/B2/BOT-3′/leaf(iii)"):**
B1/B2 (`exists_rowOp_of_strictInjection`/`rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂`), BOT-3′
`matrix_eq_mul_of_span_mem` + leaf (i) `matrix_eq_mul_of_dual_row_comb`, leaf (iii) `corner_hA_zero₁₂_of_gate`,
`finScrewDimSplitCorner` (leaf (iii)'s `em₁`) — all discharge the still-required row op `Lrow`. The
`_rowOp` wrapper + `_zero₁₂` cert + `…_edge_submatrix_fromBlocks_zero₁₂` engine are the αE4/αE3/αE2 BASE
(matrix swapped to `rigidityMatrixEdgeAug`), not retired. No blueprint `\lean{...}` pins, so deletion needs no
chapter restate (§17 gate checked). Full keep/delete/re-state map: design §(4.66.F/G).

## Decisions made during this phase

### Phase-local choices and proof techniques (compressed — most of the 23f bottom-arc / row-op apparatus is deleted by route (α), §(4.66); reasoning in git)

**Still-live (route-(α)-reused):**
- **αE3 = the augmented cert = a verbatim clone of `case_III_rank_certification_zero₁₂`, engine swap**
  (this commit). `case_III_rank_certification_aug` is `…_zero₁₂` (`Candidate.lean:2446`) with
  `rigidityMatrixEdge → rigidityMatrixEdgeAug`, `Lrow`/`re` carrying the `⊕ Unit` augmented row index,
  `(rRow, hr : rRow ∈ span F₀.rigidityRows)` added, and the body's engine call
  `…_of_edge_submatrix_fromBlocks_zero₁₂` replaced by the LANDED αE2 `…_of_aug_submatrix_…` (+ `hr`
  threaded between `hblock` and `hA`). The count tail (`hends'`/`hm₁`/`hm₂`/`hVcard`/`hVone`) is
  byte-identical. Axiom-clean (standard triple). No friction (first-try compile post long-line wrap).
- **αE2 = the augmented engine = a verbatim clone of the edge `_zero₁₂` engine, EQUALITY→`.trans`**
  (this commit). `finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂` is
  `…_of_edge_submatrix_fromBlocks_zero₁₂` with `rigidityMatrixEdge ends hgp →
  rigidityMatrixEdgeAug ends hgp rRow`, row index `+ ⊕ Unit`, and `(rRow, hr)` added. Body: the
  same backbone `Matrix.rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` (fully `M`-generic, fires
  on `augM` unchanged), but the edge engine's final `rwa [rank_eq_finrank_span …]` (the *equality*
  bridge) becomes `exact hbound.trans (rigidityMatrixEdgeAug_rank_le_finrank_span … hr)` — the αE1
  *inequality* (augmenting can only fail to add rank). Re-added the αE1-dropped `[DecidableEq α]`/
  `[DecidableEq β]`/`[Fintype {e//…}]` (the backbone + αE1's `_rank_le` need them). No friction.
- **αE1 = the augmented-matrix sibling of `rigidityMatrixEdge`, rank-bounded via the `Sum.elim`/`Matrix.of`
  defeq** (the αE1 commit). `rigidityMatrixEdgeAug = Matrix.of (Sum.elim (coordEquiv∘rigidityRowFunEdge)
  (fun _ => coordEquiv rRow))` is defeq to `Matrix.of (coordEquiv ∘ w)` for `w := Sum.elim rigidityRowFunEdge
  (fun _ => rRow)` (`congr 1; funext i; cases i <;> rfl`), so the carrier-agnostic `rank_of_coordEquiv`
  fires unchanged → `finrank (span (range w))`, bounded by `finrank (span rigidityRows)` via `finrank_mono`
  + `span_le` (the `inl` rows via the LANDED `span_range_rigidityRowFunEdge`, the `inr` row by `hr`). The
  augmented `inr` row needs only `rRow ∈ span rigidityRows`, not a `rigidityRows`-membership of a
  `blockBasisOn` read — the un-operated route. DROPPED the design's `[DecidableEq α]` + `[Fintype {e//e∈E}]`
  (linter-flagged unused; `classical` covers the former, `[Finite β]` the latter); αE2/αE3 re-add them. No friction.
- **D1 `interior_hsplitGP` = the `Arms.lean:894` chain-arm precedent at the split-off graph, taking the all-`k`
  `(k':ℤ)`+`Nonempty` `hIH`** (`splitOff_isMinimalKDof` + `splitOff_simple_of_noRigid_of_card` +
  `splitOff_vertexSet_ncard_lt`, then IH GP `.1`). `splitOff` adds `e₀` so ⊄ `G` (no `.mono`); simplicity needs
  `4 ≤ |V|` for a *proper* triangle (D1 takes `hV4`). Consumes the C.3 `hIH` add. No friction.
- **HD = a thin defeq restatement of `…_mixedBottom_of_finrank_eq` over the `Sum.elim`-`re`** (`re (Sum.inr i) =
  bottom i` definitional). Reused for αD2's bottom; the `inr` slot is now the genuine row, not the old `±r` index.
- **BOT-1 is a span SET-equality (cross-framework L-span), robust to basis choice — NOT the BLOCKED matrix-equality**
  (`submatrix_columnOp_toBlocks₂₂_eq_Gab`, which needs equal *chosen* basis vectors and is false for
  `finBasisOfFinrankEq` on term-distinct submodules). The "term-distinct, partly BLOCKED" framing was a CONFLATION
  (kernel-checked); the project takes the RANK route, so the wall never reforms. BOT-1/R1/BOT-2-free reused for αD2.

**The durable lesson + the keep/delete verdicts (CORRECTED §(4.66.F); one-line each):**
- **The §(4.62) lesson — route-composition satisfiability must be compiler-checked, not prose-argued** (the `C=0`
  shortcut leaf was JOINTLY-unsatisfiable despite "looking dischargeable"). Promoted → FRICTION. This same lesson
  fired AGAIN at §(4.65) (the `hred` over-optimism), §(4.66) (the spike before the Layer plan), and **§(4.66.F)
  (the "no row op" over-optimism — §(4.66) re-derived the `C=0`/no-row-op shortcut §(4.62) had already refuted)**.
  The durable rule.
- **DELETED at αE5 (route (α) orphans — `(e_b,j₀)`-collision machinery only):** D2 `bottom_selection_ne_corner_edge`
  (rewrite the non-dependent `ends`-term; `simp`+`hingeRow_self`; QUIRKS §28); BOT-4 `cornerRowInjection_sumElim
  _injective` + the `cornerRowInjection` proper (the `±r`-as-`(e_b,j₀)`-index host); BOT-2′ + the avoiding-engine
  (EXCLUSION-steering for the `(e_b,j₀)` collision — built to feed the §(4.65)-refuted `hred`); BOT-2 free engine +
  bridge; leaves (ii)/(iv) (bijection special cases). All SOUND, axiom-clean, no producer under route (α).
- **KEPT (CORRECTED §(4.66.F) — discharge the still-required row op `Lrow`):** B1/B2 (entrywise strict-injection
  row op, no `Equiv` middle index); BOT-3′ `matrix_eq_mul_of_span_mem` (HB, `B=L₀·D` from span-membership) + leaf (i)
  `matrix_eq_mul_of_dual_row_comb`; leaf (iii) `corner_hA_zero₁₂_of_gate` (the OPERATED-corner HA = αD3, NOT the bare
  `corner_hA'_of_gate`); `finScrewDimSplitCorner` (leaf (iii)'s `em₁`); R1 `…_eq_rigidityRows_of_off` + BOT-1
  (the bottom `hspan_id`). Friction logged where it arose (the §61-family dependent-rewrite trap; FRICTION:125/
  QUIRKS §64 the `m₂` `[Fintype]`-in-statement-type requirement) — all pre-existing, no new entries this commit.
