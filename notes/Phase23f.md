# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress. Opened 2026-06-26 as the *fifth* CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d +
23e + 23f). 23e landed the KT-faithful A3-transposed rank certificate + its LA scaffolding axiom-clean
(`notes/Phase23e.md`); 23f builds the **geometry arm** that *constructs* the cert's block data from the
IH-fed `cGv` widening, then the candidate-matching gate bridge and the general-`k` chain dispatch + CHAIN-5.
**Phase 23 stays in progress.** The authoritative recon is `notes/Phase23-design.md` §(4.54) (the re-pointed
hand-off, the three-leaf geometry-arm plan, the framework-vs-arm split, the both-block coupling). Program map:
`notes/MolecularConjecture.md`.

## Current state

**Route-(α) Layer plan DONE (design §(4.66), spike-verified). Next concrete commit = αE1** — the
augmented edge matrix + its rank-to-span bound, in `Concrete.lean`: `def rigidityMatrixEdgeAug`
(rows `(({e//e∈E}×Fin(D−1)))⊕Unit`, `inl` = `rigidityMatrixEdge` rows, `inr ()` = the genuine
`hingeRow a b ρ₀` row, coordinatized by `dualProductCoordEquiv`) + `theorem
rigidityMatrixEdgeAug_rank_le_finrank_span` (`augM.rank ≤ finrank (span F.rigidityRows)`, body =
spike PROBE C: `rank_of_coordEquiv` + `finrank_mono` + each row ∈ `span rigidityRows`). Then αE2
(augmented engine) → αE3 (augmented cert) → αE4 (augmented wrapper, the ⚑ `hblock` crux) → αE5/αE6
(delete the dead row-op apparatus) → αD1–αD7 (dispatch). Full plan + exact signatures: design §(4.66.D).

**HEADLINE (verified, supersedes §(4.65.E) phrasing — see §(4.66.A)).** The genuine `hingeRow a b ρ₀`
row CANNOT be a re-key of `re` into `rigidityMatrixEdge` — that matrix's row index `{e//e∈E}×Fin(D−1)`
forces every row to be a `blockBasisOn` read (no index reads `ρ₀`, = §(4.65.B-3)). The buildable
realization is an **AUGMENTED matrix** with a `⊕ Unit` row carrying the genuine functional (the
literal-`Matrix` mirror of the dual-space chain cert's `g`-member). Consequence: route (α) is SIMPLER
than §(4.65.E) anticipated — the augmented `±r` row reads `ρ₀` un-operated, so the corner needs **NO
row op** (HA = bare `corner_hA'_of_gate`; NO HB / `L₀` / `Lrow` / B1/B2 / BOT-3′). The `Rank.lean`
backbone (`rank_ge_…_zero₁₂`, `M`-generic) fires on `augM` unchanged. Compiler-checked spike — PROBE A
(genuine row ∈ `span rigidityRows`, via LANDED `hingeRow_mem_…reproduced`) / PROBE B (`blockBasisOn`
rows ∈ span) / PROBE C (`augM.rank ≤ span finrank`) — all built sorry-free, deleted before commit.

**Reuses (route-(α)-stable, verified row-family-agnostic by reading the signatures):**
`rank_ge_…_zero₁₂` + `rank_of_coordEquiv` (`Rank.lean`/`Concrete.lean`), the realization tail
`case_III_realization_of_rank` (consumes only `hrank`), D1 `interior_hsplitGP`, HD, `corner_hA'_of_gate`
(`Concrete.lean:620`), `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`Candidate.lean:2133`),
`span_range_rigidityRowFunEdge`, the column op `U` + `columnSplit` + the `toBlocks₂₁/₂₂` family (on the
`inl` sub-block), and the uniform-`blockBasisOn` BOTTOM (BOT-1/2-free/R1/HD). **Both gates ground to
discriminator outputs:** `ρ₀ (panelSupportExtensor (q(a,·))(q(b,·))) = 0` (`:1511`, the membership
`hperp`) and `ρ₀ (panelSupportExtensor (q(candidateVtx i,·)) n') ≠ 0` (`:1535`, the LI gate `hρe₀`) —
DIFFERENT extensors, jointly satisfiable (§(4.66.C)). **DELETES the `(e_b,j₀)`-collision + row-op
apparatus** (BOT-2′ / the avoiding-engine / D2 / `cornerRowInjection` family / B1/B2 / BOT-3′ / leaf
(i)/(iii) / leaves (ii)/(iv) — all SOUND Lean, orphaned by route (α)). NO `blockBasisOn`-def / motive /
frozen-contract change. Tree clean; `d=3` fully green; D1/HD + RE injection in tree axiom-clean.

**⚑ The ONE residual not yet compiler-locked** (flagged, §(4.66.E)): αE4's `hblock = fromBlocks A 0 C D`
decomposition of `augM * U` with the genuine `±r` row in the CORNER block. The spike verified the rank
bound + `rank_ge` composition + both gates, NOT the full column-op `fromBlocks` assembly over the
augmented `⊕ Unit` index — a bounded matrix-bookkeeping re-state of the landed
`submatrix_columnOp_…toBlocks₂₁_eq_zero` family, NOT new math. STOP and re-flag at αE4-build if the
landed bricks do not cover the augmented index.

**Landed leaves now ORPHANED by route (α)** (sound Lean, αE5/αE6 delete; design §(4.66.B)). The row-op
apparatus — B1/B2, the `_rowOp` wrapper skeleton, the full RE strict injection (corner +
BOT-2/2′/avoiding-engine/4 + `cornerRowInjection` family), BOT-3′, leaf (i)/(iii), D2 — was built for
the opaque-basis `_zero₁₂` route; route (α)'s augmented matrix fires NONE of it (no row op, no `L₀`).
**Route-(α)-REUSED (in tree, axiom-clean):** D1 `interior_hsplitGP`, HD, the uniform-`blockBasisOn`
bottom (BOT-1/2-free/R1), the `Rank.lean` backbone + column op, `corner_hA'_of_gate`,
`hingeRow_mem_…reproduced` — see the headline *Reuses* list. The cert's card target is unchanged:
`card m₁ + card m₂ = D·(|V(G)|−1) ≤ (D−1)·|E(G)|` (an inequality; no isostatic-tightness forced).
`d=3` stays fully green (zero-regression, hard constraint).

## Architectural choices made up front (inherited from 23e / the frozen contract)

- **Cert is consumed, not re-derived.** The 23e cert chain is axiom-clean and SATISFIABLE; 23f only
  *produces* its block data. Build `hblock`/`hA` against the literal `Lrow * M * U` product, NOT the
  component leaves in isolation (the §(4.46)/(4.54) lesson — compiler-check the FULL composition before
  declaring "remaining = assembly"; two leaves were elided when this was skipped).
- **The `±r` corner row reads `ρ₀` directly (route (α); §(4.66.A)) — NO row op.** The augmented matrix's
  `inr ()` row IS the genuine `hingeRow a b ρ₀`, so the corner block is `[blockBasisOn(e_a,·); ρ₀]`
  un-operated; HA = the bare `corner_hA'_of_gate`, with no `L₀`/`B`-zeroing coupling (this SUPERSEDES 23e's
  "zeroing `B` and mutating `A→A'` are ONE row op" framing). The bottom `m₂` stays pin-zero; the
  `fromBlocks A 0 C D` shape comes from the column op `U` alone (αE4's ⚑ residual).
- **`d=3` zero-regression via the cert FORK.** `d=3` keeps the `_matrix`/M₃ path; only the general-`d` arm
  routes through `case_III_rank_certification_zero₁₂`. Do NOT unify the two.
- **Below the CHAIN↔ENTRY contract + the motive/IH.** The geometry arm + dispatch are below C.3/C.1 and the
  0-dof motive. The frozen interface (C.0–C.6) + the sanctioned C.3 `hIH` addition stay valid.

## Lemma checklist

**The LIVE forward plan is item (4) — route (α)'s αE1–αD7 (design §(4.66.D)).** Items (i)–(HMEQ) below
are the LANDED-but-ORPHANED opaque-basis `_zero₁₂` ROW-OP route (sound, in tree, αE5/αE6 delete); they
are a record of what landed, not the live plan. The old `[ ]` row-op items (HA/HB/3c) DISSOLVE under
route (α) (no row op). HD + the FREE bottom selection (BOT-1/2/R1) + HMEQ are route-(α)-REUSED.

- [x] **(i)** `matrix_eq_mul_of_dual_row_comb` (`Concrete.lean`) — `cGv`→`w` `B=L₀·D` core (superseded for HB by BOT-3′; kept for explicit-weight consumers).
- [x] **(ii)/(iv)** `reindex_rowOp_isUnit_det` / `reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂` (`Rank.lean`) — the BIJECTION unit-det + `hblock` bridges. SUPERSEDED by B1/B2 (strict injection, §(4.55)); zero-caller orphans, kept as the bijection special case.
- [x] **(iii)** `corner_hA_zero₁₂_of_gate` (`Concrete.lean:657`) — operated-corner `hA` (`ρ₀`-`hAeq` + gate). ORPHANED by route (α) (no row op; the bare `corner_hA'_of_gate` is the αD3 HA). αE5 delete.
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
- [~] **(HA) DISSOLVED under route (α)** (§(4.66.A)): no row op ⟹ no operated corner. HA = the bare LANDED
  `corner_hA'_of_gate` (`Concrete.lean:620`) on `[blockBasisOn(e_a,·); ρ₀]`, fed only the gate `hρe₀` — αD3.
  (The operated leaf (iii) `corner_hA_zero₁₂_of_gate` + its `hAeq`/`L₀` are orphaned, αE5 delete.)
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
- [~] **(HB) DISSOLVED under route (α)** (§(4.66.A)): the augmented `inr` row reads `ρ₀` directly, so there
  is no `B = L₀·D` obligation and no `L₀`. BOT-3′ `matrix_eq_mul_of_span_mem` + leaf (i) are orphaned (αE5 delete).
- [→] **(3c) candidate-matching gate bridge → αD1** (route (α)): the `hρe₀` gate (`F.supportExtensor e_a` ↔
  `panelSupportExtensor (q(candidateVtx i)) n'` via `caseIIICandidate_supportExtensor_candidate`
  (`Candidate.lean:960`) + `candidateVtx_succ_eq` (`Operations.lean:2824`, `rfl`-level) + the `d=k+1`
  `ChainData` fact) is still needed — packaged in αD1's genuine-row bundle off the discriminator (`:1535`),
  NOT dissolved. §(4.66.D) αD1; verified against ground §(4.66.C).
- [ ] **(4) the realization arm + dispatch — route (α), Layer plan = design §(4.66.D).** **αE1** (the
  augmented edge matrix `rigidityMatrixEdgeAug` + its `rank_le_finrank_span` bound) is the FIRST buildable
  commit (spike PROBE C, sorry-free). Then **αE2** augmented engine → **αE3** augmented cert
  (`case_III_rank_certification_aug`, sibling of `case_III_rank_certification_zero₁₂`) → **αE4** augmented
  wrapper (`case_III_arm_realization_aug`, sibling of `case_III_arm_realization_rowOp`, WITHOUT the
  `(L₀,hB,hA-operated,Lrow)` carries; the ⚑ `hblock`-`fromBlocks` crux) → **αE5/αE6** delete the dead
  `(e_b,j₀)`/row-op apparatus → **αD1–αD7** dispatch (αD1 = the genuine-row membership+gate bundle off the
  discriminator; αD2 = the reused `blockBasisOn` bottom; αD3 = `corner_hA'_of_gate`; αD4 = `hblock`; αD5 fire;
  αD6 router; αD7 CHAIN-5, separable LAST). The §(4.64.B) D1–D8 opaque-basis plan is SUPERSEDED (D4 `hred`
  refuted, §(4.65)). D1 `interior_hsplitGP` ✓ LANDED (reused by αD2); D2 `bottom_selection_ne_corner_edge`
  ✓ LANDED but DISSOLVES under route (α) (deletable at αE5). Full exact signatures: §(4.66.D).

## Blockers / open questions

- **C.3 `hIH`-on-consume-shape addition — APPROVED** (user-adjudicated 2026-06-26, session #36; the actual
  contract reshape lands at D8/CHAIN-5 with `chainData_dispatch`). The interior arm needs the INTERIOR-split
  `hsplitGP` (`G.splitOff vᵢ …`), derivable only from `hIH` via `splitOff_isMinimalKDof` — D1
  `interior_hsplitGP` (the standalone leaf that consumes `hIH`) ✓ LANDED; the C.3 dispatch consume-shape gets
  the `hIH` field added when `chainData_dispatch` is wired (a one-field addition touching the C.0
  producer/consumer/ENTRY lockstep trio, NOT a motive/IH-strength change). Context: design §(4.43) *THE ONE
  INTERFACE OBLIGATION* + §C.3.
- **The `(e_b, j₀)` `hred` — RESOLVED + Layer-planned (route (α), design §(4.65)+§(4.66)).** `hred` for the
  literal opaque-basis `(e_b, j₀)` row was REFUTED (§(4.65.A/B): `blockBasisOn` opaque `Concrete.lean:510`;
  `ρ₀ ∈ hingeRowBlock e₀` of the splitoff ≠ `hingeRowBlock e_b` of the candidate). Route (α) re-shapes the `±r`
  row to the genuine `hingeRow a b ρ₀` via an **augmented matrix** (§(4.66.A); the `re`-rekey shape §(4.65.E)
  sketched is not buildable — no `rigidityMatrixEdge` index reads `ρ₀`). This DELETES the whole `(e_b,j₀)`/row-op
  apparatus (BOT-2′ / avoiding-engine / D2 / `cornerRowInjection` family / B1/B2 / BOT-3′ / leaf (i)/(iii) /
  (ii)/(iv) — SOUND Lean, orphaned). Route (β) (§(4.18)–(4.30) walled `mkQ`) rejected. NO `blockBasisOn`-def /
  motive / contract change. The buildable Layer plan is §(4.66.D) (αE1 next).
- **⚑ The αE4 `hblock`-`fromBlocks` decomposition is the one residual** not compiler-locked (spike verified rank
  + gates, not the column-op `fromBlocks` over the augmented `⊕ Unit` index with the genuine `±r` row in the
  corner). Bounded matrix-bookkeeping re-state of the landed `submatrix_columnOp_…toBlocks₂₁_eq_zero` family, NOT
  new math; STOP and re-flag at αE4-build if the landed bricks do not cover the augmented index. Design §(4.66.E).
- **GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive) — orthogonal to the cert;
  tracked separately, lands with 23f/the spine.
- **Cleanup folded into αE5/αE6 (route (α)):** the `(e_b,j₀)`/row-op leaves (BOT-2′, avoiding-engine, D2,
  `cornerRowInjection` family, B1/B2, BOT-3′, leaf (i)/(iii), (ii)/(iv)) are all orphaned by route (α) and get
  deleted (or `@[deprecated]`) at αE5/αE6 — no blueprint pins, so no `\lean{...}` restate needed (§17 per-slice
  gate checked). The retired `_zero₁₂` cert + `_rowOp` wrapper + edge-engine retire at αE6.
- **Downstream (23g+):** ENTRY's `exists_chain_data_of_noRigid` reshape + floor lift + OD-1, then ASSEMBLY.
  The frozen contract (C.5/C.6) is invariant; none touches 23e's cert. ENTRY is parallel-safe.

## Hand-off / next phase

**Route (α) CHOSEN (user-adjudicated 2026-06-27); the Layer plan is DONE (design §(4.66),
spike-verified). Next concrete commit = αE1.** D4's `hred` for the opaque-basis `(e_b, j₀)` row was
REFUTED (compiler-checked, §(4.65.A/B)); the fix re-shapes the `±r` corner row to read the genuine
`hingeRow a b ρ₀` (KT eq. (6.66)) via an AUGMENTED matrix (§(4.66.A) — NOT a `re`-rekey into
`rigidityMatrixEdge`, which has no index reading `ρ₀`).

**αE1 (FIRST buildable, `Concrete.lean`) — the augmented edge matrix + its rank bound.** (1) `def
BodyHingeFramework.rigidityMatrixEdgeAug (F) (ends) (hgp) (rRow : Dual ℝ (α→ScrewSpace k)) : Matrix
((({e // e ∈ E(F.graph)} × Fin (screwDim k−1)))⊕Unit) (α × Fin (finrank ℝ (ScrewSpace k))) ℝ :=
Matrix.of (Sum.elim (fun p => dualProductCoordEquiv (F.rigidityRowFunEdge ends hgp p)) (fun _ =>
dualProductCoordEquiv rRow))`. (2) `theorem rigidityMatrixEdgeAug_rank_le_finrank_span [Fintype α]
[DecidableEq α] [Finite β] (F) (ends) [Fintype {e//e∈E(F.graph)}] (hgp) (hends) {rRow} (hr : rRow ∈
span F.rigidityRows) : (F.rigidityMatrixEdgeAug ends hgp rRow).rank ≤ finrank ℝ (span F.rigidityRows)`,
body = spike PROBE C verbatim (`Matrix.rank_of_coordEquiv` + `Submodule.finrank_mono` + `span_le`;
`inl` rows ∈ span via `span_range_rigidityRowFunEdge`, `inr` via `hr`). Then αE2 (augmented engine,
sibling of `finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks_zero₁₂` `Concrete.lean:934`) →
αE3 (augmented cert `case_III_rank_certification_aug`, sibling of `…_zero₁₂` `Candidate.lean:2446`) →
αE4 (augmented wrapper `case_III_arm_realization_aug`, sibling of `case_III_arm_realization_rowOp`
`ForkedArm.lean:315`, WITHOUT the `(L₀,hB,hA-operated,Lrow)` carries; the ⚑ `hblock` crux) → αE5/αE6
(delete the dead `(e_b,j₀)`/row-op apparatus + retire `_zero₁₂`/`_rowOp`) → αD1–αD7 (dispatch). Full
exact signatures for every step: **design §(4.66.D)**; the keep/delete/re-state map: §(4.66.B).

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
expected in `m₁`). The bottom `m₂` edges sit at `Gv`/`R(Gab)`, all pin-zero.

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
- `corner_hA'_of_gate` (`Concrete.lean:620`) — the bare `[blockBasisOn(e_a,·); ρ₀]`-LI iff `hρe₀` = αD3's HA.
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

**In-tree but DELETED at αE5/αE6 (route (α) orphans them — SOUND Lean, no producer):** the `(e_b,j₀)`-collision +
row-op apparatus — BOT-2′ `bottom_selection_of_crossFramework_span_avoiding`, the avoiding-engine
`exists_finCard_linearIndependent_selection_avoiding`, D2 `bottom_selection_ne_corner_edge`, the `cornerRowInjection`
family (`+_injective`/`_sumElim_injective`/`finScrewDimSplitCorner`), B1/B2
(`exists_rowOp_of_strictInjection`/`rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂`), BOT-3′
`matrix_eq_mul_of_span_mem` + leaf (i) `matrix_eq_mul_of_dual_row_comb`, leaf (iii) `corner_hA_zero₁₂_of_gate`,
leaves (ii)/(iv) (`reindex_rowOp_isUnit_det`/`reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂`), and the retired
`_zero₁₂` cert + `case_III_arm_realization_rowOp` wrapper + `…_edge_submatrix_fromBlocks_zero₁₂` engine. No
blueprint `\lean{...}` pins, so deletion needs no chapter restate (§17 gate checked). Full keep/delete/re-state
map: design §(4.66.B).

## Decisions made during this phase

### Phase-local choices and proof techniques (compressed — most of the 23f bottom-arc / row-op apparatus is deleted by route (α), §(4.66); reasoning in git)

**Still-live (route-(α)-reused):**
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

**Route-(α)-superseded (decls deleted at αE5/αE6; recorded as one-line verdicts):**
- **The §(4.62) lesson — route-composition satisfiability must be compiler-checked, not prose-argued** (the `C=0`
  shortcut leaf was JOINTLY-unsatisfiable despite "looking dischargeable"). Promoted → FRICTION. This same lesson
  fired AGAIN at §(4.65) (the `hred` over-optimism) and §(4.66) (the spike before the Layer plan). The durable rule.
- D2 `bottom_selection_ne_corner_edge` (rewrite the non-dependent `ends`-term; `simp`+`hingeRow_self`; QUIRKS §28);
  BOT-4 `cornerRowInjection_sumElim_injective` (carrier-agnostic `Sum.elim` injectivity); BOT-2′ + the
  avoiding-engine (EXCLUSION-steering for the `(e_b,j₀)` collision — built to feed the §(4.65)-refuted `hred`);
  R1 `…_eq_rigidityRows_of_off` (the restricted-edge + zero-`e_a` `hspan_id` discharge — `e_a` row is `hingeRow a a
  = 0`); BOT-2 free engine + bridge; BOT-3′ `matrix_eq_mul_of_span_mem` (route-(b) HB, `B=L₀·D` from span-membership)
  + leaf (i); the `cornerRowInjection` family + `finScrewDimSplitCorner`; B1/B2 (entrywise strict-injection row op,
  no `Equiv` middle index); leaf (iii) `corner_hA_zero₁₂_of_gate` (operated-corner HA — route (α) uses the un-operated
  `corner_hA'_of_gate` instead); leaves (ii)/(iv) (bijection special cases). All SOUND, axiom-clean, no producer
  under route (α). Friction logged where it arose (the §61-family dependent-rewrite trap; FRICTION:125/QUIRKS §64
  the `m₂` `[Fintype]`-in-statement-type requirement) — all pre-existing, no new entries this commit.
