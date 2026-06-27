# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress. Opened 2026-06-26 as the *fifth* CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d +
23e + 23f). 23e landed the KT-faithful A3-transposed rank certificate + its LA scaffolding axiom-clean
(`notes/Phase23e.md`); 23f builds the **geometry arm** that *constructs* the cert's block data from the
IH-fed `cGv` widening, then the candidate-matching gate bridge and the general-`k` chain dispatch + CHAIN-5.
**Phase 23 stays in progress.** The authoritative recon is `notes/Phase23-design.md` §(4.54) (the re-pointed
hand-off, the three-leaf geometry-arm plan, the framework-vs-arm split, the both-block coupling). Program map:
`notes/MolecularConjecture.md`.

## Current state

**STOP — DECISION FOR THE HUMAN: which escape, (C)/fresh vs (α1) vs (α2). The KT-faithfulness recon
(design §(4.69), 2026-06-27) RECOMMENDS (C)/fresh and locates exactly why the wall forms.** Route α (the
user-chosen literal-`Matrix` cert) is BLOCKED on BOTH faces (§(4.68), both-route compiler-checked); the broad
re-read (design §(4.69), KT §6.4.1/§6.4.2 read end-to-end, eqs. 6.44–6.67) settles the path-forward question:

- **The wall is a faithful image of KT's OWN union-dimension obstruction (eq. 6.67), SHARPENED into a wall by
  ONE project-specific device KT does not use** — the `caseIIICandidate` extensor-override (slots `e_a`/`e_b`
  overridden to the candidate meet `C(L)`, `Candidate.lean:940`, the eq.-(6.12) device). KT keeps the bottom
  as the LITERAL full-rank IH matrix `R(G₁,q₁)` whose rows ARE rows of `R(G,pᵢ)` (the 6.59 substitution, no
  transport). The project requires the bottom in `span(candidate.rigidityRows)` (`hWS`), forcing a
  transport-into-the-OVERRIDDEN-span that hits the gate `ρ₀ ⊥̸ C(vᵢ₊₁,n')` — and that same gate is what the
  discriminator USES to pick the good member (KT 6.67). Two faces of one obstruction; §(4.29) re-explained.
- **RECOMMENDATION = (C)/fresh — replace the corner+bottom *transport-into-candidate-span* cert with one whose
  bottom is the LITERAL full-rank IH framework's rigidity rows** (KT's `R(G₁,q₁)` as a sub-family via KT's
  (6.61) column op + (6.62) row correspondence as a `Matrix` submatrix containment, NOT a span membership).
  This is the ONLY direction that structurally dissolves the wall (§(4.30)'s own diagnosis: "the
  override-meets-gate collision never forms"). The block-additivity machinery (`Rank.lean:480/574` backbones =
  KT 6.65), the discriminator (the moving-member pick), the realization tail (`Arms.lean:63`), and D1
  `interior_hsplitGP` (the IH full-rank `R(Gab)`) are ALL reusable. What tears out: the `mixedBottom`/`R(G−v)`
  +fill bottom, the `bottomRelabel`/transport chain, the `_aug` ladder, the chain `W`-producer.
- **FLAGGED, NOT DECOMPOSED (the recommended path crosses a new-math leaf).** (C)/fresh needs (1) a new-math
  leaf — the IH-matrix-as-literal-bottom-submatrix bridge (KT 6.61/6.62), gated on (3) a foundational question
  (is the candidate's non-slot row agreement a `Matrix` equality or still a cycle-relabel transport?). The W6e
  tail-coupling (2) is VERIFIED BENIGN (the A2 bridge `rank = finrank span` is rank-route-agnostic; the landed
  `_zero₁₂` cert already concludes the candidate span finrank). Per flag-don't-force, no A1–A6 manufactured —
  the right next step is a SINGLE compiler-checked feasibility spike on (3). Design §(4.69.6).

**The §(4.68) both-blocked verdict (re-confirmed at source, the floor for §(4.69)):** neither the dual-space
chain arm (ROUTE A) nor the `_aug` literal-`Matrix` arm with `±r = hingeRow b v ρ₀` (ROUTE B) is buildable —
both blocked by the SAME `caseIIICandidate`-override obstruction (§(4.29)):
- **ROUTE A** (the §(4.67) pivot target): `case_III_arm_corner_assembly_via_leafB2`'s `hS`
  (`∀ φ ∈ Fbase.rigidityRows, …`) is UNSATISFIABLE — the wrap-edge `edge i` base row routes (via the only
  landed producer `bottomRelabel_rigidityRows_mem_span_caseIIICandidate`) into the `(a,b)`-block tag needing
  `hG_eb_cand : G.IsLink e_b (vtx i.succ)(vtx (i−1).castSucc)`, which is **kernel-FALSE** at an interior
  chain vertex (the candidate fresh pair is 2 chain-steps apart, `deg_two`-forbidden — PROBE A; and the chain
  arm's own `e_b` links `(v,b) ≠ (a,b)`, `IsLink.right_unique` — PROBE B). **§(4.26)/(4.29) CONFIRMED**, not
  refuted. §(4.67)'s pivot conflated "decl axiom-clean" with "`hS` satisfiable" (the very error it warned of).
- **ROUTE B** (the `_aug` arm with the corrected row): the un-operated `inr` corner row reads `−ρ₀` at the
  pin (genuine — PROBE B1, fixes the §(4.67) `hingeRow a b ρ₀`-reads-`0` problem) AND `ρ₀` at body `b` off-pin
  (PROBE B2 — `B ≠ 0`, so the row op `L₀` forced by `hB` is NONTRIVIAL). The bottom STILL includes the
  v-incident `e_b`-fill row (mandatory for the full-rank count, `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`
  `hbot1` `Or.inr`), so `C ≠ 0` and the operated `inr` pin read is `−ρ₀ − (L₀C)|_pin` with `(L₀C)|_pin` the
  OPAQUE `blockBasisOn(e_b)` content. Leaf (iii)'s `hAeq` (operated row `= ρ₀`) then needs
  `ρ₀ ∈ span(blockBasisOn(e_b))` = the §(4.65)-REFUTED `hred` coupling; the gate alone does NOT give LI. **No
  restated leaf (iii) closes it.**

**The escapes (user adjudication; design §(4.69.5)/(4.68.C), RECOMMENDATION = (C)/fresh):** **(C)/fresh
[RECOMMENDED]** — the literal-`R(G₁,q₁)`-bottom block-additivity cert (KT's actual §6.4.2; closest to KT, the
only structural wall-escape; needs the new-math IH-matrix-as-bottom bridge, recon-spike-first, §(4.69.6));
(α1) a WALL-FREE `W`-producer for the chain arm (§(4.65.E) route (β); BLOCKED — it IS the wall, lowest
faithfulness, "possibly real new-math wall", ≥ the §(4.18)–(4.30) failed arc); (α2) a `ρ₀`-aligned `±r`
corner for `_aug` that does not pull the `e_b` block into the row op (a cert-row-family change; BLOCKED, its
only escape overlaps (C)). Each is a multi-commit recon-first effort with real wall risk. **No motive/IH/
C.0–C.6 change is involved in ANY** — the obstruction is below the contract, in the cert's
*transport-into-candidate-span* split (NOT the block-additivity split, which is KT-faithful and stays). **No
αD leaf is buildable until the user picks.** Do NOT build against any arm until then.

**αE1–αE5 LANDED (axiom-clean), now ALL dead-arm.** The `_aug` ladder (αE1–αE4) joins `_matrix`/`_rowOp` and
the dual-space chain arm as landed-but-unused; αE6 (retire the dead arms) stays DEFERRED to phase-close. The
αE5 `(e_b,j₀)`-machinery deletion STANDS.

**Prior αE-ladder record (sound Lean, now dead-arm).** **αE5 deleted ONLY the
`(e_b,j₀)`-collision machinery** — BOT-2′ `bottom_selection_of_crossFramework_span_avoiding`, the
avoiding-engine `exists_finCard_linearIndependent_selection_avoiding`, D2 `bottom_selection_ne_corner_edge`,
the `cornerRowInjection` proper (+`_injective`/`_sumElim_injective`), leaves (ii)/(iv)
(`reindex_rowOp_isUnit_det`/`reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂`), and the old HD `_sumElim_`
wrapper `linearIndependent_toBlocks₂₂_row_sumElim_mixedBottom_of_finrank_eq` (it baked `cornerRowInjection`
into its statement — route (α)'s αD2 rebuilds HD over the genuine `inr` `re`, no `cornerRowInjection`).
**KEPT** B1/B2/BOT-3′/leaf(i)/leaf(iii)/`finScrewDimSplitCorner` (they discharge the still-required row
op `Lrow`) + the underlying `_mixedBottom_of_finrank_eq` HD producer + the free BOT-2
`bottom_selection_of_crossFramework_span`; the `_rowOp` wrapper + `_zero₁₂` cert + edge-`_zero₁₂` engine
STAY (the αE2–αE4 BASE, matrix-swapped). 372 deletions / 25 insertions across `Rank.lean`/`Concrete.lean`
(+ 1 doc fix in `Realization.lean`); dangling docstring refs to the deleted decls rewritten in the same
files. No blueprint `\lean{...}` pins (§17 gate checked); gates clean (warning-free build + `lake lint`).
Full keep/delete map: design §(4.66.F/G). **αE4 added
`theorem PanelHingeFramework.case_III_arm_realization_aug` to `ForkedArm.lean` (right after the LANDED
`case_III_arm_realization_rowOp` `:315`): a near-verbatim clone with `rigidityMatrixEdge →
rigidityMatrixEdgeAug` + the `±r` corner row from the augmented `inr ()` slot, KEEPING
`(re,hre,L₀,hM'eq,hB,hA=leaf(iii) operated,hD)` and ADDING `(rRow, hr : rRow ∈ span F₀.rigidityRows)`;
B1 builds `Lrow` over the augmented index `(({e//…}×Fin(D−1)))⊕Unit`, B2 reduces `hblock` (the ⚑
residual — the B2 reducer is fully `M'`-generic, fires on `augM * U` unchanged), the body fires the
LANDED αE3 cert `case_III_rank_certification_aug` then the SHARED tail `case_III_realization_of_rank`.
NO friction (clone of the `_rowOp` wrapper; the only iteration was the longLine linter's Unicode
codepoint count, QUIRKS §55).** αE3 added `theorem
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

**⚑ The ONE residual is now DISCHARGED** (αE4 LANDED, axiom-clean): αE4's `hblock = fromBlocks (A−L₀C) 0 C
D` decomposition of `Lrow * augM * U` (the `_zero₁₂`, top-right zero, via `Lrow`) is the landed B2
`rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂` reduction applied to `augM` — and B2 is fully
`M'`-generic (`M' : Matrix p q K`), so the SAME B2 call the `_rowOp` wrapper makes on `rigidityMatrixEdge *
U` fires UNCHANGED on `augM * U` (the augmented `⊕ Unit` row index enters only as B1's `p`/`Lrow` carrier;
B1 `exists_rowOp_of_strictInjection` is index-agnostic too). The `conv_lhs => rw [Matrix.mul_assoc]` +
`rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂` body line is byte-identical to the `_rowOp`
wrapper's. No new math; the landed bricks covered the augmented index exactly as §(4.66.F) anticipated.

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
ONLY the `(e_b,j₀)`-collision machinery (BOT-2′ — NOT the free BOT-2 — avoiding-engine, D2,
`cornerRowInjection` family, leaves (ii)/(iv), the old HD `_sumElim_` wrapper) was deleted at αE5.
HA/HB/3c are via leaf (iii)/BOT-3′/αD1 (NOT dissolved). HD (the `_mixedBottom_` producer) + the bottom
selection (BOT-1/BOT-2-free/R1) + HMEQ are route-(α)-REUSED.

- [x] **(i)** `matrix_eq_mul_of_dual_row_comb` (`Concrete.lean`) — `cGv`→`w` `B=L₀·D` core (superseded for HB by BOT-3′; kept for explicit-weight consumers).
- [×] **(ii)/(iv)** `reindex_rowOp_isUnit_det` / `reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂` (`Rank.lean`) — the BIJECTION unit-det + `hblock` bridges. SUPERSEDED by B1/B2 (strict injection, §(4.55)); zero-caller bijection orphans — **DELETED at αE5**.
- [x] **(iii)** `corner_hA_zero₁₂_of_gate` (`Concrete.lean:657`) — operated-corner `hA` (`ρ₀`-`hAeq` + gate). **KEPT (CORRECTED §(4.66.F))** — route (α) STILL row-ops (the `_zero₁₂` shape), so leaf (iii)'s operated `(A−L₀C).row` IS αD3's HA (NOT the bare `corner_hA'_of_gate`).
- [x] **(recon §(4.55))** `re` shape = STRICT INJECTION (`card m₁+card m₂ ≤ card p`, an inequality; no bijection in general). (ii)/(iv) bijection-only don't serve; B1/B2 subsume them.
- [x] **(B1)/(B2)** `exists_rowOp_of_strictInjection` / `rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂` (`Rank.lean`) — strict-injection unit-det `Lrow` (+ off-image vanishing) + the entrywise `hblock` reducer to `fromBlocks (A−L₀C) 0 C D` (no `Equiv` middle index). Subsume (ii)/(iv).
- [x] **wrapper SKELETON** `case_III_arm_realization_rowOp` (`ForkedArm.lean`) — takes `(re,hre,L₀,hM'eq,hB,hA,hD)`, builds `Lrow`/`U`/`en`/`hblock` in-body, fires the cert (`A` slot = OPERATED `A−L₀C`; `C` free — `_zero₁₂` clears the §(4.41) wall), runs the realization tail. §(4.56) spike: composes sorry-free. OWED: the 5 carried hyps (RE done; HMEQ/HB/HA/HD below).
- [x] **(BOT-3′)** `matrix_eq_mul_of_span_mem` (`Concrete.lean`) — route-(b) HB: recovers `L₀` from `hmem : φ i ∈ span(range χ)` (span-membership sibling of leaf (i)). Subsumes the dissolved BOT-3 `μ`-match.
- [x] **(BOT-1)** `span_range_hingeRow_crossFramework_eq_rigidityRows` (`Basic.lean`) — abstract cross-framework span SET-identity (candidate a-shifted family spans `span R(Gab).rigidityRows`, finrank `card m₂`). NOT instantiable over full `E(G)` (`e_a`'s a-shift → `(a,a)` self-loop breaks `hlink₁`, §(4.60.B)); the dispatch uses R1 instead. Stays in tree as the unrestricted form.
- [x] **(R1)** `..._crossFramework_eq_rigidityRows_of_off` + `hingeRow_self` (`@[simp]`, `hingeRow a a = 0`) (`Basic.lean`) — the restricted-edge variant (matching over genuine edges `{e // P e}`; `hoff` zeroes the `e_a` row) discharging the bridge's full-`p` `hspan_id`.
- [x] **(BOT-2)** the FREE basis-pick (KEPT, route-(α) live): `exists_finCard_linearIndependent_selection` (`Rank.lean` engine) + `bottom_selection_of_crossFramework_span` (`Concrete.lean` bridge → `(re,hbot2,hbot1,hrank)`; `hbot1` tautology, `hrank` = `finrank_span_eq_card`). The `(e_b,j₀)`-avoiding need dissolved under route (α) (the `±r` row is now the augmented `inr` slot), so the free pick is the αD2 bottom.
- [×] **(avoiding engine)** `exists_finCard_linearIndependent_selection_avoiding` (`Rank.lean`) — exclusion-steered companion (redundant `i₀` ⟹ LI selection AVOIDING `i₀`). Built to feed the §(4.65)-refuted `hred` — **DELETED at αE5**.
- [×] **(BOT-2′)** `bottom_selection_of_crossFramework_span_avoiding` (`Concrete.lean`) — EXCLUSION-steered bridge resolving the §(4.61) `(e_b,j₀)` tension. **DELETED at αE5** (route (α)'s `inr` slot replaces the `(e_b,j₀)` host; the free BOT-2 stays).
- [×] **(RE) the strict row injection corner half** — `cornerRowInjection`/`_injective`/`_sumElim_injective` (`Concrete.lean` A5d): the `±r`-as-`(e_b,j₀)`-index corner read. **DELETED at αE5** (`finScrewDimSplitCorner` KEPT — it is leaf (iii)'s `em₁`). Route (α)'s αD2 builds the `re` over the genuine `inr` slot. HMEQ = mathlib `fromBlocks_toBlocks.symm`.
- [↯] **(HA) — the `_aug` operated-`hA` is NOT buildable for `hingeRow a b ρ₀` (design §(4.67), spike-checked)**:
  that row reads `0` at the pin (PROBE 1), so leaf (iii)'s `hAeq` fails for `A`, and `(A−L₀C)|_pin=ρ₀` is the
  §(4.65)-REFUTED `hred` coupling. SUPERSEDED — the buildable interior corner is the LANDED dual-space chain arm
  `case_III_arm_corner_assembly[_via_leafB2]` (corner row-LI mod `W` via `linearIndependent_mkQ_corner_of_gate`,
  genuine row `hingeRow b v ρ₀` reading `−ρ₀` at the pin; NO row op, NO operated `hA`). §(4.67) αD1–αD3.
- [×] **(HD `_sumElim_` wrapper)** `linearIndependent_toBlocks₂₂_row_sumElim_mixedBottom_of_finrank_eq` —
  baked `cornerRowInjection` into its TYPE, so **DELETED at αE5** with that family. The underlying
  `_mixedBottom_of_finrank_eq` producer (`w`-FREE, §(4.57.A), `hbot2`/`hbot1`/`hrank` ⟹ row-LI) STAYS;
  route (α)'s αD2 restates HD over the genuine `inr` `re` shape, feeding `hrank`'s `card m₂` from the
  split-off framework's def-`0` full-rank realization (`hsplitGP` via `splitOff_isMinimalKDof`, the C.3 `hIH` add).
- [x] **(HMEQ) CLOSES at the wrapper-fire** (§(4.64.A), kernel-confirmed) — `hM'eq =
  (Matrix.fromBlocks_toBlocks M').symm` with `M' := (R(F)*Uᵀ).submatrix re (columnSplit v).symm` and
  `A/B/C/D := M'.toBlocks₁₁/₁₂/₂₁/₂₂`. NO new lemma, NO sorry; pins `A/B/C/D` to ONE `M'` (the §(4.58.C)
  single-`D` concern fully discharged). HD likewise closes with `exact hD` (the §(4.63) defeq verified
  end-to-end). So owed at the fire reduces to HA(D7)/HB(D6)/the BOT-2′ inputs(D3–D4)/`?L₀`.
- [↯] **(HB) — N/A under the chain-arm pivot**: `hB : B = L₀·D` was the `_aug` matrix route's row-op factoring;
  the chain arm has no row op (corner mod `W`). BOT-3′/leaf (i) stay in tree (sound, dead-arm). The chain arm's
  bottom-block bookkeeping is the LEAF-B2 `W`-production (αD2), not `hB`.
- [→] **(3c) candidate-matching gate bridge → αD1** (chain arm): `hgate := hρe₀` (`F.supportExtensor e_a` ↔
  `panelSupportExtensor (q(candidateVtx i)) n'` via `caseIIICandidate_supportExtensor_candidate`
  (`Candidate.lean:960`) + `candidateVtx_succ_eq` (`Operations.lean:2824`, `rfl`-level) + the `d=k+1`
  `ChainData` fact). Still needed — packaged in αD1 off the discriminator (`:1535`) with the assembly perp
  `hρe₀ := hρ₀e₀` (`:1511`); both gates feed `case_III_arm_corner_assembly`. §(4.67) αD1.
- [↯] **(4) the realization arm + dispatch — BOTH candidate arms BLOCKED; STOP for user decision (design
  §(4.68), both-route compiler-checked, supersedes §(4.67)'s chain-arm pivot).** **αE1–αE5** ✓ LANDED
  axiom-clean (the `_aug` ladder + the αE5 `(e_b,j₀)`-machinery deletion), but the αD dispatch is BLOCKED:
  ROUTE A (the chain arm `…_via_leafB2`) has UNSATISFIABLE `hS` (the §(4.26)/(4.29) wall — PROBE A/B); ROUTE B
  (`_aug` with `±r = hingeRow b v ρ₀`) re-hits the §(4.65) opaque-`blockBasisOn` `hred` at the operated `hA`
  (PROBE B1/B2). Both blocked by the SAME `caseIIICandidate`-override gate; the user must pick an escape
  (α1)/(α2)/(C) — see *Hand-off* + design §(4.68.C). D1 `interior_hsplitGP` ✓ LANDED (reusable by any escape).
  All `_aug`/`_matrix`/`_rowOp`/chain arms are landed-but-dead; αE6 (retire them) DEFERRED to phase-close.

## Blockers / open questions

- **C.3 `hIH`-on-consume-shape addition — APPROVED** (user-adjudicated 2026-06-26, session #36; the actual
  contract reshape lands at D8/CHAIN-5 with `chainData_dispatch`). The interior arm needs the INTERIOR-split
  `hsplitGP` (`G.splitOff vᵢ …`), derivable only from `hIH` via `splitOff_isMinimalKDof` — D1
  `interior_hsplitGP` (the standalone leaf that consumes `hIH`) ✓ LANDED; the C.3 dispatch consume-shape gets
  the `hIH` field added when `chainData_dispatch` is wired (a one-field addition touching the C.0
  producer/consumer/ENTRY lockstep trio, NOT a motive/IH-strength change). Context: design §(4.43) *THE ONE
  INTERFACE OBLIGATION* + §C.3.
- **THE INTERIOR-ARM CORNER — route α BLOCKED both faces; user decision REQUIRED, (C)/fresh RECOMMENDED
  (design §(4.69), KT-faithfulness recon 2026-06-27).** Both route-α arms are unbuildable from the landed
  leaves, blocked by the SAME `caseIIICandidate`-override obstruction (§(4.68), compiler-checked): ROUTE A `hS`
  unsatisfiable (the wrap-edge row needs the kernel-FALSE `hG_eb_cand`); ROUTE B operated `hA` re-hits the
  §(4.65) opaque-`blockBasisOn` `hred`. The §(4.69) source re-read (KT §6.4.1/§6.4.2) locates the cause: the
  wall is KT's union-dimension obstruction (eq. 6.67) SHARPENED into a wall by the project's `caseIIICandidate`
  extensor-override, which KT does not use (KT keeps the bottom as the literal full-rank IH matrix `R(G₁,q₁)`,
  no transport-into-overridden-span). **RECOMMENDED escape = (C)/fresh** — the literal-IH-matrix-bottom
  block-additivity cert (the only structural wall-escape; reuses the block-additivity backbones + discriminator
  + realization tail + D1; tears out the `mixedBottom`/transport apparatus). Needs a new-math leaf (the
  IH-matrix-as-literal-bottom bridge, KT 6.61/6.62) gated on one foundational spike — FLAGGED, not decomposed
  (§(4.69.6)). (α1)/(α2) are BLOCKED + less faithful. None touches the motive/IH/C.0–C.6 (the obstruction is
  below the contract). No αD/cert leaf builds until the user picks.
- **GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive) — orthogonal to the cert;
  tracked separately, lands with 23f/the spine.
- **Downstream (23g+):** ENTRY's `exists_chain_data_of_noRigid` reshape + floor lift + OD-1, then ASSEMBLY.
  The frozen contract (C.5/C.6) is invariant; none touches 23e's cert. ENTRY is parallel-safe.

## Hand-off / next phase

**STOP — USER DECISION among the escapes; the KT-faithfulness recon (design §(4.69), 2026-06-27) RECOMMENDS
(C)/fresh and names the open question. NOT a build.** Route α (user-chosen literal `Matrix`) is BLOCKED on
both faces (§(4.68)); the broad re-read settles which path is closest to KT + feasible:

**RECOMMENDED — (C)/fresh: the literal-`R(G₁,q₁)`-bottom block-additivity cert** (KT §6.4.2's actual
structure; design §(4.69.5)). The bottom block is the LITERAL full-rank IH framework's rigidity rows (from D1
`interior_hsplitGP` / `hsplitGP`), via KT's (6.61) column op + (6.62) row correspondence as a `Matrix`
submatrix containment — NOT a span membership in the overridden candidate. This is the ONLY direction that
structurally dissolves the §(4.29) wall (the override-meets-gate collision never forms). **The next concrete
step is a SINGLE compiler-checked feasibility spike (design §(4.69.6)):** does
`(R(candidate)*U).submatrix (corner ⊕ bottom) en = fromBlocks Mᵢ 0 C R(Gab)` hold with `R(Gab)` the literal
IH matrix (full rank by `hsplitGP`), WITHOUT a relabel-transport span membership? That settles the one open
foundational question (is the candidate's non-slot row agreement a `Matrix` equality or still a cycle-relabel
transport?) and hence whether (C) is the genuinely-different feasible path §(4.30) hoped, or relocates the
wall. **FLAG (don't force):** (C) crosses a new-math leaf (the IH-matrix-as-literal-bottom bridge, KT
6.61/6.62) — so the agent does NOT manufacture an A1–A6 decomposition; the spike is the deliverable. The W6e
tail-coupling is VERIFIED BENIGN (the A2 `rank = finrank span` bridge is rank-route-agnostic; the landed
`_zero₁₂` cert already concludes the candidate span finrank — design §(4.69.6)(2)).

**The alternatives (both BLOCKED, less faithful; design §(4.69.4)):** (α1) a wall-free `W`-producer for the
chain arm — BLOCKED, it IS the wall (`funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` PROVES the
transport hits the gate); lowest faithfulness ("possibly real new-math wall"). (α2) a `ρ₀`-aligned `±r`
corner for `_aug` that does not pull the `e_b` block into the row op — BLOCKED, its only escape (remove the
mandatory `e_b`-fill from the bottom) breaks the full-rank count (§(4.62)) and overlaps (C). **None touches
the motive/IH/C.0–C.6** — the obstruction is below the contract, in the cert's *transport-into-candidate-span*
device (NOT the block-additivity split).

**Do NOT build against any arm** until the user picks. `d=3` stays fully green (zero-regression); nothing in
this session touched Lean (DOCS-only — spikes were deleted before commit; §(4.69) verification was
source-read + signature-read, no committed scratch).

**Still-live / reusable regardless of the escape (in tree, axiom-clean):** D1 `interior_hsplitGP`
(`Realization.lean`, the IH-fed interior split-off realization — feeds any arm's base `Fbase`); the
discriminator `exists_shared_redundancy_and_matched_candidate` (`Realization.lean:1481`, the two gates
`hperp` `:1511` / `hρe₀` `:1535` + the W6b `cGv` widening); the realization TAIL `case_III_realization_of_rank`
(`Arms.lean:63`, consumes only `hrank`); the 23e cert backbone `Rank.lean:622` + column op `U` + the
operated-entry bricks. **Landed-but-now-dead-arm:** the `_aug` ladder (αE1–αE4), `_matrix`/`_rowOp`, the
chain arm + LEAF-B2 — all sound Lean, none usable as-is; αE6 (retire them) stays DEFERRED to phase-close.

On the chosen escape closing the interior corner, the CHAIN layer closes and ENTRY (**23g**) opens; ASSEMBLY
is **23h**.

## Decisions made during this phase

### Phase-local choices and proof techniques (compressed — most of the 23f bottom-arc / row-op apparatus is deleted by route (α), §(4.66); reasoning in git)

**Still-live (route-(α)-reused):**
- **αE5 = the dead-machinery deletion; the old HD `_sumElim_` wrapper went with the `cornerRowInjection`
  family** (this commit). The §(4.66.F/G) keep/delete list deletes the `(e_b,j₀)`-collision apparatus
  (BOT-2′, avoiding-engine, D2, `cornerRowInjection` + `_injective`/`_sumElim_injective`, leaves (ii)/(iv)).
  Judgment call: `linearIndependent_toBlocks₂₂_row_sumElim_mixedBottom_of_finrank_eq` (the old HD wrapper)
  baked `cornerRowInjection` into its TYPE, so it is part of that family and was deleted too — route (α)'s
  αD2 rebuilds HD over the genuine `inr` `re` shape from the surviving `_mixedBottom_of_finrank_eq`
  producer. All deletes were zero-firing-caller orphans (grep-verified); the dangling docstring refs (B1/B2
  "leaf (ii)/(iv)" mentions, the A5d section header, D1's BOT-2′ ref) were rewritten in the same commit.
  Pure deletion; gates clean; no friction (two longLine warnings on my own new docstring lines, QUIRKS §55).
- **αE4 = the augmented wrapper = a near-verbatim clone of `case_III_arm_realization_rowOp`, matrix
  swap; the ⚑ `hblock` residual dissolves because B1/B2 are generic** (prior commit).
  `case_III_arm_realization_aug` is `…_rowOp` (`ForkedArm.lean:315`) with `rigidityMatrixEdge →
  rigidityMatrixEdgeAug`, `re`/`Lrow` over the augmented index `(({e//…}×Fin(D−1)))⊕Unit`, ADD
  `(rRow, hr)`, the cert call swapped `…_zero₁₂ → …_aug` (with `hr` threaded). The §(4.66.E/F) "⚑
  residual" (re-derive `hblock` for `augM`) was over-cautious: B1 `exists_rowOp_of_strictInjection`
  (index-agnostic over `p`) and B2 `rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂` (fully
  `M' : Matrix p q K`-generic) are carrier-blind, so the `_rowOp` wrapper's exact `conv_lhs => rw
  [Matrix.mul_assoc]; exact …_zero₁₂ _ Lrow hre _ L₀ hLsub hzero hM'eq hB` body line fires on
  `augM * U` UNCHANGED. αE4 carries the OPERATED `hA : LI (A − L₀ * C).row` (leaf (iii),
  §(4.66.F.iii) resolved). Axiom-clean (standard triple). No friction (only QUIRKS §55 longLine).
- **αE3 = the augmented cert = a verbatim clone of `case_III_rank_certification_zero₁₂`, engine swap**
  (prior commit). `case_III_rank_certification_aug` is `…_zero₁₂` (`Candidate.lean:2446`) with
  `rigidityMatrixEdge → rigidityMatrixEdgeAug`, `Lrow`/`re` carrying the `⊕ Unit` augmented row index,
  `(rRow, hr : rRow ∈ span F₀.rigidityRows)` added, and the body's engine call
  `…_of_edge_submatrix_fromBlocks_zero₁₂` replaced by the LANDED αE2 `…_of_aug_submatrix_…` (+ `hr`
  threaded between `hblock` and `hA`). The count tail (`hends'`/`hm₁`/`hm₂`/`hVcard`/`hVone`) is
  byte-identical. Axiom-clean (standard triple). No friction (first-try compile post long-line wrap).
- **αE2 = the augmented engine = a verbatim clone of the edge `_zero₁₂` engine, EQUALITY→`.trans`**
  (prior commit). `finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂` is
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
  (EXCLUSION-steering for the `(e_b,j₀)` collision — built to feed the §(4.65)-refuted `hred`); the old HD
  `_sumElim_` wrapper (it baked `cornerRowInjection` into its type); leaves (ii)/(iv) (bijection special cases).
  All SOUND, axiom-clean, zero firing callers under route (α). (The free BOT-2 engine + bridge stay.)
- **KEPT (CORRECTED §(4.66.F) — discharge the still-required row op `Lrow`):** B1/B2 (entrywise strict-injection
  row op, no `Equiv` middle index); BOT-3′ `matrix_eq_mul_of_span_mem` (HB, `B=L₀·D` from span-membership) + leaf (i)
  `matrix_eq_mul_of_dual_row_comb`; leaf (iii) `corner_hA_zero₁₂_of_gate` (the OPERATED-corner HA = αD3, NOT the bare
  `corner_hA'_of_gate`); `finScrewDimSplitCorner` (leaf (iii)'s `em₁`); R1 `…_eq_rigidityRows_of_off` + BOT-1
  (the bottom `hspan_id`). Friction logged where it arose (the §61-family dependent-rewrite trap; FRICTION:125/
  QUIRKS §64 the `m₂` `[Fintype]`-in-statement-type requirement) — all pre-existing, no new entries this commit.
