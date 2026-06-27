# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress. Opened 2026-06-26 as the *fifth* CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d +
23e + 23f). 23e landed the KT-faithful A3-transposed rank certificate + its LA scaffolding axiom-clean
(`notes/Phase23e.md`); 23f builds the **geometry arm** that *constructs* the cert's block data from the
IH-fed `cGv` widening, then the candidate-matching gate bridge and the general-`k` chain dispatch + CHAIN-5.
**Phase 23 stays in progress.** The authoritative recon is `notes/Phase23-design.md` §(4.54) (the re-pointed
hand-off, the three-leaf geometry-arm plan, the framework-vs-arm split, the both-block coupling). Program map:
`notes/MolecularConjecture.md`.

## Current state

**Next concrete commit = R1 (the RESTRICTED-edge cross-framework BOT-1 variant + the zero-`e_a`-row span-drop).**
**BOT-2 LANDED this commit, axiom-clean, in TWO pieces:** the free basis-pick *engine*
`exists_finCard_linearIndependent_selection` (`Rank.lean`, top-level before `namespace Matrix` — the indexed,
fixed-cardinality companion of `exists_linearIndependent'`: `finrank (span (range χ)) = N → ∃ injective
sel : Fin N → ι, LinearIndependent (χ ∘ sel)`, a basis of the spanned *proper* submodule), and the candidate-level
*bridge* `BodyHingeFramework.bottom_selection_of_crossFramework_span` (`Concrete.lean`, right after
`linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`) — it takes BOT-1's concrete conclusion `hspan_id`
(the a-shifted FULL candidate edge family spans `span F₂.rigidityRows`), the def-0 count `hfr`, and `hbot2_all`
(no candidate edge records `v` second), and produces EXACTLY the wrapper's `hD` data `(re, hbot2, hbot1, hrank)`:
`hbot1` = the excluded-middle tautology, `hbot2` from `hbot2_all`, `hrank` = `finrank_span_eq_card` of the FREE LI
selection (route (a) refuted §(4.58.B)). The pick never lands on `e_a` (its a-shifted row `hingeRow a a = 0`).

**THE CONCRETE BOT-1 INSTANTIATION HITS A GENUINE OBSTRUCTION (kernel-checked, §(4.60.B)).** The coordinator-flagged
subtlety RESOLVES: BOT-1's `hlink₁` ranges over ALL of `E(F₁)` incl. the corner `e_a`, whose a-shift gives
`ends₁ e_a = (a, a)`, demanding `Gab.IsLink (remap e_a) a a` — a self-loop, FALSE in loopless `Gab` for any
`remap e_a`. So `span_range_hingeRow_crossFramework_eq_rigidityRows` is NOT instantiable over the full `E(G)` family
as-stated. The fix (R1): a RESTRICTED-edge BOT-1 variant (over `Gv`-edges + `e_b` only) + the zero-`e_a`-row drop
(`hingeRow a a = 0`, so the full-family `hspan_id` follows from the restricted one). The bridge ALREADY accepts the
full-family `hspan_id` (the extra `e_a` zero rows leave the span unchanged), so only `hspan_id`'s discharge is owed.
**BOT-1 (the abstract cross-framework lemma) stays in tree, correct + axiom-clean** — R1 is a restricted SIBLING, not
an edit. Full residual + the two routes (R1 recommended; R2 = weaken `hlink₁`, rejected) in design §(4.60.C).

**THE BLOCKED-CONFLATION FRAMING IS CORRECTED (kernel-checked this commit).** The prior hand-off framed BOT-1 as
"needs the term-distinct `R(Gab)`-row matching the design flags as partly BLOCKED in matrix form
(`rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom` docstring)." This was a CONFLATION. The BLOCKED thing is the
**matrix-EQUALITY** `submatrix_columnOp_toBlocks₂₂_eq_Gab` (`notes/Phase23d.md`), whose residual needs equal *chosen*
basis vectors `F₁.blockBasisOn = F₂.blockBasisOn` — false for `finBasisOfFinrankEq` on term-distinct submodules. The
project AVOIDED it via the **RANK route** (L-span/L-rank/L-hD), and BOT-1 is a **span SET-equality** proven by mutual
inclusion — a *different, buildable* thing. Span equality is robust to basis choice (it needs equal BLOCKS, which the
support-extensor match gives, not equal basis VECTORS), so the term-distinct wall never reforms. BOT-1 built sorry-free.

**RHS CORRECTION (kernel-checked):** §(4.58.E)'s BOT-1 sig wrote RHS = `span (caseIIICandidate …).rigidityRows`. That
is WRONG — `finrank (span (caseIIICandidate …).rigidityRows) = D·(|V(G)|−1)` (the cert's conclusion), which is LARGER
than the bottom block's `card m₂ = D·(|V(Gab)|−1)`. HD's `hrank` (the consumer, `linearIndependent_toBlocks₂₂_row_
mixedBottom_of_finrank_eq`) needs `finrank (span (a-shifted family)) = card m₂`, so the RHS must be a space of finrank
`D·(|V(Gab)|−1)` = **`span (R(Gab)).rigidityRows`** (the IH split-off framework `F₂ = Q.toBodyHinge`, def-`0` rigid).
This matches the Phase-23d *step 4* hand-off intent exactly ("compose L-span [span = `span F₂.rigidityRows`] with
`finrank (span F₂.rigidityRows) = D·(|V_Gab|−1) = #m₂` from `hsplitGP`"). The a-shifted family lives on `F₁`'s
`blockBasisOn` while `R(Gab)` is a different framework, so the single-framework L-span does NOT apply directly — hence
the cross-framework lemma is the genuinely-new keystone, NOT redundant with L-span.

BOT-3′ landed the prior commit (the route-(b) HB span-membership leaf, axiom-clean). **Recon HEADLINE
(§(4.57.A), PROBE-A kernel-read):** HD's `hrank` is `w`-FREE — a basis-pick from full-rank `R(Gab)` (fed by
`hsplitGP`), NOT a "realize the W6b `w` as `(e,j)`-rows" bridge (that prior framing was wrong). **BOT-3 OPEN
DECISION ADJUDICATED (§(4.58), kernel-checked):** route (b) wins, costs **NO wrapper-signature change** (HB does NOT
need the `cGv` widening — `span(D-rows) = span R(Gab) ⊇ hingeRow a b ρ₀`, a span repr supplies `L₀`). The RE
**corner half** landed (axiom-clean): `cornerRowInjection` (`Concrete.lean`, A5d section) is the injective corner read
`Fin (D−1) ⊕ Unit → ({e // e ∈ E(G)} × Fin (D−1))` (the `D−1` `e_a`-panel rows + the one `±r` slot at `(e_b, j₀)`, KT
(6.64)/(6.66)); `cornerRowInjection_injective` from `e_a ≠ e_b`; `finScrewDimSplitCorner : Fin (screwDim k) ≃
Fin (D−1) ⊕ Unit` reindexes `m₁`. The cert-firing wrapper SKELETON `case_III_arm_realization_rowOp`
(`ForkedArm.lean`) fires `case_III_rank_certification_zero₁₂` via B1/B2 + `U`/`en`, sorry-free, carries the 5 owed
sub-leaves (`re`/`hre`/`L₀`/`hM'eq`/`hB`/`hA`/`hD`) as hypotheses (§(4.56)). **The next commit is BOT-2** (the index
basis-pick: from BOT-1's spanning family reaching finrank `card m₂`, extract an LI sub-selection of `card m₂`
`(e,j)`-indices → `bottom : m₂ → p`, `hbot2`/`hbot1` structural, `hrank` = `finrank_span_eq_card`), then BOT-4
(the `Sum.elim` assembly + HMEQ), then HA's `hAeq`, the dispatch wires `case_III_arm_realization_rowOp`, then item
3c/item 4.

**The matrix-algebra backbone (B1/B2) + the wrapper skeleton are COMPLETE; the geometry-arm leaves (i)–(iv) are in-tree:**
all six leaves are in-tree axiom-clean — (i) `matrix_eq_mul_of_dual_row_comb`, (iii)
`corner_hA_zero₁₂_of_gate`, the landed-but-superseded bijection leaves (ii) `reindex_rowOp_isUnit_det` / (iv)
`reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂`, and **the strict-injection siblings** (B1)
`exists_rowOp_of_strictInjection` + (B2) `rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂` (this commit;
the general-arm replacements for (ii)/(iv) — the `re` shape is SETTLED = strict injection, §(4.55)). B1 produces
`⟨Lrow, IsUnit Lrow.det, Lrow.submatrix re re = [1,−L₀;0,1], off-image-vanishing⟩` via the extended equiv
`e' : (m₁⊕m₂) ⊕ ↥(range re)ᶜ ≃ p`; B2 consumes B1's two structural facts (the selected block + the off-image
vanishing) and splits the product *entrywise* by `Fintype.sum_of_injective` (NO `Equiv` middle index — the
strict injection has none) to the cert's `hblock` shape. Both axiom-clean, full project build + lint green,
zero-regression.

**The 5 owed sub-leaves (§(4.56), the wrapper's carried hypotheses; the dispatch discharges):** RE (the strict
`re` + `hre`, NO precedent), HMEQ (`(fromBlocks_toBlocks _).symm`), HB (`B = L₀·D`, leaf (i) + the owed `μ`-match),
HA (`(A−L₀C).row` LI, leaf (iii) + the owed `hAeq` + gate), HD (`D.row` LI, `mixedBottom` + the IH `hrank`). Exact
kernel-checked sigs in §(4.56). Then item 3c (gate bridge), item 4 (dispatch + CHAIN-5).

The single arm-coupling is `L₀` (= the `cGv` weights, re-keyed by leaf (i)) — `cGv` is a conclusion of the IH-fed
W6b producer `exists_candidateRow_bottomRows_of_rigidOn` (`Candidate.lean:401`, takes
`hrig : IsInfinitesimallyRigidOn Gab` + `h622lb`), NOT derivable from
`caseIIICandidate`'s abstract `G`/`ends`/`e_a`/`e_b`/`v`. The `re`/`m₂` split is by contrast
FRAMEWORK-determined (the corner/bottom predicates reference only `ends`/`v`/`a`/`e_a`/`e_b`). Nothing is
mid-stream; tree clean. `d=3` stays fully green (zero-regression, hard constraint).

**Why the `re` shape is (b) strict injection (recon verdict, §(4.55)).** The grounded cardinality relation is
`card m₁ + card m₂ = D·(|V(G)|−1) ≤ (D−1)·|E(G)| = card p`, an **inequality** from the in-tree chain
`rank(M(G̃)) = D·(|V|−1)` (def-0, `rank_matroidMG_of_isKDof_zero`) + `rank(M(G̃)) ≤ (D−1)·|E(G)|` (the matroid
`rk_le_card`, `Operations.lean:882`–885). Equality is NOT stated; a minimal-0-dof graph is NOT forced
`(D,D)`-tight, so `card m₁+card m₂ < card p` is generic. Hence no bijection `(m₁⊕m₂) ≃ p` in general, while a
strict injection always exists (`card ≤ card`) — so leaves (ii)/(iv) (which fix a bijection) serve only the
measure-zero isostatic-tight case, and B1/B2 (which subsume them) are the general shape.

## Architectural choices made up front (inherited from 23e / the frozen contract)

- **Cert is consumed, not re-derived.** The 23e cert chain is axiom-clean and SATISFIABLE; 23f only
  *produces* its block data. Build `hblock`/`hA` against the literal `Lrow * M * U` product, NOT the
  component leaves in isolation (the §(4.46)/(4.54) lesson — compiler-check the FULL composition before
  declaring "remaining = assembly"; two leaves were elided when this was skipped).
- **Both-block coupling: zeroing `B` and mutating `A→A'` are ONE row op.** `ρ₀` is `A`-pin minus `L₀·C`-pin,
  computed from `cGv` — NOT a free choice; leaves (ii)/(iii) share the same `L₀`.
- **`d=3` zero-regression via the cert FORK.** `d=3` keeps the `_matrix`/M₃ path; only the general-`d` arm
  routes through `case_III_rank_certification_zero₁₂`. Do NOT unify the two.
- **Below the CHAIN↔ENTRY contract + the motive/IH.** The geometry arm + dispatch are below C.3/C.1 and the
  0-dof motive. The frozen interface (C.0–C.6) + the sanctioned C.3 `hIH` addition stay valid.

## Lemma checklist

The geometry arm: leaves (i)–(iv) + the `re`-shape recon + the strict-injection siblings B1/B2 + the
cert-firing wrapper SKELETON + the bottom sub-arc leaves BOT-3′/BOT-1 all landed (axiom-clean). Settled
entries are one-lined below (full proof detail in design §(4.54)–(4.59) + git); the active forward items
(`[~]` RE bottom sub-arc, `[ ]` HMEQ/HB/HA/HD, the gate bridge, the dispatch) stay detailed.

- [x] **(i)** `BodyHingeFramework.matrix_eq_mul_of_dual_row_comb` (`Concrete.lean`) — the `cGv`→`w` re-key
  `B = L₀·D` core (RANK-route, feeds `of_eq_mul_of_row_comb`). Superseded for the wrapper's HB by BOT-3′ (route
  (b)); kept for explicit-weight consumers.
- [x] **(ii)** `Matrix.reindex_rowOp_isUnit_det` (`Rank.lean`) — the bijection unit-det bridge. SUPERSEDED by B1
  (the `re` shape is a strict injection, §(4.55)); zero-caller orphan, kept as the bijection special case.
- [x] **(iii)** `BodyHingeFramework.corner_hA_zero₁₂_of_gate` (`Concrete.lean`) — the operated-corner `hA` from
  the entrywise read `hAeq` + the gate (`±r` row reads `ρ₀`, KT (6.66)). STILL OWED at the wrapper: the entrywise
  `hAeq` + the `em₁`/`coordEquiv` packaging (= sub-leaf HA below).
- [x] **(iv)** `Matrix.reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂` (`Rank.lean`) — the bijection `hblock`
  backbone. SUPERSEDED by B2 (strict injection, §(4.55)); zero-caller orphan, kept as the bijection special case.
- [x] **(recon §(4.55))** the `re` shape = (b) STRICT INJECTION (`card m₁+card m₂ ≤ card p` is an inequality, not
  forced `=`; no bijection `(m₁⊕m₂) ≃ p` in general). Leaves (ii)/(iv) (bijection-only) don't serve; B1/B2 owed +
  subsume them.
- [x] **(B1)** `Matrix.exists_rowOp_of_strictInjection` (`Rank.lean`) — the strict-injection unit-det `Lrow` on
  `p` (block op on `range re` + identity on the complement, via the extended equiv `e' : (m₁⊕m₂)⊕(range re)ᶜ ≃ p`)
  + the off-image vanishing B2 consumes. Subsumes (ii).
- [x] **(B2)** `Matrix.rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂` (`Rank.lean`) — the strict-injection
  `hblock` reducer to `fromBlocks (A−L₀C) 0 C D` (splits the product entrywise via `Fintype.sum_of_injective`, no
  `Equiv` middle index). Subsumes (iv).
- [x] **wrapper SKELETON** `PanelHingeFramework.case_III_arm_realization_rowOp` (`ForkedArm.lean`) — takes the
  (4b″) block data `(re,hre,L₀,hM'eq,hB,hA,hD)`, builds `Lrow`(B1)/`U`/`en`/`hblock`(B2) in-body, fires the cert
  (`A` slot = the OPERATED `A−L₀C`; `C` stays nonzero — the `_zero₁₂` shape clears the §(4.41) wall), runs the
  realization tail. §(4.56) spike: composes sorry-free. STILL OWED: the 5 carried hyps (RE/HMEQ/HB/HA/HD below).
- [x] **(BOT-3′)** `BodyHingeFramework.matrix_eq_mul_of_span_mem` (`Concrete.lean`) — the route-(b) HB discharge:
  recovers `L₀` from `hmem : ∀ i, φ i ∈ span (range χ)` (the span-membership sibling of leaf (i), via
  `mem_span_range_iff_exists_fun` + `of_eq_mul_of_row_comb`). Subsumes the dissolved BOT-3 `μ`-match.
- [x] **(BOT-1)** `BodyHingeFramework.span_range_hingeRow_crossFramework_eq_rigidityRows` (`Basic.lean`) — the
  cross-framework spanning identity (abstract): candidate a-shifted family spans `span R(Gab).rigidityRows` (def-0,
  finrank `card m₂`), given surjective `remap` + `hspan`/`hlink₁`. A span SET-equality. **NOT instantiable over the
  FULL `E(G)` family** — the corner `e_a`'s a-shift `ends₁ e_a = (a,a)` breaks `hlink₁` (would need `Gab.IsLink _ a a`,
  a self-loop; §(4.60.B)). The concrete `hspan_id` discharge is the R1 residual (restricted-edge variant + zero-`e_a`
  drop). BOT-1 stays correct in tree; R1 is a restricted sibling, not an edit.
- [x] **(BOT-2)** the FREE basis-pick, TWO pieces (this commit, axiom-clean): `exists_finCard_linearIndependent_selection`
  (`Rank.lean`, the engine: `finrank (span (range χ)) = N → ∃ injective sel : Fin N → ι, LI (χ ∘ sel)`) +
  `BodyHingeFramework.bottom_selection_of_crossFramework_span` (`Concrete.lean`, the candidate-level bridge:
  `hspan_id` [BOT-1's full-family conclusion] + `hfr` [def-0 count] + `hbot2_all` → the wrapper's `(re, hbot2, hbot1,
  hrank)`). `hbot1` = excluded-middle tautology; `hrank` = `finrank_span_eq_card` of the LI selection. NO steering
  (route (a) refuted). Card pins `hm₂` TRIVIAL off `Fin`. The bridge takes the FULL-`p` `hspan_id` (the `e_a` zero
  rows leave the span unchanged), so only `hspan_id`'s discharge (R1) is owed.
- [~] **(RE) the strict row injection `re` + `hre`** — §(4.56) sub-leaf. `re : Fin (screwDim k) ⊕ Fin (D·(|V(Gv)|−1)) →
  {e ∈ E(G)}×Fin(D−1)`: corner = `e_a`-panel + `±r` slot `(e_b, j₀)`; bottom = the BOT-2 selection.
  **CORNER HALF DONE** (460c0e3): `cornerRowInjection`/`_injective`/`finScrewDimSplitCorner` (`Concrete.lean` A5d).
  **BOTTOM HALF: BOT-2 DONE this commit; only R1 (`hspan_id` discharge) + BOT-4 (`Sum.elim`) remain.**
- [ ] **(HMEQ/HB/HA/HD) the four block reads** — §(4.56) sub-leaves. HMEQ = `(fromBlocks_toBlocks _).symm` (the
  four `toBlocks`, instantiating `D` = the mixedBottom `toBlocks₂₂`); HB = `B = L₀·D` via **span-membership**
  (route (b), §(4.58)): each `B`-row functional ∈ `span(D-rows) = span R(Gab)` (the full-rank basis-pick `D`), then
  `matrix_eq_mul_of_span_mem` (**BOT-3′ LANDED this commit**) — NOT the `cGv`-widening `μ`-match (that route (a)
  obligation is refuted/dissolved). STILL OWED at the wrapper: the per-`B`-row span-membership `hmem` facts (each
  corner `B`-row ∈ `span(D-rows)`), which BOT-1's spanning identity supplies; HA = `(A−L₀C).row` LI (leaf (iii) +
  the owed entrywise `hAeq` from `_apply_corner`/`_apply_eB_off_pin` + the gate `hρe₀`); HD = `D.row` LI — `w`-FREE
  (§(4.57.A)): `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` + the BOT-2 `hrank` (basis-pick of
  full-rank `R(Gab)`, fed `hsplitGP` via `splitOff_isMinimalKDof`, the C.3 `hIH` add). Sigs: §(4.56)/§(4.57).
- [ ] **(3c) candidate-matching gate bridge** — `F.supportExtensor e_a` ↔ LEAF-3's
  `panelSupportExtensor (q(candidateVtx i)) n'` via `caseIIICandidate_supportExtensor_candidate`
  (`Candidate.lean:960`) + `candidateVtx i = a` (interior: `= vtx i.succ`). Confirm against
  `caseIIICandidate_supportExtensor_candidate` + the `ChainData` `d = k+1` fact, NOT `Fin`-arithmetic.
- [ ] **(4) the dispatch + CHAIN-5** — `chainData_dispatch` (the `Fin cd.d` router: base/`d=3` →
  `chainData_split_realization`; interior → `chainData_arm_realization_sep` now fed the sound cert, the
  interior `hsplitGP` via `splitOff_isMinimalKDof`); LEAF-4 disjoint-block bundle takes the `mixedBottom`
  bottom (no membership); LEAF-5 router; then CHAIN-5 (the C.0 lockstep reshape of `hdispatch`/`hcand` to the
  frozen `ChainData` record + the `d=3` zero-regression adapter). Lands the C.3 `hIH` addition.

## Blockers / open questions

- **C.3 `hIH`-on-consume-shape addition — APPROVED** (user-adjudicated 2026-06-26, session #36; lands with
  23f). The interior arm needs the INTERIOR-split `hsplitGP` (`G.splitOff vᵢ …`), derivable only from `hIH`
  via `splitOff_isMinimalKDof`, not in the frozen C.3 signature — so add `hIH` to the C.3 dispatch
  consume-shape: a one-field addition touching the C.0 producer/consumer/ENTRY lockstep trio, NOT a
  motive/IH-strength change. Context: design §(4.43) *THE ONE INTERFACE OBLIGATION* + §C.3.
- **RE-bottom open decision — RESOLVED (§(4.58), kernel-checked spike; route (b), no wrapper change).** Route (a)
  (steer the basis-pick to CONTAIN the `cGv`-support) is REFUTED: the W6b conclusion carries NO `LinearIndependent`
  clause on the `cGv`-summands, so they cannot seed `LinearIndependent.extend`. Route (b) wins and needs NO
  `(hB,hD)`-signature revisit — `hB : B = L₀·D` only needs each `B`-row in `span(D-rows)`, which the full-rank
  basis-pick `D` (= what HD wants anyway) supplies for free (`span(D) = span R(Gab) ⊇ hingeRow a b ρ₀`). BOT-3
  (the `μ`-matching) DISSOLVES into a span-membership leaf BOT-3′ (`matrix_eq_mul_of_span_mem`, core kernel-checked).
- **GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive) — orthogonal to the cert;
  tracked separately, lands with 23f/the spine.
- **Build against the literal product, not the component leaves** (the §(4.46)/(4.54) lesson, twice-burned).
  When building `hblock`/`hA`, instantiate the cert's `(Lrow * M * U).submatrix re en` literally and trace
  the goals — the two elided leaves ((ii)/(iii)) surfaced only when the §(4.54) spike did this end-to-end.
- **Cleanup owed (phase-close): the superseded bijection leaves (ii)/(iv) are now zero-caller orphans.**
  `Matrix.reindex_rowOp_isUnit_det` (ii) and `Matrix.reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂` (iv) have
  no callers in tree (grep-confirmed 2026-06-26) and B1/B2 subsume them; the wrapper fires the cert via B1/B2
  for all cases. §(4.55) chose to KEEP them annotated as the bijection special case (no blueprint pins, no
  deletion mandate) — so this is a soft cleanup, not a deviation. Decide delete-vs-keep once the wrapper
  confirms B1/B2 serve in practice (at the wrapper landing or phase-close); if deleting, reword the leaf-(ii)/(iv)
  checklist annotations + §(4.55)'s "kept" note in the same commit.
- **Downstream (23g+):** ENTRY's `exists_chain_data_of_noRigid` reshape + floor lift + OD-1, then ASSEMBLY.
  The frozen contract (C.5/C.6) is invariant; none touches 23e's cert. ENTRY is parallel-safe.

## Hand-off / next phase

**Next concrete commit = R1 (the RESTRICTED-edge cross-framework BOT-1 variant + the zero-`e_a`-row span-drop) —
the only remaining bottom-sub-arc brick before the wrapper's `hD` is fully fed.** BOT-2 landed this commit
(`exists_finCard_linearIndependent_selection` + `bottom_selection_of_crossFramework_span`, axiom-clean): the bridge
produces the wrapper's `(re, hbot2, hbot1, hrank)` from BOT-1's `hspan_id` + the def-0 count + `hbot2_all`. What R1
must build (design §(4.60.C)): a restricted-index sibling of `span_range_hingeRow_crossFramework_eq_rigidityRows`
(quantifying `remap`/`hspan`/`hlink₁` only over `Gv`-edges + `e_b`, which DO have a genuine `Gab`-image) in
`Basic.lean`, then the zero-`e_a`-row span-drop (`hingeRow a a = 0`) lifting it to the full-`p` `hspan_id` the
bridge wants. **Why R1 not the full-family instantiation:** `e_a`'s a-shift `ends₁ e_a = (a,a)` makes `hlink₁` at
`e_a` demand `Gab.IsLink _ a a` (a self-loop, FALSE) — kernel-checked §(4.60.B). R2 (weaken BOT-1's `hlink₁`) is
rejected (a BOT-1 signature edit). The concrete `remap`/`hspan`/`hlink₁` then lands INSIDE the dispatch (item 4),
where `Q`/`Gab = G.splitOff v a b e₀`/`e₀`/`q` are bound (`Realization.lean:302`): `remap` = `Gv`↦itself, `e_b`↦`e₀`;
`hspan` from `hingeRow_mem_rigidityRows_of_supportExtensor_eq` (block reads only the support extensor) +
`caseIIICandidate_supportExtensor_reproduced` at `t=0`; `hlink₁` from `Q.ends`; `hbot2_all` from `hsplitG`/`hends`.

**After R1:** BOT-4 (the `Sum.elim` assembly — a CLEAN leaf, compiled sorry-free in PROBE-B:
`Function.Injective.sumElim (cornerRowInjection_injective hne j₀).comp …` — + HMEQ via `(fromBlocks_toBlocks _).symm`).
Then HA's `hAeq`, the dispatch wires `case_III_arm_realization_rowOp` (consuming `bottom_selection_of_crossFramework_span`
+ R1 for `hspan_id`), item 3c / item 4. **BOT-1 + BOT-2 + BOT-3′ + the RE corner half + the cert-firing wrapper
SKELETON done.** On the dispatch landing, the CHAIN layer closes and ENTRY (**23g**) opens; ASSEMBLY is **23h**.

**Cardinalities ground by stated facts (design §(4.57.C)/§(4.60.B)):** `card m₂ = D·(|V(Gv)|−1) = D·(|V(Gab)|−1) =
finrank (span R(Gab).rigidityRows)` (`vertexSet_splitOff` = `rfl`, so `V(Gab)=V(Gv)`; def-0 rigid identity). The
bottom edges sit at the `Gv`/`R(Gab)` level; `e_a` is the corner (∈ `m₁`), and its a-shifted row is the zero
functional `hingeRow a a` — never selected.

The arm's `re` is SETTLED = **strict injection** (§(4.55)). The wrapper rides on B1/B2, not on the superseded
bijection leaves (ii)/(iv).

**What is in-tree (cite directly — axiom-clean):**
- **Leaf BOT-2** (23f, this commit): `exists_finCard_linearIndependent_selection` (`Rank.lean`, top-level before
  `namespace Matrix`) — the free index basis-pick engine: `(χ : ι → V) [Finite ι] {N} (hrank : finrank (span
  (range χ)) = N) : ∃ sel : Fin N → ι, Function.Injective sel ∧ LinearIndependent (χ ∘ sel)`. The indexed,
  fixed-cardinality companion of `exists_linearIndependent'` (a basis of the spanned *proper* submodule). PLUS the
  candidate-level bridge `BodyHingeFramework.bottom_selection_of_crossFramework_span` (`Concrete.lean`, after
  `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`): `(F ends hgp) {v a} {m₂}[Fintype] (F₂)
  (hspan_id : span (range a-shifted-FULL-family) = span F₂.rigidityRows) (hfr : finrank (span F₂.rigidityRows) =
  card m₂) (hbot2_all : ∀ e, (ends e.1).2 ≠ v) : ∃ re hbot2 hbot1, finrank (span (a-shifted family ∘ re)) = card m₂`
  — EXACTLY the consumer's `(re, hbot2, hbot1, hrank)`. `[Finite β]`, NOT `[Fintype α]`.
- **Leaf BOT-1** (23f): `BodyHingeFramework.span_range_hingeRow_crossFramework_eq_rigidityRows` (`Basic.lean`, after
  the L-span leaf) — the abstract cross-framework spanning identity (`F₁ F₂`, `remap` surjective, `hspan`/`hlink₁`).
  Span SET-equality, `le_antisymm` + a `remap`-section. **NOT instantiable over the full `E(G)` family** (`e_a`'s
  a-shift breaks `hlink₁`, §(4.60.B)); the concrete `hspan_id` is discharged by R1 (restricted variant + zero-`e_a`
  drop). Stays in tree, correct.
- **Leaf BOT-3′** (23f, prior commit): `BodyHingeFramework.matrix_eq_mul_of_span_mem` (`Concrete.lean`, right after
  leaf (i) `matrix_eq_mul_of_dual_row_comb`) — the route-(b) HB span-membership re-key. Sig:
  `[DecidableEq α] {m₁ m₂ n} [Fintype m₂] (χ : m₂ → Dual (α→ScrewSpace k)) (φ : m₁ → …) (cols : n → α × Fin D)
  (hmem : ∀ i, φ i ∈ span (range χ)) : ∃ L₀, (of fun i x ↦ φ i (single (cols x).1 (finScrewBasis k (cols x).2)))
  = L₀ * (of fun i' x ↦ χ i' (single …))`. Proof: `choose c` the per-row repr weights
  (`Submodule.mem_span_range_iff_exists_fun`), `L₀ := of c`, close with `of_eq_mul_of_row_comb`. Subsumes the
  dissolved BOT-3 `μ`-coupling; leaf (i) stays for explicit-weight consumers.
- **The RE corner half** (23f, prior commit 460c0e3): `cornerRowInjection` + `cornerRowInjection_injective` +
  `finScrewDimSplitCorner` (`Concrete.lean`, the new "A5d" section after `edgeRowSplit_corner_card`).
  `cornerRowInjection (e_a e_b : {e // e ∈ E(G)}) (j₀ : Fin (D−1)) : Fin (D−1) ⊕ Unit → ({e // e ∈ E(G)}) × Fin (D−1)`
  `= Sum.elim (fun j => (e_a, j)) (fun _ => (e_b, j₀))` (the `D−1` `e_a`-panel rows + the one `±r` slot at `e_b`, KT
  (6.64)/(6.66)); `cornerRowInjection_injective` proves `Function.Injective` from `e_a ≠ e_b` (via
  `Function.Injective.sumElim`; the panel rows are second-coord-injective, the `±r` slot vacuous, the blocks never
  collide as their edge first-coords differ — the load-bearing fact, **no axioms**); `finScrewDimSplitCorner :
  Fin (screwDim k) ≃ Fin (D−1) ⊕ Unit` (via `Fintype.equivFinOfCardEq` off `one_le_screwDim`) reindexes
  `m₁ = Fin (screwDim k)` onto the split (HA's `em₁` reuses it). Carrier-agnostic, no `ScrewSpace` reach-in.
- **The cert-firing wrapper SKELETON** (23f, prior commit 5cd6db8): `PanelHingeFramework.case_III_arm_realization_rowOp`
  (`ForkedArm.lean`, after `…_matrix_sep`) — the `_zero₁₂` sibling of `case_III_arm_realization_matrix`/`_sep`.
  Carries the row-op (4b″) block data `(re, hre, L₀, hM'eq, hB, hA, hD)`, constructs `Lrow` (B1) / `U`+`hU` /
  `en := (columnSplit v).symm` / `hblock` (B2, via `Matrix.mul_assoc`) in-body, fires
  `case_III_rank_certification_zero₁₂`, runs `case_III_realization_of_rank` → `HasGenericFullRankRealization k n G`.
  Cert's `A` slot = OPERATED `A − L₀C`; lower-left `C` free (nonzero on the mixed bottom). `[Fintype α]`, no
  `set F` (defeq-seam shadow). The §(4.56) decomposition names the 5 carried sub-leaves.
- **Leaf B1** (23f): `Matrix.exists_rowOp_of_strictInjection` (`Rank.lean`, after
  `reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂`) — the strict-injection unit-det / rank-invariance bridge. From
  `re : m₁⊕m₂ → p` injective + `L₀`, produces `∃ Lrow`, `IsUnit Lrow.det`, `Lrow.submatrix re re = [1,−L₀;0,1]`,
  and the off-image vanishing `∀ i x, x ∉ range re → Lrow (re i) x = 0`. Via the EXTENDED equiv
  `e' : (m₁⊕m₂) ⊕ ↥(range re)ᶜ ≃ p` + `Lrow := reindex e' e' (fromBlocks [1,−L₀;0,1] 0 0 1)` + `det_reindex_self`
  / `det_fromBlocks_zero₂₁`. Carrier/field-agnostic. Subsumes leaf (ii).
- **Leaf B2** (23f, this commit): `Matrix.rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂` (`Rank.lean`,
  after B1) — the strict-injection `hblock` reducer. Takes `Lrow` + B1's `hLsub`/`hzero` + `hM' : M'.submatrix
  re en = fromBlocks A B C D` + leaf-(i) `hB : B = L₀·D`, concludes `(Lrow * M').submatrix re en =
  fromBlocks (A − L₀C) 0 C D`. Splits the product entrywise via `Fintype.sum_of_injective` (no `Equiv` middle
  index) + `rowOp_zeroes_upperRight`. Carrier/field-agnostic. Subsumes leaf (iv).
- **Leaf (iv)** (23f): `Matrix.reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂` (`Rank.lean`, after
  `of_eq_mul_of_row_comb`) — the bijection `hblock` reduction backbone (the bijection special case B2 subsumes;
  fixes a bijection `e : (m₁⊕m₂) ≃ p`, so does NOT serve the general arm — §(4.55)).
- **Leaf (iii)** (23f): `BodyHingeFramework.corner_hA_zero₁₂_of_gate` (`Concrete.lean`, after
  `corner_hA'_of_gate`) — the post-row-op corner-`hA` bridge: `LinearIndependent ℝ A.row` for the cert's
  operated `A = toBlocks₁₁(Lrow*M*U)`, from the entrywise read `hAeq` (operated corner = coordinate matrix of
  `[blockBasisOn(e_a,·); ρ₀]` reindexed by `em₁ : m₁ ≃ Fin (screwDim k − 1) ⊕ Unit`) + the gate `hρe₀`, via
  `Matrix.linearIndependent_row_of_coordEquiv` + `corner_hA'_of_gate`.`comp`. Carrier/coordinatization-agnostic.
- **Leaf (ii)** (23f): `Matrix.reindex_rowOp_isUnit_det` (`Rank.lean`, after `rowOp_isUnit_det`) —
  the `Lrow`-on-`p` reindex unit-det bridge `IsUnit (Matrix.reindex e e (fromBlocks 1 (−L₀) 0 1)).det` for
  `e : (m₁ ⊕ m₂) ≃ p`, via `Matrix.det_reindex_self` + `rowOp_isUnit_det`; carrier/field-agnostic. (Correct
  lemma, but fixes a BIJECTION `e`, so it does NOT serve the general arm — §(4.55); owed leaf B1 subsumes it.)
- **Leaf (i)** (23f): `BodyHingeFramework.matrix_eq_mul_of_dual_row_comb` (`Concrete.lean`, the
  "A6 — the corner's off-`v` block `B` factors as `L₀ · D`" section) — the `cGv`→`w` re-key feeding
  `of_eq_mul_of_row_comb`; carrier/framework-agnostic (abstract `φ`/`χ`/`μ`/`cGv`/`cols`).
- The reshaped A3-transposed cert chain (23e): `rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` (`Rank.lean`),
  `finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks_zero₁₂` (`Concrete.lean`),
  `case_III_rank_certification_zero₁₂` (`Candidate.lean`), all consuming `(Lrow, hLrow, U, hU, …, hblock, …)`.
- The row-op LA facts `rowOp_isUnit_det` + `rowOp_zeroes_upperRight` (`Rank.lean`); the matrix-algebra half
  `Matrix.of_eq_mul_of_row_comb` (`Rank.lean`); the mathlib `rank_mul_eq_right_of_isUnit_det` +
  `det_reindex_self`.
- `corner_hA'_of_gate` (`Concrete.lean:620`, the ρ₀-augmented family) + its leaf-(iii) matrix-level consumer
  `corner_hA_zero₁₂_of_gate` (the cert's `hA` for the operated `A`); `exists_corner_blockBasisOn_linearIndependent`
  (`Concrete.lean:566`, the un-op'd `[blockBasisOn(e_a); blockBasisOn(e_b,j₀)]` family — the alternative shape,
  NOT used on the row-op route).
- The union-dimension discriminator + `exists_shared_redundancy_and_matched_candidate` (Phase 23c).
- The `mixedBottom` family + `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` (`Concrete.lean:1685`,
  supplies `hD`, includes the `e_b`-fill row); `rigidityMatrixEdge_mul_columnOp_apply_pin_zero` (the LOWER-left
  pin-zero — `Gv` rows only); the operated-entry bricks `…_apply_corner`/`_apply_eB_off_pin`/`_apply_off_pin`.
- The `cGv` widening (W6b producer `exists_candidateRow_bottomRows_of_rigidOn`, `Candidate.lean:401`;
  `chainData_split_w6b_gates`, `Realization.lean:825`–831).
- The interior arm wrapper `chainData_arm_realization_sep` (`CaseIII/Realization.lean`) — parks here until the
  sound cert is wired through; it carries the disjoint-block obligations as hypotheses.

**STILL TO BUILD (all 23f):** the matrix-algebra backbone (B1/B2) + the cert-firing wrapper SKELETON
(`case_III_arm_realization_rowOp`) + the **RE corner half** + **BOT-3′** + **BOT-1** (abstract) + **BOT-2** (the
free basis-pick engine + the candidate-level bridge, this commit, axiom-clean) are COMPLETE. Owed → the remaining
RE bottom sub-arc + the wrapper's carried hyps: **R1** (next) the restricted-edge cross-framework BOT-1 variant +
the zero-`e_a`-row span-drop discharging the bridge's `hspan_id` (BOT-1 not full-family-instantiable, §(4.60.B)),
then **BOT-4** `re := Sum.elim (corner ∘ finScrewDimSplitCorner) bottom` + HMEQ (`fromBlocks_toBlocks`). Then HB
(`hmem` per-`B`-row span facts, fed BOT-3′), HA (`(A−L₀C).row` LI, leaf (iii) + `hAeq` + gate), HD (`D.row` LI,
mixedBottom + the bridge's `hrank`) → the dispatch wires `case_III_arm_realization_rowOp` (consuming the bridge + R1
for `hspan_id`; the concrete `remap`/`hspan`/`hlink₁` land here where `Q`/`Gab`/`e₀` are bound) → (3c) gate bridge →
the dispatch + CHAIN-5. All matrix-backbone leaves + BOT-3′ + BOT-1 + BOT-2 are in-tree, axiom-clean. On the
dispatch landing → 23g (ENTRY) → 23h (ASSEMBLY).

## Decisions made during this phase

### Phase-local choices and proof techniques

- **BOT-2 is a FREE basis-pick in two pieces; the concrete BOT-1 instantiation hits the `e_a`-row obstruction
  (R1 owed).** The engine `exists_finCard_linearIndependent_selection` (`Rank.lean`) extracts an injective
  `Fin N → ι` index selection from `finrank (span (range χ)) = N` (the indexed companion of
  `exists_linearIndependent'`; `κ`-finiteness forces a basis-of-submodule detour, FRICTION Open entry). The bridge
  `bottom_selection_of_crossFramework_span` (`Concrete.lean`) wires BOT-1's `hspan_id` + the def-0 count + `hbot2_all`
  to the wrapper's `(re, hbot2, hbot1, hrank)`: `hbot1` is the excluded-middle TAUTOLOGY, `hrank` =
  `finrank_span_eq_card` of the LI pick, the pick never lands on `e_a` (`hingeRow a a = 0`). The bridge takes the
  FULL-`p` `hspan_id`, but BOT-1 (the cross-framework lemma) is NOT instantiable over the full `E(G)` family — `e_a`'s
  a-shift `ends₁ e_a = (a,a)` breaks `hlink₁` (self-loop). Fix = R1 (restricted-edge BOT-1 + zero-`e_a` drop), design
  §(4.60). Both BOT-2 lemmas axiom-clean.
- **BOT-1 is a span SET-equality (the cross-framework L-span), NOT the BLOCKED matrix-equality — the prior
  "term-distinct, partly BLOCKED" framing was a CONFLATION (kernel-checked this commit).** The BLOCKED thing is
  `submatrix_columnOp_toBlocks₂₂_eq_Gab` (a matrix-EQUALITY needing equal *chosen* basis vectors `F₁.blockBasisOn
  = F₂.blockBasisOn`, false for `finBasisOfFinrankEq` on term-distinct submodules, `notes/Phase23d.md`); the project
  AVOIDED it via the RANK route. BOT-1 (`span_range_hingeRow_crossFramework_eq_rigidityRows`, `Basic.lean`) is a
  span equality proven by `le_antisymm` — robust to basis choice (needs equal BLOCKS, supplied by the
  support-extensor match, not equal basis VECTORS), so the wall never reforms. It is the cross-framework
  generalization of the landed L-span `span_range_hingeRow_blockSpanning_eq_rigidityRows` (two frameworks `F₁`
  candidate / `F₂ = R(Gab)`, a surjective edge-`remap` absorbing the `Gv↔Gv`/`e_b↔e₀` relabel + the `a`-shift in
  `ends₁`). Built sorry-free; the single-framework L-span does NOT apply directly (the a-shifted family lives on
  `F₁.blockBasisOn` while `R(Gab)` is a different framework), so BOT-1 is genuinely-new, not redundant.
- **BOT-1's RHS is `span (R(Gab)).rigidityRows`, NOT `span (caseIIICandidate …).rigidityRows` (§(4.58.E) was
  wrong).** `finrank (span candidate.rigidityRows) = D·(|V(G)|−1)` (the cert's conclusion) is LARGER than the bottom
  block's `card m₂ = D·(|V(Gab)|−1)`. HD's consumer `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`
  needs `finrank (span (a-shifted family)) = card m₂`, so the RHS must be the IH split-off framework's row span
  (`F₂ = Q.toBodyHinge`, def-0 rigid → finrank `D·(|V(Gab)|−1)`). This matches the Phase-23d *step 4* hand-off
  ("compose L-span with `finrank (span F₂.rigidityRows) = #m₂` from `hsplitGP`") exactly.
- **BOT-3′ taken first in the bottom sub-arc, ahead of the §(4.58.E) BOT-1→4 listing order, as the lowest-risk
  fully-specified leaf.** `matrix_eq_mul_of_span_mem` is the route-(b) HB discharge: it consumes only the span
  membership `hmem : ∀ i, φ i ∈ span (range χ)` and recovers `L₀` internally via
  `Submodule.mem_span_range_iff_exists_fun` (`[Fintype m₂]`) + leaf (i)'s engine `of_eq_mul_of_row_comb` — a
  near-mechanical mirror of leaf (i) (`matrix_eq_mul_of_dual_row_comb`), no new friction. Its core was kernel-checked
  in the §(4.58) spike (`probe_matrix_eq_mul_of_span_mem`). Sequenced before BOT-1 as the lower-risk leaf; BOT-1's
  "partly BLOCKED in matrix form" risk turned out to be a CONFLATION (BOT-1 is a span SET-equality, the BLOCKED
  thing is a different matrix-equality — see the BOT-1 entry above), so BOT-1 then built straightforwardly.
  Carrier/framework-agnostic, axiom-clean.
- **RE split corner-half-first; the bottom is a basis-pick sub-arc (HD is `w`-FREE — §(4.57) recon correction).**
  The corner half is carrier-agnostic and free-standing, so it lands complete: `cornerRowInjection := Sum.elim
  (fun j => (e_a, j)) (fun _ => (e_b, j₀))` over `Fin (D−1) ⊕ Unit` (KT (6.64) `e_a`-panel + (6.66) `±r` slot),
  `cornerRowInjection_injective` from `e_a ≠ e_b` via `Function.Injective.sumElim` (no axioms — the genuinely-new
  injectivity content), and `finScrewDimSplitCorner : Fin (screwDim k) ≃ Fin (D−1) ⊕ Unit` (`Fintype.equivFinOfCardEq`
  off `one_le_screwDim`) reindexing `m₁`. The **bottom half** is a 3–5-commit SUB-ARC (design §(4.57.E)): a
  basis-pick of `card m₂` `(e,j)`-rows from full-rank `R(Gab)` (BOT-1 spanning identity → BOT-2 index pick),
  the `μ`-matching for HB (BOT-3, the localized W6b coupling), the `Sum.elim` (BOT-4). The §(4.56)/prior framing
  that the bottom "must realize the W6b `w` as `(e,j)`-rows" was REFUTED by PROBE-A: HD's `hrank` mentions only
  `re`/`ends`/`a`/`v`/`blockBasisOn`, no `w`/`cGv` (§(4.57.A)); the `cGv` coupling is HB-only (§(4.57.B)).
- **The cert-firing wrapper composes sorry-free; the gaps decompose into 5 carried sub-leaves (§(4.56)).** A
  compiler-checked end-to-end spike fired `case_III_rank_certification_zero₁₂` for the real arm via B1→`Lrow`,
  B2→`hblock`, `U`/`hU` (`prodColumnOpEquiv_transpose_toMatrix'_det_isUnit`), `en := (columnSplit v).symm`, leaf
  (iii)→`hA`, mixedBottom→`hD` — sorry-free once `(re, hre, L₀, hM'eq, hB, hA, hD)` are supplied. Banked as
  `case_III_arm_realization_rowOp` (`ForkedArm.lean`). Three load-bearing seams (kernel-confirmed): cert's `A`
  slot = OPERATED `A − L₀C` (`(A := A−L₀*C)`, leaf (iii)); `Lrow*M*U` vs B2's `Lrow*(M*U)` bridged by
  `Matrix.mul_assoc`; **`set F := caseIIICandidate …` SPLITS the defeq seam (shadows `re`)** — use the literal
  candidate + `[Fintype α]`. The lower-left `C` is NONZERO (the `e_b`-fill pin read — the §(4.41) wall the
  `_zero₁₂` shape clears; `_zero₁₂` zeros the UPPER-right `B`, leaves `C` free). Owed sub-leaf RE (the strict
  `re`) has NO in-tree precedent and is FLAGGED as the hardest piece; card pins trivial off `Fin`-types.
- **B1/B2 split the matrix product *entrywise* through the strict injection — no `Equiv` middle index.** The
  general arm's `re : m₁⊕m₂ → p` is a strict injection (`card ≤ card`, §(4.55)), so `submatrix_mul_equiv`
  (leaf (iv)'s engine, needs a bijective middle index) does not apply. B1 (`exists_rowOp_of_strictInjection`)
  builds `Lrow := reindex e' e' (fromBlocks [1,−L₀;0,1] 0 0 1)` over the EXTENDED equiv
  `e' : (m₁⊕m₂) ⊕ ↥(range re)ᶜ ≃ p` (`Equiv.ofInjective re` + `Equiv.Set.sumCompl`) and exports — besides
  `IsUnit Lrow.det` (via `det_reindex_self` + `det_fromBlocks_zero₂₁`) and `Lrow.submatrix re re = [1,−L₀;0,1]`
  — the **off-image vanishing** `∀ i x, x ∉ range re → Lrow (re i) x = 0` (the image rows touch only image
  columns, `Bext`'s upper-right block being `0`). B2 (`rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂`)
  consumes those two structural facts and splits `∑ x:p, Lrow (re i) x · M' x (en j)` by
  `Fintype.sum_of_injective` (off-image columns vanish by `hzero`; image columns reindex by `re` with
  `Lrow (re i) (re k) = [1,−L₀;0,1] i k` from `hLsub`) → `[1,−L₀;0,1] · M'.submatrix re en`, then `hM'` +
  `rowOp_zeroes_upperRight`. Rank invariance is NOT exported (the cert derives it from `IsUnit Lrow.det`).
  Friction: the `re`-in-`Set.range re` dependent-rewrite trap (the §61-family, already logged) forced the
  pointwise `e'.symm (re x) = Sum.inl x` + `ext` route over `rw [re = e' ∘ inl]`; `m₂` stays `[Fintype]`
  (its `L₀ * D` matrix-mul is in the *statement type* — FRICTION:125 / QUIRKS §64), `m₁` is `[Finite]`.
- **Leaf (iv) `hblock` reducer takes `re := ⇑e`, splits through the middle `e`.**
  `reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂` (`Rank.lean`) is the pure matrix-algebra `hblock` backbone: it
  composes leaf (ii)'s `Lrow := reindex e e [1,−L₀;0,1]`-on-`p` shape with `rowOp_zeroes_upperRight`, taking the
  column-op'd block read `hM' : M'.submatrix e en = fromBlocks A B C D` + leaf (i)'s `hB : B = L₀·D` to the cert's
  `hblock` `(Lrow * M').submatrix e en = fromBlocks (A − L₀C) 0 C D`. The key move: `submatrix_mul_equiv` splits
  the product through the middle index using `e` itself, after which `Lrow.submatrix e e` collapses to the raw
  `[1,−L₀;0,1]` (`reindex_apply` + `submatrix_submatrix`, `e.symm ∘ e = id`) — so taking `re := ⇑e` (the bijection
  as the cert's row injection) makes the row op land exactly on the selected block. Carrier/field-agnostic; all
  arm-coupling (`e`/`L₀ := cGv`/`en`, the `M' = M*U` column-op, the entrywise `hM'`) deferred to the wrapper. No
  friction; the only adjust was the standing `Finite`+`Fintype.ofFinite` `unusedFintypeInType` fix on `m₁`.
- **Leaf (iii) is an abstract matrix-level bridge, coordinatization-agnostic.** `corner_hA_zero₁₂_of_gate`
  takes the operated corner read as the matrix hypothesis `hAeq` (operated `A` = coordinate matrix of the
  `D`-member family `[blockBasisOn(e_a,·); ρ₀]` reindexed by `em₁ : m₁ ≃ Fin (screwDim k − 1) ⊕ Unit`, over
  ANY `coordEquiv : Dual ℝ (ScrewSpace k) ≃ₗ (κ → ℝ)`) + the gate `hρe₀`, and produces `LinearIndependent ℝ
  A.row`. All arm-coupling (the entrywise `hAeq` from the operated-entry bricks composed with `Lrow`'s
  `cGv`-weights; the `em₁`/`coordEquiv` packaging) is deferred to the assembly — keeping the genuinely-new
  §(4.54) content (the operated `±r` row reads `ρ₀`, not `blockBasisOn`, so the un-op'd
  `linearIndependent_toBlocks₁₁_row_of_corner_gate` does NOT serve) separable. Two-step proof:
  `Matrix.linearIndependent_row_of_coordEquiv` re-wrap + `corner_hA'_of_gate`.`comp` (`em₁` injective); no
  friction (the row-rewrap + `LinearIndependent.comp` are exactly the existing API).
- **Leaf (ii) reindexes the row op onto `p`, not through `re`.** `reindex_rowOp_isUnit_det` carries the row op
  as `Matrix.reindex e e [1,−L₀;0,1]` on the full edge index `p` (`e : (m₁⊕m₂) ≃ p`), then proves its det a
  unit by `Matrix.det_reindex_self` + the landed `rowOp_isUnit_det`. (The alternative — a row op living on
  `m₁⊕m₂` split into `M` via `submatrix_mul` — is unavailable: `submatrix_mul` needs a *bijective* middle
  index, so the op is reindexed onto `p` by the bijection `e` instead.) **The arm's `re` is a strict INJECTION,
  not this bijection (verdict (b), §(4.55)): `card m₁+card m₂ ≤ card p` is an inequality (not forced `=`), so no
  `e : (m₁⊕m₂) ≃ p` exists in general — this lemma does NOT serve the general arm; the genuinely-new sibling
  B1 (the block op on `range re` extended by identity, via the EXTENDED equiv on `(m₁⊕m₂) ⊕ (p∖range re)`) is
  owed and subsumes it.** Carrier/field-agnostic,
  arm-coupling (the `e` packaging + `L₀ := cGv`-weights) deferred to the assembly. Proof is two lines, no
  friction. `m₁`/`m₂` carry `[Finite]` (only `p` is type-relevant); `Fintype.ofFinite` recovers the proof-side
  instances — the standing `unusedFintypeInType` fix (CLAUDE.md build-gates §1), not new friction.
- **Leaf (i) stated carrier/framework-agnostic, not arm-coupled.** `matrix_eq_mul_of_dual_row_comb` is the
  pure matrix-algebra `B = L₀·D` core: it takes abstract dual functionals `φ`/`χ`, a matching `μ`, weights
  `cGv`, and a single-body-column index `cols`, and produces `B = Matrix.of w · D` for `of_eq_mul_of_row_comb`.
  All the arm-coupling (the `Gv.IsLink`→`re`-image membership that builds `μ`; matching `φ` to the corner read
  `_apply_eB_off_pin` and `χ` to the `mixedBottom` block) is deferred to the assembly — keeping the genuinely-
  new content (the `cGv`→`w` fiberwise re-key via `Finset.sum_fiberwise`) separable and reusable. Proof is one
  `of_eq_mul_of_row_comb` + `LinearMap.sum_apply`/`smul_apply` + `Finset.sum_fiberwise`/`sum_mul`; no friction.
  `[DecidableEq α]` added for `Pi.single` (standard requirement, not an API gap).
