# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress. Opened 2026-06-26 as the *fifth* CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d +
23e + 23f). 23e landed the KT-faithful A3-transposed rank certificate + its LA scaffolding axiom-clean
(`notes/Phase23e.md`); 23f builds the **geometry arm** that *constructs* the cert's block data from the
IH-fed `cGv` widening, then the candidate-matching gate bridge and the general-`k` chain dispatch + CHAIN-5.
**Phase 23 stays in progress.** The authoritative recon is `notes/Phase23-design.md` §(4.54) (the re-pointed
hand-off, the three-leaf geometry-arm plan, the framework-vs-arm split, the both-block coupling). Program map:
`notes/MolecularConjecture.md`.

## Current state

**Next concrete commit = HA's `hAeq` (the entrywise operated-corner read: compose `_apply_corner` with
`Lrow`'s `cGv`-subtraction so the operated `±r` row reads `ρ₀`, fed to `corner_hA_zero₁₂_of_gate` with
`em₁ := finScrewDimSplitCorner` + the gate `hρe₀`).** **BOT-4 LANDED this commit, axiom-clean:**
`cornerRowInjection_sumElim_injective` (`Concrete.lean`, A5d, right after `cornerRowInjection_injective`) — the
full strict row injection's injectivity. `re := Sum.elim (cornerRowInjection e_a e_b j₀ ∘ finScrewDimSplitCorner)
bottom`; `hre` via `Function.Injective.sumElim ((cornerRowInjection_injective hne j₀).comp
finScrewDimSplitCorner.injective) hbotinj hdisj`, where `hdisj` splits on the corner index (`rcases
finScrewDimSplitCorner c with j | u`): the `Sum.inl j` panel slot `(e_a, j)` avoids the bottom by the carried
`hbot_ne_ea : ∀ i, (bottom i).1 ≠ e_a`, the `Sum.inr ()` `±r` slot `(e_b, j₀)` by BOT-2′'s carried `havoid : ∀ i,
bottom i ≠ (e_b, j₀)`. `hbotinj` is BOT-2′'s selection injectivity. **HMEQ needs NO new lemma** — it is mathlib's
`Matrix.fromBlocks_toBlocks _).symm` applied verbatim at the dispatch (set the wrapper's `A/B/C/D` to the four
`toBlocks` of the operated submatrix; `D` is then the mixedBottom `toBlocks₂₂`). The two `hdisj` inputs
(`havoid`/`hbot_ne_ea`) are carried as BOT-4 hypotheses; the dispatch discharges them — `havoid` from BOT-2′,
`hbot_ne_ea` from `hingeRow a a = 0` (`hingeRow_self`) leaving the `e_a` row out of any LI bottom pick. **BOT-2′
LANDED a prior commit, axiom-clean:**
`BodyHingeFramework.bottom_selection_of_crossFramework_span_avoiding` (`Concrete.lean`, right after BOT-2) — the
EXCLUSION-STEERED candidate bridge off the BANKED engine `exists_finCard_linearIndependent_selection_avoiding`: same
`hspan_id`/`hfr`/`hbot2_all` as BOT-2, plus an excluded index `p₀` (= `(e_b, j₀)`) + a redundancy `hred` (the `p₀`-row
functional ∈ span of the remaining `(e,j)`-rows), producing the wrapper's `(re, hbot2, hbot1, hrank)` PLUS `havoid :
∀ i, re i ≠ p₀`. `hred` re-states defeq against the `set χ` abbreviation; a near-mechanical mirror of BOT-2 (the engine
does the rank work). **The `(e_b, j₀)` JOINT-SATISFIABILITY TENSION is now FULLY DISCHARGED in Lean (recon §(4.61),
kernel-checked).** The free BOT-2 pick CAN select the corner's `±r` slot `(e_b, j₀)` (KT (6.66); a nonzero `R(Gab)`
row, hence pickable), so `hdisj : ∀ i, re i ≠ (e_b, j₀)` is NOT derivable from BOT-2's outputs and `re` injectivity
breaks. Route **(a) EXCLUSION-STEERING** is the fix (route (c) "drop `re` injectivity" rejected — B1/B2 need
`Equiv.ofInjective re hre`; route (b) "steer `j₀`" folds into (a)). The avoiding pick carries a redundancy `hred`
that is **the SAME fact as HB** (`B = L₀·D` ⟺ the off-`v` `±r` row factors through the bottom `D`-rows), grounded in
the W6b `hingeRow a b ρ₀ ∈ span R(Gv)` but a STRONGER `j₀`-literal instantiation. The §(4.61.E) feasibility pass found
the wrapper's 7 carried hyps JOINTLY dischargeable (`hM'eq`'s `D` IS the one mixedBottom `toBlocks₂₂` HB/HA/HD reference,
`ForkedArm.lean:349`); NO cert/motive/wrapper-signature change. Both the engine + BOT-2′ are now in tree axiom-clean.

**R1 LANDED a prior commit, axiom-clean, in `Basic.lean` as ONE lemma**
(the restricted-edge variant + the zero-`e_a` drop folded into a single hypothesis): `BodyHingeFramework.span_range_
hingeRow_crossFramework_eq_rigidityRows_of_off` quantifies the cross-framework matching (`remap` surjective, `hspan`,
`hlink₁`) only over the genuine edges `{e // P e}` (the `Gv`-edges + `e_b`), and takes a separate `hoff : ∀ e, ¬P e →
∀ i, hingeRow (ends₁ e).1 (ends₁ e).2 (B e i) = 0` discharging the corner `e_a`'s degenerate `(a,a)` row to the **zero**
functional — so the FULL `E(F₁) × ι` family spans exactly `span F₂.rigidityRows`. **This produces the bridge's
`hspan_id` shape DIRECTLY** (a compile-checked spike instantiated R1 with `ends₁ := if (ends e).1 = v then a else …`
and `B := blockBasisOn` and matched `bottom_selection_of_crossFramework_span`'s `hspan_id` argument exactly, then was
removed — §(4.60.C), the "build against the literal" gate). Supporting leaf: **`hingeRow_self`** (`@[simp]`,
`hingeRow a a r = 0`, after `hingeRow_apply`) — the `e_a`-row vanishing `hoff` will cite at the dispatch. The
`e_a`-row obstruction (§(4.60.B): the full-family BOT-1 `hlink₁` at `e_a` demands the self-loop `Gab.IsLink _ a a`,
false) is now FULLY RESOLVED — R1's `hoff` carries those rows instead of `hlink₁`. BOT-1 stays in tree, correct
(the unrestricted abstract sibling; R1 is the dispatch-ready restricted form, not an edit).

**BOT-1's framing settled (prior commits):** the "partly BLOCKED in matrix form" cite was a CONFLATION (the BLOCKED
thing is the matrix-EQUALITY `submatrix_columnOp_toBlocks₂₂_eq_Gab`; BOT-1 is a span SET-equality, robust to basis
choice); and §(4.58.E)'s BOT-1 RHS was WRONG (`span (R(Gab)).rigidityRows`, finrank `card m₂`, NOT the candidate's
`D·(|V(G)|−1)`). Both recorded in design §(4.59); BOT-1 is the genuinely-new cross-framework keystone, built sorry-free.

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

The geometry arm's matrix backbone, wrapper skeleton, and the full RE strict injection (corner +
bottom sub-arc) all landed axiom-clean. Settled entries are one-lined (full detail in design
§(4.54)–(4.61) + git); the active forward items (`[ ]` HMEQ/HB/HA/HD, gate bridge, dispatch) stay
detailed. **The RE strict injection `re`/`hre` is COMPLETE in tree.**

- [x] **(i)** `matrix_eq_mul_of_dual_row_comb` (`Concrete.lean`) — `cGv`→`w` `B=L₀·D` core (superseded for HB by BOT-3′; kept for explicit-weight consumers).
- [x] **(ii)/(iv)** `reindex_rowOp_isUnit_det` / `reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂` (`Rank.lean`) — the BIJECTION unit-det + `hblock` bridges. SUPERSEDED by B1/B2 (strict injection, §(4.55)); zero-caller orphans, kept as the bijection special case.
- [x] **(iii)** `corner_hA_zero₁₂_of_gate` (`Concrete.lean`) — operated-corner `hA` from `hAeq` + the gate. OWED at the wrapper: the entrywise `hAeq` (= sub-leaf HA below).
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
- **The `(e_b, j₀)` joint-satisfiability tension — DISCHARGED in Lean (§(4.61), route (a) exclusion-steering).** The
  free BOT-2 pick can select the corner's `±r` slot `(e_b, j₀)`, breaking `re` injectivity; the fix exclusion-steers
  the bottom over `{p // p ≠ (e_b,j₀)}` carrying a redundancy `hred` that IS HB (`B = L₀·D`). Both the engine
  (`exists_finCard_linearIndependent_selection_avoiding`) and the candidate bridge **BOT-2′** are in tree axiom-clean;
  NO cert/motive/IH/C.0–C.6/wrapper-signature change. **Remaining**: the *concrete* `hred` discharge lands at the
  dispatch (item 4) from the W6b `hingeRow a b ρ₀ ∈ span R(Gv)` + the `j₀`↔redundancy-support coupling (the SAME
  `cGv`/`lamAB` data feeding HB, §(4.61.D)) — tracked under *Hand-off* "After BOT-4" + the HB sub-leaf.
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

**Next concrete commit = HA's `hAeq`** — the entrywise operated-corner read. Compose `…_apply_corner`
(the `e_a`-panel + `±r` pin reads, `Concrete.lean:1412`) with `Lrow`'s `cGv`-subtraction to get the operated
`±r` row = `ρ₀`, then feed `corner_hA_zero₁₂_of_gate` with `em₁ := finScrewDimSplitCorner` + the gate `hρe₀`
(from the discriminator `Realization.lean:1470`). This produces the wrapper's `hA : LinearIndependent ℝ (A − L₀ *
C).row` input. Then the dispatch wires `case_III_arm_realization_rowOp`.

**BOT-4 landed this commit** (`cornerRowInjection_sumElim_injective`, `Concrete.lean` A5d, right after
`cornerRowInjection_injective`): the full strict row injection's injectivity, `re := Sum.elim (cornerRowInjection
e_a e_b j₀ ∘ finScrewDimSplitCorner) bottom`, `hre` via `Function.Injective.sumElim ((cornerRowInjection_injective
heab j₀).comp finScrewDimSplitCorner.injective) hbotinj hdisj` where `hbotinj` is BOT-2′'s selection injectivity and
`hdisj` is built (by splitting on the corner index `rcases finScrewDimSplitCorner c with j | u`) from BOT-2′'s
`havoid : ∀ i, bottom i ≠ (e_b, j₀)` (the `Sum.inr ()` `±r` slot) + the carried `hbot_ne_ea : ∀ i, (bottom i).1 ≠
e_a` (the `Sum.inl j` `e_a`-panel slots). **HMEQ needs no new lemma** — it is mathlib `Matrix.fromBlocks_toBlocks
_).symm` applied at the dispatch (set the wrapper's `A/B/C/D` to the four `toBlocks` of the operated submatrix; `D`
is then the mixedBottom `toBlocks₂₂`). The two `hdisj` inputs are carried as BOT-4 hypotheses the dispatch
discharges: `havoid` from BOT-2′, `hbot_ne_ea` from `hingeRow a a = 0` (`hingeRow_self`) leaving the `e_a` row out
of any LI bottom pick.

**After HA's `hAeq`:** the dispatch wires `case_III_arm_realization_rowOp` — consuming BOT-2′ fed R1's `hspan_id`,
instantiated where `Q`/`Gab = G.splitOff v a b e₀`/`e₀`/`q`/`ρ₀`/`j₀`/`cGv`/`lamAB` are bound (off
`exists_shared_redundancy_and_matched_candidate` `Realization.lean:1416` + `chainData_split_w6b_gates` `:771`): `P` =
"genuine `Gab`-image" (`Gv`-edges + `e_b`), `remap` = `Gv`↦itself / `e_b`↦`e₀`; `hspan` from
`hingeRow_mem_rigidityRows_of_supportExtensor_eq` + `caseIIICandidate_supportExtensor_reproduced` at `t=0`; `hlink₁` from
`Q.ends`; `hoff` from `hingeRow_self` at `e_a`; `hbot2_all` from `hsplitG`/`hends`; **`hred`** from the W6b `hingeRow a b
ρ₀ ∈ span R(Gv)` + the `j₀`↔redundancy-support coupling (the SAME `cGv`/`lamAB` data feeding HB, §(4.61.D)). Then item
3c (gate bridge) / item 4 (dispatch + CHAIN-5). **BOT-1 + the free BOT-2 + BOT-3′ + R1 + the avoiding-engine + BOT-2′ +
the RE corner half + BOT-4 + the cert-firing wrapper SKELETON done — the RE strict injection `re`/`hre` is fully
assembled.** On the dispatch landing, the CHAIN layer closes and ENTRY (**23g**) opens; ASSEMBLY is **23h**.

**Cardinalities ground by stated facts (design §(4.57.C)/§(4.60.B)):** `card m₂ = D·(|V(Gv)|−1) = D·(|V(Gab)|−1) =
finrank (span R(Gab).rigidityRows)` (`vertexSet_splitOff` = `rfl`, so `V(Gab)=V(Gv)`; def-0 rigid identity). The
bottom edges sit at the `Gv`/`R(Gab)` level; `e_a` is the corner (∈ `m₁`), and its a-shifted row is the zero
functional `hingeRow a a` — never selected.

The arm's `re` is SETTLED = **strict injection** (§(4.55)). The wrapper rides on B1/B2, not on the superseded
bijection leaves (ii)/(iv).

**What is in-tree (cite directly — axiom-clean):**
- **Leaf BOT-4** (23f, this commit): `cornerRowInjection_sumElim_injective` (`Concrete.lean`, A5d, right after
  `cornerRowInjection_injective`) — the full strict row injection's injectivity. Sig: `{G} {e_a e_b}
  (hne : e_a ≠ e_b) (j₀) {m₂} (bottom : m₂ → {e // e ∈ E(G)} × Fin (D−1)) (hbotinj : Injective bottom)
  (havoid : ∀ i, bottom i ≠ (e_b, j₀)) (hbot_ne_ea : ∀ i, (bottom i).1 ≠ e_a) : Injective (Sum.elim
  (cornerRowInjection e_a e_b j₀ ∘ finScrewDimSplitCorner) bottom)`. Via `Function.Injective.sumElim`; `hdisj`
  splits on the corner index. Carrier-agnostic. The dispatch discharges `havoid` (BOT-2′) + `hbot_ne_ea`
  (`hingeRow_self`). **HMEQ** rides on mathlib `Matrix.fromBlocks_toBlocks _).symm` — no new lemma.
- **Leaf BOT-2′** (23f, prior commit): `BodyHingeFramework.bottom_selection_of_crossFramework_span_avoiding`
  (`Concrete.lean`, right after BOT-2) — the EXCLUSION-steered candidate bridge: same `(F ends hgp) {v a} {m₂}[Fintype]
  (F₂) hspan_id hfr hbot2_all` as BOT-2 plus `(p₀)` (= `(e_b, j₀)`) + `(hred : χ p₀ ∈ span (range (χ over {p // p ≠
  p₀})))`, concludes `∃ re hbot2 hbot1 havoid, finrank (span (a-shifted family ∘ re)) = card m₂` with the extra
  `havoid : ∀ i, re i ≠ p₀`. `[Finite β]`, NOT `[Fintype α]`. Runs the BANKED avoiding-engine; `hred` re-states defeq
  against the `set χ` abbreviation. Near-mechanical mirror of BOT-2; BOT-4's `hdisj` consumes `havoid`.
- **The avoiding-engine** (23f, prior commit): `exists_finCard_linearIndependent_selection_avoiding` (`Rank.lean`, after
  the free engine) — `(χ : ι → V) [Finite ι] (i₀ : ι) {N} (hrank : finrank (span (range χ)) = N)
  (hred : χ i₀ ∈ span (range (χ over {i // i ≠ i₀}))) : ∃ sel : Fin N → ι, Injective sel ∧ LI (χ ∘ sel) ∧ ∀ j, sel j ≠ i₀`.
  The route-(a) exclusion-steered companion of the free engine; BOT-2′ consumes it. Carrier-agnostic.
- **Leaf BOT-2** (23f, prior commit): `exists_finCard_linearIndependent_selection` (`Rank.lean`, top-level before
  `namespace Matrix`) — the free index basis-pick engine: `(χ : ι → V) [Finite ι] {N} (hrank : finrank (span
  (range χ)) = N) : ∃ sel : Fin N → ι, Function.Injective sel ∧ LinearIndependent (χ ∘ sel)`. The indexed,
  fixed-cardinality companion of `exists_linearIndependent'` (a basis of the spanned *proper* submodule). PLUS the
  candidate-level bridge `BodyHingeFramework.bottom_selection_of_crossFramework_span` (`Concrete.lean`, after
  `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`): `(F ends hgp) {v a} {m₂}[Fintype] (F₂)
  (hspan_id : span (range a-shifted-FULL-family) = span F₂.rigidityRows) (hfr : finrank (span F₂.rigidityRows) =
  card m₂) (hbot2_all : ∀ e, (ends e.1).2 ≠ v) : ∃ re hbot2 hbot1, finrank (span (a-shifted family ∘ re)) = card m₂`
  — EXACTLY the consumer's `(re, hbot2, hbot1, hrank)`. `[Finite β]`, NOT `[Fintype α]`.
- **Leaf R1** (23f, prior commit): `BodyHingeFramework.span_range_hingeRow_crossFramework_eq_rigidityRows_of_off`
  (`Basic.lean`, after BOT-1) — the dispatch-ready discharge of the bridge's `hspan_id`. Sig: `(F₁ F₂) {ι} (ends₁)
  (P : {e // e ∈ E(F₁)} → Prop) (remap : {e // P e} → {e // e ∈ E(F₂)}) (hremap_surj) (B) (hspan : ∀ e : {e // P e},
  span (range (B e.1)) = F₂.hingeRowBlock (remap e)) (hlink₁ : ∀ e : {e // P e}, F₂.IsLink (remap e).1 (ends₁ e.1.1).1
  (ends₁ e.1.1).2) (hoff : ∀ e, ¬P e → ∀ i, hingeRow (ends₁ e.1).1 (ends₁ e.1).2 (B e i) = 0) : span (range FULL-family)
  = span F₂.rigidityRows`. Folds the restricted-edge variant + the zero-`e_a` drop into ONE lemma; `le_antisymm`
  (the `≤` branch routes a `P`-row into `F₂` and an off-`P` row via `hoff` to `0 ∈ span`; `≥` is BOT-1's section
  transfer over the `P`-subtype). Produces the bridge's `hspan_id` shape directly (compile-checked spike, removed).
  PLUS `hingeRow_self` (`@[simp]`, `hingeRow a a r = 0`, after `hingeRow_apply`) — the `e_a` row the dispatch's `hoff`
  cites. Carrier/coordinatization-agnostic.
- **Leaf BOT-1** (23f): `BodyHingeFramework.span_range_hingeRow_crossFramework_eq_rigidityRows` (`Basic.lean`, after
  the L-span leaf) — the abstract cross-framework spanning identity (`F₁ F₂`, `remap` over the FULL `E(F₁)` surjective,
  `hspan`/`hlink₁`). Span SET-equality, `le_antisymm` + a `remap`-section. **NOT instantiable over the full `E(G)`
  family** (`e_a`'s a-shift breaks `hlink₁`, §(4.60.B)); the dispatch uses R1 (above) instead. Stays in tree as the
  unrestricted abstract form.
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
free basis-pick engine + the candidate-level bridge) + **R1** (the restricted-edge cross-framework variant + the
zero-`e_a` drop) + the **avoiding-engine** + **BOT-2′** (the exclusion-steered candidate bridge) + **BOT-4** (the
`Sum.elim` assembly `cornerRowInjection_sumElim_injective`, this commit, axiom-clean) are COMPLETE — the RE strict
injection `re`/`hre` is now fully assembled, and HMEQ rides on mathlib `Matrix.fromBlocks_toBlocks`. Owed → the
wrapper's carried block-read hyps: **HA** (next) `(A−L₀C).row` LI via leaf (iii) `corner_hA_zero₁₂_of_gate` + the
entrywise `hAeq` (compose `…_apply_corner` with `Lrow`'s `cGv`-subtraction) + the gate `hρe₀`; then **HB** (`hmem`
per-`B`-row span facts, fed BOT-3′), **HD** (`D.row` LI, mixedBottom + the bridge's `hrank`) → the dispatch wires
`case_III_arm_realization_rowOp` (consuming the bridge fed R1's `hspan_id`; the concrete
`remap`/`hspan`/`hlink₁`/`hoff`/`hred`/`havoid`/`hbot_ne_ea` land here where `Q`/`Gab`/`e₀` are bound) → (3c) gate
bridge → the dispatch + CHAIN-5. All matrix-backbone leaves + BOT-3′ + BOT-1 + BOT-2 + R1 + the avoiding-engine +
BOT-2′ + BOT-4 are in-tree, axiom-clean. On the dispatch landing → 23g (ENTRY) → 23h (ASSEMBLY).

## Decisions made during this phase

### Phase-local choices and proof techniques

- **BOT-4 is the carrier-agnostic `Sum.elim` assembly; the two `hdisj` collisions become carried hyps the dispatch
  discharges.** `cornerRowInjection_sumElim_injective` (`Concrete.lean` A5d) builds `re`/`hre` exactly the §(4.57.D)
  shape: `Function.Injective.sumElim ((cornerRowInjection_injective hne j₀).comp finScrewDimSplitCorner.injective)
  hbotinj hdisj`, with `hdisj` split on the corner index (`rcases finScrewDimSplitCorner c with j | u`; one `simp only
  [..., cornerRowInjection, Sum.elim_inl/_inr]` per case reduces the corner read to `(e_a, j)` / `(e_b, j₀)`). Rather
  than hard-wire BOT-2′'s outputs, the lemma carries the two collision facts as hypotheses — `havoid : ∀ i, bottom i ≠
  (e_b, j₀)` (BOT-2′) and `hbot_ne_ea : ∀ i, (bottom i).1 ≠ e_a` (`hingeRow_self`: the `e_a` row is zero, never in an
  LI pick) — keeping it framework-agnostic and reusable. HMEQ needs no lemma: mathlib `Matrix.fromBlocks_toBlocks
  _).symm` applied at the dispatch. Axiom-clean; no friction (a clean `sumElim` + `rcases`/`simp only`).
- **The `(e_b, j₀)` collision needs EXCLUSION-steering, not a free pick — `hred` IS HB; BOT-2′ wraps it.** The
  corner's `±r` slot `(e_b, j₀)` is pickable by the free BOT-2 pick (nonzero `R(Gab)` row), breaking `re` injectivity
  (B1/B2 need `hre`). Fix = exclude it; the redundancy `hred` (the `(e_b,j₀)` row ∈ `span(others)`) is literally HB
  (`B = L₀·D`), grounded in W6b's `hingeRow a b ρ₀ ∈ span R(Gv)`. The engine
  `exists_finCard_linearIndependent_selection_avoiding` (`Rank.lean`) + the candidate bridge
  `bottom_selection_of_crossFramework_span_avoiding` (**BOT-2′**, `Concrete.lean`, this commit) land it — a
  near-mechanical mirror of BOT-2 threading `p₀`/`hred`, emitting `havoid : ∀ i, re i ≠ p₀` for BOT-4's `hdisj` (`hred`
  defeq against the `set χ` abbreviation). Recon: design §(4.61), partly overturns §(4.58)/§(4.60)'s "free pick". No
  friction.
- **R1 folds the restricted-edge variant + the zero-`e_a` drop into ONE lemma, discharging the bridge's `hspan_id`
  directly.** `span_range_hingeRow_crossFramework_eq_rigidityRows_of_off` (`Basic.lean`) quantifies the
  cross-framework matching (`remap` surjective, `hspan`, `hlink₁`) over the genuine `{e // P e}` (the `Gv`-edges +
  `e_b`) and takes a separate `hoff` discharging the corner `e_a`'s degenerate `(a,a)` row to the **zero** functional
  — so the FULL family span = `span F₂.rigidityRows`. The `≤` branch splits on `P`: a `P`-row routes into `F₂` via
  `hlink₁`+`hspan`, an off-`P` row via `hoff` to `0 ∈ span`; `≥` is BOT-1's `remap`-section transfer over the
  `P`-subtype. Verified to produce the bridge's `hspan_id` shape by a compile-checked spike (instantiate `ends₁ :=
  if (ends e).1 = v then a else …`, `B := blockBasisOn`; matched `bottom_selection_of_crossFramework_span`'s argument
  exactly), then removed (the concrete `remap`/`hspan`/`hlink₁`/`hoff` land at the dispatch, item 4). Supporting
  `hingeRow_self` (`@[simp]`, `hingeRow a a r = 0`): the `e_a`-row vanishing the dispatch's `hoff` cites. Axiom-clean.
- **BOT-2 is a FREE basis-pick in two pieces.** The engine `exists_finCard_linearIndependent_selection` (`Rank.lean`)
  extracts an injective `Fin N → ι` index selection from `finrank (span (range χ)) = N` (the indexed companion of
  `exists_linearIndependent'`; `κ`-finiteness forces a basis-of-submodule detour, FRICTION Open entry). The bridge
  `bottom_selection_of_crossFramework_span` (`Concrete.lean`) wires the FULL-`p` `hspan_id` + the def-0 count +
  `hbot2_all` to the wrapper's `(re, hbot2, hbot1, hrank)`: `hbot1` the excluded-middle TAUTOLOGY, `hrank` =
  `finrank_span_eq_card` of the LI pick, the pick never lands on `e_a` (`hingeRow a a = 0`). The `hspan_id` is
  discharged by R1 (above). Both BOT-2 lemmas axiom-clean.
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
- **Leaf (iv) `hblock` reducer (bijection special case, SUPERSEDED by B2).**
  `reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂` (`Rank.lean`) is the bijection-only `hblock` backbone (takes
  `re := ⇑e` for `e : (m₁⊕m₂) ≃ p`, splits via `submatrix_mul_equiv`); does NOT serve the strict-injection arm
  (§(4.55)). Zero-caller orphan, phase-close cleanup item; carrier/field-agnostic, no friction.
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
- **Leaf (ii) unit-det reindex (bijection special case, SUPERSEDED by B1).** `reindex_rowOp_isUnit_det` carries
  the row op as `Matrix.reindex e e [1,−L₀;0,1]` on `p` for a BIJECTION `e : (m₁⊕m₂) ≃ p` (det a unit via
  `det_reindex_self` + `rowOp_isUnit_det`); does NOT serve the strict-injection arm (`card m₁+card m₂ ≤ card p`
  is an inequality, no `e` exists in general — §(4.55)). Zero-caller orphan, phase-close cleanup item;
  carrier/field-agnostic, no friction.
- **Leaf (i) stated carrier/framework-agnostic, not arm-coupled.** `matrix_eq_mul_of_dual_row_comb` is the
  pure matrix-algebra `B = L₀·D` core: it takes abstract dual functionals `φ`/`χ`, a matching `μ`, weights
  `cGv`, and a single-body-column index `cols`, and produces `B = Matrix.of w · D` for `of_eq_mul_of_row_comb`.
  All the arm-coupling (the `Gv.IsLink`→`re`-image membership that builds `μ`; matching `φ` to the corner read
  `_apply_eB_off_pin` and `χ` to the `mixedBottom` block) is deferred to the assembly — keeping the genuinely-
  new content (the `cGv`→`w` fiberwise re-key via `Finset.sum_fiberwise`) separable and reusable. Proof is one
  `of_eq_mul_of_row_comb` + `LinearMap.sum_apply`/`smul_apply` + `Finset.sum_fiberwise`/`sum_mul`; no friction.
  `[DecidableEq α]` added for `Pi.single` (standard requirement, not an API gap).
