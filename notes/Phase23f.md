# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress. Opened 2026-06-26 as the *fifth* CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d +
23e + 23f). 23e landed the KT-faithful A3-transposed rank certificate + its LA scaffolding axiom-clean
(`notes/Phase23e.md`); 23f builds the **geometry arm** that *constructs* the cert's block data from the
IH-fed `cGv` widening, then the candidate-matching gate bridge and the general-`k` chain dispatch + CHAIN-5.
**Phase 23 stays in progress.** The authoritative recon is `notes/Phase23-design.md` §(4.54) (the re-pointed
hand-off, the three-leaf geometry-arm plan, the framework-vs-arm split, the both-block coupling). Program map:
`notes/MolecularConjecture.md`.

## Current state

**Next concrete commit = the framework-level cert-firing wrapper.** The matrix-algebra backbone is COMPLETE:
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

**The wrapper (still owed, all framework-level wiring):** supply the strict injection `re` (corner `e_a`-panel
+ `±r` slot, and the `mixedBottom` Gv / `a`-shifted-`e_b` bottom, into disjoint `p`-rows), `M' =
rigidityMatrixEdge * U`, `hM'` (`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` bottom +
`…_submatrix_toBlocks₂₁_eq_zero` lower-left + operated-corner entrywise reads for `toBlocks₁₁`/`toBlocks₁₂`),
`L₀ := cGv`-weights (leaf (i)); obtain `Lrow`/`hLrow`/`hLsub`/`hzero` from **B1**, `hblock` from **B2**,
`hA` (leaf (iii)'s `hAeq` = operated `±r` row reads `ρ₀`), `hD` (`mixedBottom`,
`linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`, conditional on the IH `hrank`); cardinalities
compose (`columnSplit_corner_card = screwDim k`). Fires `case_III_rank_certification_zero₁₂`. Then item 3c
(gate bridge), item 4 (dispatch + CHAIN-5).

The cert `case_III_rank_certification_zero₁₂` (landed 23e) is end-to-end SATISFIABLE for the real interior
arm — **via the strict-injection `re`** (§(4.55); its rank step is `rank_submatrix_le`, which never needs `re`
surjective). 23f now has the full `(Lrow, hLrow, U, hU, re, en, hblock, hA, hD)` matrix backbone in-tree; the
wrapper builds the *block data* (`Lrow`/`hblock` from the strict-injection siblings B1/B2, NOT the superseded
bijection leaves (ii)/(iv)). The single arm-coupling is `L₀` (= the `cGv` weights, re-keyed by leaf (i)) —
`cGv` is a conclusion of the IH-fed W6b producer `exists_candidateRow_bottomRows_of_rigidOn`
(`Candidate.lean:401`, takes `hrig : IsInfinitesimallyRigidOn Gab` + `h622lb`), NOT derivable from
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

The geometry arm: leaves (i)–(iv) landed (but (ii)/(iv) serve only the bijection sub-case — see the §(4.55)
recon), then the strict-injection siblings B1/B2 (landed this commit, the general-arm replacements), then the
cert-firing assembly, the gate bridge, the dispatch. Per design §(4.54)/§(4.55).

- [x] **(i) `cGv`→`w` re-key leaf** — DONE (axiom-clean), `BodyHingeFramework.matrix_eq_mul_of_dual_row_comb`
  (`Concrete.lean`). Carrier-agnostic / framework-agnostic matrix-algebra core: turns a per-row dual-functional
  combination `φ i = ∑ⱼ cGv i j • χ (μ i j)` (matched via `μ` to bottom functionals `χ`), pushed through the
  single-body-column reads `φ ↦ φ (Pi.single (cols x).1 (finScrewBasis k (cols x).2))` that build both `B` and
  `D`, into `B = Matrix.of w · D` (`w i i' = ∑_{μ i ·=i'} cGv i j`, `Finset.sum_fiberwise`), feeding
  `of_eq_mul_of_row_comb`. RANK-route weight, NOT a span-`∈`, so the §(4.44) `hbotmem` wall does not reform.
  STILL OWED at the assembly (deferred there, as designed): the `Gv.IsLink`→`re`-image membership that
  produces the matching `μ` and the `φ`/`χ` matching to the corner read (`_apply_eB_off_pin`) and the
  `mixedBottom` block.
- [x] **(ii) `Lrow`-on-`p` reindex unit-det bridge** — DONE (axiom-clean), `Matrix.reindex_rowOp_isUnit_det`
  (`Rank.lean`). `IsUnit (Matrix.reindex e e (fromBlocks 1 (−L₀) 0 1)).det` for any `e : (m₁ ⊕ m₂) ≃ p`, via the
  mathlib `Matrix.det_reindex_self` + the landed `rowOp_isUnit_det`. The cert's `Lrow : Matrix p p ℝ` lives on
  the full edge index `p := {e // e ∈ E(G)} × Fin (screwDim k − 1)`; the lemma reindexes the `m₁⊕m₂` block
  elementary matrix onto `p` by `e : (m₁⊕m₂) ≃ p` (a **bijection** — `det_reindex_self` needs one). Carrier/
  field-agnostic; `m₁`/`m₂` carry `[Finite]` (only `p` is type-relevant), `Fintype.ofFinite` recovers the
  proof-side instances. **`re` shape SETTLED = strict INJECTION (§(4.55)), so this BIJECTION lemma does NOT
  serve the general arm:** `card m₁+card m₂ ≤ card p` is an inequality (not forced `=`), so no `e : (m₁⊕m₂) ≃ p`
  exists in general. SUPERSEDED by owed leaf **B1** (the strict-injection unit-det / rank-invariance bridge: a
  unit-det `Lrow` on `p` that is the block op on `range re` + identity on the complement, built via the
  EXTENDED equiv `e' : (m₁⊕m₂) ⊕ (p∖range re) ≃ p`). This lemma is the bijection special case B1 subsumes.
- [x] **(iii) post-row-op corner-`hA` bridge** — DONE (axiom-clean), `BodyHingeFramework.corner_hA_zero₁₂_of_gate`
  (`Concrete.lean`, after `corner_hA'_of_gate`). Produces `LinearIndependent ℝ A.row` for the cert's operated
  top-left block `A = toBlocks₁₁(Lrow*M*U)`, given the entrywise read `hAeq` that the operated corner reads the
  `D`-member family `[blockBasisOn(e_a,·); ρ₀]` under the corner-index split `em₁ : m₁ ≃ Fin (screwDim k − 1) ⊕ Unit`
  (the operated `±r` row is `ρ₀`, KT (6.66), NOT a `blockBasisOn`, so the un-op'd
  `linearIndependent_toBlocks₁₁_row_of_corner_gate` does NOT serve). Re-wrap via
  `Matrix.linearIndependent_row_of_coordEquiv` + close via `corner_hA'_of_gate` reindexed by `em₁`
  (`LinearIndependent.comp`). Carrier/coordinatization-agnostic. STILL OWED at the assembly: the entrywise `hAeq`
  (operated-entry bricks composed with `Lrow`'s `cGv`-weights) and the `em₁`/`coordEquiv` packaging.
- [x] **(iv) `hblock` reduction matrix backbone** — DONE (axiom-clean),
  `Matrix.reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂` (`Rank.lean`, after `of_eq_mul_of_row_comb`). The pure
  matrix-algebra composition of leaf (ii)'s `Lrow := reindex e e [1,−L₀;0,1]`-on-`p` shape with
  `rowOp_zeroes_upperRight`: from `e : (m₁⊕m₂) ≃ p`, the column-op'd block read
  `hM' : M'.submatrix e en = fromBlocks A B C D`, and leaf (i)'s `hB : B = L₀·D`, yields the cert's `hblock`
  shape `(Lrow * M').submatrix e en = fromBlocks (A − L₀C) 0 C D` with `re := ⇑e`. Proof:
  `submatrix_mul_equiv` through the middle `e` (collapses `Lrow.submatrix e e` to `[1,−L₀;0,1]`,
  `e.symm ∘ e = id`) + `hM'` + `rowOp_zeroes_upperRight`. Carrier/field-agnostic; no friction (the only adjust
  was the standing `Finite`+`Fintype.ofFinite` `unusedFintypeInType` fix on `m₁`). **NOTE (§(4.55)): this fixes
  a BIJECTION `e`, so it does NOT serve the general arm (the `re` shape is a strict injection — no `Equiv` to
  split `submatrix_mul_equiv` through). SUPERSEDED by owed leaf B2 (the strict-injection `hblock` reducer,
  splitting through the EXTENDED equiv `e' : (m₁⊕m₂) ⊕ (p∖range re) ≃ p`); this lemma is the bijection special
  case B2 subsumes.**
- [x] **(recon) settle the bijection-vs-injection `re` shape** — DONE (verdict = **(b) strict injection**;
  design §(4.55), compiler-checked recon session #40). The grounded relation is `card m₁ + card m₂ =
  D·(|V(G)|−1) ≤ (D−1)·|E(G)| = card p`, an **inequality** (`rank_matroidMG_of_isKDof_zero` + `rk_le_card`,
  `Operations.lean:882`); **equality is NOT stated** and a minimal-0-dof graph is not forced `(D,D)`-tight, so
  `card m₁+card m₂ < card p` is generic. Hence NO bijection `(m₁⊕m₂) ≃ p` in general — **leaves (ii)/(iv) (which
  fix a bijection, `re := ⇑e`) do NOT serve**; a strict injection (always exists, `card ≤ card`) is the real
  shape. Owed genuinely-new (next): **B1** strict-injection unit-det / rank-invariance bridge + **B2**
  strict-injection `hblock` reducer (sigs in §(4.55) / *Current state*; leaf (iv)'s `submatrix_mul_equiv` needs
  a bijective middle index, absent here). Leaves (i)/(iii) unaffected.
- [x] **(B1) strict-injection unit-det / rank-invariance bridge** — DONE (axiom-clean),
  `Matrix.exists_rowOp_of_strictInjection` (`Rank.lean`, after
  `reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂`). Given `re : m₁⊕m₂ → p` injective and the `m₁⊕m₂` block op
  `[1,−L₀;0,1]`, produces `∃ Lrow : Matrix p p ℝ`, `IsUnit Lrow.det`, `Lrow.submatrix re re = [1,−L₀;0,1]`,
  **and** the off-image vanishing `∀ i x, x ∉ range re → Lrow (re i) x = 0` (the structural fact B2 uses to
  split the product). Built via the EXTENDED equiv `e' : (m₁⊕m₂) ⊕ ↥(range re)ᶜ ≃ p` (`Equiv.ofInjective re` +
  `Equiv.Set.sumCompl`) and `Lrow := reindex e' e' (fromBlocks [1,−L₀;0,1] 0 0 1)`. Rank invariance is NOT
  exported (the cert derives it from `IsUnit Lrow.det` via `rank_mul_eq_right_of_isUnit_det`). Subsumes leaf
  (ii) (the bijection special case). Carrier/field-agnostic; `m₁`/`m₂` carry `[Finite]` (`Fintype.ofFinite` in
  proof). STILL OWED at the wrapper: the strict `re` construction + `L₀ := cGv`-weights.
- [x] **(B2) strict-injection `hblock` reducer** — DONE (axiom-clean),
  `Matrix.rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂` (`Rank.lean`, after B1). The `_zero₁₂` analogue
  of leaf (iv) for B1's `Lrow`: takes `Lrow` + B1's two structural facts (`hLsub : Lrow.submatrix re re =
  [1,−L₀;0,1]`, `hzero : off-image vanishing`) + `hM' : M'.submatrix re en = fromBlocks A B C D` + leaf-(i)
  `hB : B = L₀*D`, concludes `(Lrow * M').submatrix re en = fromBlocks (A − L₀C) 0 C D`. Splits the product
  *entrywise* by `Fintype.sum_of_injective` (off-image columns vanish by `hzero`; image columns reindex by `re`
  with `Lrow (re i) (re k) = [1,−L₀;0,1] i k` from `hLsub`) → `[1,−L₀;0,1] * M'.submatrix re en`, then `hM'` +
  `rowOp_zeroes_upperRight L₀ hB`. NO `Equiv` split (no bijective middle index exists). Subsumes leaf (iv).
  `m₂` stays `[Fintype]` (the `L₀ * D` matrix-mul is in the statement type, FRICTION:125/QUIRKS §64); `m₁` is
  `[Finite]`.
- [ ] **assemble `hblock`/`hA` (the framework-level cert-firing wrapper)** — build `M' = rigidityMatrixEdge * U`
  (the column-op'd matrix), supply the strict injection `re` (corner `e_a`-panel + `±r` slot, and the
  `mixedBottom` Gv / `a`-shifted-`e_b` bottom, into disjoint `p`-rows), `hM'` (the `fromBlocks` block read:
  `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` bottom + `…_submatrix_toBlocks₂₁_eq_zero` lower-left + the
  operated-corner entrywise reads for `toBlocks₁₁`/`toBlocks₁₂`) into **B2** with `L₀ := cGv`-weights via leaf
  (i) and `Lrow` from **B1**; `hA` via leaf (iii) (`hAeq` = operated `±r` row reads `ρ₀`), `hD` from the
  `mixedBottom` family (`linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`, conditional on the IH
  `hrank`); cardinalities compose (`columnSplit_corner_card = screwDim k`). Fire
  `case_III_rank_certification_zero₁₂`.
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
- **GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive) — orthogonal to the cert;
  tracked separately, lands with 23f/the spine.
- **Build against the literal product, not the component leaves** (the §(4.46)/(4.54) lesson, twice-burned).
  When building `hblock`/`hA`, instantiate the cert's `(Lrow * M * U).submatrix re en` literally and trace
  the goals — the two elided leaves ((ii)/(iii)) surfaced only when the §(4.54) spike did this end-to-end.
- **Downstream (23g+):** ENTRY's `exists_chain_data_of_noRigid` reshape + floor lift + OD-1, then ASSEMBLY.
  The frozen contract (C.5/C.6) is invariant; none touches 23e's cert. ENTRY is parallel-safe.

## Hand-off / next phase

**Next concrete commit = the framework-level cert-firing wrapper.** B1/B2 (the strict-injection matrix backbone)
landed this commit, axiom-clean; the matrix-algebra layer of the geometry arm is now COMPLETE. The wrapper is
pure framework-level composition: supply the strict injection `re` (corner `e_a`-panel + `±r` slot, and the
`mixedBottom` Gv / `a`-shifted-`e_b` bottom, into disjoint `p`-rows — built from the corner/bottom predicates,
FRAMEWORK-determined), `M' = rigidityMatrixEdge * U`, the block read `hM'`
(`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` bottom + `…_submatrix_toBlocks₂₁_eq_zero` lower-left +
operated-corner entrywise reads for `toBlocks₁₁`/`toBlocks₁₂`), the `L₀ := cGv`-weights (leaf (i)) / `en`
packaging; obtain `⟨Lrow, hLrow, hLsub, hzero⟩` from **B1** (`exists_rowOp_of_strictInjection`), `hblock` from
**B2** (`rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂`, fed `hLsub`/`hzero`/`hM'`/`hB`), `hA` from leaf
(iii) (`corner_hA_zero₁₂_of_gate`, `hAeq` = operated `±r` row reads `ρ₀`), `hD` from the `mixedBottom` family
(`linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`, conditional on the IH `hrank`); cardinalities
compose (`columnSplit_corner_card = screwDim k`). Fire `case_III_rank_certification_zero₁₂`. Then item 3c (gate
bridge), item 4 (dispatch + CHAIN-5). On the dispatch landing, the CHAIN layer closes and ENTRY (**23g**) opens;
ASSEMBLY is **23h**.

The arm's `re` is SETTLED = **strict injection** (§(4.55); `card m₁ + card m₂ ≤ card p` is an inequality, so no
bijection exists in general). B1/B2 are the strict-injection replacements for the superseded bijection leaves
(ii)/(iv); the wrapper rides on B1/B2, not on (ii)/(iv).

**What is in-tree (cite directly — axiom-clean):**
- **Leaf B1** (23f, this commit): `Matrix.exists_rowOp_of_strictInjection` (`Rank.lean`, after
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

**STILL TO BUILD (all 23f):** the matrix-algebra backbone is COMPLETE (B1/B2 landed this commit, axiom-clean) →
the framework-level cert-firing wrapper (supply the strict `re`, build `M'`/`hM'`, the `en`/`L₀ := cGv`
packaging, fire `case_III_rank_certification_zero₁₂` via B2 + B1 + leaves (i)/(iii)) → (3c) candidate-matching
gate bridge → the dispatch + CHAIN-5. All six matrix-backbone leaves ((i) `matrix_eq_mul_of_dual_row_comb`,
(ii) `reindex_rowOp_isUnit_det`, (iii) `corner_hA_zero₁₂_of_gate`, (iv)
`reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂`, **(B1) `exists_rowOp_of_strictInjection`, (B2)
`rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂`**) are in-tree, axiom-clean. (ii)/(iv) fix a bijection
`e : (m₁⊕m₂) ≃ p` (the measure-zero isostatic-tight case); B1/B2 are the strict-injection siblings the general
arm rides on and subsume (ii)/(iv). The wrapper itself is framework-level composition (still-owed wiring: the
strict `re`, the entrywise `hM'`/`hAeq` reads, the `em₁` packaging, the `L₀ := cGv`-weights). On the dispatch
landing → 23g (ENTRY) → 23h (ASSEMBLY).

## Decisions made during this phase

### Phase-local choices and proof techniques

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
