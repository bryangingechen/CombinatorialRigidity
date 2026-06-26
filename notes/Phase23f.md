# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress. Opened 2026-06-26 as the *fifth* CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d +
23e + 23f). 23e landed the KT-faithful A3-transposed rank certificate + its LA scaffolding axiom-clean
(`notes/Phase23e.md`); 23f builds the **geometry arm** that *constructs* the cert's block data from the
IH-fed `cGv` widening, then the candidate-matching gate bridge and the general-`k` chain dispatch + CHAIN-5.
**Phase 23 stays in progress.** The authoritative recon is `notes/Phase23-design.md` §(4.54) (the re-pointed
hand-off, the three-leaf geometry-arm plan, the framework-vs-arm split, the both-block coupling). Program map:
`notes/MolecularConjecture.md`.

## Current state

**Next concrete commit = leaf (iii), the post-row-op corner-`hA` bridge.** Leaf (ii) — the `Lrow`-on-`p`
reindex unit-det bridge — LANDED axiom-clean: `Matrix.reindex_rowOp_isUnit_det` (`Rank.lean`, after
`rowOp_isUnit_det`) gives `IsUnit (Matrix.reindex e e (fromBlocks 1 (-L₀) 0 1)).det` for any equivalence
`e : (m₁ ⊕ m₂) ≃ p`, via the mathlib `Matrix.det_reindex_self` + the landed `rowOp_isUnit_det`. This is the
unit-det `Lrow` the cert threads on the full edge index `p := {e // e ∈ E(G)} × Fin (screwDim k − 1)`: the
row op is the `m₁ ⊕ m₂` block elementary matrix, but `re` is an *injection* (drops the `D−2` surplus `v`-rows),
so `submatrix_mul` cannot split the product through it; carrying `Lrow` as `reindex e e [1,-L₀;0,1]` lives on
`p` and `re` selects the block rows back out. Carrier/field-agnostic; `m₁`/`m₂` carry `[Finite]` (only `p` is
type-relevant), `Fintype.ofFinite` recovers the proof-side instances. STILL OWED at the assembly (deferred
there, as designed): the choice of `e` packaging the `re`-image rows + the surplus, and the `L₀ := cGv`-weights.

Leaf (i) — the `cGv`→`w` re-key — landed earlier (axiom-clean): `BodyHingeFramework.matrix_eq_mul_of_dual_row_comb`
(`Concrete.lean`, the "A6 — the corner's off-`v` block `B` factors as `L₀ · D`" section) turns the W6b functional
combination `hingeRow a b ρ = ∑ⱼ cGv j • hingeRow (uvGv j) (vvGv j) (rvGv j)` (each summand matched via `μ` to a
bottom row `χ (μ j)`) into the matrix product `B = Matrix.of w · D` (`w i i' = ∑_{μ i ·=i'} cGv i j`), feeding
`of_eq_mul_of_row_comb`. RANK-route weight, no span-`∈` (the §(4.44) wall does not reform).

The cert `case_III_rank_certification_zero₁₂` (landed 23e) is end-to-end SATISFIABLE for the real interior
arm; 23f constructs its `(Lrow, hLrow, U, hU, re, en, hblock, hA, hD)` block data. The single arm-coupling is
`L₀` (= the `cGv` weights, now re-keyed by leaf (i)) — `cGv` is a conclusion of the IH-fed W6b producer
`exists_candidateRow_bottomRows_of_rigidOn` (`Candidate.lean:401`, takes `hrig : IsInfinitesimallyRigidOn Gab`
+ `h622lb`), NOT derivable from `caseIIICandidate`'s abstract `G`/`ends`/`e_a`/`e_b`/`v`. The `re`/`m₂` split
is by contrast FRAMEWORK-determined (the corner/bottom predicates reference only `ends`/`v`/`a`/`e_a`/`e_b`).
Nothing is mid-stream; tree clean. `d=3` stays fully green (zero-regression, hard constraint).

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

The geometry arm (3 new leaves + assembly), then the gate bridge, then the dispatch. Per design §(4.54).

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
  mathlib `Matrix.det_reindex_self` + the landed `rowOp_isUnit_det`. The cert's `Lrow : Matrix p p ℝ` is on the
  full edge index `p := {e // e ∈ E(G)} × Fin (screwDim k − 1) ≠ m₁ ⊕ m₂` (the `re` injection DROPS the `D−2`
  surplus `v`-rows; `submatrix_mul` does NOT split through the *injection* `re` — it needs a bijective middle
  index — so the row op lives on `p` and is selected by `re`). Carrier/field-agnostic; `m₁`/`m₂` carry
  `[Finite]` (only `p` is type-relevant), `Fintype.ofFinite` recovers the proof-side instances. STILL OWED at
  the assembly: the `e` packaging the `re`-image + surplus rows, and `L₀ := cGv`-weights.
- [ ] **(iii) post-row-op corner-`hA` bridge** (genuinely-new) — after the op the cert's `A = A' = A − L₀C`;
  `C`'s `e_b`-fill pin row (`.1 = v`, NOT pin-zero) gets `cGv`-subtracted from the corner `±r` pin row, turning
  `blockBasisOn(e_b, j₀)` into `ρ₀`. Read `A' = toBlocks₁₁(Lrow*M*U)` as the `[blockBasisOn(e_a); ρ₀]`
  coordinate matrix, close via the landed `corner_hA'_of_gate`. The landed
  `linearIndependent_toBlocks₁₁_row_of_corner_gate` reads the *un*-row-op'd corner, so it does NOT serve here —
  a new bridge reading `A'` is owed.
- [ ] **assemble `hblock`/`hA`** — `hblock` from (i)+(ii) + `rowOp_zeroes_upperRight`-on-`p` + the
  `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` bottom + `…_submatrix_toBlocks₂₁` lower-left (the `_zero₁₂`
  shape's `C`/`D`); `hA` from (iii). `hD` from the `mixedBottom` family
  (`linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`, conditional on the IH `hrank`); cardinalities
  already compose (`columnSplit_corner_card = screwDim k`). Fire `case_III_rank_certification_zero₁₂`.
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

**Next concrete commit = leaf (iii), the post-row-op corner-`hA` bridge** (geometry leaf (iii) above) —
after the row op the cert's `A = A' = A − L₀C`; `C`'s `e_b`-fill pin row (`.1 = v`, NOT pin-zero) gets
`cGv`-subtracted from the corner `±r` pin row, turning `blockBasisOn(e_b, j₀)` into `ρ₀`. Read
`A' = toBlocks₁₁(Lrow*M*U)` as the `[blockBasisOn(e_a); ρ₀]` coordinate matrix, close via the landed
`corner_hA'_of_gate` (`Concrete.lean:620`). The landed `linearIndependent_toBlocks₁₁_row_of_corner_gate` reads
the *un*-row-op'd corner, so it does NOT serve here — a new bridge reading `A'` is owed. Then the `hblock`/`hA`
assembly (fire `case_III_rank_certification_zero₁₂`), then item 3c (candidate-matching gate bridge), then item 4
(dispatch + CHAIN-5). On the dispatch landing, the CHAIN layer closes and ENTRY (**23g**) opens; ASSEMBLY is
**23h**. (Leaf (ii), `reindex_rowOp_isUnit_det`, landed this commit; leaf (i),
`matrix_eq_mul_of_dual_row_comb`, landed earlier.)

**What is in-tree (cite directly — axiom-clean):**
- **Leaf (ii)** (23f, this commit): `Matrix.reindex_rowOp_isUnit_det` (`Rank.lean`, after `rowOp_isUnit_det`) —
  the `Lrow`-on-`p` reindex unit-det bridge `IsUnit (Matrix.reindex e e (fromBlocks 1 (−L₀) 0 1)).det` for
  `e : (m₁ ⊕ m₂) ≃ p`, via `Matrix.det_reindex_self` + `rowOp_isUnit_det`; carrier/field-agnostic.
- **Leaf (i)** (23f, earlier): `BodyHingeFramework.matrix_eq_mul_of_dual_row_comb` (`Concrete.lean`, the
  "A6 — the corner's off-`v` block `B` factors as `L₀ · D`" section) — the `cGv`→`w` re-key feeding
  `of_eq_mul_of_row_comb`; carrier/framework-agnostic (abstract `φ`/`χ`/`μ`/`cGv`/`cols`).
- The reshaped A3-transposed cert chain (23e): `rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` (`Rank.lean`),
  `finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks_zero₁₂` (`Concrete.lean`),
  `case_III_rank_certification_zero₁₂` (`Candidate.lean`), all consuming `(Lrow, hLrow, U, hU, …, hblock, …)`.
- The row-op LA facts `rowOp_isUnit_det` + `rowOp_zeroes_upperRight` (`Rank.lean`); the matrix-algebra half
  `Matrix.of_eq_mul_of_row_comb` (`Rank.lean`); the mathlib `rank_mul_eq_right_of_isUnit_det` +
  `det_reindex_self`.
- `corner_hA'_of_gate` (`Concrete.lean:620`, the ρ₀-augmented family — its consumer is leaf (iii)'s post-op
  corner `hA`); `exists_corner_blockBasisOn_linearIndependent` (`Concrete.lean:566`, the un-op'd
  `[blockBasisOn(e_a); blockBasisOn(e_b,j₀)]` family — the alternative shape, NOT used on the row-op route).
- The union-dimension discriminator + `exists_shared_redundancy_and_matched_candidate` (Phase 23c).
- The `mixedBottom` family + `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` (`Concrete.lean:1685`,
  supplies `hD`, includes the `e_b`-fill row); `rigidityMatrixEdge_mul_columnOp_apply_pin_zero` (the LOWER-left
  pin-zero — `Gv` rows only); the operated-entry bricks `…_apply_corner`/`_apply_eB_off_pin`/`_apply_off_pin`.
- The `cGv` widening (W6b producer `exists_candidateRow_bottomRows_of_rigidOn`, `Candidate.lean:401`;
  `chainData_split_w6b_gates`, `Realization.lean:825`–831).
- The interior arm wrapper `chainData_arm_realization_sep` (`CaseIII/Realization.lean`) — parks here until the
  sound cert is wired through; it carries the disjoint-block obligations as hypotheses.

**STILL TO BUILD (all 23f):** geometry leaf (iii) + `hblock`/`hA` assembly → (3c) candidate-matching
gate bridge → the dispatch + CHAIN-5. **NOT** "assembly, no new math" — leaf (iii) is genuinely-new
tracked content (design §(4.54)). Leaves (i) (`matrix_eq_mul_of_dual_row_comb`, `Concrete.lean`) and (ii)
(`reindex_rowOp_isUnit_det`, `Rank.lean`) are in-tree, axiom-clean. On the dispatch landing → 23g (ENTRY) →
23h (ASSEMBLY).

## Decisions made during this phase

### Phase-local choices and proof techniques

- **Leaf (ii) reindexes the row op onto `p`, not through `re`.** `reindex_rowOp_isUnit_det` carries the row op
  as `Matrix.reindex e e [1,−L₀;0,1]` on the full edge index `p` (`e : (m₁⊕m₂) ≃ p`), then proves its det a
  unit by `Matrix.det_reindex_self` + the landed `rowOp_isUnit_det`. The cert's `re` is an *injection* (drops
  the `D−2` surplus `v`-rows), so the alternative — left-multiplying a row op living on `m₁⊕m₂` and splitting
  via `submatrix_mul` — is unavailable (`submatrix_mul` needs a bijective middle index). Carrier/field-agnostic,
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
