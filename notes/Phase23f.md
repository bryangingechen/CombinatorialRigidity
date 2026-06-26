# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress. Opened 2026-06-26 as the *fifth* CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d +
23e + 23f). 23e landed the KT-faithful A3-transposed rank certificate + its LA scaffolding axiom-clean
(`notes/Phase23e.md`); 23f builds the **geometry arm** that *constructs* the cert's block data from the
IH-fed `cGv` widening, then the candidate-matching gate bridge and the general-`k` chain dispatch + CHAIN-5.
**Phase 23 stays in progress.** The authoritative recon is `notes/Phase23-design.md` §(4.54) (the re-pointed
hand-off, the three-leaf geometry-arm plan, the framework-vs-arm split, the both-block coupling). Program map:
`notes/MolecularConjecture.md`.

## Current state

**⚠ Next concrete commit = GROUND the cert's `re` shape (a recon/design-pass), THEN the wrapper.** All four
matrix-backbone leaves are in-tree axiom-clean (checklist (i)–(iv) below); the remaining 23f Lean work is the
framework-level wrapper that builds `M' = rigidityMatrixEdge * U`, supplies the `fromBlocks` block read `hM'`
(`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` bottom + `…_submatrix_toBlocks₂₁_eq_zero` lower-left + the
operated-corner entrywise reads for `toBlocks₁₁`/`toBlocks₁₂`), the `L₀ := cGv`/`e`/`en` packaging, `hA` (leaf
(iii)'s `hAeq` = operated `±r` row `= ρ₀`), `hD` (`mixedBottom`, conditional on the IH `hrank`), and fires
`case_III_rank_certification_zero₁₂`. **But this is NOT yet plumbing** — there is one open shape question to
settle first, by reading (not building):

**The bijection-vs-injection `re` reconciliation (OPEN — recon before the wrapper build).** Leaves (ii) and
(iv) both fix `e : (m₁⊕m₂) ≃ p` a **bijection** with `re := ⇑e` — forced by `det_reindex_self` /
`submatrix_mul_equiv`, which need a *bijective* middle index — so they certify `card m₁ + card m₂ = |p| ≤
M.rank`, i.e. FULL edge-row rank with `m₂` absorbing every non-corner row. But the design / earlier leaf-(ii)
prose describes the arm's `re` as a strict **injection dropping the `D−2` surplus `v`-rows** (a weaker,
sub-`|p|` bound). The cert's `re : m₁⊕m₂ → p` is a *general function* (Rank.lean:517; the rank step is
`rank_submatrix_le`), so both type-check — but only one is the real arm's shape, and the landed leaves serve
ONLY the bijection. Read the real arm's intended `re`/`m₂`/`hD` (against the cert signature + the §(4.54)
spike) and decide:
- **(a) bijection** — `m₂` absorbs the surplus rows; then `hD` must show the FULL bottom block (incl. surplus)
  is row-LI — confirm the `mixedBottom` family covers them (NOT obvious: the surplus rows are precisely what KT
  drops). Leaves (ii)/(iv) then serve as-is and the wrapper IS the wiring.
- **(b) strict injection** — `re` drops the surplus; then leaves (ii)/(iv) do NOT serve (a bijection can't drop
  rows), and a strict-injection `hblock` reducer + unit-det bridge are **genuinely-new owed leaves** (no
  `submatrix_mul`/`det` split through a non-bijective `re`). A P≈3 design+build, not plumbing.

This is a read-and-decide recon, NOT a build; the landed leaves (i)–(iv) are correct generic lemmas either way
(see the checklist for each). Then item 3c (gate bridge), item 4 (dispatch + CHAIN-5).

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
  mathlib `Matrix.det_reindex_self` + the landed `rowOp_isUnit_det`. The cert's `Lrow : Matrix p p ℝ` lives on
  the full edge index `p := {e // e ∈ E(G)} × Fin (screwDim k − 1)`; the lemma reindexes the `m₁⊕m₂` block
  elementary matrix onto `p` by `e : (m₁⊕m₂) ≃ p` (a **bijection** — `det_reindex_self` needs one). Carrier/
  field-agnostic; `m₁`/`m₂` carry `[Finite]` (only `p` is type-relevant), `Fintype.ofFinite` recovers the
  proof-side instances. **Open at the wrapper (Current state):** whether the arm fires the cert with this
  bijection `re := ⇑e` (`m₂` absorbing the `D−2` surplus rows) or a strict injection that drops them — the
  bijection lemma serves only the former; the latter owes a new strict-injection bridge. STILL OWED: the
  `e`/`m₂` packaging + `L₀ := cGv`-weights (after the `re` shape is settled).
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
  was the standing `Finite`+`Fintype.ofFinite` `unusedFintypeInType` fix on `m₁`).
- [ ] **(recon) settle the bijection-vs-injection `re` shape** — read-and-decide pass (see *Current state*):
  does the arm fire the cert with `re := ⇑e` a bijection (`m₂` absorbs the `D−2` surplus, `hD` covers the full
  bottom) or a strict injection (drops surplus → leaves (ii)/(iv) don't serve, a strict-injection bridge is
  owed)? Settle this against the cert signature + the §(4.54) spike BEFORE the wrapper build.
- [ ] **assemble `hblock`/`hA` (the framework-level cert-firing wrapper)** — build `M' = rigidityMatrixEdge * U`
  (the column-op'd matrix), supply `hM'` (the `fromBlocks` block read: `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`
  bottom + `…_submatrix_toBlocks₂₁_eq_zero` lower-left + the operated-corner entrywise reads for
  `toBlocks₁₁`/`toBlocks₁₂`) into `reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂` with `L₀ := cGv`-weights via leaf
  (i); `hA` via leaf (iii) (`hAeq` = operated `±r` row reads `ρ₀`), `hD` from the `mixedBottom` family
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

**Next concrete commit = a recon/design-pass settling the bijection-vs-injection `re` shape** (full statement
in *Current state*), THEN the framework-level cert-firing wrapper. All four matrix-backbone leaves are in-tree
axiom-clean — (i) `matrix_eq_mul_of_dual_row_comb`, (ii) `reindex_rowOp_isUnit_det`, (iii)
`corner_hA_zero₁₂_of_gate`, (iv) `reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂` — but leaves (ii)/(iv) fix
`e : (m₁⊕m₂) ≃ p` a **bijection** (`re := ⇑e`), while the design describes the arm's `re` as a strict injection
dropping the `D−2` surplus rows, and the landed leaves serve only the bijection. **Read the real arm's intended
`re`/`m₂`/`hD` first (recon, not build):** if bijection, the wrapper is wiring — build `M' = rigidityMatrixEdge
* U`, the block read `hM'` (`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` bottom + `…_submatrix_toBlocks₂₁_eq_zero`
lower-left + operated-corner entrywise reads for `toBlocks₁₁`/`toBlocks₁₂`), the `L₀:=cGv`/`e`/`en` packaging,
and fire `case_III_rank_certification_zero₁₂` with `hA` (leaf (iii)'s `hAeq`) / `hD` (`mixedBottom`, conditional
on the IH `hrank`); cardinalities compose (`columnSplit_corner_card = screwDim k`). If strict injection, a
strict-injection `hblock` reducer + unit-det bridge are genuinely-new owed leaves (P≈3, no `submatrix_mul`/`det`
split through a non-bijective `re`). Then item 3c (gate bridge), item 4 (dispatch + CHAIN-5). On the dispatch
landing, the CHAIN layer closes and ENTRY (**23g**) opens; ASSEMBLY is **23h**.

**What is in-tree (cite directly — axiom-clean):**
- **Leaf (iv)** (23f, this commit): `Matrix.reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂` (`Rank.lean`, after
  `of_eq_mul_of_row_comb`) — the `hblock` reduction matrix backbone: composes leaf (ii)'s
  `Lrow := reindex e e [1,−L₀;0,1]`-on-`p` shape with `rowOp_zeroes_upperRight`, taking `hM' : M'.submatrix e en
  = fromBlocks A B C D` (the column-op'd block read) + `hB : B = L₀·D` (leaf (i)) to the cert's `hblock`
  `(Lrow * M').submatrix e en = fromBlocks (A − L₀C) 0 C D` (`re := ⇑e`). Via `submatrix_mul_equiv` +
  `rowOp_zeroes_upperRight`. Carrier/field-agnostic.
- **Leaf (iii)** (23f): `BodyHingeFramework.corner_hA_zero₁₂_of_gate` (`Concrete.lean`, after
  `corner_hA'_of_gate`) — the post-row-op corner-`hA` bridge: `LinearIndependent ℝ A.row` for the cert's
  operated `A = toBlocks₁₁(Lrow*M*U)`, from the entrywise read `hAeq` (operated corner = coordinate matrix of
  `[blockBasisOn(e_a,·); ρ₀]` reindexed by `em₁ : m₁ ≃ Fin (screwDim k − 1) ⊕ Unit`) + the gate `hρe₀`, via
  `Matrix.linearIndependent_row_of_coordEquiv` + `corner_hA'_of_gate`.`comp`. Carrier/coordinatization-agnostic.
- **Leaf (ii)** (23f): `Matrix.reindex_rowOp_isUnit_det` (`Rank.lean`, after `rowOp_isUnit_det`) —
  the `Lrow`-on-`p` reindex unit-det bridge `IsUnit (Matrix.reindex e e (fromBlocks 1 (−L₀) 0 1)).det` for
  `e : (m₁ ⊕ m₂) ≃ p`, via `Matrix.det_reindex_self` + `rowOp_isUnit_det`; carrier/field-agnostic.
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

**STILL TO BUILD (all 23f):** settle the bijection-vs-injection `re` shape (recon — see *Current state*) → the
framework-level cert-firing wrapper (build `M'`/`hM'`, the `e`/`en`/`L₀ := cGv` packaging, fire
`case_III_rank_certification_zero₁₂` via the `hblock` reducer + leaves (i)/(iii)) → (3c) candidate-matching gate
bridge → the dispatch + CHAIN-5. All four matrix-backbone leaves ((i) `matrix_eq_mul_of_dual_row_comb`, (ii)
`reindex_rowOp_isUnit_det`, (iii) `corner_hA_zero₁₂_of_gate`, (iv) `reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂`)
are in-tree, axiom-clean — **no new matrix-algebra owed IF the arm fires with the bijection `re := ⇑e`**; if it
needs a strict-injection `re` (drops the `D−2` surplus), a strict-injection `hblock` reducer + unit-det bridge
are genuinely-new owed leaves. The wrapper itself is framework-level composition (still-owed wiring: the
entrywise `hM'`/`hAeq` reads, the `e`/`em₁` packaging, the `L₀ := cGv`-weights). On the dispatch landing → 23g
(ENTRY) → 23h (ASSEMBLY).

## Decisions made during this phase

### Phase-local choices and proof techniques

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
  index, so the op is reindexed onto `p` by the bijection `e` instead.) **Whether the arm's `re` is this
  bijection `⇑e` (`m₂` absorbing the `D−2` surplus rows) or a strict injection that drops them is OPEN
  (Current state); the bijection lemma serves only the former.** Carrier/field-agnostic,
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
