# Phase 23d — Case III general `d`: the CHAIN rank-certification reconsideration (work log)

**Status:** in progress (opened 2026-06-24 at a user-adjudicated clean-break close of 23c, at the
member-mapping-wall STOP). **Phase 23 stays in progress**; 23d is the third CHAIN-layer sub-phase
(CHAIN spans 23b + 23c + 23d, design §3). ENTRY + ASSEMBLY are later sub-phases (codes). The full
23d route history — every wall + verdict — lives in `notes/Phase23-design.md` §I.8.24(4.18)–(4.30);
program map `notes/MolecularConjecture.md`; the 23c landed-leaf inventory is `notes/Phase23c.md`.

**What 23d is.** 23c built option (A) (the `±r`-block rank-cert engine) end-to-end + closed the
interior-`hρe₀` conjecture-crux, but the general-`d` rank cert hit the `hρGv` member-mapping wall. 23d
reconsiders the rank cert. The genuine-row base-block family (route B, route 4-bare, route 4-splitOff)
was built/scoped and **all walled on the same obstruction**: the wrap edge `edge i` content cannot
enter the corner-overridden `caseIIICandidate` span — the discriminator gate `ρ₀ ⊥̸ C(vᵢ₊₁, n')` is
**intrinsic to the slot-override, invariant under base-block re-targeting** (4 wall appearances,
§(4.18)–(4.29)). So the user chose **route A** — the honest unconditional concrete-`Matrix` Theorem 5.5.
All landed leaves stay in tree (sound in isolation; the route-B/4 inventory is reusable or harmless).
`d=3` stays fully green throughout.

## Current state

**✅ ROUTE A is the plan; A1+A2 (de-risk) + A3 (block-additivity kernel) + A4 (the (6.61) column-op
bridge) + A4.5 (product-column matrix) + A5a (column-op-as-right-multiply) + now A5b (the gate
re-wrap) are LANDED + gate-verified.** A1+A2: `Molecular/RigidityMatrix/Concrete.lean` (2026-06-24,
opacity CLEAN — the §(4.30) one-residual concern is RESOLVED). A3 (2026-06-24,
`Mathlib/LinearAlgebra/Matrix/Rank.lean`): `Matrix.rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows`
— KT eq. (6.64)'s block-triangular additivity as a *pure-`Matrix`* inequality, never forming a span
membership (the §(4.18)–(4.30) wall). A4 (2026-06-24, build/lint/warning/axiom-clean) — the column-op
half of the §(4.30) A4 leaf:
- `Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks` (`Rank.lean`, carrier-agnostic): the A4→A3 bridge —
  for any `M`, a *unit-det* column-op matrix `U`, and reindexing equivs `em`/`en` exhibiting `M * U` in
  the `fromBlocks A B 0 D` block-triangular shape with LI diagonal-block rows, `#m₁ + #m₂ ≤ M.rank`. One
  `calc`: A3 ⟹ `rank_reindex` ⟹ `rank_mul_eq_left_of_isUnit_det`. This is the matrix realization of KT's
  "(6.61) submatrix containment is not difficult to see" — a *right-multiply by a unit-det matrix*, NEVER
  a span membership, so the override-meets-gate collision never arises.
- `BodyHingeFramework.rigidityMatrix_mul_rank` (`Concrete.lean`): the rigidity specialization —
  `(rigidityMatrix * U).rank = rigidityMatrix.rank` for `IsUnit U.det`.

**✅ A4.5 LANDED (2026-06-24, `Concrete.lean`, build/lint/warning/axiom-clean)** — the re-coordinatization
the A5 spike (design §I.8.24(4.31)) found `hblock`'s `D×D` corner split needs (the flat `rigidityMatrix`'s
arbitrary `Module.finBasis` columns don't factor `α × Fin D`). Landed:
- **the generalization** `Matrix.rank_of_coordEquiv` — the carrier-agnostic rank bridge over ANY
  coordinatizing `coordEquiv : Dual ℝ M ≃ₗ[ℝ] (κ → ℝ)`; the old `Matrix.rank_of_dualCoord` is now its
  one-line flat instance, and `rigidityMatrix_rank` + the clause-(iii) capstone stay green unchanged (no
  orphan, no duplication — the coordinator's refactor).
- **A4.5a** `finScrewBasis` (the `Fin D`-indexed `ScrewSpace` basis; renamed off `screwBasis` to dodge a
  namespace clash with `PanelLayer.screwBasis`, the powerset-indexed one — FRICTION + TACTICS-QUIRKS §65);
  **A4.5b** `dualProductCoordEquiv` (`Dual ℝ (α → ScrewSpace k) ≃ₗ (α × Fin D → ℝ)`); **A4.5c**
  `BodyHingeFramework.rigidityMatrixProd : Matrix (β × Fin (D−1)) (α × Fin D) ℝ`.
- **A4.5d** `rigidityMatrixProd_rank` + `rigidityMatrixProd_rank_eq_finrank_span_rigidityRows` — the
  product matrix's `Matrix.rank` = `finrank (span rigidityRows)`, the honest target, via
  `Matrix.rank_of_coordEquiv` + the shared `span_range_rigidityRowFun` (no `ScrewSpace` unfolding).

**✅ A5a LANDED (2026-06-24, `Concrete.lean`, build/lint/warning/axiom-clean)** — the (6.61)
column-op-as-right-multiply on the product matrix:
- `prodColumnOpEquiv Φ := dualProductCoordEquiv.symm.trans (Φ.symm.dualMap.trans dualProductCoordEquiv)`
  (`[Fintype α]`): the coordinatized column-op equiv on `α × Fin D → ℝ`, for ANY primal column-op
  automorphism `Φ : (α → ScrewSpace k) ≃ₗ[ℝ] (α → ScrewSpace k)` (KT's `columnOp` is one).
- `prodColumnOpEquiv_transpose_toMatrix'_det_isUnit` (`[Fintype α] [DecidableEq α]`):
  `IsUnit ((toMatrix' (prodColumnOpEquiv Φ))ᵀ).det` (the A4/A3 unit-det right-multiply input;
  PROBE-2c shape `det_transpose` + `IsUnit.of_mul_eq_one … ; ← det_mul ; ← toMatrix'_comp ; simp`).
- `BodyHingeFramework.rigidityMatrixProd_mul_columnOp_row` (`[Fintype α] [DecidableEq α]`): the row
  identity `(rigidityMatrixProd F ends hgp * U).row p = dualProductCoordEquiv (Φ.symm.dualMap
  (rigidityRowFun p))` — the right-multiply precomposes every rigidity-row functional with `Φ`.
  PROBE-4 proof: `change`-to-`vecMul` defeq + `vecMul_transpose` + `toMatrix'_mulVec` + the
  `.trans`/`symm_apply_apply` unfold (FRICTION: `(M*Uᵀ).row` needs `change`, not `mul_apply'`).
  No `ScrewSpace` unfolding anywhere — the span-membership wall never forms.

**✅ A5b LANDED (2026-06-24, `Concrete.lean`, build/lint/warning/axiom-clean)** — the gate re-wrap,
the `LinearIndependent (·.row)` form the A3/A4 bridge's `hA`/`hD` consume:
- `Matrix.linearIndependent_row_of_coordEquiv` (carrier-agnostic): for ANY coordinatizing
  `coordEquiv : Dual ℝ M ≃ₗ (κ → ℝ)`, `LinearIndependent ℝ (Matrix.of (coordEquiv ∘ w)).row ↔
  LinearIndependent ℝ w`. One-line: `LinearMap.linearIndependent_iff coordEquiv coordEquiv.ker`
  (rows are `⇑coordEquiv ∘ w` defeq; a `LinearEquiv`'s kernel is `⊥`). The LI sibling of
  `Matrix.rank_of_coordEquiv` — no `ScrewSpace` unfolding.
- `BodyHingeFramework.linearIndependent_rigidityMatrixProd_row_iff` (the rigidity specialization,
  `coordEquiv := dualProductCoordEquiv` instance): `LinearIndependent ℝ (rigidityMatrixProd ends
  hgp).row ↔ LinearIndependent ℝ (rigidityRowFun ends hgp)`. So the A5c arm reads the corner/bottom
  blocks' row-LI off `rigidityMatrixProd` (or its column-op image) and discharges from the landed
  dual-space facts (`exists_independent_rigidityRows_of_edge` + `omitTwoExtensor_linearIndependent`).

**✅ A5c-keystone LANDED (2026-06-24, `Concrete.lean`, build/lint/warning/axiom-clean)** — the two
entrywise facts the `hblock` block-fill reads:
- `dualProductCoordEquiv_apply` (`[Fintype α] [DecidableEq α]`): the keystone entrywise identity
  `dualProductCoordEquiv φ (body, j) = φ (Pi.single body (finScrewBasis k j))` (PROBE 5; pure
  `Basis.dualBasis_equivFun` + `Pi.basis_apply`). Proved with `simp only` not `rw` — the def froze a
  `Classical.decEq` on its `Σ`-index, so `rw` of the dual-basis API hits an instance-defeq mismatch
  against the ambient `[DecidableEq α]` (TACTICS-QUIRKS § 66, new).
- `BodyHingeFramework.rigidityMatrixProd_apply_eq_zero_of_ne` (`[Fintype α]`, `classical` in body):
  the (6.61) lower-left **zero block made entrywise-visible** — `rigidityMatrixProd p (body, c) = 0`
  whenever `body ≠ (ends p.1).1` and `body ≠ (ends p.1).2` (the single-body screw lands on neither
  endpoint, so `hingeRow … (S u − S v) = r (0 − 0) = 0`). NO span argument; NO `ScrewSpace` unfold.
- The owed **doc-comment fix landed**: the flat `rigidityMatrix`/`rigidityMatrix_mul_rank` prose now
  states the flat column index is an *arbitrary* `finBasis` (dimension `D·|V|`, not the literal
  product `α × Fin D`), pointing at `rigidityMatrixProd` for the form whose columns factor `α × Fin D`.

**Still OPEN:** the **A5c-assembly** — construct the `em`/`en` reindexing (the product split `en :
(α × Fin D) ≃ ({vᵢ₊₁} × Fin D) ⊕ rest` from the chain geometry) and prove `(rigidityMatrixProd *
U).reindex em en = fromBlocks Mᵢ B 0 (R(G₁,q₁))` via the two landed entrywise facts (the `0` block is
`rigidityMatrixProd_apply_eq_zero_of_ne` post-`U`; the diagonal blocks are read off
`rigidityMatrixProd_mul_columnOp_row`), wiring the corner/bottom block-row LI through the A5b iff
`linearIndependent_rigidityMatrixProd_row_iff` into A3/A4's `hA`/`hD`. Then **A6** (dispatch+spine).
The A5c-assembly is the part needing the chain-data geometry (`Φ = columnOp`, the specific `vᵢ₊₁`
split), so it naturally folds toward A6.

**What landed (A1 + A2, axiom-clean):**
- **A1 — `BodyHingeFramework.rigidityMatrix`**: `R(G,p)` as a literal
  `Matrix (β × Fin (D−1)) (Fin (finrank ℝ (Dual ℝ (α → ScrewSpace k)))) ℝ` — the `(e,j)`-row is the
  `dualCoordEquiv`-coordinate vector of `hingeRow (ends e).1 (ends e).2 (blockBasis hgp e j)`, with
  `blockBasis` a basis of the `(D−1)`-dim hinge-row block. The `(edge,j)↔hingeRow` correspondence is
  `rigidityMatrix_row` (`rfl`). KT's `(D−1)|E| × D|V|` matrix made literal.
- **A2 — the rank bridge**: `Matrix.rank_of_dualCoord` (carrier-AGNOSTIC core), its rigidity
  specialization `rigidityMatrix_rank`, and the **clause-(iii) capstone**
  `rigidityMatrix_rank_eq_finrank_span_rigidityRows`: `(rigidityMatrix ends hgp).rank =
  finrank (span F.rigidityRows)` — lands on the HONEST `HasGenericFullRankRealization` target
  (`PanelHinge.lean:1035`), NOT a weaker matrix fact; the A1→target link is `span_range_rigidityRowFun`.
- **The opacity finding (the de-risk's point):** the bridge runs entirely through
  `Module.finBasis`/`Basis.equivFun`/`LinearEquiv.finrank_map_eq` — opaque `ScrewSpace` (Phase 22l) is
  **never unfolded**; `Matrix.rank_eq_finrank_span_row` fires with zero detour.

**Remaining leaf count (post-A5c-keystone, ≈2–3.5):** A5c-assembly (the `em`/`en` split + the
`fromBlocks` reindex, now reading the two landed entrywise facts) ~1–1.5; A6 (dispatch+spine) ~1–2.
Per-leaf signatures + bankable SORRY-FREE fragments: design §I.8.24(4.31)(4).

## Remaining work in Phase 23

1. **The general-`d` rank certification — route A (concrete `Matrix`).** ✅ A1+A2+A3+A4+A4.5+A5a+A5b
   landed; ✅ **A5c-keystone** landed (`Concrete.lean`: `dualProductCoordEquiv_apply` the entrywise
   identity + `BodyHingeFramework.rigidityMatrixProd_apply_eq_zero_of_ne` the (6.61) zero-block made
   entrywise-visible; + the owed flat-matrix doc-comment fix). OPEN: **A5c-assembly** (the `em`/`en`
   product split + the `fromBlocks` reindex, reading the two landed entrywise facts; **NEXT**) → **A6**
   (dispatch+spine). The route-B/4 dual-space leaves + the chain cert
   `case_III_rank_certification_chain` stay in tree (sound in isolation — the dual-space approach the
   wall closed; do not build on them). The interior-`hρe₀` crux is CLOSED.
2. **CHAIN-2c-iii `chainData_dispatch`** — the general-`k` `Fin cd.d` router (base/`d=3` via
   `chainData_split_realization`; interior `2 ≤ i < d` via the route-A arm). The `ChainData`
   interior-split accessors are landed and reusable: `removeVertex_isLink_edge_succ_pred_off`
   (`Induction/Operations.lean`, the off-slot input), the interior-`hρe₀` chain
   `interior_hρe₀_of_baseWidening`/`_of_widening` (`CaseIII/Relabel/ForkedArm.lean`, the dispatch reads
   `hρe₀` off LEAF-3's `hedgeGv` in one call), and LEAF-3
   `exists_shared_redundancy_and_matched_candidate` (`CaseIII/Realization.lean`, re-exposes `hedgeGv`).
   Folds into A6. GAP 2: the `ends`-orientation pins need a `Function.update` override (LEAF-3's
   `ends = Q.ends` is only orientation-free).
3. **CHAIN-5** — wire the dispatch into the spine to discharge `hdispatch`.
4. **ENTRY** *(parallel-safe; own sub-phase when minted)* — reshape `Graph.exists_chain_data_of_noRigid`
   (`Reduction.lean:383`) to the `G.ChainData n` producer `exists_chainData_of_noRigid` (KT Lemma 4.6
   chain + Lemma 4.8 split-off, general `d`); lift the `6 ≤ bodyBarDim n` floor; resolve the chain/cycle
   dichotomy (OD-1, KT Lemma 4.6 / Lemma 5.4). Consumer: `case_III_hsplit_producer_all_k`
   (`Arms.lean:777`). The CHAIN↔ENTRY contract is frozen (below).
5. **ASSEMBLY** — compose the honest general-`d` Theorem 5.5, re-green `prop:rigidity-matrix-prop11` +
   `hub`, derive Thm 5.6, state Conjecture 1.2.

**Contract/motive note.** No C.0–C.6/motive change is forced (§I.8.21 confirmed). Route A re-shapes the
rank cert + arm realization only — not the dispatch's `hdispatch` consume-shape (C.3), the `ChainData`
record (C.1), or the 0-dof motive/IH.

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

## Hand-off / next phase

**✅ Route A on track; A1+A2+A3+A4+A4.5+A5a+A5b + the A5c-keystone LANDED (`Concrete.lean` +
`Rank.lean`). NEXT CONCRETE COMMIT = A5c-assembly — the `em`/`en` product split + the `fromBlocks`
reindex** of `(rigidityMatrixProd * U).reindex em en = fromBlocks Mᵢ B 0 (R(G₁,q₁))`, reading the two
landed entrywise facts (`rigidityMatrixProd_apply_eq_zero_of_ne` for the `0` block post-`U`,
`rigidityMatrixProd_mul_columnOp_row` for the diagonal blocks), and discharging the corner/bottom
block-row LI through the A5b iff `linearIndependent_rigidityMatrixProd_row_iff`. This is the part that
needs the chain-data geometry (`Φ = columnOp`, the specific `vᵢ₊₁` split), so it folds toward A6.
The A5c-keystone just landed: `dualProductCoordEquiv_apply` (`= φ (Pi.single body (finScrewBasis k
j))`; PROBE 5) + `rigidityMatrixProd_apply_eq_zero_of_ne` (the (6.61) zero block, entrywise) +
the owed flat-matrix doc-comment fix (*Current state* has the inventory). After A5c-assembly: A6
(dispatch+spine — fire `Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks (rigidityMatrixProd …) U hU
em en hblock hA hD`, bridge via `rigidityMatrixProd_rank_eq_finrank_span_rigidityRows`, route the
`Fin cd.d` arms), then ENTRY + ASSEMBLY (parallel-safe). **No motive/IH change, no phase-direction
decision owed** (within route A).

**The route-A build should open as its own sub-phase at the next phase-open** (A1–A4.5 confirm route A
on track; the A5–A6 layer plan is in *Current state* + §(4.31); the new Lean lives in
`Molecular/RigidityMatrix/Concrete.lean` + the upstream-eligible `Mathlib/LinearAlgebra/Matrix/Rank.lean`
+ further `RigidityMatrix/` files). Route (C) (honest-conditional — carry the rank-cert obligation as one
explicit hypothesis, ~1 leaf + wiring, gap = KT's own (6.61) "not difficult to see") is the documented
fallback only if route A later walls.

**Do NOT re-attempt** the closed genuine-row base-block routes (B, 4-bare, 4-splitOff) or the dual-space
rank-cert variants — the wall (the discriminator gate intrinsic to the `caseIIICandidate` slot-override)
is kernel-confirmed across all of them (§(4.18)–(4.29)); route A escapes via the literal-`Matrix` model
(where KT's (6.61) is a column-op equality, never a span membership), not by re-targeting the base block.

## Decisions made during this phase

*(Fresh at open. The 23c landed-leaf inventory + wall-characterization is the settled archive in
`notes/Phase23c.md`; the full 23d route history — every wall, spike, and verdict — is
`notes/Phase23-design.md` §I.8.24(4.18)–(4.30). This section keeps the live route-A decisions + one
compressed history verdict; the per-leaf landed-route-B descriptions are in git + the design doc.)*

- **A5c-keystone LANDED — the entrywise facts the `hblock` block-fill reads (2026-06-24,
  `Concrete.lean`, build/lint/warning/axiom-clean).** Two decls + the owed doc-fix:
  `dualProductCoordEquiv_apply` (the PROBE-5 keystone `dualProductCoordEquiv φ (body, j) =
  φ (Pi.single body (finScrewBasis k j))`; pure `Basis.dualBasis_equivFun` + `Pi.basis_apply`) and
  `BodyHingeFramework.rigidityMatrixProd_apply_eq_zero_of_ne` (the (6.61) lower-left **zero block
  entrywise-visible** — the entry vanishes off the edge's endpoints, `r (0 − 0) = 0`, NO span argument,
  NO `ScrewSpace` unfold). The keystone forced `simp only` not `rw` (the def froze a `Classical.decEq`
  on its `Σ`-index → instance-defeq mismatch with ambient `[DecidableEq α]`; new TACTICS-QUIRKS § 66 +
  FRICTION). Came in under the ~1.5–2.5-leaf A5c estimate because it is just the entrywise *content*;
  the `em`/`en` split + `fromBlocks` reindex (the A5c-assembly) needs the chain-data geometry and folds
  toward A6. NEXT = A5c-assembly.
- **A5b LANDED — the gate re-wrap (`LinearIndependent (·.row)` for the A3/A4 `hA`/`hD`) (2026-06-24,
  `Concrete.lean`, build/lint/warning/axiom-clean).** Two decls: `Matrix.linearIndependent_row_of_coordEquiv`
  (carrier-agnostic: for ANY `coordEquiv : Dual ℝ M ≃ₗ (κ → ℝ)`,
  `LinearIndependent ℝ (Matrix.of (coordEquiv ∘ w)).row ↔ LinearIndependent ℝ w`; one-liner
  `LinearMap.linearIndependent_iff coordEquiv coordEquiv.ker`, the LI sibling of
  `Matrix.rank_of_coordEquiv`) + `BodyHingeFramework.linearIndependent_rigidityMatrixProd_row_iff` (the
  `coordEquiv := dualProductCoordEquiv` instance). No `ScrewSpace` unfolding (the re-wrap stays at the
  `LinearEquiv` boundary, kernel `⊥`). Came in well under the ~1–2-leaf estimate — the iff is the whole
  content; the corner-block full-rank *content* (`exists_independent_rigidityRows_of_edge` +
  `omitTwoExtensor_linearIndependent`) is consumed *by A5c* via this iff, not re-derived here. NEXT = A5c.
- **A5a LANDED — the (6.61) column-op-as-right-multiply on the product matrix (2026-06-24,
  `Concrete.lean`, build/lint/warning/axiom-clean).** Three decls: `prodColumnOpEquiv Φ` (the
  coordinatized column-op equiv = `Φ.symm.dualMap` conjugated by `dualProductCoordEquiv`),
  `prodColumnOpEquiv_transpose_toMatrix'_det_isUnit` (`IsUnit ((toMatrix' (prodColumnOpEquiv Φ))ᵀ).det`,
  the A4/A3 unit-det right-multiply input), and `rigidityMatrixProd_mul_columnOp_row` (the row identity:
  `· * U` precomposes each rigidity-row functional with `Φ`). Generic in `Φ` — KT's `columnOp` is one
  such, so A5a never references `columnOp`. All carrier-agnostic (no `ScrewSpace` unfold); the
  span-membership wall never forms. PROBE-2c/4 fragments landed verbatim. NEXT = A5b (gate re-wrap).
- **A4.5 LANDED — the product-column rigidity matrix + the generalized rank bridge (2026-06-24,
  `Concrete.lean`, build/lint/warning/axiom-clean).** Generalized `Matrix.rank_of_dualCoord` →
  `Matrix.rank_of_coordEquiv` (any coordinatizing `Dual ℝ M ≃ₗ (κ → ℝ)`); the old name is its flat
  instance, and `rigidityMatrix_rank` + the capstone stay green (no orphan/dup — coordinator's refactor).
  Added `finScrewBasis` / `dualProductCoordEquiv` / `BodyHingeFramework.rigidityMatrixProd : Matrix
  (β × Fin (D−1)) (α × Fin D) ℝ` + its honest-rank bridges `rigidityMatrixProd_rank`(`_eq_finrank_span
  _rigidityRows`), all one-line instances of the generalized lemma + the shared `span_range_rigidityRowFun`.
  The `screwBasis` name was taken (powerset-indexed, `PanelLayer.lean`) → renamed `finScrewBasis`
  (FRICTION + TACTICS-QUIRKS §65: single-file build hides the clash, `lake lint` catches it). NEXT = A5a.
- **A5 ROUTE-COMPOSITION SPIKE (2026-06-24, design §I.8.24(4.31)).** Verdict (now LANDED as A4.5): the flat
  `rigidityMatrix`'s arbitrary `finBasis` columns don't factor `α × Fin D`, so `hblock`'s `D×D` split needs
  the product matrix; the (6.61) column op IS a unit-det right-multiply over a coordinatized matrix (route
  A's escape holds, never a span membership). 5 probes SORRY-FREE. Exact A5/A6 signatures → design §(4.31).
- **A4 LANDED — the (6.61) column-op bridge into A3 (2026-06-24, build/lint/warning/axiom-clean).**
  Two composing lemmas: `Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks` (`Rank.lean`,
  carrier-agnostic — `hblock : (M*U).reindex em en = fromBlocks A B 0 D` + LI diagonal rows ⟹
  `#m₁+#m₂ ≤ M.rank`, one `calc`: A3 ⟹ `rank_reindex` ⟹ `rank_mul_eq_left_of_isUnit_det`) +
  `BodyHingeFramework.rigidityMatrix_mul_rank` (`Concrete.lean`, the rigidity specialization of the
  column op). This is KT's "(6.61) submatrix containment, not difficult to see" realized as a
  *unit-det right-multiply* (rank-invariant), NEVER a span membership — why route A escapes the wall.
  Scope finding: the rank-invariance/bridge *plumbing* is A4; the entrywise *construction* of the
  specific `U` + its `fromBlocks` reindexing needs the chain-data geometry, so it folds into A5 (which
  supplies `hblock`'s blocks). § 64 (Fintype-in-signature) recurred but is fully covered — `m₁/m₂`
  appear in the goal's `Fintype.card`, so `[Fintype]`; `p/n₁/n₂` only in hyps, so `[Finite]`+`ofFinite`.
- **A3 LANDED — the (6.64) block-additivity kernel as a pure-`Matrix` inequality (2026-06-24,
  `Mathlib/LinearAlgebra/Matrix/Rank.lean`, build/lint/warning/axiom-clean).**
  `Matrix.rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows`: `fromBlocks A B 0 D` with `A`,`D` rows
  each LI ⟹ `#m₁+#m₂ ≤ rank`. Stated in the LI-rows form the realization arm supplies (full-rank `D×D`
  corner + full-row-rank IH bottom-block) — so the general-rank → LI-rows row-subset extraction is
  *unneeded*, and the lemma collapses to: combined `(m₁⊕m₂)`-square minor is block-triangular ⟹
  `det = det·det ≠ 0` (`det_fromBlocks_zero₂₁`) ⟹ LI rows ⟹ `rank = #m₁+#m₂`, then `rank_submatrix_le`.
  Came in at ~1 clean leaf (vs §(4.30)'s 2–3 estimate). It is route A's analog of
  `finrank_add_card_le_of_linearIndependent_mkQ` but forms **no span membership** — why route A
  dissolves the §(4.18)–(4.30) wall (a literal block-matrix fact, not a dual-space containment).
- **A1+A2 de-risk LANDED — opacity CLEAN (2026-06-24, `Concrete.lean`, build/lint/warning/axiom-clean).**
  A1 (`rigidityMatrix` + `rigidityMatrix_row`) + A2 (`Matrix.rank_of_dualCoord` carrier-agnostic,
  `rigidityMatrix_rank`, the clause-(iii) capstone `rigidityMatrix_rank_eq_finrank_span_rigidityRows` on
  the honest `finrank (span rigidityRows)`, `span_range_rigidityRowFun`). The §(4.30) residual RESOLVED:
  the bridge runs through `Basis`/`LinearEquiv`, never unfolding opaque `ScrewSpace`;
  `Matrix.rank_eq_finrank_span_row` fires zero-detour. Sharpened cost ≈7–11 (A4 the column-op now the
  outlier). Lesson (the carrier-agnostic A2 bridge is WHY opacity is a non-issue) → Findings.
- **Route A CHOSEN by the user (2026-06-24), with cost data.** After the genuine-row base-block family
  closed (4 walls, §(4.18)–(4.29)) and route A was scoped FEASIBLE-but-HEAVY (§(4.30), ~9–14-leaf
  sub-phase), the user chose route A (the honest unconditional `Matrix`-model Thm 5.5) over the cheap
  honest-conditional (C). Execution: A1+A2 `d=3` de-risk landed (above); next A3; open route A as its own
  sub-phase. (C) demoted to documented fallback. Lesson (the 4-wall saga + the verify-first wins) →
  Findings.
- **Route A SCOPED — FEASIBLE but HEAVY, genuinely ≠ the refuted §(4.22)/(4.23) work (§(4.30)).** §(4.22)/
  (4.23) refuted option (i) (abstract span-block-rank — landed as
  `finrank_add_card_le_of_linearIndependent_mkQ`, the chain cert's kernel, walling on span MEMBERSHIP);
  route A is option (ii) (a literal mathlib `Matrix R(G,p)`) where KT's (6.61) submatrix-containment is an
  entrywise column-op equality (`Matrix.rank_mul_eq_right_of_isUnit_det`, mathlib-confirmed), never a
  membership — so it dissolves the wall. COST ≈9–14 leaves (A3/A4 genuinely-new; no existing `Matrix`
  rigidity infra). A-vs-(C) is a COST call. The A1/A2 opacity constant-factor was the one unsettled item
  (now resolved by the de-risk).
- **The genuine-row base-block family is CLOSED — the wall is intrinsic to the `caseIIICandidate`
  slot-override, 4 wall appearances (§(4.18)–(4.29)).** Route B's interior `hS` (§(4.26)), route 4-bare's
  `hseedrank` (§(4.28)), route 4-splitOff's `hWS` (§(4.29)) all wall: the wrap edge `edge i` content
  cannot enter the corner-overridden candidate span — the discriminator gate `ρ₀ ⊥̸ C(vᵢ₊₁, n')` is
  invariant under base-block re-targeting (the load-bearing finding; "Q1-clean/Q2-walls" the diagnostic —
  the relabel/rank machinery generalizes, the block is one layer up at the override). The route-B/4
  leaves stay in tree sound-in-isolation; `exists_seed_base_block` (057a86e) is a dead conditional
  (unsatisfiable `hseedrank` for the bare seed, harmless, no caller). Full kernel traces: design
  §(4.18)–(4.29). Lesson → Findings.
- **Opened 2026-06-24 at a clean-break close of 23c (user-adjudicated), at the member-mapping-wall STOP.**
  23c's option (A) `±r`-block engine is refuted at the rank-cert level (the redundancy-carry half
  succeeded — interior `hρe₀` closed). 23d = the rank-cert reconsideration, within the CHAIN layer
  (CHAIN spans 23b+23c+23d). Structural precedent: the 23b→23c clean-break close at this same wall.

### Promoted to TACTICS-QUIRKS / Findings (model-experiment.md) / DESIGN.md
- *A lemma whose goal exposes `Matrix.rank`/`mulVec` on a constructed column type (`m⊕n`, Pi, …) needs
  `[Fintype]` on that type in the signature — `[Finite]` + in-proof `Fintype.ofFinite` is too late (the
  signature elaborates first)* → TACTICS-QUIRKS § 64 (hit authoring A3).
- *`(M * Uᵀ).row p c` does not `rw` via `Matrix.mul_apply'` but IS defeq to `Matrix.vecMul (M.row p) Uᵀ c`
  — open with `change … = _`, then `Matrix.vecMul_transpose` + `LinearMap.toMatrix'_mulVec`* →
  FRICTION [idiom] (hit authoring A5a's row identity).
- *`rw [defName, …apiLemma]` fails *"synthesized instance not defeq … instDecidableEqSigma / Classical.decEq"*
  when the def froze a `Classical.decEq` in its body — use `simp only` (lenient on instances) or `congr 1`+`rw`*
  → TACTICS-QUIRKS § 66 + FRICTION [idiom] (hit authoring the A5c-keystone `dualProductCoordEquiv_apply`).
- *The deferred-hypothesis-unsat trap recurs at composition; a wall recurring across structurally-different
  fixes is intrinsic to a shared downstream object* → model-experiment Findings (rows 449–455) + DESIGN.md
  *Constructibility recon*. The full per-route kernel traces (§(4.18)–(4.30)) live in `Phase23-design.md`.
