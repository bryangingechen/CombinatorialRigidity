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

**✅ ROUTE A is the plan; A1+A2 (de-risk) + A3 (block-additivity kernel) + now A4 (the (6.61) column-op
bridge) are LANDED + gate-verified.** A1+A2: `Molecular/RigidityMatrix/Concrete.lean` (2026-06-24,
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

**Still OPEN (post-A5 spike, 2026-06-24):** the `hblock` construction. The A5 route-composition spike
(design §I.8.24(4.31), 5 probes all SORRY-FREE) settled the coordinator's kernel concern: the (6.61)
column op IS expressible over a coordinatized matrix as a unit-det right-multiply (route A's escape
holds — never a span membership), BUT `hblock`'s `D×D` corner split is **NOT dischargeable on the flat
`rigidityMatrix`** — its arbitrary `Module.finBasis` columns (`dualCoordEquiv`) do not factor as
`α × Fin D` (confirmed: `finrank ℝ (Dual ℝ (α → ScrewSpace k)) = card α · screwDim k`, but no column
subset = "body `vᵢ₊₁`'s `D` columns"). **Fix = one preceding re-coordinatization leaf A4.5: a
PRODUCT-column rigidity matrix `rigidityMatrixProd : Matrix (β × Fin (D−1)) (α × Fin D) ℝ`**, same
honest rank (same opacity-clean bridge), columns factor `α × Fin D` so the KT block split is the obvious
product reindex. The A4 bridge `rank_ge_of_isUnit_mul_reindex_fromBlocks` takes ANY `M`, so it consumes
the product matrix directly. **The next concrete commit is A4.5a–c** (the `screwBasis` /
`dualProductCoordEquiv` / `rigidityMatrixProd` defs — mechanical, all spike-verified). NOT a motive/IH
change, NOT new math beyond the re-coordinatization. Doc-comment fix owed: `Concrete.lean:276` + the
`rigidityMatrix`/`rigidityMatrix_mul_rank` `α × Fin D` prose is dimension-correct but index-imprecise
(the flat index is an arbitrary basis); A5-build corrects it.

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

**Sharpened A5–A6 leaf count (post-A4, ≈3–6 remaining):** A1+A2 ~2 effective leaves; **A3** ~1; **A4**
~1 (two short composing lemmas — the column-op is `rank_mul_eq_left_of_isUnit_det`, rank-invariant
outright; the A4→A3 bridge a single `calc`). Still OPEN: **A5** re-aim the gate/union-dim cert at the
`D×D` minor + *construct* the specific (6.61) `U` and its `fromBlocks` reindexing (the `hblock` input to
`rank_ge_of_isUnit_mul_reindex_fromBlocks`); content LANDED for the gate
(`interior_group_eq_baseRedundancy`, `omitTwoExtensor_linearIndependent`) but the `U` construction +
block-reindex is the entrywise work A4's bridge deferred — ~2–3, MEDIUM; **A6** dispatch+spine (~1–2,
MEDIUM).

## Remaining work in Phase 23

1. **The general-`d` rank certification — route A (concrete `Matrix`).** ✅ A1+A2 landed (`Concrete.lean`);
   ✅ A3 landed (`Rank.lean`, `Matrix.rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows`); ✅ A4 column-op
   bridge landed (`Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks` + `BodyHingeFramework.rigidityMatrix_mul_rank`).
   OPEN (re-decomposed by the A5 spike, design §(4.31)): **A4.5** the re-coordinatization leaf — a
   PRODUCT-column matrix `rigidityMatrixProd` (the flat `rigidityMatrix` columns don't factor `α × Fin D`,
   so `hblock`'s `D×D` corner split needs product columns; **NEXT**) → **A5** (gate re-wrap `A5b` +
   `hblock` entrywise block-fill `A5c`) → **A6** (dispatch+spine). The route-B/4 dual-space leaves +
   the chain cert `case_III_rank_certification_chain` stay in tree (sound in isolation — the dual-space
   approach the wall closed; do not build on them). The interior-`hρe₀` crux is CLOSED.
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

**✅ Route A on track; A1+A2+A3+A4 LANDED. The A5 route-composition SPIKE (2026-06-24, design §(4.31),
5 probes SORRY-FREE) RE-DECOMPOSED the next work: NEXT CONCRETE COMMIT = A4.5a–c — the re-coordinatization
leaf (`screwBasis` + `dualProductCoordEquiv` + `rigidityMatrixProd`).** The spike settled the
coordinator's kernel concern: the flat `rigidityMatrix`'s columns (`Fin (finrank ℝ (Dual …))`, an
arbitrary `Module.finBasis`) do NOT factor as `α × Fin D`, so the A4-bridge `hblock`'s `D×D` corner
split is **not dischargeable on the flat matrix**. But (a) the (6.61) column op IS expressible over a
coordinatized matrix as a unit-det right-multiply (`U = (toMatrix' (coordOpEquiv Φ))ᵀ`, route A's
"never a span membership" escape holds — SORRY-FREE PROBE 2b/4); (b) a PRODUCT-column matrix
`rigidityMatrixProd : Matrix (β × Fin (D−1)) (α × Fin D) ℝ` has the SAME honest rank by the same
opacity-clean bridge (SORRY-FREE PROBE 3) and its columns DO factor `α × Fin D`, so it feeds the same
A4 bridge `rank_ge_of_isUnit_mul_reindex_fromBlocks` (which takes ANY `M`) with the obvious product
block split. **A4.5 is the genuinely-new leaf the spike surfaced** (mechanical, all spike-verified —
exact signatures + bankable SORRY-FREE fragments in design §(4.31)(4)). After A4.5: A5b (gate re-wrap,
content LANDED) + A5c (the `hblock` entrywise block-fill — the residual MED–HIGH crux, now entrywise
over `α × Fin D` via `dualProductCoordEquiv φ (body,j) = φ (Pi.single body (screwBasis j))`, NOT a span
argument), then A6 (dispatch+spine), then ENTRY + ASSEMBLY (parallel-safe). **No motive/IH change, no
new math beyond the re-coordinatization, no phase-direction decision owed** (within route A; A4.5 is a
sub-leaf of the §(4.30) A5 scope). Recommend the A4.5d refactor = GENERALIZE `Matrix.rank_of_dualCoord`
(`Concrete.lean:84`) over an arbitrary coordinatizing equiv so both flat + product rank bridges are
one-line instances.

**The route-A build should open as its own sub-phase at the next phase-open** (A1+A2+A3 confirm route A
on track; the A4–A6 layer plan is in *Current state* + §(4.30); the new Lean lives in
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

- **A5 ROUTE-COMPOSITION SPIKE — verdict: A5 needs one preceding re-coordinatization leaf A4.5
  (2026-06-24, compiler-checked, scratch reverted, tree clean; design §I.8.24(4.31)).** The flat
  `rigidityMatrix`'s columns are an arbitrary `Module.finBasis` of `Dual ℝ (α → ScrewSpace k)` (via
  `dualCoordEquiv`) — dimension `card α · screwDim k` but NOT factoring as `α × Fin D`, so the A4-bridge
  `hblock`'s `D×D` corner split is undischargeable on it (the coordinator's concern, kernel-confirmed).
  Fix: a product-column matrix `rigidityMatrixProd : Matrix (β × Fin (D−1)) (α × Fin D) ℝ`, same honest
  rank by the same carrier-agnostic bridge, feeding the same `rank_ge_of_isUnit_mul_reindex_fromBlocks`.
  The column op IS a unit-det right-multiply over a coordinatized matrix (route A's escape holds — never
  a span membership). 5 probes SORRY-FREE; only the `hblock` block-fill (A5c) residual. No motive/IH
  change. Full verdict + exact A4.5/A5/A6 signatures + bankable fragments → design §(4.31).
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
- *The deferred-hypothesis-unsat trap recurs at composition; a wall recurring across structurally-different
  fixes is intrinsic to a shared downstream object* → model-experiment Findings (rows 449–455) + DESIGN.md
  *Constructibility recon*. The full per-route kernel traces (§(4.18)–(4.30)) live in `Phase23-design.md`.
