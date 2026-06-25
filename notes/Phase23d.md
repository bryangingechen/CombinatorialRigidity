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
bridge) + A4.5 (product-column matrix) + A5a (column-op-as-right-multiply) + A5b (the gate re-wrap)
+ the A5c-keystone + the A5c operated-entry facts + A4.5e (the edge-restricted matrix) + the A5c
COMPOSITION CORE (`finrank_span_rigidityRows_ge_of_edge_fromBlocks`) + the `en` column split
(`columnSplit`) + the `em` panel-row split (`edgeRowSplit`) + now the ROUTE-A CERT ITSELF
(`case_III_rank_certification_matrix`, the abstract block-data drop-in replacing
`case_III_rank_certification_chain` at the arm's `hrank` seam) are LANDED + gate-verified.**
A1+A2: `Molecular/RigidityMatrix/Concrete.lean` (opacity CLEAN — the bridge runs through
`Basis`/`LinearEquiv`, never unfolding `ScrewSpace`; the §(4.30) residual RESOLVED). The full landed
route-A leaf inventory (all 2026-06-24/25, build/lint/warning/axiom-clean — per-leaf prose in git +
*Decisions made* + design §(4.31)/(4.32)):

| Leaf | Decl(s) | Home |
|---|---|---|
| A1 | `rigidityMatrix` (literal `(D−1)|E|×D|V|`) + `rigidityMatrix_row` (`rfl`) | `Concrete.lean` |
| A2 | `Matrix.rank_of_dualCoord` / `rigidityMatrix_rank` / clause-(iii) `..._eq_finrank_span_rigidityRows` (honest target) + `span_range_rigidityRowFun` | `Concrete.lean` |
| A3 | `Matrix.rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows` (KT (6.64) block-additivity, pure-`Matrix`, no span membership) | `Rank.lean` |
| A4 | `Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks` (A4→A3 bridge: unit-det `M*U` + `em`/`en`/`fromBlocks` ⟹ `#m₁+#m₂ ≤ M.rank`) + `rigidityMatrix_mul_rank` | `Rank.lean`/`Concrete.lean` |
| A4.5 | `Matrix.rank_of_coordEquiv` (generalized) + `finScrewBasis`/`dualProductCoordEquiv`/`rigidityMatrixProd` + `rigidityMatrixProd_rank(_eq_finrank…)` | `Concrete.lean` |
| A5a | `prodColumnOpEquiv` + `..._transpose_toMatrix'_det_isUnit` (unit-det) + `rigidityMatrixProd_mul_columnOp_row` (the (6.61) `· * U` precomposes each row with `Φ`) | `Concrete.lean` |
| A5b | `Matrix.linearIndependent_row_of_coordEquiv` + `linearIndependent_rigidityMatrixProd_row_iff` (the `hA`/`hD` gate re-wrap) | `Concrete.lean` |
| A5c keystone | `dualProductCoordEquiv_apply` (entrywise) + `rigidityMatrixProd_apply_eq_zero_of_ne` (un-operated (6.61) zero block) | `Concrete.lean` |
| A5c operated | `rigidityMatrixProd_mul_columnOp_apply` (entry formula) + `..._apply_eq_zero_of_ne` (operated (6.61) zero block, `Φ=(columnOp hva).symm`) | `Concrete.lean` |
| A4.5e | `rigidityMatrixEdge` + `rigidityMatrixEdge_rank(_eq_finrank…)` (EDGE-restricted row index `{e // e ∈ E(G)} × Fin (D−1)`, the satisfiable real-arm form) | `Concrete.lean` |
| A5c core | `finrank_span_rigidityRows_ge_of_edge_fromBlocks` (the A4 + A4.5e composition: block data ⟹ `#m₁+#m₂ ≤ finrank (span rigidityRows)`) | `Concrete.lean` |
| `en`/`em` splits | `columnSplit`/`columnSplit_corner_card` (corner `=D`) + `edgeRowSplit`/`edgeRowSplit_corner_card` (corner `=D−1`) | `Concrete.lean` |
| CERT | `case_III_rank_certification_matrix` (abstract block-data drop-in for `_chain`) | `Candidate.lean` |

Everything is carrier-agnostic — **no `ScrewSpace` unfolding** anywhere (route A's escape from the
§(4.18)–(4.30) span-membership wall: KT's (6.61) is a unit-det right-multiply, never a membership).

**✅ The ROUTE-A CERT is now LANDED** (`PanelHingeFramework.case_III_rank_certification_matrix`,
`CaseIII/Candidate.lean`, 2026-06-25, full-build/lint/warning/axiom-clean) — the abstract block-data
drop-in for `case_III_rank_certification_chain`. It takes the candidate framework `caseIIICandidate G
ends q e_a e_b (q(a,·)) n' n_b 0`, its edge-restricted GP/link hyps (`hgp`/`hends` over `G.edgeSet`),
the (6.61)→(6.64) matrix block data (`U`/`hU`/`em`/`en`/`hblock`/`hA`/`hD`), and the cardinality facts
(`hm₁ : #m₁ = D`, `hm₂ : #m₂ = D·(|V_Gv|−1)`) + count facts (`hVone`/`hVcard`), and produces the
honest target `screwDim k · (|V(G)|−1) ≤ finrank (span (caseIIICandidate …).rigidityRows)` — the SAME
conclusion form `_chain` has, so it is a drop-in at the arm's `hrank` seam. Body: fire the landed A5c
composition core `finrank_span_rigidityRows_ge_of_edge_fromBlocks` (`F₀.graph = G` is `rfl`, so the
edge-restricted hyps transport), then the `_chain` count arithmetic. The block data + cardinalities
enter as hypotheses (the standing "carry the crux as `h…`" idiom; the geometry is the arm's burden,
A6) — exactly paralleling how `_chain` consumed `(W, g, hWS, hWcard, hιcard, hg, hLI)`. New import
edge `Candidate.lean → RigidityMatrix.Concrete` (acyclic; full build green).

**Still OPEN: the NEXT LEAF is A6 — building the block data from the chain-data geometry + wiring the
cert into the arm.** Supply `U := (toMatrix' (prodColumnOpEquiv (columnOp hva).symm))ᵀ` (unit-det via
`prodColumnOpEquiv_transpose_toMatrix'_det_isUnit`), `en := columnSplit a` (`#n₁ = D` via
`columnSplit_corner_card`), `em` extending `edgeRowSplit ⟨e_a, _⟩`'s `(D−1)` panel rows with the one
reproduced `e_b` `±r` row (`#m₁ = D`, eq. (6.66)), the IH bottom `m₂` (`#m₂ = D·(|V_Gv|−1)`), and the
crux **`hblock`** (the `fromBlocks` equality) entrywise — `0` block off
`rigidityMatrixProd_mul_columnOp_apply_eq_zero_of_ne` (`Φ = (columnOp hva).symm`; row-index-agnostic
so it reads on the `{e // e ∈ E(G)}` edge index of `rigidityMatrixEdge`), diagonal blocks off
`rigidityMatrixProd_mul_columnOp_apply`, corner/bottom row-LI (`hA`/`hD`) via the A5b iff
`linearIndependent_rigidityMatrixProd_row_iff`. Then swap the `case_III_rank_certification`/`_chain`
call for `case_III_rank_certification_matrix` at the arm's `hrank` seam (`Arms.lean:350` /
`ForkedArm.lean:90`); the route-agnostic SHARED tail `case_III_realization_of_rank` is consumed
verbatim. `hblock` is the MED–HIGH crux — the genuine remaining route-A work. Full corrected
signatures + bankable fragments: design §I.8.24(4.32).

**Remaining leaf count (post-cert, ≈1.5–2):** A6 = the chain-data-geometry block construction
(`U`/`en`/`em`/`hblock`/`hA`/`hD` from the candidate geometry, the `hblock` `fromBlocks` equality the
MED–HIGH crux) + the arm re-route (swap the `_chain` call for `_matrix` at `Arms.lean:350` /
`ForkedArm.lean:90`, route the `Fin cd.d` dispatch). All the cert-side bricks are LANDED — the cert
`case_III_rank_certification_matrix`, the composition core, the `en` split (`columnSplit`), the `em`
panel-row half (`edgeRowSplit`), `U`/`hU` (`prodColumnOpEquiv (columnOp hva).symm` +
`..._transpose_toMatrix'_det_isUnit`), and the operated-entry facts — so A6 is the geometry-supply +
wiring only, with `hblock` the one genuinely-hard remaining sub-goal. Per-leaf signatures + bankable
SORRY-FREE fragments (PROBE 1/2/3/5/6): design §I.8.24(4.32).

## Remaining work in Phase 23

1. **The general-`d` rank certification — route A (concrete `Matrix`).** ✅
   A1+A2+A3+A4+A4.5+A5a+A5b + A5c-keystone + A5c operated-entry facts + A4.5e (the edge-restricted
   matrix) + the A5c composition core (`finrank_span_rigidityRows_ge_of_edge_fromBlocks`) + the `en`
   column split (`columnSplit`) + the `em` panel-row split (`edgeRowSplit`) + the ROUTE-A CERT
   `case_III_rank_certification_matrix` (`CaseIII/Candidate.lean`, the abstract block-data drop-in for
   `_chain`) landed. **NEXT = A6** — build the block data (`U`/`en`/`em`/`hblock`/`hA`/`hD`) from the
   chain-data geometry (the `hblock` `fromBlocks` equality the MED–HIGH crux; `U`/`en`/`edgeRowSplit` +
   the operated-entry facts in hand) and swap the `_chain` call for `_matrix` at the arm's `hrank` seam
   (`Arms.lean:350` / `ForkedArm.lean:90`). The route-B/4 dual-space leaves + the chain cert
   `case_III_rank_certification_chain` stay in tree (sound in isolation — the dual-space approach the
   wall closed; do not build on them; route A REPLACES `_chain` at the arm's `hrank` seam). The
   interior-`hρe₀` crux is CLOSED.
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

**✅ Route A on track; the ROUTE-A CERT `case_III_rank_certification_matrix` is LANDED**
(`CaseIII/Candidate.lean`, full-build/lint/warning/axiom-clean), on top of A1–A5c + the composition
core + `columnSplit`/`edgeRowSplit` + the operated-entry facts. The cert is the abstract block-data
drop-in for `case_III_rank_certification_chain`: it consumes the candidate framework, its
edge-restricted `hgp`/`hends`, the (6.61)→(6.64) block data (`U`/`hU`/`em`/`en`/`hblock`/`hA`/`hD`) +
cardinalities (`#m₁=D`, `#m₂=D·(|V_Gv|−1)`) + count facts, and produces the byte-identical-to-`_chain`
conclusion `screwDim k · (|V(G)|−1) ≤ finrank (span (caseIIICandidate …).rigidityRows)` by firing the
composition core + the count arithmetic. **NEXT CONCRETE COMMIT = A6** — build the block data from the
chain-data geometry and wire the cert into the arm. Supply `U := (toMatrix' (prodColumnOpEquiv
(columnOp hva).symm))ᵀ` (unit-det, `prodColumnOpEquiv_transpose_toMatrix'_det_isUnit`), `en :=
columnSplit a` (`#n₁=D`, `columnSplit_corner_card`), `em` extending `edgeRowSplit ⟨e_a,_⟩`'s `(D−1)`
panel rows with the reproduced `e_b` `±r` row (`#m₁=D`, eq. (6.66)), `m₂` the IH bottom
(`#m₂=D·(|V_Gv|−1)`), and the crux **`hblock`** (the `fromBlocks` equality) entrywise — `0` block off
`rigidityMatrixProd_mul_columnOp_apply_eq_zero_of_ne` (`Φ=(columnOp hva).symm`; row-index-agnostic, so
it reads on the `{e // e ∈ E(G)}` edge index), diagonal blocks off `rigidityMatrixProd_mul_columnOp_
apply`, row-LI (`hA`/`hD`) via `linearIndependent_rigidityMatrixProd_row_iff`. Then swap the `_chain`
call for `case_III_rank_certification_matrix` at the arm's `hrank` seam (`Arms.lean:350` /
`ForkedArm.lean:90`); the route-agnostic SHARED tail `case_III_realization_of_rank` is consumed
verbatim, and the `Fin cd.d` dispatch matches the STATED `d_eq_kAdd` (no 23c-style coincidence gap —
question (d) clean). `hblock` is the MED–HIGH crux, the one genuinely-hard remaining route-A sub-goal;
everything else is geometry-supply + wiring. After A6: ENTRY + ASSEMBLY (parallel-safe). **No motive/IH
change, no phase-direction decision owed** (within route A; fall-back (C) unaffected). Bankable
SORRY-FREE fragments (PROBE 1/2/3/5/6): design §I.8.24(4.32).

**The route-A build should open as its own sub-phase at the next phase-open** (A1–A5c confirm route A
on track; the A4.5e/A5c/A6 layer plan is in *Current state* + §(4.32), superseding §(4.31)'s A5c/A6;
the new Lean lives in
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

- **ROUTE-A CERT LANDED — `case_III_rank_certification_matrix` (2026-06-25, `CaseIII/Candidate.lean`,
  full-build/lint/warning/axiom-clean).** The abstract block-data drop-in for
  `case_III_rank_certification_chain`: takes the candidate framework + edge-restricted `hgp`/`hends`
  (over `G.edgeSet`; `F₀.graph = G` is `rfl`) + the (6.61)→(6.64) block data + cardinalities + count
  facts, fires the landed composition core, produces the byte-identical-to-`_chain` honest target.
  Block data + cardinalities enter as `h…` hypotheses (the geometry is A6's burden) — parallels how
  `_chain` consumed `(W, g, …)`. New import edge `Candidate.lean → RigidityMatrix.Concrete` (acyclic;
  full build green). Friction: `[Fintype α] [DecidableEq α]` needed in the signature (not `[Finite α]`)
  for the `Matrix.mul`/`reindex` over `α × Fin D` — recurrence of TACTICS-QUIRKS §64 (signature
  elaborates first), no new entry. NEXT = A6 (build `hblock` from the geometry + wire the arm).
- **`em` panel-row split LANDED — `edgeRowSplit` + `edgeRowSplit_corner_card` (2026-06-25,
  `Concrete.lean`, build/lint/warning/axiom-clean).** The structural row analog of `columnSplit`: the
  designated-edge `ea` corner/rest partition of the EDGE-restricted row index `{e // e ∈ E(G)} ×
  Fin (D−1)` (same `Equiv.sumCompl (· = ea)`/`prodCongr`/`sumProdDistrib` build), `ea`-corner card
  `= screwDim k − 1` (the `(D−1)` panel rows of `e_a`). The panel-row half of the composition-core's
  `em` input — the full corner `m₁` adds the one reproduced `e_b` `±r` row (eq. (6.66), card
  `D = (D−1)+1`) at the `hblock` assembly. With `en`/`U`/`hU` already landed, three of the four named
  A5c inputs are in hand. Shrunk to fit one sitting (`case_III_rank_certification_matrix` is the
  MED–HIGH crux; this banks one complete reusable carrier-agnostic input SORRY-FREE). No new friction
  (exact mirror of `columnSplit`). NEXT = the `+1`-row `em` assembly + `hblock`.
- **`en` column split LANDED — `columnSplit` + `columnSplit_corner_card` (2026-06-24, `Concrete.lean`,
  build/lint/warning/axiom-clean).** The body-`a` corner/bottom partition of the product column index
  `α × Fin D` (PROBE 3): `columnSplit a : α × Fin D ≃ ({body // body = a} × Fin D) ⊕ ({body // body ≠
  a} × Fin D)` (`Equiv.sumCompl (· = a)` distributed over `Fin D` via `Equiv.prodCongr` +
  `Equiv.sumProdDistrib`), with the corner card `= screwDim k` (`Fintype.card_prod` +
  `Fintype.card_subtype_eq` + `screwSpace_finrank`). This is the `en` input the composition core
  consumes; with the already-landed `U`/`hU` (`prodColumnOpEquiv (columnOp hva).symm` +
  `..._transpose_toMatrix'_det_isUnit`), two of the three named A5c inputs are now in hand. Shrunk to
  fit one sitting (per the one-sitting scope rule) — the full `case_III_rank_certification_matrix` is
  MED–HIGH/2–3 leaves; this banks one complete, reusable, carrier-agnostic input SORRY-FREE. NEXT =
  the `em` row split + `hblock`. Friction: a computable `Equiv.sumCompl (· = a)`-based def needs a
  `[DecidableEq α]` *hypothesis*, not an in-body `Classical` (→ FRICTION [idiom]).
- **A5c composition core LANDED — `finrank_span_rigidityRows_ge_of_edge_fromBlocks` (2026-06-24,
  `Concrete.lean`, build/lint/warning/axiom-clean).** The PROBE-2 body packaged as a standalone
  carrier-agnostic lemma (`[Fintype α] [DecidableEq α] [Finite β]`): edge-restricted `hgp`/`hends` +
  unit-det `U` + `em`/`en` with `(rigidityMatrixEdge * U).reindex em en = fromBlocks A B 0 D` (LI
  corner/bottom rows) ⟹ `#m₁ + #m₂ ≤ finrank (span F.rigidityRows)`. Two-line proof: the A4 bridge
  `Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks` + the A4.5e honest-rank bridge. Shrunk the named
  A5c deliverable to fit one sitting (per the one-sitting scope rule) — this lands the composition
  half SORRY-FREE; the remaining A5c work is the chain-data-geometry inputs (`U`/`em`/`en`/`hblock`/LI)
  that feed it. One build-config friction: had to add a `public import` of the project
  `Mathlib.LinearAlgebra.Matrix.Rank` mirror to `Concrete.lean` — the A4 specialization
  `rigidityMatrix_mul_rank` used only the *mathlib* `rank_mul_eq_left_of_isUnit_det`, so the project
  bridge `rank_ge_of_isUnit_mul_reindex_fromBlocks` was not transitively imported until now (phase-local;
  the next A5c leaf builds in the same file). NO `ScrewSpace` unfolding. NEXT = the A5c `hblock` residual.
- **A4.5e LANDED — the edge-restricted matrix `rigidityMatrixEdge` (2026-06-24, `Concrete.lean`,
  build/lint/warning/axiom-clean).** Six decls (`blockBasisOn`, `rigidityRowFunEdge`,
  `rigidityMatrixEdge : Matrix ({e // e ∈ E(G)} × Fin (D−1)) (α × Fin D) ℝ`, `rigidityMatrixEdge_rank`,
  `span_range_rigidityRowFunEdge`, `rigidityMatrixEdge_rank_eq_finrank_span_rigidityRows`) — the
  product matrix re-indexed by edges only, with `hgp`/`hends` quantified `∀ e ∈ E(G), …` (the
  satisfiable real-arm form: the all-`β` `rigidityMatrixProd` honest-rank bridges need them total over
  `β`, unfireable once `β` has non-edges). Rank bridge = a one-line `Matrix.rank_of_coordEquiv` on the
  `Subtype` row index (the carrier-agnostic lemma's `[Finite ι]` row index takes the subtype-product
  for free; no `ScrewSpace` unfold); the span identity is the `span_range_rigidityRowFun` argument
  restricted to edges (`≥` uses `IsLink.edge_mem` for the link's edge-membership). Came in under the
  ~1–1.5-leaf estimate — both bridges are mechanical re-statements of the landed all-`β` versions.
  NEXT = A5c. One friction: `E(G)` scoped notation isn't in scope here (`Concrete.lean` has no
  `open Graph`) → wrote `F.graph.edgeSet` (TACTICS-QUIRKS § 67).
- **A5c+A6 INTEGRATION SPIKE — re-pointed the next leaf to A4.5e (docs-only, 2026-06-24, design
  §I.8.24(4.32); A4.5e now landed).** Verdict: the A6 composition skeleton is SORRY-FREE on the actual
  `caseIIICandidate` arm, but the §(4.31) decomposition was off by one leaf — the all-`β`-row
  `rigidityMatrix(Prod)` honest-rank bridges need `hgp`/`hends` total over `β`, unsatisfiable with
  non-edges. Fix = A4.5e (edge-restricted matrix, now landed above). Bankable PROBE 1/2/3/5/6 fragments
  + the A5c/A6 corrected signatures: design §I.8.24(4.32).
- **A5c operated-entry facts LANDED — the entrywise facts for `rigidityMatrixProd * U` (2026-06-24,
  `Concrete.lean`, build/lint/warning/axiom-clean).** Two decls: `rigidityMatrixProd_mul_columnOp_apply`
  (the operated entry formula `(M*U) p (body,c) = rigidityRowFun p (Φ.symm (Pi.single body …))` for ANY
  `Φ`; composes the A5a `_row` identity + the keystone + `LinearEquiv.dualMap_apply`) and
  `rigidityMatrixProd_mul_columnOp_apply_eq_zero_of_ne` (the operated (6.61) zero block, `Φ =
  (columnOp hva).symm` so the precomposition is `columnOp hva` — `hingeRow_comp_columnOp_apply`
  collapses the operated wrap row to a *pure `v`-column* row, KT (6.14)–(6.16), `0` off `v`). The
  earlier keystone facts (`dualProductCoordEquiv_apply`, `..._apply_eq_zero_of_ne`) were for the
  *un-operated* matrix; the `hblock` block-fill reads the *operated* `M*U`, which these supply directly.
  One small friction: `congrFun … (body,c)` of the `_row` identity needs `rw [Matrix.row] at h` to align
  `.row p (body,c)` with the goal's bare `p (body,c)` (FRICTION sibling of the A5a `.row` idiom). NEXT =
  the A5c-assembly residue (the `em`/`en` split + `fromBlocks` reindex), which folds toward A6.
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
- *`E(G)`/`V(G)` scoped Graph notation is not in scope in `Molecular/RigidityMatrix/` files (no
  `open Graph`) — write the `F.graph.edgeSet` dot form in signatures; `lean_multi_attempt` masks it*
  → TACTICS-QUIRKS § 67 + FRICTION [idiom] (hit authoring A4.5e's edge-restricted binders).
- *A computable `Equiv` built from `Equiv.sumCompl (· = a)` needs a `[DecidableEq α]` hypothesis on
  the def, not an in-body `Classical` (else it fails to compile as `noncomputable`)* → FRICTION
  [idiom] (hit authoring the A5c `columnSplit`).
- *The deferred-hypothesis-unsat trap recurs at composition; a wall recurring across structurally-different
  fixes is intrinsic to a shared downstream object* → model-experiment Findings (rows 449–455) + DESIGN.md
  *Constructibility recon*. The full per-route kernel traces (§(4.18)–(4.30)) live in `Phase23-design.md`.
