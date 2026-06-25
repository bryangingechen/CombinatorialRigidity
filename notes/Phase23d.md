# Phase 23d — Case III general `d`: the CHAIN rank-certification reconsideration (work log)

**Status:** in progress (opened 2026-06-24 at a user-adjudicated clean-break close of 23c, at the
member-mapping-wall STOP). **Phase 23 stays in progress**; 23d is the third CHAIN-layer sub-phase
(CHAIN spans 23b + 23c + 23d, design §3). ENTRY + ASSEMBLY are later sub-phases (codes). The full
23d route history — every wall + verdict — lives in `notes/Phase23-design.md` §I.8.24(4.18)–(4.34);
program map `notes/MolecularConjecture.md`; the 23c landed-leaf inventory is `notes/Phase23c.md`.

**What 23d is.** 23c built option (A) (the `±r`-block rank-cert engine) end-to-end + closed the
interior-`hρe₀` conjecture-crux, but the general-`d` rank cert hit the `hρGv` member-mapping wall. 23d
reconsiders the rank cert. The genuine-row base-block family (route B, route 4-bare, route 4-splitOff)
all walled on the same obstruction (the wrap edge `edge i` content cannot enter the corner-overridden
`caseIIICandidate` span — the discriminator gate `ρ₀ ⊥̸ C(vᵢ₊₁, n')` is intrinsic to the slot-override,
4 appearances §(4.18)–(4.29)). So the user chose **route A** — the honest unconditional concrete-`Matrix`
Theorem 5.5 (the literal-`Matrix` model, where KT's (6.61) is a unit-det column-op, never a span
membership). All landed leaves stay in tree (sound; the route-B/4 inventory is reusable/harmless).
`d=3` stays fully green throughout.

## Current state

**✅ NEXT = the `hA` corner-LI bridge (§(4.34) leaf 2), then the dispatch wiring (item 2).** Route A is
assembled through the arm: the A1–A5c chain + the cert `case_III_rank_certification_matrix` (reshaped to
the (4b′) row-submatrix core) + the A6 `hblock` 0-block kernel + the arm spine
`case_III_arm_realization_matrix` (carrying `(m₁,m₂,hm₁,hm₂,re,hbot,hA,hD)` as hypotheses, constructing
`U`/`hU`/`en`/`hblock` in-body) + the `hD` bridge (leaf 1) are all LANDED, gate/axiom-clean, no
`ScrewSpace` unfold. `_chain` + the route-B/4 dual-space leaves stay in tree (parallel/sound). The
interior-`hρe₀` crux is CLOSED. The §(4.33) cert-shape obstruction (the total-`em`-bijection `fromBlocks`
is unsatisfiable for `D ≥ 3` — the `D−2` surplus `v`-rows break both `toBlocks₂₁=0` and `hD`) is
structurally dissolved by (4b′): the `re` injection drops the surplus, the SUBSPACE shape KT's (6.64)
states (full trace design §(4.33)).

**A6-assembly RECON verdict (session #33):** the arm composes sorry-free, but `hA`/`hD` are TWO
genuinely-new dual-space→matrix-row LI bridges — NOT the ~1-leaf gate facts the row-473 prose claimed.
`hD` (leaf 1) LANDED via the bottom-block op-invariance (the operated `toBlocks₂₂` IS the un-operated
`R(Gᵥ,q)` submatrix; the column op only touches the pin `v`'s coordinate). `hA` (leaf 2) is NEXT (see
*Hand-off*; §38 whnf guard). Exact residual goals + signatures: design §I.8.24(4.34).

The canonical landed route-A leaf inventory (all 2026-06-24/25, build/lint/warning/axiom-clean — per-leaf
rationale in git + *Decisions made* + design §(4.31)/(4.32)/(4.34)):

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
| CERT | `case_III_rank_certification_matrix` (abstract block-data drop-in for `_chain`; **reshaped to the (4b′) row-submatrix core** — `re` injection + `.submatrix re en` + fires `…_of_edge_submatrix_fromBlocks`) | `Candidate.lean` |
| A6-entry | `rigidityMatrixEdge_mul_columnOp_row` / `..._apply` / `..._apply_eq_zero_of_ne` (the (6.61) operated-entry facts on the EDGE-restricted `rigidityMatrixEdge`; per-row-keyed op — sound but the WRONG vanishing for the `0` block, replaced by A6-fix) | `Concrete.lean` |
| A6-fix | `rigidityMatrixEdge_mul_columnOp_apply_pin_zero` (FIXED-pin-`v` `0`-block) / `..._apply_corner` (the `hA` corner entry, panel functional on `v`'s cols) / `..._reindex_toBlocks₂₁_eq_zero` (the `.reindex`-form `toBlocks₂₁=0`, now superseded by the `.submatrix` form) — the CORRECTED §(4.33) index map | `Concrete.lean` |
| 4b′ kernel | `Matrix.rank_ge_of_isUnit_mul_submatrix_fromBlocks` (the A4 bridge in row-SUBMATRIX form: row injection `re : m₁⊕m₂ → rows` + col equiv `en`, `(M*U).submatrix re en = fromBlocks A B 0 D` ⟹ `#m₁+#m₂ ≤ M.rank`; `rank_submatrix_le` for `rank_reindex`) + `…_finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks` (its A4.5e composition) — drops the `D−2` surplus `v`-rows | `Rank.lean`/`Concrete.lean` |
| A6 `hblock` 0-block | `rigidityMatrixEdge_mul_columnOp_submatrix_toBlocks₂₁_eq_zero` (row-*injection* analogue: any `re` with bottom rows avoiding `v` + `en := (columnSplit v).symm` ⟹ `((… * U).submatrix re en).toBlocks₂₁ = 0`) — makes the cert's `hblock` a `fromBlocks_toBlocks` one-liner | `Concrete.lean` |
| A6 `hD` (leaf 1) | `rigidityMatrixEdge_apply` + `rigidityMatrixEdge_mul_columnOp_apply_off_pin` (operated = un-operated off the pin) + `submatrix_columnOp_toBlocks₂₂_eq` (the (6.64) bottom block IS the un-operated `R(Gᵥ,q)` submatrix) + `linearIndependent_toBlocks₂₂_row_of_off_pin` (the `hD` bridge: IH-restricted un-operated submatrix row-LI ⟹ `toBlocks₂₂.row` LI) | `Concrete.lean` |
| A6 ARM SPINE | `case_III_arm_realization_matrix` (`ForkedArm.lean`, route-A sibling of `_chain`: carries `(m₁,m₂,hm₁,hm₂,re,hbot,hA,hD)`, constructs `U`/`hU`/`en`/`hblock` in-body, calls the cert + the route-agnostic tail; conclusion byte-identical to `_chain`) | `ForkedArm.lean` |

Everything is carrier-agnostic — **no `ScrewSpace` unfolding** anywhere (route A's escape from the
§(4.18)–(4.30) span-membership wall: KT's (6.61) is a unit-det right-multiply, never a membership).

## Remaining work in Phase 23

1. **The general-`d` rank certification — route A (concrete `Matrix`).** ◐ The A1–A5c chain + the cert
   (reshaped to the (4b′) row-submatrix core) + the (4b′) kernel + the A6 `hblock` 0-block kernel + the
   arm spine `case_III_arm_realization_matrix` + the `hD` bridge (leaf 1) are LANDED (full inventory:
   *Current state* table). **NEXT = the `hA` corner-LI bridge (leaf 2)** (see *Hand-off*), then the
   dispatch (item 2) discharges `(re, hbot, hA, hD)` + wires the arm. `_chain` + the route-B/4 dual-space
   leaves stay in tree (sound in isolation — the dual-space approach the wall closed; do not build on
   them). The interior-`hρe₀` crux is CLOSED.
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

**State** (full landed inventory: *Current state* table; per-leaf rationale: *Decisions made* + design
§(4.31)–(4.34)). Route A is assembled through the arm spine + the `hD` bridge — all gate/axiom-clean, no
`ScrewSpace` unfold. `_chain` + the route-B/4 leaves stay in tree (parallel/sound). The §(4.33) cert-shape
obstruction is structurally dissolved by (4b′). The arm carries `(re, hbot, hA, hD)` as hypotheses (the
standing carry-the-crux idiom); the dispatch (item 2) discharges them.

**NEXT CONCRETE LEAF = `hA` (leaf 2)** — the `D×D` corner-LI bridge
`linearIndependent_toBlocks₁₁_row_of_corner_gate` (`Concrete.lean`). Rewrite entries via the landed
`rigidityMatrixEdge_mul_columnOp_apply_corner` to `(blockBasisOn)(finScrewBasis c)` (needs a structural
fact that the corner `re ∘ Sum.inl` rows have endpoints `(v,a)`/`(v,b)`), then port
`linearIndependent_mkQ_corner_of_gate` to matrix-row form. **GUARD the `caseIIICandidate` whnf — §38**
(the recon hit a 200000-heartbeat timeout on a naive `linearIndependent_row_of_coordEquiv`; use `apply`
with explicit carrier, never `simp`/`whnf` on `F₀`). The `hD` bridge (leaf 1, landed) is the parallel
template — but `hA` is harder (the corner-gate content + the whnf guard). Exact `hA`/`hD` residual goals +
signatures: design §I.8.24(4.34).

**Then the dispatch wiring (item 2)** — `chainData_dispatch` discharges `(re, hbot, hA, hD)` from the
`ChainData` interior split (as it discharges `_chain`'s `(W, g)`) + wires whichever arm. Then ENTRY +
ASSEMBLY (parallel-safe).

**DIRECTION (4b′)** (user-adjudicated 2026-06-25, session #33): row-submatrix reshape. DECLINED: (4a)
`D := R(G₁,q₁)` relabelled-IH matrix (forces the hard `chainData_bottom_relabel` matrix analogue now,
hard); (C) honest-conditional fallback (carry the rank-cert obligation as one hypothesis; abandons the
unconditional Thm 5.5 — the documented fallback only if route A later walls). **No motive/IH/contract
change** (within route A). Full options + signatures: design §I.8.24(4.33)(5).

**Do NOT re-attempt** the closed genuine-row base-block routes (B, 4-bare, 4-splitOff) or the dual-space
rank-cert variants — the wall (the discriminator gate intrinsic to the `caseIIICandidate` slot-override)
is kernel-confirmed across all of them (§(4.18)–(4.29)); route A escapes via the literal-`Matrix` model
(KT's (6.61) is a column-op equality, never a span membership), not by re-targeting the base block.

## Decisions made during this phase

*(The 23c landed-leaf inventory + wall-characterization is the settled archive in `notes/Phase23c.md`;
the full 23d route history — every wall, spike, and verdict — is `notes/Phase23-design.md`
§I.8.24(4.18)–(4.34). This section keeps the two most forward-relevant route-A decisions full; the rest
are one-line verdicts — the landed inventory + per-leaf prose live in the *Current state* table, git, and
the design doc.)*

### Forward-relevant (full)

- **A6 ARM SPINE LANDED + A6-assembly RECON verdict (2026-06-25, `ForkedArm.lean` + recon, design
  §(4.34)).** `case_III_arm_realization_matrix` — the route-A sibling of `_chain`: same split-data/count
  signature (+ `[Fintype α] [DecidableEq α]`), carrying the matrix block data
  `(m₁, m₂, hm₁, hm₂, re, hbot, hA, hD)` (carry-the-crux), CONSTRUCTING `U`/`hU`/`en`/`hblock` in-body
  (the recon's sorry-free composition banked), calling the cert then the shared tail. **RECON
  (compiler-checked spike): the arm composes sorry-free, but `hA`/`hD` are TWO genuinely-new
  dual-space→matrix-row LI bridges, NOT the row-473 "~1-leaf gate facts"** — the A5b iff is for the FULL
  `rigidityProd.row`, not the operated/`v`-restricted `toBlocks`; `omitTwoExtensor` LI is extensor-space,
  not `toBlocks₁₁.row`. `hA` (leaf 2) ports `linearIndependent_mkQ_corner_of_gate` — GUARD the whnf (§38).
- **A6 `hD` LEAF (leaf 1) LANDED — `linearIndependent_toBlocks₂₂_row_of_off_pin` (2026-06-25,
  `Concrete.lean`).** The cert's `hD` from the IH full-rank, via the **op-invariance of the bottom
  block**: the column op `columnOp hva` only updates body `v`'s screw coordinate, invisible to a `Gᵥ`-row
  whose endpoints both avoid `v`, so the operated (6.64) block `toBlocks₂₂` IS the un-operated `R(Gᵥ,q)`
  submatrix (`submatrix_columnOp_toBlocks₂₂_eq`, entrywise off `rigidityMatrixEdge_mul_columnOp_apply_off_pin`
  + `rigidityMatrixEdge_apply`). Hence `hD` is a pure submatrix-restriction of the IH row-LI — **cleaner
  than the design's `rank_eq_finrank_span_row` route** (no Gram/rank detour). The remaining IH-rank →
  `hIH` step is the dispatch's burden (item 2). Friction: `rw` with an explicit lemma rewrites only the
  first match → `simp only` to fixpoint (→ FRICTION [idiom]).

### Landed-leaf verdicts (one line each — full prose in git / the table / design)

- **A6 `hblock` 0-block kernel** `rigidityMatrixEdge_mul_columnOp_submatrix_toBlocks₂₁_eq_zero`
  (2026-06-25) — the row-*injection* analogue of the reindex-form brick; makes the cert's `hblock` a
  one-line `fromBlocks_toBlocks` rewrite.
- **(4b′) cert reshape** (2026-06-25, `Candidate.lean`) — `case_III_rank_certification_matrix` fires the
  row-submatrix core (`em ≃`→`re` injection, `.reindex`→`.submatrix`, `…_of_edge_submatrix_fromBlocks`);
  conclusion byte-identical to `_chain`; mechanical.
- **(4b′) kernel reshape** (2026-06-25, `Rank.lean`+`Concrete.lean`) —
  `rank_ge_of_isUnit_mul_submatrix_fromBlocks` + its composition core; `rank_submatrix_le` for
  `rank_reindex` (no injectivity needed) drops the `D−2` surplus, resolving §(4.33)(3) at the kernel.
- **Corrected-`hblock` spike** (2026-06-25, design §(4.33)) — 3 corner-pin-`v` index-map bricks
  (`…_apply_pin_zero`/`…_apply_corner`/`…_reindex_toBlocks₂₁_eq_zero`) + FLAGGED the cert-SHAPE
  obstruction (the total-`em`-bijection `fromBlocks` unsatisfiable for `D ≥ 3`) → option (4b′).
- **A6 edge-restricted operated-entry facts** (2026-06-25) — `rigidityMatrixEdge_mul_columnOp_row`/`_apply`/
  `_apply_eq_zero_of_ne` on the cert's edge row index (the all-`β` versions were arm-unsatisfiable).
- **The A1–A5c chain + cert + `en`/`em` splits** (2026-06-24/25) — A1+A2 (de-risk, opacity CLEAN) → A3
  ((6.64) block-additivity kernel) → A4 ((6.61) column-op bridge) → A4.5/A4.5e (product/edge matrices) →
  A5a/A5b/A5c (column-op-as-right-multiply + gate re-wrap + entrywise keystone/operated facts + composition
  core) → `columnSplit`/`edgeRowSplit` → the cert `case_III_rank_certification_matrix`. All in the
  *Current state* table; per-leaf rationale in git + design §(4.31)/(4.32). Two integration spikes
  (§(4.31) re-route to A4.5; §(4.32) re-point to A4.5e) preceded their builds.
- **Route A CHOSEN + SCOPED; base-block family CLOSED; phase opened** (2026-06-24) — the user chose route
  A (honest unconditional `Matrix` Thm 5.5) over fallback (C) after the genuine-row base-block family
  closed (4 walls §(4.18)–(4.29), the discriminator gate intrinsic to the `caseIIICandidate`
  slot-override); route A scoped FEASIBLE-but-HEAVY (§(4.30)). Opened at the 23c clean-break close.

### Promoted to TACTICS-QUIRKS / Findings (model-experiment.md) / DESIGN.md
- *A lemma whose goal exposes `Matrix.rank`/`mulVec` on a constructed column type (`m⊕n`, Pi, …) needs
  `[Fintype]` on that type in the signature — `[Finite]` + in-proof `Fintype.ofFinite` is too late* →
  TACTICS-QUIRKS § 64.
- *`(M * Uᵀ).row p c` does not `rw` via `Matrix.mul_apply'` but IS defeq to `Matrix.vecMul (M.row p) Uᵀ c`
  — open with `change … = _`, then `Matrix.vecMul_transpose` + `LinearMap.toMatrix'_mulVec`* →
  FRICTION [idiom].
- *`rw [defName, …apiLemma]` fails "synthesized instance not defeq … instDecidableEqSigma / Classical.decEq"
  when the def froze a `Classical.decEq` in its body — use `simp only` (lenient on instances) or `congr 1`+`rw`*
  → TACTICS-QUIRKS § 66 + FRICTION [idiom].
- *`E(G)`/`V(G)` scoped Graph notation is not in scope in `Molecular/RigidityMatrix/` files (no
  `open Graph`) — write the `F.graph.edgeSet` dot form in signatures; `lean_multi_attempt` masks it* →
  TACTICS-QUIRKS § 67 + FRICTION [idiom].
- *A computable `Equiv` built from `Equiv.sumCompl (· = a)` needs a `[DecidableEq α]` hypothesis on the
  def, not an in-body `Classical`* → FRICTION [idiom].
- *`rw` with an explicit lemma application rewrites only the first matched occurrence — use `simp only` to
  fixpoint for repeated reads (the dual-endpoint `columnOp` case)* → FRICTION [idiom].
- *The deferred-hypothesis-satisfiability trap recurs at COMPOSITION and at the ARM-ASSEMBLY consumer (not
  only leaf hypotheses); a wall recurring across structurally-different fixes is intrinsic to a shared
  downstream object; for a route-composition crux in the defeq-fragile zone, spike-before-build beats
  build-then-BLOCK even when a prior recon "settled" it* → model-experiment Findings (rows 449–455,
  457–473, 477–478) + DESIGN.md *Constructibility recon*. Full per-route kernel traces (§(4.18)–(4.34))
  live in `Phase23-design.md`.
