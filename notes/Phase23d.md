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

**✅ ROUTE FIGURED OUT — FORK 1 (design §(4.40)): KT's proof is SOUND, the project's `columnOp` IS KT's
(6.61), and the wall was a formalization artifact — the cert's `hbot` excluded the `e_b` row that KT's
column op converts into the full-rank `R(Gab)` bottom fill. RESHAPE STEPS 1–2 LANDED; the cross-label
bridge (the `e_b`→`e₀` row-routing primitive) LANDED 2026-06-25. The `hD` step-3 reshape via the RANK
route decomposes into three leaves L-span/L-rank/L-hD; **ALL THREE LANDED 2026-06-25** — L-span
(`span_range_hingeRow_blockSpanning_eq_rigidityRows`, `Basic.lean`), L-rank
(`rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom`, `Concrete.lean`), and L-hD
(`linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`, `Concrete.lean`, the row-LI conclusion
via `linearIndependent_rows_iff_rank_eq_card`, carrying the IH count `hrank` as a hypothesis). The two
column-restriction support facts (`Matrix.linearIndependent_row_of_zero_left_cols`,
`Matrix.rank_submatrix_inr_of_zero_left_cols`, both mirrored in `Rank.lean`) discharge the off-`v`
column drop. **NEXT = step 4** — re-point the cert/arm/dispatch `re`/`hm₂` (and the `F₂ = splitOff`
framework + the `hrank` IH instantiation) from `removeVertex` to `splitOff`, then leaf 5 (the dispatch
wiring). NOT the matrix-equality form (BLOCKED, see below).**

**⚠ ASSEMBLY-ROUTE DECISION (compiler-grounded spike, 2026-06-25): the matrix-equality form
`submatrix_columnOp_toBlocks₂₂_eq_Gab` (`M.toBlocks₂₂ = F₂.rigidityMatrixEdge.submatrix …`) is BLOCKED.**
A kernel-checked probe assembled it modulo per-row hyps and found the residual goal needs
`hblk : F₁.blockBasisOn hgp₁ he_b j = F₂.blockBasisOn hgp₂ he₀ j` (equality of *chosen* basis vectors).
That is **unprovable**: `blockBasisOn` is a `Module.finBasisOfFinrankEq` choice on the submodule term
`F₁.hingeRowBlock e_b` vs `F₂.hingeRowBlock e₀` — propositionally-equal blocks (same extensor) but
term-distinct submodules, so the chosen vectors differ. **The sound route is RANK** (verified composing,
below): `hD : LinearIndependent ℝ M.toBlocks₂₂.row ⟸ M.toBlocks₂₂.rank = #m₂` (the landed
`Matrix.linearIndependent_rows_iff_rank_eq_card`), with `M.toBlocks₂₂.rank = #m₂` from the IH `R(Gab)`
full rank via the bottom-block row functionals' span = `span F₂.rigidityRows` (each row ∈ via the landed
cross-label bridge; spanning by per-edge block coverage; `finrank = D·(|V_Gab|−1) = #m₂` from
`hsplitGP`). This is **genuinely-new multi-leaf work** (~3–5 leaves), NOT the design's "~1-commit step 3".
The fork-decider recon (row 488, 7 kernel-clean theorems) + the coordinator's independent
primary-source read of KT (6.61)/(6.62) converge: the §(4.39) spike tested the WRONG edge
(`e_a = vᵢvᵢ₊₁`, the CORNER edge — correctly zero off-`v`); KT routes the OTHER `v`-incident edge
`e_b = vᵢ₋₁vᵢ` to the `e₀=(a,b)` bottom fill. The cert's `hbot` (both endpoints `≠ v`) is the artifact:
it excludes the `e_b` row, which is `v`-incident PRE-op but off-`v`-supported AFTER the column op;
including the operated `e_b` row makes the bottom the full-rank `R(Gab)` (split-off, minimal 0-dof; the
`e₀` rows ADD the `k'=D−2` fill, NOT redundant w.r.t. `Gv`). **Steps 1 + 2 + L-span LANDED** (per-leaf
decls + algebra in the *Current state* table rows `R(Gab)`-bottom step 1 / step 2 / step 3 L-span); the
remaining `hD` reshape is L-rank → L-hD (~2 leaves) + the cert/arm/dispatch `re`/`hm₂` re-point to
`splitOff`, all corner leaves (1,2,3) + A1–A5c + (4b′) core + A4 bridge + cert shape REUSED, no motive
change. Single-matrix confirmed. Full plan: design §(4.40). This SUPERSEDES the §(4.36)/(4.37)/(4.39)
"walls" (they tested the wrong edge / the un-operated `Gv` bottom).

**Context (the §(4.38) wrong-graph diagnosis — confirmed, now MECHANIZED by §(4.40): the bottom IS
`R(Gab)`, and the `e₀` fill comes from the operated `e_b` row).** The diverse-lens scoping pair (rows
485/486, **coordinator-verified vs KT + tree**) found **route A instantiated its bottom block on the
WRONG graph.** The
leaf-4 + comparative spikes (rows 483/484) correctly found the bottom walls — but they (and route A) used
`Gv = G.removeVertex v`, which is **deficient** by `k' > 0`. **KT's eq. 6.64 bottom block is the FULL-RANK
split-off `Gab = G.splitOff v a b e₀`** (zero deficiency, Lemma 4.8 / eq. 6.51), and the landed **d=3 arm
already uses `Gab`** (`exists_candidateRow_bottomRows_of_rigidOn`): the deficiency-fill rows are the
split-off edge `e₀ = (a,b)`'s GENUINE rows, off-`v`. On `R(Gab)` those fill rows are **literal matrix
edge-rows, NOT span members** — so the span-membership wall does NOT arise. Make-or-break unspiked piece:
KT's (6.61)→(6.62) column-op + **row-correspondence** as a literal matrix operation (carrying `R(G,pᵢ)`'s
genuine `G`-edge rows — incl. the `v`-incident `e_a` row — onto `R(Gab,q)`'s rows, so the single-matrix
`fromBlocks` cert gets a full-rank `R(Gab)` bottom). **No motive change** (the IH is consumed via the
landed rank-bridge). Decision owed: **a focused feasibility spike on the (6.62) row-correspondence**
(coordinator-rec — if it lands, reshape the bottom to `R(Gab)`, ~5–7 commits; if it walls, the wall is
intrinsic → (C)). §(4.37)'s "both options wall" stands for the two `removeVertex` options but is
SUPERSEDED as the verdict — the pair found the KT-faithful `Gab` bottom it didn't consider; route-4-splitOff
remains closed (row 454). Full verdict: design §(4.38). **The landed corner leaves (1, 2, 3=3a+3b) stay in
tree + reusable regardless.**

**Leaves 1, 2, 3 (3a + 3b) are all LANDED.** Leaf 3 (the corner `hLI` producer) is
`BodyHingeFramework.exists_corner_blockBasisOn_linearIndependent` (`Concrete.lean`): 3a
`linearIndependent_blockBasisOn_screwDual` (the `e_a` `D−1` within-block half, carrier-safe via the
mirror `Module.Basis.linearIndependent_coe_subtype`) + 3b the cross-hinge half, the **EXISTENCE-form**
`∃ j₀, LinearIndependent ℝ (Sum.elim (e_a block basis) (blockBasisOn hgp hb j₀))`. **THE CORRECTION
(the mkQ-quotient lift was a RED HERRING):** the `hA` leaf's `hLI` is a *uniform `blockBasisOn`-family
in the full screw dual* — every corner row (incl. the reproduced `±r`) reads `blockBasisOn` at the pin
(`rigidityMatrixEdge_mul_columnOp_apply_corner`), NOT a span/quotient/Lemma-2.1 object. So leaf 3b
does **not** route through `linearIndependent_mkQ_corner_of_gate`: it goes the two FIXED-`ρ₀` gates
(`hρeb : ρ₀ ∈ hingeRowBlock e_b` = `hρe₀` at the reproduced support `t=0`; `hρe₀ : ρ₀(supportExtensor
e_a) ≠ 0` the candidate-slot gate) → *block-incomparability* (`¬ hingeRowBlock e_b ≤ hingeRowBlock
e_a`, `mem_hingeRowBlock_iff`) → *some* fresh `e_b` basis vector escapes `e_a`'s block → append-one via
`linearIndependent_sumElim_candidateRow_iff` (Claim612) + 3a. NO Lemma 2.1, NO `omitTwoExtensor`, NO
`mkQ`. New mirror `Module.Basis.span_coe_eq` (coerced-basis-spans-`W`, companion of
`linearIndependent_coe_subtype`). Carrier-safe at default heartbeats. Leaf 5 (the dispatch) consumes
the `∃` by `obtain`-ing `j₀` BEFORE baking it into `re`'s corner injection, then feeds the reindexed
(`Fin (D−1) ⊕ Unit ≃ Fin D`) family as `hLI`. All gate/lint/warning/axiom-clean. Leaves 1 + 2 recap:
leaf 1 (generalize the corner-entry brick `rigidityMatrixEdge_mul_columnOp_apply_corner` to
`hv2 : .2 ≠ v`) and leaf 2 (generalize the `hA` leaf `linearIndependent_toBlocks₁₁_row_of_corner_gate`'s
`hc2 : .2 = a` to `hc2 : .2 ≠ v`).
The dispatch spike (row 480, design §(4.35)) confirmed route A composes end-to-end through `chainData_dispatch`
modulo a 5-leaf decomposition; **the wrap-edge wall DOES NOT re-surface** (kernel-probed: the `e_b` `±r`
row enters as a literal member of corner block `A`, reading `blockBasisOn` at the pin, never a span
membership) and **GAP-2 is resolved** (the `Function.update` `ends₁` override = the landed `d=3` router
pattern). Route A is assembled through the arm: the A1–A5c chain + the cert
`case_III_rank_certification_matrix` (reshaped to the (4b′) row-submatrix core) + the A6 `hblock` 0-block
kernel + the arm spine `case_III_arm_realization_matrix` (carrying `(m₁,m₂,hm₁,hm₂,re,hbot,hA,hD)` as
hypotheses, constructing `U`/`hU`/`en`/`hblock` in-body) + **BOTH** the `hD` bridge (leaf 1) **and the
`hA` bridge (leaf 2)** are LANDED, gate/axiom-clean, no `ScrewSpace` unfold. `_chain` + the route-B/4
dual-space leaves stay in tree (parallel/sound). The interior-`hρe₀` crux is CLOSED. The §(4.33)
cert-shape obstruction is structurally dissolved by (4b′).

**Dispatch decomposition (design §(4.35), the dispatch spike verdict).** `chainData_dispatch`'s interior
arm needs 5 ordered leaves: **(1)** ✅ LANDED — generalized `rigidityMatrixEdge_mul_columnOp_apply_corner`'s
corner hypothesis `.2 = a` → `.2 ≠ v` (mechanical, the `columnOp hva (Pi.single v s)` reduction reads
`blockBasisOn` at the pin for ANY second endpoint `≠ v`); **(2)** ✅ LANDED — generalized the `hA` leaf
`linearIndependent_toBlocks₁₁_row_of_corner_gate` likewise (`hc2 : .2 = a` → `hc2 : .2 ≠ v`, so it
accepts the `e_b` `±r` corner row); **(3)** ✅ LANDED — the corner `hLI` producer
`exists_corner_blockBasisOn_linearIndependent` (3a + 3b). The mkQ-quotient gate was a RED HERRING:
the `hA` leaf's `hLI` is a *uniform `blockBasisOn`-family in the full screw dual*, so 3b is the
EXISTENCE-form append-one (gate → block-incomparability → fresh `j₀` → `linearIndependent_sumElim_
candidateRow_iff` + 3a), NOT KT eq. 6.66 / Lemma 2.1 / `mkQ`; **(4)** the bottom-row producer
`dispatch_bottom_rowLI_of_IH` (genuinely-new — `hIH` row-LI submatrix of the un-operated edge matrix from
the IH; the landed `chainData_bottom_relabel` is span-shaped, WRONG shape); **(5)** the `chainData_dispatch`
wiring itself (consumes leaf 3's `∃` by obtaining `j₀` before building `re`). Leaf 4 is genuinely-new
(NOT a re-use of a landed dual-space bridge); leaf 3 was the dispatch's hardest single obligation.

**A6-assembly RECON verdict (session #33):** the arm composes sorry-free, but `hA`/`hD` are TWO
genuinely-new dual-space→matrix-row LI bridges — NOT the ~1-leaf gate facts the row-473 prose claimed.
`hD` (leaf 1) LANDED via the bottom-block op-invariance (the operated `toBlocks₂₂` IS the un-operated
`R(Gᵥ,q)` submatrix; the column op only touches the pin `v`'s coordinate). `hA` (leaf 2) LANDED via the
**dual-space→matrix-row coordinate re-wrap**: the corner block IS the coordinate matrix of the corner
block-basis functional family against `(finScrewBasis k).dualBasis` (reindexed across the singleton
`v`-column index `Equiv.uniqueProd`), so its row-LI ⟸ the dual-space gate LI via
`Matrix.linearIndependent_row_of_coordEquiv` — `whnf`-guard held (no `simp`/`whnf` on `F₀`). Both leaves
carry `(hc1/hc2/hLI)`-style structural-endpoint + dual-LI hypotheses the dispatch supplies.

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
| `R(Gab)`-bottom step 1 | `rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin` (the operated `e_b`-row (FIRST endpoint `=v`, SECOND `≠v`) off-`v` entry = the un-operated `hingeRow a b ρ (single body s)` = `R(Gab,q)`'s `ab`-row read; the (4.40) make-or-break entry equality, single all-off-`v`-columns lemma, NO span membership) | `Concrete.lean` |
| `R(Gab)`-bottom step 2 (matrix-shape half) | `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` (the operated bottom block over a MIXED bottom — each row `.2 ≠ v`, FIRST endpoint `= v` (the `e_b` row) OR `≠ v` (the `Gv` rows) — entrywise = `Matrix.of` of the **`a`-shifted** `hingeRow` reads: `e_b` rows read `hingeRow a (.2)`, off-`v` rows read un-operated `hingeRow (.1) (.2)`; the bookkeeping foundation the `R(Gab)` bottom rewrites through; col reduced via `hcol := simp [columnSplit]`, branches via step-1 + `_apply_off_pin`; NO span membership) | `Concrete.lean` |
| `R(Gab)`-bottom step 2 (extensor-identity BRIDGE, now CROSS-LABEL) | `hingeRow_mem_rigidityRows_of_supportExtensor_eq` (framework-general, `Basic.lean`) + its `blockBasisOn`-keyed specialization `hingeRow_blockBasisOn_mem_rigidityRows_of_supportExtensor_eq` (`Concrete.lean`), **both generalized 2026-06-25 to DISTINCT labels `e₁ e₂`**: a block row `r ∈ F₁.hingeRowBlock e₁` + a link `F₂.IsLink e₂ u v` with `F₁.supportExtensor e₁ = F₂.supportExtensor e₂` ⟹ `hingeRow u v r ∈ F₂.rigidityRows`. The cross-label case `e₁≠e₂` is the `e_b`→`e₀` row (`e_b ∉ E(Gab)`; routes into the fresh `e₀=(a,b)`, `hsupp` from `caseIIICandidate_supportExtensor_reproduced` at `t=0`). Same-label `e₁=e₂` subsumes the original Phase-23c form (1 caller in `Candidate.lean` dropped a `(e := …)` named-arg). NO span membership beyond the row's own | `Basic.lean`/`Concrete.lean` |
| `R(Gab)`-bottom step 3 **L-span** | `span_range_hingeRow_blockSpanning_eq_rigidityRows` (`Basic.lean`, framework-general): for a per-edge block-spanning family `B : β → ι → Dual ℝ (ScrewSpace k)` (each `B e i ∈ F.hingeRowBlock e`, `span (range (B e)) = F.hingeRowBlock e` per edge) + a link selector `ends`, `span (range fun (⟨e,_⟩,i) => hingeRow (ends e).1 (ends e).2 (B e i)) = span F.rigidityRows`. The arbitrary-spanning-family generalization of `span_range_rigidityRowFunEdge` (which fixes `B = F.blockBasisOn`) — needed because the `R(Gab)`-bottom rows route `F₁`'s `blockBasisOn` into `F₂ = splitOff`'s blocks via the cross-label bridge. Proof: `le_antisymm`; `≤` per-row rigidity-row membership; `≥` push `r ∈ block = span (range (B e))` through the linear `(screwDiff u v).dualMap` via `Submodule.span_induction` (the generators are `± bottom-rows`, `hingeRow_swap` for the orientation flip). NO `ScrewSpace` unfold; axiom-clean | `Basic.lean` |
| `R(Gab)`-bottom step 3 **L-rank** | `rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom` (`Concrete.lean`): the operated (6.64) MIXED bottom block `toBlocks₂₂` (same `hbot1`/`hbot2` as `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`) has `Matrix.rank` = `finrank (span (range wfun))`, `wfun` the `a`-shifted bottom-row functionals (= `R(Gab,q)`'s genuine rows). Proof: rewrite `toBlocks₂₂` to the `mixedBottom` `Matrix.of` form (off-`v` columns), recognize it as the off-`v` submatrix of the **full** product-column `Nfull := Matrix.of (dualProductCoordEquiv ∘ wfun)`, drop the zero `v`-columns (mirror `rank_submatrix_inr_of_zero_left_cols`, each `wfun i` blind to body `v`), `rank_reindex` for the surviving reindex, then `Matrix.rank_of_coordEquiv`. NO span membership; NO `ScrewSpace` unfold; axiom-clean | `Concrete.lean` |
| `R(Gab)`-bottom step 3 **L-hD** | `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` (`Concrete.lean`): same `hbot1`/`hbot2` + the IH count `hrank : finrank (span (range wfun)) = #m₂` ⟹ the operated (6.64) bottom block `toBlocks₂₂` is row-LI. Proof: `linearIndependent_rows_iff_rank_eq_card` (landed) reduces to `toBlocks₂₂.rank = #m₂`, L-rank rewrites that rank to the span finrank, `hrank` closes. The `R(Gab)`-bottom analogue of `linearIndependent_toBlocks₂₂_row_of_off_pin`, but the IH enters as a *rank count* `hrank` (the matrix-equality form is BLOCKED). NO span membership; NO `ScrewSpace` unfold; axiom-clean | `Concrete.lean` |
| zero-left-col support (mirror) | `Matrix.linearIndependent_row_of_zero_left_cols` + `Matrix.rank_submatrix_inr_of_zero_left_cols` (`Mathlib/LinearAlgebra/Matrix/Rank.lean`): dropping all-zero `Sum.inl` columns of `N : Matrix m (n₁⊕n₂) R` preserves row-LI / rank (the off-`v`-column drop in L-rank/L-hD). LI via `Sum.elimZeroLeft` injective (`ker = ⊥`); rank via `rank_eq_finrank_span_cols` column-span `le_antisymm`. FRICTION [mirrored]. Axiom-clean | `Rank.lean` |
| A6 `hA` (leaf 2) | `linearIndependent_toBlocks₁₁_row_of_corner_gate` (the `hA` bridge: corner-rows-record-`.1=v` `hc1` + `.2≠v` `hc2` (relaxed from `=a` by dispatch leaf 2, so it covers the `e_b` `±r` corner row too) + dual-space corner block-basis-functional LI `hLI` ⟹ `toBlocks₁₁.row` LI; proof = `ext` the corner block to `Matrix.of (coordEquiv ∘ family)` via `…_apply_corner` + the singleton-`v`-column `coordEquiv := (finScrewBasis k).dualBasis.equivFun` reindexed by `Equiv.uniqueProd`, then `Matrix.linearIndependent_row_of_coordEquiv`; §38 whnf-guard held) | `Concrete.lean` |
| A6 ARM SPINE | `case_III_arm_realization_matrix` (`ForkedArm.lean`, route-A sibling of `_chain`: carries `(m₁,m₂,hm₁,hm₂,re,hbot,hA,hD)`, constructs `U`/`hU`/`en`/`hblock` in-body, calls the cert + the route-agnostic tail; conclusion byte-identical to `_chain`) | `ForkedArm.lean` |
| dispatch leaf 3a | `linearIndependent_blockBasisOn_screwDual` (per-edge block-basis functionals `fun j => (blockBasisOn hgp he j : Dual ℝ (ScrewSpace k))` LI in the screw dual — the `e_a` `D−1` half of the corner `hLI` family) via the new generic mirror `Module.Basis.linearIndependent_coe_subtype` (carrier-safe `Basis.linearIndependent.map' W.subtype` factored over abstract `V`) | `Concrete.lean` / `Mathlib/LinearAlgebra/Dimension/Constructions.lean` |
| dispatch leaf 3b | `exists_corner_blockBasisOn_linearIndependent` (the cross-hinge corner `hLI`, EXISTENCE-form `∃ j₀, LinearIndependent ℝ (Sum.elim (e_a block basis) (blockBasisOn hgp hb j₀))` from the two FIXED-`ρ₀` gates `hρeb`/`hρe₀`; bypasses the `mkQ` gate: gate → block-incomparability (`mem_hingeRowBlock_iff`) → fresh `e_b` basis vector → append-one via `linearIndependent_sumElim_candidateRow_iff` + leaf 3a; the `r∈block_b ⟹ r∈block_a` step routes through `LinearMap.applyₗ`'s kernel via `span_le`) + new mirror `Module.Basis.span_coe_eq` (coerced-basis-spans-`W`) | `Concrete.lean` / `Mathlib/LinearAlgebra/Dimension/Constructions.lean` |

Everything is carrier-agnostic — **no `ScrewSpace` unfolding** anywhere (route A's escape from the
§(4.18)–(4.30) span-membership wall: KT's (6.61) is a unit-det right-multiply, never a membership).

## Remaining work in Phase 23

1. **The general-`d` rank certification — route A (concrete `Matrix`).** ✅ The A1–A5c chain + the cert
   (reshaped to the (4b′) row-submatrix core) + the (4b′) kernel + the A6 `hblock` 0-block kernel + the
   arm spine `case_III_arm_realization_matrix` + the `hD` bridge (leaf 1) + the `hA` bridge (leaf 2) are
   all LANDED (full inventory: *Current state* table). The cert's two carried LI hypotheses now both
   have producing leaves. **NEXT = the dispatch (item 2)** discharges `(re, hbot, hA, hD)` from the
   `ChainData` interior split + wires the arm. `_chain` + the route-B/4 dual-space leaves stay in tree
   (sound in isolation — the dual-space approach the wall closed; do not build on them). The
   interior-`hρe₀` crux is CLOSED.
2. **CHAIN-2c-iii `chainData_dispatch`** — the general-`k` `Fin cd.d` router (base/`d=3` via
   `chainData_split_realization`; interior `2 ≤ i < d` via the route-A arm). **DISPATCH LEAVES 1, 2,
   3 (3a+3b) LANDED** (leaf 1: the corner-entry brick `rigidityMatrixEdge_mul_columnOp_apply_corner`
   generalized to `.2 ≠ v`; leaf 2: the `hA` leaf `linearIndependent_toBlocks₁₁_row_of_corner_gate`
   relaxed likewise; leaf 3: `exists_corner_blockBasisOn_linearIndependent`, the corner `hLI` producer
   3a+3b, the EXISTENCE-form gate→block-incomparability→fresh-`j₀` argument that bypasses the `mkQ`
   gate); NEXT = leaf 4 (`dispatch_bottom_rowLI_of_IH`, the bottom-row producer). The `ChainData`
   interior-split accessors are landed and reusable: `removeVertex_isLink_edge_succ_pred_off`
   (`Induction/Operations.lean`, the off-slot input), the interior-`hρe₀` chain
   `interior_hρe₀_of_baseWidening`/`_of_widening` (`CaseIII/Relabel/ForkedArm.lean`, the dispatch reads
   `hρe₀` off LEAF-3's `hedgeGv` in one call), and LEAF-3
   `exists_shared_redundancy_and_matched_candidate` (`CaseIII/Realization.lean`, re-exposes `hedgeGv`).
   Folds into A6. Decomposed into 5 leaves by the dispatch spike (design §(4.35)). GAP 2 RESOLVED:
   the `ends`-orientation pins use the `Function.update` override `ends₁` (= the landed `d=3` router
   `chainData_split_realization` pattern, `Realization.lean:1159`); no motive/contract change.
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
§(4.31)–(4.34)). Route A is fully assembled through the arm spine + BOTH the `hD` (leaf 1) and `hA`
(leaf 2) bridges — all gate/lint/warning/axiom-clean (`[propext, Classical.choice, Quot.sound]`), no
`ScrewSpace` unfold. `_chain` + the route-B/4 leaves stay in tree (parallel/sound). The §(4.33)
cert-shape obstruction is structurally dissolved by (4b′). The arm carries `(re, hbot, hA, hD)` as
hypotheses (the standing carry-the-crux idiom); the dispatch (item 2) discharges them.

**NEXT = step 4 (re-point the cert/arm/dispatch to `splitOff`) → leaf 5 (the dispatch wiring).** The
`hD` step-3 reshape via the RANK route is **fully landed** (the matrix-equality form stays BLOCKED;
see *Current state*) — all three leaves L-span/L-rank/L-hD plus the two zero-left-col mirror support
facts closed 2026-06-25:

- **✅ L-span — LANDED** as `span_range_hingeRow_blockSpanning_eq_rigidityRows` (`Basic.lean`,
  framework-general). The arbitrary-`B` generalization of `span_range_rigidityRowFunEdge` (`B =
  F.blockBasisOn` fixed), needed because the `R(Gab)`-bottom rows route `F₁`'s `blockBasisOn` into
  `F₂ = splitOff`'s blocks via the cross-label bridge. (Was the substantive leaf.)
- **✅ L-rank — LANDED** as `rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom` (`Concrete.lean`):
  `M.toBlocks₂₂.rank = finrank (span (range wfun))`, `wfun` the `a`-shifted bottom functionals. The
  off-`v`-column bottom block IS the off-`v` submatrix of the **full** product-column `Nfull =
  Matrix.of (dualProductCoordEquiv ∘ wfun)`; drop the zero `v`-columns (mirror
  `rank_submatrix_inr_of_zero_left_cols`), `rank_reindex`, then `Matrix.rank_of_coordEquiv`.
- **✅ L-hD — LANDED** as `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` (`Concrete.lean`):
  `LinearIndependent ℝ M.toBlocks₂₂.row` from the IH count `hrank : finrank (span (range wfun)) = #m₂`,
  via `Matrix.linearIndependent_rows_iff_rank_eq_card` + L-rank. The IH enters as the *rank count*
  `hrank` (carried as a hypothesis, the standing carry-the-crux idiom) — NOT the matrix-equality form.

**Step 4 (NEXT concrete commit):** re-point the cert/arm/dispatch `re` + `hm₂` from `removeVertex` to
`splitOff`, including the `e_b` row in `m₂`, and instantiate L-hD's `hrank` from the split-off
framework's full-rank realization. The dispatch supplies `hrank` from `finrank (span F₂.rigidityRows)
= D·(|V_Gab|−1) = #m₂` (`hsplitGP`'s `HasGenericFullRankRealization` at `Gab.deficiency n = 0`, +
`V(Gab).ncard = V(Gv).ncard`) composed with L-span (which equates the bottom rows' span to `span
F₂.rigidityRows`). `F₂ = Q.toBodyHinge` (the IH framework from `hsplitGP`), NOT a fresh build — reuse
the `case_III_candidate_dispatch` `Q`-unpacking pattern (`Realization.lean:302`).

The fork-decider recon (row 488, 7 kernel-clean theorems) +
coordinator primary-source read RESOLVED the route: KT's proof is SOUND, the project's `columnOp` IS
KT's (6.61) (`col_a += col_v`), and the wall was a formalization artifact — the §(4.39) spike tested the
CORNER edge `e_a = vᵢvᵢ₊₁` (correctly 0 off-`v`); KT routes the OTHER `v`-incident edge `e_b = vᵢ₋₁vᵢ`
to the `e₀=(a,b)` bottom fill. The cert's `hbot` (both
endpoints `≠ v`) wrongly EXCLUDED the `v`-incident `e_b` row (off-`v`-supported only AFTER the op);
including it makes the bottom the full-rank `R(Gab)`.

**RESHAPE PLAN (~3–5 commits left, design §(4.40); SUPERSEDES the §(4.36)/(4.37)/(4.39) "walls"):**
1. **✅ LANDED** the operated `e_b`-row off-`v` entry equality
   `rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin` (`Concrete.lean`): a single all-off-`v`-columns
   lemma subsuming the spike's `operated_eB_at_{a,b}_col` cases — the operated `e_b` entry =
   `hingeRow a b ρ (single body s)`, i.e. the un-operated `ab`-row read (`gab_ab_row` is then just
   `hingeRow_apply`). `b ≠ a` is NOT needed here (genuineness enters only in step 2's extensor half).
2. **✅ matrix-shape half + extensor-identity BRIDGE (now CROSS-LABEL) LANDED.** Matrix-shape:
   `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` (`Concrete.lean`). Extensor-identity bridge:
   `hingeRow_mem_rigidityRows_of_supportExtensor_eq` (`Basic.lean`) + its `blockBasisOn` specialization
   (`Concrete.lean`), **generalized 2026-06-25 to distinct labels `e₁ e₂`** so the `e_b`→`e₀` row routes
   (the original `e_b ∉ E(Gab)`, so the read-block label `e_b ∈ F₁` and the link label `e₀ ∈ F₂` differ;
   `hsupp` from `caseIIICandidate_supportExtensor_reproduced` at `t=0`). Same-label `e₁=e₂` subsumes the
   prior Phase-23c form.
3. **✅ LANDED** the `hD` leaf via the RANK route (the matrix-equality form
   `submatrix_columnOp_toBlocks₂₂_eq_Gab` is BLOCKED on the un-provable `blockBasisOn`-equality `hblk` —
   *Current state*): the three leaves L-span / L-rank / L-hD (`Basic.lean` + `Concrete.lean`) + the two
   zero-left-col mirror support facts (`Rank.lean`), drawing `M.toBlocks₂₂.rank = #m₂` from the IH
   `R(Gab)` full rank via the bottom rows' span = `span F₂.rigidityRows` (L-hD carries the `= #m₂` count
   `hrank` as a hypothesis, the dispatch instantiates it in step 4).
4. **(NEXT)** re-point the cert's `Gv`/`hm₂` + the arm/dispatch `re` from `removeVertex` to `splitOff`,
   including the `e_b` row in `m₂`, instantiating L-hD's `hrank` from the split-off framework.
Single-matrix CONFIRMED (corner + bottom both submatrices of the one operated `R(G,pᵢ)*U`; the A4 bridge
applies as-is). No motive/IH/contract change (IH consumed on `splitOff` instead of `removeVertex`).

The CORNER leaves are done + sound + REUSED intact: **Leaf 3 (3a+3b) is LANDED** as
`exists_corner_blockBasisOn_linearIndependent` (the corner `hLI` producer, EXISTENCE-form, the mkQ-lift
was a RED HERRING — uniform `blockBasisOn`-family, gate → block-incomparability → fresh `j₀` →
`linearIndependent_sumElim_candidateRow_iff` + leaf 3a); leaf 5 (the dispatch) consumes the `∃` by
`obtain`-ing `j₀` before baking it into `re`'s corner injection. All landed corner leaves (1,2,3) stay in
tree + reusable under either bottom-block option.

**Then (after the bottom-block resolution) leaf 5** — the `chainData_dispatch` wiring (case-splits
`(i:ℕ)`: `i≤1` → landed `chainData_split_realization`; `2≤i` → the route-A arm; obtains leaf 3's `j₀`,
builds `re`, reads `hρe₀` off `interior_hρe₀_of_baseWidening`, discharges the geometric hyps via the `d=3`
`hne_F₀` pattern). The interior-`hρe₀` chain + the `ChainData` accessors are landed + reusable (item 2).
Then CHAIN-5 (wire into the spine), ENTRY + ASSEMBLY (parallel-safe).

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

- **`R(Gab)`-BOTTOM RESHAPE STEP 3 L-rank + L-hD LANDED → the `hD` RANK route is COMPLETE (2026-06-25,
  `Concrete.lean` + `Rank.lean`).** The two remaining `hD` leaves, closing the RANK route the §(4.40)
  spike scoped (the matrix-equality form stays BLOCKED). **L-rank**
  `rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom`: the operated (6.64) MIXED bottom block
  `toBlocks₂₂` has `Matrix.rank = finrank (span (range wfun))`, `wfun` the `a`-shifted bottom functionals.
  The key move dodging the column-restriction (the bottom block lives on the off-`v` columns
  `{body≠v}×Fin D`, NOT the full `α×Fin D` that `Matrix.rank_of_coordEquiv` needs): recognize it as the
  off-`v`-column submatrix of the **full** `Nfull = Matrix.of (dualProductCoordEquiv ∘ wfun)`, whose
  dropped `v`-columns are ZERO (each `wfun i` reads `S(≠v) − S(≠v)`, blind to body `v`); drop them with
  the new mirror `Matrix.rank_submatrix_inr_of_zero_left_cols`, `rank_reindex` the surviving reindex,
  then `Matrix.rank_of_coordEquiv`. **L-hD** `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`:
  row-LI of `toBlocks₂₂` from the IH count `hrank : finrank (span (range wfun)) = #m₂`, via the landed
  `Matrix.linearIndependent_rows_iff_rank_eq_card` + L-rank. The IH enters as the *rank count* `hrank`
  (carry-the-crux), NOT the BLOCKED matrix equality. Both axiom-clean; the two zero-left-col mirror
  support facts → FRICTION [mirrored]. NEXT = step 4 (re-point cert/arm/dispatch to `splitOff`,
  instantiate `hrank`).
- **L-span (the spanning equality)** `span_range_hingeRow_blockSpanning_eq_rigidityRows` (2026-06-25,
  `Basic.lean`): the arbitrary-`B` block-spanning generalization of `span_range_rigidityRowFunEdge`
  (needed because the `R(Gab)`-bottom rows route `F₁`'s `blockBasisOn` into `F₂`'s blocks via the
  cross-label bridge); `≥` via `Submodule.span_induction` through `(screwDiff u v).dualMap`. Axiom-clean,
  no FRICTION. Was the substantive `hD`-route leaf; consumed by step 4's `hrank` instantiation.
- **`R(Gab)`-BOTTOM RESHAPE STEP 2 BRIDGE GENERALIZED to CROSS-LABEL + the matrix-equality form FLAGGED
  BLOCKED (2026-06-25, `Basic.lean` + `Concrete.lean`).** A compiler-grounded spike (kernel-checked,
  banked) settled the assembly route. (1) The bridge `hingeRow_mem_rigidityRows_of_supportExtensor_eq`
  (+ its `blockBasisOn` specialization) is now stated over **distinct labels `e₁ e₂`** — a block row
  `r ∈ F₁.hingeRowBlock e₁` + a link `F₂.IsLink e₂ u v` with `F₁.supportExtensor e₁ = F₂.supportExtensor e₂`
  ⟹ `hingeRow u v r ∈ F₂.rigidityRows` (one-line; the block depends only on the extensor). This is
  required because the `e_b`→`e₀` row reads the block at `e_b ∈ E(F₁)` (which does NOT survive the
  splitting-off) but links at the fresh `e₀ ∈ E(F₂)` — coordinator finding 3, verified. Same-label
  subsumes the Phase-23c form (1 caller dropped a `(e := …)` named-arg). (2) **FLAG:** the
  matrix-equality assembly `submatrix_columnOp_toBlocks₂₂_eq_Gab` (`M.toBlocks₂₂ =
  F₂.rigidityMatrixEdge.submatrix …`) is BLOCKED — the residual goal needs equal *chosen* basis vectors
  `F₁.blockBasisOn = F₂.blockBasisOn`, false for `finBasisOfFinrankEq` on term-distinct submodules.
  Sound route = RANK (`linearIndependent_rows_iff_rank_eq_card`, final step kernel-verified):
  `M.toBlocks₂₂.rank = #m₂` from the IH `R(Gab)` rank via the bottom rows' span = `span F₂.rigidityRows`.
  Three new leaves L-span/L-rank/L-hD (*Hand-off*). Gate/lint/warning-clean; axiom-clean
  (`[propext, Classical.choice, Quot.sound]`, `#print axioms` via `lake env lean`; `lean_verify`'s
  `sorryAx` was a stale-cache false positive — the warning-clean build is authoritative).
- **`R(Gab)`-BOTTOM RESHAPE STEP 2 (matrix-shape half) LANDED —
  `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` (2026-06-25, `Concrete.lean`).** Generalizes
  `submatrix_columnOp_toBlocks₂₂_eq` to a MIXED bottom: each bottom row's SECOND endpoint `≠ v`
  (`hbot2`) and its FIRST endpoint is `= v` (the `e_b` split row) OR `≠ v` (a `Gv` row) (`hbot1`, a
  per-row disjunction). The operated `toBlocks₂₂` (FIXED-pin col reindex `(columnSplit v).symm`)
  entrywise = `Matrix.of` of the **`a`-shifted** `hingeRow` reads (`if .1 = v then a else .1`): off-`v`
  rows read their un-operated `hingeRow (.1) (.2)` (the column op is invisible — step-1 sibling
  `_apply_off_pin`), the `e_b` row reads `hingeRow a (.2)` (step 1
  `rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin`). The matrix-bookkeeping foundation the `R(Gab)`
  bottom rewrites through. Proof: reduce the bottom column `(columnSplit v).symm (Sum.inr (⟨b,hb⟩,c))`
  to `(b,c)` ONCE via `hcol := by simp [columnSplit]` (cleaner than the existing lemma's leave-it-abstract
  RHS, because the shifted-read RHS needs the reduced column), then `rcases hbot1` + the two `rw`
  branches. NO span membership; NO `ScrewSpace` unfold; axiom-clean. NEXT = step 2's extensor-identity
  half (match the reads to `R(Gab,q)`'s genuine rows via a `splitOff` framework + the reproduced-slot
  extensor equality). No FRICTION (clean `simp`/`rcases`/`rw`).
- **DISPATCH LEAF 3b LANDED + THE mkQ RED-HERRING CORRECTION —
  `exists_corner_blockBasisOn_linearIndependent` + the mirror `Module.Basis.span_coe_eq` (2026-06-25,
  `Concrete.lean` + `Mathlib/LinearAlgebra/Dimension/Constructions.lean`).** The corner `hLI` producer,
  EXISTENCE-form `∃ j₀, LinearIndependent ℝ (Sum.elim (e_a block basis) (blockBasisOn hgp hb j₀))`. A
  read-only spike (verdict accepted by coordinator) caught that **the recon's mkQ-quotient-lift framing
  was a RED HERRING**: the `hA` leaf's `hLI` is a *uniform `blockBasisOn`-family in the full screw dual*
  (every corner row, incl. the reproduced `±r`, reads `blockBasisOn` at the pin via
  `rigidityMatrixEdge_mul_columnOp_apply_corner`), NOT a span/quotient/Lemma-2.1 object. So 3b bypasses
  `linearIndependent_mkQ_corner_of_gate` entirely: the two FIXED-`ρ₀` gates the dispatch carries
  (`hρeb : ρ₀ ∈ hingeRowBlock e_b`, `hρe₀ : ρ₀(C(e_a)) ≠ 0`) make the two hinge-row hyperplanes
  *incomparable* (`mem_hingeRowBlock_iff`), so *some* `e_b` basis vector escapes `e_a`'s block, and
  append-one (`linearIndependent_sumElim_candidateRow_iff` + leaf 3a) closes it. The `r∈block_b ⟹
  r∈block_a` step routes through `LinearMap.applyₗ (C(e_a))`'s kernel via `span_le` (the new mirror
  `span_coe_eq`). Carrier-safe at default heartbeats; leaf 5 consumes the `∃` by `obtain`-ing `j₀`.
  Friction → FRICTION [mirrored] (`span_coe_eq`). Gate/lint/warning/axiom-clean.
- **DISPATCH LEAF 3a LANDED — `linearIndependent_blockBasisOn_screwDual` + the carrier-safe generic
  mirror (2026-06-25, `Concrete.lean` + `Mathlib/LinearAlgebra/Dimension/Constructions.lean`).** The
  within-block `e_a` half of the corner `hLI` family: the per-edge block-basis functionals
  `fun j => (blockBasisOn hgp he j : Dual ℝ (ScrewSpace k))` are LI in the screw dual. The inline
  `Basis.linearIndependent.map' W.subtype` blew the 200000-heartbeat budget at the concrete
  `Module.Dual ℝ (ScrewSpace k)` carrier, and NO §38 in-proof medicine helped (`set`/`clear_value`,
  `linearIndependent_iff'` finset-form, `Subtype.ext`/`coe_eq_zero` all still tipped — the `whnf` is
  intrinsic to `.map'`'s instance unification with the concrete codomain). Fix: factored the `.map'`
  into a **generic-over-`V` mirror** `Module.Basis.linearIndependent_coe_subtype` (the named-family
  complement of `exists_linearIndependent_fin_of_finrank_eq`, beside it in the same mirror file); the
  call site applies it at the heavy carrier with the unification already discharged. Friction + idiom →
  FRICTION [mirrored] + TACTICS-QUIRKS § 38 new sub-case. Gate/lint/warning/axiom-clean.
- **DISPATCH LEAF 2 LANDED — relaxed `linearIndependent_toBlocks₁₁_row_of_corner_gate`'s `hc2` to
  `.2 ≠ v` (2026-06-25, `Concrete.lean`).** Dropped the corner second-endpoint binder
  `hc2 : ∀ i, (ends (re (Sum.inl i)).1.1).2 = a` to `hc2 : ∀ i, … ≠ v` (kept `hc1 : .1 = v`), so the
  `hA` leaf now accepts BOTH split edges' corner rows — the `e_a` panel rows (`.2 = a`) and the
  reproduced `e_b` `±r` row (`.2 = b ≠ a`, KT eq. 6.66), the full `D × D` corner. Mechanical, as the
  leaf-1 handoff predicted: the `hmeq` `ext` already calls leaf 1's brick
  `rigidityMatrixEdge_mul_columnOp_apply_corner` (which takes `.2 ≠ v`), so the only proof change was
  passing `(hc2 i)` straight through in place of the leaf-1-era derivation `(hc2 i).symm ▸ hva.symm`.
  `a`/`hva` stay in the signature (the conclusion's `columnOp hva`). Gate/lint/warning-clean; no
  FRICTION (only a docstring long-line reflow). Unblocks leaf 3 (the corner `hLI` producer).
- **A6 `hA` LEAF (the bridge) LANDED — `linearIndependent_toBlocks₁₁_row_of_corner_gate` (2026-06-25,
  `Concrete.lean`).** The cert's `hA` from the dual-space corner LI, via the **dual-space→matrix-row
  coordinate re-wrap**: `ext` the corner block `toBlocks₁₁` to `Matrix.of (coordEquiv ∘ corner-func
  family)` (each entry via the landed `rigidityMatrixEdge_mul_columnOp_apply_corner`, given `hc1`/`hc2`:
  corner rows record endpoints `(v,a)`), where `coordEquiv := (finScrewBasis k).dualBasis.equivFun`
  reindexed across the singleton `v`-column index `{body//body=v}×Fin D ≃ Fin D` (`Equiv.uniqueProd` +
  `LinearEquiv.funCongrLeft`); then `Matrix.linearIndependent_row_of_coordEquiv` (A5b core) turns
  row-LI ⟸ the carried dual-space `hLI`. **The §38 whnf guard HELD** — no `simp`/`whnf` on `F₀`; the
  `coordEquiv` is a `LinearEquiv` (kernel ⊥) so the carrier never unfolds. Cleaner than the design's
  "port `linearIndependent_mkQ_corner_of_gate`" route (no `mkQ`/quotient detour — the corner reads at a
  single body `v`, so the panel rows + `±r` row independence factors through the screw-dual coord map
  directly). The `(hc1,hc2,hLI)` inputs are the dispatch's burden (item 2). Friction: idiom → FRICTION.
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

- **`R(Gab)`-BOTTOM RESHAPE STEP 1** `rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin` (2026-06-25)
  — the (4.40) make-or-break entry equality: the operated `e_b` row (FIRST endpoint `=v`, SECOND `≠v`)
  at any off-`v` column = the un-operated `hingeRow a (.2) ρ (single body s)` = `R(Gab,q)`'s `ab`-row
  read; single all-off-`v`-columns lemma, `b ≠ a` not used (enters step 2's extensor half), NO span
  membership. Consumed by step 2's `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`.
- **DISPATCH LEAF 1** `rigidityMatrixEdge_mul_columnOp_apply_corner` generalized to `.2 ≠ v` (2026-06-25)
  — keyed `hingeRow_comp_columnOp_apply` → direct `hingeRow_apply` + `simp only` of the
  `columnOp`/`update`/`Pi.single` reads (`columnOp hva (Pi.single v s)` zeroes every non-`v` body, so the
  read is `r s` for ANY `.2 ≠ v`); covers both `e_a` panel and `e_b` `±r` corner rows. Friction:
  missing-sibling `unusedSimpArgs` false signal → TACTICS-QUIRKS § 68.
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
- *A `Module.Basis`-vector's submodule-membership proof is `(basis j).property` (or `.2`), not
  `.coe_mem` — `Subtype.coe_mem` is not in this environment* → FRICTION [idiom].
- *An inline `Basis.linearIndependent.map' W.subtype` to coerce a *named* submodule basis into a heavy
  carrier `whnf`-blows the budget and no in-proof §38 medicine helps; factor the `.map'` into a
  generic-over-`V` mirror (`Module.Basis.linearIndependent_coe_subtype`)* → TACTICS-QUIRKS § 38 new
  sub-case + FRICTION [mirrored].
- *An `unusedSimpArgs` warning can be a false signal — a missing *sibling* lemma stalled `simp` upstream
  of the flagged arg; read the post-`simp` goal and *add* the sibling (the dual `Pi.single_eq_of_ne`
  case), don't drop the named arg* → TACTICS-QUIRKS § 68.
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
- *dual-space→matrix-row LI bridge: rewrite the block to `Matrix.of (coordEquiv ∘ family)` then
  `(Matrix.linearIndependent_row_of_coordEquiv coordEquiv _).2 hLI`; never `simp`/`whnf` the carrier
  (the §38 guard). The standing route-A pattern for `hA`/`hD`* → FRICTION [idiom].
- *The deferred-hypothesis-satisfiability trap recurs at COMPOSITION and at the ARM-ASSEMBLY consumer (not
  only leaf hypotheses); a wall recurring across structurally-different fixes is intrinsic to a shared
  downstream object; for a route-composition crux in the defeq-fragile zone, spike-before-build beats
  build-then-BLOCK even when a prior recon "settled" it* → model-experiment Findings (rows 449–455,
  457–473, 477–478) + DESIGN.md *Constructibility recon*. Full per-route kernel traces (§(4.18)–(4.34))
  live in `Phase23-design.md`.
