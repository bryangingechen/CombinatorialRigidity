# Phase 23e — Case III general `d`: the KT-faithful rank certificate (work log)

**Status:** in progress. Opened 2026-06-26 (as the general-`k` dispatch + CHAIN-5); **RE-SCOPED the
same day** to the **KT-faithful rank certificate** after the `R(Gab)`-reproduction feasibility spike
returned a kernel-grounded NO-GO and the user chose to pursue the genuinely-new certificate (complete
formalization of KT is the goal; fallback (C) / freeze-at-`d=3` declined). **Phase 23 stays in progress**;
23e is the *fourth* CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d + 23e). The authoritative recon + plan is
**`notes/Phase23-design.md` §(4.48)** (the spike verdict, the dual-orientation obstruction, the
Schur-complement route, the `mixedBottom` lever, the cert-before-dispatch plan); this note carries the
current state, the leaf checklist, blockers, and hand-off, and points there. Program map:
`notes/MolecularConjecture.md`.

## Current state

**WALL found (design §(4.53), step-3b matrix-assembly spike, kernel-checked). The forked cert
`case_III_rank_certification_zero₁₂` is NOT consumable from the landed geometry**, and the §(4.52) "remaining =
ASSEMBLY, no new math" framing is REFUTED. **Next step = adjudication + two genuinely-new LEAF-RowOp leaves**
(below), NOT the literal `U`/`re`/`en`/`hblock` assembly the prior hand-off named. Item (3a) (the cert + scaffolding)
and the `hA`-half (3b) (`corner_hA'_of_gate`) are LANDED axiom-clean — but they do NOT compose to the cert:

- The cert's `hblock : (rigidityMatrixEdge * U).submatrix re en = fromBlocks A 0 C D` demands an **UPPER-right-zero**
  block. The only landed `U` (the column op) produces the **LOWER-left-zero** shape `fromBlocks A B 0 D`, with the
  upper-right `B` (the `±r`/`e_b` corner row's off-`v` `ab`-fill) **GENERICALLY NONZERO** — kernel residual: one
  `rw [rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin]` reduces the upper-right-zero claim to
  `hingeRow a b ρ (Pi.single body s) = 0`, false in general. No reindex `(re, en)` rescues it (the cert's
  `hm₁ : card m₁ = screwDim k` PINS `m₁` to the corner, whose only zero column block is empty).
- The §(4.49)–(4.52) "row op zeros the upper-right `B`" plan needs a **LEFT row-op `L`** that (a) is NOT in tracked
  source (only the reverted `Spike49`/`Spike49c`) and (b) cannot be expressed inside `(M * U)` (a RIGHT multiply only).
- `corner_hA'_of_gate` (the ρ₀-augmented `[blockBasisOn(e_a); ρ₀]` family) does **NOT** feed the cert's `hA`: the only
  landed corner→`A.row` bridge (`linearIndependent_toBlocks₁₁_row_of_corner_gate`) takes a PLAIN `m₁`-indexed
  `blockBasisOn` family — ρ₀ is not a `blockBasisOn` vector. ρ₀ only becomes the corner's `D`-th row AFTER the absent
  left row op. So `corner_hA'_of_gate` is a landed dual-space fact with NO consumer until the row op lands.

**What DOES compose (kept honest):** `hD` reads off `mixedBottom` exactly (`linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`,
conditional on the IH `hrank`); the cardinalities ground out (`columnSplit_corner_card = screwDim k = finrank ScrewSpace`).
But both compose only for the LOWER-left-zero `_matrix` cert, not `_zero₁₂`.

Nothing is mid-stream; tree clean. `d=3` stays fully green (zero-regression, hard constraint).
The landed `chainData_arm_realization_sep` wrapper parks in **23f** until the sound cert is wired through.

## Architectural choices made up front

- **Cert before dispatch.** The dispatch consumes the cert, so the cert (23e) precedes the general-`k`
  dispatch + CHAIN-5 (now **23f**), ENTRY (**23g**), ASSEMBLY (**23h**) — codes-until-open. 23d's "rank-cert
  scope CLOSED" was premature (the §(4.38) `R(Gab)`-dissolves-the-wall claim was unspiked; §(4.44) refuted it),
  so the cert work genuinely re-opens here.
- **Below the CHAIN↔ENTRY contract + the motive/IH.** The cert + arm are infrastructure beneath the dispatch
  (C.3) and the `ChainData` record (C.1); the reshape does not touch the `hdispatch` consume-shape or the
  0-dof motive (§I.8.21 re-verified). The frozen interface (C.0–C.6) + the sanctioned C.3 `hIH` addition stay
  valid for 23f.
- **`d=3` zero-regression via a cert FORK** (recon-decided, §(4.49)). The `d=3` wrapper keeps the current
  `_matrix`/M₃ path; only the general-`d` arm routes through the new `case_III_rank_certification_zero₁₂`. Clean
  separation, zero `d=3` risk — do NOT try to unify the two.

## Lemma checklist

Per design §(4.48) plan. The cert work (items 1–4); the dispatch/CHAIN-5/ENTRY/ASSEMBLY are 23f+.

- [x] **(1) Cert-shape design recon** (DONE, design §(4.49)) — VERDICT GO: the third shape `fromBlocks A 0 C D`
  (zero UPPER-right, A3-transposed), NOT the Schur-complement route (which zeros `C` and mutates the bottom).
  The bottom is the LANDED full-rank `mixedBottom` block; the row op zeros `B` (corner off-`v`), leaving the
  bottom untouched; the genuinely-new content localizes to the corner `hA'` (union-dimension `Mᵢ`-invertibility).
- [x] **(2) Construct-or-concede de-risk spike** (DONE, design §(4.50)) — the A3-transposed SCAFFOLDING goes
  sorry-free (A3-transposed mirror + the row-op machinery `rowOp_isUnit_det`/`rowOp_zeroes_upperRight` + the
  `mixedBottom` bottom), but the genuinely-new content RELOCATED INTACT into the corner `hA'` (NOT the landed
  `d=3` discriminator). Convergence verdict: the crux is KT's union-dimension `Mᵢ`-invertibility, irreducible.
- [x] **(2b) Focused structural recon on `hA'` / the `Mᵢ` row-structure** (DONE, design §(4.51)) — VERDICT GO,
  and §(4.50)'s "hardest single argument" framing was STALE: KT's union-dimension `Mᵢ`-invertibility (6.65–6.67)
  is ALREADY LANDED at general `d` (the discriminator + callees are `{k : ℕ}`, `Claim612.lean` sorry-free, fired
  by the landed `exists_shared_redundancy_and_matched_candidate`). The §(4.50) collapse was a generic-`L₀`
  artifact; KT's `λ` (LEAF-3) gives the clean `Mᵢ = [r(Lᵢ); ±r]`. Remaining = ASSEMBLY, not new math.
- [x] **(2c) Wiring spike** (DONE — GO, design §(4.52)) — kernel-confirmed the LEAF-3-`λ` → `A' = Mᵢ` →
  discriminator `hA'` route-composition reduces to landed facts + LEAF-3 outputs with no new hypothesis. The
  §(4.50) concede is dissolved by `Gv_row_pin_zero`. Two sorry-free facts built: `corner_hA'_of_gate`,
  `Gv_row_pin_zero`. De-risking arc complete.
- [x] **(3a) Build the forked general-`d` cert** (DONE, axiom-clean) — `case_III_rank_certification_zero₁₂`
  (`CaseIII/Candidate.lean`) consumes the A3-transposed `fromBlocks A 0 C D` matrix block data + `hA`/`hD` and
  fires the A5c-transposed composition core, certifying the full target rank `D(|V(G)|−1)`. Its A3-transposed
  scaffolding re-created as tracked Lean: `rank_fromBlocks_zero₁₂_ge_of_linearIndependent_rows` +
  `rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` (`Rank.lean`); the rigidity-matrix bridge
  `finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks_zero₁₂` (`Concrete.lean`). `d=3` keeps the
  `_matrix`/M₃ path (zero-regression); the cert is the general-`d` arm's slot only.
- [~] **(3b) the literal `re`/`L₀` construction — WALL (design §(4.53))** — the cert is NOT consumable from the
  landed geometry: it needs an UPPER-right-zero `hblock`, the column op gives LOWER-left-zero (upper-right `B`
  nonzero, kernel-checked), and the LEFT row op that would fix it is (a) absent from tracked source and (b) not
  expressible in `(M * U)`. `corner_hA'_of_gate` is landed but has NO consumer (the cert's `hA` bridge takes a plain
  `blockBasisOn` family, not the ρ₀-augmented one). Two genuinely-new LEAF-RowOp leaves + a cert reshape owed
  (below). `hD`/cardinalities compose (but only for the lower-left-zero `_matrix` cert).
- [ ] **(3b′) LEAF-RowOp-1/2** (next concrete commit, design §(4.53)) — re-create the two reverted `Spike49` row-op
  LA facts as tracked Lean under `Mathlib/LinearAlgebra/Matrix/Rank.lean`: `rowOp_isUnit_det`
  (`IsUnit (fromBlocks 1 (-L₀) 0 1).det`) + `rowOp_zeroes_upperRight`
  (`B = L₀*D ⟹ fromBlocks 1 (-L₀) 0 1 * fromBlocks A B C D = fromBlocks (A−L₀C) 0 C D`). Both TRIVIAL. Signatures
  in §(4.53).
- [ ] **(3b″) cert + A4 reshape to thread the LEFT row op `Lrow`** (design §(4.53) adjudication (A)) — reshape
  `case_III_rank_certification_zero₁₂` + `rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` to consume a unit-det
  LEFT factor (`hblock : (Lrow * (M * U)).submatrix re en = fromBlocks A 0 C D`, rank-invariant via
  `rank_mul_eq_right_of_isUnit_det`); then the genuinely-new geometry leaf `L₀C = B` from LEAF-3's `cGv` widening +
  the corner-`hA` leaf `A − L₀C = [blockBasisOn(e_a); ρ₀]` (where `corner_hA'_of_gate` FINALLY plugs in). ≈ 3–4 leaves.
- [ ] **(3c) the candidate-matching gate bridge** — `F.supportExtensor e_a` ↔ LEAF-3's
  `panelSupportExtensor (q(candidateVtx i)) n'` via `caseIIICandidate_supportExtensor_candidate`
  (`Candidate.lean:960`) + `candidateVtx i = a` (interior: `= vtx i.succ`).
- [ ] **(4) Wire into the dispatch (the original 23e/23f scope, UNBLOCKED)** — the A3-transposed cert dissolves
  the `hbotmem` wall: LEAF-4 disjoint-block bundle now takes the `mixedBottom` bottom (no membership); LEAF-5
  router (base/`d=3` → `chainData_split_realization`; interior → `chainData_arm_realization_sep`); fire LEAF-3.

## Blockers / open questions

- **OPEN BLOCKER — cert-shape adjudication owed (design §(4.53)).** The forked cert `case_III_rank_certification_zero₁₂`
  is NOT consumable as landed (the matrix-assembly spike found the upper-right-zero `hblock` is not producible from
  the column op, and the LEFT row op needed is absent + not expressible in `(M * U)`). The §(4.52) "remaining =
  ASSEMBLY, no new math" verdict is REFUTED — there ARE two genuinely-new LEAF-RowOp leaves + a cert reshape.
  Adjudication: **(A)** thread a unit-det LEFT row op `Lrow` into the cert/A4 + build the `L₀C = B` geometry leaf
  (recommended — the row op is real KT (6.63) content, the LA leaves trivial, `corner_hA'_of_gate`/`mixedBottom`/`cGv`
  all landed); **(B)** find a cert shape avoiding the left row op (none found in §(4.49)–(4.53); the `_matrix` and
  `_sep` shapes both re-hit the §(4.41)/(4.44) walls). Recommend (A); full directions in §(4.53).
- **Lesson (the §(4.46) principle, second occurrence).** §(4.52)'s "wiring kernel-confirmed" spike (`Spike49c`)
  confirmed `corner_hA'_of_gate` + the pin-zero fact in ISOLATION but never instantiated the cert's `hblock`/`hA`
  against them — the end-to-end route-composition is where the gap hid. Compiler-check the FULL composition (the cert
  `hblock`/`hA` literally), not the component facts, before declaring "remaining = assembly."
- The item-(3c) candidate-matching gate bridge (`candidateVtx i = a`) still owed after the cert is consumable;
  confirm against `caseIIICandidate_supportExtensor_candidate` + the `ChainData` `d = k+1` fact, not `Fin`-arithmetic.
- **Orthogonal carried hypothesis: GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive) —
  independent of the cert; tracked separately, lands with 23f/the spine.
- **Downstream (23f+):** the general-`k` dispatch + CHAIN-5, ENTRY's `exists_chain_data_of_noRigid` reshape +
  floor lift + OD-1, ASSEMBLY. The frozen contract (C.5/C.6) is invariant; none touches 23e's cert.

## Hand-off / next phase

**Next concrete commit = LEAF-RowOp-1 + LEAF-RowOp-2** (the two trivial row-op LA facts, re-created from the
reverted `Spike49`, landed together under `Mathlib/LinearAlgebra/Matrix/Rank.lean`; exact signatures in design
§(4.53)):
```
theorem rowOp_isUnit_det {K m₁ m₂ : Type*} [Field K] [Fintype m₁] [Fintype m₂] [DecidableEq m₁]
    [DecidableEq m₂] (L₀ : Matrix m₁ m₂ K) :
    IsUnit (Matrix.fromBlocks (1 : Matrix m₁ m₁ K) (-L₀) 0 (1 : Matrix m₂ m₂ K)).det
theorem rowOp_zeroes_upperRight {K m₁ m₂ n₁ n₂ : Type*} [Field K] [Fintype m₁] [Fintype m₂]
    {A : Matrix m₁ n₁ K} {B : Matrix m₁ n₂ K} {C : Matrix m₂ n₁ K} {D : Matrix m₂ n₂ K}
    (L₀ : Matrix m₁ m₂ K) (hB : B = L₀ * D) :
    Matrix.fromBlocks (1 : Matrix m₁ m₁ K) (-L₀) 0 (1 : Matrix m₂ m₂ K) * Matrix.fromBlocks A B C D
      = Matrix.fromBlocks (A - L₀ * C) 0 C D
```
**THEN the cert-shape adjudication is owed** (see *Blockers*) before the cert reshape — recommend (A): thread a
unit-det LEFT row op `Lrow` into `case_III_rank_certification_zero₁₂` + `rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂`
(`hblock : (Lrow * (M * U)).submatrix re en = fromBlocks A 0 C D`), then build the geometry leaf `L₀C = B` from
LEAF-3's `cGv` widening + wire `corner_hA'_of_gate` as `A − L₀C = [blockBasisOn(e_a); ρ₀]`. ≈ 3–4 leaves.

**What is in-tree (cite directly):** the A3-transposed cert + A3-transposed A4 scaffolding (item 3a, axiom-clean —
but consumes the not-yet-producible upper-right `hblock`); `corner_hA'_of_gate` (`Concrete.lean:620`, landed but NO
consumer until the row op lands); the union-dimension discriminator + `exists_shared_redundancy_and_matched_candidate`
(Phase 23c); the `mixedBottom` family + `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`
(`Concrete.lean:1677`, supplies `hD` — composes); `rigidityMatrixEdge_mul_columnOp_apply_pin_zero` (`:1274`, the
LOWER-left pin-zero — zeros the BOTTOM rows' pin, NOT the corner's upper-right); the operated-entry bricks
`rigidityMatrixEdge_mul_columnOp_apply_corner`/`_apply_eB_off_pin`/`_apply_off_pin` (`:1306`/`:1462`/`:1426`);
`linearIndependent_toBlocks₁₁_row_of_corner_gate` (`Concrete.lean:1775`, the ONLY corner→`A.row` bridge — takes a
PLAIN `blockBasisOn` family, does NOT consume `corner_hA'_of_gate`).

**STILL TO BUILD:** LEAF-RowOp-1/2 (next commit) → cert/A4 `Lrow`-reshape + `L₀C = B` geometry leaf + corner-`hA`
wire (after adjudication) → (3c) candidate-matching gate bridge → LEAF-4/LEAF-5/dispatch → 23f. **NOT** "remaining =
assembly, no new math" — the row op is genuinely-new tracked content (§(4.53)). Then 23g (ENTRY) → 23h (ASSEMBLY).

## Decisions made during this phase

### Phase-local choices and proof techniques

- **Item (3b) WALL — the cert is NOT consumable from landed geometry** (design §(4.53), kernel-checked spike,
  session #38). The cert `case_III_rank_certification_zero₁₂` needs an UPPER-right-zero `hblock`; the column op
  gives LOWER-left-zero (upper-right `B` = the `±r` row's off-`v` `ab`-fill, GENERICALLY nonzero — one-`rw` kernel
  residual). The fixing LEFT row op is (a) absent from tracked source (reverted `Spike49`) + (b) inexpressible in
  `(M * U)`. `corner_hA'_of_gate` (landed) has NO consumer: the only corner→`A.row` bridge takes a plain
  `blockBasisOn` family, not the ρ₀-augmented one. §(4.52)'s "remaining = ASSEMBLY" is REFUTED; two new LEAF-RowOp
  leaves + a `Lrow`-threading cert reshape owed (next commit = LEAF-RowOp-1/2; then adjudication). Meta-lesson (the
  §(4.46) principle, 2nd occurrence): compiler-check the FULL cert `hblock`/`hA` composition, not the component
  facts in isolation, before declaring "assembly."
- **Item (3b), `hA` half — `corner_hA'_of_gate` LANDED** (axiom-clean; `RigidityMatrix/Concrete.lean`, after
  `exists_corner_blockBasisOn_linearIndependent`). Re-created the §(4.52) sorry-free fact as tracked Lean: from
  the candidate-slot gate `ρ₀(F.supportExtensor e_a) ≠ 0` it builds the corner LI
  `Sum.elim (blockBasisOn e_a) (fun _ : Unit => ρ₀)` (= `Mᵢ = [r(Lᵢ); ρ₀]`) via the row-space criterion
  `linearIndependent_sumElim_candidateRow_iff` + `linearIndependent_blockBasisOn_screwDual` + `span_coe_eq`. One
  `rw` + one `exact` — strictly simpler than `exists_corner_blockBasisOn_linearIndependent` (augments with `ρ₀`
  itself, no escape argument). **CAVEAT (§(4.53)):** this is a dual-space fact with NO consumer until the LEFT row
  op lands — `linearIndependent_toBlocks₁₁_row_of_corner_gate` does NOT re-wrap it (it takes a plain `blockBasisOn`
  family, not the ρ₀-augmented one); ρ₀ only becomes the corner's `D`-th row after the row op. No friction logged.
- **Item (3a) — the forked A3-transposed cert + scaffolding LANDED** (axiom-clean). The A3-transposed cert leaf
  `case_III_rank_certification_zero₁₂` (`CaseIII/Candidate.lean`) consumes `fromBlocks A 0 C D` block data + the
  corner/bottom row-LI `hA`/`hD`, firing the A5c-transposed core. Scaffolding re-created as tracked Lean (all
  trivial mirrors of the landed A3 lemmas, swap `det_fromBlocks_zero₂₁ → det_fromBlocks_zero₁₂`, built first
  try): `rank_fromBlocks_zero₁₂_ge_of_linearIndependent_rows` +
  `rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` (`Rank.lean`),
  `finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks_zero₁₂` (`Concrete.lean`). The §(4.50) spike's
  `rowOp_isUnit_det`/`rowOp_zeroes_upperRight` are NOT needed at the cert layer — they belong to item (3b)'s arm
  that *constructs* `hblock`; the cert just consumes the resulting `fromBlocks A 0 C D` equality.
- **De-risking arc (sessions #36–37) → GO on the A3-transposed cert; remaining = ASSEMBLY** (canonical record:
  design §(4.48)–(4.52); the full per-spike traces are there + in git). The general-`d` cert wall resolved end
  to end: `R(Gab)`-reproduction is a kernel-grounded NO-GO (§(4.48); the deficiency wall is a FORMALIZATION
  representation-mismatch with KT's non-block-triangular argument, NOT open math), so the user chose to pursue
  the genuinely-new cert → the A3-transposed `fromBlocks A 0 C D` shape, zero UPPER-right via a row op zeroing
  `B` (§(4.49); NOT §(4.42)'s Schur, which zeros `C`) → the scaffolding builds sorry-free but relocated the crux
  to the corner `hA'` (§(4.50)) → KT's union-dimension `Mᵢ`-invertibility (6.65–6.67) is ALREADY LANDED
  general-`d` (§(4.51); the discriminator + callees are `{k:ℕ}`, fired by `exists_shared_redundancy_and_matched_candidate`
  — the "hardest argument" framing was STALE) → `hA'` reduces via the `Gv`-row PIN-ZERO fact, kernel-confirmed
  (§(4.52); the §(4.50) collapse was a generic-`L₀` artifact). **OVERTURNED at §(4.53):** §(4.51)/(4.52)'s
  "remaining = ASSEMBLY" was premature — the row-op facts (`rowOp_isUnit_det`/`rowOp_zeroes_upperRight`) were in the
  REVERTED `Spike49`/`Spike49c`, never tracked Lean; the step-3b assembly spike found the cert's upper-right `hblock`
  is not producible from the column op without that absent LEFT row op (kernel-checked). So the §(4.51) `Mᵢ`
  union-dimension result stands (that IS landed general-`d`), but the cert plumbing needs 2 new LEAF-RowOp leaves +
  a `Lrow`-reshape (§(4.53)) — genuinely-new tracked content, not assembly.

### Carried-forward interface decisions (for 23f, the dispatch)

- **C.3 `hIH`-on-consume-shape addition — APPROVED** (user-adjudicated 2026-06-26, session #36). The interior
  arm needs the INTERIOR-split `hsplitGP` (`G.splitOff vᵢ …`), derivable only from `hIH` (via
  `splitOff_isMinimalKDof`), not in the frozen C.3 signature — so add `hIH` to the C.3 dispatch consume-shape: a
  one-field addition touching the C.0 producer/consumer/ENTRY lockstep trio, NOT a motive/IH-strength change
  (the landed `chainData_split_realization` already carries `hIH` separately). Lands with 23f. Context: design
  §(4.43) *THE ONE INTERFACE OBLIGATION* + §C.3.
- **Interior arm wrapper landed, parks in 23f** (`chainData_arm_realization_sep`, `CaseIII/Realization.lean`,
  2026-06-26). The `ChainData`-indexed sibling of `chainData_split_realization` for the interior route; sound
  (carries the disjoint-block obligations as hypotheses) but consumes the walled `hbotmem`, so it waits for the
  sound cert before wiring into the dispatch.
