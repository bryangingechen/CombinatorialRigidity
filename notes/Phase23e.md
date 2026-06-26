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

**`B = L₀ * D` matrix-algebra half LANDED (item 3b″ geometry-arm leaf 1a, axiom-clean) —
`Matrix.of_eq_mul_of_row_comb` (`Rank.lean`): a matrix `B` whose every row is the `w i`-weighted
combination of `D`'s rows (`∀ i j, B i j = ∑ i', w i i' * D i' j`) factors as `Matrix.of w * D`.**
This is the separable matrix-algebra step of the `L₀C = B` leaf — it turns the *per-row* combination
the `cGv` widening produces into the `B = L₀ * D` form `rowOp_zeroes_upperRight` needs, with
`L₀ := Matrix.of w`. Next step = the **geometry half** (arm-coupled): exhibit the operated corner's
off-`v` block `B` as exactly such a `cGv`-weighted combination of the `mixedBottom` bottom rows `D` —
i.e. instantiate `w` from LEAF-3's `cGv` against the arm's `re`/`m₂` row index. This half needs the
dispatch's `re` injection (the corner `m₁` / bottom `m₂` split), which is the 23f arm, so it lands
once that index is pinned; then the corner-`hA` leaf `A − L₀C = [blockBasisOn(e_a); ρ₀]` (where
`corner_hA'_of_gate` FINALLY plugs in). The §(4.53) adjudication = route (A) is DISCHARGED at the
cert layer; the geometry arm supplying the block data remains.

**What is now consumable vs. what the geometry arm still owes** (design §(4.53)). With the `Lrow`-reshape landed,
`case_III_rank_certification_zero₁₂` consumes `(Lrow, hLrow, U, hU, re, en, hblock, hA, hD)` where
`hblock : (Lrow * rigidityMatrixEdge * U).submatrix re en = fromBlocks A 0 C D` — the LEFT row op `Lrow` is now a
real cert parameter (rank-invariant via the landed `rank_mul_eq_right_of_isUnit_det`). The geometry arm still owes
the *construction* of that block data from landed facts (the next ≈ 2–3 leaves):

- **`L₀C = B` (`hblock`'s upper-right zeroing) — matrix-algebra half LANDED.**
  `Matrix.of_eq_mul_of_row_comb` (`Rank.lean`): a per-row combination `B i = Σ_{i'} w i i' • D i'`
  factors as `B = Matrix.of w * D`. The geometry half (arm-coupled, REMAINS) instantiates `w` from
  LEAF-3's `cGv` widening (`hingeRow a b ρ = Σⱼ cGv j • hingeRow (uvGv j) (vvGv j) (rvGv j)`, all
  endpoints `≠ v`) against the arm's `re`/`m₂` row index, so `Lrow := fromBlocks 1 (−L₀) 0 1` zeros
  the corner's off-`v` `B` (`rowOp_zeroes_upperRight` + `hLrow` from `rowOp_isUnit_det`) while leaving
  the pin (`Gv`-rows pin-zero, `rigidityMatrixEdge_mul_columnOp_apply_pin_zero`) untouched.
- **corner-`hA` `A − L₀C = [blockBasisOn(e_a); ρ₀]`.** Where `corner_hA'_of_gate` (`Concrete.lean:620`) FINALLY
  plugs in: after the row op the corner's `D`-th row IS ρ₀, so the ρ₀-augmented family is the post-op `A.row`.
- **`hD`/cardinalities already compose** (kept honest): `hD` from `mixedBottom`
  (`linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`, conditional on the IH `hrank`);
  `columnSplit_corner_card = screwDim k = finrank ScrewSpace`.

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
- [x] **(3b′) LEAF-RowOp-1/2** (DONE, axiom-clean) — the two trivial row-op LA facts landed as tracked Lean under
  `Mathlib/LinearAlgebra/Matrix/Rank.lean` (after `rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂`):
  `rowOp_isUnit_det` (`IsUnit (fromBlocks 1 (-L₀) 0 1).det`, via `det_fromBlocks_zero₂₁` + `det_one`) +
  `rowOp_zeroes_upperRight` (`B = L₀*D ⟹ fromBlocks 1 (-L₀) 0 1 * fromBlocks A B C D = fromBlocks (A−L₀C) 0 C D`,
  via `fromBlocks_multiply` + `hB`). Both needed `[DecidableEq m₁] [DecidableEq m₂]` (the identity-matrix `One`
  instance — §(4.53)'s signature elided it for LEAF-RowOp-2; added). These are the unit-det `Lrow` factor + its
  action that item (3b″) threads into the cert.
- [~] **(3b″) cert + A4 `Lrow`-reshape — CERT-LAYER DONE (axiom-clean), geometry arm remains** (design §(4.53)
  adjudication (A)). The three-decl chain now consumes a unit-det LEFT factor `Lrow`
  (`hblock : (Lrow * (M * U)).submatrix re en = fromBlocks A 0 C D`, rank-invariant via the mathlib
  `rank_mul_eq_right_of_isUnit_det`): `rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` (`Rank.lean`, threads
  `Lrow`/`hLrow` + two rank-invariance `calc` steps), `finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks_zero₁₂`
  (`Concrete.lean`, + a `Fintype {e // e ∈ F.graph.edgeSet}` binder for the `Lrow * M` product), and
  `case_III_rank_certification_zero₁₂` (`Candidate.lean`, `Lrow` typed at the candidate-graph edgeSet so `*` composes
  syntactically). STILL OWED (the geometry arm): the **geometry half** of the `L₀C = B` leaf (the matrix-algebra
  half `Matrix.of_eq_mul_of_row_comb` LANDED, see item (3b‴)) — instantiate `w` from `cGv` against the arm's `re`/`m₂`,
  then `rowOp_*` discharge `hLrow`/upper-right-zeroing — + the corner-`hA` leaf `A − L₀C = [blockBasisOn(e_a); ρ₀]`
  (where `corner_hA'_of_gate` FINALLY plugs in).
- [x] **(3b‴) the `B = L₀ * D` matrix-algebra half** (DONE, axiom-clean) — `Matrix.of_eq_mul_of_row_comb`
  (`Mathlib/LinearAlgebra/Matrix/Rank.lean`, after `rowOp_zeroes_upperRight`): `(∀ i j, B i j = ∑ i', w i i' * D i' j)
  → B = Matrix.of w * D`, one `ext` + `mul_apply` + `rfl`. The separable matrix-algebra step of the `L₀C = B` leaf —
  turns the *per-row* combination the `cGv` widening produces into the `B = L₀ * D` form `rowOp_zeroes_upperRight`
  consumes (`L₀ := Matrix.of w`). Decoupled from the arm's `re`/`m₂` construction; upstream-eligible.
- [ ] **(3c) the candidate-matching gate bridge** — `F.supportExtensor e_a` ↔ LEAF-3's
  `panelSupportExtensor (q(candidateVtx i)) n'` via `caseIIICandidate_supportExtensor_candidate`
  (`Candidate.lean:960`) + `candidateVtx i = a` (interior: `= vtx i.succ`).
- [ ] **(4) Wire into the dispatch (the original 23e/23f scope, UNBLOCKED)** — the A3-transposed cert dissolves
  the `hbotmem` wall: LEAF-4 disjoint-block bundle now takes the `mixedBottom` bottom (no membership); LEAF-5
  router (base/`d=3` → `chainData_split_realization`; interior → `chainData_arm_realization_sep`); fire LEAF-3.

## Blockers / open questions

- **Cert-shape adjudication = route (A), DISCHARGED at the cert layer** (user-confirmed, session #38; design
  §(4.53)). The `Lrow`-reshape landed this session — the cert chain now consumes the unit-det LEFT row op as a real
  parameter. What remains is the *geometry arm* that constructs `(Lrow, hLrow, hblock)` from landed facts (the
  `L₀C = B` + corner-`hA` leaves; see *Current state*), not an adjudication. (Route (B) — a cert shape avoiding the
  left row op — was found non-viable: the `_matrix`/`_sep` shapes re-hit the §(4.41)/(4.44) walls.)
- **Lesson (the §(4.46) principle, second occurrence).** §(4.52)'s "wiring kernel-confirmed" spike (`Spike49c`)
  confirmed `corner_hA'_of_gate` + the pin-zero fact in ISOLATION but never instantiated the cert's `hblock`/`hA`
  against them — the end-to-end route-composition is where the gap hid. Compiler-check the FULL composition (the cert
  `hblock`/`hA` literally), not the component facts, before declaring "remaining = assembly." (Still live for the
  geometry arm: build `hblock` against the literal `Lrow * rigidityMatrixEdge * U` product, not `L₀C = B` in isolation.)
- The item-(3c) candidate-matching gate bridge (`candidateVtx i = a`) still owed after the cert is consumable;
  confirm against `caseIIICandidate_supportExtensor_candidate` + the `ChainData` `d = k+1` fact, not `Fin`-arithmetic.
- **Orthogonal carried hypothesis: GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive) —
  independent of the cert; tracked separately, lands with 23f/the spine.
- **Downstream (23f+):** the general-`k` dispatch + CHAIN-5, ENTRY's `exists_chain_data_of_noRigid` reshape +
  floor lift + OD-1, ASSEMBLY. The frozen contract (C.5/C.6) is invariant; none touches 23e's cert.

## Hand-off / next phase

**Next concrete commit = item (3b″) geometry arm, the GEOMETRY half of the `L₀C = B` leaf.** The
matrix-algebra half landed this session (`Matrix.of_eq_mul_of_row_comb`, item (3b‴), axiom-clean: a
per-row combination `B i = Σ_{i'} w i i' • D i'` factors as `B = Matrix.of w * D`). The geometry half
exhibits the operated corner's off-`v` block `B` as exactly such a combination of the `mixedBottom`
bottom rows `D` — instantiate the weights `w` from LEAF-3's `cGv` widening
(`hingeRow a b ρ = Σⱼ cGv j • hingeRow (uvGv j) (vvGv j) (rvGv j)`, all endpoints `≠ v`) against the
arm's `re`/`m₂` row index. This needs the dispatch's `re` injection (the corner `m₁` / bottom `m₂`
split), which is the 23f arm, so it lands once that index is pinned; then `L₀ := Matrix.of w`,
`Lrow := fromBlocks 1 (−L₀) 0 1` + `rowOp_zeroes_upperRight` gives the upper-right-zero `hblock` and
`rowOp_isUnit_det` gives `hLrow`, `pin-zero` keeps the pin untouched. THEN the corner-`hA` leaf
`A − L₀C = [blockBasisOn(e_a); ρ₀]` (wiring `corner_hA'_of_gate`). ≈ 2 geometry leaves remain.

**What is in-tree (cite directly):** the reshaped A3-transposed cert chain (item 3b″, axiom-clean) —
`rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` (`Rank.lean`),
`finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks_zero₁₂` (`Concrete.lean`),
`case_III_rank_certification_zero₁₂` (`Candidate.lean`), all now consuming `(Lrow, hLrow, U, hU, …, hblock, …)`;
the row-op LA facts `rowOp_isUnit_det` + `rowOp_zeroes_upperRight` (`Rank.lean`, item 3b′ — discharge `hLrow` + the
upper-right-zeroing); the matrix-algebra half `Matrix.of_eq_mul_of_row_comb` (`Rank.lean`, item 3b‴ — `B = L₀ * D`
from the per-row `cGv` combination); the mathlib `rank_mul_eq_right_of_isUnit_det` (the LEFT-op rank-invariance the reshape uses);
`corner_hA'_of_gate` (`Concrete.lean:620`, the ρ₀-augmented family — NOW has its consumer: the post-op corner `hA`);
the union-dimension discriminator + `exists_shared_redundancy_and_matched_candidate` (Phase 23c); the `mixedBottom`
family + `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` (`Concrete.lean:1677`, supplies `hD`);
`rigidityMatrixEdge_mul_columnOp_apply_pin_zero` (`:1274`, the LOWER-left pin-zero); the operated-entry bricks
`rigidityMatrixEdge_mul_columnOp_apply_corner`/`_apply_eB_off_pin`/`_apply_off_pin` (`:1306`/`:1462`/`:1426`).

**STILL TO BUILD:** `L₀C = B` GEOMETRY half (the matrix-algebra half `Matrix.of_eq_mul_of_row_comb` is LANDED) +
corner-`hA` wire → (3c) candidate-matching gate bridge → LEAF-4/LEAF-5/dispatch → 23f. **NOT** "remaining = assembly,
no new math" — the geometry arm is genuinely-new tracked content (§(4.53)). Then 23g (ENTRY) → 23h (ASSEMBLY).

## Decisions made during this phase

### Phase-local choices and proof techniques

- **Item (3b‴) — the `B = L₀ * D` matrix-algebra half LANDED** (axiom-clean; `Matrix.of_eq_mul_of_row_comb`,
  `Mathlib/LinearAlgebra/Matrix/Rank.lean`, after `rowOp_zeroes_upperRight`). The separable matrix-algebra
  step of the `L₀C = B` geometry leaf: `(∀ i j, B i j = ∑ i', w i i' * D i' j) → B = Matrix.of w * D`, proved
  `ext i j; rw [Matrix.mul_apply, hcomb]; rfl`. Decoupling rationale: the `L₀C = B` leaf splits into (a) the
  per-row→matrix-product conversion (this, arm-independent) and (b) exhibiting the operated corner off-`v`
  reads AS a `cGv`-weighted combination of the `mixedBottom` rows (arm-coupled — needs the dispatch's `re`/`m₂`
  split, so it lands with 23f). Landing (a) now keeps the genuinely-new matrix-algebra content isolated and
  axiom-clean. Upstream-eligible. No friction (one-step proof, `Matrix.mul_apply`).
- **Item (3b″) cert-layer — the `Lrow`-reshape LANDED** (axiom-clean; three decls). Threaded a unit-det LEFT
  factor `Lrow` through the A3-transposed cert chain so it consumes `hblock : (Lrow * M * U).submatrix re en =
  fromBlocks A 0 C D`. `rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` (`Rank.lean`) adds `Lrow`/`hLrow` + two
  `calc` rank-invariance steps (`rank_mul_eq_left_of_isUnit_det` then mathlib `rank_mul_eq_right_of_isUnit_det`);
  needs `[Fintype p] [DecidableEq p]` (was `[Finite p]`) for the `Lrow * M` product. The A5c core
  (`Concrete.lean`) + cert (`Candidate.lean`) propagate `Lrow`/`hLrow`. Two Lean-mechanics gotchas → TACTICS-QUIRKS
  § 69: the edge-row index `{e // e ∈ G.edgeSet} × Fin (D−1)` needs an explicit `[Fintype {e // e ∈ F.graph.edgeSet}]`
  binder (subtype `Fintype` is never auto-synthesized); and `Lrow * rigidityMatrixEdge` requires `Lrow` typed at the
  *candidate-graph* edgeSet (`*`/`HMul` unifies indices syntactically, not up to the `caseIIICandidate_graph = G`
  `rfl`), which forced dropping `set F₀` (it rewrote the candidate occurrence inside `Lrow`'s type, splitting the
  `Fintype` instance from `hLrow`'s).
- **Item (3b′) — LEAF-RowOp-1/2 LANDED** (axiom-clean; `Mathlib/LinearAlgebra/Matrix/Rank.lean`, after
  `rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂`). The two trivial row-op LA facts: `rowOp_isUnit_det`
  (`IsUnit (fromBlocks 1 (-L₀) 0 1).det`, one `rw [det_fromBlocks_zero₂₁, det_one, det_one, mul_one]` + `isUnit_one`)
  + `rowOp_zeroes_upperRight` (`B = L₀*D ⟹ fromBlocks 1 (-L₀) 0 1 * fromBlocks A B C D = fromBlocks (A−L₀C) 0 C D`,
  `rw [fromBlocks_multiply, hB]; simp [sub_eq_add_neg]`). §(4.53)'s LEAF-RowOp-2 signature elided the identity
  matrix's `[DecidableEq m₁] [DecidableEq m₂]` (the `One (Matrix m m K)` instance needs it) — added. These are the
  unit-det `Lrow` factor + its upper-right-zeroing action that item (3b″)'s cert reshape threads. Upstream-eligible.
- **Item (3b) WALL (resolved by the `Lrow`-reshape).** The §(4.53) spike found the cert's upper-right-zero `hblock`
  not producible from the column op alone (it gives LOWER-left-zero; the LEFT row op `Lrow` is needed) — this drove
  items 3b′ (LEAF-RowOp) + 3b″ (the reshape), now both landed at the cert layer. The remaining gap is the geometry
  arm (`L₀C = B` + corner-`hA`), tracked in *Current state* / *Hand-off*. Lesson lifted to *Blockers* (§(4.46), 2nd).
- **Item (3b), `hA` half — `corner_hA'_of_gate` LANDED** (axiom-clean; `RigidityMatrix/Concrete.lean`, after
  `exists_corner_blockBasisOn_linearIndependent`). From the candidate-slot gate `ρ₀(F.supportExtensor e_a) ≠ 0` it
  builds the corner LI `Sum.elim (blockBasisOn e_a) (fun _ : Unit => ρ₀)` (= `Mᵢ = [r(Lᵢ); ρ₀]`) via
  `linearIndependent_sumElim_candidateRow_iff` + `linearIndependent_blockBasisOn_screwDual` + `span_coe_eq` (one
  `rw` + one `exact`). Its consumer is the (3b″) geometry arm's corner-`hA` leaf (`A − L₀C = [blockBasisOn(e_a);
  ρ₀]`) — ρ₀ becomes the corner's `D`-th row after the now-threaded row op.
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
