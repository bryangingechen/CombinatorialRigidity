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

**Next step = item (3b)/(3c): the literal `re`/`L₀`/gate-bridge arm that supplies the forked cert's matrix block
data.** Item (3a) is DONE — the forked A3-transposed cert `case_III_rank_certification_zero₁₂`
(`CaseIII/Candidate.lean`) lands sorry-free + axiom-clean, consuming the A3-transposed `fromBlocks A 0 C D` matrix
block data and firing the new A5c-transposed composition core. The A3-transposed scaffolding it needed is now
TRACKED LEAN (re-created from the deleted spikes): `rank_fromBlocks_zero₁₂_ge_of_linearIndependent_rows` +
`rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` (`Mathlib/LinearAlgebra/Matrix/Rank.lean`) and
`finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks_zero₁₂` (`RigidityMatrix/Concrete.lean`). All trivial
mirrors of the landed A3 lemmas (swap `det_fromBlocks_zero₂₁ → det_fromBlocks_zero₁₂`), built first try.

**The cert now consumes `(U, hU, re, en, hblock, hA, hD)` as explicit `h…` hypotheses.** The remaining 23e work is
the ARM that produces them: (3b) the literal `re`/`L₀` row-op construction wiring LEAF-3's `cGv` widening as the
row-op weights + the `(row-op'd corner) = ρ₀` identity (composed from the two §(4.52) sorry-free facts
`corner_hA'_of_gate` + `Gv_row_pin_zero`), and (3c) the candidate-matching gate bridge. `hD` reads off the landed
`mixedBottom` family (the RANK fact, not `hbotmem`); `hA` reads off `corner_hA'_of_gate`. Then item (4) wires the
cert into LEAF-4/LEAF-5/the dispatch (the original 23e/23f scope, UNBLOCKED — the A3-transposed cert dissolves the
`hbotmem` wall).

Nothing is mid-stream; tree clean. `d=3` stays fully green throughout (zero-regression is a hard constraint).
The landed `chainData_arm_realization_sep` wrapper (the old 23e dispatch work) is SOUND but consumes the
walled `hbotmem`; it parks in **23f** (the dispatch) until the sound cert is wired through (item 4).

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
- [ ] **(3b) the literal `re`/`L₀` construction** (next concrete work) — wire LEAF-3's `cGv` edge-grouped
  widening as the row-op weights + the `(row-op'd corner) = ρ₀` identity (composed from the two §(4.52)
  sorry-free facts `corner_hA'_of_gate` + `Gv_row_pin_zero`); supply the cert's `(U, re, en, hblock, hA, hD)`.
- [ ] **(3c) the candidate-matching gate bridge** — `F.supportExtensor e_a` ↔ LEAF-3's
  `panelSupportExtensor (q(candidateVtx i)) n'` via `caseIIICandidate_supportExtensor_candidate`
  (`Candidate.lean:960`) + `candidateVtx i = a` (interior: `= vtx i.succ`).
- [ ] **(4) Wire into the dispatch (the original 23e/23f scope, UNBLOCKED)** — the A3-transposed cert dissolves
  the `hbotmem` wall: LEAF-4 disjoint-block bundle now takes the `mixedBottom` bottom (no membership); LEAF-5
  router (base/`d=3` → `chainData_split_realization`; interior → `chainData_arm_realization_sep`); fire LEAF-3.

## Blockers / open questions

- **No open blocker for the build.** The cert route is settled (A3-transposed, design §(4.49)–(4.52)); all
  foundations are landed or sorry-free-confirmed. The one thing the builder must verify (not a blocker, a
  build-time check, flagged in *Hand-off*): the item-(3c) candidate-matching gate bridge involves the
  `candidateVtx i = a` index identification — confirm it against the landed `caseIIICandidate_supportExtensor_candidate`
  + the `ChainData` `d = k+1` contract fact, not by `Fin`-arithmetic hand-waving (the 23c LEAF-3 `d = n` lesson).
- **Orthogonal carried hypothesis: GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive) —
  independent of the cert; tracked separately, lands with 23f/the spine.
- **Downstream (23f+):** the general-`k` dispatch + CHAIN-5, ENTRY's `exists_chain_data_of_noRigid` reshape +
  floor lift + OD-1, ASSEMBLY. The frozen contract (C.5/C.6) is invariant; none touches 23e's cert.

## Hand-off / next phase

**Next concrete commit = item (3b): the literal `re`/`L₀` row-op construction** that supplies the forked cert's
matrix block data `(U, re, en, hblock, hA, hD)`. Item (3a) landed the cert
`case_III_rank_certification_zero₁₂` + its A3-transposed scaffolding (all tracked, axiom-clean) — the cert now
consumes the block data as explicit `h…` hypotheses, so (3b) is the arm that constructs them. **What is in-tree:**
- **IN-TREE (cite directly):** the A3-transposed cert + scaffolding (item 3a, just landed); the union-dimension
  discriminator + `exists_shared_redundancy_and_matched_candidate` (Phase 23c); the `mixedBottom` family
  (`Concrete.lean:1460/1518/1610`, supplies `hD` — the RANK fact, via
  `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`);
  `rigidityMatrixEdge_mul_columnOp_apply_pin_zero` (the `Gv`-row pin-zero, §(4.52)'s `Gv_row_pin_zero`);
  `linearIndependent_sumElim_candidateRow_iff` (`Claim612.lean:845`); `caseIIICandidate_supportExtensor_candidate`
  (`Candidate.lean:960`).
- **STILL TO BUILD (item 3b/3c):** the `corner_hA'_of_gate` corner reduction (scratch-confirmed sorry-free in
  `Spike49c`, now deleted — re-create as tracked Lean; supplies `hA`); the literal `U`/`re`/`en` geometry +
  `hblock` entrywise off the operated-entry bricks + LEAF-3's row-op weights; the (3c) gate bridge.

Remaining = ASSEMBLY (3b/3c → LEAF-4/LEAF-5/dispatch → 23f), no new math. The one build-time gotcha is item
(3c)'s `candidateVtx i = a` index match (see *Blockers*). Then 23g (ENTRY) → 23h (ASSEMBLY proper).

## Decisions made during this phase

### Phase-local choices and proof techniques

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
  (§(4.52); the §(4.50) collapse was a generic-`L₀` artifact). NET: every foundation is landed or
  sorry-free-confirmed; remaining 23e = ASSEMBLY (items 3/4).

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
