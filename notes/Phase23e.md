# Phase 23e — Case III general `d`: the KT-faithful rank certificate (work log)

**Status:** ✓ closed 2026-06-26. The *fourth* CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d + 23e).
Opened 2026-06-26 as the general-`k` dispatch + CHAIN-5, **re-scoped the same day** to the KT-faithful rank
certificate after the `R(Gab)`-reproduction spike returned a kernel-grounded NO-GO and the user chose to
pursue the genuinely-new certificate (complete formalization of KT is the goal; fallback (C) / freeze-at-`d=3`
declined). The authoritative recon is `notes/Phase23-design.md` §(4.44)–(4.54) (compressed to cited verdicts at
this close). The geometry arm that *constructs* the cert's block data is **23f** (`notes/Phase23f.md`). Program
map: `notes/MolecularConjecture.md`.

## What 23e delivered

The **forked A3-transposed rank certificate** `fromBlocks A 0 C D` (zero UPPER-right) + all its
framework-level LA scaffolding, ALL axiom-clean, and the cert is end-to-end **SATISFIABLE** for the real
interior arm (kernel-confirmed §(4.54); no fourth wall). The `d=3` line stays fully green via a cert FORK
(zero-regression; only the general-`d` arm routes through the new cert).

In-tree (cite directly):
- **Cert chain** (axiom-clean): `case_III_rank_certification_zero₁₂` (`CaseIII/Candidate.lean`) + its A4 bridge
  `rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` (`Rank.lean`) + the A5c core
  `finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks_zero₁₂` (`Concrete.lean`), all consuming
  `(Lrow, hLrow, U, hU, re, en, hblock, hA, hD)` with `hblock : (Lrow * M * U).submatrix re en = fromBlocks A 0 C D`
  (rank-invariant via mathlib `rank_mul_eq_right_of_isUnit_det`). Plus the trivial A3-transposed mirror
  `rank_fromBlocks_zero₁₂_ge_of_linearIndependent_rows` (`Rank.lean`).
- **Row-op LA facts** (`Mathlib/LinearAlgebra/Matrix/Rank.lean`, upstream-eligible): `rowOp_isUnit_det`
  (via `det_fromBlocks_zero₂₁`), `rowOp_zeroes_upperRight` (via `fromBlocks_multiply`), and the matrix-algebra
  half `Matrix.of_eq_mul_of_row_comb`.
- **Corner gate** `corner_hA'_of_gate` (`Concrete.lean:620`): the ρ₀-augmented `[blockBasisOn(e_a); ρ₀]`
  corner LI from the candidate-slot gate (= KT (6.66) `Mᵢ = [r(Lᵢ); ±r]`). Its consumer is 23f's post-row-op
  corner-`hA` bridge.
- **Bottom + bricks** (landed earlier): the `mixedBottom` family +
  `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` (`Concrete.lean:1685`, supplies `hD`);
  `rigidityMatrixEdge_mul_columnOp_apply_pin_zero`/`_apply_corner`/`_apply_eB_off_pin`/`_apply_off_pin`.

## Hand-off → 23f (the geometry arm)

**23f's first buildable commit = the geometry arm `hblock`/`hA` construction** — full plan in `notes/Phase23f.md`.
The cert's block data is built from the IH-fed `cGv` widening (W6b producer `exists_candidateRow_bottomRows_of_rigidOn`,
takes `hrig`/`h622lb`), so it is genuinely 23f-arm-coupled; the single arm-coupling is `L₀` (= the `cGv` weights),
the `re`/`m₂` split is framework-determined. Three new leaves + assembly: (i) the `cGv`→`w` re-key leaf
(`Gv.IsLink`→`m₂` + `of_eq_mul_of_row_comb`, arm-coupled — a RANK-route weight, so the §(4.44) `hbotmem` wall
does NOT reform); (ii) the `Lrow`-on-`p` reindex unit-det bridge (`reindex e e (fromBlocks 1 (−L₀') 0 1)` +
`det_reindex_self`, genuinely-new); (iii) the post-row-op corner-`hA` bridge (`A' = A − L₀C` reads as
`[blockBasisOn(e_a); ρ₀]`, close via `corner_hA'_of_gate`, genuinely-new). Then item 3c (the candidate-matching
gate bridge), item 4 (the dispatch + CHAIN-5) → 23g (ENTRY) → 23h (ASSEMBLY).

## Decisions made during this phase (settled — one-line verdicts; full traces in design §(4.44)–(4.54) + git)

- **De-risking arc (sessions #36–39) → the A3-transposed cert.** §(4.44)/(4.45) WALL (option-2 `hbotmem`
  unsatisfiable; R1/R2/R3 all wall on the §(4.29) override gate) → §(4.46)/(4.47)/(4.48) the wall is a
  dual-span-representation artifact / literal-`Matrix` does not escape / `R(Gab)`-reproduction kernel-grounded
  NO-GO (representation-mismatch, not open math) → user chose the genuinely-new cert → §(4.49) the
  A3-transposed `fromBlocks A 0 C D` shape (NOT §(4.42)'s Schur) → §(4.50)/(4.51)/(4.52) the corner
  `Mᵢ`-invertibility is ALREADY LANDED general-`d` (the discriminator + callees are `{k:ℕ}`, fired by
  `exists_shared_redundancy_and_matched_candidate`) → §(4.53) route (A): the cert needs a LEFT row op `Lrow`,
  two LEAF-RowOp leaves + a `Lrow`-reshape → §(4.54) the reshaped cert is SATISFIABLE end-to-end, cert scope
  COMPLETE; the geometry arm is 23f.
- **Cert before dispatch; `d=3` zero-regression via a cert FORK.** The dispatch consumes the cert, so the cert
  (23e) precedes the dispatch + CHAIN-5 (23f). `d=3` keeps the `_matrix`/M₃ path; only the general-`d` arm
  routes through `case_III_rank_certification_zero₁₂` — do NOT try to unify the two.
- **Below the CHAIN↔ENTRY contract + the motive/IH.** The cert + arm are infrastructure beneath the dispatch
  (C.3) and the `ChainData` record (C.1); the reshape does not touch the `hdispatch` consume-shape or the
  0-dof motive. The frozen interface (C.0–C.6) + the sanctioned C.3 `hIH` addition stay valid for 23f.
- **Items (3a)–(3b‴) cert-layer LANDED** (axiom-clean): the forked A3-transposed cert + scaffolding (3a); the
  `corner_hA'_of_gate` corner gate (3b `hA` half); LEAF-RowOp-1/2 (3b′, both needed `[DecidableEq m₁/m₂]` for
  the identity-matrix `One` instance); the `Lrow`-reshape threading the unit-det LEFT factor through the cert
  chain (3b″); the `B = L₀ * D` matrix-algebra half `Matrix.of_eq_mul_of_row_comb` (3b‴, upstream-eligible).
  Two Lean-mechanics gotchas → TACTICS-QUIRKS § 69 (the subtype `Fintype {e // e ∈ G.edgeSet}` binder; `Lrow`
  must be typed at the candidate-graph edgeSet for `*` to compose syntactically, which forced dropping `set F₀`).

### Carried-forward interface decisions (for 23f)

- **C.3 `hIH`-on-consume-shape addition — APPROVED** (user-adjudicated 2026-06-26, session #36). The interior
  arm needs the INTERIOR-split `hsplitGP`, derivable only from `hIH` via `splitOff_isMinimalKDof`, not in the
  frozen C.3 signature — so add `hIH` to the C.3 dispatch consume-shape: a one-field addition touching the C.0
  producer/consumer/ENTRY lockstep trio, NOT a motive/IH-strength change. Lands with 23f. Context: design
  §(4.43) *THE ONE INTERFACE OBLIGATION* + §C.3.
- **Interior arm wrapper landed, parks in 23f** (`chainData_arm_realization_sep`, `CaseIII/Realization.lean`).
  The `ChainData`-indexed sibling of `chainData_split_realization`; sound (carries the disjoint-block
  obligations as hypotheses) but consumes the walled `hbotmem`, so it waits for the sound cert to be wired
  through (23f).
- **GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive) — orthogonal to the cert; tracked
  separately, lands with 23f/the spine.
