# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress, **route (D) ADJUDICATED FEASIBLE — clear path to CHAIN close, BUILD next** (§(4.78)).
The fifth CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d + 23e + 23f). 23e landed the KT-faithful A3-transposed
rank certificate + its LA scaffolding axiom-clean (`notes/Phase23e.md`); 23f builds the **geometry arm** that
*constructs* the cert's block data, then the chain dispatch + CHAIN-5. The interior-corner cert is BUILT
(D-CAN-1..3b + the `hsupp`/`hgp`/`Gab`-bottom/`hfr₂` feeders). Route α (the corner 3-normal-LI source) is DEAD
(§(4.77): its `_escape` side-condition is provably false for reachable joins). The route-(D) feasibility spike
(§(4.78), kernel-checked) found route (D) = the **LANDED `_aug` ladder** (`rigidityMatrixEdgeAug` cert +
engine + arm, αE1–αE4) fired on the **D-canonical PIN-ZERO bottom** (`C = 0`) — a combination §(4.67)/§(4.68)
never tested (they had `C ≠ 0`). Under `C = 0` the operated corner `A − L₀·C = A`, the augmented `inr ()` `±r`
row (oriented `hingeRow b v ρ₀`) reads `−ρ₀` at the v-pin (PROBE 5), so `corner_hA'_of_gate` fires from the
discriminator gate ALONE — no `n'`-escape, no side-condition, no override-gate re-entry. The remaining work is
a SMALL family of augmented-matrix bricks (D1–D4, siblings of the landed un-augmented ones) + the dispatch,
~5–8 commits. **Phase 23 stays in progress.** Authoritative recon: `notes/Phase23-design.md` §(4.78) (the
route-(D) feasibility verdict + sub-commit list), on top of §(4.71)/(4.72) (D-canonical + `hsupp` gate-free).
Route history §(4.54)→(4.66)→(4.67)→(4.68)→(4.71)→(4.74)→(4.75)→(4.77)→(4.78). Program map:
`notes/MolecularConjecture.md`.

## Current state

**ROUTE (D) IS THE LIVE ROUTE — ADJUDICATED FEASIBLE (§(4.78), kernel-checked); next action is the BUILD,
not a decision.** Route α (the corner 3-normal-LI source) is DEAD (§(4.77): the `_escape` side-condition
`∃ i, p i ⬝ᵥ q b ≠ 0` is provably false for reachable joins; the `_escape` LA core + the `_of_triLI` corner
chain stay correct-but-unused, they consume `htriLI` as a hypothesis). **Route (D) = fire the LANDED `_aug`
ladder on the D-canonical PIN-ZERO bottom** (§(4.78)): the augmented cert/engine/arm
(`case_III_rank_certification_aug` `Candidate.lean:2694` / `finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂`
`Concrete.lean:1258` / `case_III_arm_realization_aug` `ForkedArm.lean:426`, the αE1–αE4 "landed-but-dead"
ladder) carry a GENUINE `ρ₀` row in the `inr ()` slot of `rigidityMatrixEdgeAug`. Under the D-canonical bottom
the bottom is the literal `R(Gab)` (full-rank, NO `e_b`-fill ⟹ `C = toBlocks₂₁ = 0`), so the operated corner
`A − L₀·C = A` is **bare** `A.row` LI, and the augmented `inr ()` `±r` row — oriented `hingeRow b v ρ₀` (head
the OTHER neighbor `b`, tail the pin `v`) — reads `−ρ₀ (finScrewBasis c)` at the v-pin THROUGH the column op
(PROBE 5, sorry-free), so `A = coordEquiv ∘ [blockBasisOn(e_a); −ρ₀]` and `corner_hA'_of_gate`
(`Concrete.lean:810`) fires from the discriminator's NONZERO gate ALONE (PROBE 4). This is the combination
§(4.67)/§(4.68) never tested — they blocked `_aug` under the `mixedBottom` (`C ≠ 0`); the D-canonical bottom
(post-dating them, §(4.71)) makes `C = 0`. No `n'`-escape, no side-condition, no override-gate re-entry
(§(4.78.4), verified). The four genuinely-new bricks (D1–D4: augmented corner-apply / C=0 collapse /
`hA` leaf / `hM'eq`, all siblings of landed un-augmented ones) + the dispatch = ~5–8 commits to CHAIN close.

The interior-corner cert is BUILT (D-CAN-1..3b + the `hsupp`/`hgp`/`Gab`-bottom/`hfr₂` feeders, all
gate-free); the §(4.29) `caseIIICandidate`-override gate wall is DISSOLVED at its root by the D-canonical
support-extensor re-keying. The §(4.73.2) seam was a MISDIAGNOSIS (kernel-checked): the corner consumes the
DIRECT-`q` NONZERO gate `ρ₀(F.supportExtensor e_a) ≠ 0`, NO `shiftPerm`.

**The dead `ρ₀`-route OPERATED leaves (OFF-path; kept in tree, phase-close cleanup candidates):** the A6
operated-corner identity `submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_eq_coordEquiv` + the operated `hA`
bundle `…_row_linearIndependent_of_gate` + leaf (iii) `corner_hA_zero₁₂_of_gate` (they presume `C ≠ 0`). The
`hB`-machinery (`dual_comb_reindex_fiberwise` + `submatrix_columnOp_toBlocks₁₂_eq{,_mul_toBlocks₂₂}`) is
ON-path (still discharges the augmented arm's `hB`, via span-membership / the `B = L₀·D` factoring).
**The §(4.75) un-augmented `ρ₀`-free incomparability core was the route-(a)/route-α path (now dead-source).**
That route also exploited `C = 0` (`A − L₀·C = A`, bare `A.row` LI) but read the `±r` slot as an `e_b`-block
basis vector `blockBasisOn(e_b, j₀)`, needing only block INCOMPARABILITY — landed `ρ₀`-free
(`hingeRowBlock_not_le_of_supportExtensor_not_mem_span` + `exists_corner_blockBasisOn_linearIndependent_of_not_le`
+ the source leaves `panelSupportExtensor_not_mem_span_of_triLI` / `chainData_arm_corner_blockBasis_linearIndependent_of_triLI`).
But it reduced `hA` to the direct-`q` 3-normal LI `![q a, n', q b]`, whose only source was route α (DEAD,
§(4.77)). Those incomparability leaves are correct-but-unused under route (D) (which instead carries the
GENUINE `ρ₀` augmented `inr` row — reading `−ρ₀` at the v-pin, no incomparability/3-normal-LI needed); kept in
tree. `d=3` stays fully green (hard constraint).

**Landed (all axiom-clean, GATE-FREE, in tree — per-leaf detail in *Lemma checklist* + *Still-live*):**
- **D-CAN-1** the canonical, support-extensor-keyed hinge-block basis + the `blockBasisOn`/`blockBasis` def
  swap + `_congr` lemmas (`Concrete.lean`; type-transparent drop-in, ZERO interface breaks).
- **D-CAN-2** the literal-`Matrix` (C) bottom bridge `submatrix_columnOp_toBlocks₂₂_eq_Gab` (`Concrete.lean`;
  the PROBE-Q2 transport — `blockBasisOn_congr` firing inside the `hingeRow`/`Pi.single` wrapper — closing the
  §(4.70)-blocked equality in 3 lines).
- **D-CAN-3a** the (C) `hD` leaf `linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq` + its rank sibling
  `rank_columnOp_toBlocks₂₂_eq_finrank_span_Gab` over the literal IH bottom (`Concrete.lean`; replaces the
  `mixedBottom` `hD` route, same target type, so the §(4.29) gate never forms).
- **D-CAN-3b** the interior-arm spine `chainData_arm_realization_zero₁₂` (`Realization.lean`, after
  `chainData_arm_realization_sep`; fires the `_zero₁₂` cert via `case_III_arm_realization_rowOp`, carrying the
  row-op matrix data + candidate edge-facts + gates + `hends_Gv`/`hne_Gv` as hypotheses for the dispatch — as
  `_sep` does its disjoint-block obligations).
- **D-CAN-4 feeders** (all gate-free): the two cross-framework `hsupp` leaves + the `∀ i` producer
  `caseIIICandidate_hsupp_of_rowClassifier`; the candidate `hgp` producer
  `caseIIICandidate_supportExtensor_ne_zero_of_genPos`; the `Gab` bottom-selection producer
  `bottom_selection_of_crossFramework_span_Gab` (+ feeder `span_range_aShifted_blockBasisOn_eq_rigidityRows`);
  the IH-bottom finrank-count producer `exists_ofNormals_finrank_span_rigidityRows_eq_of_hsplitGP`.
- **route-α LA core** `exists_independent_perp_family_escape` (`Claim612.lean`) — the strengthened
  perp-family lemma (escape `span {n_u, w}` for any `w ∉ ker (of p)`); the engine the strengthened
  discriminator builds the corner transversal through.

**§(4.72) settled the make-or-break gate-free** (the `hsupp` discharge for the real candidate↔IH-`Q` pair, the
crux the §(4.71) plan asserted but did not compiler-verify): both bottom-row kinds discharge via the candidate
override ACCESSORS — off-slot via `caseIIICandidate_supportExtensor_of_ne`; the §(4.65)-feared a-shifted
`e_b`-fill row via `caseIIICandidate_supportExtensor_reproduced` (a `Function.update_self`); the chain relabel
via `ofNormals_supportExtensor_relabel_perm` — never the gate `ρ₀ ⊥̸ C(vᵢ₊₁,n')`, the discriminator, or a span
membership. `q := Q.normal` is the established conflict-free placement (no new dispatch obligation). So the
§(4.29) wall is DISSOLVED, not relocated.

**Route history (settled/dead — full arc in git + design §(4.66)/(4.68)/(4.69)/(4.70)):** the route-(α)
`_aug`/`_rowOp`/chain-arm ladder (αE1–αE5) is landed-but-dead; the three as-scoped escapes (α1)/(α2)/(C) were
all blocked-or-relocate under the *opaque* `blockBasisOn` (§(4.68)–(4.70)); (D-canonical) re-keys the basis on
the support extensor and dissolves that wall. Cert card target unchanged: `card m₁ + card m₂ = D·(|V(G)|−1) ≤
(D−1)·|E(G)|` (an inequality, no isostatic-tightness forced).

## Architectural choices made up front (inherited from 23e / the frozen contract)

- **Cert is consumed, not re-derived.** The 23e cert chain is axiom-clean + SATISFIABLE; 23f only *produces*
  its block data. Build against the literal `Lrow * M * U` product, NOT the component leaves in isolation
  (the §(4.46)/(4.54) lesson — compiler-check the FULL composition before declaring "remaining = assembly").
- **The interior-corner cert is the literal-IH-bottom (C) cert via (D-canonical)** (design §(4.71)); the
  route-(α) `±r`/row-op corner framing is dead-arm (git + design §(4.66)).
- **`d=3` zero-regression via the cert FORK.** `d=3` keeps the `_matrix`/M₃ path; only the general-`d` arm
  routes through `case_III_rank_certification_zero₁₂`. Do NOT unify the two.
- **Below the CHAIN↔ENTRY contract + the motive/IH.** The geometry arm + dispatch are below C.3/C.1 and the
  0-dof motive. The frozen interface (C.0–C.6) + the sanctioned C.3 `hIH` addition stay valid.

## Lemma checklist

**The LIVE forward plan is item (4) — (D-canonical), the D-CAN-1..4 sequence (design §(4.71.4),
kernel-de-risked §(4.71); `hsupp` gate-free §(4.72)).**

**Route-(α) ladder (the former checklist items (i)–(HB)) — LANDED-but-DEAD** (the `_aug`/`_rowOp`
interior-corner strategy D-canonical replaced; settled detail in git + design §(4.66)/(4.68)). **REUSED by
D-canonical** (see *Still-live*): B1/B2, leaf (i) `matrix_eq_mul_of_dual_row_comb`, leaf (iii)
`corner_hA_zero₁₂_of_gate`, BOT-3′, `finScrewDimSplitCorner`, the `_mixedBottom_of_finrank_eq` HD producer,
the free BOT-2, the `_rowOp` wrapper + `_zero₁₂` cert + edge-`_zero₁₂` engine, BOT-1/R1, D1
`interior_hsplitGP`. The αE5 deletion removed only the `(e_b,j₀)`-collision machinery (zero-caller orphans).

- [→] **(4) the realization arm + dispatch — BUILD via (D-canonical).**
  - [x] **D-CAN-1** canonical basis + def swap + `_congr` (`Concrete.lean`) — ✓ LANDED axiom-clean; zero
    interface breaks (the §(4.71.3) type-transparent-drop-in prediction held).
  - [x] **D-CAN-2** the literal-`Matrix` (C) bottom bridge `submatrix_columnOp_toBlocks₂₂_eq_Gab`
    (`Concrete.lean`) — ✓ LANDED axiom-clean (PROBE-Q2 transport).
  - [x] **D-CAN-3a** the (C) `hD` leaf `linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq` + rank sibling
    (`Concrete.lean`) — ✓ LANDED axiom-clean (near-verbatim transfer of the `_mixedBottom` rank/LI pair).
  - [x] **D-CAN-3b** the interior-arm spine `chainData_arm_realization_zero₁₂` (`Realization.lean`) — ✓
    LANDED axiom-clean (fires the `_zero₁₂` cert; obligations carried for the dispatch).
  - [~] **D-CAN-4** the dispatch + CHAIN-5 + the C.3 `hIH` one-field add. **IN PROGRESS — all feeders landed:**
    - [x] the cross-framework `hsupp` leaves
      (`caseIIICandidate_supportExtensor_eq_ofNormals_of_ends_eq` off-slot +
      `caseIIICandidate_supportExtensor_reproduced_eq_ofNormals` a-shifted `e_b`-fill) + the assembled `∀ i`
      producer `caseIIICandidate_hsupp_of_rowClassifier` (`Candidate.lean`). GATE-FREE.
    - [x] the candidate `hgp` producer `caseIIICandidate_supportExtensor_ne_zero_of_genPos`
      (`Candidate.lean`). GATE-FREE.
    - [x] the `Gab` bottom-selection producer `bottom_selection_of_crossFramework_span_Gab` + its feeder
      `span_range_aShifted_blockBasisOn_eq_rigidityRows` (`Concrete.lean`) — the
      `reInr`/`re₂`/`hbot2`/`hbot1`/`hj`/`hsupp`/`hrank` index bundle D-CAN-3a's `hD` consumes. GATE-FREE.
    - [x] the IH-bottom full-rank count `hfr₂` producer
      `exists_ofNormals_finrank_span_rigidityRows_eq_of_hsplitGP` (`Realization.lean`) — the
      `q`/GP/link-record/`ℕ`-finrank bundle off the def-0 IH `hsplitGP`, feeding the selector's `hfr₂` slot.
      GATE-FREE.
    - [x] **the `chainData_dispatch` composition SPIKE** (§(4.73), `SpikeDispatch.lean`, kernel-checked) —
      9/13 obligations compose sorry-free; 4 residuals + 1 placement seam mapped to buildable sub-commits.
    - [x] **the §(4.73.2) placement seam RESOLVED + the `hA` leaf LANDED**
      `chainData_arm_corner_hA_of_discriminator_gate` (`Realization.lean`, after the spine) — the seam was a
      MISDIAGNOSIS (the perp-producer is dead-arm; the corner consumes the direct-`q` NONZERO gate); the `hA`
      leaf is sorry-free modulo the carried `hAeq` (KT 6.66). GATE-FREE, axiom-clean.
    - [x] **the `hAeq` leaf (KT 6.66, §(4.73.4) item (2)) LANDED**
      `submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_eq_coordEquiv` (`Concrete.lean`, A6) — the
      operated-corner matrix-entry identity: `toBlocks₁₁ − L₀·toBlocks₂₁ = coordEquiv ∘ φ` for the operated
      corner-functional family `φ` (corner panel `−` `L₀`-weighted bottom; `hφ` carries the KT-6.66 `ρ₀`
      coupling for the dispatch). Composes `_apply_corner`/`_apply_pin_zero`; abstract over `L₀`/`φ`.
      GATE-FREE, axiom-clean.
    - [x] **the CORNER-BLOCK `hA`/`hB`/`L₀` sub-assembly LANDED** (`Concrete.lean`, A6, all axiom-clean,
      GATE-FREE) — the corner half of the spine's obligations through ONE explicit `L₀`:
      - `dual_comb_reindex_fiberwise` (the engine, the fiberwise `cGv`→`L₀`-row re-key; `matrix_eq_mul_of_
        dual_row_comb` refactored to delegate).
      - `submatrix_columnOp_toBlocks₁₂_eq` (the corner `B`-block read: every corner row off-`v` reads its
        `a`-shifted `hingeRow`, `_apply_eB_off_pin`; the `e_a` panel rows' `B`-fill is `hingeRow a a · = 0`).
      - `submatrix_columnOp_toBlocks₁₂_eq_mul_toBlocks₂₂` (the `hB`/`L₀` factoring: `toBlocks₁₂ =
        L₀·toBlocks₂₂` for the explicit fiberwise `L₀`, given the per-corner-row `hcomb` widening).
      - `toBlocks₁₁_sub_mul_toBlocks₂₁_row_linearIndependent_of_gate` (the `hA` bundle: `(A − L₀·C).row` LI,
        composing the item-(2) `hAeq` identity with `corner_hA_zero₁₂_of_gate`, given the gate + `hφ`).
    - [x] **the NON-`ρ₀` corner-LI core** (the pin-zero-`C` re-route; §(4.75)) —
      `hingeRowBlock_not_le_of_supportExtensor_not_mem_span` (incomparability from support non-parallelism) +
      `exists_corner_blockBasisOn_linearIndependent_of_not_le` (corner family LI from incomparability)
      (`Concrete.lean`, both `ρ₀`-free, axiom-clean). Sidesteps the false `blockBasisOn(±r) = ρ₀`: under the
      pin-zero `Gab` bottom `hA` = bare `A.row` LI via `linearIndependent_toBlocks₁₁_row_of_corner_gate`.
    - [x] **the incomparability SOURCE leaf + the corner-LI chain (route (a), §(4.75.3) RESOLVED)** —
      the panel-meet non-parallelism leaf `panelSupportExtensor_not_mem_span_of_triLI` (`PanelLayer.lean`,
      `C(e_a) ∉ span {C(e_b)}` from the 3-normal LI `![q a, n', q b]`; via
      `normalsJoin_pair_linearIndependent_of_triLI` + `panelSupportExtensor_linearIndependent_iff`) + the
      spine-binding corner-LI chain `chainData_arm_corner_blockBasis_linearIndependent_of_triLI`
      (`Realization.lean`, composing PROBE A + the landed incomparability + corner family LI; the spine's
      direct-`q` candidate/reproduced supports threaded). BOTH axiom-clean, GATE-FREE. **The corner `hA`
      now reduces to exactly ONE carried genuinely-new input: the direct-`q` 3-normal LI `![q a, n', q b]`
      (`n'` off `span {q a, q b}` — KT general position on the panels, NOT a discriminator output as-is).**
      Route (a) chosen over route (b): the spine is direct-`q` (forced by the direct-`q` NONZERO gate), so
      its reproduced panel is the SHORT-CIRCUIT panel `(vtx(i+1), vtx(i-1))` — distinct from the landed perp
      crux's chain-edge panel `(vtx(i+1), vtx i)` (the relabel-`q`-equivalent; §(4.73.2) seam REAL for the
      perp). DECISION FLAGGED — see *Blockers*.
    - [x] **the route-α LA core `exists_independent_perp_family_escape`** (`Claim612.lean`, next to
      `exists_independent_perp_family`) — the strengthened perp-family lemma: with `m ≤ k` kept points,
      `n_u` perp to all + `≠ 0`, AND `w` NOT perp to all (`∃ i, p i ⬝ᵥ w ≠ 0`), produces `n'` perp to
      the kept points, `![n_u, n'] LI`, AND `n' ∉ span {n_u, w}`. The reusable engine the strengthened
      discriminator builds its transversal through (so `n'` escapes the chain plane `span {q a, q b}`,
      `n_u := q a`, `w := q b`). The `W ⊓ ker L = span {n_u}` count: `w ∉ ker L` collapses the
      intersection to 1-dim, proper in the ≥2-dim `ker L`. GATE-FREE, axiom-clean (`propext`,
      `Classical.choice`, `Quot.sound` only). LANDED this session.
    - [✗] **the 3-normal-LI producer — ROUTE α DEAD (§(4.77)).** Its side-condition `∃ idx, p idx ⬝ᵥ q b ≠ 0`
      is provably FALSE for reachable matched joins. SUPERSEDED by route (D) (§(4.78)) — the corner `hA` no
      longer needs the 3-normal LI; it carries the genuine `ρ₀` augmented `inr` row instead.
    - [→] **ROUTE (D) — BUILD (§(4.78), adjudicated FEASIBLE).** Fire the LANDED `_aug` ladder on the
      D-canonical pin-zero bottom; the augmented `inr ()` `±r` row (`hingeRow b v ρ₀`) reads `−ρ₀` at the v-pin
      (PROBE 5), `corner_hA'_of_gate` fires from the discriminator gate alone (PROBE 4). The four genuinely-new
      bricks (D1–D4: augmented corner-apply / C=0 collapse / `hA` leaf / `hM'eq`) + the augmented spine +
      `re`/`hre` + the dispatch + CHAIN-5 + the C.3 `hIH` add — ~5–8 commits to CHAIN close (the §(4.78.5)
      sub-commit list, copied into *Hand-off*). No new geometry, no contract/motive change, no override-gate
      re-entry.

  A1–A5c (matrix model + column op + block-additivity backbones `Rank.lean:480/574/622`) + D1
  `interior_hsplitGP` ✓ LANDED and REUSED. The `_aug` ladder is NOW LIVE (route (D)); `_matrix`/`_rowOp`/chain
  dead arms stay landed-but-dead (αE6 retire DEFERRED to phase-close).

## Blockers / open questions

- **THE CORNER `hA` SOURCE — ROUTE (D) ADJUDICATED FEASIBLE; BUILD NEXT (§(4.78)).** Route α (the 3-normal-LI
  source) is DEAD (§(4.77): the `_escape` side-condition `∃ i, p i ⬝ᵥ q b ≠ 0` is provably false for reachable
  joins). Route (D) — fire the LANDED `_aug` ladder on the D-canonical PIN-ZERO bottom — is feasible
  (kernel-checked, §(4.78)): under `C = 0` the operated corner `A − L₀·C = A`, the augmented `inr ()` `±r` row
  (oriented `hingeRow b v ρ₀`) reads `−ρ₀` at the v-pin (PROBE 5, through the column op), so the corner family
  is `[blockBasisOn(e_a); −ρ₀]` and `corner_hA'_of_gate` (`Concrete.lean:810`) fires from the discriminator's
  NONZERO gate alone (PROBE 4). This is the combination §(4.67)/§(4.68) never tested — they blocked `_aug`
  under the `mixedBottom` (`C ≠ 0`, the count forced the v-incident `e_b`-fill into the bottom); the
  D-canonical bottom (literal `R(Gab)`, full-rank, no `e_b`-fill ⟹ `C = 0`) post-dates them (§(4.71)). The
  genuinely-new work is FOUR augmented-matrix bricks D1–D4 (augmented corner-apply / C=0 collapse / `hA` leaf /
  `hM'eq`, each a sibling of a landed un-augmented one + a kernel one-liner) + the dispatch — ~5–8 commits, no
  new geometry, no contract/motive change, no override-gate re-entry (§(4.78.4)). See *Hand-off* for the
  sub-commit list. The `_escape` LA core + the route-(a) incomparability/3-normal-LI leaves stay
  correct-but-unused (they consume `htriLI`/`hw` as hypotheses); the OPERATED `hAeq` `ρ₀`-route leaves stay
  dead (`C ≠ 0`).
- **C.3 `hIH`-on-consume-shape addition — APPROVED** (user-adjudicated 2026-06-26, session #36; lands at
  D-CAN-4/CHAIN-5 with `chainData_dispatch`). The interior arm needs the INTERIOR-split `hsplitGP`
  (`G.splitOff vᵢ …`), derivable only from `hIH` via `splitOff_isMinimalKDof` — D1 `interior_hsplitGP` ✓
  LANDED; the C.3 dispatch consume-shape gets the `hIH` field added when `chainData_dispatch` is wired (a
  one-field addition touching the C.0 producer/consumer/ENTRY lockstep trio, NOT a motive/IH-strength change).
  Context: design §(4.43) *THE ONE INTERFACE OBLIGATION* + §C.3.
- **THE INTERIOR-ARM CORNER — RESOLVED + BUILT via (D-canonical) (D-CAN-1..3b LANDED).** The
  support-extensor-keyed canonical `blockBasisOn` (D-CAN-1) made the cross-framework basis equality provable +
  transportable to the literal `Matrix`-row equality `submatrix_columnOp_toBlocks₂₂_eq_Gab` (D-CAN-2), so the
  (C) bottom is the literal IH matrix `R(Gab)` full rank (D-CAN-3a's `hD`), the §(4.29) gate never forms, and
  the interior arm `chainData_arm_realization_zero₁₂` (D-CAN-3b) fires the `_zero₁₂` cert. The `hsupp`
  gate-free discharge (§(4.72)) is now a landed D-CAN-4 feeder. Only the `chainData_dispatch` wiring remains.
- **THE §(4.73.2) PLACEMENT SEAM — RESOLVED (no reconciliation needed; the `hA` leaf is LANDED).** The design
  doc's seam was a MISDIAGNOSIS: it cross-wired the dead-arm `_sep` route's perp-producer
  (`interior_hρe₀_of_widening`, `q∘shiftPerm` perp `= 0`) into the live `_zero₁₂` corner leaf, but
  `corner_hA_zero₁₂_of_gate` consumes the **direct-`q` NONZERO** gate the discriminator already outputs. The
  `hA` leaf `chainData_arm_corner_hA_of_discriminator_gate` (`Realization.lean`) threads it sorry-free (modulo
  the carried `hAeq`). See *Decisions made → The §(4.73.2) seam misdiagnosis*.
- **GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive) — orthogonal to the cert;
  tracked separately, lands with D-CAN-4/the dispatch.
- **Downstream (23g+):** ENTRY's `exists_chain_data_of_noRigid` reshape + floor lift + OD-1, then ASSEMBLY.
  The frozen contract (C.5/C.6) is invariant; none touches 23e's cert. ENTRY is parallel-safe.

## Hand-off / next phase

**BUILD ROUTE (D) — adjudicated FEASIBLE (§(4.78), kernel-checked); the next action is the build, not a
decision.** Route (D) = fire the LANDED `_aug` ladder (`case_III_rank_certification_aug` `Candidate.lean:2694`
/ `case_III_arm_realization_aug` `ForkedArm.lean:426` over `rigidityMatrixEdgeAug` `Concrete.lean:1045`) on
the D-canonical PIN-ZERO bottom, carrying a GENUINE `ρ₀` row in the `inr ()` slot. Under `C = 0` the operated
corner `A − L₀·C = A`, the `inr ()` `±r` row (`rRow := hingeRow b v ρ₀`) reads `−ρ₀` at the v-pin (PROBE 5),
and `corner_hA'_of_gate` fires from the discriminator's NONZERO gate alone (PROBE 4). The §(4.78.5) sub-commit
list (~5–8 commits to CHAIN close):

1. **D1 + D2 (`Concrete.lean`)** — the augmented corner-apply `rigidityMatrixEdgeAug_mul_columnOp_apply_corner_inr`
   (the `inr ()` row at the v-pin reads `−ρ₀`; kernel core = PROBE 5; the `inl` e_a-panel rows reuse the landed
   `rigidityMatrixEdge_mul_columnOp_apply_corner`) + the augmented C=0 collapse
   `rigidityMatrixEdgeAug_mul_columnOp_submatrix_toBlocks₂₁_eq_zero` (clone of the landed un-augmented
   `_submatrix_toBlocks₂₁_eq_zero` `:1774`, over the augmented row index, bottom `m₂` pure-`Gab`). ~1–2 commits.
2. **D3 + D4 (`Concrete.lean`/`Candidate.lean`)** — the augmented corner `hA` leaf (under `C = 0`,
   `A.row = coordEquiv ∘ [blockBasisOn(e_a); −ρ₀]` LI via `corner_hA'_of_gate` + `Matrix.linearIndependent_row_of_coordEquiv`)
   + the augmented `hM'eq`/`hblock` read (the `_aug` arm's `⚑` residual `ForkedArm.lean:421`). ~1–2 commits.
3. **the augmented-arm spine `chainData_arm_realization_aug_zero₁₂` (`Realization.lean`)** — clone
   `chainData_arm_realization_zero₁₂` (`:1481`) with `case_III_arm_realization_rowOp → _aug`, carrying
   `rRow := hingeRow b v ρ₀` + `hr` (the chain-pair perp `ρ₀(C(a,b)) = 0` via
   `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` `Candidate.lean:2286`) + `hρe₀` (the matched gate). ~1 commit.
4. **`re`/`hre`** — the corner⊕bottom `Sum.elim` selector (corner → `inl` e_a-panel + `inr ()`; bottom → the
   `reInr` Gab-selector `bottom_selection_of_crossFramework_span_Gab` LANDED) + injectivity. ~1 commit.
5. **the `chainData_dispatch` router + CHAIN-5 + the C.3 `hIH` add** — `Fin cd.d`: base/`d=3` → landed
   `chainData_split_realization`; interior `2 ≤ i` → the augmented spine of (3). ~1–2 commits. **Gate:** full
   `lake build` green + `lake lint` clean + axiom-clean.

On (5) landing the CHAIN layer closes and ENTRY (23g) opens. The αE6 retirement of the now-LIVE `_aug` ladder
is MOOT (route (D) uses it); the dead arms to retire shrink to `_matrix`/`_rowOp`/the dual-space chain arm.

**The obligation→feeder wiring (the 9/13 §(4.73) obligations unchanged; §(4.72.3) + §(4.43)):**
the `Fin cd.d` router: base/`d=3` → the landed `chainData_split_realization`; interior `2 ≤ i` → the augmented
spine (sub-commit 3 above, the `_aug`-fired clone of D-CAN-3b's `chainData_arm_realization_zero₁₂`). Per-obligation:
- **`hgp`** from `caseIIICandidate_supportExtensor_ne_zero_of_genPos`: `hgppair` = the IH `Q`'s panel general
  position (every distinct pair LI; from `Q.IsGeneralPosition` via `ofNormals_normal`, the `hgp_split a b`
  pattern at `chainData_split_realization:1184`); `hends` = the candidate `ends`-override's link record +
  `heab`/`hLn`/`hgab` from the `cd`-accessors + the discriminator's transversal `n'`.
- **the bottom `re`/`hre`/`hD`** via `bottom_selection_of_crossFramework_span_Gab`: build `lift` (KT's (6.62)
  row map — surviving `Gv`-edge → same `Gab`-edge via `hle`; the a-shifted `e_b`-fill → the fresh `e₀` via
  `he₀ab`), `hlift_ends`/`hlift_supp` (recorded-endpoint + support agreement off the candidate `ends`-override
  + `caseIIICandidate_supportExtensor_of_ne`/`_reproduced`, with the relabel
  `ofNormals_supportExtensor_relabel_perm`), and the bottom seed `q`/GP/link-record/`hfr₂` from
  `exists_ofNormals_finrank_span_rigidityRows_eq_of_hsplitGP` (at the interior `interior_hsplitGP` split,
  def-0); the producer returns `reInr`/`re₂`/`hbot2`/`hbot1`/`hj`/`hsupp`/`hrank`, then `Sum.elim` `reInr`
  with the corner injection's `m₁`-half to form `re`/`hre`, and fire D-CAN-3a's `hD`
  (`linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq`).
- **the corner `hA`** — route (D), the augmented `inr ()` `±r` row carrying genuine `ρ₀` (the D3/D4 augmented
  bricks above). Under the augmented C=0 collapse (D2) `A − L₀·C = A`; the corner reads
  `coordEquiv ∘ [blockBasisOn(e_a); −ρ₀]` (D1 + the un-augmented `_apply_corner` for the `inl` rows), closed by
  `corner_hA'_of_gate` + `Matrix.linearIndependent_row_of_coordEquiv`. **`hB`/`hM'eq`/`L₀`** via the
  `hB`-machinery (span-membership and/or the exact-combination factoring; the row op `Lrow` STILL zeros the
  off-pin `B`, but `hA` no longer depends on `L₀` under `C = 0`); `hne_Gv` from the candidate GP; the
  placement `q := Q.normal` (the established pattern, d=3 `hQeq` `:303`; general-`d` `chainData_split_realization` `:907`).
- Then **CHAIN-5** + the **C.3 `hIH`** one-field add (§(4.43); D1 `interior_hsplitGP` `Realization.lean:758`
  consumes it for the interior `hsplitGP`). **Gate:** full `lake build` green + `lake lint` clean + axiom-clean.

**Still-live / reusable (in tree, axiom-clean) — all REUSED by the D-CAN plan:** A1–A5c (the matrix model +
column op `U` `Concrete.lean:1259/1274` + block-additivity backbones `Rank.lean:480/574/622`); D1
`interior_hsplitGP` (`Realization.lean:758`, the IH full-rank `R(Gab)`); the discriminator
`exists_shared_redundancy_and_matched_candidate` (`Realization.lean:1481`, the moving-member pick + gates
`hperp` `:1511` / `hρe₀` `:1535`); the realization tail `case_III_realization_of_rank` (`Arms.lean:63`,
consumes only `hrank`, W6e input unchanged by the bottom shape); the D-CAN landings —
`submatrix_columnOp_toBlocks₂₂_eq_Gab` (D-CAN-2), `linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq` +
`rank_columnOp_toBlocks₂₂_eq_finrank_span_Gab` (D-CAN-3a), `chainData_arm_realization_zero₁₂` (D-CAN-3b,
the model the route-(D) augmented spine clones), the `hsupp`/`hgp`/`Gab`-bottom/`hfr₂` feeders (D-CAN-4);
**the route-(D) `_aug` ladder (NOW LIVE, §(4.78)):** `rigidityMatrixEdgeAug` (`Concrete.lean:1045`),
`rigidityMatrixEdgeAug_rank_le_finrank_span` (`:1071`), `finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂`
(`:1258`), `case_III_rank_certification_aug` (`Candidate.lean:2694`), `case_III_arm_realization_aug`
(`ForkedArm.lean:426`), the genuine-row source `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced`
(`Candidate.lean:2286`) + the `−ρ₀` pin fact `reproducedSlot_pmR_acolumn_eq` (`:2314`), the corner gate leaf
`corner_hA'_of_gate` (`Concrete.lean:810`); **the `hB`-machinery (ON-path):** the engine
`dual_comb_reindex_fiberwise` + B-read `submatrix_columnOp_toBlocks₁₂_eq` + exact-combination factoring
`submatrix_columnOp_toBlocks₁₂_eq_mul_toBlocks₂₂` (`Concrete.lean`); the support-extensor agreement
`caseIIICandidate_supportExtensor_of_ne`/`_reproduced` (`Candidate.lean`); the B1/B2 row-op apparatus
(`exists_rowOp_of_strictInjection` + `rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂`, `M`-generic, fire
on the augmented matrix unchanged).
**Correct-but-unused (kept in tree; phase-close cleanup candidates):** the route-(a)/route-α `ρ₀`-free
incomparability leaves (`hingeRowBlock_not_le_of_supportExtensor_not_mem_span`,
`exists_corner_blockBasisOn_linearIndependent_of_not_le`, `panelSupportExtensor_not_mem_span_of_triLI`,
`chainData_arm_corner_blockBasis_linearIndependent_of_triLI`, the LA core `exists_independent_perp_family_escape`);
the OPERATED `ρ₀`-route corner leaves (`chainData_arm_corner_hA_of_discriminator_gate`,
`submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_eq_coordEquiv`, `…_row_linearIndependent_of_gate`,
`corner_hA_zero₁₂_of_gate`; presume `C ≠ 0`); the un-augmented spine arm `case_III_arm_realization_rowOp`
(`ForkedArm.lean:315`; D-CAN-3b calls it, but route (D) re-points to `_aug`).
**Landed-but-dead-arm** (none used; αE6 retire DEFERRED to phase-close): `_matrix`, the dual-space chain arm +
LEAF-B2.

On sub-commit (5) wiring the dispatch, the CHAIN layer closes and ENTRY (**23g**) opens; ASSEMBLY is **23h**.

## Decisions made during this phase

### Phase-local choices and proof techniques

**(route (D) — the LIVE corner-`hA` route; §(4.78), feasibility-spiked session #46.)**
- **Route (D) = the LANDED `_aug` ladder on the D-canonical PIN-ZERO bottom** — NOT a "cert re-shape" (the
  augmented cert `case_III_rank_certification_aug` carrying a genuine `ρ₀` row already EXISTS, the αE1–αE4
  "landed-but-dead" ladder). The combination §(4.67)/§(4.68) never tested: they blocked `_aug` under the
  `mixedBottom` (`C ≠ 0`, the count forced the v-incident `e_b`-fill into the bottom, coupling the operated
  corner to the opaque `blockBasisOn(e_b)` block); the D-canonical bottom is the literal `R(Gab)` (full-rank,
  no `e_b`-fill ⟹ `C = 0`), so the operated corner `A − L₀·C = A` is bare `A.row` LI, the augmented `inr ()`
  `±r` row (`hingeRow b v ρ₀`) reads `−ρ₀` at the v-pin THROUGH the column op (PROBE 5,
  `reproducedSlot_pmR_acolumn_eq` + `columnOp` invisible to the v-column), and `corner_hA'_of_gate` fires from
  the discriminator's NONZERO gate alone (PROBE 4). The §(4.67) "`±r` reads `0`" was for the WRONG orientation
  `hingeRow a b ρ₀` (both `a,b ≠ v` ⟹ `0`); the head-`v`-tail orientation reads `−ρ₀`. Genuinely-new work:
  four augmented-matrix bricks D1–D4 (siblings of landed un-augmented ones + a kernel one-liner) + the
  dispatch, ~5–8 commits. No new geometry, no contract/motive change, no override-gate re-entry
  (the gate `hρe₀` + the `hr` perp `ρ₀(C(a,b)) = 0` are the discriminator's DIRECT-`q` outputs, NOT the §(4.29)
  override gate). Full verdict + sub-commit list: design §(4.78).

**(route α — corner 3-normal-LI source; LA core landed session #45, route BLOCKED session #46 → §(4.77); SUPERSEDED by route (D).)**
- **Route α is BLOCKED: its `_escape` side-condition `q b ∉ ker (of p)` is provably FALSE for a reachable
  family of matched joins.** `exists_independent_perp_family_escape` (`Claim612.lean`) is a correct,
  axiom-clean leaf — `ker (of p)` (finrank ≥ 2, contains `n_u`) meets `span {n_u, w}` in exactly `span {n_u}`
  when `w ∉ ker`, so `SetLike.exists_of_lt` hands over `n' ∈ ker \ span {n_u, w}`; the `w ∉ ker` precondition
  is load-bearing. But for the spine's actual `w = q b = q(vtx(i−1))` that precondition is sometimes a false
  proposition: the kept points satisfy the off-one-panel incidence
  (`∀ idx, p idx ⬝ᵥ n j = 0 ⟺ j.succ ∈ {a,b}`), so a join whose preceding panel `q b = n j'` has
  `j'.succ ∈ {a,b}` makes `p ⊥ q b` (and the two-panel discriminator branch sets `n' := n u_b`, so `q b = n
  u_b ⟹ n' = q b`, `htriLI` outright degenerate). The threading half is sound (`spike_triLI_of_escape`,
  kernel-confirmed: `_escape` + the spine's `hgab` compose into `htriLI`); the geometry is the wall. STOP for
  adjudication among (D) the `ρ₀`-route cert re-shape / (α′) candidate-aware discriminator / (β) KT's
  disjunction-over-all-`Mᵢ`. Full analysis + costs: §(4.77.4). (The initial `m+1 ≤ k` headroom variant of the
  LA core was REJECTED — exactly `m = k` kept points, no headroom — so the side-condition was the only LA
  shape; that part stands, it is the *consumer feasibility* that fails.)

**(D-canonical — the live route; design §(4.71)/(4.72) carry the recon detail.)**
- **The corner `hA` does NOT need `blockBasisOn(±r) = ρ₀` — it needs block INCOMPARABILITY** (§(4.74)/§(4.75),
  kernel-checked). Under the pin-zero `Gab` bottom (both endpoints `≠ v` ⟹ `C = toBlocks₂₁ = 0`) the operated
  corner `A − L₀·C = A`, so `hA` = bare `A.row` LI = corner block-basis family `[blockBasisOn(e_a,·);
  blockBasisOn(e_b,j₀)]` LI, which holds iff some `e_b`-block vector escapes `e_a`'s block — i.e.
  `¬ hingeRowBlock e_b ≤ hingeRowBlock e_a`. The opaque-basis dead-end (`blockBasisOn(±r) = ρ₀`, FALSE since
  `blockBasisOn = finBasisOfFinrankEq`) is on the OPERATED (`C ≠ 0`) path only; it is sidestepped here. Landed
  `ρ₀`-free: `hingeRowBlock_not_le_of_supportExtensor_not_mem_span` (incomparability from support non-parallelism
  `C(e_a) ∉ span {C(e_b)}`, via dual-annihilator order-reversal + `Subspace.dualAnnihilator_dualCoannihilator_eq`)
  + `exists_corner_blockBasisOn_linearIndependent_of_not_le` (corner family LI from incomparability; the escape
  half of `exists_corner_blockBasisOn_linearIndependent` minus the `ρ₀`-construction). Remaining = the
  incomparability SOURCE (a panel-meet non-parallelism leaf, or the direct-`q` perp — see *Hand-off*).
- **The `hB`-machinery (ON-path) + the engine technique.** `dual_comb_reindex_fiberwise` re-keys
  `ψ = ∑ⱼ c j • χ (μ j)` to `ψ = ∑ᵢ' (∑ⱼ∈{μ ·=i'} c j) • χ i'` (`Finset.sum_smul` + per-fiber
  `χ i' = χ (μ j)` + `← Finset.sum_fiberwise`; generic in the module `N`; `matrix_eq_mul_of_dual_row_comb`
  refactored to delegate). It + the corner `B`-read `submatrix_columnOp_toBlocks₁₂_eq` (every corner row's
  off-`v` fill is its `a`-shifted `hingeRow`, `e_a` rows giving `hingeRow a a · = 0`) + the `hB` factoring
  `submatrix_columnOp_toBlocks₁₂_eq_mul_toBlocks₂₂` discharge the spine's `hB` (`B = L₀·D`). The `cols`-lambda
  binder needs a type ascription → FRICTION.
- **The corner `hA` was first built via the `ρ₀`-route, then RE-ROUTED `ρ₀`-free (§(4.74)/(4.75)) — the
  ρ₀-route is DEAD.** The ρ₀-route (the hA bundle `toBlocks₁₁_sub_mul_toBlocks₂₁_row_linearIndependent_of_gate`
  composing the `hAeq` identity `…_eq_coordEquiv` with `corner_hA_zero₁₂_of_gate`, fed the discriminator's
  direct-`q` NONZERO gate — the §(4.73.2) "misdiagnosis for the nonzero gate" finding) DIED at the dispatch
  composition spike (§(4.74)): its carried `hAeq` (`Sum.elim blockBasisOn ρ₀`) is UNSATISFIABLE — it needs
  `blockBasisOn(±r)=ρ₀`, FALSE (opaque `finBasisOfFinrankEq`). Re-routed `ρ₀`-free via block incomparability
  (§(4.75); the live route, see *Current state*). Those ρ₀-route leaves (eeafe64/32808a3/a1e5f9a's hA bundle +
  leaf (iii)) are OFF-path, kept in tree (phase-close cleanup). **Durable lesson** (→ *Findings* rows 559–565
  + DESIGN.md *Constructibility recon*): the `hAeq` carried as a hypothesis through 3 leaves was satisfiability-
  checked only at the producer spike, where it failed — a deferred hypothesis through a multi-step arc must be
  satisfiability-checked at the producer, not just type-checked per leaf.
- **(D-canonical) = re-key `blockBasisOn` on the support extensor, making the literal-IH-bottom (C) cert
  buildable.** D-CAN-1 `canonBlock`/`canonBlockBasis`/`_congr` + the `blockBasisOn`/`blockBasis` drop-in (the
  re-keying); D-CAN-2 `submatrix_columnOp_toBlocks₂₂_eq_Gab` (the literal-`Matrix` bottom equality, the
  PROBE-Q2 `_congr`-fires-inside-`Matrix.of` transport); D-CAN-3a the `hD` over the literal IH bottom (replaces
  `mixedBottom`); D-CAN-3b the arm spine firing the `_zero₁₂` cert. The wall §(4.70) found ((C) relocates it
  under the *opaque* basis) DISSOLVES under the re-keying — the cross-framework basis equality is provable AND
  transports to the literal `Matrix` equality (§(4.71) PROBE 2a/Q2, kernel-checked).
- **The D-CAN-4 feeders are all GATE-FREE** (§(4.72), kernel-checked): `hsupp` (candidate↔IH-`Q` support
  agreement) discharges via the override accessors (`_of_ne` off-slot; `_reproduced` for the §(4.65)-feared
  `e_b`-fill row — a `Function.update_self`), not the gate; `hgp` via per-edge slot classification; the `Gab`
  bottom selection via the literal-IH-bottom route (`bottom_selection_of_crossFramework_span_Gab`, lifting
  selected `F₂ = R(Gab)` rows to `F`-rows by a per-edge `lift`); `hfr₂` via the IH `hsplitGP` finrank count
  (`exists_ofNormals_finrank_span_rigidityRows_eq_of_hsplitGP`, the `ℤ→ℕ` cast via `def=0` + nonempty,
  TACTICS-QUIRKS §47). `q := Q.normal` is the established conflict-free placement.
- **D1 `interior_hsplitGP`** = the `Arms.lean:894` chain-arm precedent at the split-off graph, taking the
  all-`k` `(k':ℤ)`+`Nonempty` `hIH` (`splitOff_isMinimalKDof` + `splitOff_simple_of_noRigid_of_card` +
  `splitOff_vertexSet_ncard_lt`, then IH GP `.1`). Consumes the C.3 `hIH` add. (`splitOff` adds `e₀` so ⊄ `G`;
  simplicity needs `4 ≤ |V|` for a proper triangle — D1 takes `hV4`.)

**Route-(α) αE ladder + bottom-arc — SETTLED/DEAD (verdicts only; full blow-by-blow in git + design
§(4.66)/(4.68)/(4.69)/(4.70)):** αE1–αE4 = the `rigidityMatrixEdgeAug` engine/cert/wrapper ladder
(landed-but-dead); αE5 = the `(e_b,j₀)`-collision-machinery deletion (KEPT B1/B2/BOT-3′/leaf(i)/(iii)/
`_mixedBottom`/free-BOT-2/`_rowOp`/`_zero₁₂` — all REUSED by D-canonical, zero-caller orphans deleted); HD,
BOT-1 = route-(α) landings reused. The αD interior-corner arc (§(4.67)/(4.68)) compiler-confirmed BOTH
candidate arms blocked by the same `caseIIICandidate`-override gate → the §(4.69)–(4.72) recon arc re-routed to
(D-canonical).

### Promoted to FRICTION / TACTICS-QUIRKS / DESIGN
- **The §(4.62) durable lesson — route-composition satisfiability must be COMPILER-CHECKED, not prose-argued**
  (the deferred-hypothesis-satisfiability trap; fired at §(4.62)/(4.65)/(4.66.F)/(4.70), and the recon-before-
  build rule that caught the D-CAN-2 `hsupp` deferral at §(4.72)). → FRICTION; DESIGN.md *Constructibility
  recon*.
- **`set`-folding a carried hypothesis's heavy type breaks the downstream `exact`/whnf match** → TACTICS-QUIRKS
  § 43 (lemma-application variant). **`ℤ→ℕ` cast-subtraction (`push_cast`/`ring` leaves a `.pred`)** → the
  explicit `Nat.cast_mul`/`Nat.cast_sub` route, TACTICS-QUIRKS §47.
- **A projecting argument-lambda (`fun x => (↑x.1, x.2)`) fed to an implicit-domain parameter needs a binder
  type ascription** (the `cols` arg of `matrix_eq_mul_of_dual_row_comb`) → FRICTION *[idiom] Feeding
  `matrix_eq_mul_of_dual_row_comb`'s `cols` …*.
