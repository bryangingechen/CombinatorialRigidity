# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress, **BLOCKED on a user decision** (the corner-`hA` source route — §(4.77)). The fifth
CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d + 23e + 23f). 23e landed the KT-faithful A3-transposed rank
certificate + its LA scaffolding axiom-clean (`notes/Phase23e.md`); 23f builds the **geometry arm** that
*constructs* the cert's block data, then the chain dispatch + CHAIN-5. The interior-corner cert is BUILT
(D-CAN-1..3b + the `hsupp`/`hgp`/`Gab`-bottom/`hfr₂` feeders); the corner `hA`'s last genuinely-new source
(route α) is BLOCKED — its side-condition is provably false for reachable joins (§(4.77)), so the next action
is a user pick among three faithful re-routes (D / α′ / β; §(4.77.4)). **Phase 23 stays in progress.**
Authoritative recon: `notes/Phase23-design.md` §(4.77) (the route-α STOP + the three options), on top of
§(4.71) ((D-canonical) feasibility + D-CAN-1..4) / §(4.72) (the `hsupp` gate-free discharge); route history
§(4.54)→(4.66)→(4.68)→(4.70)→(4.74)→(4.75)→(4.76)→(4.77). Program map: `notes/MolecularConjecture.md`.

## Current state

**ROUTE α IS BLOCKED — the design recon (§(4.77)) found its load-bearing side-condition `∃ i, p i ⬝ᵥ q b ≠ 0`
is provably FALSE for a concrete reachable family of matched joins, so "thread `_escape` and build" CANNOT be
completed. STOP for user adjudication among three faithful re-routes.** The LA core
`exists_independent_perp_family_escape` (`Claim612.lean`) is a correct, axiom-clean leaf — but its `hw`
precondition (`q b ∉ ker (of p)`) is sometimes an unsatisfiable proposition for the spine's actual `q b =
q(vtx(i−1))`. The sharpest failure: in the two-panel branch of `exists_line_data_of_homogeneousIncidence_gen`
the discriminator sets `n' := n u_b` directly, and if `q b` IS that second panel `n u_b` then `n' = q b`, so
`htriLI : ![q a, n', q b]` is *outright false* (degenerate). The threading half is FINE (kernel-confirmed: `_escape`
+ the spine's carried `hgab` compose into `htriLI`); the gap is the geometric input it demands. See *Blockers*
+ *Hand-off* for the three options. `d=3` stays fully green.

**D-CAN-4 IN PROGRESS — all FEEDER leaves + the `hA` leaf + its `hAeq` operated-corner identity LANDED.**
Escape **(D-canonical)** (user-picked, design §(4.71)) is the live route: re-key `blockBasisOn` on the
support extensor so the literal-IH-bottom (C) cert builds and the §(4.29) `caseIIICandidate`-override gate
wall dissolves *at its root* (the opaque per-framework `finBasisOfFinrankEq`). The interior-corner cert is
BUILT (D-CAN-1..3b); D-CAN-4 wires the dispatch that constructs the arm's carried obligations from the
landed feeders. The §(4.73.2) seam was a MISDIAGNOSIS (kernel-checked, session #45):
`corner_hA_zero₁₂_of_gate` consumes the discriminator's DIRECT-`q` **NONZERO** gate `ρ₀(F.supportExtensor
e_a) ≠ 0`, NOT the `q∘shiftPerm` **perp** `= 0`; the `hA` leaf
`chainData_arm_corner_hA_of_discriminator_gate` (`Realization.lean`) threads it with NO `shiftPerm`.
**The §(4.73.4) item (2) `hAeq` leaf is now LANDED** as the genuinely-new KT-6.66 operated-corner identity
`submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_eq_coordEquiv` (`Concrete.lean`, A6): the OPERATED corner
block `toBlocks₁₁ − L₀·toBlocks₂₁` of the column-operated edge matrix IS the `coordEquiv` coordinate matrix
of its operated corner-functional family `φ` (corner panel minus the `L₀`-weighted bottom contributions),
provided the dispatch supplies `hφ` (`φ i = blockBasisOn(corner i) − ∑ L₀ • χ`, the KT-6.66 form coupling
the `±r` slot to `ρ₀`). Composes the `_apply_corner`/`_apply_pin_zero` entry bricks; abstract over `L₀`/`φ`
so the dispatch's `Sum.elim blockBasisOn ρ₀ ∘ em₁` slots in. **The `hB`-machinery is LANDED** (`Concrete.lean`,
A6, ON-path): the engine `dual_comb_reindex_fiberwise`, the corner `B`-read `submatrix_columnOp_toBlocks₁₂_eq`,
the `hB`/`L₀` factoring `submatrix_columnOp_toBlocks₁₂_eq_mul_toBlocks₂₂` (`toBlocks₁₂ = L₀·toBlocks₂₂`) — these
discharge the spine's `hB` slot (`hB` is also dischargeable via span-membership `matrix_eq_mul_of_span_mem`;
exact route TBC at the dispatch build). The corner `hA`-via-`ρ₀` bundle from the same A6 batch
(`…toBlocks₁₁_sub_mul_toBlocks₂₁_row_linearIndependent_of_gate` + the `hAeq` identity) is the **dead `ρ₀`-route,
OFF-path** (see the re-route below).
**CORNER `hA` RE-ROUTED off `ρ₀` (§(4.74)/§(4.75), kernel-checked).** The OPERATED `hAeq` path needs
`blockBasisOn(±r slot) = ρ₀` (FALSE — opaque `finBasisOfFinrankEq`); but it is the WRONG path under the
pin-zero `Gab` bottom (`C = toBlocks₂₁ = 0`), where `A − L₀·C = A` and `hA` is **bare `A.row` LI** needing
only block INCOMPARABILITY, NOT the `ρ₀`-identity. Landed this session (`Concrete.lean`, `ρ₀`-free,
axiom-clean): `hingeRowBlock_not_le_of_supportExtensor_not_mem_span` + `exists_corner_blockBasisOn_linearIndependent_of_not_le`.
**The incomparability SOURCE leaf + corner-LI chain (route (a)) LANDED** (this session, axiom-clean): the
panel-meet non-parallelism leaf `panelSupportExtensor_not_mem_span_of_triLI` (`PanelLayer.lean`) + the
spine-binding `chainData_arm_corner_blockBasis_linearIndependent_of_triLI` (`Realization.lean`). These reduce
the corner `hA` to EXACTLY ONE carried genuinely-new input: the direct-`q` 3-normal LI `![q a, n', q b]` — the
LAST genuinely-new corner input, now FLAGGED for adjudication (`n'` is the discriminator transversal, NOT a
`q`-vertex, so the alg-indep triple does NOT apply; the discriminator's contract does not certify `n' ∉ span
{q a, q b}`). Route (b)'s direct-`q` perp is the §(4.73.2) seam (REAL, kernel-confirmed — the landed perp crux
gives the chain-edge panel `(i+1, i)`, NOT the spine's direct-`q` short-circuit panel `(i+1, i-1)`). See
*Blockers* + *Hand-off*. The OPERATED `hAeq` leaves (eeafe64/32808a3/a1e5f9a) are NOT on this path (`C ≠ 0`);
kept in tree. `d=3` stays fully green (hard constraint).

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
    - [✗] **the 3-normal-LI producer — ROUTE α BLOCKED (§(4.77)).** Plan was: feed
      `exists_independent_perp_family_escape`'s `w := q(vtx(i−1))` slot through the discriminator + supply the
      side-condition `∃ idx, p idx ⬝ᵥ q b ≠ 0` + thread to `htriLI`. The recon found that side-condition is
      provably FALSE for reachable matched joins (the preceding panel `q b` can hold the witness join line ⟹
      `p ⊥ q b`; the two-panel branch even gives `n' = q b`). The threading composes (`spike_triLI_of_escape`)
      but its geometric input is unsatisfiable. STOP for user decision — (D) `ρ₀`-route cert re-shape / (α′) /
      (β); see *Blockers* + *Hand-off* + §(4.77.4). The `hA` matrix wiring (`linearIndependent_toBlocks₁₁_row_of_corner_gate`
      + the `C = 0` collapse `rigidityMatrixEdge_mul_columnOp_submatrix_toBlocks₂₁_eq_zero` feeding the corner
      family + `re`/`em₁`) is unchanged across all three options — only the corner-LI *source* swaps.
    - [ ] **the rest: wire `chainData_dispatch`** (the `Fin cd.d` router) — `hcomb`/`hB` via span-membership
      (`matrix_eq_mul_of_span_mem`, no `cGv` widening needed) → `re`/`hre` → dispatch shell + CHAIN-5 + the
      C.3 `hIH` add. ~2-3 commits. (The OPERATED `hAeq` leaves eeafe64/32808a3/a1e5f9a are NOT on the pin-zero
      path — they presume `C ≠ 0`; kept in tree for any future `C ≠ 0` consumer.)

  A1–A5c (matrix model + column op + block-additivity backbones `Rank.lean:480/574/622`) + D1
  `interior_hsplitGP` ✓ LANDED and REUSED. The `_aug`/`_matrix`/`_rowOp`/chain dead arms stay landed-but-dead
  (αE6 retire DEFERRED to phase-close).

## Blockers / open questions

- **THE 3-NORMAL-LI SOURCE `![q a, n', q b]` — ROUTE α BLOCKED; STOP FOR USER ADJUDICATION (§(4.77)).** The
  recon found route α's load-bearing side-condition `∃ i, p i ⬝ᵥ q b ≠ 0` (the `hw` precondition of
  `exists_independent_perp_family_escape`) is **provably FALSE** for a concrete reachable family of matched
  joins, so the planned "swap `_escape` in + supply the side-condition + thread to `htriLI`" route CANNOT be
  completed. The kept points `p idx = pbar(emb idx)` satisfy the off-one-panel incidence
  (`pbar_dotProduct_eq_zero_of_ne_succ`): `∀ idx, p idx ⬝ᵥ n j = 0 ⟺ j.succ ∈ {a,b}` (the witness join). So
  whenever `q b = n j'` is a candidate panel with `j'.succ ∈ {a,b}` (the join line lies in `Π(q b)` too) ALL
  kept points are perp to `q b` and `_escape` dies — and in the two-panel discriminator branch `n' := n u_b`
  *directly*, so if `q b = n u_b` then `n' = q b` and `htriLI` is outright degenerate. The matched candidate
  `i` and the witness join `{a,b}` are not jointly controlled (the discriminator picks off a `ρ(·) ≠ 0`
  witness join with no link to `q b`'s panel), so the failing configs are reachable. KT general position does
  NOT supply the side-condition (the failure is combinatorial, not measure-zero). **The threading half is
  sound** (kernel-confirmed: `_escape`'s output + the spine's carried `hgab` compose into `htriLI` —
  `spike_triLI_of_escape`); the obstruction is the geometry, not the wiring. THREE faithful re-routes,
  none picked unilaterally — see *Hand-off* + §(4.77.4): **(D / `ρ₀`-route)** the cert re-shape carrying a
  genuine `ρ₀` corner row so `corner_hA'_of_gate` fires off the discriminator gate the spine already produces
  (most KT-faithful — KT's `Mᵢ = [r(Lᵢ); ±r=ρ₀]`, eq. (6.64)); **(α′)** re-architect the discriminator to be
  candidate-aware (blocked by the two-panel `n' = n u_b` forcing — likely impossible without a line-data
  rebuild); **(β)** replace the per-candidate discriminator with KT's actual disjunction-over-all-`Mᵢ`
  dimension count (eq. (6.65)–(6.67), removes `n'`/the side-condition entirely but re-opens the dispatch
  architecture). **The `=ρ₀` operated path + route-(b) perp stay dead for their original reasons** (§(4.74)
  opaque-basis / §(4.73.2) relabel mismatch); option (D) revives the `ρ₀` *idea* via a genuine extra row, not
  the operated-`hAeq` identity.
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

**STOP — ROUTE α IS BLOCKED; the next action is a USER DECISION, not a build.** The recon (§(4.77),
kernel-checked) found route α's load-bearing geometric input — the `_escape` side-condition
`∃ i, p i ⬝ᵥ q b ≠ 0` — is a sometimes-FALSE proposition for the spine's actual `q b = q(vtx(i−1))`, so the
planned "swap `_escape` in + supply the side-condition + thread to `htriLI`" CANNOT be completed. The
threading machinery is correct and the corner-LI chain
(`chainData_arm_corner_blockBasis_linearIndependent_of_triLI` + `panelSupportExtensor_not_mem_span_of_triLI`)
+ the LA core (`exists_independent_perp_family_escape`) stay landed/correct — they consume `htriLI` /
`hw` as *hypotheses*; the obstruction is that those hypotheses are not always derivable. Pick a re-route:

- **Option (D) — the `ρ₀`-route cert re-shape (most KT-faithful; RECOMMENDED for adjudication).** KT's corner
  is `Mᵢ = [r(Lᵢ); ±r=ρ₀]` (eq. (6.64)), full-rank from `ρ₀(C(e_a)) ≠ 0` — exactly the LANDED
  `corner_hA'_of_gate` (`Concrete.lean:810`), needing NO `n'`-escape and NO side-condition. The discriminator
  gate the spine already produces (`exists_shared_redundancy_and_matched_candidate` returns
  `ρ₀(panelSupportExtensor (q(candidateVtx i)) n') ≠ 0`, `Realization.lean:1879`) feeds it directly. The
  blocker that drove the project OFF `ρ₀` was a cert-SHAPE artifact (§(4.74): the *operated* `hAeq` wanted
  `blockBasisOn(±r) = ρ₀`, false for the opaque basis), NOT geometry — the fix is to carry a *genuine* `ρ₀`
  corner row (an extra `m₁`-row that is literally `ρ₀`) instead of the opaque `blockBasisOn(e_b, j₀)` the
  pin-zero read forced. Cost ≈ 3–6 commits (the corner-row augmentation + re-wiring `corner_hA_zero₁₂_of_gate`
  to the genuine row), no new geometry.
- **Option (α′) — re-architect the discriminator to be candidate-aware** (so `n'` escapes `Π(q b)`). Blocked
  by circularity (the pick precedes the candidate match) and the two-panel branch forcing `n' := n u_b`; likely
  needs a line-data-builder rebuild. NOT recommended without deeper recon.
- **Option (β) — replace the per-candidate discriminator with KT's disjunction-over-all-`Mᵢ`** dimension count
  (eq. (6.65)–(6.67): `dim span ⋃ C(Lᵢ) = D` by Lemma 2.1, so the nonzero `r` cannot annihilate it ⟹ ≥1 `Mᵢ`
  full rank). Removes `n'` / the side-condition entirely, maximally KT-faithful, but re-opens the CHAIN-2c
  dispatch architecture (the cert certifies an existential candidate, not a fixed matched `i`). Large; the
  fallback if (D) entangles with the opaque basis.

The §(4.77.4) entry carries the full obstruction analysis + cost framing for each. Whichever the user picks,
the rest of the dispatch (the obligation→feeder wiring below) is unchanged from the §(4.72.3) plan — only the
corner-`hA` slot's source swaps.

**The obligation→feeder wiring (unchanged; the build plan once the corner route is chosen; §(4.72.3) + §(4.43)):**
the `Fin cd.d` router: base/`d=3` → the landed `chainData_split_realization`; interior `2 ≤ i` → D-CAN-3b's
`chainData_arm_realization_zero₁₂`. Per-obligation:
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
- **the corner `hA`** — the slot under adjudication (option D/α′/β above). Either route reindexes by `re`/`em₁`
  via `linearIndependent_toBlocks₁₁_row_of_corner_gate` + the `C = 0` collapse
  `rigidityMatrixEdge_mul_columnOp_submatrix_toBlocks₂₁_eq_zero`. **`hB`/`hM'eq`/`L₀`** via the `hB`-machinery
  below (span-membership and/or the exact-combination factoring); `hne_Gv` from the candidate GP; the
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
`rank_columnOp_toBlocks₂₂_eq_finrank_span_Gab` (D-CAN-3a), `chainData_arm_realization_zero₁₂` (D-CAN-3b),
the `hsupp`/`hgp`/`Gab`-bottom/`hfr₂` feeders (D-CAN-4); **the `ρ₀`-FREE CORNER route (ON-path, §(4.75)):**
the corner-LI core `hingeRowBlock_not_le_of_supportExtensor_not_mem_span` + `exists_corner_blockBasisOn_linearIndependent_of_not_le`,
the source leaves `panelSupportExtensor_not_mem_span_of_triLI` (`PanelLayer.lean`) + `chainData_arm_corner_blockBasis_linearIndependent_of_triLI`,
the route-α LA core `exists_independent_perp_family_escape` (`Claim612.lean`); **the `hB`-machinery (ON-path):**
the engine `dual_comb_reindex_fiberwise` + B-read `submatrix_columnOp_toBlocks₁₂_eq` + exact-combination
factoring `submatrix_columnOp_toBlocks₁₂_eq_mul_toBlocks₂₂` (`Concrete.lean`); the support-extensor
agreement `caseIIICandidate_supportExtensor_of_ne`/`_reproduced` (`Candidate.lean`); the row-op matrix-data
arm `case_III_arm_realization_rowOp` (`ForkedArm.lean:315`, LIVE — D-CAN-3b calls it; builds
`Lrow`/`U`/`hblock`/`hrank` in-body via B1/B2 + the `_zero₁₂` cert + the SHARED tail) + its
leaf (i)/B1/B2 row-op apparatus.
**OFF-path — the dead `ρ₀`-route corner leaves** (kept in tree, §(4.74); phase-close cleanup candidates): the
`hA`-via-`ρ₀` leaf `chainData_arm_corner_hA_of_discriminator_gate` + the `hAeq` identity
`submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_eq_coordEquiv` + the operated `hA` bundle
`toBlocks₁₁_sub_mul_toBlocks₂₁_row_linearIndependent_of_gate` + leaf (iii) `corner_hA_zero₁₂_of_gate`.
**Landed-but-dead-arm** (none used by D-CAN; αE6 retire DEFERRED to phase-close): the `_aug` ladder (αE1–αE4),
`_matrix`, the dual-space chain arm + LEAF-B2.

On D-CAN-4 wiring the dispatch, the CHAIN layer closes and ENTRY (**23g**) opens; ASSEMBLY is **23h**.

## Decisions made during this phase

### Phase-local choices and proof techniques

**(route α — corner 3-normal-LI source; LA core landed session #45, route BLOCKED session #46 → §(4.77).)**
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
