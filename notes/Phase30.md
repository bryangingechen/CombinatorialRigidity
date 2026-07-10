# Phase 30 — Algebraic-independence relaxation (RELAX) (work log)

**Status:** in progress (opened 2026-07-09).

## Current state

**R1 is done — verdict GO-WITH-RESHAPINGS** (2026-07-10,
compiler-witnessed: a general-`k` spike compiled sorry-free with zero
`AlgebraicIndependent` hypotheses; durable route in *R1 spike route*
below). Both §2 residual risks resolved favorably; §2's two wrong
premises and §3's live-site undercount are corrected in
`notes/AlgebraicIndependence.md`. **Next concrete step: dispatch the R2
recon** (re-routed question below). The refactor is scoped only after
R2 plus the user's call on the motive-conjunct deletion (flag in
*Blockers*).

## Architectural choices made up front

- **Investigation phase, not a build phase.** The first deliverable is
  a **recon verdict**, not Lean. No blueprint chapter opens at phase
  open (the dep-graph is fully green — there are no red/deferred target
  nodes, so the phase-open red-node consistency gate is vacuous). The
  follow-on refactor is a **structural-edit-mode** change (restate
  existing green nodes as the alg-independence content is deleted),
  planned after the recons — not now.
- **The live site is at general grade.** §2's hypothesis was written at
  `d=3` (pre-Phase-23); the footnote-6 seed-rank transfer landed at
  general grade (`case_III_nested_rank_lower_all_k`, on the live A2/A5
  spine). R1 settled §2's risks (a)+(b) against that landed spine;
  R2 is the general-`d` chain/relabel question. (The phase-open claim
  that §3 site 107(a) was the *only* live consumer was an undercount —
  see *composition-point pins* below; all extra consumers are
  product-routable.)

## Investigation checklist

- [x] **R1 — the §2 product-route recon at `d=3`**: **GO-WITH-RESHAPINGS**
  (2026-07-10; compiler-witnessed sorry-free at general `k`). **(a)** no
  circularity — every `q`-condition at the composition is a non-root
  condition of one of four polynomials fixed before `q`; but `q` is *not*
  free as landed (it is the IH seed of `G_v^{ab}` from the `hsplitGP`
  unpack) — the freedom is created by a local reshape of that unpack.
  **(b)** the nested-IH rank polynomial is already landed as the
  deficiency-aware `exists_rankPolynomial_of_IH_linking` (not §2's
  def=0 pair) and feeds the device. Pins + route below.
- [ ] **R2 — the general-`d` question, re-routed by R1**: the
  single-split composition is `k`-uniform (the spike is general-`k`;
  the touched family at one split is exactly `{G_v^{ab}, G_v}`), so the
  stale "does the family grow with `d`" framing is dead. The live
  question: **enumerate the `q`-conditions consumed by
  `case_III_arm_corner_assembly` + the `CaseIII/Relabel/` arm off the
  base w6b bundle** (the general-`d` dispatch fires W6b ONCE at the base
  split; interior candidates consume the base `q` through relabel
  transports chosen *after* the discriminator picks `i`), and check each
  is a pre-foldable `q`-free polynomial factor. Expected shape: fold
  per-candidate factors for all `i ∈ Fin d` (≤ `d` factors; relabel
  images of polynomials are polynomials via `rename`).
- [ ] *(conditional on R2 + user adjudication)* **the refactor** —
  structural-edit sub-phase, est. **8–15 slices / ~10 Lean files** +
  blueprint restates. Changes: drop the motive conjunct; reshape
  `case_III_nested_rank_lower_all_k` + the two `hsplitGP`-unpack sites +
  `exists_shared_redundancy_and_matched_candidate` +
  `exists_chainData_discriminator_pick` (swap `hq` for an LI input);
  switch the ~10 alg-indep-chooser sites to `exists_eval_ne_zero` on
  products. Deletions: the transcendental-seed producers + mirrors, the
  LI-from-alg-indep bridges, the seed-rank-bridge family (`CaseI.lean`),
  relabel alg-indep transports; optionally the (ii-b) rationality-bridge
  machinery (unused under the product route).

## R1 composition-point pins (2026-07-10)

Live `AlgebraicIndependent ℚ q` consumers (all product-routable):

- `case_III_nested_rank_lower_all_k` (`CaseIII/Realization.lean`) — the
  ∀-statement's alg-indep hypothesis, consumed once via
  `MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent`;
  instantiated at the IH seed by `chainData_split_w6b_gates` and
  `case_III_candidate_dispatch`.
- the LI bridges `linearIndependent_normals_of_algebraicIndependent`
  (+ `_triple`, `_general`) — consumed by the `d=3` dispatch's
  discriminator, `Theorem55.lean`'s reduction arm, and the general-grade
  `exists_chainData_discriminator_pick`.
- the motive fifth conjunct (`HasGenericFullRankRealization`,
  `PanelHinge.lean`) — produced by GAP-2
  (`hasGenericFullRankRealization_of_rigidOn_ofNormals`) and ~9 sibling
  `exists_injective_algebraicIndependent_real` chooser sites
  (Coupling/CaseI/CaseII/Theorem55), transported by
  `CaseIII/Relabel/Basic.lean`. The shared rank-polynomial cores discard
  it (`obtain ⟨Q, hQg, hQgp, hQrank, hQrec, _⟩`), so deletion doesn't
  break the producers.

**Where the product-route choice of `q` happens:** the `hsplitGP`-unpack
(step 1 of `chainData_split_w6b_gates` / `case_III_candidate_dispatch`),
replaced by polynomial extraction + one `MvPolynomial.exists_eval_ne_zero`
shot — below the motive's existential, so no IH-interface change beyond
the conjunct deletion.

## R1 spike route (the refactor's route; re-derivable without re-running the recon)

Two theorems, compiled sorry-free at general `k` (scratch deleted; this
is the durable record).

**`exists_tripleLI_polynomial`** — the one genuinely-new brick.
Statement: for `1 ≤ k` and pairwise-distinct `a b c : α`,
`∃ P : MvPolynomial (α × Fin (k+2)) ℝ, P ≠ 0 ∧ ∀ q, eval q P ≠ 0 →
LinearIndependent ℝ ![q(a,·), q(b,·), q(c,·)]`. Construction:
`P := rename f (map (algebraMap ℚ ℝ) (det (mvPolynomialX (Fin 3) (Fin 3) ℚ)))`
with `f (i,j) = (![a,b,c] i, Fin.castLE h3 j)` (injective from the
distinctness + `Fin.castLE_injective`). Nonzero:
`Matrix.det_mvPolynomialX_ne_zero` + `MvPolynomial.map_injective` (at
`(algebraMap ℚ ℝ).injective`) + `MvPolynomial.rename_injective`.
Consumer direction: `eval q P = aeval (q ∘ f) (det …)` via
`MvPolynomial.eval_rename` + `MvPolynomial.eval_map` +
`MvPolynomial.aeval_def`, then the landed tail of
`linearIndependent_normals_of_algebraicIndependent_triple` verbatim
(`Matrix.mvPolynomialX_mapMatrix_aeval` + `AlgHom.map_det` →
`Matrix.linearIndependent_rows_of_det_ne_zero` →
`LinearIndependent.of_comp` at the `Fin.castLE h3` projections).

**`product_route_spike`** — the composition. Hypotheses: `hQab/hQv :
HasGenericFullRankRealization k n G_v^{ab}/G_v` (both already held by
the landed callers from `hIH`), a `q`-free link-recording `ends` for
`G_v^{ab}` (hence for `G_v`), `hdef_Gab`, `hk'le : def(G_v,n) ≤ D−2`
(landed: `splitOff_removeVertex_minimalKDof`), `2 ≤ |V(G_v^{ab})|`,
looplessness, `a,b,c` distinct. Four product factors, all fixed before
`q`:

1. `P_ab` := `exists_rankPolynomial_of_IH_linking G_v^{ab} ends hQab`
   (the deficiency-aware Phase-22k L7a producer);
2. `P_v` := the same at `G_v` — this IS the eq.-(6.22) input
   (`case_III_nested_rank_lower_all_k` already calls it internally);
3. `Qgp` := `exists_generalPosition_polynomial G_v^{ab} ends` (nonzero
   via its moment-curve witness at an injective
   `Countable.exists_injective_nat` param);
4. `Ptri` := the brick above.

One `MvPolynomial.exists_eval_ne_zero` shot on the product
(`mul_ne_zero`; factor nonvanishing recovered through `map_mul`). The
four `q`-dependent gates delivered at the chosen `q` — exactly the
dispatch's two `hQalg` uses plus GP:

- GP of `ofNormals G_v^{ab} ends q` (from `Qgp`);
- **eq. (6.18)**: `IsInfinitesimallyRigidOn V(G_v^{ab})` — `P_ab`'s
  `N ≤ finrank` + `finrank_span_rigidityRows_add_deficiency_le` (B2) at
  `def = 0` → equality →
  `isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`;
- **eq. (6.22)**: `D(|V(G_v^{ab})|−1) − (D−2) ≤ finrank (span R(G_v, q))`
  — `P_v`'s transfer + the landed arithmetic (`two_le_screwDim`,
  `screwDim_sub_two_le_mul`, the `vertexSet_splitOff` /
  `vertexSet_removeVertex` card equality, `hk'le`);
- triple LI of `![q(a,·), q(b,·), q(c,·)]` (from `Ptri`).

Rationality clauses (`coeffs ⊆ range (algebraMap ℚ ℝ)`) are **unused** —
they served only the alg-indep transfer. Downstream of the four gates,
the dispatch machinery (W6b, discriminator, arm closers, GAP-2) imposes
no further conditions on `q` (verified end-to-end on
`case_III_candidate_dispatch`).

**Genuine build residuals** (wiring, not open math): (i) the
`(k+1)`-row sibling of the brick — same rename/det construction at
`Fin (k+1)`, adapting
`linearIndependent_normals_of_algebraicIndependent_general`; needed for
`exists_chainData_discriminator_pick` (at `k = 2` it coincides with the
triple brick). (ii) the `ends`-selector wiring — replace the IH's
`Q.ends` with the `q`-free canonical `Gab.endsOf` + the landed
`ofNormals_recordsLinks_of_hends` / `recordsLinks_agree_swap` transport.

## Blockers / open questions

- **Motive-level flag, awaiting user adjudication post-R2:** the
  refactor deletes the fifth (`AlgebraicIndependent ℚ`) conjunct of
  `HasGenericFullRankRealization` — an IH/motive-level edit, though a
  pure weakening (every producer/consumer in the pins above is
  product-routable). Est. 8–15 slices / ~10 Lean files + blueprint
  restates. Not a blocker for R2 itself.

## Hand-off / next phase

**Next concrete step: dispatch the R2 recon** (re-routed by R1):
enumerate the `q`-conditions consumed by `case_III_arm_corner_assembly`
and the `CaseIII/Relabel/` arm off the base w6b bundle, and check each
is a pre-foldable `q`-free polynomial factor (per-candidate factors for
all `i ∈ Fin d` are the expected shape; relabel images of polynomials
are polynomials via `rename`). Read-only; verdict in the return message.
The refactor is scoped only after that verdict plus the user's call on
the motive-conjunct deletion.

## Decisions made during this phase

- **R1 verdict (2026-07-10): GO-WITH-RESHAPINGS** at `d=3` (and the
  single-split composition at general `k`), compiler-witnessed
  sorry-free. §2's two wrong premises corrected in
  `notes/AlgebraicIndependence.md` (producer pair; `q` not free as
  landed); §3's "only live site" undercount corrected (LI bridges +
  motive conjunct are also live, all product-routable). Route + pins:
  this file, *R1 spike route* / *R1 composition-point pins*.
