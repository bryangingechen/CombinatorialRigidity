# Phase 30 — Algebraic-independence relaxation (RELAX) (work log)

**Status:** in progress (opened 2026-07-09; refactor **user-sanctioned
2026-07-10** — structural-edit build stage, slices (a)–(d) landed).

## Current state

**Next step: slice (e)** — the last sweep (sanctioned, not optional): drop
the now-unconsumed `coeffs ⊆ range (algebraMap ℚ ℝ)` rationality clauses
across the `exists_rankPolynomial_*` family (incl. slice (a)'s
`exists_nested_rankPolynomial_lower_all_k`). Zero risk; closes the phase
once landed (no further slice queued). See *Hand-off*.

**Slice (d) landed 2026-07-10** (closes the deletion arc): the
callerless algebraic-independence family + the three `AlgebraicIndependent`
mirror files are deleted. Precise inventory (matches the *Refactor slice
tracker* item (d)): `linearIndependent_normals_of_algebraicIndependent{,_triple,_general}`,
`exists_chainData_discriminator_pick` (alg-indep form; the LI-form sibling
`exists_chainData_discriminator_pick_of_LI` survives and is now the sole live
pick), the nested-rank pair `case_III_nested_rank_lower{,_all_k}` (the
polynomial form `exists_nested_rankPolynomial_lower_all_k` is now the sole
surviving form), D-CAN-4 `exists_ofNormals_finrank_span_rigidityRows_eq_of_hsplitGP`
(all five in `CaseIII/Realization.lean`); the seed-rank-bridge family
(`isInfinitesimallyRigidOn_ofNormals_of_algebraicIndependent`,
`finrank_infinitesimalMotions_le_of_rankPolynomial_algebraicIndependent`,
`rankHypothesis_ofNormals_of_rankPolynomial_algebraicIndependent`,
`CaseI.lean`, replaced by a retirement-history comment); `exists_injective_algebraicIndependent_real`
+ the three mirror files (`Mathlib/RingTheory/AlgebraicIndependent/{Defs,TranscendenceBasis}.lean`,
`Mathlib/RingTheory/MvPolynomial/Tower.lean`, deleted wholesale — each was
fully dead once its sole consumer went) + their imports (top-level
`CombinatorialRigidity.lean`, `PanelHinge.lean`, `Coupling.lean`) + the
transfer lemma `eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent`.
Deletion-variant grep discipline applied: every dangling docstring/comment
reference outside the deleted decls repointed to the surviving successor
(`Rank.lean`, `Meet.lean`, `PanelLayer.lean`, `RigidityMatrix/Basic.lean`,
`Theorem55.lean`, `Claim612.lean`, `Operations.lean`, `Pinning.lean`,
`Candidate.lean`); the two intentional retirement-history survivors are the
`HasGenericFullRankRealization` docstring's slice-(c) paragraph (unchanged)
and the new `CaseI.lean` retirement note. Blueprint: `lem:case-III-nested-rank-lower`
restated to the polynomial form (pinned solely to
`exists_nested_rankPolynomial_lower_all_k`); the seed-rank-bridge /
seed-rank-upper / rank-attainment nodes + their contextualizing preamble
collapsed to a plain-prose remark (the whole-dead-route rule,
`blueprint/CLAUDE.md` supersession gate); the two downstream `\uses` edges
onto the collapsed labels (`lem:case-III-claim-6-11-redundant-row`,
`lem:case-III-claim-6-11`) dropped (`h618`/`h622` are ambient hypotheses of
those Lean declarations, supplied by the caller, not derived from a named
lemma). Build + lint clean.

**Slices (a)–(c) landed 2026-07-10** (route summaries compressed below;
full detail in git history and the reshaped decls' docstrings): (a) four
pure det/rank-polynomial leaves added beside their alg-indep siblings,
purely additive; (b) the three IH-seed-reuse compositions
(`case_III_candidate_dispatch`, `chainData_split_w6b_gates`,
`case_I_realization_h65_gen`) reshaped to a device-chosen seed via one
`MvPolynomial.exists_eval_ne_zero` shot on a product of four base
polynomials fixed before the seed; (c) the `AlgebraicIndependent ℚ` fifth
conjunct deleted from `HasGenericFullRankRealization`, with every forced
repair (destructures, chooser sites, producer hypothesis drops) in the same
commit.

**Both recons were GO** (2026-07-10, each compiler-witnessed by a
sorry-free general-`k` spike). The product route replaces every
algebraic-independence use on the spine with non-root conditions of **the
same four base polynomial factors at every `d`** — zero per-candidate
factors. Recon detail (route derivations, the `q`-condition table, the
composition-point pins): `notes/AlgebraicIndependence.md` (frozen recon
record) and git history for the (a)–(d) commits.

## User adjudication (2026-07-10, verbatim)

> The user sanctioned the RELAX refactor — delete the
> `AlgebraicIndependent ℚ` fifth conjunct from
> `HasGenericFullRankRealization` and product-route the spine, per the
> (a)–(e) slice order in notes/Phase30.md, INCLUDING the optional final
> sweep (e) (drop the now-unconsumed rationality clauses across the
> `exists_rankPolynomial_*` family). The refactor runs as Phase 30's
> structural-edit build stage, tracked in notes/Phase30.md.

## Investigation checklist

- [x] **R1 — the §2 product-route recon at `d=3`**: GO-WITH-RESHAPINGS.
- [x] **R2 — the general-`d` question**: GO (zero per-candidate factors).
- [x] **user adjudication** — SANCTIONED 2026-07-10, incl. slice (e).

### Refactor slice tracker (the structural-edit Layer plan)

- [x] **(a)** the two det-factor bricks (`exists_tripleLI_polynomial`,
  `exists_tupleLI_polynomial`) + the LI-form pick
  (`exists_chainData_discriminator_pick_of_LI`) + the polynomial-form
  nested-rank bound (`exists_nested_rankPolynomial_lower_all_k`), all in
  `CaseIII/Realization.lean` beside their (then still live) alg-indep
  siblings. **DONE 2026-07-10.**
- [x] **(b)** the three IH-seed-reuse compositions reshaped to
  device-chosen seeds. **DONE 2026-07-10** (three commits: `d=3`
  `case_III_candidate_dispatch`; the general-`d` `chainData_split_w6b_gates`
  chain; `case_I_realization_h65_gen`).
- [x] **(c)** the motive conjunct deleted + the ~10 chooser sites switched
  to `exists_eval_ne_zero` + producer hypothesis drops. **DONE 2026-07-10**
  (one commit).
- [x] **(d)** the now-callerless alg-indep family + the three mirrors
  deleted, blueprint restated. **DONE 2026-07-10** (one commit; inventory:
  *Current state*).
- [ ] **(e)** last sweep (**sanctioned**, not optional): the
  then-unconsumed `coeffs ⊆ range (algebraMap ℚ ℝ)` rationality clauses
  across the `exists_rankPolynomial_*` family (incl.
  `exists_nested_rankPolynomial_lower_all_k`) — zero risk.

## Blockers / open questions

- None.

## Hand-off / next phase

**Next concrete commit: slice (e)** — drop the `coeffs ⊆ range (algebraMap
ℚ ℝ)` rationality clause across the `exists_rankPolynomial_*` family: the
underlying producers (`exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range`
in `Rank.lean`, `exists_rankPolynomial_of_rigidOn`/`exists_rankPolynomial_of_IH_linking`
and siblings in `GenericityDevice.lean`, the rationality leaves in `Meet.lean`/
`PanelLayer.lean`) plus `exists_nested_rankPolynomial_lower_all_k`'s own
`hPrat` output component and its caller `chainData_split_w6b_gates`'s
`h622lb` field. Grep `slice-(e) sweep` across the tree (`Rank.lean`,
`Meet.lean`, `PanelLayer.lean`, `CaseIII/Realization.lean`) to find the
docstring notes this phase's slice-(d) commit left marking each site. Each
site: drop the `⊆ range (algebraMap ℚ ℝ)` conjunct/hypothesis, repair
callers, re-word the docstring's "rationality clause retained…"/"dropped in
the RELAX slice (e) sweep" sentence. This closes Phase 30 — run the
phase-close checklist (`PHASE-BOUNDARIES.md`) once it lands.

## Decisions made during this phase

- **Slice (d) landed (2026-07-10):** see *Current state* for the full
  inventory + blueprint restate. Notable: the two Lean nodes downstream of
  the collapsed seed-rank-bridge/rank-attainment lemmas
  (`exists_redundant_panelRow_{of_edge_of_finrank_lt,ab_of_finrank_eq}`)
  take `h618`/`h622` as caller-supplied hypotheses, not derived
  internally — so their blueprint `\uses` edges onto the collapsed labels
  were dropped rather than repointed (the honesty gate's "ambient input"
  case, not a dangling dependency).
- **Slices (a)–(c) landed (2026-07-10):** additive leaves → device-seed
  reshapes → conjunct deletion, each build+lint clean. Route detail:
  *Current state*; full detail in git history + the reshaped decls'
  docstrings.
- **R1/R2 verdicts (2026-07-10): both GO**, compiler-witnessed sorry-free
  at general `k`. Recon detail: `notes/AlgebraicIndependence.md`.
