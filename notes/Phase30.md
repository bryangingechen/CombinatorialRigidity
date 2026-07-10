# Phase 30 — Algebraic-independence relaxation (RELAX) (work log)

**Status:** in progress (opened 2026-07-09; refactor **user-sanctioned
2026-07-10** — structural-edit build stage, slices (a)–(e) landed; the
(a)–(e) slice plan is **complete**).

## Current state

**Next step: the phase-close checklist** (`PHASE-BOUNDARIES.md` *When this
commit closes a phase*) — ROADMAP row flip + re-thin the §30 planning
section, sync user-facing status surfaces (README/home_page/intro.tex/
`formalization.yaml` incl. `#print axioms`), end-to-end blueprint chapter
re-read + `notes/BlueprintExposition.md` write-up, project-organization
review. No further Lean lemma is queued. See *Hand-off*.

**Slice (e) landed 2026-07-10** (closes the (a)–(e) plan): swept the
`exists_rankPolynomial_*` family's now-unconsumed rationality clause to
zero, end to end.
- **Producers edited** (conjunct dropped from the `∃` type; `hQrat`/`hPrat`
  forwarding removed from every caller): the four GenericityDevice.lean
  rank-polynomial producers
  (`exists_rankPolynomial_of_{rigidOn,rigidOn_linking,le_finrank_linking,
  rigidOn_linking_set}`); the four CaseI.lean pass-through siblings
  (`exists_rankPolynomial_of_{IH_relabel_linking,IH_linking,
  rigidOn_linking_set_proj,IH_relabel_linking_set_proj}` — the last one's
  `hMrat`/`hcD` rationality-derivation block, ~40 lines, dropped outright
  since it fed nothing else once `hc` was gone);
  `exists_nested_rankPolynomial_lower_all_k` and its two `h622lb`-shaped
  callers (`chainData_split_w6b_gates`,
  `exists_shared_redundancy_and_matched_candidate`) plus
  `case_III_candidate_dispatch`'s `h622lb` param, all in
  `CaseIII/Realization.lean`.
- **Deleted as newly-callerless** (deletion-variant discipline): the
  Rank.lean rationality-refinement
  `exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range`
  (once `hc` was unused it was an exact duplicate of
  `exists_polynomial_ne_zero_of_linearIndependent_at`); the whole
  PanelLayer.lean rationality-leaf chain
  (`{normalsJoin,panelSupport,annihRow}Poly_mem_range_map`,
  `annihRowPoly_smul_sign_mem_range_map`, plus its section header);
  Meet.lean's `complementIso_exteriorPower_repr_mem_range_{intCast,
  algebraMap}` and `wedgePairing_ιMulti_family_mem_range_intCast`;
  CaseI.lean's private `dualMap_matrix_entry_eq`.
- **Kept as independent-value survivors** (the task's explicit
  keep-or-delete allowance): `Matrix.det_mem_range_of_entries`
  (Rank.lean — a general ring-hom/det/range fact, FRICTION-flagged
  `[mirrored]`) and `ExteriorAlgebra.ιMulti_family_congr`
  (`Mathlib/LinearAlgebra/ExteriorPower/Basis.lean` — the general
  cardinality-cast helper, also `[mirrored]`); both now have zero live
  callers in-tree, docstrings/FRICTION entries reworded to say so rather
  than claim a consumer.
- **Out of scope** (named pattern is `exists_rankPolynomial_*`; these
  aren't): `PanelHinge.lean`'s `exists_generalPosition_polynomial` and
  `Molecule/GeneralPosition4.lean`'s `exists_generalPosition4_polynomial`
  still carry a live rationality conjunct — untouched (no slice-(e) marker
  was ever left on them; distinct math family, general-position avoidance
  rather than rank witnessing). Their conjunct is also unconsumed at every
  call site (all discard it via `_`), so a future pass *could* fold them
  in, but that is new scope, not this sweep's — noted here so a phase-close
  reviewer doesn't need to rediscover it.
- **Blueprint prose synced** (the "rational"/"rational polynomial" claims
  that no longer match the Lean): `rigidity-matrix.tex`
  (`lem:rank-polynomial-IH-relabel`, `lem:rank-polynomial-IH-relabel-proj`),
  `algebraic-induction/case-iii.tex` (`lem:case-III-nested-rank-lower`),
  `algebraic-induction/genericity-and-count.tex`
  (`lem:rank-polynomial-of-le-finrank`) — none needed a `\lean{...}` repin
  (no name changed), only the prose word. `blueprint/verify.sh` and
  `blueprint/lint.sh` both green.
- **Non-Lean cross-references to deleted names swept**: `TACTICS-GOLF.md`
  § 14, `TACTICS-QUIRKS.md` §§ 36/38 (reworded to historical/no-live-
  consumer framing) + a new § 78 (the tuple-arity miss below);
  `notes/FRICTION.md` (3 entries reworded). Closed/archived phase notes
  (`Phase22-realization-design.md`, `Phase22d.md`, `Phase22e.md`,
  `FRICTION-archive.md`, the frozen `AlgebraicIndependence.md`) left
  untouched per the archival-record exemption — they document what was
  true when written, not a live claim.
- **Friction:** a first pass missed two sibling call sites of
  `exists_rankPolynomial_of_IH_linking` inside `CaseIII/Realization.lean`
  itself (`case_III_candidate_dispatch`, `chainData_split_w6b_gates`),
  caught only by the next `lake build`'s `rcases`-arity error. Lifted to
  **TACTICS-QUIRKS § 78**.

Build + lint clean; `blueprint/verify.sh` + `blueprint/lint.sh` clean.

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
- [x] **(e)** last sweep (**sanctioned**, not optional): the
  then-unconsumed `coeffs ⊆ range (algebraMap ℚ ℝ)` rationality clauses
  across the `exists_rankPolynomial_*` family (incl.
  `exists_nested_rankPolynomial_lower_all_k`) — zero risk. **DONE
  2026-07-10** (one commit; inventory: *Current state*). **Closes the
  (a)–(e) slice plan — no further slice queued.**

## Blockers / open questions

- None.

## Hand-off / next phase

**The (a)–(e) slice plan is complete; the next concrete commit is the
phase-close checklist** (`PHASE-BOUNDARIES.md` *When this commit closes a
phase*): flip + re-thin the ROADMAP §30 row/planning section, sync the
user-facing status surfaces (README, `home_page`, `intro.tex`,
`formalization.yaml` — including a fresh `#print axioms` check against the
molecular-conjecture top-level statements), the end-to-end blueprint
chapter re-read + `notes/BlueprintExposition.md` write-up for this phase,
and the project-organization review. No further Lean lemma is queued for
Phase 30 itself; see `ROADMAP.md`'s *Queued post-program phases* for
what comes after.

## Decisions made during this phase

- **Slice (e) landed (2026-07-10), closing the (a)–(e) plan:** see
  *Current state* for the full inventory (edited/deleted/kept-as-survivor
  decls, blueprint prose sync, non-Lean cross-reference sweep). Keep-vs-
  delete calls on newly-callerless infrastructure went by independent
  value (`Matrix.det_mem_range_of_entries`,
  `ExteriorAlgebra.ιMulti_family_congr` kept; the project-specific
  rationality-leaf chain deleted).
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
