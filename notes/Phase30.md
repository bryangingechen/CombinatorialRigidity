# Phase 30 — Algebraic-independence relaxation (RELAX) (work log)

**Status:** ✓ complete (opened 2026-07-09; closed 2026-07-10).

## Current state

**Phase closed.** The molecular-conjecture development no longer uses
algebraic independence anywhere. Delivered (the user-sanctioned (a)–(e)
structural-edit slice plan, green at every commit): the
`AlgebraicIndependent ℚ` fifth conjunct of `HasGenericFullRankRealization`
is deleted; every composition that re-uses an induction-hypothesis
realization now chooses its seed as a non-root of a finite product of base
det/rank polynomials fixed *before* the seed (one
`MvPolynomial.exists_eval_ne_zero` shot — the same four base factors at
every `d`); the now-callerless alg-independence family and its three mirror
files are deleted; and the then-unconsumed rationality clauses across the
`exists_rankPolynomial_*` family are swept. The headline theorem statements
are unchanged; `#print axioms` was re-checked at close on all eleven
`formalization.yaml` main results (`propext`, `Classical.choice`,
`Quot.sound` only). Build + lint + blueprint gates green throughout.

## R1/R2 recon records (compressed)

Lean docstrings cite this note's recon working sections by name (*R1 spike
route*, *R1 composition-point pins*, *R2 record*, *R2 spike route*). Those
sections were working memory for the build, compressed out at slices
(d)/(e); they live in this file's git history (the R1/R2 verdict commits
`aeed97a0` / `2f8496d9`, and this file as of the slice-(c) commit). The
surviving route content is in the landed declarations' docstrings
(`case_III_candidate_dispatch`, `chainData_split_w6b_gates`,
`case_I_realization_h65_gen`, `exists_tripleLI_polynomial`,
`exists_tupleLI_polynomial`) and the frozen derivation record
`notes/AlgebraicIndependence.md` §2. Both recons were **GO** (2026-07-10,
each compiler-witnessed by a sorry-free general-`k` spike): the product
route replaces every spine algebraic-independence use with non-root
conditions of the **same four base polynomial factors at every `d`** —
zero per-candidate factors.

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
- [x] **slices (a)–(e)** — all landed 2026-07-10 (tracker below).
- [x] **phase close** — 2026-07-10 (record under *Decisions made*).

### Refactor slice tracker (the structural-edit Layer plan; all DONE 2026-07-10)

- [x] **(a)** the two det-factor bricks (`exists_tripleLI_polynomial`,
  `exists_tupleLI_polynomial`) + the LI-form pick
  (`exists_chainData_discriminator_pick_of_LI`) + the polynomial-form
  nested-rank bound (`exists_nested_rankPolynomial_lower_all_k`), additive,
  in `CaseIII/Realization.lean`.
- [x] **(b)** the three IH-seed-reuse compositions
  (`case_III_candidate_dispatch`, `chainData_split_w6b_gates`,
  `case_I_realization_h65_gen`) reshaped to device-chosen seeds (three
  commits).
- [x] **(c)** the motive conjunct deleted + the ~10 chooser sites switched
  to `exists_eval_ne_zero` + producer hypothesis drops (one commit).
- [x] **(d)** the now-callerless alg-indep family + the three mirrors
  deleted, blueprint restated (one commit; inventory: *Decisions made*).
- [x] **(e)** the then-unconsumed rationality clauses across the
  `exists_rankPolynomial_*` family swept (one commit; inventory:
  *Decisions made*). Closed the (a)–(e) plan.

## Blockers / open questions

- None.

## Hand-off / next phase

**Phase 30 is closed; no successor phase is open.** The next concrete task
is opening the first phase off ROADMAP's *Queued post-program phases*
subsection (UPSTREAM — mathlib upstreaming of the `[mirrored]` lemmas — or
VERSO, external-gated), minting its number per `PHASE-BOUNDARIES.md` *When
this commit opens a phase*.

## Decisions made during this phase

- **R1/R2 verdicts (2026-07-10): both GO**, compiler-witnessed sorry-free
  at general `k`. Frozen derivation record:
  `notes/AlgebraicIndependence.md` §2 (two premise corrections there);
  compressed recon pointers: *R1/R2 recon records* above.
- **Slices (a)–(c) (2026-07-10):** additive leaves → device-seed reshapes →
  conjunct deletion, each build+lint clean; every forced repair
  (destructures, chooser sites, producer hypothesis drops) landed in the
  same commit as its slice. Route detail: the reshaped decls' docstrings +
  git history.
- **Slice (d) (2026-07-10) — the deletion inventory:** the five
  `CaseIII/Realization.lean` alg-indep decls
  (`linearIndependent_normals_of_algebraicIndependent{,_triple,_general}`,
  the alg-indep `exists_chainData_discriminator_pick`, the nested-rank pair
  `case_III_nested_rank_lower{,_all_k}`, D-CAN-4); the `CaseI.lean`
  seed-rank-bridge family (retirement-history comment left in place);
  `exists_injective_algebraicIndependent_real` + the three mirror files
  (`Mathlib/RingTheory/AlgebraicIndependent/{Defs,TranscendenceBasis}.lean`,
  `Mathlib/RingTheory/MvPolynomial/Tower.lean`) + the transfer lemma
  `eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent`.
  Deletion-variant grep discipline applied tree-wide; blueprint:
  `lem:case-III-nested-rank-lower` restated to polynomial form, the
  seed-rank-bridge/-upper/-attainment nodes collapsed to a prose remark,
  two downstream `\uses` edges dropped (ambient-hypothesis case, not
  dangling deps).
- **Slice (e) (2026-07-10) — the rationality sweep inventory:** conjunct
  dropped from the four `GenericityDevice.lean` producers, the four
  `CaseI.lean` pass-through siblings,
  `exists_nested_rankPolynomial_lower_all_k` + its `h622lb`-shaped callers;
  deleted as newly-callerless: the Rank.lean rationality refinement, the
  `PanelLayer.lean` rationality-leaf chain, `Meet.lean`'s
  `complementIso`/`wedgePairing` range lemmas, `CaseI.lean`'s private
  `dualMap_matrix_entry_eq`. Kept as independent-value survivors (zero
  live callers, docstrings + FRICTION reworded to say so):
  `Matrix.det_mem_range_of_entries`,
  `ExteriorAlgebra.ιMulti_family_congr` (both `[mirrored]`). Blueprint
  prose + `TACTICS-GOLF.md` § 14 / `TACTICS-QUIRKS.md` §§ 36/38 /
  `notes/FRICTION.md` synced in the same commit.
- **Deliberately out of scope (recorded so it isn't rediscovered):** the
  two general-position producers `exists_generalPosition_polynomial`
  (`PanelHinge.lean`) and `exists_generalPosition4_polynomial`
  (`Molecule/GeneralPosition4.lean`) still carry a live rationality
  conjunct, unconsumed at every call site (all discard it via `_`) — a
  distinct math family (general-position avoidance, not the
  `exists_rankPolynomial_*` rank-witnessing pattern the sanctioned sweep
  named). A future pass *could* fold them in; that is new scope.
- **Phase close (2026-07-10):** ROADMAP row + §30 compressed;
  `notes/AlgebraicIndependence.md` frozen (status/pointers updated to the
  landed state); `notes/MolecularConjecture.md` phase pointer closed;
  `formalization.yaml` `status.scope` re-summarized + `#print axioms`
  re-verified; README / home_page / intro.tex deliberately unchanged (the
  post-program-phase precedent from Phases 27–29: those surfaces summarize
  at arc level and the headline results didn't change). Blueprint
  re-read of the eight Phase-30-edited chapters: prose coherent, no
  accumulated per-commit asides to collapse. Exposition ledger: **no new
  entry** (the product-route reroute is a project-side simplification, not
  a compressed KT step); three existing entries reconciled to the landed
  route (`lem:case-III-claim-6-11`, `lem:theorem-56-general-position`, the
  23a/CARRIER screening row). Stale-doc sweep: the five leftover
  slice-(b)-era "fifth conjunct rides unused" comments
  (`CaseIII/Realization.lean`, `Theorem55.lean`) and
  `exists_generalPosition4_polynomial`'s "algebraically-independent seed"
  docstring reworded to the product route; the dangling `notes/Phase30.md`
  section pointers in Lean docstrings resolve via *R1/R2 recon records*
  above. Dispatch-log grooming left to the coordinator (coordinator-owned
  file). Friction review: no new entries (doc/comment-only Lean changes).
