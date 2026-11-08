# Phase 43b — LIFT3: the `d = 3` generic conjunct by the lift, the reduction proved once (work log)

**Status:** in progress (opened 2026-11-08 with the PI), the second sub-phase of Phase 43
(PENCIL-NATURAL): layer LIFT3, N1c whole as one sub-phase, at the PI's choice (design doc §1).
Five commits, in order: slice 1 (N1a, landed), slice 2 (N1b's deletions, behind N1c's reroute),
slice 3 (N1c's), slice 4 (the old route as one remark, D1), slice 5 (the close). The next concrete
commit is slice 2, checklist item 2: `pencilPair_of_nonempty` as the `m = 1` case, 49 declarations
deleted.

## Current state

**Next concrete commit: slice 2, checklist item 2.** Mode: structural edit, no new chapter and no
red target node; each slice reads and restates the nodes it reaches (`CombinatorialRigidity/CLAUDE.md`
*Forward-mode slices*). Plan and inputs: `notes/Phase43-design.md` §2, LIFT3.

**Slice 1 landed (N1a).** `x0Gen` is `liftAttains_of_simple 0` read at `d = 3`
(`MainComponent/Statements.lean`, importing only `X0` and `Grade.Generic`); `pencilPair_of_nonempty`
is `pencilPair_of_arms` with `pencilPair_of_X0 x0Dist x0Gen`. The 21 declarations, `GenericEar.lean`
and `GenericTriangle.lean` are gone; `thm:pencil-x0-base-generic`, `lem:pencil-generic-one-ear`,
`lem:pencil-generic-pendant-triangle` and `thm:pencil-generic-step` are deleted;
`lem:pencil-rigid-good-ear` stops at the tight set; `thm:pencil-conditioned-pair-nonempty` follows
`thm:pencil-x0-generic-attains`, whose proof `\uses` `thm:pencil-d-generic` (the reversed `:6673`
edge). Main results' signatures byte-identical, the standard three axioms; `n1c_graph.py` slice 1:
0 cycles, nothing orphaned.

**Inputs for slices 2–3.** Dead constants of the `d = 3` modules (`Pencil/*` less `Pencil/Grade/*`,
`notes/pencil-natural/N1Spike.lean` item 5), re-run after slice 1 (`lake lean`, 0 errors, all seven
`SAME TYPE … true`): R1 0, R1′ 52 (2,392 declaration lines), R2 65 (2,771), the open's figures less
R1's 20 (1,821). Slice 2: two surviving users (`pencilPair_of_nonempty`,
`pencil_realization_theorem`, both restated), two orphans outside the slice:
`Submodule.exists_mem_notMem_notMem` (a mirror, `Mathlib/Algebra/Module/Submodule/Union.lean`) and
`exists_smul_extensor_eq_of_mem_span_range` (`Meet.lean`). Slice 3: no surviving user and no new
orphan. The graph (`notes/pencil-natural/n1c_graph.py`, re-run after slice 1): slice 2 leaves slice
3's four `d = 3` A cases with no user for one commit; slice 3 leaves
`lem:extensor-pair-through-given-point` with none (*Blockers*).

## Architectural choices made up front

- **Statements byte-identical:** `pencil_realization_theorem`, `pencilPair_of_nonempty`,
  `Graph.graded_pencil_conditioned_pair`, and `x0Dist`, `x0Gen` (their types, `X0Dist`, `X0Gen`,
  stay). Each Lean slice diffs their signature lines and runs `#print axioms` on the three main
  results in a scratch file (`lake lean`): the standard three.
- **Slice boundaries from the bodies.** A slice deletes a set the spike's walk finds dead and
  closed upward: nothing outside it uses it, at HEAD less the slice's restated proofs (item 5's
  check). Figures from the walk are measured; the recon's are labelled so.
- **N1b's deletions behind N1c's reroute.** The spike's R1′ keeps A by writing its step out
  (`pencilPair_of_nonempty_R1'`, about 40 lines) that slice 3 would delete again. Slice 2 lands
  R2's six lines instead and deletes R1′'s set; slice 3 deletes R2's remainder. The PI's order of
  deletions holds; the literal R1′ stays available from the spike if the coordinator prefers it.
- **The old route's prose.** Slices 1–3 cut or restate, about the lift at `d = 3`, each sentence
  that names a node they delete. Slice 4 writes D1's one remark (the route and why the lift
  replaces it; the deleted text is in `git show <slice sha>^`).

## Lemma checklist

- [x] **1. Slice 1 — N1a: `x0Gen` from the lift** (landed; *Current state*). Its pinned plan is
  in `git show 9c68719e:notes/Phase43b.md`. Beyond the pins: `pencil.tex`'s
  `thm:pencil-realization-theorem` proof dropped "on which the proof of the generic statement
  rests", `intro.tex`'s Phase 43 sentence and `formalization.yaml`'s route note (`x0Gen` by phase 43)
  were updated, and `Chart.lean`'s `cons_updateRow_three` docstring and FRICTION's triangle
  status line were repointed. For slice 2: the new lead-in to `lem:pencil-generic-steer`
  (`main-component.tex`) names part (b) and `lem:pencil-pair-loop-base-cut`, and
  `MainComponent/GenericSteer.lean`'s module docstring names `Pair2.lean`; both go with them.
- [ ] **2. Slice 2 — `pencilPair_of_nonempty` as the `m = 1` case; N1b's deletions.** Lean:
  `pencilPair_of_nonempty` := the spike's `pencilPair_of_nonempty_R2` (six lines, through
  `hasGradedPencilRealization_two_iff`, `hasGradedDistinctPencilRealization_two_iff`,
  `hasGradedGenericPencilRealization_two_iff`, `gradedPencilNondegFeasible_two_iff`);
  `pencil_realization_theorem` := `pencilPair_of_nonempty G (hspan ▸ Set.univ_nonempty)`;
  `x0Gen` as slice 1 left it. Delete the spike's `n1Slice2`, 49 declarations, 2,321
  declaration lines (R1′'s 2,393 less the transport's 72): `Pair2.lean` whole (5); in `Pair.lean`
  the four generic arms; `X0.lean` `pencilPair_of_X0`, `pencil_realization_theorem_of_X0`;
  `Arms.lean` six (it keeps `exists_contragredient_linearEquiv`, used by
  `Grade/LiftCutEdge.lean`, and `exists_perp_linearIndependent`, `exists_reposition_cross_incidences`,
  unreached but pins of `lem:pencil-cut-nondegeneracy`, a premise of the lift, and the transport's
  three until slice 3); `Steer.lean` 10; `Engine.lean` 13; `GenericSteer.lean` 5; `Motive.lean` 3;
  `Statement.lean` 1. Imports: `X0.lean` off `Pair2`; `Nonvacuity.lean` imports `Pair` (its
  `exists_isNondegPencilRealization_parallel_pair` loses its only route). Blueprint: delete
  `lem:pencil-pair-loop-base-cut`, `thm:pencil-conditional-realization-pair`,
  `thm:pencil-conditional-realization-main-component`; `lem:pencil-generic-steer` loses part (b)
  and the pin `exists_isNondegPencilRealization_steer`; `cor:pencil-d-conditioned-pair` drops
  `thm:pencil-conditioned-pair-nonempty` (`:6755`) and `thm:pencil-conditioned-pair-nonempty`
  `\uses` it with `lem:pencil-d-rank-agrees-three`, `lem:pencil-d-nondegenerate-three` (the
  reversal); `thm:pencil-realization-theorem`'s proof loses the main-component route;
  `sec:pencil-main-component-route`'s framing, `def:pencil-main-component-statements`' role and
  the comparisons at `pencil-d.tex:5551`, `:5626`, `:5730`, `:5886`, `:5979` are restated;
  `formalization.yaml`'s `pencil_realization_theorem` description. Deleted-name list: the 49,
  `Pair2.lean`, the three labels.
- [ ] **3. Slice 3 — the rest of N1c.** Delete `n1Slice3`, 16 declarations, 451 declaration
  lines: `ArmsAssembly.lean` whole (4); `Pair.lean` `pencilPair_of_isLoopAt`,
  `pencilPair_of_ncard_le_two`, `hasGenericPencilRealization_of_ncard_le_two` (it keeps
  `exists_isNondegPencilRealization_parallel_pair`, and changes its import off `ArmsAssembly`);
  `X0.lean` `hasPencilRealization_of_not_simple`; `Motive.lean` `not_simple_of_parallel`, `hasDistinctPencilRealization_of_generic`,
  `not_pencilNondegFeasible_of_isLoopAt`; `Statement.lean` `hasPencilRealization_of_distinct`,
  `exists_linearIndependent_extensor_pair_through_point`; `Arms.lean` the transport's three.
  Blueprint: delete `lem:pencil-loop-case`, `lem:pencil-cut-case`, `lem:pencil-base-case`,
  `lem:pencil-nonsimple-case` with its note, `lem:extensor-pair-through-point`,
  `lem:pencil-projective-transport`; the seven `\cref`s in `sec:pencil-d-reduction` (:4468, :4533,
  :4593, :4672, :4777, with :4300 and :4835 read against the result).
- [ ] **4. Slice 4 — the old route as one remark (D1).** One short unlabelled remark, in
  `sec:main-component-statements` or `sec:pencil-d-generic`, naming the `d = 3` route (the
  generic conjunct inside the reduction's induction: no planar-rigid set, the triangle, a
  one-body ear, a pendant triangle) and why the lift replaces it; the `sec:pencil-d-lift` intro
  read end to end; the "At `d = 3` this is …" sentences left after slices 1–3 (the recon: about
  17 in all) collapsed; the open questions of *Blockers* settled.
- [ ] **5. Close (43b).** The sub-phase close of `PHASE-BOUNDARIES.md`: the ROADMAP marker, §43's
  43b detail compressed, the design doc's LIFT3 entry to a verdict, the ledger's 43b section, the
  main results' axioms run, `formalization.yaml`'s route descriptions; then NORMAL's open, at the
  PI's word.

## Blockers / open questions

- **Two outside orphans after slice 2:** `Submodule.exists_mem_notMem_notMem` (a mirror, so an
  upstream candidate) and `exists_smul_extensor_eq_of_mem_span_range` (`Meet.lean`, the `j = 2`
  case of a graded lemma). Keep or delete: slice 2's builder proposes, the coordinator decides.
- **`lem:extensor-pair-through-given-point` loses its only user in slice 3**; its pin is already
  unreached at HEAD. Keep (a proved result) or delete with its Lean: slice 3's call.
- **Two nodes pin `pencilPair_of_nonempty`:** `thm:pencil-conditioned-pair-nonempty` and
  `thm:pencil-realization-theorem`. With `thm:pencil-generic-step` gone (slice 1), the first
  exists only as the reversed edge's target; whether it folds into the second is slice 4's.
- **`X0.lean` after slice 3** holds only `X0Dist` and `X0Gen`: whether they move into
  `Statements.lean`: slice 3's call.

## Hand-off / next phase

The next concrete commit is slice 2 (checklist item 2), whole: `pencilPair_of_nonempty` as the
spike's `pencilPair_of_nonempty_R2`, and N1b's 49 deletions, one commit. The spike still runs at
HEAD, so its item 5 re-checks the deletion set first. Builder rung: the coordinator's (Opus
suggested). After it, slice 3.

## Decisions made during this phase

The decisions of the open are `notes/Phase43-design.md` §1 (the PI's one-sub-phase choice,
2026-11-08) and the choices above.
