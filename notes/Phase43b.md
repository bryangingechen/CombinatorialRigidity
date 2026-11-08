# Phase 43b — LIFT3: the `d = 3` generic conjunct by the lift, the reduction proved once (work log)

**Status:** in progress (opened 2026-11-08 with the PI), the second sub-phase of Phase 43
(PENCIL-NATURAL): layer LIFT3, N1c whole as one sub-phase, at the PI's choice (design doc §1).
Five commits, in order: slice 1 (N1a, landed), slice 2 (N1b's deletions, behind N1c's reroute,
landed), slice 3 (N1c's), slice 4 (the old route as one remark, D1), slice 5 (the close). The next
concrete commit is slice 3, checklist item 3: the rest of N1c, 16 declarations deleted.

## Current state

**Next concrete commit: slice 3, checklist item 3.** Mode: structural edit, no new chapter and no
red target node; each slice reads and restates the nodes it reaches (`CombinatorialRigidity/CLAUDE.md`
*Forward-mode slices*). Plan and inputs: `notes/Phase43-design.md` §2, LIFT3.

**Slices 1–2 landed.** Slice 1 (N1a): `x0Gen` is `liftAttains_of_simple 0` read at `d = 3`; the
`d = 3` generic route went (21 declarations, four nodes). Slice 2: `pencilPair_of_nonempty` is the
`m = 1` case of `Graph.graded_pencil_conditioned_pair` through the four `d = 3` bridges, and
`pencil_realization_theorem` is it at a spanning graph. N1b's 49 declarations (`Pair2.lean` whole)
and `exists_smul_extensor_eq_of_mem_span_range` are gone; so are `lem:pencil-pair-loop-base-cut`,
`thm:pencil-conditional-realization-pair` and `thm:pencil-conditional-realization-main-component`.
`lem:pencil-generic-steer` is its old part (a), unlabelled; `thm:pencil-conditioned-pair-nonempty`
follows `cor:pencil-d-conditioned-pair` (the reversed `:6755` edge), and
`thm:pencil-realization-theorem` follows it alone. `x0Dist`, `x0Gen` have no Lean consumer. Main
results' signatures byte-identical, the standard three axioms. The blueprint graph against the
parent: 0 cycles; orphaned, the four `d = 3` A cases (`lem:pencil-loop-case`, `-base-case`,
`-cut-case`, `lem:pencil-nonsimple-case`, planned, slice 3 deletes them) and
`thm:pencil-x0-generic-attains` (*Blockers*).

**Inputs for slice 3.** The spike (`lake lean`) runs at HEAD with two errors, its (2) and R1 naming
slice 2's deletions; its item 5 reports slice 3: no surviving user, no orphan, all 16 UNREACHED.
`notes/pencil-natural/n1c_graph.py`, whose start is now the post-slice-2 tree: slice 3 leaves
`lem:extensor-pair-through-given-point` with no user (*Blockers*).

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
  in `git show 9c68719e:notes/Phase43b.md`.
- [x] **2. Slice 2 — `pencilPair_of_nonempty` as the `m = 1` case; N1b's deletions** (landed;
  *Current state*). Its pinned plan is in `git show c5d115ba:notes/Phase43b.md`. Beyond the pins:
  `exists_smul_extensor_eq_of_mem_span_range` deleted (*Decisions*); `lem:pencil-generic-steer`'s
  `(a)` label dropped with part (b), in its three `pencil-d.tex` crefs and the Lean docstrings, and
  its proof's rank step with it; `thm:pencil-realization-theorem`'s proof drops
  `thm:pencil-x0-generic-attains` too; `Motive.lean`'s cut-side helpers repointed to
  `lem:pencil-d-lift-small`, `lem:pencil-d-lift-cut-edge`; `sec:pencil-reduction`'s case order,
  `main-component.tex`'s introduction, `intro.tex`, README, the home page, the ledger (two entries
  retired) and FRICTION (`extensor_pair_smul`'s status, the mirror's) updated.
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

- **`lem:extensor-pair-through-given-point` loses its only user in slice 3**; its pin is already
  unreached at HEAD. Keep (a proved result) or delete with its Lean: slice 3's call.
- **`thm:pencil-x0-generic-attains` has had no user since slice 2**, and its pins `x0Dist`, `x0Gen`
  no Lean consumer: the theorem no longer routes through the main-component statements. It sums up
  `sec:main-component` (its first claim, `thm:pencil-x0-coverage`, serves `sec:pencil-d-stable`).
  Its role beside the every-dimension route: slice 4's, with D1's remark.
- **Two nodes pin `pencilPair_of_nonempty`:** `thm:pencil-conditioned-pair-nonempty` (the `d = 3`
  case of `cor:pencil-d-conditioned-pair`, used only by the other) and
  `thm:pencil-realization-theorem`; whether the first folds into the second is slice 4's.
- **`X0.lean` after slice 3** holds only `X0Dist` and `X0Gen`: whether they move into
  `Statements.lean`: slice 3's call.

## Hand-off / next phase

The next concrete commit is slice 3 (checklist item 3), whole: the spike's `n1Slice3`, 16
declarations, and the six nodes, one commit. The spike's item 5 re-checks the set at HEAD first
(its two errors, in (2) and R1, are expected). The `pencil-d.tex` crefs of item 3 have moved by a
line at most; the four cases are also cited at `:4318`–`:4322` (the section's introduction, as
slice 2 restated it) and `:4702`. Builder rung: the coordinator's. After it, slice 4.

## Decisions made during this phase

The decisions of the open are `notes/Phase43-design.md` §1 (the PI's one-sub-phase choice,
2026-11-08) and the choices above.

- **Slice 2's outside orphans** (coordinator, 2026-11-08): `Submodule.exists_mem_notMem_notMem`
  kept, an upstream candidate; `exists_smul_extensor_eq_of_mem_span_range` deleted.
