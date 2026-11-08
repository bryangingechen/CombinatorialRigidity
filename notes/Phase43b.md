# Phase 43b — LIFT3: the `d = 3` generic conjunct by the lift, the reduction proved once (work log)

**Status:** in progress (opened 2026-11-08 with the PI), the second sub-phase of Phase 43
(PENCIL-NATURAL): layer LIFT3, N1c whole as one sub-phase, at the PI's choice (design doc §1). No
Lean has changed yet. Five commits, in order: slice 1 (N1a), slice 2 (N1b's deletions, behind
N1c's reroute), slice 3 (N1c's), slice 4 (the old route as one remark, D1), slice 5 (the close).
The next concrete commit is slice 1, pinned below to builder precision: `x0Gen` from the lift, 21
declarations and two files deleted, four nodes deleted and two restated.

## Current state

**Next concrete commit: slice 1 (N1a), checklist item 1.** Its new Lean is two short bodies,
compile-checked at the open against the slice's own imports; the rest is deletion, docstrings and
blueprint prose. Opened on 2026-11-08 with the PI, who chose one sub-phase (design doc §1). Mode:
structural edit. There is no new chapter and no red target node, so the red-node consistency gate
has nothing to read: each slice reads and restates the nodes it reaches
(`CombinatorialRigidity/CLAUDE.md` *Forward-mode slices*: a changed statement, a deletion, a moved
pin). Plan and inputs: `notes/Phase43-design.md` §2, LIFT3.

**Verified at the open (HEAD `f5100f28`).**
- `lake lean notes/pencil-natural/N1Spike.lean` re-run: exit 0, no error, warning or `sorry`,
  the standard three axioms, all seven `SAME TYPE … true`. Dead constants of the `d = 3` modules
  (`Pencil/*` less `Pencil/Grade/*`): R1 20 (1,821 declaration lines), R1′ 72 (4,214), R2 85
  (4,593); the control 0. The recon's figures, unmoved.
- The spike, extended (its item 5, the earlier output byte-identical): every constant of those
  modules tagged by the first restructure that kills it, and each slice's deletion set checked.
  Slice 1: one surviving user (`pencilPair_of_nonempty`, which the slice restates), one orphan
  (the private `cons_updateRow_two`, `Chart.lean`, only `cross₃_smul_thd` uses it). Slice 2: two
  surviving users (`pencilPair_of_nonempty`, `pencil_realization_theorem`, both restated), two
  orphans outside the slice: `Submodule.exists_mem_notMem_notMem` (a mirror,
  `Mathlib/Algebra/Module/Submodule/Union.lean`) and `exists_smul_extensor_eq_of_mem_span_range`
  (`Meet.lean`). Slice 3: no surviving user and no new orphan (the three `d = 3` bridges it
  lists are premises of R2's form, which the walk at HEAD does not see).
- The graph after each slice (`notes/pencil-natural/n1c_graph.py`): no cycle at any stage; the
  lift's closure reaches no `d = 3` statement node after slice 1; slice 2 leaves slice 3's four
  `d = 3` A cases with no user for one commit; slice 3 leaves `lem:extensor-pair-through-given-point`
  with none (*Blockers*).
- Measured, scratch not retained: slice 1's `Statements.lean` bodies (item 1(b)) compile against
  the imports `X0` and `Grade.Generic` alone (`lake lean`, 0 errors, 0 warnings, the standard
  axioms); `Grade/LiftWitness.lean` compiles with its `Pencil.Pair` import deleted (no message),
  and a module-import walk shows only `Pair` and `ArmsAssembly` leave its importers' closures, of
  which `Grade/*` uses no constant (the R2 walk; the one constant of `Pair` R2 keeps,
  `exists_isNondegPencilRealization_parallel_pair`, has `Nonvacuity.lean` as its only user). The two lost from `Statements.lean`'s closure
  under item 1(b) are `GenericEar` and `GenericTriangle` alone.

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

- [ ] **1. Slice 1 — N1a: `x0Gen` from the lift** (Lean, blueprint, surfaces; one commit). Line
  numbers at `f5100f28`. The spike gives all of its new Lean (1(b)); the rest is deletion,
  docstrings and prose, so it is a transcription plus a sweep, not a pure transcription. If the
  builder must split it, (a)–(b) with the `:6673` removal and the two rerouted proofs land first
  as one green commit, the deletions second.
  - **(a)** `Grade/LiftWitness.lean`: delete `public import …Molecule.Pencil.Pair` (unused), so
    slices 2–3's edits to `Pair.lean` rebuild no `Grade/Lift*` module.
  - **(b)** `MainComponent/Statements.lean`. Imports: `…Pencil.X0` and `…Pencil.Grade.Generic`
    only (acyclic: `Grade.Generic` does not import it). Delete `hasGenericPencilRealization_of_IH`
    (:72–128) and `pencilPair_of_IH` (:130–153). Order: `x0Dist`, `x0Gen`, `pencilPair_of_nonempty`,
    `pencil_realization_theorem` (body unchanged). The two new bodies (spike (1c) and R1):
    ```lean
    theorem x0Gen [Finite α] [Finite β] [Infinite K] : X0Gen K α β :=
      fun G hS hV _ hfeas => (hasGradedGenericPencilRealization_two_iff 3 G).1
        (liftAttains_of_simple 0 hS (Set.nonempty_of_ncard_ne_zero (by omega))
          hfeas).hasGradedGenericPencilRealization

    theorem pencilPair_of_nonempty [Finite α] [Finite β] [Infinite K] (G : Graph α β)
        (hne : V(G).Nonempty) : PencilPair K 3 G :=
      pencilPair_of_arms (fun G hloop hV _ hIH => pencilPair_of_X0 x0Dist x0Gen G hloop hV hIH)
        (fun G hloop hV _ _ _ hIH => pencilPair_of_X0 x0Dist x0Gen G hloop hV hIH) G hne
    ```
    Docstring leads: `x0Gen` names `thm:pencil-x0-generic-attains` (its route:
    `liftAttains_of_simple 0`, `thm:pencil-d-generic`; `LiftAttains.hasGradedGenericPencilRealization`;
    `hasGradedGenericPencilRealization_two_iff`, `lem:pencil-d-nondegenerate-three`);
    `pencilPair_of_nonempty` names `thm:pencil-conditioned-pair-nonempty` (`pencilPair_of_arms` with
    `pencilPair_of_X0` at `x0Dist`, `x0Gen`). Rewrite the module docstring: no "inside the
    induction". No `#print` line from a spike rides into the file (`TACTICS-QUIRKS.md`, the
    40o calibration).
  - **The consumer slot, opened.** `pencilPair_of_X0`'s simple two-edge-connected arm
    (`X0.lean:103`) is `fun _ hf => hgen G hs hV h2ec hf`: `PencilPair K 3 G`'s generic conjunct at
    `G` itself, not at a smaller graph. The brick gives `HasGenericPencilRealization K 3 G` at the
    same `G` from `G.Simple`, `V(G).Nonempty` and `PencilNondegFeasible K G` alone (no `hIH`, no
    two-edge-connectivity, no third body); `liftAttains_of_simple` runs its own induction on its
    own motive (`LiftAttains K 0`). The rank is the same: `LiftAttains K 0 G` yields
    `HasGradedGenericPencilRealization K (0+1+1) (0+1+2) G`, which is `K 2 3` by evaluation, with
    target `screwDim 2 * (|V| - 1) - G.deficiency 3`, and the bridge at `n = 3` is
    `HasGenericPencilRealization K 3 G`'s. So it sits at the slot's level, on weaker hypotheses.
  - **(c)** Delete `MainComponent/GenericEar.lean` (3 declarations) and
    `MainComponent/GenericTriangle.lean` (6), all dead; drop both from `CombinatorialRigidity.lean`
    (:105, :107).
  - **(d)** Delete in place: `MainComponent/GoodEar.lean` `Graph.exists_closedEar_two_of_triangle`
    (:241–252), `Graph.IsX0Graph.exists_oneEar_or_pendantTriangle` (:442–492);
    `MainComponent/GenericBase.lean` `Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero`
    (:827–946); `MainComponent/Flat.lean` `pointJoin_ne_zero`, `extensorInPanel_pointJoin`,
    `extensorThroughPoint_pointJoin` (:814–838); `Chart.lean` `cross₃_smul_thd` (:121–128) and the
    private `cons_updateRow_two` (:86–91); `Engine.lean` the section `A nonzero vector orthogonal to
    a nonzero n as cross₃ …` with `exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero` (:588–645);
    `Motive.lean` `hasPencilRealization_of_generic` (:204–211). With (b) and (c): 21 declarations;
    nine are pins (the four deleted nodes' six, `pencilPair_of_IH`, the two that
    `lem:pencil-rigid-good-ear` loses), the rest unpinned.
  - **Kept beside it** (premises of the lift, design doc §2): `GenericBase.lean`'s other 29
    constants, `GoodEar.lean`'s other 3, `GenericSteer.lean` whole (its steering, part (b),
    until slice 2), and the nodes `lem:pencil-generic-steer`, `lem:pencil-feasible-hub-conditions`,
    `def:pencil-two-ear-graph`, `lem:pencil-x0-planes-separate`, `lem:pencil-x0-conjunct-three`,
    `lem:pencil-x0-fibre-intersection`, `lem:pencil-condition-linear`.
  - **(e)** Repoint every surviving docstring that names a deleted declaration, file or label:
    `Grade/Generic.lean:20–23`; `Grade/GoodEar.lean:16` (to
    `exists_minimalRigid_ear_or_pendantTriangle`); `Grade/LiftNoRigid.lean:20–22`;
    `MainComponent/GenericBase.lean:13–19, 34–35, 51–53` and `:767` (lead: a step of
    `lem:pencil-d-lift-no-rigid` and `lem:pencil-d-ear-extend`, its two users' nodes); `MainComponent/GoodEar.lean:13–37`
    and `:254–257`; `MainComponent/GenericSteer.lean:36–38` and `:800–801`;
    `MainComponent/Lines.lean:61–62` and `:201`; `MainComponent/Cut.lean:104` and `:771`;
    `MainComponent/Flat.lean:95–96`; `Motive.lean:511–517`; `Engine.lean:30–34`; `Chart.lean:64`.
  - **The deleted names, for the tree-wide grep** (every file kind; `grep -w`, then each stem):
    the 21 of (b)–(d); `GenericEar.lean`, `GenericTriangle.lean`; `thm:pencil-x0-base-generic`,
    `lem:pencil-generic-one-ear`, `lem:pencil-generic-pendant-triangle`, `thm:pencil-generic-step`.
    Stems: `oneEar_or_pendantTriangle`, `closedEar_two_of_triangle`, `closedEar_two`, `_of_IH`,
    `pointJoin_triangle`, `simple_ncard_eq_three`, `mem_perp_pair`, `cross₃_eq_of_ne_zero`,
    `smul_thd`, `pencilRealization_of_generic`, `pencil-generic-`. Two live names share a stem:
    `liftAttains_of_forall_deficiency_two_ne_zero` and the `…_induce_union_singleton`,
    `…_induce_pendant_of_hubLI` names, live until slice 2. Intentional survivors: closed phase
    notes, `notes/Prose-findings.md`, `notes/attacks/`, `notes/pencil/`, FRICTION's *Where it bit*
    lines, the recon record `notes/PencilNatural.md`, the design doc's 43a figures, the 40o
    calibration in `TACTICS-QUIRKS.md`, the banked probes, and the ledger's retirement lines
    (*Surfaces* below).
  - **Blueprint, `main-component.tex`.** Delete `thm:pencil-x0-base-generic` (:5182–5219),
    `lem:pencil-generic-one-ear` (:5358–5415), `lem:pencil-generic-pendant-triangle`
    (:5417–5466), `thm:pencil-generic-step` (:5534–5578) and the paragraph after it (:5580–5583).
    Restate `lem:pencil-rigid-good-ear` (:5472–5532): `\lean` keeps
    `Graph.exists_eq_triple_of_minimal`, `Graph.closedEar_two_of_triangle`,
    `Graph.IsX0Graph.exists_minimalRigid_ear_or_pendantTriangle`; the statement becomes the last
    one's conclusion (a set `W₀` with `s(W₀) ≤ 0`, `s(Z) ≥ 1` on its proper subsets of two or
    more, two neighbours in `W₀` at each body; and a body `y ∈ W₀` of degree two with hub
    neighbours `a ≠ b` in `W₀`, `|W₀ ∖ {y}| ≥ 3`, `s(W₀ ∖ {y}) ≤ 1`, or a pendant triangle whose
    common neighbour has degree at least four); the proof stops before the deficiency, and drops
    `lem:deficiency-tight-rigid`, `-merge-rigid`, `-ear-merge` (still used by
    `lem:pencil-d-good-ear`); rewrite the lead-in (:5468–5470). Restate
    `thm:pencil-conditioned-pair-nonempty` (:5585–5616): drop the `pencilPair_of_IH` pin; proof =
    `thm:pencil-conditional-realization-main-component`'s three cases at the two statements,
    which hold; `\uses{thm:pencil-conditional-realization-pair,
    thm:pencil-conditional-realization-main-component, thm:pencil-x0-generic-attains}`; move it
    after `thm:pencil-x0-generic-attains`. Reroute `thm:pencil-x0-generic-attains`'s proof
    (:5640–5650): `thm:pencil-conditioned-pair-nonempty` out, `thm:pencil-d-generic` and
    `lem:pencil-d-nondegenerate-three` in (the reversed `:6673` edge, landing on the node whose pin
    carries the route); keep the two-hubs sentence; say the forward reference uses no result that
    rests on the generic statement (43a's premise check). Prose: :148–157, :4905–4926, :5050–5054
    (`K_{2,3}` by `lem:pencil-d-good-ear`, `lem:pencil-d-lift-ear` at `d = 3`), :5055–5056 (the
    base case's lemmas serve `lem:pencil-d-lift-no-rigid`), :5221–5239 (the lemma's (a) serves the
    lift's steps; (b) the cut-edge case of `lem:pencil-pair-loop-base-cut`, until slice 2).
  - **Blueprint, `pencil-d.tex`.** The edge: `thm:pencil-conditioned-pair-nonempty` out of
    `thm:pencil-d-generic`'s proof `\uses` (:6673–6680). Its last paragraph (:6717–6732) becomes
    one sentence: at `d = 3` the theorem gives the generic main-component statement
    (`\cref{thm:pencil-x0-generic-attains}`), through `lem:pencil-d-nondegenerate-three`.
    :5146–5148, drop "is proved inside the induction of the reduction"; :5652–5653, drop the
    sentence naming `thm:pencil-generic-step`; :5730–5732, drop the triangle clause. At :6058,
    :6193, :6400 and :6652, each "At `d = 3` this is \cref{…}" sentence naming a deleted node
    says instead what the lift does at `d = 3`, where the lift is the realization itself (no
    condition at the ear, `(q, z¹)` itself generic, the triangle of rank 12), or goes; :6285–6290
    reads (i) and (ii) off the restated `lem:pencil-rigid-good-ear`. :6755–6761 stays (slice 2).
  - **Blueprint, elsewhere.** `pencil.tex:1083–1088` and `intro.tex:333–337`: the second
    statement is the case `d = 3` of the generic conjunct in every dimension
    (`thm:pencil-d-generic`), not proved inside the reduction's induction.
  - **Surfaces.** `formalization.yaml`: the fidelity sentence "proved instead inside the pencil
    reduction's own induction" (:707–711), `pencilPair_of_nonempty`'s description (:610–612:
    `x0Gen` is no longer its corollary) and `status.scope`'s "It has no Lean yet"; README
    (:219–220, and the Phase 43 paragraph) and `home_page/index.md` (:213–214, and its Phase 43
    sentence): the second statement is no longer "proved instead inside the reduction's own
    induction". `notes/BlueprintExposition.md`:
    the `thm:pencil-x0-base-generic` entry (:1657) retired in one line; the
    `lem:pencil-rigid-good-ear` entry (:1702) lists the surviving pins.
  - **Gates.** Whole `lake build`, warning-clean, 0 `failed to cache artifact`; `lake lint`;
    `blueprint/lint.sh`; `blueprint/verify.sh` (checkdecls silent);
    `python3 scripts/check-docstring-labels.py` total 0, diffed against the parent;
    `python3 notes/pencil-natural/n1c_graph.py` (slice 1's line: 0 cycles, nothing orphaned);
    `python3 notes/check-phase-note.py`; the statement and axioms checks above.
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

The next concrete commit is slice 1 (checklist item 1), whole: N1a, one commit, pinned above.
Builder rung: the coordinator's (Opus suggested: four chapters' prose and a docstring sweep beside
the Lean). After it, slice 2.

## Decisions made during this phase

The decisions of the open are `notes/Phase43-design.md` §1 (the PI's one-sub-phase choice,
2026-11-08) and the choices above.
