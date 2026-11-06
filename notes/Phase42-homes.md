# HOMES — Phase 42's deferred lemma homes and the friction log (work log)

**Status:** in progress (opened 2026-11-05 at the PI's word, after a review of the 62 friction
entries tagged `open`, `mirror-candidate`, `process` or `blueprint`). A cleanup round after
CLEANUP-42 and ahead of ORIGAMI, in two parts: the friction log's docs and tooling fixes (tasks
2–4), then the lemmas Phase 42 left outside their home files, one task per home file, with the
mirror lemmas that now meet their entries' own bar (tasks 5–18). No statement changes. Phase 42
deferred the moves because a declaration added to these files rebuilds most of `Molecular/`
mid-phase; ORIGAMI will not edit them, so they are cheapest now. Task 1 landed.
**Next concrete task:** task 2, `notes/check-phase-note.py --selftest` between phases.
Round manual: `CLEANUP.md`.

## Autopilot: for the PI

HOMES's row of `.claude/autopilot/queue.toml` is attended (a decision below), so the driver stops
before it; the PI may set `attended = false` to let `/coordinate-phase 42-homes` run it. **The one
stop is the PI's:** a task that would change a main result's statement, a blueprint statement or a
public declaration's name, or delete a pinned declaration, does not land that change: it writes a
`NEEDS_PI` entry here, newest first, and the loop stops; the PI answers in an entry that starts
`**PI, <date>:**`.

- None yet.

## Current state

**Task 1 landed** (this commit; docs only): this log, its row in ROADMAP's Status table, ROADMAP
§42's *Next* and *Queued post-program phases*, `notes/MolecularConjecture.md`, and a queue row
ahead of ORIGAMI.

**Verified at the open** (2026-11-05, at `445d8069`):
- **The review.** Of the 62 entries, about 30 can be fixed now (tasks 2–18). The rest are process
  lessons waiting to recur, blocked upstream, single-call-site mirror candidates or waiting for a
  consumer (*Scope*, out of scope).
- **Live.** `python3 notes/check-phase-note.py --selftest` exits 1 between phases ("no ACTIVE note
  found"). `TACTICS-GOLF.md`'s index lists §1–§19, an index-only §20 (the list-recursor idiom,
  `96c37025`, never given a body section) and §25–§29; the body's §20–§24 have no index entry.
- **Fixed upstream.** lean-lsp-mcp 0.33.0 ends `lean_local_search`'s pattern with `(?:\s|:|$)`; a
  live search finds `not_isNondegPencilRealization_of_two_hubs_three_common`, the entry's example
  (the results also list its copies under `scratch/`).
- **Stale entries.** The eq.-(6.12) shear: the chain is one `simp only` in
  `exists_candidate_row_eq612` (`CaseIII/Candidate.lean`), the fused
  `ofNormals_supportExtensor_eq_panel_of_ends` exists (`PanelHinge.lean`, Phase 23c), and
  `case_II_placement_eq612` is gone. The finite-set injection: `exists_injOn_mapsTo_of_ncard_le`
  was deleted in 40-simplify (`1e7d78a9`).
- **The declarations** tasks 5–18 move are where their entries say, except: the cut-sides copies
  are in `Pair2.lean`, `MainComponent/CoverageCut.lean`, `Grade/Reduction.lean` and
  `Grade/Generic.lean` (and the private helper in `ArmsAssembly.lean`; `Pair.lean` and
  `Grade/LiftSmall.lean` have none now); the `bodyBarDim` monotonicity and lower-bound unfolds are
  in `Deficiency.lean` (two), `Induction/SparseDeficiency.lean` and `Grade/Coverage.lean` (the
  `rw [bodyBarDim, Nat.mul_div_cancel' …]` sites evaluate it, which `bodyBarDim_mono` does not
  replace); `Set.ncard_range_le`'s inline glue has three sites, not two (`MainComponent/Ear.lean`,
  `MainComponent/Chain.lean`, `Grade/Chain.lean`).
- **Rebuild cost** (modules importing each home file, of 194, read from every `import` line):
  `BodyBar/Framework` 118, the `LinearIndependent/Basic` mirror 118, `Deficiency` 114, the
  `Set/Card` mirror 111, `Meet` 110, `RigidityMatrix/Basic` 109, `PanelLayer` 104,
  `GenericityDevice` 98, `Pencil/Motive` 75, `MainComponent/Cut` 42, `Grade/Realization` 39,
  `Grade/Carrier` 30, `MainComponent/ContractCurve` 25, `MainComponent/ContractAdditive` 20,
  `Grade/Configuration` and the `Fin/Basic` mirror 18, `Grade/PlanesMeet` and `Grade/Short` 6,
  `Molecule/Carrier` 4. `RigidityMatrix/Basic`'s importers include all of `GenericityDevice`'s, and
  `Meet`'s all of `PanelLayer`'s; `BodyBar/Framework`'s and the `Set/Card` mirror's overlap (146
  modules together, 229 apart).

## Scope and standing rules

- **The hygiene rule.** No main result's statement, no blueprint statement and no public
  declaration's name changes. A move keeps the declaration's name, statement and proof; a
  de-duplication keeps every surviving statement byte for byte (`diff`ed), and deletes a duplicate
  only if no `\lean{}` pin names it. A finding that would break this is a `NEEDS_PI` entry and a
  stop; anything else out of scope goes under *Candidates for the PI* or *Moved to a later round*.
- **Writes.** Lean in the files each task names (a new mirror file where a task says so, with its
  line in `CombinatorialRigidity.lean`), and the docstrings that name a moved declaration's file;
  `notes/check-phase-note.py`, `TACTICS-GOLF.md`, `notes/FRICTION.md` and `FRICTION-archive.md`
  where tasks 2–4 say; each resolved FRICTION entry, in the task that resolves it; this log; at the
  close only, the open's status surfaces. No TeX (a move keeps every pinned name), and no
  `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` or `formalization.yaml`.
- **Evidence.** A claim about a declaration comes from its statement and body at HEAD, never its
  docstring or its FRICTION entry (root `CLAUDE.md`). Each task re-`grep`s its names before
  editing: the entries were filed during Phase 42, and CLEANUP-42 round 4 moved code since.
- **The moved-name sweep.** For each moved declaration, `grep -rn` its name over the tree. A live
  mention of its old file (a Lean docstring, the blueprint, an open FRICTION entry) is repointed in
  the same commit; a dated record (a closed note, a frozen design doc, a FRICTION *Where it bit*
  line) stays.
- **Out of scope, left open in FRICTION.** Single-call-site mirror candidates, each entry's own
  bar unmet: `exists_dotProduct_eq_one_zero` (it leans on `dotPerp`), `RingHom.map_crossProduct`,
  `extensor_pair_smul`, the `ιMulti` nonvanishing iff, the dual-annihilator `map` form,
  `Submodule.span_range_smul_eq`, the `Graph.OfSimpleGraph` `Simple` instance (two sites, one
  file), `finrank_map_of_injOn` and `exists_pair_of_ncard_le_two_of_edgeSet_nonempty` (each stays
  in its file, moved by no task). Blocked upstream: `Graph.embedEdges`, the `Fin.castPred`
  simproc. Waiting to recur: the two process lessons (red-node re-classification, green-modulo
  targets). Waiting for a consumer: `IsSparse` decidability (ORIGAMI's open may want it), the
  perturbation pattern and `Function.Injective.option_elim` (a third caller). The `RecordsLinks`
  entries: *Candidates for the PI*.
- **The gates**, each in the foreground with an explicit `timeout`, the commit under
  `if <gates>; then git commit …; fi`:
  - **Every task:** (G1) `python3 notes/check-phase-note.py` green.
  - **Every Lean task:** (G2) a whole-tree `lake build`, warning-clean (`grep -cE
    'warning:|error:'` 0, `grep -c 'failed to cache artifact'` 0), then bare `lake lint` green;
    task 5 runs both before editing, as the round's baseline. (G3) `blueprint/lint.sh` green,
    check 9's docstring-label total still 0. (G4) `blueprint/verify.sh`, `checkdecls` silent,
    when a moved declaration is pinned.
  - **A Lean task that replaces a proof:** (G5) `#print axioms` of each `formalization.yaml` main
    result that imports its files, by a scratch `lake lean` file: unchanged.
  - **The close:** G1 and the tallies its line names.
- **One task, one dispatch**, the rung beside each task (`.claude/commands/coordinate-phase.md`
  *Pick the rung*). A task that does not fit lands what closes and appends the rest as a new task
  right after it, with a one-line note. One `lake build` at a time
  (`CombinatorialRigidity/CLAUDE.md`).

## Lemma checklist (the round's task list)

One commit per task, in this order: the docs tasks first, then the home files, respecting three
dependencies (7 before 8, 9 before 11, `Fin.val_succAbove` first within 14). Names are at
`445d8069`; re-`grep` before editing. FRICTION entries are named by title, since task 4 moves
entries. **On landing, a task's line is cut to at most three lines:** number, sha, what landed,
the entries it resolved.

- [x] **1. Open** (this commit; docs only).
- [ ] **2. The selftest between phases** (tooling; sonnet). `notes/check-phase-note.py`'s
  `selftest()` fails on zero ACTIVE notes only when a ROADMAP Status row reads "In progress", and
  otherwise reports them as the between-phases state; both branches tested. Resolves FRICTION
  *`check-phase-note.py --selftest` fails when no phase note is in progress*.
- [ ] **3. `TACTICS-GOLF.md`'s index** (docs only; sonnet). Index entries for the body's §20–§24,
  in the index's style. The list-recursor idiom (index-only §20) becomes body §30 with its own
  index entry, and its pointers move to §30: FRICTION's two (the *`foldl` recurrence* sub-bullet,
  and the *Lifted to* of *A `List.foldl` whose induction base case…*), and `notes/Phase23b.md`'s
  two if G1 stays green on that closed note (else kept, and listed). Phase 32's §20 pointers
  already mean the body section. Resolves FRICTION *sections-index ↔ body drift*.
- [ ] **4. The friction log's statuses and the archive sweep** (docs only; sonnet). In
  `notes/FRICTION.md`, retag:
  - `[resolved]`: the `lean_local_search` entry (*Verified at the open*); the nine `[process]` and
    `[blueprint]` entries whose status already says resolved (the `verify.sh` silent skip, the
    `blueprint/CLAUDE.md` size, the mirror ahead of its consumers, the pinned home across a
    `module` boundary, the duplicate name at the import-merge, the un-instantiable lemma, which
    gains a **Lifted to:** `DESIGN.md`'s satisfiability corollaries, the Claim-6.12 `\uses` cycle,
    the 22e column operation, the 22c superseded-route rot); the two stale entries; and the nine
    struck-through `### ~~[…]` headings;
  - `[wontfix]`, moved to *Anti-patterns*: Phase 22a's splice glue and Phase 21b's four re-plans
    (the two "don't retry" lists);
  - `[idiom]`: five Phase 7–8 `[open]` notes that are inline techniques (the `insert _ ∅` chain,
    `h ▸` oversubstitution, `nonempty_of_affineSpan_eq_top`'s explicit arguments, `fin_cases`'s
    `⟨n, ⋯⟩`, the 2×2 rotation).

  Then every `[resolved]` entry moves to `FRICTION-archive.md`, verbatim, after a `grep` for live
  pointers to each (repointed to the archive, or none found and listed).
- [ ] **5. The tree-wide basics** (Lean; sonnet). Baseline first (G2's build and lint, before
  editing). `Graph.bodyBarDim_mono : Monotone bodyBarDim` in `BodyBar/Framework.lean` beside
  `six_le_bodyBarDim`, and the four sites through it: `Connected.deficiency_le_deficiency_of_le`
  and `Connected.deficiency_eq_of_deficiency_two_add_three_le` (`Deficiency.lean`),
  `Graph.deficiencyMerged_two_add_two_le_of_three_le` (`Induction/SparseDeficiency.lean`), the
  private `exists_chainBound` (`Grade/Coverage.lean`). In the `Mathlib/Data/Set/Card.lean` mirror:
  `Set.ncard_range_le [Finite ι] (f : ι → α) : (Set.range f).ncard ≤ Nat.card ι` and its three
  sites (*Verified at the open*); `Set.ncard_eq_ncard_preimage_inl_add_ncard_preimage_inr` in
  place of `Nonvacuity.lean`'s private `ncard_eq_ncard_preimage_inl_add`. Resolves *`bodyBarDim`
  has no monotonicity…*, *No `Set.ncard_range_le`…*, part (1) of *No `Set.ncard` of a set of a
  sum type…*.
- [ ] **6. `Deficiency.lean`** (Lean; sonnet). A public
  `Graph.exists_cut_sides_of_not_twoEdgeConnected` beside `Graph.TwoEdgeConnected` (from
  `ArmsAssembly.lean`'s private `exists_cut_sides`, which goes), and the copies through it:
  `Pair2.lean`, `MainComponent/CoverageCut.lean`, `Grade/Reduction.lean`
  (`Graph.graded_pencil_realization_theorem`), `Grade/Generic.lean`. `@[simp] vertexSet_mulTilde :
  V(G.mulTilde n) = V(G)` beside `mem_edgeSet_mulTilde`, and its two sites
  (`mulTilde_removeVertex_le_splitOff`, `ForestSurgery/EdgeSplitting.lean`; `Contraction.lean`'s
  `simp [mulTilde]`). Resolves *The two sides of a cut…*, *`mulTilde` has no vertex-set lemma*.
- [ ] **7. The linear-independence mirrors** (Lean; sonnet), each at the mirror path of its
  mathlib home (`TACTICS-GOLF.md` §3): `exists_extend_linearIndependent` (from `Pencil/Reseed.lean`,
  for any finite-dimensional `V` and `Fintype ι`); `finrank_span_pair_eq_two` and
  `exists_mem_linearIndependent_pair` (from `Grade/TwoPencil.lean`, for a vector space over a
  division ring); a fused two-vector form, `LinearIndepOn K f {i, j} ↔ LinearIndependent K ![f i,
  f j]` at `i ≠ j`, named against mathlib's. Their consumers repointed; the fused form's sites are
  task 8. Resolves *No packaged "extend a `LinearIndepOn` partial family…"*, *No two-vector
  `finrank_span_pair`…*.
- [ ] **8. The two-vector sweep** (Lean; sonnet). The pencil sites (about 25 in 9 files, by the
  entry's count; re-`grep`) that bridge `LinearIndepOn.pair_iff` and `LinearIndependent.pair_iff`
  in two steps (e.g. `Base.lean`'s `hadj`), through task 7's fused form. Resolves the `n = 2` part
  of *No `n`-ary (`n ≥ 3`) analogue of `LinearIndepOn.pair_iff`*.
- [ ] **9. `Meet.lean`** (Lean; sonnet). `exists_smul_extensor_eq_of_mem_span_range_grade` (from
  `Grade/TwoPencil.lean`) beside `exists_smul_extensor_eq_of_mem_span_range`, which becomes its
  `j = 2` case; `span_range_eq_of_extensor_eq_grade` (from `Grade/Realization.lean`) beside
  `span_range_eq_of_extensor_eq`, likewise; a new `contragredientEquiv` beside `contragredient`,
  and `Grade/Collineation.lean`'s inline `toDualEquiv ≪≫ₗ g.symm.dualMap ≪≫ₗ toDualEquiv.symm`
  through it. Resolves `Meet.lean`'s parts of *42k's home debts*, *No linear-equivalence form of
  `contragredient`…* and *Grade-general extensor and panel lemmas…*.
- [ ] **10. `RigidityMatrix/Basic.lean` and `GenericityDevice.lean`** (Lean; sonnet). Into
  `Basic.lean`: `ExtensorInPanel.smul` (from `Grade/TwoPencil.lean`) beside `ExtensorInPanel`;
  `BodyHingeFramework.map`, `map_graph`, `map_supportExtensor` and
  `isInfinitesimalMotion_iff_of_supportExtensor_eq_zero` (from `Grade/Embedding.lean`) beside
  `mapExtensor`; a new `hingeRow_add_hingeRow (u v w) (r) : hingeRow u v r + hingeRow v w r =
  hingeRow u w r` beside `hingeRow_sub_hingeRow_eq`, with any `sub_add_cancel` site through it.
  Into `GenericityDevice.lean`: `finrank_span_rigidityRows_of_single_edge` (from `Grade/Arms.lean`)
  beside `finrank_span_rigidityRows_add_deficiency_le`, and
  `finrank_infinitesimalMotions_of_supportExtensor_eq_zero` (from `Grade/Embedding.lean`), whose
  import of `GenericityDevice` goes if unused. Resolves *`BodyHingeFramework.map` and the
  zero-hinge motion lemmas…*, *`hingeRow` has no additive form…*, the one-edge count of *42k build
  2…*, `ExtensorInPanel.smul` of *42k's home debts*.
- [ ] **11. `PanelLayer.lean`** (Lean; sonnet). Beside `normalsJoin`: `normalsJoin_add_right`,
  `normalsJoin_smul_right`, `normalsJoin_zero_left`, `exists_linearMap_normalsJoin_eq` (from
  `Grade/Polygon.lean`); `normalsJoin_sub_left`, `normalsJoin_zero_right`, `normalsJoinLin`,
  `normalsJoin_add_smul_add_smul` (from `Grade/Stars.lean`); `exteriorPower_map_normalsJoin` (from
  `Grade/Embedding.lean`), with `Grade/Collineation.lean`'s inline join through it; a new fold
  `ιMulti K 2 ![a, b] = normalsJoin a b`, with `starGrade_sup_starGrade_eq_ker`'s `change` through
  it. `complementScrew` (from `Grade/Short.lean`) beside `panelSupportExtensor`, with
  `panelSupportExtensor_eq_complementScrew` by `rfl` (the definition itself unchanged).
  `extensorInPanel_panelSupportExtensor_gen` (from `Grade/Realization.lean`) beside
  `extensorInPanel_panelSupportExtensor`, which becomes its `Fin 4` case. Resolves *The
  `normalsJoin` linearity and minor lemmas…*, *`complementScrew` sits in…*, and the rest of *No
  linear-equivalence form of `contragredient`…* and *Grade-general extensor and panel lemmas…*.
- [ ] **12. `Grade/Realization.lean`** (Lean; sonnet). Beside `finrank_dotPerp`: `dotPerp_sup`,
  `dotPerp_inf`, `dotPerp_antitone`, `dotPerp_top`, `finrank_dotPerp_add` and
  `finrank_dotPerp_span_singleton_of_ne_zero` (from `Grade/Feasible.lean`), and `dotPerp_map_eq`
  (from `Grade/TwoPencil.lean`). Resolves the `dotPerp` parts of *42l's home debts* and *42k's
  home debts*.
- [ ] **13. `Grade/Carrier.lean` and `Grade/Configuration.lean`** (Lean; sonnet). `gradeSigma` and
  `gradeSigma_apply` (from `Grade/ConditionLinear.lean`) beside `gradeMk`, and
  `finrank_span_pencilConfigPointGrade_closedNbhd_le`'s inline `let` through it; `pictureProj` and
  `pictureProj_pencilConfigPointGrade` made public, and the two other projections through them
  (`ConditionLinear.lean`'s local `funLeft`, `Grade/GluedEnds.lean`'s `gradePlanarProj`, with
  `gradePiForm` and `gradePi` built on `pictureProj`); `pencilConfigPointGrade_ofPoints` (from
  `Grade/Chain.lean`) beside `pencilConfigPointGrade_eq_gradeMk`. Resolves *`gradeSigma` and the
  picture projection…*, *`pencilConfigPointGrade_ofPoints` sits in…*.
- [ ] **14. `MainComponent/Cut.lean`, after `Fin.val_succAbove`** (Lean; sonnet).
  `Fin.val_succAbove (p : Fin (n + 1)) (j : Fin n) : (p.succAbove j : ℕ) = if (j : ℕ) < p then j
  else j + 1` in the `Mathlib/Data/Fin/Basic.lean` mirror (unless the pinned mathlib has it), with
  `Grade/Short.lean`'s `coe_succAbove_one` and `coe_succAbove_two` through it. Then beside
  `pathVertex_cases`: `pathVertex_add_smul`, `pathVertex_succ_castSucc`, `pathVertex_eq_of_val_eq`
  (from `Grade/Stars.lean`), `pathVertex_comp_succAbove_one`, `pathVertex_smul_comp`,
  `pathVertex_map` (from `Grade/Short.lean`); `pathVertex_zero_single` may stay. Resolves *The
  `pathVertex` lemmas of 42h…*, the `Fin` part of *No `Fin.val_succAbove`…*.
- [ ] **15. The glued-ends helpers' homes** (Lean; sonnet), all from `Grade/GluedEnds.lean`:
  `Graph.mem_closedNbhd_comm` to `Pencil/Motive.lean`, beside `closedNbhd`;
  `Graph.edgeSet_induce_pair_eq_empty`, `rigidContract_pair_simple`,
  `mem_vertexSet_rigidContract_pair`, `exists_isLink_of_rigidContract_pair`,
  `partitionDef_rigidContract_pair` and `three_le_ncard_closedNbhd_rigidContract_pair` to
  `MainComponent/ContractCurve.lean`, beside `rigidContract_induce_simple`;
  `Graph.liftingPlanesDiff_eq_top_of_notMem` to `Grade/PlanesMeet.lean`, beside
  `liftingPlanesDiff`. Resolves *Glued-ends' contraction and lifting-planes helpers…*.
- [ ] **16. The additive core's kernel argument, once** (Lean; sonnet). Re-spike first: the entry
  records a scratch copy compiling against the target file alone at 42f's close. Move
  `Graph.finrank_ker_contractLiftingMatrix_zero_eq_and_map_eq` (from `Grade/ContractAdditive.lean`),
  unchanged, into `MainComponent/ContractAdditive.lean` before `Graph.X0Attains.of_additiveContract`;
  replace that proof's `hlow0`, `hup0` and `honto` by one call (admissibility for `G` from the main
  picture); `Grade/ContractAdditive.lean` gains a `public import` of `MainComponent.ContractAdditive`.
  Resolves *The kernel argument at an additive core is proved twice…*.
- [ ] **17. The ear insertion, once** (Lean; sonnet). The insertion stated once, for an ear of
  `G″` with `n + 2` interior bodies, in `Grade/Short.lean`; `of_openEar_four`'s inline tail (`hcfa`
  to `hL`, about 80 lines) and `Grade/ShortThree.lean`'s `exists_insertion_earDataGrade_three`
  through it (the latter its `n = 0` case, or deleted if unpinned and unused). Watch the
  200 000-heartbeat budget that split `of_openEar_three`. Resolves *The insertion at three bodies
  repeats `of_openEar_four`'s inline tail*.
- [ ] **18. Two small lemmas** (Lean; sonnet). `@[simp] shadowGraph_isLink : G.shadowGraph.IsLink e
  x y ↔ G.Adj x y ∧ Sum.inl s(x, y) = e` beside `shadowGraph_isLink_iff`
  (`Molecular/Molecule/Carrier.lean`), with `Nonvacuity.lean`'s local `hL` through it.
  `LinearMap.pi_apply_eq_sum_univ_single` at the mirror path of mathlib's
  `LinearMap.pi_apply_eq_sum_univ`, with its two sites (`mem_liftMaps_pencilConfigPoint_iff`,
  `Grade/LiftNoRigid.lean`; `exists_mem_liftSpaceTilde_of_mem_liftSpace`, `Grade/LiftWitness.lean`).
  Resolves *`SimpleGraph.shadowGraph` has no `IsLink`…*, *42m build 5…*.
- [ ] **19. The close** (docs only; coordinator). Each task's sha in its line; the round closed on
  the open's status surfaces and the queue row `done = true`; FRICTION's open count before and
  after.

## Candidates for the PI

- **The `RecordsLinks` entries** (FRICTION *The tree's link hypotheses are in the form at links…*
  and *`RecordsLinks` lives in `PanelHingeFramework`…*). Moving `RecordsLinks` to `Molecular` or
  `Graph` renames a public declaration (with deprecated aliases) across the 26 files that name it,
  and restating the link hypotheses as `RecordsLinks G ends` changes statements: both break the
  hygiene rule, so they stay open for the PI.

## Moved to a later round

- None yet.

## Blockers / open questions

- None.

## Hand-off / next phase

**Next concrete task:** task 2, `notes/check-phase-note.py`'s `selftest()` between phases (*Lemma
checklist*). After the round: ORIGAMI's open, with the PI (`notes/Origami.md`).

## Decisions made during this round

- **The review's docs fixes are this round's tasks 2–4** (the open), not after-close commits of
  CLEANUP-42: each then has a work log to update, and the friction sweep is a cleanup round's job
  (`CLEANUP.md` §D).
- **One task per home file** (the open), so each deep file's importers rebuild once.
  `RigidityMatrix/Basic` shares task 10 with `GenericityDevice`, whose importers it covers, and
  `BodyBar/Framework` shares task 5 with the `Set/Card` mirror (146 modules together, 229 apart).
  `Meet` and `PanelLayer` stay apart (tasks 9 and 11), as one task would be too large.
- **Moves are unchanged** (the open): where an entry proposed restating a lemma (the one-edge count
  at `k`, `panelSupportExtensor` defined through `complementScrew`), the round moves it as it is.
- **The queue row is attended** (the open): the driver stops before it, and the PI may flip it.
