# HOMES — Phase 42's deferred lemma homes and the friction log (work log)

**Status:** in progress (opened 2026-11-05 at the PI's word, after a review of the 62 friction
entries tagged `open`, `mirror-candidate`, `process` or `blueprint`). A cleanup round after
CLEANUP-42 and ahead of ORIGAMI, in two parts: the friction log's docs and tooling fixes (tasks
2–4), then the lemmas Phase 42 left outside their home files, one task per home file, with the
mirror lemmas that now meet their entries' own bar (tasks 5–18). No statement changes. Phase 42
deferred the moves because a declaration added to these files rebuilds most of `Molecular/`
mid-phase; ORIGAMI will not edit them, so they are cheapest now. Tasks 1–12 landed
(the docs part, the tree-wide basics, `Deficiency.lean`, the linear-independence mirrors and their
sweep, `Meet.lean`, `RigidityMatrix/Basic.lean` with `GenericityDevice.lean`, `PanelLayer.lean`):
62 actionable entries down to 27 (heading tags: open 17, mirror-candidate 8, process 2, blueprint
0). **Next concrete task:** task 13, `Grade/Carrier.lean` and `Grade/Configuration.lean` (*Lemma checklist*).
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

**Task 12 landed** (this commit; Lean; sonnet; one dispatch). The seven `dotPerp` declarations are
sliced, not retyped (48 lines out of `Feasible.lean` and `TwoPencil.lean`, the same 48 in): after
`finrank_dotPerp` in `Grade/Realization.lean`, `finrank_dotPerp_add`,
`finrank_dotPerp_span_singleton_of_ne_zero`, `dotPerp_sup`, `dotPerp_inf`, `dotPerp_antitone`,
`dotPerp_top` (from `Feasible.lean`) and `dotPerp_map_eq` (from `TwoPencil.lean`). Import cone: all
proofs use only `dotPerp_dotPerp`, `mem_dotPerp`, `finrank_dotPerp` and mathlib, so the cone is
met (the build is the check). **Binders:** unchanged, as all seven sit under the same `variable
{K} [Field K]` line in both files; no caller passes any with `@`. None pinned in the blueprint, so
G4 is vacuous. Gates: G2 `lake build` (6249 jobs, 0 warnings or errors) and `lake lint`; G3
`blueprint/lint.sh` (all static reference checks passed); G5 vacuous (no proof replaced); G1.
FRICTION: *42k's home debts* `[resolved]`; *42l's home debts* retagged `[mirror-candidate]`
(`finrank_map_of_injOn` remains).

**Task 11** (`PanelLayer.lean`) is one line below; its binder reorderings are in its commit.

**Tasks 1-10** are in the checklist below, one line each. Details kept only where no line carries
them: task 10 put `isInfinitesimalMotion_iff_of_supportExtensor_eq_zero` after
`isInfinitesimalMotion_iff` (its proof calls it), and `Embedding.lean` keeps its
`GenericityDevice` import; task 9's two `j = 2` statements are byte for byte as before, and
`contragredient_toDual_pairing g` still fits the coerced `contragredientEquiv g` by defeq; task 7's
`exists_extend_linearIndependent` is `[Fintype ι]` with `Fintype.card ι ≤ finrank K M` over a
division ring and takes no `FiniteDimensional` hypothesis (the bound forces it once `ι` is
nonempty); task 8 left `Pair.lean` (four), `Nonvacuity.lean` (two) and
`MatroidIdentification.lean:125` in scalar form for its own sake, and its `Grade/LiftCases` sites
(five) came in the corrective after `bb4c09d6` misfiled them. Task 5 proved `Set.ncard_range_le` by
`ncard_image_le` on `univ` (the mirror's import closure lacks `Finite.card_range_le`); task 6
dropped `Nonvacuity.lean`'s `hV` simp argument; task 4 moved 23 `[resolved]` entries to
`FRICTION-archive.md` (pointer sweep: none needed), and tasks 2-3 are tooling and index fixes.

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

- [x] **1. Open** (`a0c236a6`; docs only).
- [x] **2. The selftest between phases** (`c0bf555a`; tooling). `selftest()` fails on zero ACTIVE
  notes only while a ROADMAP Status row is in progress (new `roadmap_in_progress()`); tested on four
  trees (*Current state*). FRICTION *`--selftest` fails when no phase note…* `[resolved]`.
- [x] **3. `TACTICS-GOLF.md`'s index** (`1b49081f`; docs only). Index entries for body §20–§24;
  the list-recursor idiom is body and index §30, its four pointers repointed (two in FRICTION, two
  in `notes/Phase23b.md`, G1 green). FRICTION *sections-index ↔ body drift* `[resolved]`.
- [x] **4. The friction log's statuses and the archive sweep** (`671661b3`; docs only). 21
  entries `[resolved]`, two `[wontfix]`, five `[idiom]`; the 23 `[resolved]` entries to
  `FRICTION-archive.md`, verbatim (*Current state*). Open entries 62 → 41.
- [x] **5. The tree-wide basics** (`5a88c26a`; Lean). `Graph.bodyBarDim_mono` and its four
  sites; `Set.ncard_range_le` (three sites) and the sum-type `ncard` lemma in the `Set/Card`
  mirror. Resolves *`bodyBarDim` has no monotonicity…*, *No `Set.ncard_range_le`…*, part (1) of
  *No `Set.ncard` of a set of a sum type…*.
- [x] **6. `Deficiency.lean`** (`b271c1f2`; Lean). Public
  `Graph.exists_cut_sides_of_not_twoEdgeConnected` (four copies and the private original through
  it) and `@[simp] vertexSet_mulTilde` (two sites). Resolves *The two sides of a cut…*, *`mulTilde`
  has no vertex-set lemma*.
- [x] **7. The linear-independence mirrors** (`a293975a`; Lean). Four lemmas in the
  `LinearIndependent/Basic` mirror, the fused two-vector form among them. Resolves *No packaged
  "extend a `LinearIndepOn` partial family…"*, *No two-vector `finrank_span_pair`…*.
- [x] **8. The two-vector sweep** (`bb4c09d6`, corrective `a654dd56`; Lean). 22 two-step sites in 9
  pencil files through the fused form. Resolves *No `n`-ary (`n ≥ 3`) analogue of `LinearIndepOn.pair_iff`*.
- [x] **9. `Meet.lean`** (`2ae15d09`; Lean). The two grade lemmas moved in, the two `j = 2`
  lemmas re-proved through them (statements unchanged); `contragredientEquiv` and its one site.
  Resolves `Meet.lean`'s parts of *42k's home debts*, *No linear-equivalence form of
  `contragredient`…* and *Grade-general extensor and panel lemmas…*.
- [x] **10. `RigidityMatrix/Basic.lean` and `GenericityDevice.lean`** (`47b63f92`; Lean). Seven
  moves, new `hingeRow_add_hingeRow`. Resolves *`BodyHingeFramework.map`…*, *`hingeRow` has no
  additive form…*, the count of *42k build 2…*, `ExtensorInPanel.smul` of *42k's home debts*.
- [x] **11. `PanelLayer.lean`** (`98be141b`; Lean; opus). Eleven moves, the new fold and `rfl`
  equation, the `Fin 4` case. Resolves *The `normalsJoin` linearity…*, *`complementScrew` sits
  in…*, *No linear-equivalence form…*, *Grade-general extensor…*.
- [x] **12. `Grade/Realization.lean`** (this commit; Lean; sonnet). Seven `dotPerp` moves beside
  `finrank_dotPerp`. Resolves the `dotPerp` parts of *42l's home debts* and *42k's home debts*.
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

- **`PanelLayer.lean`'s split** (task 11): 1705 → 1805 lines, past the ~1500 tripwire
  (`CombinatorialRigidity/CLAUDE.md`) since before the round; its three `/-! ##` sections are the
  seams. A split is not a home move, so not this round's.

## Blockers / open questions

- None.

## Hand-off / next phase

**Next concrete task:** task 13, `Grade/Carrier.lean` and `Grade/Configuration.lean` (*Lemma
checklist*): `gradeSigma` and the picture projections, one commit.
After the round: ORIGAMI's open, with the PI (`notes/Origami.md`).

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
- **A move keeps the written statement; its implicit binders follow the new file's `variable`
  order** (task 10). Keep the old order where a one-token `variable` edit does it (`{k' k : ℕ}` in
  `Basic.lean`); otherwise confirm no caller passes the name with `@`
  (`finrank_infinitesimalMotions_of_supportExtensor_eq_zero` now leads with `{k}`, as
  `GenericityDevice.lean`'s declarations do; task 11's nine reorderings are in *Current state*).
