# HOMES — Phase 42's deferred lemma homes and the friction log (work log)

**Status:** closed (2026-11-05; opened the same day at the PI's word, after a review of the 62
friction entries tagged `open`, `mirror-candidate`, `process` or `blueprint`). A cleanup round after
CLEANUP-42 and ahead of ORIGAMI, in two parts: the friction log's docs and tooling fixes and its
archive sweep (tasks 2–4), then the lemmas Phase 42 left outside their home files, one task per
home file, with the mirror lemmas that now meet their entries' own bar (tasks 5–18). Nineteen
tasks, twenty commits (task 8 had a corrective); no `NEEDS_PI` stop; no main result's statement,
blueprint statement or public declaration's name changed, and `formalization.yaml` is unchanged.
The friction log's actionable entries went from 62 to 18 (heading tags by
`grep -c '^### \[<tag>\]'`, open / mirror-candidate / process / blueprint: 35 / 13 / 12 / 2 at the
open, 8 / 8 / 2 / 0 at the close). Left for a later round: `PanelLayer.lean`'s split and, at the PI's word, the
blueprint's dependency-graph debt (*Moved to a later round*).
**Next concrete task:** ORIGAMI's open, with the PI (ROADMAP *Queued post-program phases*).
Round manual: `CLEANUP.md`.

## Autopilot: for the PI

HOMES's row of `.claude/autopilot/queue.toml` was attended (a decision below), so the driver
stopped before it; the close set it `done = true`. **The one stop was the PI's:** a task that would
change a main result's statement, a blueprint statement or a public declaration's name, or delete a
pinned declaration, did not land that change: it wrote a `NEEDS_PI` entry here, newest first, and
the loop stopped; the PI answered in an entry that starts `**PI, <date>:**`.

- None arose. The PI's one word in the round, how to close it, came at a coordinator check-in, not
  a stop (*Decisions*, the close).

## Current state

**Task 19 landed** (this commit; docs only; opus): the close. Each task's sha is in its line, and
tasks 13, 15 and 18's lines are cut to three. The round is closed on the status surfaces that
`python3 notes/phasenote.py Phase42-homes --surfaces` lists (this log's **Status**, *Current state*
and *Hand-off*, and ROADMAP's row) and on the others the open touched: ROADMAP §42's *Next*,
*Queued post-program phases*' intro, its program bullet and its CLEANUP-42 and HOMES bullets,
`notes/MolecularConjecture.md`'s HOMES sentence, and the queue's `42-homes` row (`done = true`, its
comment). The PI's word on the close is under *Decisions*. Of *Moved to a later round*,
`PanelLayer.lean`'s split is mirrored into `notes/PERFORMANCE.md` *(C) Other molecular split
candidates*, item 3; the dependency-graph debt has no round to take it and stays recorded there.
FRICTION, by `grep -c '^### \[<tag>\]' notes/FRICTION.md` (open / mirror-candidate / process /
blueprint): 35 / 13 / 12 / 2, 62 in all, at the open (`445d8069`); 8 / 8 / 2 / 0, 18 in all, at
the close. The 22 entries tasks 5–18 resolved stay `[resolved]` in `FRICTION.md` until the next
archive sweep (its filing rule). Seen at the close, not a task: besides `PanelLayer.lean`, the
round grew three files already past the ~1500-line tripwire, `Deficiency.lean` (3864 → 3882),
`Meet.lean` (1528 → 1560) and `RigidityMatrix/Basic.lean` (1633 → 1686); recorded beside
`PanelLayer.lean` in `notes/PERFORMANCE.md`. Gates: G1, and the Lean and TeX diff empty.

**The round's gates** (each task's own were in this section at its landing; git keeps them). The
coordinator re-ran each Lean task's (5–18) gates: a warning-clean build of the touched modules,
bare `lake lint`, `blueprint/lint.sh` and the sorry grep, all green. At `f97c681c`, `#print axioms`
of the 21 `formalization.yaml` main results (`scratch/homes/coord_axioms.lean`) is `[propext,
Classical.choice, Quot.sound]` each, as at the open. The coordinator's `scripts/blueprint-deps.py`
audit at `834845db`, against the pre-round cache, shows exactly the debt under *Moved to a later
round*, and task 18 replaced no pinned proof.

**What the task lines do not carry** (the rest is in each task's commit). Task 18's
`shadowGraph_isLink` has no `Sum.inl` (the carrier is `Graph V (Sym2 V)`). Task 17 left
`of_openEar_four`'s `hax` and `hbx` dead (they were before), for a golf. Task 14 left
`val_succ_succAbove` as it is (its `≤` form is a different statement), and `Cut.lean` now imports
the `Fin/Basic` mirror. Task 13's one binder change: `pencilConfigPointGrade_ofPoints` is now
`{K} {α} {m}`. Task 10 put `isInfinitesimalMotion_iff_of_supportExtensor_eq_zero` after
`isInfinitesimalMotion_iff` (its proof calls it), and `Embedding.lean` keeps its
`GenericityDevice` import; task 9's two `j = 2` statements are byte for byte as before, and
`contragredient_toDual_pairing g` still fits the coerced `contragredientEquiv g` by defeq; task 8
left `Pair.lean` (four), `Nonvacuity.lean` (two) and `MatroidIdentification.lean:125` in scalar
form for its own sake, and its `Grade/LiftCases` sites (five) came in the corrective after
`bb4c09d6` misfiled them; task 7's `exists_extend_linearIndependent` is `[Fintype ι]` with
`Fintype.card ι ≤ finrank K M` over a division ring and takes no `FiniteDimensional` hypothesis.
Task 5 proved `Set.ncard_range_le` by `ncard_image_le` on `univ` (the mirror's import closure
lacks `Finite.card_range_le`); task 6 dropped `Nonvacuity.lean`'s `hV` simp argument; task 4
moved 23 `[resolved]` entries to `FRICTION-archive.md` (pointer sweep: none needed).

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
  trees (its commit). FRICTION *`--selftest` fails when no phase note…* `[resolved]`.
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
- [x] **12. `Grade/Realization.lean`** (`cb2f8db1`; Lean; sonnet). Seven `dotPerp` moves beside
  `finrank_dotPerp`. Resolves the `dotPerp` parts of *42l's home debts* and *42k's home debts*.
- [x] **13. `Grade/Carrier.lean` and `Grade/Configuration.lean`** (`d2d407f7`; Lean; sonnet).
  `gradeSigma` beside `gradeMk`; `pictureProj` public, two projections through it; `…_ofPoints` in.
  Resolves *`gradeSigma` and the picture projection…*, *`pencilConfigPointGrade_ofPoints` sits in…*.
- [x] **14. `MainComponent/Cut.lean`, after `Fin.val_succAbove`** (`0e2da1be`; Lean; sonnet).
  `Fin.val_succAbove` in the `Fin/Basic` mirror; six `pathVertex` lemmas into `Cut.lean`. Resolves
  *The `pathVertex` lemmas of 42h…*, the `Fin` part of *No `Fin.val_succAbove`…*.
- [x] **15. The glued-ends helpers' homes** (`bdc85fdc`; Lean; sonnet), from `Grade/GluedEnds.lean`
  to `Pencil/Motive.lean` (one), `MainComponent/ContractCurve.lean` (six) and `Grade/PlanesMeet.lean`
  (one). Resolves *Glued-ends' contraction and lifting-planes helpers…*.
- [x] **16. The additive core's kernel argument, once** (`63fd4e68`; Lean; sonnet). The lemma
  into `MainComponent/ContractAdditive.lean`, `of_additiveContract` through it. Resolves *The kernel
  argument at an additive core is proved twice…*.
- [x] **17. The ear insertion, once** (`834845db`; Lean; opus). `exists_insertion_earDataGrade`
  (`Grade/Short.lean`, `n + 2` bodies of `G″`), called by `of_openEar_four` and `of_openEar_three`;
  `exists_insertion_earDataGrade_three` deleted. Resolves *The insertion at three bodies repeats…*.
- [x] **18. Two small lemmas** (`f97c681c`; Lean; sonnet). `@[simp] shadowGraph_isLink` beside
  `shadowGraph_isLink_iff`; the mirror `LinearMap.pi_apply_eq_sum_univ_single`, with its two sites.
  Resolves *`SimpleGraph.shadowGraph` has no `IsLink`…*, *42m build 5…*.
- [x] **19. The close** (this commit; docs only; opus). Each task's sha in its line; the round
  closed on its status surfaces and the queue row `done = true`; FRICTION's actionable entries 62
  at the open, 18 at the close (*Current state*).

## Candidates for the PI

- **The `RecordsLinks` entries** (FRICTION *The tree's link hypotheses are in the form at links…*
  and *`RecordsLinks` lives in `PanelHingeFramework`…*). Moving `RecordsLinks` to `Molecular` or
  `Graph` renames a public declaration (with deprecated aliases) across the 26 files that name it,
  and restating the link hypotheses as `RecordsLinks G ends` changes statements: both break the
  hygiene rule, so they stay open for the PI.

## Moved to a later round

- **`PanelLayer.lean`'s split** (task 11): 1705 → 1805 lines, past the ~1500 tripwire
  (`CombinatorialRigidity/CLAUDE.md`) since before the round; its three `/-! ##` sections are the
  seams. A split is not a home move, so not this round's. Mirrored at the close into
  `notes/PERFORMANCE.md` *(C) Other molecular split candidates*, item 3, where splits are ranked.
- **The blueprint's dependency graph is behind the round's Lean** (the coordinator's run at
  `63fd4e68` of `python3 scripts/blueprint-deps.py`, diffed against its cached pre-round run,
  `.lake/blueprint-deps/12e3e35a9ffe3111.jsonl`, written before task 5). The round's proof
  replacements left the blueprint's dependency graph behind its Lean, and HOMES writes no TeX.
  Four **missing** `\uses` edges: `lem:pencil-contract-additive-kernel` from
  `Graph.X0Attains.of_additiveContract` (task 16); `lem:pencil-d-condition-linear` from
  `finrank_span_pencilConfigPointGrade_closedNbhd_le` → `gradeSigma` (task 13), which the tool
  flags as one that "would close a cycle", so it needs a node restructure, not just an edge;
  `lem:pencil-d-embedding-join` from `panelSupportExtensor_linearEquiv_eq_det_smul` (task 11) and
  from `starGrade_sup_starGrade_eq_ker` (task 11). One new **unbacked** edge:
  `lem:decomposable-extensor-span-unique` (`meet.tex:577`) `\uses{def:join}`, which task 9's
  re-proof of `span_range_eq_of_extensor_eq` through the grade lemma no longer reaches; its Lean
  docstring still describes the `join_extensor` / `extensor_triple_eq_zero_iff` route. The other
  twelve missing edges predate the round. (Task 17 adds none: `--label` on its two theorems' nodes
  gives the same edges as at `63fd4e68`; the coordinator's audit at `834845db` finds this list
  exactly.) At the PI's word all five stay here (*Decisions*, the close). No round takes them yet:
  none is queued, and ORIGAMI's chapters are others. This entry is their record until a later
  round's open takes them; ROADMAP's HOMES bullet points here.

## Blockers / open questions

- None.

## Hand-off / next phase

**Next concrete task:** ORIGAMI's open, with the PI (ROADMAP *Queued post-program phases*;
`notes/Origami.md`). HOMES is done: the round closed with this commit, and the queue's `42-homes`
row is `done = true`. ORIGAMI, the queue's next row, is attended, so it opens with the PI and takes
its phase number then.

**What carries over:** *Moved to a later round*'s two entries, `PanelLayer.lean`'s split (ranked
in `notes/PERFORMANCE.md`) and the blueprint's dependency-graph debt (four missing `\uses` edges,
one of which would close a cycle, and one unbacked `def:join` edge), which no round yet takes.
Also left: the `RecordsLinks` entries (*Candidates for the PI*, open in FRICTION), task 17's dead
`hax`/`hbx` (a golf; *Current state*) and the 22 `[resolved]` FRICTION entries, for the next
archive sweep.

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
  `GenericityDevice.lean`'s declarations do; task 11's nine reorderings are in its commit, task
  13's one in *Current state*).
- **The close, at the PI's word** (task 19). The coordinator asked the PI how HOMES should close,
  given the dependency-graph debt under *Moved to a later round*. The PI's choice, verbatim
  (2026-11-05): **"Close now, defer all"**, whose option text read: "The close only (1 commit). All
  five edge issues stay recorded under *Moved to a later round* in notes/Phase42-homes.md, and
  ORIGAMI opens next."
- **The deferred items' homes** (task 19). `PanelLayer.lean`'s split is mirrored into
  `notes/PERFORMANCE.md` *(C)*, item 3, the list that ranks split candidates (where
  `notes/Phase40-cleanup.md`'s close said a split would be ranked). The dependency-graph debt has
  no round or plan to mirror into, so it stays under *Moved*, as the PI's word says, and ROADMAP's
  HOMES bullet points at it.
