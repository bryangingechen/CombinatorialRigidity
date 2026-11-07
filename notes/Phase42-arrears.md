# ARREARS — what HOMES left: the dependency graph, four splits and `RecordsLinks` (work log)

**Status:** closed (2026-11-06; opened 2026-11-05 at the PI's word: "Let's take care of the items
that were deferred by the last phase"). A cleanup round after HOMES and ahead of ORIGAMI. It took
what HOMES's close carried over, with the scope the PI chose at the open and the four *Candidates*
the PI took into the round on 2026-11-06 (*Decisions*): the blueprint's dependency-graph debt (16
missing edges to 0), the friction log's archive sweep, the splits of the four molecular files past
the ~1500-line tripwire, and `RecordsLinks` moved to `Graph`, with the link hypotheses, witnesses
and conclusions in its terms. Twenty tasks (10 a no-op, 11 unused), nineteen commits with the PI's
record of the candidates; no `NEEDS_PI` stop. Tasks 13-18's restatements are equivalent; at the
PI's word, task 19 weakened three total-form hypotheses to `RecordsLinks` plus a new `hs` and
repinned one node. Four lemmas left without a caller were deleted, one by the open's scope and
three at the PI's word (*Scope*). No main result's statement changed, and `formalization.yaml` is
unchanged. FRICTION's actionable entries went from 18 to 16 (*Current state*).
**Next concrete task:** PENCIL-NATURAL's open, with the PI (queued 2026-11-07 ahead of ORIGAMI;
`notes/PencilNatural.md`), then ORIGAMI's. Round manual: `CLEANUP.md`.

## Autopilot: for the PI

ARREARS's row of `.claude/autopilot/queue.toml` was attended (the open's choice), so the driver
stopped before it; the close set it `done = true`. **The one stop was the PI's:** a task that would
change a main result's statement, or a blueprint statement's strength, or rename a public
declaration other than the `RecordsLinks` API, did not land that change: it wrote a `NEEDS_PI`
entry here, newest first, and the loop stopped; the PI answered in an entry that starts `**PI,
<date>:**`.

- None arose. The PI's words in the round (the scope at the open, the four candidates, the total
  form; *Decisions*) came at the coordinator's questions, not at stops.

## Current state

**Task 20 landed** (this commit; docs only; opus): the close. Each task's sha is in its line (task
19's `ac1ab052`), and task 11's says it went unused. The round is closed on the status surfaces that
`python3 notes/phasenote.py notes/Phase42-arrears.md --surfaces` lists (this log's **Status**,
*Current state* and *Hand-off*, and ROADMAP's row) and on the others the open touched: ROADMAP
§42's *Next*, *Queued post-program phases*' intro, its program bullet and its HOMES and ARREARS
bullets, `notes/MolecularConjecture.md`'s ARREARS sentence, and the queue's `42-arrears` row
(`done = true`, its comment). `README.md`, `home_page/index.md` and `intro.tex` never named the
round, and `formalization.yaml` is unchanged (*Writes*). *Candidates* and *Moved* are empty, so
nothing is mirrored. FRICTION, by `grep -c '^### \[<tag>\]' notes/FRICTION.md` (open /
mirror-candidate / process / blueprint): 8 / 8 / 2 / 0, 18 in all, at the open (`6d75d694`); 6 / 8 /
2 / 0, 16 in all, at the close. Task 12 took *`RecordsLinks` lives in `PanelHingeFramework`…* to
`[mirrored]` (71 → 72) and task 18 resolved *The tree's link hypotheses are in the form at
links…*; tasks 12, 14 and 19 filed one `[idiom]` each (248 → 251); task 2 archived the 22
`[resolved]` entries HOMES left. Task 18's `[resolved]` entry waits for the next archive sweep. G6
at the close (`scripts/blueprint-deps.py --summary`): 0 missing edges (16 at the open), unbacked
190 (187 at the open; task 4's three, below), unbacked-transitive 140, implied 3068, both
consistency lines OK. Gates: G1, G6, and the Lean and TeX diff empty.

**The round's gates** (each task's are in its commit message). Tasks 4-9 and 12-19 record G2 (a
whole-tree `lake build`, 0 warnings; bare `lake lint`) and G3 (`blueprint/lint.sh` green); tasks
4-9 and 19, which moved a pin or a pinned declaration's module, G4 (`verify.sh`, `checkdecls`
silent); tasks 13-19, G5 (`#print axioms` of the 21 `formalization.yaml` main results, `[propext,
Classical.choice, Quot.sound]` each, as at the open); tasks 6-9 and 12-19, G6 at 0 missing
edges. Task 3's message names no gate (two dead `have`s deleted, the statement unchanged); every
later whole-tree build covers its file.

**What the task lines do not carry** (the rest is in each task's commit). Unbacked 187 → 190 at task
4: the σ pin's move leaves `lem:pencil-d-condition-linear` unbacked at `lem:pencil-d-ear-data`,
`thm:pencil-d-open-ear-four` and `lem:pencil-d-planes-meet`, whose Lean reaches it only through
`gradeSigma`; not defects (an unbacked edge is a check), left as they are. Task 17's grep:
`recordsLinks_iff_forall_isLink`'s Lean mentions 60 → 21, the API's own 12 (the mirror 6,
`PanelHinge`'s alias and `link_tac` 4, `Operations` 2), records built link by link 8 (`Theorem55`
5, `CaseIII/` 2, `Application` 1) and one docstring (`Theorem55`). Task 18: `ofNormals_relabel`'s
caller keeps the name `hrec`, which `link_tac` finds by `assumption` (a `-` pattern fails there),
and `rigidityRows_ofNormals_congr_ends_swap` takes `hlinks`, `hlinks'` explicit (implicit ones are
not inferred from the goal; unpinned); its dropped `hagree` followed from them. Task 19 repointed
the deleted lemmas' docstring mentions (`Pinning`'s header, `panelRow`,
`span_panelRow_linking_eq_rigidityRows`, `finrank_span_rigidityRows_of_rigidOn`,
`RecordsLinks.of_forall`, `PanelGeneric`'s two); no total-form binder is left in the tree.

**Verified at the open** (2026-11-05, at `6d75d694`; a whole-tree `lake build` replays clean, 0
warnings, 0 cache failures):
- **The dependency audit** (`python3 scripts/blueprint-deps.py`, its consistency lines OK) finds
  **16 missing edges**: HOMES's four and twelve older ones (task 5's list), and 187 unbacked, among
  them HOMES's `def:join` one at `lem:decomposable-extensor-span-unique`. `blueprint/lint.sh` is
  green.
- **The cycle.** `lem:pencil-d-config-realization`'s pin `finrank_span_pencilConfigPointGrade_closedNbhd_le`
  (`Grade/Configuration.lean`) builds its bound through `gradeSigma` (`Grade/Carrier.lean`, HOMES
  task 13), the map `σ_v` that `lem:pencil-d-condition-linear` pins and states; that node's proof
  `\uses` the first. So the edge would close a cycle: `σ_v` needs a node of its own, or a home on a
  node both reach.
- **The `def:join` edge.** `span_range_eq_of_extensor_eq` (`Meet.lean`) is now one line through
  `span_range_eq_of_extensor_eq_grade`, which multiplies by `ι x` in the exterior algebra; the
  join of `def:join` *is* that product, so the chapter's argument is the Lean's, but the pin no
  longer reaches `join`. Its docstring still describes the `join_extensor` /
  `extensor_triple_eq_zero_iff` route, and `extensor_triple_eq_zero_iff` has no caller left (its
  only mention is that docstring; no pin).
- **FRICTION** (`grep -c '^### \[<tag>\]'`): open 8, mirror-candidate 8, process 2, blueprint 0,
  resolved 22 (HOMES's, for the sweep), idiom 248, mirrored 71, wontfix 11.
- **The four files** (lines; direct importers; modules importing them, HOMES's count):
  `Deficiency.lean` 3882 (3; 114), 24 `/-! ##` sections, `embedEdges` a `section`;
  `RigidityMatrix/Basic.lean` 1686 (4; 109), 11 sections; `Meet.lean` 1560 (1; 110), 21
  sections; `AlgebraicInduction/PanelLayer.lean` 1805 (3; 104), three sections at lines 53, 1163
  and 1359. File names in live text (Lean docstrings / live root docs): `Deficiency.lean` 15 /
  TACTICS-GOLF, TACTICS-QUIRKS, ROADMAP; `Meet.lean` 14 / the same three; `RigidityMatrix/Basic.lean`
  8 / TACTICS-QUIRKS; `PanelLayer.lean` 11 / the same three. No TeX names a Lean file.
- **`RecordsLinks`** is `PanelHingeFramework.RecordsLinks` (`AlgebraicInduction/PanelHinge.lean`,
  section `RecordsLinks`), with 14 lemmas there and `link_tac` after them; 206 mentions in 26 Lean
  files; no pin names it (two pins have `recordsLinks` in their names). Of its lemmas, only
  `recordsLinks_endsOf` and `RecordsLinks.update_splitOff` need `Induction/Operations.lean`
  (`Graph.endsOf`, `Graph.splitOff`); the rest need only mathlib's `Graph` (task 12: not
  `RecordsLinks.map`, whose `Graph.map` is the `Matroid` package's). `Pinning.lean` and
  `Molecule/Dictionary.lean`, which state link hypotheses, import neither `PanelHinge` nor
  `Operations` (`Operations.lean` is 2680 lines).
- **The link hypotheses.** 92 declarations take a binder in the form at links
  (`∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2`) or the pair form
  (`… → ends e = (u, v) ∨ ends e = (v, u)`), both equivalent to `RecordsLinks G ends`
  (`recordsLinks_iff_forall_isLink`, `RecordsLinks.of_pair`); 48 are pinned. By file group:
  `GenericityDevice` 6, `Pinning` 1, `Coupling` 2, `CaseI` 6, `CaseIII/` 14, `Dictionary` 4,
  `Pencil/MainComponent/` 26, `Pencil/Grade/` 33. None is a `formalization.yaml` main result.
  **Five** take the **total form** `∀ e, G.IsLink e (ends e).1 (ends e).2`, which is stronger (every
  label an edge): four in `GenericityDevice`, one in `Pinning` (the open wrote 24; recounted on
  2026-11-06, the same five at `6d75d694` and at `74290376`). Restating those weakens hypotheses:
  task 19, at the PI's word. The counts come from a signature scan; each task re-greps its files.
- **The dead `have`s:** `Graph.X0AttainsGrade.of_openEar_four` (`Grade/Short.lean:1101`) opens with
  `hax`, `hbx` (lines 1110–1111), used nowhere in it.

## Scope and standing rules

- **The hygiene rule.** No `formalization.yaml` main result's statement changes, and no blueprint
  statement's strength. The round's statement changes are tasks 13–18's: each replaces a link
  hypothesis, witness or conclusion by the equivalent `RecordsLinks G ends`, so a node pinning one
  keeps its strength; a node whose prose states the old form is reworded in the same commit (the
  *changed statement* gate, `CombinatorialRigidity/CLAUDE.md` *Forward-mode slices*). The one
  exception is task 19's, at the PI's word (*Decisions*): three total-form hypotheses weakened to
  `RecordsLinks` plus `hs` (the rows at edges of `G`), two lemmas deleted, a node repinned.
  The round's renames are task 12's `RecordsLinks` API (its 15 deprecated aliases removed after the
  close, *Decisions*). A
  split or move keeps every declaration's name, statement and proof. The deletions are
  `extensor_triple_eq_zero_iff` (task 4) and, at the PI's word, `induce_isLink_ends` (task 17), each
  dead and unpinned, and task 19's `exists_independent_panelRow_subfamily_of_rigidOn` (unpinned by
  its node's repin) and `span_panelRow_eq_rigidityRows` (its only caller gone). Anything else out
  of scope goes under *Candidates* or *Moved*.
- **Writes.** Lean in the files each task names (new files where a split or task 12 says, each a
  `module` with its line in `CombinatorialRigidity.lean`), and the docstrings that name a moved
  declaration's file; TeX in tasks 4–5 and where a restated node's prose needs it;
  `notes/FRICTION.md` and `FRICTION-archive.md`; `notes/PERFORMANCE.md` *(C)* item 3 as the splits
  land; the live root docs that name a split file; this log; at the close, the open's status
  surfaces. No `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` or `formalization.yaml`.
- **Evidence.** A claim about a declaration comes from its statement and body at HEAD, never its
  docstring or FRICTION entry (root `CLAUDE.md`). Each task re-`grep`s its names before editing.
- **The moved-name sweep.** For each moved declaration or split file, `grep -rn` its name over the
  tree: a live mention of the old file (a Lean docstring, a live root doc, an open FRICTION entry)
  is repointed in the same commit; a dated record (a closed note, a frozen design doc, a FRICTION
  *Where it bit* line) stays.
- **The gates**, each in the foreground with an explicit `timeout`, the commit under
  `if <gates>; then git commit …; fi`:
  - **Every task:** (G1) `python3 notes/check-phase-note.py` green.
  - **Every Lean task:** (G2) a whole-tree `lake build`, warning-clean (`grep -cE
    'warning:|error:'` 0, `grep -c 'failed to cache artifact'` 0), then bare `lake lint` green.
    (G3) `blueprint/lint.sh` green, check 9's total not above its baseline. (G4)
    `blueprint/verify.sh`, `checkdecls` silent, when a pinned declaration moves module or a pin
    changes.
  - **A task that changes a statement** (13–19): (G5) `#print axioms` of the 21
    `formalization.yaml` main results, by a scratch `lake lean` file: `[propext,
    Classical.choice, Quot.sound]` each, as at the open.
  - **Every task from 6 on:** (G6) `python3 scripts/blueprint-deps.py --summary`: 0 missing
    edges (tasks 4–5 bring it there), consistency lines OK.
  - **The close:** G1, G6, and the tallies its line names.
- **One task, one dispatch**, the rung beside each task (`.claude/commands/coordinate-phase.md`
  *Pick the rung*). A task that does not fit lands what closes and appends the rest as a new task
  right after it, with a one-line note. One `lake build` at a time
  (`CombinatorialRigidity/CLAUDE.md`).

## Lemma checklist (the round's task list)

One commit per task, in this order. Names are at `6d75d694`; re-`grep` before editing. **On
landing, a task's line is cut to at most three lines:** number, sha, what landed, the entries it
resolved.

- [x] **1. Open** (`381dcae1`; docs only).
- [x] **2. The friction log's archive sweep** (`0edd6e7e`; docs only). 22 `[resolved]` entries
  moved verbatim (425 lines, non-blank lines equal as multisets; `FRICTION.md` 6110 to 5685). One
  live pointer repointed (`PERFORMANCE.md`'s `mulTilde` mention); dated records stay.
- [x] **3. The dead `have`s** (`6f227b5e`; Lean, proof only). `hax`, `hbx` deleted from
  `X0AttainsGrade.of_openEar_four` (`Grade/Short.lean`); statement unchanged.
- [x] **4. HOMES's dependency-graph debt** (`a0b498a0`; TeX, `Meet.lean`, one docstring in
  `Grade/Carrier.lean`). `def:pencil-d-affine-heights-map` pins `gradeSigma`; the three edges with
  their prose; `extensor_triple_eq_zero_iff` deleted. G6: 12 missing (*Decisions*).
- [x] **5. The twelve older missing edges** (`ca348e9d`; TeX, one docstring in
  `HingeGeneric.lean`). Eight `\uses` edges with their prose; `dof_eq_zero_iff` moved to
  `cor:bodyhinge-generic-rigid`; two edges implied. G6: 0 missing (*Decisions*).
- [x] **6. Split `Deficiency.lean`** (`7dc78901`; Lean, a pure move). `Deficiency.lean` 851,
  `Deficiency/Cut.lean` 1207 (with the merged deficiency, the cut vertex), `Deficiency/Corank.lean`
  1371, `Deficiency/MinimalKDof.lean` 569; seven docstrings, three TACTICS-QUIRKS lines repointed.
- [x] **7. Split `RigidityMatrix/Basic.lean`** (`175bcb33`; Lean, a pure move). `Basic.lean` 819,
  `RigidityMatrix/ColumnOperation.lean` 915 (lines 817-1683: the column operation, the star-forest
  rows, the trivial motions and rank lemmas). Also repointed task 6's missed mention in
  `Induction/SparseDeficiency.lean` (`deficiencyMerged_le_deficiency`, `partitionDef_map`, now
  `Deficiency/Cut.lean`).
- [x] **8. Split `Meet.lean`** (`0f6d16a8`; Lean, a pure move). `Meet.lean` 672, new
  `MeetHyperplanes.lean` 908 (lines 672-1542: the `a ∨ v` section through the meet of two
  hyperplanes). Four live docstrings and two TACTICS-GOLF lines repointed.
- [x] **9. Split `AlgebraicInduction/PanelLayer.lean`** (`a2d7fe04`; Lean, a pure move).
  `PanelLayer.lean` 1162 (the panel support extensor), new `PanelHingeForms.lean` 223 (imports
  `PanelLayer`) and `DeficiencyBound.lean` 476 (imports `Deficiency`, `ColumnOperation`, not
  `PanelLayer`). 36 users import the part they use. The root lists no `PanelLayer`, so neither new
  file is added to it (reached through `Theorem55`). Also repointed task 8's `Motive.lean` mention
  of `finrank_toDualPerp_single_eq` (`Statement.lean`).
- [x] **10. `notes/PERFORMANCE.md` *(C)* item 3** (no-op, `a2d7fe04`): tasks 6-9 each recorded
  their sizes there, and task 9 closed the item.
- [x] **11. (reserved; unused)** for a split that did not fit its task (*One task, one dispatch*):
  each of tasks 6-9 fit, so no commit.
- [x] **12. `RecordsLinks` to `Graph`** (`651ecc60`; Lean). The def and 11 lemmas in the new mirror
  `Graph/RecordsLinks.lean`, three in `Operations.lean`; 15 deprecated aliases (removed
  after the close, *Decisions*); 33 callers renamed.
  Resolves FRICTION *`RecordsLinks` lives in `PanelHingeFramework`…* (now `[mirrored]`).
- [x] **13. Restate: upstream of Case III** (`03215eb1`; Lean). 22 binders in the five files;
  `PanelHingeFramework.recordsLinks_of_graph_eq` and its `link_base_tac` branch; callers converted
  (*Decisions*). FRICTION's open `RecordsLinks` entry updated; TACTICS-QUIRKS § 120 a case.
- [x] **14. Restate: Case III** (`d7f2d00c`; Lean). 23 binders in six files (*Decisions*), the
  three conversions task 13 left and the rest of `CaseIII/`'s gone; `RecordsLinks.eq_pair_or_swap`
  in the mirror, read by `CaseII`'s three pair sites too. FRICTION's `RecordsLinks` entry updated.
- [x] **15. Restate: `Pencil/MainComponent/`** (`c7449832`; Lean). 28 binders in 12 files
  (*Decisions*); task 13's six conversions gone, 15 left, all from `X0Attains`'s existential and one
  conclusion (*Candidates*). FRICTION's `RecordsLinks` entry updated.
- [x] **16. Restate: `Pencil/Grade/`** (`74290376`; Lean). 37 binders in 16 files; tasks 13 and
  15's conversions there gone; the tree-wide grep classified (in FRICTION's). FRICTION *The tree's
  link hypotheses are in the form at links…* stays open, narrowed to the PI's (*Candidates*).
- [x] **17. The defs' link witnesses, two conclusions, `induce_isLink_ends`** (`44215b92`; Lean).
  `X0Attains`, `X0AttainsGrade`, `LiftAttains`, `Bridge`'s and `Modelling`'s conclusions read
  `RecordsLinks`; 39 conversions gone (60 → 21); `induce_isLink_ends` deleted (*Decisions*).
- [x] **18. Case III's pair forms** (`60204c00`; Lean). `ofNormals_relabel`'s third conjunct and
  `fullLink_recording_of_splitOff_recording`'s conclusion read `RecordsLinks`;
  `rigidityRows_ofNormals_congr_ends_swap` drops `hagree`. Resolves FRICTION's link-form entry.
- [x] **19. The total form** (`ac1ab052`; recon, then Lean; the PI's word). The device trio takes
  `RecordsLinks` and `hs`; `lem:case-II-placement-old-rows-extract` pins `…_of_rigidOn_linking`;
  `…_of_rigidOn` and `span_panelRow_eq_rigidityRows` deleted (*Decisions*). G1-G6.
- [x] **20. The close** (this commit; docs only; opus). Each task's sha in its line; the round closed
  on its status surfaces and the queue row `done = true`; G6 0 missing; FRICTION's actionable
  entries 18 at the open, 16 at the close (*Current state*).

## Candidates for the PI

- None left: the PI took all four of task 16's into the round on 2026-11-06, as tasks 17-19
  (*Decisions*).

## Moved to a later round

- None.

## Blockers / open questions

- None.

## Hand-off / next phase

**Next concrete task:** PENCIL-NATURAL's open, with the PI (ROADMAP *Queued post-program phases*;
`notes/PencilNatural.md`): the PI queued it on 2026-11-07, after this close, ahead of ORIGAMI. Its
first task is a read-only recon. ARREARS is done: the round closed with its task 20, and the
queue's `42-arrears` row is `done = true`. PENCIL-NATURAL and ORIGAMI, the queue's next rows, are
attended, so each opens with the PI.

**What carries over:** nothing of the round's scope (*Candidates*, *Moved*: none). Left: task 18's
`[resolved]` FRICTION entry, for the next archive sweep; and, for the coordinator, the grooming of
`notes/dispatch-log.md` (`PHASE-BOUNDARIES.md` *When this commit closes a phase*).

## Decisions made during this round

- **The scope, at the PI's word** (the open, 2026-11-05). Asked whether the round should take the
  `RecordsLinks` entries HOMES left for the PI, the PI chose **"Move and restate"** (option text:
  "Do the move, and also restate the link hypotheses as `RecordsLinks G ends`. The round grows by
  several Lean tasks."). Asked whether to split only `PanelLayer.lean` or also the three other
  files HOMES grew past the cap, the PI chose **"All four"** ("Split all four files, one task each.
  Each split rebuilds most of Molecular/."). The twelve older missing edges are in scope by the
  open's choice, announced to the PI with the questions.
- **The candidates, at the PI's word** (2026-11-06, before the close). Asked about task 16's four
  *Candidates* one at a time, the PI chose, for the defs' witnesses and two conclusions, **"Take it
  (Recommended)"** (option text: "Est. 1–2 opus build tasks (tasks 15/16 each did ~30 sites in one
  dispatch), then the close."); Case III's three, **"Take it (Recommended)"** ("Est. 1 small task in
  CaseIII/. It removes the last pair forms outside binders."); `induce_isLink_ends`, **"Delete it
  (Recommended)"** ("A few lines. It rides along with group 1's task if you take that, or goes in its
  own tiny commit."); the total form, **"Take it, recon first"** ("Add a read-only recon to check
  whether the 5 proofs survive with only RecordsLinks, then a build task if they do. Est. 2 dispatches."). Tasks 17-19.
- **The total form, at the PI's word** (2026-11-06, after task 19's recon). Asked about the three
  lemmas false with only `RecordsLinks` (#1-#3, the device trio), the PI chose **"Adopt
  RecordsLinks + hs (Recommended)"** (option text: "One build task from the recon's compiled fix.
  The pinned Lean then matches the two nodes' statements. No main result uses any of the three.");
  about #4 (true with it) and #5 (false), **"Repin, delete #4 and #5 (Recommended)"** ("The node
  pins _linking in place of #4; #4 and #5 (both then uncalled, unpinned) are deleted, with their
  docstring mentions repointed. One task; moves a pin, so verify.sh and the dependency audit
  run."). Task 19.
- **Task 12's aliases removed, at the PI's word** (2026-11-06, after the close): "task 12 created
  15 @[deprecated (since := "2026-11-05")] aliases for the old RecordsLinks names which aren't
  needed (the commits haven't been pushed, so nothing should depend on the old names)". The
  aliases and their section leave `PanelHinge.lean`; the tree named none of them. The
  `notes/reconcile-formal/` witnesses that name the old forms are frozen Phase-41 records, already
  failing against the tree for other reasons, and stay as they are.
- **Task 19's shapes.** (a) The recon: with only `RecordsLinks`, #1-#3 and #5 are false
  (kernel-checked counterexamples at `k = 1` on a graph with no edges: a label off `E(G)` with ends
  `(0, 1)` and a nonzero hinge gives panel rows outside the row space); #4 holds, as `_linking` with
  `hne` at every label. (b) `hs : ∀ i ∈ s, i.1 ∈ E(G)`; #1's device runs on the rows masked to `0` off `E(G)`
  (FRICTION). (c) The node's statement block agrees with `_linking` (a nonzero hinge and rows at
  edges), so unchanged; its proof `\uses` `lem:independent-rows-of-rank`, the one edge the audit
  found missing, with its prose; three formalization notes reworded, no statement block changed.
- **The order** (the open). Docs and the dependency graph first, so G6 holds at 0 from task 6 on;
  the splits before task 12, so the restate's tasks edit the final files; the restate bottom-up
  by import order, a caller converting until its own task.
- **The queue row is attended** (the open): the driver stops before it, and the PI may flip it.
- **Tasks 4-5's shapes** (TeX, settled). `σ_v` has its own node, `def:pencil-d-affine-heights-map`
  (pin `gradeSigma`); the d = 3 contraction names its kernel step in a formalization note;
  `def:join` stays unbacked by design. `dof_eq_zero_iff` moved to its one consumer
  `cor:bodyhinge-generic-rigid`; eight `\uses` edges, each with a `\cref` at its step; two implied
  via `lem:reduction-step`.
- **Tasks 6-9's shapes** (splits, settled). Each seam at a section header, no name changing
  visibility (task 6 moved the merged-deficiency and cut-vertex sections into `Deficiency/Cut.lean`
  for its private `crossingEdges_induce`); the parts import in a chain; importers by use; live
  mentions repointed, dated records kept. Sizes are in the checklist.
- **Task 12's shapes.** (a) The def and 11 lemmas are a mirror,
  `Mathlib/Combinatorics/Graph/RecordsLinks.lean` (a new upstream file; mathlib's `Graph/Delete.lean`
  its one import); `mono` goes through mathlib's `IsLink.mono`, as `IsLink.of_le` is the `Matroid`
  package's. (b) `RecordsLinks.map` joins the two `Operations.lean` lemmas: the tree's `Graph.map` is
  the package's, and mathlib's `Graph/Maps.lean` cannot be imported beside it (both declare
  `Graph.map_map`). (c) The aliases were in `PanelHinge.lean` (removed after the close); every
  mention is `Graph.`-qualified (in `PanelHingeFramework` a bare name resolved to the alias).
  (d) The root lists the mirror, beside `Graph/Delete.lean`'s.
- **Task 13's shapes.** (a) 22 binders (`Pinning` 1, `Dictionary` 4, `GenericityDevice` 6, `Coupling`
  2, `CaseI` 9), each `(hends : Graph.RecordsLinks G ends)`; `Pinning`, `Dictionary` import the
  mirror. (b) Local `have`s feeding them restated in place: in these files and in those of no task
  (`Theorem55`, `CaseII`, `HingeGeneric`, `PanelGeneric`, `Steer`, `Theorem56`, `Application`); a
  later task's file converts by `.mpr`. (c) A restated `have` is stated at the graph of the
  `ofNormals` it serves, not an `F.graph` that unfolds to it (TACTICS-QUIRKS § 120). (d) CaseI's three
  `hQrec` `have`s go: the new branch finds the field through `hQg`. (e) No pinned node's prose
  states the old form (8 nodes read), so no TeX.
- **Task 14's shapes.** (a) 23 binders, pair form and form at links: 20 in signatures (`Relabel/Basic`
  2, `Relabel/Chain` 5, `Arms` 3, `Relabel/Arm` 2, `Relabel/ChainColumn` 3, `Realization` 5) and the
  selector's inside the three `h622lb`; every caller is in `CaseIII/`. (b) `RecordsLinks.eq_pair_or_swap`
  (the mirror) gives the pair form back, so `rcases hrec f x y h` becomes `rcases hrec.eq_pair_or_swap
  h` and nothing else moves; `CaseII`'s three pair sites read it too. (c) A local repeating a record in
  scope goes (`hends_q₀`, `hends_G`, `hends_Gv₁` ×2, `hrec'`, `hends_Gab`, `hrecGab`); the rest are
  built by `mono`, `of_isLink_imp`, `congr`, or link by link. (d) Conclusions stay (*Candidates*).
  (e) No TeX: five pinned nodes read, each in the record's own words.
- **Task 15's shapes.** (a) 28 binders: 27 in 26 signatures (`Carrier` 2, `Configuration` 5, `Cut`
  3, `Flat` 6, `Ear` 4, `ContractCurve` 2, `Bridge`, `EarGen`, `Short`, `SplitOff`, `GenericBase`)
  and the hypothesis inside `exists_oneEar_base`'s conclusion (`Orbit`; a binder the user supplies,
  like task 14's `h622lb`). (b) Locals from `G.endsOf` read `Graph.recordsLinks_endsOf`; the rest are
  built by `induce`, `mono`, `map`, `update_splitOff`, `congr`; seven `hendsG`, one `hendsI` and
  `SplitOff`'s `hends2` (it repeated the statement's `hlinks`) go. (c) `X0Attains`'s existential and
  one conclusion stay at links (task 14 (d)), converting where used, until task 17; `Cut`'s two `hcongr` keep
  their binder, fed from both. (d) `Pencil/Grade/` converts 13. (e) No TeX: 18 pinned nodes read.
- **Task 16's shapes.** (a) 37 binders in 35 signatures (`Collineation`, `Carrier` 2, `Configuration`
  2, `Contract`, `Witness` 2, `ZeroHeights`, `Cut` 2, `Flat` 3, `Chain`, `EarData`, `Short` 3, `Lift`
  3, `LiftWitness` 7, `LiftSmall` 2, `LiftCases` 5, `LiftCutEdge`), and `LiftSmall`'s local `side`'s
  two; every caller is in `Grade/`. (b) Locals as task 15 (b), `GluedEnds`' too; five `hendsG`, three
  `hendsI`, `hr`, `hr'`, `hrecH` go, and `CaseII`'s two locals at links repeating a record in scope.
  (c) `LiftAttains`'s existential stays at links, as `X0AttainsGrade`'s, with `LiftSmall`'s `hendsG`
  that feeds only it; a witness of two uses converts once, by `replace`. (d) `induce_isLink_ends`
  keeps its conclusion; callers read `.induce` (deleted at task 17). (e) No TeX: 14 pinned nodes read.
- **Task 17's shapes.** (a) The existentials of `X0Attains`, `X0AttainsGrade`, `LiftAttains`, the
  existential in `exists_mvPolynomial_le_finrank_span_rigidityRows_pencilPicturePoint`'s conclusion
  and `exists_molecular_rankHypothesis_generalPosition`'s third conjunct read `Graph.RecordsLinks G
  ends`. (b) Task 16's 39 conversions all went (re-checked per site; none stays); so did `Cut`'s two
  `hcongr` binders at links and `Modelling`'s `hQends` (`recordsLinks_of_graph_eq hQg`), and
  `LiftSmall`'s `hendsG` is built on `E(G)` (FRICTION). (c) `induce_isLink_ends` deleted; the repo
  grep finds it only in this log. (d) No TeX: the five pinned nodes state no selector condition.
