# ARREARS — what HOMES left: the dependency graph, four splits and `RecordsLinks` (work log)

**Status:** open (2026-11-05, at the PI's word: "Let's take care of the items that were deferred by
the last phase"). A cleanup round after HOMES and ahead of ORIGAMI. It takes what HOMES's close
carried over (`notes/Phase42-homes.md` *Moved to a later round*, *Candidates for the PI*,
*Hand-off*), with the scope the PI chose at the open (*Decisions*): the blueprint's dependency-graph
debt, the friction log's archive sweep, a dead pair of `have`s, the splits of the four molecular
files past the ~1500-line tripwire, and `RecordsLinks` moved to `Graph` with its link hypotheses
restated. Seventeen tasks; no main result's statement changes.
**Next concrete task:** task 5, the twelve older missing edges (*Lemma checklist*).
Round manual: `CLEANUP.md`.

## Autopilot: for the PI

ARREARS's row of `.claude/autopilot/queue.toml` is attended (the open's choice), so the driver
stops before it. **The one stop is the PI's:** a task that would change a main result's statement,
or a blueprint statement's strength, or rename a public declaration other than the `RecordsLinks`
API, does not land that change: it writes a `NEEDS_PI` entry here, newest first, and the loop
stops; the PI answers in an entry that starts `**PI, <date>:**`.

- None yet.

## Current state

**Tasks 1-4 landed.** Task 1 (`381dcae1`): the open. Task 2 (`0edd6e7e`): the friction log's
archive sweep, 22 `[resolved]` entries to `FRICTION-archive.md`; FRICTION's counts now open 8,
mirror-candidate 8, process 2, blueprint 0, resolved 0. Task 3 (`6f227b5e`): `hax`, `hbx` deleted
from `X0AttainsGrade.of_openEar_four`. Task 4 (this commit): HOMES's four missing edges closed
(*Decisions*), `extensor_triple_eq_zero_iff` deleted. Gates: G1, G2, G3 (check 9 at 0, the
docstring-label report unchanged), G4; G6 missing total **12** (the older twelve, task 5), 802
nodes, consistency OK. Unbacked 187 → 190: the σ pin's move leaves `lem:pencil-d-condition-linear`
unbacked at `lem:pencil-d-ear-data`, `thm:pencil-d-open-ear-four` and `lem:pencil-d-planes-meet`,
whose Lean reaches it only through `gradeSigma` (the new node, now implied through the lemma's
statement); not defects (an unbacked edge is a check), left as they are.

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
  (`Graph.endsOf`, `Graph.splitOff`); the rest need only mathlib's `Graph`. `Pinning.lean` and
  `Molecule/Dictionary.lean`, which state link hypotheses, import neither `PanelHinge` nor
  `Operations` (`Operations.lean` is 2680 lines).
- **The link hypotheses.** 92 declarations take a binder in the form at links
  (`∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2`) or the pair form
  (`… → ends e = (u, v) ∨ ends e = (v, u)`), both equivalent to `RecordsLinks G ends`
  (`recordsLinks_iff_forall_isLink`, `RecordsLinks.of_pair`); 48 are pinned. By file group:
  `GenericityDevice` 6, `Pinning` 1, `Coupling` 2, `CaseI` 6, `CaseIII/` 14, `Dictionary` 4,
  `Pencil/MainComponent/` 26, `Pencil/Grade/` 33. None is a `formalization.yaml` main result. Another
  24 take the **total form** `∀ e, G.IsLink e (ends e).1 (ends e).2`, which is stronger (every label
  an edge): restating those would weaken hypotheses, out of scope (*Candidates for the PI*). The
  counts come from a signature scan; each task re-greps its files.
- **The dead `have`s:** `Graph.X0AttainsGrade.of_openEar_four` (`Grade/Short.lean:1101`) opens with
  `hax`, `hbx` (lines 1110–1111), used nowhere in it.

## Scope and standing rules

- **The hygiene rule.** No `formalization.yaml` main result's statement changes, and no blueprint
  statement's strength. The round's statement changes are tasks 13–16's: each replaces a link
  hypothesis by the equivalent `RecordsLinks G ends`, so a node pinning one keeps its strength; a
  node whose prose states the old form is reworded in the same commit (the *changed statement*
  gate, `CombinatorialRigidity/CLAUDE.md` *Forward-mode slices*). The round's renames are task 12's
  `RecordsLinks` API, each old name kept as a deprecated alias. A split or move keeps every
  declaration's name, statement and proof. The one deletion is `extensor_triple_eq_zero_iff`
  (task 4; dead, unpinned). Anything else out of scope goes under *Candidates* or *Moved*.
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
  - **A task that changes a statement** (13–16): (G5) `#print axioms` of the 21
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
- [x] **4. HOMES's dependency-graph debt** (this commit; TeX, `Meet.lean`, one docstring in
  `Grade/Carrier.lean`). `def:pencil-d-affine-heights-map` pins `gradeSigma`; the three edges with
  their prose; `extensor_triple_eq_zero_iff` deleted. G6: 12 missing (*Decisions*).
- [ ] **5. The twelve older missing edges** (TeX; opus). Each judged on its node: an edge where the
  dependency is real and in order, a moved pin where a node pins a helper its prose does not state.
  `def:dof-generic`'s proof (pin `dof_eq_zero_iff`) → `lem:case-II-placement-old-rows-extract`,
  `lem:isInfRigidOn-of-relative-count` (a definition reaching two later lemmas: a pin to move, most
  likely); `lem:splitoff-edge-substitution`, reached through `Graph.removeVertex_le` (or
  `…_le_splitOff_of_notMem_removeVertex`) by `lem:reverse-pendant-insert`,
  `lem:splitoff-deficiency-reuse`, `lem:dof-tracking`, `lem:reduction-step`,
  `thm:minimal-kdof-reduction`, `lem:chain-data-extract`; `lem:splitoff-deficiency-reuse` →
  `lem:splitoff-deficiency`; `def:panel-nonparallel`'s statement → `def:panel-general-position`;
  `thm:theorem-55-6-rows`'s proof → `def:framework-with-graph`; `lem:generic-hinge-points-max-rank`'s
  proof → `lem:independent-rows-of-rank`. G6: 0 missing.
- [ ] **6. Split `Deficiency.lean`** (Lean; opus). Along its sections into about four files under
  ~1500 lines: the file keeps its module name and its first sections (the deficiency, `k`-dof,
  rigid subgraphs, the small `0`-dof graphs, minimality, the circuit, to line 868), and the rest go
  to new files under `Molecular/Deficiency/` (suggested seams: the two-edge-connectivity and cut
  sections, 869–1780; tight partitions to tree packing, 1781–3106; the two-vertex trichotomy to the
  cut vertex, 3107–3881), each importing only what it uses, so the parts form a DAG where the
  sections allow. Importers import the parts they use. A pure move.
- [ ] **7. Split `RigidityMatrix/Basic.lean`** (Lean; sonnet). At the column-operation section
  (line 817): the rest to a new `RigidityMatrix/` file. A pure move.
- [ ] **8. Split `Meet.lean`** (Lean; sonnet). At a seam near line 689 (the `a ∨ v` sections on),
  the rest to a new file. A pure move.
- [ ] **9. Split `AlgebraicInduction/PanelLayer.lean`** (Lean; sonnet). Along its three sections:
  the panel support extensor stays (to line 1162); the hinge forms (1163–1358) and the deficiency
  bound (1359–1805) to new files. A pure move. HOMES *Moved to a later round*.
- [ ] **10. `notes/PERFORMANCE.md` *(C)* item 3** (docs only; sonnet), if tasks 6–9 left it stale:
  the four files' new sizes; the item closes. (Each split task may do this in its own commit, in
  which case this task is a no-op and is ticked so.)
- [ ] **11. (reserved)** for a split that does not fit its task (*One task, one dispatch*).
- [ ] **12. `RecordsLinks` to `Graph`** (Lean; opus). `Graph.RecordsLinks` and its lemmas in the
  `Graph` namespace, in a new low-level file importing only mathlib's `Graph` files it needs, so
  `Pinning.lean` and `Dictionary.lean` can import it; `recordsLinks_endsOf` and `update_splitOff`
  beside `endsOf` and `splitOff` in `Operations.lean`. Every old name a
  `@[deprecated (since := "2026-11-05")] alias`. The 26 files' mentions and `link_tac`'s rules use
  the new names. Resolves FRICTION *`RecordsLinks` lives in `PanelHingeFramework`…*.
- [ ] **13. Restate the link hypotheses: upstream of Case III** (Lean; opus). `Pinning`,
  `Dictionary`, `GenericityDevice`, `Coupling`, `CaseI` (19 binders): each to `RecordsLinks G ends`,
  proofs through `.isLink` / `.eq_or_swap`; a downstream caller not yet restated converts with
  `recordsLinks_iff_forall_isLink.mpr` until its own task. Also
  `PanelHingeFramework.recordsLinks_of_graph_eq (hQg : Q.graph = G) : RecordsLinks G Q.ends` and a
  `link_base_tac` branch applying it with `hQg` in scope (FRICTION's proposed fix).
- [ ] **14. Restate: Case III** (Lean; opus). `CaseIII/` (14 binders), and the conversions tasks
  13's callers left there.
- [ ] **15. Restate: `Pencil/MainComponent/`** (Lean; opus). 26 binders in 12 files, and the
  conversions left there.
- [ ] **16. Restate: `Pencil/Grade/`** (Lean; opus). 33 binders in 16 files, and the last
  conversions (grep `recordsLinks_iff_forall_isLink` over the tree: what remains is the API's own
  and the total form's). Resolves FRICTION *The tree's link hypotheses are in the form at links…*.
- [ ] **17. The close** (docs only; opus). Each task's sha; the status surfaces; the queue row
  `done = true`; G6; FRICTION's counts.

## Candidates for the PI

- **The total-form link hypotheses** (24 declarations, `∀ e, G.IsLink e (ends e).1 (ends e).2`):
  stronger than `RecordsLinks G ends`, so restating them generalizes the declarations, beyond the
  equivalent restatement the PI chose. Recorded at the open.

## Moved to a later round

- None yet.

## Blockers / open questions

- None.

## Hand-off / next phase

**Next concrete task:** task 5, the twelve older missing edges (*Lemma checklist*; G6 lists them,
`python3 scripts/blueprint-deps.py --chapter <name>`). After the close: ORIGAMI's open, with the
PI (ROADMAP *Queued post-program phases*).

## Decisions made during this round

- **The scope, at the PI's word** (the open, 2026-11-05). Asked whether the round should take the
  `RecordsLinks` entries HOMES left for the PI, the PI chose **"Move and restate"** (option text:
  "Do the move, and also restate the link hypotheses as `RecordsLinks G ends`. The round grows by
  several Lean tasks."). Asked whether to split only `PanelLayer.lean` or also the three other
  files HOMES grew past the cap, the PI chose **"All four"** ("Split all four files, one task each.
  Each split rebuilds most of Molecular/."). The twelve older missing edges are in scope by the
  open's choice, announced to the PI with the questions.
- **The order** (the open). Docs and the dependency graph first, so G6 holds at 0 from task 6 on;
  the splits before task 12, so the restate's tasks edit the final files; the restate bottom-up
  by import order, a caller converting until its own task.
- **The queue row is attended** (the open): the driver stops before it, and the PI may flip it.
- **Task 4's shapes.** (a) `σ_v` has its own node, `def:pencil-d-affine-heights-map`, before
  `lem:pencil-d-config-realization`: not a home on `def:pencil-d-configuration` (four pins already;
  σ is no part of a configuration). Pins by statement: `gradeSigma` (the map) moves there, its
  docstring label with it; `gradeSigmaPerp` (the `n^i`), `dotPerp_range_gradeSigma` stay on
  `lem:pencil-d-condition-linear`, whose statement states both. (b) The d = 3 contraction names its
  kernel step in a formalization note (the `lem:deficiency-core-bound` precedent); the other two
  cite the join identity of `lem:pencil-d-embedding-join`'s proof, its general-map pin
  (`exteriorPower_map_normalsJoin`), forward at the first. (c) `def:join` stays unbacked by design.
