# RECONCILE round 2/3 — `reconcile-statements`, every false statement and KT's route explained (work log)

**Status:** in progress (opened 2026-10-15). Round 2 of **RECONCILE**'s three autopilot rounds; the
plan and the PI's decisions are `notes/Reconcile.md`, and `.claude/autopilot/queue.toml` is the
authority for which rounds are done. The round fixes the blueprint statements the plan assigns it
(S4–S10 but S3, S14, S15, S20, S21, S26–S29, S35, S36, S38–S42), makes G1's three pin changes and
G2's merges of true duplicates, and gives each group of nodes where the formal proof leaves Katoh
and Tanigawa's route a framing remark, under the expected-diff and honesty gates; the Lean is not
edited. The open (task 1, docs only) reproduced round 1's close values and sliced the round into
21 one-commit tasks; S3, S16, S18, S19, S22–S25 and S31 wait for the phase. Tasks 1–12 are done
(the open; the false statements S6–S10; S4 and S5; S7's repin; Case I's S14, S15 and S21; Case
III's three counts, S20; S26, S27 and S35; S29; S36's and the rescaling's pins, `F-259` and
`F-260`; S38 and S39, stated generally; S40–S42, the hypotheses the pins do not take; G1's first
two pin changes). **Next concrete task:** task 13, G1's third pin change (*Lemma checklist*).
Three missing edges that would be forward wait for the coordinator (*Blockers*); `F-255`'s and
`F-257`'s other cures are tasks 15 and 18's. Round manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop (`notes/Reconcile.md` §4): the queue runs the three rounds unattended and stops
before `RECONCILE-FORMAL`. An unplanned `NEEDS_PI` entry goes here, newest first, and the PI
answers in an entry that starts `**PI, <date>:**`. No entries yet.

## Current state

**Tasks 1–12 are done**; task 12, G1's first two pin changes, is this commit (`rigidity-matrix.tex`,
`main-component.tex`, `case-iii.tex`, `case-i.tex`, `generic-lift.tex`). Nothing is mid-stream; task
13 is next. Open for the coordinator: `F-257`'s first edge, which task 12's move did not cure, and
`F-261` and `F-262`, two missing edges that task 12 exposed; each would be forward (*Blockers*).
Task 12's gates: `lint.sh` green; `verify.sh` green, `checkdecls` silent, the same 9 `WARNING:`
lines; **`1527 edges 4b5c8b4912b3ffcd`**, **`0105d5fb12c84423`**; the dump's diff from
`dump-t11.txt` exactly the line's prediction, kept as `scratch/reconcile-statements/dump-t12.txt`;
`--summary` exits 0, both checks OK, as predicted (690 nodes pinned, 1011 pins (994 distinct), 6
missing edges, 171 dead pins, 134 edges with no Lean basis, 85 transitive, 14 nodes with 4+ pins);
the forward screen `rigidity-matrix 2/1` and `case-i 13/6`, the rest the open's lines; `print.log`
rebuilt by latexmk, 0 `LaTeX Warning` lines, 31 overfull boxes; `check-phase-note.py` green; the
no-Lean-edit diff from `1cbdbff5` empty. The declarations round 2 unpins, for the close's list
(tasks 8–11 unpin none): task 4's `rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`
(no caller), task 5's `exists_good_realization` and `exists_good_realization_const` (dead, `F-152`),
task 7's `linearIndependent_sum_augment_candidateRow`, `linearIndependent_sum_p2_candidateRow` and
`linearIndependent_sum_p3_candidateRow` (dead), and task 12's
`add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath` (live: the bridge theorem's and
the path lemma's pins call it, and its docstring names no node). Their docstrings are `F-254`'s,
`F-256`'s and `F-258`'s, and the moved pin's `F-263`'s, round 3.

**Verified at the open** (2026-10-15, at `1cbdbff5`, round 1's close tree, whose Lean is
`f39e35e6`'s):
- Whole-project `lake build` green: "Build completed successfully (2996 jobs)", 0 `warning:` and 0
  `error:` lines. **The no-Lean-edit base is `1cbdbff5`**: the close checks that `git diff --stat
  1cbdbff5.. -- CombinatorialRigidity/ lakefile.toml lake-manifest.json lean-toolchain` is empty
  (from `f39e35e6`, the program's base, it is empty too).
- Round 1's close values, reproduced exactly: `lint.sh` green; `verify.sh` green, `checkdecls`
  silent, **9** `WARNING:` lines; the invariance check **`1501 edges 11033da1dbaa0fae`** and
  **`8cdc1b9723e22064`** (1 010 pins, 1 000 distinct); `print.log` **0** `LaTeX Warning` lines and
  31 overfull boxes (not gated); the dump (`python3 scripts/blueprint-deps.py --dump`, after
  `verify.sh`) 3 588 lines, **`2e4cbc2acd13d193`**, byte-identical to round 1's close, kept as
  `scratch/reconcile-statements/dump-1cbdbff5.txt` (gitignored); `--summary` exits 0, both
  consistency checks OK, the same bytes as round 1's open: 692 nodes (689 pinned; unfilled are
  `def:blockingWitness`, `def:dof-generic` and `lem:forest-surgery-unsplit`), 0 missing edges, 177
  dead pins.
- **The forward-`\uses` screen** (gate 4): 33 edges at 17 nodes to a later file, 4 at 4 within a
  file, the same lines as round 5's close (`scratch/reconcile-statements/forward-open.txt`).
- **The axioms check** (`notes/Reconcile.md` §2): the harness
  `scratch/reconcile-statements/Axioms.lean`, generated by gate 8's command, is `cmp`-identical to
  round 1's open and close harnesses. Run with `lake lean`, all 19 main results give `[propext,
  Classical.choice, Quot.sound]`, and the output equals round 1's open byte for byte, and its close
  net of the harness's path (its one warning is its own long line 31).
- **The ledger** (`notes/Prose-findings.md`): 252 entries, 89 `done`, 16 `left`, 147 `reported`;
  the next ID is `F-253`. The open made no entry.

## Scope and standing rules

From `notes/Reconcile.md` §1–§3, restated as far as a builder needs them.

- **Surface.** The blueprint chapters' statements, titles, `\lean{…}` pins, `\uses`, `\leanok` and
  node environments that a task's line names, with the notes, remarks and `\cref`s its fix needs
  (`retrospective.tex` is out); `notes/BlueprintExposition.md`'s pointers to a node that a task
  merges, adds or restates; `blueprint/CLAUDE.md`'s honesty-gate example only as task 14 says; the
  ledger's dispositions; this log, ROADMAP's row and bullet, and `notes/Reconcile.md`'s
  **Status** and §3. `formalization.yaml`, README and the home page change only where a fix reaches
  a sentence there (none is expected), and no `main_results` entry's `declaration:` or `file:`.
- **No Lean edits** (§2 *Gates*): `CombinatorialRigidity/`, `lakefile.toml`, `lake-manifest.json`
  and `lean-toolchain` stay untouched. A fix that needs a new or changed declaration (kind E, Lean+,
  Lean±) waits for the phase, or round 3 for a docstring: it goes under *Moved to a later round*,
  mirrored in the same commit; it is not a stop.
- **The hygiene rule, lifted exactly for the task list's items** (§1's table, §3 *Round 2*). A
  statement change outside them is recorded as a ledger `S` entry, with its line under *Candidates
  for the PI*, and not acted on; it is not a stop. The 19 main results' statements and rows change
  only in the phase; a main result's node keeps its pins (task 11's S41 changes two such nodes'
  hypotheses, not their pins). The PI's choices bind: no node of KT's route is retired or merged
  away (G2's true duplicates aside), and S1's and S2's scope stays round 1's text.
- **Evidence** (§2): claims about the Lean come from declarations' statements and bodies, never
  docstrings, and `scripts/blueprint-deps.py --label` or `--chapter` for what a pin reaches; a
  surprise gets a `lake lean` witness in `scratch/reconcile-statements/` before it is written;
  citations meet `CLAUDE.md` *Referencing prior work* against `.refs/`.
- **The ledger** stays each finding's home. A task names the IDs it acts on. An entry the round
  finishes becomes `done (task N)`; one it acts on in part keeps `reported` and gains `; round 2:
  <what> (task N)`; the close writes each task's sha. New entries take IDs from `F-253`, under the
  ledger's format and categories, with `open (notes/Reconcile-statements-cleanup.md, task N)` until
  a task sets their disposition; one line here per new entry.
- **Gates for every commit**, each in the foreground with an explicit `timeout`:
  1. `blueprint/lint.sh` green.
  2. `blueprint/verify.sh` green: `checkdecls` silent, 9 `WARNING:` lines.
  3. **The expected-diff gate** (PROSE round 5's, `notes/Prose-graph-cleanup.md` *Scope*). (a) The
     parent's dump, `python3 scripts/blueprint-deps.py --dump >
     scratch/reconcile-statements/dump-<parent>.txt` after `verify.sh` (the previous task's
     after-dump serves; task 2's is the open's `dump-1cbdbff5.txt`, as the open changes no TeX).
     (b) Before editing, the expected diff in the task's checklist line: nodes added and removed;
     `\uses` added, moved and removed; pins moved, added and removed; `\leanok` changed; whether
     the `lean_decls` hash changes (a move keeps it; an added or removed pin, a duplicate included,
     changes it). (c) After: `verify.sh`, the dump again, and `diff`: exactly the listed changes,
     with the drawn edges they imply; the `## uses:` section shows every `\uses` change. (d)
     `--summary` exits 0, both consistency checks OK. A task that lists no change has a
     byte-identical dump.
  4. **The forward-`\uses` screen** (the same *Scope*; its block is
     `scratch/reconcile-statements/forward-screen.py`), on a task that adds a node or a `\uses`: no
     new forward edge, against the open's 33/17 and 4/4.
  5. `blueprint/print/print.log` has 0 `LaTeX Warning` lines; a TeX task checks that latexmk
     rebuilt (the log's date).
  6. `python3 notes/check-phase-note.py` green.
  7. The no-Lean-edit `git diff --stat` above is empty.
  8. A task that edits `formalization.yaml` regenerates the harness and `cmp`s it with the open's
     (identical):
     ```sh
     ruby -ryaml -e 'r=YAML.load_file("formalization.yaml")["status"]["main_results"]; i=r.map{|x| x["file"].sub(/\.lean$/,"").tr("/",".")}.uniq.sort; print i.map{|m| "import #{m}\n"}.join+"\n"+r.map{|x| "#print axioms #{x["declaration"]}\n"}.join' > scratch/reconcile-statements/Axioms-tN.lean
     ```
  Every commit also updates this log: its checklist line, *Current state* and *Hand-off*.
- **The honesty gate** (PROSE round 5's, the same *Scope*), for every node a task restates, repins,
  fills, adds or merges: (i) every pin resolves and the statement claims what its pins prove, each
  clause beside the pin that proves it; (ii) `blueprint/CLAUDE.md`'s honesty gate: each
  non-ambient hypothesis of each pin is discharged in its body or is the conclusion of a node it
  `\uses`, read from the pin's statement, and its `--label` report shows no missing statement edge;
  (iii) a definition node passes the definition-faithfulness gate; (iv) a node that gives up a pin
  or a clause still passes (i)–(ii) for what it keeps. A fix that fails is not made: the entry stays
  `reported`, with the reason in the task's line, and a new finding gets an `S` entry.
- **Retargeting by the reach report** (the same *Scope*). After a pin moves, is added or removed,
  or a node is merged away, every node that `\uses` the node is re-read with `--label`, and every
  `\cref` of its label (`grep` over `blueprint/src/` and `notes/BlueprintExposition.md`) is read
  and pointed at the node whose claim its sentence cites. A task's own fixes add the edges their new
  pins need (not implied, closing no cycle) and remove an edge only when neither the statement, the
  proof prose nor the pins use it, with each removal's reason in the commit message.
- **KT's route, kept and explained** (§3; M3, G3, G4). No node is retired or merged away. Each
  off-route group gets one framing remark: KT's step, why the formal proof leaves it, and what
  replaces it, with `\cref`s to the live nodes. Each node in it states what is true, and a node that
  restates a general form says so. The crux carve-out holds: a node with a *done* entry in
  `notes/BlueprintExposition.md` keeps its proof's depth.
- **Rungs** (§2): Opus for tasks 2–20 (statements, pins and KT's route), a fresh agent per task;
  Sonnet may take the close.

## Lemma checklist (the round's task list)

One commit per task, in this order; a group's statement fixes come before its framing remark. Each
line names the ledger IDs and report items it acts on, its surfaces with lines and labels as at the
open (re-`grep` before editing), and *Expected*: the open's estimate of the gate's diff, which the
task makes exact before editing. Every task is at Opus but the close.

- [x] **1. Open** (`1468bc31`; docs only): this log, the baselines, the task list.
- [x] **2. The four false statements: S6, S7's restatement, S8, S9** (`3456d6a7`; `F-049`, `F-154`,
  `F-060`; `F-117` and `F-149` in part). S6: `lem:rank-rotation-semicont`, retitled "Smaller hinge
  spans give fewer infinitesimal motions", states its pins' inclusion, the rank bound by the remark
  after `def:rigidity-matrix`; KT Lemma 5.2 (p. 669) is stated before
  `lem:generic-realization-of-rigid`, beside JJ 2010 Lemma 7.1, and the label's six `\cref`s cite
  what they use. S7: `lem:genericity-device` on the open set $U$ of normals with nondegenerate
  hinges. S8: `lem:case-III-nested-rank-lower` gains "simple". S9:
  `lem:case-III-claim612-extensor-span` for the omit-two extensors $E_{ij}$. The dump
  byte-identical. New: `F-253`.
- [x] **3. S10: `lem:forest-surgery-unsplit` restated in its pin's form and filled** (`43c5c8d7`;
  `F-234`; `F-091`, `F-008` in part). Pinned on `Graph.splitOff_indep_extend_of_fiber_lt`, also
  `lem:edge-splitting`'s, and stated at its case $h' = 0$, KT's use at p. 662 ("Edge-splitting and
  independent sets avoiding $ab$"), with the forest construction as its proof; moved after
  `lem:edge-splitting` (*Node order*) to keep the screen, its `\uses` per the pin's reach (1502
  edges). `F-234` done.
- [x] **4. The two kind-A statements: S4, S5** (`ab3a0d45`; `F-145`, `F-169`). S4: `lem:case-II`
  drops its vacuous second assertion with its pin
  `rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions` and keeps the first in its Case II
  setting, its `\uses` now statement `def:rigidity-matrix` alone (1500 edges). S5:
  `lem:case-III-chain-discriminator` states its pin's conclusion (KT eqs. (6.46), (6.52), read at
  p. 693), its three new statement edges implied. Both done; new: `F-254`.
- [x] **5. S7's repin** (`1b46edc6`; `F-117`, `F-149`; `F-152` in part): `lem:genericity-device` on
  `exists_rankPolynomial_of_le_finrank_linking`, `lem:relative-device-count`'s edge moved to
  `def:panel-hinge-framework`; the body's forward edge recorded. New: `F-255`, `F-256`.
- [x] **6. Case I's S14, S15, S21** (`c2cfcd08`; `F-141`, `F-115`, `F-138`): each node at its pin's
  hypotheses (`lem:cycle-realization` at $3 \le m \le d + 1$, `lem:claim-6-4` at its pin's point,
  one proof edge removed). All done; no new entry.
- [x] **7. S20** (`9e98aaba`; `F-158`, `F-165`; `F-159`, `F-167` in part): Case III's three counts
  on `case_III_rank_certification` at the arms' roles; three forward proof edges recorded. New:
  `F-257`, `F-258`.
- [x] **8. S26, S27, S35** (`41e7a771`; `F-188`, `F-217`, `F-187`): each node at what its pins
  prove, S26 also pinning its rank form. All done; no new entry.
- [x] **9. S29, S36** (`6e56a1d1`; `F-180`, `F-184`): `lem:polarity-join` over a field $K$; S36's
  pin and the rescaling's went to task 9.1. `F-180` done; new: `F-259`, `F-260`.
- [x] **9.1. The pins of `F-259` and `F-260`** (`64a531db`; the coordinator):
  `rankHypothesis_zero_iff` joins `lem:trivial-motions-rank-bound`, the rescaling's two pins
  `lem:panel-hinge-dual-molecular`'s (2); the dump's four predicted lines. `F-184`, `F-259`, `F-260`
  done.
- [x] **10. S38, S39: special cases stated generally** (`0b8a78e0`; `F-239`, `F-079`; `F-191` in
  part): `lem:case-II-placement-old-rows-extract` and `-block-independent` at their pins'
  generality, `lem:rk-within-parts` for every $Y$ within parts, `lem:partitionDef-merge` for any
  nonempty $Q$; three unbacked statement edges gone, `def:screw-space` added (1499 edges); the
  `\cref`s that read a special case retargeted. `F-079`, `F-239` done; `F-191` in part.
- [x] **11. S40, S41, S42: hypotheses the pins do not take** (`40e1f4c8`; `F-034`, `F-036`,
  `F-058`, `F-015`, `F-026`, `F-027`, `F-028`, `F-031`, `F-037`, `F-042`, `F-046`): the pebble
  game's invariants and soundness without $\ell < 2k$ (but soundness's "In particular"), both Tay
  theorems and `intro.tex`'s summary at every $d$, fifteen nodes' finiteness as their pins take it;
  the `\cref`s that read a dropped hypothesis cite the claim. The dump byte-identical. All eleven
  done; no new entry.
- [x] **12. G1's first two pin changes** (this commit; `F-247`, `F-248`). (a) A node in
  `rigidity-matrix.tex`, before `lem:block-rank-path` (749), takes
  `add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath` from `thm:pencil-x0-bridge`
  (`main-component.tex` 1617); `lem:block-rank-path`'s proof edge to the theorem moves to it, and
  the theorem's proof `\uses` it. If the pin reaches a later chapter's node, it is unpinned instead.
  (b) `mem_hingeRowBlock_iff` moves from `lem:case-III-claim612-block-iff-perp` (`case-iii.tex`
  1295) to `def:hinge-row-block` (`rigidity-matrix.tex` 113); `lem:screw-map-rows`'s
  (`generic-lift.tex` 1273) proof edge moves with it. (b) also cures the first of `F-257`'s three
  missing edges (the coordinator, after task 7): `lem:case-III-candidate-row`'s pin then reaches
  `mem_hingeRowBlock_iff` at `def:hinge-row-block`, an earlier chapter, so its proof gains that
  edge, per the reach report. *Expected:* one node added; two pins moved (`lean_decls` unchanged);
  the edges as listed, the new node's per its pin's reach, and `F-257`'s first; the screen's
  `rigidity-matrix` count one edge lower; the missing edges one fewer. *Exact, before editing*
  (the reach reports and the reduced graph on a scratch copy, `--tex-root`): (a) the pin's proof
  reaches `def:cut-edges-2ec` (`deficiency.tex`, through `Graph.cutEdges`), so it is unpinned and
  no node is added. `lem:block-rank-path`'s proof loses the theorem (no Lean basis or citation
  left); its pin, through the unpinned lemma, then reaches `def:cut-edges-2ec`, a missing edge
  that would be forward (new: `F-261`). `thm:pencil-x0-cycle`'s proof gains
  `lem:pencil-lifting-restrict`, which the removal would leave missing. (b) `def:hinge-row-block`
  takes a fourth pin (principle D's flag). The proofs of `lem:screw-map-rows`,
  `lem:case-I-realization-h65` and `lem:case-III-chain-discriminator`, `-relabel-rows` and
  `-eq666`, whose pins reached `lem:case-III-claim612-block-iff-perp` only through the moved pin
  and whose text does not cite its criterion, trade it for `def:hinge-row-block`;
  `lem:case-III-candidate-row`'s proof gains that node (its text cites it); all six implied.
  `F-257`'s first edge stays missing: the certification also reaches the node through
  `case_III_full_family_restriction` and its other pin. `lem:case-I-realization-h65`'s pin
  reaches `lem:case-II-placement-new-rows`, a later file, a missing edge that would be forward
  (new: `F-262`). So: no node added or removed; one pin removed, one moved (`lean_decls`
  changes); no `\leanok` change. Drawn, `1527 edges` (2222 statements): the five edges into
  `lem:case-III-claim612-block-iff-perp` and `thm:pencil-x0-bridge -> lem:block-rank-path` go,
  and 34 that the removed edges made transitive come: 10 dashed (`def:graph-operations`,
  `def:panel-hinge-framework`, `def:rigidity-matrix` into `-chain-relabel-rows`;
  `def:panel-hinge-framework` into `lem:pencil-rank-collineation`; `def:pencil-x0-standing` into
  the six `thm:pencil-x0-open-ear*`), and 24 solid (`lem:block-rank-cut` into
  `lem:block-rank-path`; `lem:pencil-lifting-restrict` into the cycle; `lem:pencil-rank-congr` and
  `lem:pencil-x0-fibre-intersection` into four open-ear theorems; `-main-picture-open` into the
  cycle and those four; `-one-witness` into the cycle and all six;
  `lem:splitoff-edge-substitution` into `lem:case-I-realization-h65`; `thm:pencil-x0-bridge` into
  `thm:pencil-x0-reduction-attains`). `--summary`: 1011 pins (994 distinct), 14 nodes with 4+
  pins, 6 missing edges, 2426 implied, 85 transitive, 134 with no Lean basis, 171 dead pins; the
  screen `rigidity-matrix 2/1`, `case-i 13/6`, the rest the open's.
  *Done:* exactly that: the dump's diff is its three header lines, the 40 graph lines, the three
  pin lines and the eight `\uses` lines; `--summary` and the screen as predicted. The remark after
  `def:hinge-row-block` states the fourth pin's claim, and a new note names the four pins;
  `lem:case-III-claim612-block-iff-perp`'s proof cites that remark, its note one pin. Honesty gate:
  no missing statement edge at the seventeen nodes read; the moved and the kept pins each beside its
  clause; at $C(p(e)) = 0$ every form lies in the space, and the note gives $D - 1$ only for
  $C(p(e)) \neq 0$. `F-247`, `F-248` done; new `F-261`, `F-262` (*Blockers*) and `F-263` (round 3).
- [ ] **13. G1's third: a node for open ears** (`F-249`). A definition node in `main-component.tex`'s
  *Ears and cycles* (2157) takes `Graph.IsOpenEar` from `def:pencil-x0-reduces` (4428), which
  `\uses` it; the statement edges of `lem:pencil-generic-one-ear` (5337) and
  `lem:pencil-rigid-good-ear` (5451) to `def:pencil-x0-reduces` move to it where neither statement
  names a reduction (the reach report); the definition-faithfulness gate. *Expected:* one node
  added; one pin moved (`lean_decls` unchanged); the edges as listed.
- [ ] **14. G2: the true duplicates merged, `case_III_realization` unpinned** (`F-120`; `F-163`,
  `F-171` in part). `lem:case-III-claim-6-11-base` (`case-iii.tex` 54) merges into
  `lem:splitoff-kdof-criterion` (`molecular-induction.tex` 1342), which pins its one pin: KT's
  argument (p. 661) kept where a reader needs it; `lem:case-III-gap3-minimalKDof`'s statement edge
  (110) and the `\cref`s (`case-iii.tex` 40, 133; `notes/BlueprintExposition.md` 536) moved.
  `lem:case-III-claim612-points-affineIndep-witness` (1174) and
  `lem:case-III-claim612-points-affineIndep` (1205), one statement on one dead pin, become one
  node. `lem:case-III` (2455) drops its dead $d = 3$ pin `case_III_realization`;
  `blueprint/CLAUDE.md`'s honesty-gate example says "`lem:case-III`'s pins", so the word follows
  (round 1 task 7's sanctioned example), nothing else in the manual. *Expected:* two nodes removed;
  three `lean_decls` lines removed (two duplicates and `case_III_realization`); the merged nodes'
  edges moved to the survivors, listed before editing.
- [ ] **15. KT's route: the genericity device's citations** (M3; `F-118` in part). Its twelve
  `\cref`s at the open (the plan's eleven, with the section lead's `\Cref`):
  `genericity-and-count.tex` 17, 115, 172, 303; `case-i.tex` 251, 492, 673, 1068, 1247;
  `case-ii.tex` 275; `panel-layer.tex` 751; `molecule-modelling.tex` 687. Each says which argument
  it borrows (task 5's open-set form, or the minor of `lem:rank-polynomial-of-le-finrank`), and
  points at another node where its sentence cites that node's claim. **And `F-255`'s cure** (the
  coordinator, after task 5): `lem:independent-rows-of-rank` and its note move from the counting
  subsection into the first, before `lem:genericity-device`, whose proof gains the edge to it; both
  subsections' leads follow. Its `\uses` (`rigidity-matrix.tex`, `case-i.tex` 630) all precede the
  new place, and its users all follow it or (`case-i.tex`) were forward already. *Expected:* that
  proof `\uses` added, the missing edge 0; the dump otherwise byte-identical, or a proof edge moved
  with its `\cref`, listed before editing; the screen unchanged.
- [ ] **16. KT's route: Case I's group** (M3, G3, G4; `F-134`, `F-139`, `F-118`). One framing
  remark in `case-i.tex` for `lem:cycle-realization-base` (48; it restates `lem:theorem-55-base`,
  `panel-layer.tex` 789, for panel-hinge frameworks, and says so), `lem:cycle-realization-dim-bound`
  (68), `lem:exists-independent-panel-extensor` (88), the three `lem:pinned-motions-on-*` (282,
  305, 329; since task 4 no node `\uses` `-mono`), `lem:case-I-splice-seed` (522), `lem:case-I`'s
  two dead pins (404) and `lem:claim-6-4` (task 6's). `lem:case-I` and `lem:claim-6-4` keep their
  crux depth.
  *Expected:* the dump byte-identical.
- [ ] **17. KT's route: Case II's group** (M3, G4; `F-147`, `F-152`). One framing remark for
  `case-ii.tex`'s `lem:case-II-rank-lift` (32; since task 4 no node `\uses` it) and `lem:case-II`
  (task 4's), and `genericity-and-count.tex`'s `lem:relative-device-count` (144),
  `lem:realization-of-independent-rows` (213), `lem:case-II-placement-old-rows` (437) and
  `lem:case-II-realization-placement` (495; S3's, which keeps its statement and note for the
  phase). *Expected:* the dump byte-identical.
- [ ] **18. KT's route: Case III's group** (M3, G3, G4; `F-159`, `F-163`, `F-167`, `F-118`). One
  framing remark in `case-iii.tex` for the six dead row-operation nodes
  (`lem:case-III-vanish-off-column` 450, `-seam` 523, `-acolumn-zero` 673, `-conditional-block`
  701, `-candidate-row-construction` 788, `-candidate-row` 855), the affine nodes left by task 14
  and `lem:case-III-claim612-r-nonzero` (1329), the relabel nodes (1410, 1445, 1497) and the three
  counts (task 7's); `lem:case-III-chain-dispatch`'s (2350) citations of the relabel nodes and of
  `lem:case-II-realization-placement` say which argument they borrow. Crux depth kept. **And
  `F-257`'s other two edges** (the coordinator, after task 7): `lem:case-III-claim612-eq644` (KT
  eq. (6.44)) moves to just after `lem:case-III-acolumn-zero` (KT eq. (6.43)), with the setting
  its statement needs; the lead before the third framework then cites it. Its `\uses`
  (`lem:case-III-redundant-decomposition`, `lem:case-III-acolumn-zero`) precede the new place, and
  its users (the third framework, the certification, `lem:case-III-chain-eq666`) follow it. The
  proofs of `lem:case-III-candidate-row` and `lem:case-III-claim612-p2-placement` gain their edges
  to it. *Expected:* those two proof `\uses` added, the missing edges two fewer; otherwise the
  dump byte-identical; the screen unchanged.
- [ ] **19. `meet.tex`: S28, and the route through $\bigwedge^2 W$** (`F-113`; G4, `F-111`). S28:
  `lem:complement-iso-decomposable-wedge-perp` (342–358) for $n = n_1$, as its second and third
  pins, without the independence (the case $n_2$ by alternation, in the proof). One framing remark
  for `lem:complement-iso-line-one-dim` (381) and `lem:complement-iso-exterior-map-injective`
  (397), with the dead pins of `def:meet` (197) and `def:meet-pairing-dual` (82): the formal proof
  of `lem:case-III-claim612-line-in-panel-union` (413) takes the span of dimension 5 and the Gram
  determinant instead. *Expected:* the dump byte-identical.
- [ ] **20. KT's route: the forest surgery** (G3, G4; `F-090`, `F-091`). One framing remark in
  `molecular-induction.tex`'s *Forest surgery* (476): KT's forests (their Lemmas 4.1–4.2, for
  4.3–4.4) beside the formal independent sets (`lem:edge-splitting` 1001, `lem:removal-deficiency`
  1229); `cor:forest-surgery-deficiency` (878), on a narrative-bridge shim, says that it restates
  `lem:forest-surgery-split` (835); `lem:forest-surgery-unsplit` (task 3's) that it is a case of
  `lem:edge-splitting`. *Expected:* the dump byte-identical.
- [ ] **21. Close** (`CLEANUP.md` *Workflow* 5; Sonnet may take it). The axioms check
  byte-identical to the open's, net of the path; the no-Lean-edit check from `1cbdbff5`; gates 1–5
  at the last task's values; the script's report and the forward screen beside the open's figures;
  `notes/BlueprintExposition.md`'s pointers to every node the round merged, added or restated
  checked, with a round note; the declarations the round unpinned listed in round 3's list for
  L9's §B check; every ledger entry the round touched has its disposition, task numbers as shas;
  the queue row `done = true`; ROADMAP's row ✓ and its RECONCILE bullet, and `notes/Reconcile.md`'s
  **Status**, pointing at round 3's open.

## Candidates for the PI

`S` and `M` findings this round makes, one line each naming the ledger ID.

None open: task 9's `F-260` (S), the rescaling's pin, went to task 9.1, which made it.

## Moved to a later round

Items outside this round's scope, one line each, mirrored in the same commit into the target's list
(`notes/Reconcile.md` §3: the phase's list, which already names each, and round 3's).

- S3 (`F-150`; `lem:case-II-realization-placement`): a declaration for the count at a rigid
  splitting-off comes first, then the repin; the phase's (c).
- S16 (`F-124`; `lem:generic-yields-genuine-hinge`): "loopless", or the case with loops in Lean;
  §3 holds it for the phase so the statement changes once; the phase's (c).
- S18 (`F-121`; `prop:rigidity-matrix-prop11`): restated or repinned on the generic forms after
  S1's refactor; the phase's (a).
- S19 (`F-116`; `lem:case-I`, a crux node): the rank-addition identity in Lean; task 16's remark
  names the live route meanwhile; the phase's (c).
- S22–S25 (`F-101`, `F-083`, `F-051`, `F-041`; `thm:minimal-kdof-reduction` (i),
  `lem:circuit-induces-rigid`, `thm:matroid-partition-rank`, `thm:pebble-game-correct`): kind E,
  formalized, not restated (§1); the phase's (c).
- S31 (`F-174`, `F-183`; `thm:molecular-iff-square-bar-joint`'s "Moreover", a crux node): the
  modelling equivalence in Lean; the phase's (c).
- `F-253` (L, task 2): the docstrings of `infinitesimalMotions_mono_of_span_le` and
  `finrank_infinitesimalMotions_le_of_span_le` call them KT Lemma 5.2 and reverse their inclusion.
  Round 3's docstring sweep.
- `F-254` (L, task 4): the docstrings of `rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`,
  which task 4 unpinned, and `isInfinitesimallyRigidOn_insert_iff` still give both as
  `lem:case-II`'s. Round 3's docstring sweep.
- `F-256` (L, task 5): the docstrings of `exists_good_realization`, `exists_good_realization_reindex`
  and `exists_good_realization_const`, and the first two's section header, still give them as
  `lem:genericity-device`'s. Round 3's docstring sweep.
- `F-258` (L, task 7): the docstrings of `linearIndependent_sum_augment_candidateRow`,
  `linearIndependent_sum_p2_candidateRow` and `linearIndependent_sum_p3_candidateRow`, which task 7
  unpinned, still give them as Case III's three count nodes'. Round 3's docstring sweep.
- `F-263` (L, task 12): `mem_hingeRowBlock_iff`'s docstring, and its file's header, still place it
  in `case-iii.tex`, at `lem:case-III-claim612-block-iff-perp`. Round 3's docstring sweep.
- `F-090`'s shim `splitOff_deficiency_le_of_forest_surgery`: it stays `cor:forest-surgery-deficiency`'s
  pin this round (no node retired; task 20); round 3's deletion of it (L9) repins the corollary on
  `forest_surgery_split` in the same commit. Round 3's list.

## Blockers / open questions

None for task 13. Three missing proof edges, each of which would be forward, wait for the
coordinator (task 12; the ledger has each cure's options):
- `F-257`'s first, `lem:case-III-candidate-row` to `lem:case-III-claim612-block-iff-perp`: task
  12's pin move did not cure it, as the certification reaches the node's other pin through
  `case_III_full_family_restriction`; `F-257` names the node's move.
- `F-261`, `lem:block-rank-path` to `def:cut-edges-2ec` (`deficiency.tex`), exposed by task 12's
  unpinning.
- `F-262`, `lem:case-I-realization-h65` to `lem:case-II-placement-new-rows`
  (`genericity-and-count.tex`), exposed by task 12's edge move.

`F-255` (task 5) is task 15's, and `F-257`'s other two (task 7) are task 18's: *Decisions made*.

## Hand-off / next phase

**Next: task 13**, at Opus: G1's third pin change (`F-249`), as its line says: a definition node in
`main-component.tex`'s *Ears and cycles* takes `Graph.IsOpenEar` from `def:pencil-x0-reduces`,
which `\uses` it, and the statement edges of `lem:pencil-generic-one-ear` and
`lem:pencil-rigid-good-ear` to `def:pencil-x0-reduces` move to it where neither statement names a
reduction; the definition-faithfulness gate. Before editing, write the exact expected diff in the
task's line from the reach reports and the reduced graph on a scratch copy (`--tex-root`;
`scratch/reconcile-statements/t12-predict.py` diffs the reduced graphs and lists the ancestors
each node loses), as task 12 did: check the new node's proof reach for a later node, and each
node that loses an ancestor for a reach left missing. Its parent dump is task 12's after-dump,
`scratch/reconcile-statements/dump-t12.txt` (gitignored, so regenerate it on the parent if it is
missing). Lines moved since the open's numbering, which later tasks use: task 12's,
`main-component.tex` −1 after 1620 (task 13's *Ears and cycles* is 2156, `def:pencil-x0-reduces`
4427, `lem:pencil-generic-one-ear` 5336, `lem:pencil-rigid-good-ear` 5450); `case-i.tex`, after
tasks 2 and 6, has the device's `\cref`s at 261, 503, 685, 1080 and 1259 (task 15) and task 16's
nodes at 49, 69, 89, 293, 316, 340, 415 (`lem:case-I`), 534 and 850 (`lem:claim-6-4`);
`molecule-modelling.tex`, after tasks 2, 9 and 9.1, has the device's `\cref` (task 15) at 691;
`genericity-and-count.tex`, after tasks 2, 5 and 10, has the device's `\cref`s at 17, 123, 180
and 311 (task 15) and task 17's nodes at 152, 221, 449 and 509 (`lem:relative-device-count`,
`lem:realization-of-independent-rows`, `lem:case-II-placement-old-rows`,
`lem:case-II-realization-placement`); task 3's, `molecular-induction.tex` −32 for 935–1059
(`lem:edge-splitting` is 969) and +17 after 1059 (`lem:removal-deficiency` 1246,
`lem:splitoff-kdof-criterion` 1359), with `lem:forest-surgery-unsplit` now at 1032;
`case-iii.tex`, after tasks 2, 4, 7 and 12, has the nodes later tasks name at (`\begin` lines):
task 14's `lem:case-III-claim-6-11-base` 54, the affine pair 1183 and 1214, `lem:case-III` 2503;
task 18's row-operation nodes 455, 528, 678, 706, 793 and 860, `lem:case-III-claim612-r-nonzero`
1336, the relabel nodes 1421, 1456 and 1508, the counts 1363 and 1603,
`lem:case-III-claim612-eq644` 1546 and `lem:case-III-chain-dispatch` 2394; task 4's,
`case-ii.tex` −5 for 72–133 (`lem:case-II` is 67) and −44 after 133 (`lem:case-II-realization`
91). Re-`grep` as ever. Carried in from round 1: `F-252` for the PI (round 1's *Candidates*; the
phase's (a) removes it), and its two docstring lines, already in round 3's list.

## Decisions made during this round

- **The slicing** (the open): 21 tasks against §3's ~20–30. The four false statements first, in
  one commit as §3 says, with S7's repin apart (task 5) so that commit moves no pin; then the other
  fixes by chapter, G1 and G2; then KT's route by group, each after its group's statement fixes.
- **What stays as it is** (the open, as the report suggests): S39's other nodes (`F-086`,
  `F-191`'s other three, `F-195`) keep their sources' standing hypotheses; S29's rescaling keeps its
  note; `lem:splitoff-edge-substitution`'s unpinned clause stays (true); the pencil doubles and
  `lem:reduction-step`'s stay (G2); S27 and S28 take the restatement, not Lean+.
- **S42 as one sweep** (the open): §1's table counts S42 among the statements fixed, which is the
  report's "or one restatement sweep".
- **The forward screen as gate 4** (the open): a task that adds a node or an edge adds no forward
  `\uses`, so round 5's ordering holds.
- **KT Lemma 5.2's credit** (task 2): in the prose before `lem:generic-realization-of-rigid`, not a
  node; that lemma and `lem:rank-polynomial-of-le-finrank` replace the rotation formally.
- **S10 at $h' = 0$, after `lem:edge-splitting`** (task 3): KT's use at p. 662, the proof keeping
  the forest construction; the node moved after `lem:edge-splitting`, whose two reverse lemmas its
  pin reaches, instead of gaining forward `\uses`.
- **S4 in its Case II setting; S5's edges implied** (task 4): `lem:case-II` keeps the first
  assertion at $t = V(G) \setminus \{v\}$, its note naming the general form (task 17 frames it);
  S5's new statement edges name what its clauses use, all implied.
- **Forward edges recorded, not added** (tasks 5, 7, 12): a pin whose reach makes a missing edge
  that would be forward gets a ledger entry for the coordinator, as the cure moves nodes the line
  does not name (`F-255`: `lem:genericity-device`'s note says which clauses its shared pin proves;
  `F-257`: Case III's counts pin the certification at the arms' roles, their notes mapping its
  hypotheses). The coordinator gave `F-255` to task 15 (`lem:independent-rows-of-rank` before the
  device) and `F-257`'s eq. (6.44) edges to task 18 (that node after `lem:case-III-acolumn-zero`).
- **S21 at its pin's point** (task 6): "there are normals $q_0$"; KT's point and the crux's steps
  are the proof's, the polynomial `lem:rank-polynomial-IH-relabel-proj`'s.
- **G1's first two: the line's alternative, and edges that follow their pin** (task 12): the
  bridge-path lemma is unpinned, since its proof reaches `def:cut-edges-2ec`, a later chapter; the
  path lemma then reaches it through the lemma (`F-261`), and the forward edge into the last chapter
  goes. Each `\uses` that only the moved pin backed follows it to `def:hinge-row-block`, as the
  line has `lem:screw-map-rows`'s do. A removal that leaves a reach missing adds that edge when it
  is backward (`thm:pencil-x0-cycle`), and records it when forward (`F-262`). `F-257`'s first edge
  survives the move, through the node's other pin; its cure is unassigned.
- **S26, S35, S27; S36 and the rescaling** (tasks 8, 9, 9.1): each node at what its pins prove;
  `rankHypothesis_zero_iff` joins `lem:trivial-motions-rank-bound` rather than pin the theorem
  (whose reach would close a cycle); (2) of the dual lemma shares `lem:pencil-jj-rescale`'s pins.
- **S38 and S39 in their pins' generality** (task 10): each edge what the new statement names
  (three unbacked edges go, `def:screw-space` comes); a note whose content became the statement
  gives way to a remark on its users, and each `\cref` that read a special case cites the claim.
- **S40–S42 in one commit; a hypothesis kept only where a definition needs it** (task 11): the
  drops free no edge and move no pin, so the nineteen nodes fit one commit. Soundness keeps
  $\ell < 2k$ in its "In particular" alone, since `def:runPebbleGame` defines the pebble game on
  $G$ for $\ell < 2k$ (that definition is not the task's); a node under a chapter lead that fixes
  $V$ finite says that its $V$ need not be. A `\cref` that cited an invariant's proof, or bounded
  $d$, because the statement assumed too much now cites the claim.
