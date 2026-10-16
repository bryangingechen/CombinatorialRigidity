# RECONCILE round 2/3 — `reconcile-statements`, every false statement and KT's route explained (work log)

**Status:** in progress (opened 2026-10-15). Round 2 of **RECONCILE**'s three autopilot rounds; the
plan and the PI's decisions are `notes/Reconcile.md`, and `.claude/autopilot/queue.toml` is the
authority for which rounds are done. The round fixes the blueprint statements the plan assigns it
(S4–S10 but S3, S14, S15, S20, S21, S26–S29, S35, S36, S38–S42), makes G1's three pin changes and
G2's merges of true duplicates, and gives each group of nodes where the formal proof leaves Katoh
and Tanigawa's route a framing remark, under the expected-diff and honesty gates; the Lean is not
edited. The open (task 1, docs only) reproduced round 1's close values and sliced the round into
21 one-commit tasks; S3, S16, S18, S19, S22–S25 and S31 wait for the phase. Tasks 1–11 are done
(the open; the false statements S6–S10; S4 and S5; S7's repin; Case I's S14, S15 and S21; Case
III's three counts, S20; S26, S27 and S35; S29; S36's and the rescaling's pins, `F-259` and
`F-260`; S38 and S39, stated generally; S40–S42, the hypotheses the pins do not take). **Next
concrete task:** task 12, G1's first two pin changes (*Lemma checklist*); `F-255`'s and
`F-257`'s cures are tasks 12, 15 and 18's. Round manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop (`notes/Reconcile.md` §4): the queue runs the three rounds unattended and stops
before `RECONCILE-FORMAL`. An unplanned `NEEDS_PI` entry goes here, newest first, and the PI
answers in an entry that starts `**PI, <date>:**`. No entries yet.

## Current state

**Tasks 1–11 are done**; task 11, S40–S42, is this commit (`pebble-game.tex`, `body-bar.tex`,
`body-hinge.tex`, `intro.tex`, `sparsity.tex`, `laman-theorem.tex`, `rigidity-matroid.tex`,
`count-matroid.tex`, `executable.tex`, and the citing sentence in `deficiency.tex`). Nothing is
mid-stream; task 12 is next. `F-255`'s cure is task 15's (its line); `F-257`'s, three missing
proof edges that would be forward, are tasks 12's and 18's (their lines). Task 11's gates:
`lint.sh` green; `verify.sh` green, `checkdecls` silent, the same 9 `WARNING:` lines; **`1499
edges 3e9dbd3eeddc9a23`**, **`9c98f641ae650627`**; the dump byte-identical to `dump-t10.txt`, kept
as `scratch/reconcile-statements/dump-t11.txt`; `--summary` exits 0, both checks OK, byte-identical
to task 10's (690 nodes pinned, 1012 pins (995 distinct), 4 missing edges, 171 dead pins, 134
edges with no Lean basis, 85 transitive, 13 nodes with 4+ pins); the nineteen nodes' `--label`
reports show no missing edge; the forward screen the open's lines; `print.log` rebuilt by latexmk,
0 `LaTeX Warning` lines, 31 overfull boxes; `check-phase-note.py` green; the no-Lean-edit diff
from `1cbdbff5` empty; no `formalization.yaml` edit (its two Tay rows bound no dimension);
`notes/BlueprintExposition.md` names one of the nineteen, `lem:isSparse-of-rowIndependent-two`, in
its light screen, and that sentence holds. The declarations round 2 unpins, for the close's list
(tasks 8–11 unpin none): task 4's `rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`
(no caller), task 5's `exists_good_realization` and `exists_good_realization_const` (dead,
`F-152`), and task 7's `linearIndependent_sum_augment_candidateRow`,
`linearIndependent_sum_p2_candidateRow` and `linearIndependent_sum_p3_candidateRow` (dead); their
docstrings are `F-254`'s, `F-256`'s and `F-258`'s, round 3.

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
- [x] **11. S40, S41, S42: hypotheses the pins do not take** (this commit; `F-034`, `F-036`,
  `F-058`, `F-015`, `F-026`, `F-027`, `F-028`, `F-031`, `F-037`, `F-042`, `F-046`). S40:
  `lem:pebble-game-invariants` (`pebble-game.tex` 230–251) without $V$ finite and $\ell < 2k$,
  parts (1)–(2) for every vertex and finite $V'$, (3)–(4) at $\ell \le k|V'|$;
  `thm:pebble-game-soundness` (697–711) without $\ell < 2k$. S41: `thm:tay-witness` (`body-bar.tex`
  689) and `thm:body-hinge-tay` (`body-hinge.tex` 126), main results' nodes, without $d \ge 2$,
  and `intro.tex`'s summary of Tay's theorem (167) with them (no row or README sentence states
  it). S42: fifteen nodes' finiteness as their pins take it:
  `sparsity.tex` 537; `laman-theorem.tex` 198, 402; `rigidity-matroid.tex` 76, 130, 158, 185, 294;
  `count-matroid.tex` 89; `pebble-game.tex` 846, 999; `executable.tex` 34, 46, 63, 74. May split
  by chapter (11.1, 11.2). *Expected:* the dump byte-identical. *Exact, before editing* (the 24
  pins' statements by `#check`, `scratch/reconcile-statements/T11Pins.lean`; the nineteen nodes'
  `--label` reports, no missing edge): one commit, no split. No node added or removed; no `\uses`
  added, moved or removed (no dropped hypothesis is a node, and each statement still names what
  its edges name); no pin moved, added or removed (`lean_decls` stays `9c98f641ae650627`); no
  `\leanok` change; so `1499 edges 3e9dbd3eeddc9a23`, the dump byte-identical to `dump-t10.txt`,
  `--summary` task 10's, the screen unchanged. The `\cref`s that read a dropped hypothesis follow:
  `pebble-game.tex`'s four that cite an invariant's proof for want of its hypotheses (after
  `def:pebble-counts` and `def:tryAddEdge`, the proofs of
  `lem:pebble-game-independent-brings-pebble` and `-tryAddEdgeWith-isSparse`) cite the invariant;
  the paraphrase of `lem:workhorseWitness-certifies` before `def:tryAddEdge` takes its graph; the
  soundness proof's remark on $\ell < 2k$ says why only the last claim takes it; `deficiency.tex`
  94 drops "When $d \ge 2$". No `formalization.yaml` edit: its two rows bound no dimension.
  *Done:* exactly that; `--summary` and the screen byte-identical to task 10's. The invariants on
  any $V$ at any $k, \ell$, (3) and (4) each "if $\ell \le k|V'|$", the note saying no part needs
  $\ell < 2k$; soundness at any $\ell$ but its "In particular" (the game on $G$ is defined for
  $\ell < 2k$); both Tay theorems and the summary at every $d$, as `lem:edge-multiply-sparse` was.
  S42's nodes take no finiteness, or finitely many edges (`lem:span-range-rigidityRow`,
  `lem:workhorseWitness-certifies`, `def:pebbleGameResult`, `def:edgeListSorted`); the two
  membership lemmas follow their definitions; `count-matroid.tex`'s says "need not be finite"
  against the section's lead. Honesty gate: each clause beside its pin, read by `#check`; soundness
  keeps `[Fintype V]`. All eleven entries done; no new entry.
- [ ] **12. G1's first two pin changes** (`F-247`, `F-248`). (a) A node in `rigidity-matrix.tex`,
  before `lem:block-rank-path` (749), takes
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
  `rigidity-matrix` count one edge lower; the missing edges one fewer.
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
- `F-090`'s shim `splitOff_deficiency_le_of_forest_surgery`: it stays `cor:forest-surgery-deficiency`'s
  pin this round (no node retired; task 20); round 3's deletion of it (L9) repins the corollary on
  `forest_surgery_split` in the same commit. Round 3's list.

## Blockers / open questions

None. (`F-255`, task 5's missing proof edge, is task 15's; `F-257`, task 7's three, are tasks 12's
and 18's: *Decisions made*.)

## Hand-off / next phase

**Next: task 12**, at Opus: G1's first two pin changes (`F-247`, `F-248`) with `F-257`'s first
cure, as its line says: (a) a node in `rigidity-matrix.tex` before `lem:block-rank-path` takes
`add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath` from `thm:pencil-x0-bridge`
(`main-component.tex` 1617), or the pin is unpinned if it reaches a later chapter's node; (b)
`mem_hingeRowBlock_iff` moves to `def:hinge-row-block` (`rigidity-matrix.tex` 113), with
`lem:screw-map-rows`'s proof edge, and `lem:case-III-candidate-row`'s proof gains its edge to that
node. Before editing, write the exact expected diff in the task's line, from the reach reports on a
scratch copy (`--tex-root`), as task 10 did; the open's estimate is one node added, two pins moved
(`lean_decls` unchanged), the screen's `rigidity-matrix` count one lower and the missing edges one
fewer. Its parent dump is task 11's after-dump, `scratch/reconcile-statements/dump-t11.txt`
(gitignored, so regenerate it on the parent if it is missing). Task 11 moved no line that a later
task names. Lines moved since the open's numbering, which later tasks use: tasks 2's and 9.1's,
`rigidity-matrix.tex` −3 after the old 478 (`lem:block-rank-path`, task 12, is 746); tasks 8's and
10's, `generic-lift.tex` −2 after 527 and −1 after 1140 (`lem:screw-map-rows`, task 12, is 1270);
`case-i.tex`, after tasks 2 and 6, has the device's `\cref`s at 261, 503, 685, 1080 and 1259 (task
15) and task 16's nodes at 49, 69, 89, 293, 316, 340, 415 (`lem:case-I`), 534 and 850
(`lem:claim-6-4`); `molecule-modelling.tex`, after tasks 2, 9 and 9.1, has the device's `\cref`
(task 15) at 691; `genericity-and-count.tex`, after tasks 2, 5 and 10, has the device's `\cref`s
at 17, 123, 180 and 311 (task 15) and task 17's nodes at 152, 221, 449 and 509
(`lem:relative-device-count`, `lem:realization-of-independent-rows`,
`lem:case-II-placement-old-rows`, `lem:case-II-realization-placement`); task 3's,
`molecular-induction.tex` −32 for 935–1059 (`lem:edge-splitting` is 969) and +17 after 1059
(`lem:removal-deficiency` 1246, `lem:splitoff-kdof-criterion` 1359), with
`lem:forest-surgery-unsplit` now at 1032; `case-iii.tex`, after tasks 2, 4 and 7, has the nodes
later tasks name at (`\begin` lines; none moved before 873 by task 7): task 12's
`lem:case-III-claim612-block-iff-perp` 1304; task 14's `lem:case-III-claim-6-11-base` 54, the
affine pair 1183 and 1214, `lem:case-III` 2505; task 18's row-operation nodes 455, 528, 678, 706,
793 and 860, `lem:case-III-claim612-r-nonzero` 1338, the relabel nodes 1423, 1458 and 1510, the
counts 1365 and 1605, and `lem:case-III-chain-dispatch` 2396; task 4's, `case-ii.tex` −5 for
72–133 (`lem:case-II` is 67) and −44 after 133 (`lem:case-II-realization` 91). Re-`grep` as ever.
`F-255`'s cure is task 15's (its line); `F-257`'s are tasks 12's and 18's (their lines). Carried in
from round 1: `F-252` for the PI (round 1's *Candidates*; the phase's (a) removes it), and its two
docstring lines, already in round 3's list.

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
- **KT Lemma 5.2's credit** (task 2): in the prose before `lem:generic-realization-of-rigid`, not in
  a node title. No node states it: where the two equal panels are joined by an edge, its input is a
  degenerate hinge in the carrier, and the formal steps that replace the rotation are that lemma
  (rigid realizations) and `lem:rank-polynomial-of-le-finrank` (any rank). Citations of KT's
  rotation cite KT's pages.
- **S10 at $h' = 0$, after `lem:edge-splitting`** (task 3): the node states its pin's case
  $h' = 0$, KT's use at p. 662, rather than the pin's whole case (i), which is
  `lem:edge-splitting`'s; its proof keeps the forest construction. The pin's value reach takes in
  the two reverse lemmas, which followed the node, so the node moved after `lem:edge-splitting`
  (`AUTHORING.md` *Node order*) instead of gaining forward `\uses`; the dump does not record order.
  `lem:removal-deficiency-equality`'s proof still cites `lem:edge-splitting` at $h' = 0$, which is
  true; it stays, as the task changes no other node's edges.
- **S4 in its Case II setting; S5's edges implied** (task 4): `lem:case-II` keeps the first
  assertion as stated, at $t = V(G) \setminus \{v\}$, not its pin's general form, as the task drops
  the vacuous assertion only; the note names the general form, and task 17's remark frames the
  node. S5's three new statement edges name what its new clauses use, as
  `lem:case-III-chain-relabel-rows`'s do; each is already an ancestor, so no drawn edge changes.
- **S7's repin; its forward edge recorded, not cured** (task 5): `lem:genericity-device` shares
  `lem:rank-polynomial-of-le-finrank`'s pin, its note saying which clauses the pin proves (each
  rank locus open in $U$, over any field) and which are the proof's, as S6's note does for its rank
  bound. The pin's body reaches `lem:independent-rows-of-rank`, later in the file; that edge would
  be forward and the cure moves a node the line does not name, so it is `F-255`, for the
  coordinator. `lem:relative-device-count`'s edge to the node moves to `def:panel-hinge-framework`,
  which its pin's statement reaches and the removal would leave missing.
- **`F-255`'s cure goes to task 15** (the coordinator, after task 5): move
  `lem:independent-rows-of-rank` before `lem:genericity-device`, rather than the device after it
  (which would leave the first subsection a lead alone) or leaving the edge missing (round 5 left
  none). Task 15 already edits both leads; the move adds no forward `\uses`.
- **S21 at its pin's point; the polynomial left to `lem:rank-polynomial-IH-relabel-proj`** (task
  6): the pin's statement gives some $q_0$, so the node says "there are normals $q_0$" and KT's
  point is its proof's. The proof keeps the crux's steps (the contraction's rank, KT Lemma 5.1, KT's
  point, the spanning forms) and stops at $q_0$; the polynomial, its former last step, is that
  lemma's, so the proof's edge to `lem:rank-polynomial-proj-eval`, with no Lean basis, goes. The
  `\cref`s that cite KT Claim 6.4 at generic panels now point at both nodes.
- **S20 at the three roles; the forward edges recorded, not added** (task 7): each count node pins
  `case_III_rank_certification` and keeps KT's statement, naming its framework as
  `def:case-III-candidate`'s at the role the arms' bodies give; its note maps each of the
  theorem's hypotheses to its source (the honesty gate's reading). The crux proofs keep KT's route,
  the notes saying how the theorem's count differs. The theorem's body reaches two later nodes of
  the file, so, as for `F-255`, three proof edges stay missing (`F-257`) rather than forward: the
  cure moves nodes that the line does not name.
- **`F-257`'s cures go to tasks 12 and 18** (the coordinator, after task 7): task 12(b)'s pin move
  puts `mem_hingeRowBlock_iff` in an earlier chapter, so the first edge is no longer forward; for
  the two edges to `lem:case-III-claim612-eq644`, that node moves after `lem:case-III-acolumn-zero`,
  whose KT eq. (6.43) it follows (task 18, which frames that subsubsection), rather than the
  certification's users after it. Neither move adds a forward `\uses`.
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
