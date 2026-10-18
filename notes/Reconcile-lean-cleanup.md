# RECONCILE round 3/3 — `reconcile-lean`, the Lean outside the phase's footprint (work log)

**Status:** in progress (opened 2026-10-15). Round 3 of **RECONCILE**'s three autopilot rounds; the
plan and the PI's decisions are `notes/Reconcile.md`, and `.claude/autopilot/queue.toml` is the
authority for which rounds are done. The round acts on the Lean: a script that checks the blueprint
labels the docstrings name, L9's deletions after `CLEANUP.md` §B's trial deletion (with `F-090`'s
shim and round 2's unpinned declarations), `F-061`'s rename, L6–L8's signatures and repeated
derivations with S17, L1–L2 (the pebble game's search, after a recon), a non-vacuity witness for
each of the 16 main results outside S1's and S2's rows, and the docstring sweep by directory (L3–L5,
L10–L12, M2's, M4's and M5's docstrings, round 2's six `L` entries). No main result's statement
changes. In the footprint (34 files: the 33 that construct `PanelHingeFramework`, and
`GenericLift/HingeGeneric.lean`) the docstrings that describe the carrier or S1's and S2's theorems
wait for the phase. Tasks 1–30 are done (*Current state*): the open, the docstring-label check
(gate 9: 422 at task 2, 319 now), L9's deletions with `F-090`'s shim, `F-061`'s rename, L6–L8's
hypotheses and repeated derivations, the pebble game's search with one visited set and its texts
(tasks 16–20), the sixteen non-vacuity witnesses (tasks 21–24), and the docstrings of every
top-level file but `Nonvacuity.lean`, of `Search/`, of `Mathlib/`, of `PebbleGame/`, of `Matroid/`
and of `BodyBar/` (tasks 25–28), of `Molecular/Deficiency.lean` (tasks 29–29.1) and of
`Molecular/Induction/Operations.lean` (task 30).
**Next concrete task:** task 30.1, the docstrings of `Molecular/Induction/` but `Operations.lean`
and `ForestSurgery/` (*Lemma checklist*).
Round manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop (`notes/Reconcile.md` §4): the queue runs the three rounds unattended and stops
before `RECONCILE-FORMAL`. An unplanned `NEEDS_PI` entry goes here, newest first, and the PI
answers in an entry that starts `**PI, <date>:**`. No entries yet.

## Current state

**Task 30 is done** (this commit); nothing is mid-stream.

**Task 30** (`F-235` `done`; `F-085`, `F-088`, `F-097`, `F-108`, `F-148`, `F-168`, `F-172`, `F-240`
in part; `F-279` gains twenty-two; new `F-282`, `open` for task 38): every docstring and comment of
`Molecular/Induction/Operations.lean` (3 348 lines; the hand-off's split, 30/30.1) read against
its body under the sweep's form; credits checked in `.refs/` (KT 2011 pp. 658–698, the arXiv
version's Lemma 5.1). Its message names the false claims (among them KT Lemma 4.5(ii)'s eq. (4.4)
credited to KT Lemma 4.6, the triangle lemma called a case of the cycle lemma, `ChainData`'s `n`
called the dof regime, KT Lemma 4.6 placed in §6.4.2, uses by four declarations that do not
exist). Gate 9 333 → 319. The ledger: 282 entries, 180 `done`, 9 `left`, 84 `reported`, 9 `open`.

**Tasks 25–29.1** (`F-018`, `F-022`, `F-023`, `F-025`, `F-030`, `F-032`, `F-035`, `F-040`, `F-045`,
`F-053`, `F-057`, `F-074`, `F-077`, `F-080`, `F-081`, `F-176`, `F-194`, `F-198`, `F-200`, `F-205`,
`F-230`, `F-244` `done`; others in part; new `F-278` to `F-281`): the planar files, `Search/`,
`Mathlib/`, `PebbleGame/`, `Matroid/Constructions/`, `BodyBar/`, the square-graph and
generic-rigidity files, and `Molecular/Deficiency.lean` (split at the tight partitions), under
*Decisions*' sweep form; their messages name each false claim.

**Done before** (tasks 3–24; their `[x]` lines and messages carry the detail): L9's thirty-nine
deletions (`F-266`'s and `F-267`'s orphans among them; the pins they left without a caller stay with
their nodes), `F-090`'s shim, `F-061`'s rename to `_starForest`, L6–L8's unused or derivable
hypotheses and repeated derivations (each node they reach restated in the same commit; gate 2 runs
block (c) since task 5), the search with one marked set and its texts (tasks 16–20; `F-033`,
`F-047` `done`, new `F-276`, `F-277` `reported`), and `Nonvacuity.lean`'s sixteen witnesses (tasks
21–24, all on the three axioms; FRICTION: tasks 22–24's entries, task 21's waits for task 38).

**The docstring-label check** (`scripts/check-docstring-labels.py`, gate 9; its rule is its
docstring and *Decisions*): **422** at task 2 (39 *missing*, 136 *pinned, another node*, 247
*unpinned, own node*; `scratch/reconcile-lean/labels-t2.txt`, gitignored); its acceptance is
`65a5c0ee`'s message. Of the stale or absent labels `F-230`–`F-264` list, all are reported but
`runPebbleGame.aux`'s (past its lead; task 26 fixed it); a docstring naming no node is outside it.

**Verified at the open** (2026-10-15, at `347ba9c4`, round 2's close tree; its Lean is `64bb9754`'s,
unchanged since `6f4f7afa`, the tree of the ledger's Lean baselines):
- Whole-project `lake build` green: "Build completed successfully (2996 jobs)", 0 `warning:`, 0
  `error:` and 0 `failed to cache artifact` lines; `lake lint` green ("Linting passed for
  CombinatorialRigidity.").
- **The axioms check** (`notes/Reconcile.md` §2): the harness `scratch/reconcile-lean/Axioms.lean`,
  generated by gate 3's command, is `cmp`-identical to round 2's open and close harnesses. Run with
  `lake lean`, all 19 main results give `[propext, Classical.choice, Quot.sound]`, and the output
  equals round 2's close byte for byte net of the harness's path (its one warning is its own long
  line 31).
- Round 2's close values, reproduced exactly: `lint.sh` green; `verify.sh` green, `checkdecls`
  silent, **9** `WARNING:` lines; the dump (`python3 scripts/blueprint-deps.py --dump`, after
  `verify.sh`) 3 609 lines, first lines **`1525 edges aa87ce11152366b1`** and
  **`558613b168745717`**, `cmp`-identical to round 2's close dump, kept as
  `scratch/reconcile-lean/dump-open.txt` (gitignored); `--summary` exits 0, both consistency checks
  OK, byte-identical to round 2's close (691 nodes, 689 pinned, 1 008 pins, 993 distinct, 169 dead
  pins, 0 missing edges); `print.log` **0** `LaTeX Warning` lines, 31 overfull boxes (not gated);
  the forward-`\uses` screen 33 edges at 17 nodes to a later file and 4 at 4 within a file, the same
  lines as round 2's close (`scratch/reconcile-lean/forward-open.txt`).
- **The ledger's Lean baselines** (`notes/Prose-findings.md` *Lean baselines*) hold: `python3
  scripts/cleanup-smell-sweep.py --base HEAD --rev HEAD --tree CombinatorialRigidity/` gives the
  table's counts exactly (152 files, 110 881 lines; `classical` 430, `nolint/linter` 34, `rw4+` 282,
  …), and the span ranking stands, as the Lean has not changed since its tree. Task 38 re-runs both.
- **The footprint** (block (a) under *Scope*): 33 files whose declarations (257) name
  `PanelHingeFramework.mk` or one of the eight definitions returning one (`ofNormals`, `ofParam`,
  `withMomentNormals`, `withGraph`, `withNormal`, `Theorem55.lean`'s private `reaim`, `reaimSub`,
  `reaimSubLink`; read from their types by a `lake lean` probe, script not retained) in a statement
  or a body; with `GenericLift/HingeGeneric.lean`, 34. Under `Molecular/`:
  `AlgebraicInduction/{CaseI, CaseII, Coupling, GenericityDevice, PanelHinge, Theorem55}`,
  `CaseIII/{Arms, Candidate, Realization}`, `CaseIII/Relabel/{Arm, Basic, Chain, ChainColumn,
  ForkedArm}`, `GenericLift/{PanelGeneric, HingeGeneric}`, `Molecule/{Duality, GeneralPosition4,
  Modelling, Theorem56}`, `Molecule/Pencil/MainComponent/{Bridge, Carrier, Chain, Configuration,
  ContractAdditive, ContractCurve, Cut, Ear, EarGen, Flat, GenericBase, Orbit, Short, SplitOff}`.
- **The L9 screen** (block (b)) gave tasks 3–5 their 36 declarations and task 6 the shim. It kept
  `exists_good_realization` and `_reindex` (pinned declarations reach them), the three helpers of
  the pinned $d = 3$ dispatch `case_III_candidate_dispatch`, the pinned dead declarations
  (`minimal_kdof_reduction`, `annihRowPoly_totalDegree_le`, `F-114`'s three, `F-233`'s three), and
  the live `add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath`.

## Scope and standing rules

From `notes/Reconcile.md` §1–§3, restated as far as a builder needs them.

- **Surface.** The Lean under `CombinatorialRigidity/` and `Main.lean`; the blueprint nodes and prose
  a task's line names (pins renamed, moved or removed, the statements L6–L8 reach, `dfs.tex`);
  `DESIGN.md`'s pebble-game section and the `lakefile.toml` comment (task 20); `PHASE-BOUNDARIES.md`'s
  witness sentence (task 21); new scripts under `scripts/` (tasks 2, 18); the ledger's
  dispositions; this log, ROADMAP's row and bullet, and `notes/Reconcile.md`'s **Status** and §3. No
  `main_results` entry's `declaration:` or `file:`; no toolchain, manifest or lakefile option.
- **The hygiene rule, lifted exactly for §3 *Round 3*'s items.** No main result's statement changes.
  A declaration's signature changes only as L6–L8 and S17 say (an unused, derivable or over-strong
  hypothesis dropped, a repeated derivation replaced), and a blueprint statement only where such a
  change reaches it. Any other statement change, in the Lean or the blueprint, is an `S` entry with
  its line under *Candidates for the PI*, not acted on and not a stop. A witness that fails is a new
  `S` entry for the phase.
- **The footprint** (*Current state*). In it, a docstring part waits for the phase when it says what
  `PanelHingeFramework`'s fields mean or what its constructors guarantee (`ends`, the eight
  definitions, `toBodyHinge`, `IsHingeCoplanar`, `HasCoplanarPanelRealization`), or documents a
  declaration of S1's or S2's rows or a node the phase restates (S13, S18,
  `cor:theorem-55-d3-spanning`); `GenericLift/` is S1's refactor's, so its docstrings wait. Every
  other part (a label, a credit, a page, process narration, false mathematics about something else)
  is this round's, and so are code changes everywhere. Outside the footprint everything proceeds.
- **Evidence** (§2): claims about the Lean come from statements and bodies, never docstrings; a
  surprise gets a `lake lean` witness in `scratch/reconcile-lean/` before it is written; citations
  meet `CLAUDE.md` *Referencing prior work* against `.refs/`.
- **The ledger** stays each finding's home. A task names the IDs it acts on. An entry the round
  finishes becomes `done (task N)`; one it acts on in part keeps its disposition and gains `; round
  3: <what> (task N)`; a part moved to the phase gains `; round 3: <what> moved to the phase`; the
  close writes each task's sha. New entries take IDs from `F-266`, with `open
  (notes/Reconcile-lean-cleanup.md, task N)` until a task sets their disposition; one line here per
  new entry.
- **Gates for every commit**, each in the foreground with an explicit `timeout`, its output written
  to a file under `scratch/reconcile-lean/` and grepped (never piped into `tail`):
  1. A Lean task: whole-project `lake build`, 0 `warning:`, 0 `error:`, 0 `failed to cache artifact`
     lines; then `lake lint` green.
  2. A Lean task: the friction review, and the per-slice gates of `CombinatorialRigidity/CLAUDE.md`
     *Forward-mode slices*: a changed statement (grep `blueprint/src/` for the name; restate the node
     in the same commit) and a deletion (`grep -rn` the repository for each deleted name, and block
     (c) for its brace and suffix forms; every docstring, comment, blueprint and live-doc reference
     repointed or removed in the same commit; closed phase notes and the ledger are history).
  3. A Lean task: the axioms harness, regenerated, `cmp`-identical to the open's, run with `lake
     lean`: all 19 main results `[propext, Classical.choice, Quot.sound]`, the output the open's net
     of the path. A witness task adds its witnesses' `#print axioms` (the same three).
     ```sh
     ruby -ryaml -e 'r=YAML.load_file("formalization.yaml")["status"]["main_results"]; i=r.map{|x| x["file"].sub(/\.lean$/,"").tr("/",".")}.uniq.sort; print i.map{|m| "import #{m}\n"}.join+"\n"+r.map{|x| "#print axioms #{x["declaration"]}\n"}.join' > scratch/reconcile-lean/Axioms-tN.lean
     ```
  4. A deletion task: block (b) on every name first (no blocker), then **§B's trial deletion**:
     delete, and gate 1 green before the commit.
  5. `blueprint/lint.sh` green; `blueprint/verify.sh` green, `checkdecls` silent, 9 `WARNING:` lines.
  6. **The dump**: `python3 scripts/blueprint-deps.py --dump > scratch/reconcile-lean/dump-tN.txt`
     after `verify.sh`, `cmp`-identical to the parent's (the previous task's; task 2's is the open's
     `dump-open.txt`) unless the task's line lists a change; then round 2's expected-diff gate
     (`notes/Reconcile-statements-cleanup.md` *Scope*, gate 3), the expected diff written in the
     line before editing. `--summary` exits 0, both consistency checks OK; a Lean change can move a
     pin's reach (dead pins, unbacked edges), and the line names the counts that move.
  7. A task that adds a `\uses`: the forward-`\uses` screen (`notes/Prose-graph-cleanup.md`
     *Scope*'s block, as `scratch/reconcile-lean/forward-screen.py`): no new forward edge against
     33/17 and 4/4.
  8. A TeX task: `blueprint/print/print.log` 0 `LaTeX Warning` lines, latexmk having rebuilt it.
  9. From task 2 on, task 2's docstring-label check: its count does not rise, and falls by what the
     task fixes; a task that moves, renames or removes a pin runs it. The count is the `total` line
     of `python3 scripts/check-docstring-labels.py > scratch/reconcile-lean/labels-tN.txt` (task 2:
     422); every task runs it (a second) and diffs the report against the parent's.
  10. `python3 notes/check-phase-note.py` green.
  Every commit also updates this log: its checklist line, *Current state* and *Hand-off*.
- **The honesty gate** (round 2's, `notes/Reconcile-statements-cleanup.md` *Scope*) for every node a
  task restates or repins.
- **Rungs** (§2): Opus for tasks 2–38, a fresh agent per task; Sonnet may take the close.
- **Block (a), the footprint**, from `scripts/blueprint-deps.py`'s Lean cache (refreshed by any run
  of the script after a Lean edit):
  ```sh
  python3 - <<'PY'
  import json,glob,os,re,collections
  c=max(glob.glob('.lake/blueprint-deps/*.jsonl'),key=os.path.getmtime)
  P='CombinatorialRigidity.Molecular.PanelHingeFramework.'
  C={P+x for x in 'mk ofNormals ofParam withMomentNormals withGraph withNormal reaim reaimSub reaimSubLink'.split()}
  b=lambda n: re.sub(r'\.(_proof|match_|_simp_|eq_\d|proof_).*$','',re.sub(r'^_private\.(?:[^.]+\.)*?0\.','',n))
  D=collections.defaultdict(set)
  for r in map(json.loads,list(open(c))[1:]):
    if 'n' in r and {b(x) for x in r['t']+r['v']}&C and b(r['n']) not in C: D[r['m'].replace('.','/')+'.lean'].add(b(r['n']))
  print(len(D),'files,',sum(map(len,D.values())),'declarations'); [print(len(v),k) for k,v in sorted(D.items())]
  PY
  ```
- **Block (b), the liveness screen** (`CLEANUP.md` §B), from the same cache: for each name, pinned or
  not, reached by a main result or not, its callers, and the pinned or live declarations among its
  callers' callers, which block its deletion; then the callees that deleting all the names would
  leave without a caller, transitively (*Decisions*; a pinned or live one stays):
  ```sh
  python3 - NAME1 NAME2 <<'PY'
  import json,glob,os,re,sys
  c=max(glob.glob('.lake/blueprint-deps/*.jsonl'),key=os.path.getmtime)
  b=lambda n: re.sub(r'\.(_proof|match_|_simp_|eq_\d|proof_).*$','',re.sub(r'^_private\.(?:[^.]+\.)*?0\.','',n))
  T={};[T.setdefault(b(r['n']),set()).update(map(b,r['t']+r['v'])) for r in map(json.loads,list(open(c))[1:]) if 'n' in r]
  P={x.strip() for x in open('blueprint/lean_decls')}
  M=re.findall(r'^  - declaration:\s*"([^"]+)"',open('formalization.yaml').read(),re.M);L=set(M);s=list(M)
  while s: [L.add(n) or s.append(n) for n in T.get(s.pop(),()) if n not in L]
  R={};[R.setdefault(x,set()).add(n) for n,u in T.items() for x in u if x!=n]
  for q in sys.argv[1:]:
    for f in [n for n in T if n==q or n.endswith('.'+q)]:
      U=set();s=[f]
      while s: [U.add(c) or s.append(c) for c in R.get(s.pop(),()) if c not in U and c!=f]
      k=lambda X: sorted(x.split('.')[-1] for x in X)
      print(q,'pinned' if f in P else 'unpinned','live' if f in L else 'dead','| callers',k(R.get(f,())),'| blocked by',k(x for x in U if x in P or x in L))
  D={f for q in sys.argv[1:] for f in T if f==q or f.endswith('.'+q)};O=set();s={1}
  while s: s={x for d in D for x in T[d] if x in T and x not in D and not R.get(x,set())-D};O|=s;s-=P|L;D|=s
  print('orphans',[(x.split('.')[-1],x in P,x in L) for x in sorted(O)])
  PY
  ```
- **Block (c), a deletion's abbreviated mentions** (task 5: task 4's `grep` missed six): each
  backticked brace form `a_{b,c}_d` expanded, and each suffix form `_d`, matched against the deleted
  names over the Lean, the blueprint source and the top-level docs (a short suffix also hits live
  names; read each hit):
  ```sh
  python3 - NAME1 NAME2 <<'PY'
  import re,sys,glob,itertools
  D=set(sys.argv[1:]);F=glob.glob('CombinatorialRigidity/**/*.lean',recursive=True)+glob.glob('blueprint/src/**/*.tex',recursive=True)+glob.glob('*.md')
  for f in F:
    for i,l in enumerate(open(f),1):
      for t in re.findall(r'`([^`]+)`',l):
        p=re.split(r'\{([^{}]*)\}',t);X={''.join(x).split('.')[-1] for x in itertools.product(*[[q] if j%2==0 else q.split(',') for j,q in enumerate(p)])}
        if '{' in t and X&D or t.startswith('_') and any(d.endswith(t) for d in D): print(f'{f}:{i}: `{t}`')
  PY
  ```

## Lemma checklist (the round's task list)

One commit per task, in this order. Each line names the ledger IDs it acts on, its surfaces as at
the open (lines at `347ba9c4`; re-`grep` before editing), and *Expected*: the open's estimate of
gate 6, which the task makes exact before editing. Every task is at Opus but the close.

- [x] **1. Open** (docs only): this log, the baselines, the footprint, the L9 screen, `F-265`, the
  task list.
- [x] **2. The docstring-label check** (report §2.1; L10–L11): `scripts/check-docstring-labels.py`,
  gate 9; baseline 422, its rule under *Decisions*.
- [x] **3. L9: the Theorem 5.5 and Case I wrappers, the cycle forms** (`F-237`, `F-144`, `F-238`,
  `F-236`, `F-254`): fourteen deleted (`F-266`'s orphan); gate 9 409.
- [x] **4. L9: Case III's line route, the candidate rows, `case_III_realization`, `blockPiSpan`**
  (`F-232`, `F-258`, `F-264`): seventeen deleted (`F-267`'s orphan); gate 9 396.
- [x] **5. L9: `exists_good_realization_const`, `exists_finite_spanning_rigidityRows` and their five
  dead callers** (`F-265`; `F-256`, `F-233` in part): seven deleted, the two pins orphaned stay;
  gate 9 390.
- [x] **6. L9: `F-090`'s shim** (`F-090`): deleted, `cor:forest-surgery-deficiency` on
  `forest_surgery_split`; implied 2 424 → 2 430, no Lean basis 133 → 134; gate 9 390.
- [x] **7. `F-061`'s rename** (`F-061`; `F-233` in part): `_forest` to `_starForest`, the pins
  following; gate 9 388. The forest lemma is the phase's (c).
- [x] **8. L6–L7: the planar layer** (`F-013`, `F-017`, `F-021`, `F-024`): two `hab`, two
  `hF_finite`, `[Finite V]`; `lem:trivialMotionFamily-linearIndependent` restated; gate 9 388.
- [x] **9. L7: the pebble game's `hloops`** (`F-039`): derived from `himg`;
  `edgeListSorted_no_loops` gone.
- [x] **10. L6: the deficiency and the induction** (`F-075`, `F-077`, `F-092`, `F-094`): four
  binders, 26 call sites; `lem:deficiency-ear-merge` restated.
- [x] **11. L6–L8: the chain extraction** (`F-108`): the triangle the cycle's case $m = 3$;
  `lem:chain-data-extract` restated; new `F-270`.
- [x] **11.1. `F-270`'s cure** (docs only): `lem:cycle-zero-dof` to `deficiency.tex`; 1 526 edges.
- [x] **12. L6–L7 and S17: the algebraic induction** (`F-104`, `F-102`, `F-070`, `F-063`, `F-140`):
  `rigidContract_exterior_rank_transport` deleted, two statements restated; new `F-271`; gate 9 387.
- [x] **13. L8: one disjoint cover** (`F-055`): `lem:k-frame-forest-packing-of-sparse` restated;
  1 525 edges.
- [x] **14. L8: the descent calls the move** (`F-088` in part, `F-087`; new `F-272`):
  `lem:packing-move` restated; dead pins 168, unbacked transitive 85.
- [x] **15. L8: KT Lemma 4.8's shorter case** (`F-097` in part; new `F-273`):
  `lem:reduction-step-pos` and `lem:removal-deficiency-strict` restated; 1 526 edges, dead pins 172,
  implied 2 429, unbacked transitive 84.
- [x] **15.1. L6: task 15's lemma without its derivable vertex hypotheses** (new `F-274`; the
  siblings' `F-275`): the dump byte-identical; gate 9 387.
- [x] **16. L1–L2: the recon** (`F-033`, `F-047`; docs only): the spike closes; task 20 adjusted.
- [x] **17. L1: the search with one visited set** (`F-033` in part): `dropUntilBundle` deleted,
  `dfs.tex` restated; new `F-276` and `F-277`, both `reported`.
- [x] **18. L1: the timing script; the `decide` facts**: `scripts/DFSTiming.lean` (at $n = 18$,
  2196 ms per walk, 157 µs for the new search).
- [x] **19. L2: `parsePair` on any whitespace** (`F-047`): tabs and CRLF read.
- [x] **20. L1–L2: one rewrite of the texts** (`F-033`, `F-047`, both `done`): no bound claimed.
- [x] **21. Witnesses, 1: the planar and matroid rows**: `Nonvacuity.lean`, at `K₂` and the
  double edge with $k = 2$; `PHASE-BOUNDARIES.md` names the file.
- [x] **22. Witnesses, 2: the body-bar and body-hinge rows**: at the triple edge and `K₃`.
- [x] **23. Witnesses, 3: the molecular rows**: at the single and double edges and `K₁,₃`.
- [x] **24. Witnesses, 4: the molecule and Jacobs rows**: in 3-space, at `K₃`, `P₃` and the paw;
  none of the sixteen failed.
- *The docstring sweep, tasks 25–37, by directory.* Each docstring read against its body; each
  label it names checked by task 2's script; process narration (phase numbers, design codes,
  "brick", "producer", "seed", "genuine", "motive", "carry", "this commit") removed; credits as the
  chapters give them, checked against `.refs/`. *Expected* for each: the dump byte-identical; gate 9
  falls. Each entry's declarations are in its ledger text.
- [x] **25. The planar files** (`F-018`, `F-022`, `F-023`, `F-030`, `F-032` `done`; `F-025`,
  `F-228`, `F-200` in part): the nine files, credits Pollaczek-Geiringer and Laman, Jordán's and
  Whiteley's pages; no Lovász–Yemini but `TayTheorem.lean` 548 (task 27); the dump
  byte-identical; gate 9 387, none of its report's lines in these files.
- [x] **25.1. The planar files no task named** (`F-020` in part; new `F-278`): `Framework.lean`,
  `Henneberg.lean`, `HennebergReverse.lean`, `SparsityIComponents.lean`; the dump byte-identical;
  gate 9 387.
- [x] **25.2. `Search/` and `Mathlib/` but two files** (new `F-279`): `Search/DFS.lean` and 33
  files; the mirrors in mathlib's register; the dump byte-identical; gate 9 387.
- [x] **25.3. `Mathlib/LinearAlgebra/Matrix/Rank.lean` and `Dimension/Constructions.lean`**: the
  phase pointers gone, KT's equations (6.6), (6.16), (6.60)–(6.66) and Lemma 5.2's page checked in
  `.refs/`; `F-279` gains nine of `Rank.lean`; the dump byte-identical; gate 9 387.
- [x] **26. `PebbleGame/`** (`F-035`, `F-040`, `F-045`, `F-230` `done`; `F-279` in part): the four
  files and `Examples.lean`, which no task named; the three "verified-iterative" gone; task 20's
  running-time texts kept; `Quotient.lift` also in `DFS.lean` and `DESIGN.md`; the dump
  byte-identical; gate 9 381.
- [x] **27. `Matroid/` and `BodyBar/`** (M4's `F-053`; `F-057`; `F-215` but S13's part; `F-243`'s
  `BodyBar/GenericLift.lean` header; M2's `TayTheorem.lean` 548): `Matroid/Constructions/{Submodular,
  Union}.lean` (ported from `apnelson1/Matroid`; its credit stays), `BodyBar/{Framework, TayTheorem,
  BodyHinge, GenericLift}.lean`, and `KFrame.lean`, `TreePacking.lean`, which no task named;
  `F-025`, `F-057` `done`, `F-279` gains sixty-five; the dump byte-identical; gate 9 369.
- [x] **28. The square-graph and generic-rigidity files** (`F-176`, `F-198`, `F-200`, `F-205`
  `done`; the parts there of `F-186`, `F-194`, `F-210`, `F-244`): `GenericRigidityMatroid.lean`,
  `GeneralPositionPlacement.lean`, the five `Jacobs*.lean`, `SquareGraph.lean`, `TwoCore.lean`,
  `EdgesIn.lean`; credits Jacobs 1998, JJ 2008 and KT p. 650; `F-279` gains two; the dump
  byte-identical; gate 9 357.
- [x] **29. `Molecular/Deficiency.lean`, the first half** (`F-074`, `F-077` `done`; the parts there
  of `F-053`, `F-081`, `F-108`, `F-210`, `F-235`, `F-240`; new `F-280`): the header and the
  docstrings to `exists_cut_decomposition_of_not_twoEdgeConnected` (1711); credits KT 2011
  pp. 654–677; the dump byte-identical; gate 9 346.
- [x] **29.1. `Molecular/Deficiency.lean`, the rest** (`F-080`, `F-194`, `F-244`, `F-081`, `F-053`
  `done`; `F-250`, `F-210` in part; new `F-281`): from the tight partitions to the end, with a
  docstring for `rank_matroidMG_le`; credits JJ 2008 §§2–3, 5 and JJ 2010 Theorem 4.1(a); the
  dump byte-identical; gate 9 346 → 333.
- [x] **30. `Molecular/Induction/Operations.lean`** (`F-235` `done`; the parts there of `F-085`,
  `F-088`, `F-097`, `F-108`, `F-148`, `F-168`, `F-172`, `F-240`; new `F-282`): credits KT 2011
  pp. 658–698; `F-279` gains twenty-two; the dump byte-identical; gate 9 333 → 319.
- [ ] **30.1. `Molecular/Induction/` but `Operations.lean` and `ForestSurgery/`** (`F-094`; the parts
  in `ReducibleVertex.lean`, `Contraction.lean`, `SplitOffDeficiency.lean` and
  `SparseDeficiency.lean` of `F-085`, `F-088`, `F-097`, `F-104`, `F-236`, `F-238`). *Expected:* the
  dump byte-identical; gate 9 319 → 312 (its seven lines there).
- [ ] **31. `Molecular/Induction/ForestSurgery/`** (`F-092`; the parts there of `F-088`, `F-097`,
  `F-104`, `F-108`, `F-156`, `F-236`).
- [ ] **32. `Molecular/RigidityMatrix/`, `Meet.lean`, `Extensor.lean`** (`F-064`, `F-114`, `F-164`,
  `F-233`, `F-253`, `F-263`; the parts there of `F-153`, `F-161`, `F-168`, `F-225`, `F-232`, `F-242`):
  `infinitesimalMotions_mono_of_span_le` (`Basic.lean` 2522) and its sibling, not KT Lemma 5.2, the
  inclusion as `hspan` states it; `mem_hingeRowBlock_iff` (`Claim612.lean` 919) and the file's
  header: `def:hinge-row-block`'s, in `rigidity-matrix.tex`.
- [ ] **33. `AlgebraicInduction/` outside the footprint: `Pinning.lean`, `PanelLayer.lean`** (the
  parts there of `F-126`, `F-132`, `F-133`, `F-135`, `F-140`, `F-148`, `F-153`, `F-210` (the year),
  `F-233`, `F-237`, `F-238`, `F-254` (`isInfinitesimallyRigidOn_insert_iff`, 1611)).
- [ ] **34. The footprint: `CaseI.lean`, `CaseII.lean`, `GenericityDevice.lean`, `Coupling.lean`**
  (`F-069`, `F-256`: `exists_good_realization` (110), `_reindex` (139) and their section header are
  not `lem:genericity-device`'s; the parts there of `F-140`, `F-148`, `F-153`, `F-232`, `F-238`,
  `F-240`). Also the sentence task 7 rewrote in `exists_independent_panelRow_subfamily_of_rigidOn`'s
  docstring (`GenericityDevice.lean` 650–651): the star-forest rows number "at most `(D−1)(|V|−1)`
  in all, fewer than `D(|V|−1)`", which needs `|V| ≥ 2` (at `|V| = 1` both are 0; the
  coordinator's finding from task 7's diff, which named task 29's `Deficiency.lean`, whose
  rewritten sentence, a fraction `(D−1)/D`, holds).
- [ ] **35. The footprint: `CaseIII/`** (`F-156`, `F-172`, `F-241`; the parts there of `F-135`,
  `F-161`, `F-168`, `F-242`, and `F-264`'s if task 4 left any).
- [ ] **36. The footprint: `Theorem55.lean`, `PanelHinge.lean`, this round's parts** (`F-132`,
  `F-144`, `F-250`; the parts there of `F-126` (`HasFullRankRealization`, 1021;
  `HasGenericFullRankRealization`'s p. 670, 1075; the signature comments of
  `theorem_55_minimalKDof_k_all_k`), `F-104`, `F-135`, `F-140`, `F-148`, `F-153`, `F-161`,
  `F-237`, `F-238`). The parts that wait are *Moved to a later round*'s.
- [ ] **37. `Molecular/Molecule/`** (`F-182`, `F-190`, `F-245`, `F-246`; the parts there of `F-186`
  (`Modelling.lean`: the link is projective duality), `F-210`, `F-243`).
- [ ] **38. §B and §C, screened** (`CLEANUP.md` §B–§C; the ledger's baselines; `F-268`'s and
  `F-269`'s eight declarations and `F-271`'s `case_I_realization` through block (b); `F-275`'s
  derivable vertex hypotheses, `F-278`'s and `F-280`'s two each, `F-281`'s five and `F-282`'s nine,
  L6's, and `F-282`'s repeated derivation, L8's; `F-279`'s unused declarations). The smell
  counts again (`--base 347ba9c4 --rev HEAD --tree CombinatorialRigidity/`) beside the open's; each
  `@[nolint …]` and `set_option linter` site checked for its one-line justification (task 8 found
  that one of the seven bridge "false positives" `notes/ToolchainBumps.md` counts was a real unused
  binder, and dropped it: that note's "11 such sites in the tree today" is now 10 `grep` lines, 9
  sites, and the others want the same `lake lean` check); §C's ranking, the top ten walked with the
  four questions (expected no-op, §C's calibration). A fix found is a task appended before the
  close. *Expected:* docs only.
- [ ] **39. Close** (`CLEANUP.md` *Workflow* 5; Sonnet may take it). The axioms check with the
  witnesses; the build, `lake lint` and gates 5–10 at the last task's values; the script's report
  and the forward screen beside the open's; the smell counts; the ledger's dispositions, task
  numbers as shas, and its header's counts; the queue row `done = true`; ROADMAP's row ✓ and its
  RECONCILE bullet, and `notes/Reconcile.md`'s **Status**, pointing at `RECONCILE-FORMAL`
  (attended: the queue stops); and a proposal, for the PI, of whether task 2's check joins the
  project's gates for a commit that moves a pin (`CombinatorialRigidity/CLAUDE.md`).

## Candidates for the PI

`S` and `M` findings this round makes, one line each naming the ledger ID.

- `F-273` (task 15): `lem:reduction-step-pos`'s $D \ge 3$, which its pin now uses only as $D \ge 2$;
  the two are one condition on $D = n(n+1)/2$ (a `lake lean` witness), so a change would alter
  only the form. `hD` stays.
- `F-277` (task 16): `reachClosureComputable` by one search with `P` false, whose marked set is the
  region; it would restate `def:reachClosureComputable`, so the per-vertex body stays.

## Moved to a later round

Items outside this round's scope, one line each, mirrored in the same commit into
`notes/Reconcile.md` §3's list for the phase. All are the footprint's docstrings (*Scope*).

- `F-123` (L3; `PanelHinge.lean`): the field `ends` (S2), `rigidityMatrix_prop11`'s header and
  docstring (S18) with the JJ year beside it (`F-210`'s), and the docstrings of `withMomentNormals`
  and `ofParam`. The phase's (a).
- `F-130` (L4; `Theorem55.lean`): `molecular_conjecture`'s docstring and the KT Theorem 5.6 forms'
  (S2's rows). The phase's (a).
- `F-126` in part: `rankHypothesis_deficiency_of_theorem_55_d3`'s `_hSimple` and docstring
  (`cor:theorem-55-d3-spanning`, which the phase fixes). The phase's (a).
- `F-133` in part: the docstrings of `PanelHingeFramework.withGraph`, `toBodyHinge_withGraph` and
  `toBodyHinge_withNormal_pinnedMotions_eq` (the carrier's operations; the phase settles
  `withGraph`), and of `HasCoplanarPanelRealization` and `theorem_55_6_multigraph_of_two_le`. The
  phase's (a).
- `F-237` in part: `rankHypothesis_of_theorem_55_gen`'s docstring (S2's row). The phase's (a).
- `F-220`, and `F-210`, `F-225` and `F-243` in part: the docstrings of
  `GenericLift/PanelGeneric.lean` and `GenericLift/HingeGeneric.lean` (S1's refactor). The phase's
  (a).
- `F-215` in part: `exists_isGenericEndpoints_abundance`'s "`2n|E(G)|` endpoint coordinates"
  (S13, within S1's refactor). The phase's (a).

## Blockers / open questions

None.

## Hand-off / next phase

**Next: task 30.1**, at Opus: the docstrings of `ReducibleVertex.lean`, `Contraction.lean`,
`SplitOffDeficiency.lean` and `SparseDeficiency.lean` in `Molecular/Induction/` (4 214 lines; the IDs
and parts its checklist line names; under the sweep's rules and *Decisions*' sweep form).
*Expected:* the dump byte-identical; gate 9 319 → 312. Gates 1–3 (gate 3's witnesses: the sixteen
of `scratch/reconcile-lean/Witnesses-t30.lean`), 5, 6, 9 and 10 (the parent dump
`scratch/reconcile-lean/dump-t30.txt`, gitignored; regenerate it if missing). Task 30's screens
may serve (gitignored): `scratch/reconcile-lean/t30/unused_src.py` finds unused declarations from
the code, as the Lean cache counts a shared `_proof_N` auxiliary as a use, and `t30/binders.py`
lists named hypotheses absent from their proofs (`lake lint` missed two, `F-282`). Carried in:
`F-252`, `F-273`, `F-276` and `F-277` for the PI; `F-268`, `F-269`, `F-271`, `F-275`, `F-278` to
`F-282` and FRICTION's `edgeFiber_nonempty` (task 15) and count-matroid (task 21) entries for
task 38. After the round the queue stops before `RECONCILE-FORMAL`, which is attended.

## Decisions made during this round

- **The slicing** (the open): 39 tasks; code before the docstring sweep that documents it.
- **The footprint's measure** (the open): read from the Lean (block (a)), not the plan's count.
- **L9 by the screen** (the open): only with every caller, transitively, unpinned and dead (`F-265`).
- **`F-088` here** (the open): §3 gives L8's repeated derivations to this round, and G5's packing
  move in the phase's (c) is the same change, so task 14 takes it and the phase's list says so.
  Task 14: a conclusion strengthened so the caller can call it is L8's "repeated derivation
  replaced", as task 13's disjoint cover was; its node is restated in the same commit.
- **The label check's own node** (task 2): a pin's docstring names its node in its lead, so a lead
  naming nodes none of which pins it is reported; an unpinned declaration's own node is its lead
  parenthetical's first item when that is a bare label of its kind (`def:` for definitions,
  `lem:`/`thm:`/`cor:`/`prop:` for theorems). The house style leads pins and helpers alike with the
  node, so this also reports helpers (most of the 247): the sweep says, in that item, how a helper
  serves its node (`a step of <label>`), and gives a stale one its node or none. Section headers
  and line comments are read for absent labels only.
- **A deletion's screen covers what it orphans** (task 3): deleting the `Fin m` cycle forms left
  `eq_succ_of_isInfinitesimalMotion_cycle` (unpinned, dead) without a caller, so it went with them,
  as L9's "no caller outside themselves" covers (`F-266`); block (b) now lists such orphans (task 4,
  `F-267`). A signature change's orphan goes too, after block (b) and the trial deletion (task 9:
  `edgeListSorted_no_loops`, the discharge of a dropped hypothesis), and so does a consumer the
  change leaves a pass-through (task 12: `rigidContract_exterior_rank_transport`, whose hypothesis
  was `_htransport`'s dropped form).
- **The rename's name** (task 7): `_starForest`, the shape `hu` and `hsep` force (`F-061`).
- **A caller's binder the change leaves unused goes with it** (task 8): dropping `hF_finite` left
  `contradiction_one_pair`'s `[Finite V]` unused (it had passed `Set.toFinite _` for it), which
  `lake lint`'s `unusedArguments` reported; an unused hypothesis is the hygiene rule's, so it went, and
  `lake lint` runs to a fixed point (`notes/ToolchainBumps.md`: the linter cascades).
- **A pin more general than its node's setting** (task 10): a node that states a dropped hypothesis
  is restated (`lem:deficiency-ear-merge`'s distinct vertices, as task 8's finite $V$), but not
  where it is the setting a definition node fixes: `def:graph-operations` defines $G_v$ and
  $G_v^{ab}$ at a vertex of degree two, so `lem:edge-splitting`, `lem:forest-surgery-unsplit` and
  `lem:removal-deficiency-equality` keep it, stating a case of what their pins prove.
- **A forward missing edge** (task 11): a Lean change whose reach makes one gets an `E` entry and a
  cure task right after, a node moved so the edge points back (round 2's rule,
  `notes/Reconcile-statements-cleanup.md` *Decisions*), as gate 7 bars the forward `\uses`.
- **`F-097`'s `hD`** (the open; task 15): weakening `3 ≤ D` to `2 ≤ D` is a statement change
  beyond L8's suggestion. The shorter proof holds there, and the two are one condition on
  `bodyBarDim n`, so `hD` stays and `F-273` reports the form to the PI.
- **A `\uses` removed can strand an implied edge** (task 15): `lem:rigid-full-rank`, reached by the
  pin, was an ancestor only through the removed `lem:edge-set-indep-pos`, so the removal alone
  makes it missing. A task's *Expected* models the summary on the cache (`t15-model.py`) and adds
  such an edge in the same commit (backward here, 170 < 1793).
- **The search's fix** (tasks 16–17): one search threading a marked set, its completeness from
  closure under the arcs; `decide` stops at `List.mergeSort` and unexposed bodies (`F-276`).
- **The witnesses' form** (tasks 21–24): `CombinatorialRigidity.<name>_witness` in the
  non-`module` `Nonvacuity.lean`, at the smallest non-degenerate input of its row (the inputs in
  tasks 21–24's lines).
- **The texts' running time and `decide`** (task 20): a running time only as measured, naming
  the script, or no bound; `decide` only as the committed script's facts and `F-276`'s reasons. A
  claim on the line's subject that a re-`grep` finds beyond its surfaces is fixed in the same commit.
- **The sweep's form** (task 25): a header's process narration (a *Project context* section, phase
  and commit numbers, `notes/` pointers) becomes one sentence naming the blueprint section that
  presents the file; a credit is the chapter's, and one a docstring keeps beyond it (a page, a
  theorem number) is checked in `.refs/`; a docstring claim the body contradicts is fixed in the
  same pass and named in the commit. A hypothesis the sweep finds derivable or unneeded is a new
  `L` entry for task 38, not a signature change in a docstring task (task 25.1, `F-278`), and so
  is a declaration nothing uses (task 25.2, `F-279`). `Mathlib/`'s mirrors keep mathlib's
  register, with a pointer to the project file that uses a mirror (task 25.2).
