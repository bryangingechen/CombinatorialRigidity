# RECONCILE round 3/3 — `reconcile-lean`, the Lean outside the phase's footprint (work log)

**Status:** in progress (opened 2026-10-15). Round 3 of **RECONCILE**'s three autopilot rounds; the
plan and the PI's decisions are `notes/Reconcile.md`, and `.claude/autopilot/queue.toml` is the
authority for which rounds are done. The round acts on the Lean: a script that checks the blueprint
labels the docstrings name, L9's deletions after `CLEANUP.md` §B's trial deletion, `F-061`'s rename,
L6–L8's signatures and repeated derivations with S17, L1–L2 (the pebble game's search), a
non-vacuity witness for each of the 16 main results outside S1's and S2's rows, the docstring
sweep by directory, and the §B–§C screen with the fixes it appends. No main result's statement
changes. In the footprint (34 files: the 33 that construct `PanelHingeFramework`, and
`GenericLift/HingeGeneric.lean`) the docstrings that describe the carrier or S1's and S2's theorems
wait for the phase. Tasks 1–38.3 are done (*Current state*; gate 9: 422 at task 2, 4 now): the
sweep, the §B–§C screen, whose fixes are tasks 38.2–38.27, and the first two of them.
**Next concrete task:** task 38.4, the deletions in `Pinning.lean`, `PanelLayer.lean` and
`PanelHinge.lean` (*Hand-off*). Round manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop (`notes/Reconcile.md` §4): the queue runs the three rounds unattended and stops
before `RECONCILE-FORMAL`. An unplanned `NEEDS_PI` entry goes here, newest first, and the PI
answers in an entry that starts `**PI, <date>:**`.

**PI, 2026-10-21:** The crash is mimalloc's, fixed from Lean v4.34.1 on. v4.34.0-rc2 bundles
mimalloc v3.4.1, which on macOS keeps each thread's heap in the reserved TSD slots 126 and 127, and
macOS 27 runs a destructor on slots 125–127 at thread exit (a C thread that leaves a static pointer
in one aborts; slots 89, 108 and 120 don't). When the thread `lake` runs `main` on ends, mimalloc
resets slot 126 to the static `_mi_theap_empty`, which libpthread then `free`s. `lean --run` aborts
the same way, so (c)'s bare `lean` is no safe stand-in, and (a) has no macOS fix to wait for:
mimalloc issue #1333 is this backtrace, fixed by v3.4.4, which v4.34.1 backports (lean4 #14938).
**Decision:** bump to Lean v4.36.0-rc1 (mimalloc v3.4.5), where `Matroid`'s tip `8ece630` sits,
with its mathlib `930ae14` (115 commits past the tag `v4.36.0-rc1`, 1 476 past our pin), whose
transitive pins are exactly `Matroid`'s; no `Matroid` rev since v4.29.0 sits on a stable release.
A new autopilot queue item ahead of this round, by `notes/ToolchainBumps.md`; then resume here at
task 34.1. More than (b)'s 1–3 commits: `ab64d1c` (hopscotch's issue #2) is in range, `Matroid` has
absorbed it, and our Lean meets the rest.

**2026-10-21, BLOCKED (answered above):** after macOS 27.0.1 every `lake` command of
`leanprover/lean4:v4.34.0-rc2` aborted after its output (exit 133). **Asked:** (a) fix the machine;
(b) bump to v4.34.1 first; (c) a stand-in gate of bare `lean`. Resolved: the bump closed 2026-10-21
(`notes/Bump-v4.36.0-rc1.md`).

## Current state

**Task 38.3 is done**, the deletions in `CaseI.lean`, `GenericityDevice.lean` and `Coupling.lean`
with `F-291`'s re-pointing and `F-290`'s two hypotheses; nothing is mid-stream. **Next:** task 38.4.

**Task 38.3** (scratch `scratch/reconcile-lean/t383/`, gitignored; `delete.py`, `blockb.py`,
`blockc.py` and `rmhdr.py`, which removes an emptied section header). Block (b) at `a1c4fe3a` gives
the line's 26 names unpinned, dead and uncalled from outside, and the one unpinned orphan; the five
pins stay, uncalled. `F-291`'s six were blocked only through the projected extraction, which now
calls the pinned `injOn` form without `hnev` (`reachdiff.py`: the Claim 6.4 pin's reach loses
`def:pinned-motions-on`'s pin, an ancestor, and gains `lem:extProj-preserves-rank-of-inter`'s, now
in its proof `\uses`). 33 declarations in four files, and `neworphans.py` finds none newly
uncalled but the five pins; `hne` and `hnesH` derived where used. The
`hr` of that extraction is now derivable: new `F-325`, task 38.16. Gates: the dump's one change,
`--summary` OK with `implied` 2432 → 2431 (case-i 156 → 155), the label check identical (4). The
ledger: 325 entries, 220 `done`, 9 `left`, 50 `reported`, 46 `open`.

**Tasks 38–38.1** (docs only; new `F-322`–`F-324`): §B's screen (the smell counts beside the open's,
the 30 suppression sites, block (b) over the dead declarations in task order: tasks 38.2–38.10) and
§C's (the top ten, each a no-op), and a verdict on each part of the `L` entries, in their ledger
dispositions: fixes merged into tasks 38.3–38.6 and 38.10 or appended as tasks 38.11–38.27.

**Done before** (tasks 3–38.2; the ledger's dispositions name each part's task, the messages the
detail): task 38.2's ninety deletions in `CaseIII/` and its orphans, L9's thirty-nine deletions, `F-090`'s shim, `F-061`'s rename, L6–L8's hypotheses and
repeated derivations (each node they reach restated in the same commit), the search and its texts
(tasks 16–20), `Nonvacuity.lean`'s sixteen witnesses (tasks 21–24), and the docstring sweep, a task
per one to five files in import order (tasks 25–37.21; new `F-278` to `F-321`).

**The docstring-label check** (`scripts/check-docstring-labels.py`, gate 9; its rule is its
docstring and *Decisions*): **422** at task 2 (`scratch/reconcile-lean/labels-t2.txt`, gitignored;
its acceptance is `65a5c0ee`'s message); the 4 left are in `GenericLift/` (S1's, the phase).

**Verified at the open** (2026-10-15, at `347ba9c4`, round 2's close tree; its Lean is that of the
ledger's Lean baselines), the values the close compares against: the build green (2996 jobs, 0
`warning:`, `error:` and `failed to cache artifact` lines) and `lake lint`; the axioms harness
`scratch/reconcile-lean/Axioms.lean` (gate 3's command) `cmp`-identical to round 2's, all 19 main
results `[propext, Classical.choice, Quot.sound]`; `lint.sh` green, `verify.sh` green with
`checkdecls` silent and **9** `WARNING:` lines, `print.log` **0** `LaTeX Warning` lines (31 overfull
boxes, not gated); the dump 3 609 lines, first lines **`1525 edges aa87ce11152366b1`** and
**`558613b168745717`** (`scratch/reconcile-lean/dump-open.txt`, gitignored), `--summary` both checks
OK (691 nodes, 689 pinned, 1 008 pins, 993 distinct, 169 dead pins, 0 missing edges); the
forward-`\uses` screen 33 edges at 17 nodes to a later file and 4 at 4 within a file
(`scratch/reconcile-lean/forward-open.txt`); the ledger's Lean baselines (`notes/Prose-findings.md`
*Lean baselines*: `cleanup-smell-sweep.py`, 152 files, 110 881 lines), which task 38 re-runs.
- **The footprint** (block (a) under *Scope*, which lists it): 33 files whose declarations (257)
  name `PanelHingeFramework.mk` or one of the eight definitions returning one (`ofNormals`,
  `ofParam`, `withMomentNormals`, `withGraph`, `withNormal`, `Theorem55.lean`'s private `reaim`,
  `reaimSub`, `reaimSubLink`), and `GenericLift/HingeGeneric.lean`, 34: under `Molecular/`, six of
  `AlgebraicInduction/`'s top level, all of `CaseIII/` (eight) and `GenericLift/` (two), four of
  `Molecule/`'s and fourteen of `Pencil/MainComponent/`'s.
- **The L9 screen** (block (b)) gave tasks 3–5 their 36 declarations and task 6 the shim, and kept
  the declarations that pinned or live ones reach (`F-265`'s message lists them).

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
- **Block (a), the footprint**: the declarations that name `PanelHingeFramework.mk` or one of the
  eight definitions returning one, read from `scripts/blueprint-deps.py`'s Lean cache by the open's
  script (in this log at `abcd9d72`, *Scope*).
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

- [x] **1–2. Open; the docstring-label check** (L10–L11; `F-265`): the baselines, the footprint,
  the L9 screen; `scripts/check-docstring-labels.py`, gate 9, 422.
- [x] **3–7. L9's deletions, `F-090`'s shim, `F-061`'s rename** (`F-237`, `F-144`, `F-238`, `F-236`,
  `F-254`, `F-232`, `F-258`, `F-264`, `F-265`, `F-256`, `F-233`, `F-090`, `F-061`).
- [x] **8–15.1. L6–L8 and S17** (`F-013`, `F-017`, `F-021`, `F-024`, `F-039`, `F-075`, `F-077`,
  `F-092`, `F-094`, `F-108`, `F-104`, `F-102`, `F-070`, `F-063`, `F-140`, `F-055`, `F-088`,
  `F-087`, `F-097`; new `F-270`–`F-275`; 11.1 `F-270`'s cure).
- [x] **16–20. L1–L2, the search and its texts** (`F-033`, `F-047`; new `F-276`, `F-277`;
  `scripts/DFSTiming.lean`).
- [x] **21–24. The sixteen witnesses** (`Nonvacuity.lean`; `PHASE-BOUNDARIES.md`); none failed.
- *The docstring sweep, tasks 25–37, by directory.* Each docstring read against its body; each
  label it names checked by task 2's script; process narration (phase numbers, design codes,
  "brick", "producer", "seed", "genuine", "motive", "carry", "this commit") removed; credits as the
  chapters give them, checked against `.refs/`. *Expected* for each: the dump byte-identical; gate 9
  falls. Each entry's declarations are in its ledger text.
- [x] **25–33. Before the footprint**: the planar files, `Search/`, `Mathlib/`, `PebbleGame/`,
  `Matroid/`, `BodyBar/`, the square-graph and generic-rigidity files, `Deficiency.lean`,
  `Induction/`, `RigidityMatrix/`, `Meet.lean`, `Extensor.lean`, `Pinning.lean`, `PanelLayer.lean`
  (new `F-278`–`F-289`; `F-279` lists the unused declarations).
- [x] **34–37.21. The footprint's `AlgebraicInduction/` files, `Theorem55.lean` (36.1–36.2),
  `Molecule/`'s top level (37–37.1), and `Pencil/` and `MainComponent/` (37.2–37.21)**, a task per
  one to five files in import order (new `F-290`–`F-321`; `F-104`, `F-132`,
  `F-144`, `F-182`, `F-186`, `F-190`, `F-238`, `F-245`, `F-246`, `F-250` `done`; `F-122`, `F-126`,
  `F-130`, `F-133`, `F-210`, `F-243` in part; the messages name each task's files).
- [x] **38–38.1. §B and §C, screened; the entries' verdicts** (docs only; new `F-322`–`F-324`):
  the deletions, re-seeding and suppressions appended as tasks 38.2–38.10, the fixes as 38.11–38.27.
- *Tasks 38.2–38.9, the deletions §B's block (b) found* (`F-279`'s task-38 paragraph and the
  dispositions of `F-268`, `F-269`, `F-271`, `F-305` and `F-306` give each name, its orphans and
  what stays). Each runs gate 4 first (block (b) on its names at its own tree; an orphan it reports
  goes too, a pinned or live one stays), then §B's trial deletion with gates 1–3, and gate 2's
  `grep` and block (c) over every deleted name, each live reference repointed or removed
  (docstrings, file headers' lists, `TACTICS-QUIRKS.md` and `DESIGN.md`, where a precedent may say
  "since deleted"). *Expected* for each: the dump and `--summary` unchanged (no pin reaches a
  deleted name), gate 9 at 4 or below.
- [x] **38.2. `CaseIII/`** (`F-268`'s `case_III_old_new_blocks`, `F-269`, `F-279`'s tasks 35–35.3):
  the 71 names and 19 orphans block (b) gave at `af9ad25b`, deleted; the two pins stay, uncalled.
- [x] **38.3. `CaseI.lean`, `GenericityDevice.lean`, `Coupling.lean`** (`F-268`'s other three,
  `F-271`'s two, `F-279`'s task 34.1; 26 names), and the orphan
  `isInfinitesimallyRigidOn_of_finrank_le_set` (`Pinning.lean`); five pins stay, uncalled. Then
  (task 38.1) `F-291`'s re-pointing and six deletions (gate 4), `lem:claim-6-4`'s proof gaining a
  `\uses` of `lem:extProj-preserves-rank-of-inter` (the dump's one change; gate 8), and `F-290`'s
  `hne`, `hnesH`. Done as planned, in one commit (new `F-325`).
- [ ] **38.4. `Pinning.lean`, `PanelLayer.lean`, `PanelHinge.lean`** (`F-279`'s tasks 33 and 36; 16
  names), and four orphans in `Pinning.lean` and `RigidityMatrix/Basic.lean`. Then (task 38.1)
  `F-289`'s eight hypotheses and two instances (`lem:theorem-55-base`, `lem:theorem-55-triangle`
  restated; gate 8) and `F-296`'s two re-proofs.
- [ ] **38.5. `RigidityMatrix/Concrete.lean` whole, and `Basic.lean`, `Claim612.lean`, `Meet.lean`,
  `Extensor.lean`** (`F-279`'s tasks 32–32.2 but `pluckerCoord_univ`; 99 names): the file and its
  imports in `CaseIII/Candidate.lean` and `CombinatorialRigidity.lean`, and twelve orphans in
  `Mathlib/LinearAlgebra/{Matrix/Rank,Dimension/Constructions}.lean` and `RigidityMatrix/Basic.lean`
  (two `nolint`s go with them); docstrings of `Rank.lean`, `PanelLayer.lean` and `Candidate.lean`
  name the file. Then (task 38.1) `F-287`'s `ha`, `hb` and `mem_hingeRowBlock_iff`'s move.
- [ ] **38.6. `Induction/`** (`F-279`'s tasks 30–31 and `candidateSeed_apply`; 30 names):
  `Operations.lean`, `ReducibleVertex.lean`, `Contraction.lean`, `ForestSurgery/EdgeSplitting.lean`,
  the orphan `shiftBody_isLink_succ_edge`, and `indep_matroidMG_of_noRigid_of_deficiency_pos` (task
  38.1, `F-282`: no orphan). The cache's caller of `shiftCycle_eq_cons` is a shared auxiliary proof.
- [ ] **38.7. `Molecule/`** (`F-279`'s tasks 37–37.15 but `Pair.lean`'s; 15 names):
  `ProjectiveInvariance.lean`, `Pencil/{Statement,Chart,Arms}.lean`,
  `Pencil/MainComponent/{ContractCurve,Lines,EarGen}.lean`; no orphan.
- [ ] **38.8. `Search/`, `PebbleGame/`, `Mathlib/`, `SquareGraph.lean`, `BodyBar/`** (`F-279`'s
  tasks 25.2–28 but the vendored port's and `spanningVerts_edgeMultiply`; 31 names), and three
  orphans in `PebbleGame/Basic.lean` and `Matrix/Rank.lean`.
- [ ] **38.9. L8's re-seeding** (`F-305`; `F-306`'s first part). Add the selector of a set of at
  most three members (`IsFin3SelectorOf`, `Pencil/Chart.lean`: by `Finset.toList`, injective by
  `List.Nodup.getElem?_inj`; the witness `t375/Hyps-t375.lean`) and re-prove
  `exists_pencilSeed_of_nondeg` (`Reseed.lean`, unpinned) from it,
  `exists_pencilSeed_of_nondeg_of_selectors` and `Motive.lean`'s two bounds; delete `Engine.lean`'s
  four re-seeding lemmas, the three helpers `F-305` names, and `range_cross₃L_eq_perp` if block (b)
  then orphans it. Re-prove `pencilChartPoint_ofCoord_toCoord` (`Steer.lean`) as
  `pencilChartPoint_congr` at `PencilSeed.ofCoord_toCoord_hubNormal` and `_fillHub` (the witness
  `t376/Hyps-t376.lean`) and delete `hubSlotNormal_ofCoord_toCoord`. No statement changes.
- [ ] **38.10. The suppression sites** (`F-322`; `F-298`'s four `set_option`s; the `[DecidableEq β]`
  of `F-281`–`F-283` and `F-285`), by `TACTICS-QUIRKS.md` §115 and `CombinatorialRigidity/CLAUDE.md`
  *Fix warnings at the source*. (a) Drop the `[DecidableEq β]`, its `set_option` and the sentence
  justifying it, and open the proof with `classical`, at
  `deficiency_eq_zero_iff_exists_spanningTrees`, `rigidContract_deficiency_eq`,
  `exists_isProperRigidSubgraph_of_three_le_degree`, `pencil_reduction` (and §115's precedent
  sentence on it), `rankHypothesis_of_theorem_55_d3`, `theorem_55_6_multigraph_gen`,
  `theorem_55_6_multigraph_d3`, `exists_molecular_rankHypothesis_generalPosition` and the two
  `exists_rankHypothesis_isGeneralPosition4` forms; a caller's binder left unused goes too (`lake
  lint` to a fixed point); a step that computes with the instance keeps its site by §115 rule 2, its
  reason written. (b) Drop only the `set_option` and its sentence at `F-298`'s four; the main
  results keep theirs (`F-323`). (c) Drop the `@[nolint unusedArguments]` and its comment at
  `finrank_realBlockPiSpanOn`, `exists_independent_panelRow_subfamily_of_le_finrank` and
  `trivialMotions` (its docstring's last clause), and update `notes/ToolchainBumps.md`'s count of
  such sites and its bullet expecting bridge false positives: on this toolchain the linter counts a
  bridge `have` as a use even when nothing uses it (`F-286`'s copies). (d) Break the header of
  `…_ofNormals_set_kdof` (`CaseI.lean`) after `theorem` (98 columns) and drop its `set_option`, or
  keep it with a one-line reason. (e) `GenericBase.lean`: `exists_mem_forall_eval_ne_zero` at
  `[Finite ι]` with the bridge; the primed theorem's proof moved into its pin after `have :=
  Fintype.ofFinite α`, and the primed theorem deleted (gate 4) with both `set_option`s. Gates 1–3;
  the nodes state no instance (gate 2's `grep` confirms). And (task 38.1) drop `F-300`'s
  `[Nonempty α]` at the same three theorems.
- *Tasks 38.11–38.27, the entries' fixes* (task 38.1), by file in import order; the dispositions of
  the entries a line names are its specification (the declarations, the hypothesis or step, what
  replaces it, the callers, the node to restate). One Lean commit each: gates 1–3 (gate 3 with the
  sixteen witnesses), `lake lint` to a fixed point, gate 2's checks (a restated node: the honesty
  gate; a deletion: gate 4 and block (c)), gates 5, 6, 8 (a restated node), 9 and 10. *Expected:*
  the dump byte-identical and `--summary` OK (`t381/reach.py` finds no pin reaching a new node); a
  re-proof that would add a forward `\uses` is left (gate 7), noted in its entry.
- [ ] **38.11. `HennebergReverse.lean`** (`F-278`): `hnone`, `hab`; callers in `LamanTheorem.lean`
  and `MatroidIdentification.lean`.
- [ ] **38.12. `Molecular/Deficiency.lean`** (`F-280`, `F-281`'s `deficiency_of_single_edge`): three
  hypotheses; `lem:cut-edge-decomposition` (1) restated.
- [ ] **38.13. `Induction/Operations`, `SplitOffDeficiency`, `Contraction`, `ReducibleVertex.lean`**
  (`F-282`'s eight, `F-283`'s five; `IsProperRigidSubgraph.three_le_ncard` added): nodes restated
  where they state a dropped hypothesis (`lem:claim-6-6` does).
- [ ] **38.14. `Induction/ForestSurgery/ChainExtraction`, `Reduction.lean`** (`F-275`'s first two,
  `F-284`, `F-285`): `lem:reduction-step`, `lem:forest-surgery-count` restated where they state
  them.
- [ ] **38.15. `RigidityMatrix/Bricks.lean`** (`F-286`): `_hE₁`, `honly`, three `[Finite β]`, two
  `nolint`s; `lem:block-rank-cut` restated; `notes/ToolchainBumps.md`'s count of `nolint` sites.
- [ ] **38.16. `CaseII.lean`, `GenericityDevice.lean`** (`F-290`'s `_hG_ea`, `F-291`'s rest): the
  rows' coordinatization as one lemma; rank–nullity and the single-body pin called. And `F-325`
  (`Coupling.lean`): the projected extraction's `hr`, derived from `hinter`, and its caller's
  `hr'`.
- [ ] **38.17. `CaseIII/Arms`, `Candidate`, `Realization.lean`** (`F-275`'s third, `F-289`'s last,
  `F-292`, `F-293`): seven hypotheses, `eq_add_one_of_bodyBarDim_eq_screwDim` twice, a lemma for
  `hGv_off` (eight sites), one for a chain's split at `vtx 1`.
- [ ] **38.18. `CaseIII/Relabel/`** (`F-294`, `F-295`): `hdeg2r` twice, `hV3`, two lemmas' `ab₁`,
  `ab₂`, a step's fourth conjunct, `perp_panelSupportExtensor_swap`; all unpinned.
- [ ] **38.19. `Theorem55.lean`** (`F-297`, `F-298`): `hV3` three times, `hLI_va`, `hLI_ab`,
  `hFcut`, and the `hD` of the seven declarations above the main result (`F-324`); four nodes
  restated where they state them.
- [ ] **38.20. `Molecule/ScrewVelocity.lean`, `Pencil/Chart`, `Arms`, `ArmsAssembly`,
  `Motive.lean`** (`F-299`, `F-279`'s `cross₃_…`, `F-303`, `F-304`): six re-proofs by existing
  lemmas, four `hD`, three weakenings, a degree lemma; `finrank_span_insert_le` deleted (gate 4).
- [ ] **38.21. `Pencil/Chart`, `Reseed`, `Steer.lean`** (`F-302`, `F-306`): the `IsFin3SelectorOf`
  injectivity lemma at four sites; one re-proof by mathlib.
- [ ] **38.22. `Pencil/Pair`, `Pair2`, `X0`, `MainComponent/GenericSteer.lean`** (`F-307`, `F-308`):
  seven hypotheses, one `have` for seven copies; `lem:pencil-generic-steer` (b) restated.
- [ ] **38.23. `MainComponent/`'s `Carrier` to `Ear.lean`** (`F-309`–`F-312`): a `K³` lemma at four
  sites, four re-proofs by existing lemmas, `[Finite α]`, a binder, `hinj`.
- [ ] **38.24. `MainComponent/`'s shared steps** (`F-311`'s `hendsI`, `F-316`'s `hcard`): a lemma
  each, at eight and six sites; no statement changes.
- [ ] **38.25. `MainComponent/ContractCurve`, `Chain`, `ContractAdditive`, `Lines.lean`** (`F-313`
  to `F-315`): two re-proofs, `closedNbhd_induce_subset` deleted (gate 4), an unused conjunct, three
  needless steps, `hevZ`.
- [ ] **38.26. `MainComponent/Short`, `Orbit`, `SplitOff`, `Coverage`, `CoverageChain.lean`**
  (`F-316`–`F-318`): lemmas for `hab` and for `hinj` at `Fin 2`, fourteen hypotheses, three unused
  steps, `h0`, `hlast`; six nodes restated where they state them.
- [ ] **38.27. `MainComponent/CoverageCut` to `GenericTriangle.lean`** (`F-319`–`F-321`): nine
  hypotheses, six unused `have`s, a lemma moved to `Motive.lean`, three on `pointJoin`; four nodes
  restated where they state them.
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
- `F-301` (task 37.2): `def:extensor-through-point`'s remark that the zero element passes through
  every point, true for $k \ge 2$ and false at $k = 1$ (a `lake lean` witness); the chapter uses
  only $k = 2$, so the remark could say $k \ge 2$.
- `F-323` (task 38): the `[DecidableEq β]` of three main results (`rankHypothesis_of_theorem_55_gen`,
  `molecular_conjecture`, `molecular_conjecture_multigraph`), which their types do not use and
  `classical` supplies; dropping it changes their statements, which the phase restates (S1, S2).
- `F-324` (task 38.1): `theorem_55_minimalKDof_gen`'s `hD : 3 ≤ D`, which `hk1` and `hn` give;
  dropping it changes a main result's statement (the phase, with `F-323`), and until then the
  derivable `hD`s of the chain it passes them down stay (`F-293`, `F-297`, `F-298`).

## Moved to a later round

Items outside this round's scope, one line each, mirrored in the same commit into
`notes/Reconcile.md` §3's list for the phase. All are the footprint's docstrings (*Scope*).

- `F-123` (L3; `PanelHinge.lean`): the field `ends` (S2), `rigidityMatrix_prop11`'s header and
  docstring (S18) with the JJ year beside it (`F-210`'s), and the docstrings of `withMomentNormals`
  and `ofParam` (task 36 gave their leads the node they serve). The phase's (a).
- `F-130` (L4; `Theorem55.lean`): `molecular_conjecture`'s docstring and the KT Theorem 5.6 forms'
  (S2's rows), kept but for their leads (task 36.2: their labels, no phase). The phase's (a).
- `F-126` in part: `rankHypothesis_deficiency_of_theorem_55_d3`'s `_hSimple` and docstring
  (`cor:theorem-55-d3-spanning`, which the phase fixes; task 36.1 gave its lead its node). The
  phase's (a).
- `F-133` in part: the docstrings of `PanelHingeFramework.withGraph`, `toBodyHinge_withGraph` and
  `toBodyHinge_withNormal_pinnedMotions_eq` (the carrier's operations; the phase settles
  `withGraph`; task 36 gave the last's lead its node), and of `HasCoplanarPanelRealization` and
  `theorem_55_6_multigraph_of_two_le` (task 36.2: their leads without codes). The phase's (a).
- `F-237` in part: `rankHypothesis_of_theorem_55_gen`'s docstring (S2's row). The phase's (a).
- `F-220`, and `F-210`, `F-225` and `F-243` in part: the docstrings of
  `GenericLift/PanelGeneric.lean` and `GenericLift/HingeGeneric.lean` (S1's refactor). The phase's
  (a).
- `F-215` in part: `exists_isGenericEndpoints_abundance`'s "`2n|E(G)|` endpoint coordinates"
  (S13, within S1's refactor). The phase's (a).
- `F-122` in part (S2's structure field): in each footprint file the sweep reaches, the sentences on
  what a selector records or asks and on what the carrier's constructors give, kept as they stand,
  true (tasks 34–37.13 and 37.15–37.18; none in tasks 37.14's and 37.20's files), and throughout,
  the selector of a generic full-rank realization, which gives each link its ends in some order (two
  such agree up to order).
  The per-file list is `F-122`'s disposition in the ledger (`notes/Prose-findings.md`). The phase's
  (a).

## Blockers / open questions

None. The 2026-10-21 toolchain blocker ended with the bump to Lean v4.36.0-rc1 (*Autopilot: for the
PI*).

## Hand-off / next phase

**Next: task 38.4**, at Opus (its line): the deletions in `Pinning.lean`, `PanelLayer.lean` and
`PanelHinge.lean` with their four orphans, then `F-289`'s eight hypotheses and two instances
(`lem:theorem-55-base` and `lem:theorem-55-triangle` restated; gate 8) and `F-296`'s two re-proofs.
Gate 4 first (block (b) on its names at its tree), then §B's trial deletion with gates 1–3, gate 2's
`grep` and block (c) over every deleted name (`t383/blockb.py`, `blockc.py`, `delete.py`, the last a
dry run unless `--apply`, `rmhdr.py` for an emptied section header, `grepall.py` for whole-name
mentions, and `neworphans.py` and `reachdiff.py`, which compare the parent's Lean cache with the
new one); *Expected* (made exact before editing): the deletions leave the dump and `--summary`
unchanged (the parent dump `scratch/reconcile-lean/dump-t383.txt`), a restated node's prose moves
no edge, gate 9 at 4 or below. If it does not fit one sitting, the deletions are 38.4 and the rest
38.4.1. Then tasks 38.5–38.27 in order, one commit each, then the close. A fix task's gate 3 adds
the sixteen witnesses of `scratch/reconcile-lean/Witnesses-t378.lean` and `t36/MolWitness.lean`
(task 38.3's harness of both: `t383/Axioms-wit.lean`).

A whole-project build after an edit the main results import can pass the Bash tool's 600 s (tasks
37.9's and 38.2's did) and go to the background: wait for it in-turn (a foreground loop on its log's
exit marker, `for i in $(seq 1 110); do grep -q '^exit ' LOG && break; sleep 5; done`, the build
writing `exit $?` to its log), and if it is stopped, run it again in the foreground (task 38.2's,
stopped at the background limit, finished on the rerun); one build at a time. The hook that blocks a
commit adding a `sorry` also reads the words "sorry" and "admit" in a `.lean` diff (task 37.4).
`check-docstring-labels.py --lean` on a stale cache, and a `lake lean` of a harness importing an
edited module, rebuild the edited modules: give each an explicit `timeout`, and run a harness once
the files are built (tasks 37, 37.7). The screens (gitignored): `t341/unused_joint.py` (it misses a
use written `Name.mp`), `t33/info.py`, `t321/codecmp.py`, the `Hyps-t*.lean` witnesses (each entry's
*Evidence* names its own), `t38/blockb2.py`, `t38/seq.py`, and `t381/q.py` (a name's pins, liveness
and callers) and `t381/reach.py` (the nodes a re-proof would make a pin reach). Carried in: `F-252`,
`F-273`, `F-276`, `F-277`, `F-301`, `F-323` and `F-324` for the PI. After the round the queue stops
before `RECONCILE-FORMAL`, which is attended.

## Decisions made during this round

- **The slicing** (the open): 39 tasks; code before the docstring sweep that documents it.
- **The footprint's measure** (the open): read from the Lean (block (a)), not the plan's count.
- **L9 by the screen** (the open): only with every caller, transitively, unpinned and dead
  (`F-265`).
- **`F-088` here** (task 14): G5's packing move is L8's repeated derivation, its node restated.
- **The label check's own node** (task 2): a pin's docstring names its node in its lead; an unpinned
  declaration's own node is its lead parenthetical's first item when that is a bare label of its
  kind, so the sweep says there how a helper serves its node (`a step of <label>`), or names none.
  Section headers and line comments are read for absent labels only.
- **A deletion's screen covers what it orphans** (tasks 3, 9, 12): a declaration a deletion or a
  signature change leaves without a caller goes with it, after block (b) and the trial deletion, and
  so does a consumer the change leaves a pass-through (`F-266`, `F-267`).
- **The rename's name** (task 7): `_starForest`, the shape `hu` and `hsep` force (`F-061`).
- **A caller's binder the change leaves unused goes with it** (task 8): `lake lint` runs to a fixed
  point (`notes/ToolchainBumps.md`: the linter cascades).
- **A pin more general than its node's setting** (task 10): the node is restated, except where a
  definition node fixes the setting (`def:graph-operations`).
- **A forward missing edge** (task 11): an `E` entry and a cure task right after (round 2's rule).
- **`F-097`'s `hD`** (task 15): `3 ≤ D` stays, one condition with `2 ≤ D` (`F-273`).
- **A `\uses` removed can strand an implied edge** (task 15): *Expected* models the summary on the
  cache (`t15-model.py`).
- **The search's fix** (tasks 16–17): one search threading a marked set (`F-276` for `decide`).
- **The witnesses' form** (tasks 21–24): `CombinatorialRigidity.<name>_witness` in the non-`module`
  `Nonvacuity.lean`, at its row's smallest non-degenerate input.
- **The texts' running time and `decide`** (task 20): a running time only as measured, or none.
- **The sweep's form** (task 25): a header's process narration becomes one sentence naming the
  blueprint section that presents the file; a credit is the chapter's, one kept beyond it checked in
  `.refs/`; a docstring claim the body contradicts is fixed in the same pass; a hypothesis found
  derivable or unneeded, or a declaration nothing uses, is a new `L` entry for task 38 (25.1, 25.2).
- **A docstring the open moved whole** (task 36): kept but for its lead's label; a line comment in
  its declaration's body loses its codes (task 36.2).
- **What the deletions leave** (task 38): a declaration that a chapter names as the Lean form of its
  prose, or that witnesses a chapter's claim, stays though nothing calls it; so does the vendored
  port's code (`DESIGN.md`: the rebased port stays whole for an upstream offer). Suppressions follow
  `TACTICS-QUIRKS.md` §115, a main result's binder going to the phase (`F-323`).
- **A file nothing uses** (task 32.2): swept like any other, its header saying so (task 38.5).
- **The entries' verdicts** (task 38.1): an unused hypothesis, `have` or step goes; a derivable one
  goes, derived where it was used, unless a later hypothesis's type reads it or a main result passes
  it on (`F-324`); an over-strong one is weakened only where a binder or a step goes or a chapter
  states the weak form, a change of form alone left (as `F-273`); a repeated derivation goes where
  an existing lemma, or one new lemma with a statement of its own, replaces two or more copies at a
  real saving, unless its re-proof adds a forward `\uses` (gate 7). A repetition inside one proof,
  or one that threads a proof's locals, stays (§C's calibration); so does a generalization needing a
  new proof (a lemma at any number of bodies).
