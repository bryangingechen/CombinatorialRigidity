# RECONCILE round 3/3 — `reconcile-lean`, the Lean outside the phase's footprint (work log)

**Status:** in progress (opened 2026-10-15). Round 3 of **RECONCILE**'s three autopilot rounds; the
plan and the PI's decisions are `notes/Reconcile.md`, and `.claude/autopilot/queue.toml` is the
authority for which rounds are done. The round acts on the Lean: a script that checks the blueprint
labels the docstrings name, L9's deletions after `CLEANUP.md` §B's trial deletion, `F-061`'s rename,
L6–L8's signatures and repeated derivations with S17, L1–L2 (the pebble game's search), a
non-vacuity witness for each of the 16 main results outside S1's and S2's rows, and the docstring
sweep by directory. No main result's statement changes. In the footprint (34 files: the 33 that
construct `PanelHingeFramework`, and `GenericLift/HingeGeneric.lean`) the docstrings that describe
the carrier or S1's and S2's theorems wait for the phase. Tasks 1–37.21 are done (*Current state*;
gate 9: 422 at task 2, 4 now), the docstring sweep with them, through `AlgebraicInduction/`,
`Molecular/Molecule/`'s top level and all of `Pencil/`, in import order.
**Next concrete task:** task 38, §B and §C screened over the round's `L` entries, docs only
(*Hand-off*). Round manual: `CLEANUP.md`.

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

**Task 37.21 is done**, the docstring sweep's last; nothing is mid-stream. **Next:** task 38.

**Task 37.21** (new `F-321`): `MainComponent/GenericTriangle.lean` and `Statements.lean`, neither
in the footprint, swept, each with a new header that describes the file; every pin's lead names its
node with no code, every other bold lead the node its declaration is a step of; gate 9 stays at 4.
Corrected: the extension's normals "independent on every closed hub-neighbourhood of `G`" (the Lean
asks it at the bodies of `V₁`), "`c`'s plane" (the panel of `c`), and in the assembly's comments
"the steered realization" for part (a)'s restriction (as task 37.20's) and an undefined `H`. The
ledger: 321 entries, 217 `done`, 9 `left`, 48 `reported`, 47 `open`. The build rebuilt 4 modules,
within the Bash tool's limit; the axioms harness's output is unchanged.

**Done before** (tasks 3–37.20; the ledger's dispositions name the task of each part, and the
messages carry the detail): L9's thirty-nine deletions (the pins they left without a caller stay
with their nodes), `F-090`'s shim, `F-061`'s rename, L6–L8's hypotheses and repeated derivations
(each node they reach restated in the same commit; gate 2 runs block (c) since task 5), the search
and its texts (tasks 16–20), `Nonvacuity.lean`'s sixteen witnesses (tasks 21–24; FRICTION: tasks
22–24's entries, task 21's waits for task 38), and the docstring sweep, a task per one to five files
in import order: every directory before the footprint (tasks 25–33), the footprint's files of
`AlgebraicInduction/` (tasks 34–36.2), `Molecule/`'s top level (tasks 37–37.1), and `Pencil/`'s top
level and `MainComponent/` to `GenericEar.lean` (tasks 37.2–37.20; new `F-301` to `F-320`).

**The docstring-label check** (`scripts/check-docstring-labels.py`, gate 9; its rule is its
docstring and *Decisions*): **422** at task 2 (39 *missing*, 136 *pinned, another node*, 247
*unpinned, own node*; `scratch/reconcile-lean/labels-t2.txt`, gitignored); its acceptance is
`65a5c0ee`'s message. Of the stale or absent labels `F-230`–`F-264` list, all are reported but
`runPebbleGame.aux`'s (past its lead; task 26 fixed it); a docstring naming no node is outside it.
The 4 left are in `GenericLift/` (S1's, the phase).

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
- **The footprint** (block (a) under *Scope*): 33 files whose declarations (257) name
  `PanelHingeFramework.mk` or one of the eight definitions returning one (`ofNormals`, `ofParam`,
  `withMomentNormals`, `withGraph`, `withNormal`, `Theorem55.lean`'s private `reaim`, `reaimSub`,
  `reaimSubLink`), and `GenericLift/HingeGeneric.lean`, 34. Under `Molecular/`:
  `AlgebraicInduction/{CaseI, CaseII, Coupling, GenericityDevice, PanelHinge, Theorem55}`,
  `CaseIII/{Arms, Candidate, Realization}`, `CaseIII/Relabel/{Arm, Basic, Chain, ChainColumn,
  ForkedArm}`, `GenericLift/{PanelGeneric, HingeGeneric}`, `Molecule/{Duality, GeneralPosition4,
  Modelling, Theorem56}`, `Molecule/Pencil/MainComponent/{Bridge, Carrier, Chain, Configuration,
  ContractAdditive, ContractCurve, Cut, Ear, EarGen, Flat, GenericBase, Orbit, Short, SplitOff}`.
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
- [x] **34–36. The footprint's `CaseI.lean`, `CaseII.lean`, `GenericityDevice.lean`,
  `Coupling.lean`, `CaseIII/`, `PanelHinge.lean`, `AlgebraicInduction/Nonvacuity.lean`** (new
  `F-290`–`F-296`), split by file.
- [x] **36.1. `Theorem55.lean` to the cut case** (`F-104`, `F-132` `done`; new `F-297`).
- [x] **36.2. `Theorem55.lean` from Case I on** (`F-144`, `F-238`, `F-250` `done`; `F-126`, `F-130`,
  `F-133` in part; new `F-298`).
- [x] **37. `Molecule/ScrewVelocity.lean`, `Duality.lean`, `ProjectiveInvariance.lean`,
  `Dictionary.lean`** (`F-182` `done`; `F-243` in part; new `F-299`).
- [x] **37.1. `Molecule/Carrier.lean`, `Application.lean`, `GeneralPosition4.lean`,
  `Theorem56.lean`, `Modelling.lean`** (`F-186`, `F-190` `done`; `F-210` in part; new `F-300`).
- [x] **37.2–37.21. `Molecule/Pencil/`'s top level and all of `MainComponent/`**, a task per one
  to three files in import order (`F-243`'s part there; `F-245`, `F-246` `done`; new `F-301` to
  `F-321`; `F-279` fifteen more; `F-122` in part; the messages name each task's files).
- [ ] **38. §B and §C, screened** (`CLEANUP.md` §B–§C; the ledger's baselines; `F-268`'s and
  `F-269`'s eight declarations and `F-271`'s `case_I_realization` through block (b); `F-275`'s
  derivable vertex hypotheses, `F-278`'s and `F-280`'s two each, `F-281`'s five, `F-282`'s nine,
  `F-283`'s six, `F-284`'s four, `F-285`'s three, `F-286`'s to `F-295`'s, `F-297`'s, `F-298`'s,
  `F-300`'s three, `F-303`'s four, `F-304`'s three, `F-307`'s eight, `F-308`'s two, `F-309`'s
  `[Finite α]`, `F-310`'s two over-strong hypotheses and repeated binder, `F-312`'s `hinj`,
  `F-313`'s unused conjunct, `have` and rewrite, `F-314`'s `have`, `F-316`'s `hle`, `hxfa` and
  `hxlb`, `F-317`'s two `hinj` and `hab`, `F-318`'s two `hinj`, `hab`, `_hv`, `obtain` and `have`s
  and `F-319`'s `hne`, `hv`, `hyu`, `hwy`, `hwu` and `_hG`, `F-320`'s two `have`s and `F-321`'s
  `hS`, two `have`s and two `hinj`, L6's, and `F-282`'s, `F-289`'s, `F-291`'s to `F-300`'s,
  `F-302`'s to `F-321`'s repeated derivations, L8's
  (`F-305`'s re-seeding and `F-306`'s `hubSlotNormal_ofCoord_toCoord` through block (b) and the
  trial deletion); `F-279`'s unused declarations; `F-298`'s four needless `set_option`s; `F-299`'s,
  `F-303`'s, `F-304`'s and `F-306`'s mathlib lemmas).
  The smell counts again (`--base 347ba9c4 --rev HEAD --tree CombinatorialRigidity/`) beside the
  open's; each `@[nolint …]` and `set_option linter` site checked for its one-line justification
  (task 8 found that one of the seven bridge "false positives" `notes/ToolchainBumps.md` counts was
  a real unused binder, and dropped it: that note's "11 such sites in the tree today" is now 10
  `grep` lines, 9 sites, and the others want the same `lake lean` check); §C's ranking, the top ten
  walked with the four questions (expected no-op, §C's calibration). A fix found is a task appended
  before the close. *Expected:* docs only.
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

**Next: task 38**, at Opus: §B and §C, screened (`CLEANUP.md` §B–§C), the docstring sweep being done
(tasks 25–37.21). Its inputs are its checklist line's, as they stand: the smell counts again beside
the open's (`scripts/cleanup-smell-sweep.py` with
`--base 347ba9c4 --rev HEAD --tree CombinatorialRigidity/`; the ledger's *Lean baselines*); each
`@[nolint …]` and `set_option linter` site and its one-line justification, with task 8's `lake lean`
check at the bridge sites; block (b) and §B's trial deletion for `F-268`'s and `F-269`'s eight
declarations, `F-271`'s `case_I_realization`, `F-279`'s unused declarations and L8's two (`F-305`,
`F-306`); the unused, derivable or over-strong hypotheses and the repeated derivations that the line
lists by entry (`F-275`, `F-278`, and `F-280` to `F-321` but `F-301`), and L6's; `F-298`'s four
needless `set_option`s and the mathlib lemmas of `F-299`, `F-303`, `F-304` and `F-306`; and §C's
ranking, the top ten walked with the four questions (expected no-op, §C's calibration). **The
smallest next commit:** the screen, docs only: its verdicts in this log and the ledger, and each fix
it finds appended to the checklist as a task before the close (38.1, 38.2, …, one commit each, a
Lean task with gates 1–3, and gate 4, §B's trial deletion, for a deletion). FRICTION's
`edgeFiber_nonempty` (task 15) and count-matroid (task 21) entries are read in the same screen. If
the screen does not fit one sitting, task 38 is §B (the counts, the suppression sites and block
(b)), and §C with the entries' verdicts is task 38.1; say so in this line. *Expected:* the dump
byte-identical; gate 9 at 4. Gates 5, 6, 9 and 10 (the parent dump
`scratch/reconcile-lean/dump-t3721.txt`, gitignored; regenerate it if missing); a fix task's gate 3
adds the sixteen witnesses of `scratch/reconcile-lean/Witnesses-t378.lean` and
`scratch/reconcile-lean/t36/MolWitness.lean`.

The whole-project build of an edit to a file the main results import can pass the Bash tool's 600 s
(task 37.9's did; tasks 37.5–37.8's and 37.10–37.21's, 4 to 24 modules, did not) and go to the
background, where it can be stopped at its own limit before it ends: wait for it in-turn (a
foreground loop on its log's exit marker, as task 37.9 did:
`for i in $(seq 1 110); do grep -q '^exit ' LOG && break; sleep 5; done`, with the build writing
`exit $?` to its log), and if it is stopped, run it again in the foreground, which finishes the jobs
left; one build at a time. The hook that blocks a commit adding a `sorry` also reads the prose words
"sorry" and "admit" in a `.lean` diff (task 37.4). `check-docstring-labels.py --lean` on a stale
Lean cache runs a fresh `lake lean` that rebuilds the edited modules: give it an explicit `timeout`
(task 37). A `lake lean` of a harness that imports `CombinatorialRigidity` rebuilds the edited
modules too: run it once the files are final and built, or against the parent's build with the
parent's copies of the edited files put back (task 37.7). The screens may serve (gitignored):
`t341/unused_joint.py` (unused declarations over several files at once; it misses a use written
`Name.mp` or `h.name.f`, so read its hits against the cache), `t33/info.py` (a module's
declarations, their pins, liveness, callers and the nodes they serve), `t321/codecmp.py` (a file's
code, comments stripped, unchanged), and the `Hyps-t*.lean` witnesses of tasks 29–37.21 (in
`scratch/reconcile-lean/` and its task directories; each entry's *Evidence* names its own), each a
trial of the proofs without the hypotheses or steps its entry names. Carried in: `F-252`, `F-273`,
`F-276`, `F-277` and `F-301` for the PI; `F-268`, `F-269`, `F-271`, `F-275`, `F-278` to `F-300`,
`F-302` to `F-321` and FRICTION's `edgeFiber_nonempty` (task 15) and count-matroid (task 21)
entries for task 38. After the round the queue stops before `RECONCILE-FORMAL`, which is attended.

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
- **The sweep's form** (task 25): a header's process narration (a *Project context* section, phase
  and commit numbers, `notes/` pointers) becomes one sentence naming the blueprint section that
  presents the file; a credit is the chapter's, and one a docstring keeps beyond it (a page, a
  theorem number) is checked in `.refs/`; a docstring claim the body contradicts is fixed in the
  same pass and named in the commit. A hypothesis the sweep finds derivable or unneeded, or a
  declaration nothing uses, is a new `L` entry for task 38, not a code change in a docstring task
  (tasks 25.1, 25.2). `Mathlib/`'s mirrors keep mathlib's register, with a pointer to the project
  file that uses a mirror (task 25.2).
- **A docstring the open moved whole** (task 36): kept as it stands but for its lead's label, which
  is this round's (*Scope*); the phase writes the rest once. A line comment in its declaration's
  body loses its codes, as the open moved docstrings, not comments (task 36.2).
- **A file nothing uses** (task 32.2): its docstrings are swept like any other, its header says that
  no node presents it and no declaration outside it uses its declarations, and `F-279` lists the
  file and the declarations its removal would leave without a caller, for task 38.
