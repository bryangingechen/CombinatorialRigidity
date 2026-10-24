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
wait for the phase. Tasks 1–38.23 are done (*Current state*; gate 9: 422 at task 2, 4 now): the
sweep, the §B–§C screen, whose fixes are tasks 38.2–38.27, and the first twenty-two of them.
**Next concrete task:** task 38.24, `MainComponent/`'s shared steps (*Hand-off*). Round manual:
`CLEANUP.md`.

## Autopilot: for the PI

No planned stop (`notes/Reconcile.md` §4): the queue runs the three rounds unattended and stops
before `RECONCILE-FORMAL`. An unplanned `NEEDS_PI` entry goes here, newest first, and the PI
answers in an entry that starts `**PI, <date>:**`. A PI entry is never edited, shortened or
paraphrased, not even to bring this log under its line cap (tasks 35.1 and 38.4 did; each was
restored).

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

**Task 38.23 is done**, `F-309`, `F-310`, `F-312` and `F-311`'s first part, `MainComponent/Carrier`
to `Ear.lean`, no node restated; the new `F-328`. Nothing is mid-stream. **Next:** 38.24.

**Task 38.23** (scratch `scratch/reconcile-lean/t3823/`, gitignored: task 38.22's scripts, copied).
New: `LinearIndependent.eq_zero_of_forall_dotProduct_eq_zero` in the mirror
`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean` (no `lean_loogle` hit), at
`finrank_affineLifts`, `finrank_ker_liftingMatrix`,
`IsAdmissiblePicture.mem_liftingSpace_of_coplanar` and `finrank_liftingPlanes`; three copies in
later files are `F-328` (tasks 38.25–38.27). Dropped: `finrank_affineLifts`'s `[Finite α]` with its
`Fintype` `have`, and its caller `three_le_finrank_liftingSpace`'s, which fed nothing;
`finite_setOf_finrank_lt_of_curve`'s repeated `{k : ℕ}`; `mem_liftingSpace_oneEar`'s `hinj`
(`Function.injective_of_subsingleton`; the caller `X0Attains.of_splitOff` keeps its own, used
thrice). Re-proved: `hpath₂` as `isLink_pathVertex_rev hpath`, inline; `pathVertex_eq_or_exists`
from `pathVertex_cases`, moved above it; `panelSupportExtensor_mem_span_ofNormals` from
`span_supportExtensor_ofNormals_eq`; `span_supportExtensor_eq_top_of_linearIndependent` from
`card_le_finrank_of_linearIndependent_pointJoin`, moved above it. No node restated:
`lem:pencil-lifting-space-affine` states no instance, `lem:pencil-splitoff-ear-extension` no
injectivity. Gates: the build green on its first run (6147 jobs, 0 `warning:`, `error:`, `failed to
cache artifact`), `lake lint` green; the axioms harness and the witnesses' identical to task 38.22's
net of the exit line; the dump identical; `--summary` OK, 6608 constants (the mirror lemma in); one
pin's reach moved, the hinge-span lemma's, now through its sibling pin of the same node
(`lem:pencil-ear-hinge-span`); `neworphans.py` empty; the label check identical (4); `lint.sh`,
`verify.sh` green (9 `WARNING:`). The ledger: 328 entries, 258 `done`, 9 `left`, 50 `reported`, 11
`open`.

**Done before** (tasks 3–38.22; the ledger's dispositions name each part's task, the messages the
detail): tasks 38.11–38.22, the entries' fixes from `HennebergReverse.lean` to
`MainComponent/GenericSteer.lean` (new `F-325`–`F-327`, `TACTICS-QUIRKS.md` §118; seven nodes
restated); tasks 38.2–38.10's deletions,
re-seeding and suppression sites; tasks 38–38.1, the §B–§C screen and the verdicts (new
`F-322`–`F-324`); tasks 3–24, L9's deletions, `F-090`'s shim, `F-061`'s rename, L6–L8, the search
and `Nonvacuity.lean`'s sixteen witnesses; tasks 25–37.21, the docstring sweep (new `F-278` to
`F-321`).

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
- **The L9 screen** (block (b)) gave tasks 3–5 their 36 declarations and task 6 the shim
  (`F-265`'s message lists what it kept).

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

- [x] **1–24.** The open and the label check (L10–L11; `F-265`; gate 9, 422); L9's deletions,
  `F-090`'s shim and `F-061`'s rename (tasks 3–7); L6–L8 and S17 (tasks 8–15.1; new
  `F-270`–`F-275`, 11.1 `F-270`'s cure); L1–L2, the search and its texts (tasks 16–20; new `F-276`,
  `F-277`; `scripts/DFSTiming.lean`); the sixteen witnesses (tasks 21–24, `Nonvacuity.lean`,
  `PHASE-BOUNDARIES.md`; none failed). The ledger's dispositions name each entry's task.
- [x] **25–37.21. The docstring sweep, by directory**, a task per one to five files in import
  order (new `F-278`–`F-321`; the messages name each task's files, the ledger each entry's
  declarations).
- [x] **38–38.1. §B and §C, screened; the entries' verdicts** (docs only; new `F-322`–`F-324`):
  the deletions, re-seeding and suppressions appended as tasks 38.2–38.10, the fixes as 38.11–38.27.
- [x] **38.2–38.10. The deletions §B's block (b) found, L8's re-seeding, the suppression sites**
  (`F-268`, `F-269`, `F-271`, `F-279`, `F-287`–`F-291`, `F-296`, `F-298`'s four `set_option`s,
  `F-300`, `F-305`, `F-306`'s first part, `F-322`; new `F-325`): 90, 33, 20, 105, 32, 15, 33 and 12
  deletions with their orphans, `IsFin3SelectorOf`, and `TACTICS-QUIRKS.md` §115 at nine
  declarations (`theorem_55_6_multigraph_gen`'s binder kept by its rule 3, `F-323`). The messages
  and the dispositions name each declaration.
- *Tasks 38.11–38.27, the entries' fixes* (task 38.1), by file in import order; the dispositions of
  the entries a line names are its specification (the declarations, the hypothesis or step, what
  replaces it, the callers, the node to restate). One Lean commit each: gates 1–3 (gate 3 with the
  sixteen witnesses), `lake lint` to a fixed point, gate 2's checks (a restated node: the honesty
  gate; a deletion: gate 4 and block (c)), gates 5, 6, 8 (a restated node), 9 and 10. *Expected:*
  the dump byte-identical and `--summary` OK (`t381/reach.py` finds no pin reaching a new node); a
  re-proof that would add a forward `\uses` is left (gate 7), noted in its entry.
- [x] **38.11–38.23. The entries' fixes, `HennebergReverse.lean` to `MainComponent/Ear.lean`**
  (`F-275`, `F-278`–`F-286`, `F-289`–`F-295`, `F-297`–`F-299`, `F-302`–`F-312`, `F-325`–`F-327`, in
  whole or part; new `F-328`; `lem:cut-edge-decomposition` (1), `lem:claim-6-6`,
  `lem:block-rank-cut`, three Case I nodes and `lem:pencil-generic-steer` (b) restated). The
  messages and the dispositions name each task's declarations.
- [ ] **38.24. `MainComponent/`'s shared steps** (`F-311`'s `hendsI`, `F-316`'s `hcard`): a lemma
  each, at eight and six sites; no statement changes.
- [ ] **38.25. `MainComponent/ContractCurve`, `Chain`, `ContractAdditive`, `Lines.lean`** (`F-313`
  to `F-315`, `F-328`'s first): two re-proofs, `closedNbhd_induce_subset` and
  `eq_zero_of_dotProduct_pencilPicturePoint` deleted (gate 4), an unused conjunct, three needless
  steps, `hevZ`.
- [ ] **38.26. `MainComponent/Short`, `Orbit`, `SplitOff`, `Coverage`, `CoverageChain.lean`**
  (`F-316`–`F-318`, `F-328`'s `horth`): lemmas for `hab` and for `hinj` at `Fin 2`, fourteen
  hypotheses, three unused steps, `h0`, `hlast`, `horth` by task 38.23's lemma; six nodes restated
  where they state them.
- [ ] **38.27. `MainComponent/CoverageCut` to `GenericTriangle.lean`** (`F-319`–`F-321`, `F-328`'s
  last): nine hypotheses, six unused `have`s, a lemma moved to `Motive.lean`, three on `pointJoin`,
  `eq_zero_of_dotProduct_triple` by task 38.23's lemma; four nodes restated where they state them.
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
  `theorem_55_6_multigraph_gen`'s goes with `molecular_conjecture_multigraph`'s (task 38.10).
- `F-324` (task 38.1): `theorem_55_minimalKDof_gen`'s `hD : 3 ≤ D`, which `hk1` and `hn` give;
  dropping it changes a main result's statement (the phase, with `F-323`), and until then the
  derivable `hD`s of the chain it passes them down stay (`F-293`, `F-297`, `F-298`). So does that
  of the main result `isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees`
  (S1's row), which its `NeZero` step uses (task 38.19, `F-298`).

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

**Next: task 38.24**, at Opus (its line and the dispositions of `F-311` and `F-316` are its
specification; their other parts are task 38.23's, done, and 38.26's): one lemma for `hendsI`, that
a selector recording every link of `G` records every link of `G.induce X` (7 lines at each of the
eight `have hendsI`: `Cut.lean`, `Ear.lean`, `ContractAdditive.lean`, `Short.lean`, `Orbit.lean`),
and one for `hcard`, `|V₁ ∪ range z| = |V₁| + k` for an injective `z : Fin k → α` off `V₁` (a
`Mathlib/` mirror on `Set.ncard` unless mathlib has it), at its six sites (`Short.lean`, `Ear.lean`,
`Orbit.lean` three, `SplitOff.lean`); no statement changes. If the line does not fit one sitting,
split it at an entry boundary (the rest as 38.24.1), recorded here. Grep `blueprint/src/` for each
changed name. Left: the dispositions' own. Gates 1–3 (gate 3 with the sixteen witnesses, harness
`t3823/Axioms-wit.lean`), `lake lint` to a fixed point, gate 2's checks; gates 5, 6, 7 if a re-proof
adds a `\uses`, 8 for a restated node, 9 and 10. *Expected* (made exact before editing): the dump
unchanged (the parent `scratch/reconcile-lean/dump-t3823.txt`), `--summary` OK, gate 9 at 4; a pin
whose reach gains another pin is fine where its node already uses that pin's node (task 38.22's
steering lemma), and a re-proof that would add a forward `\uses` is left, noted in its entry
(`t381/reach.py`); a new lemma's docstring names its node (`a step of <label>`), a mirror's none,
its file's header naming its users (task 38.23). A disposition whose direction cannot hold is
applied the way that does, and its entry says so (task 38.16). A weakened hypothesis's callers pass
the weak form (task 38.20).
After each drop, read the callers' binders rather than trusting `lake lint`'s silence
(`TACTICS-QUIRKS.md` §118: it misses a binder that a `subst` or an `rfl` pattern reverts, and a
re-proof that removes such a `subst` can make the build report one, `F-326`): drop a caller's binder
or local `have` that fed only the dropped argument, following a pass-through up its callers (tasks
38.13, 38.19 and 38.20; task 38.22's `hS₁`), and inside each caller's proof a local `have`'s premise
that fed only it (task 38.14). A drop that turns `by … exact e` into the term `e` can expose an
unused lambda binder (task 38.13); a dropped `[Finite β]` can leave an `ncard` bound loose (task
38.15; both FRICTION idioms). A binder dropped from a callee can leave a main result's unused for
`lake lint` (task 38.10): check each caller that is a main result first (one that uses it elsewhere
keeps it, task 38.19).
Tooling, in `t3823/` (task 38.10's, copied): `blockb.py`, `blockc.py`, `delete.py` (a dry run unless
`--apply`; it cuts every declaration whose short name is listed, so a name two namespaces share is
cut by hand, and it leaves a preceding `omit … in`), `rmhdr.py`, `grepall.py`, `cols.py` (the
100-column check), `neworphans.py` and `reachdiff.py` (the last two compare the parent's Lean
cache, copied first, with the new one; `t3823/cache-new.jsonl` is task 38.23's; `reachdiff.py`
takes the pins to compare as arguments, `$(LC_ALL=C sort -u blueprint/lean_decls)` for all). Build
name lists with `LC_ALL=C sort -u` (a UTF-8 `sort -u` merges names that differ only in subscripts).
A live doc's mention of a deleted name says "since deleted"; a `[mirrored]` FRICTION entry whose
lemma goes is retired; closed notes, the frozen design docs and the ledger are history. A re-proof
that a deletion needs is built, and its Lean cache regenerated, before block (b) runs on the names
it frees (task 38.9); a definition moved off a file whose declarations still use it moves with their
deletion, not before. Then tasks 38.24–38.27 in order, one commit each, then the close.

A whole-project build after an edit the main results import can pass the Bash tool's 600 s (tasks
37.9's, 38.2's, 38.8's, 38.9's, 38.10's and 38.12's did; 38.4's to 38.7's and 38.13's to 38.23's,
from `RigidityMatrix/Basic.lean`, `Bricks.lean`, `Molecular/Deficiency.lean`, `Induction/`,
`Molecule/`, `AlgebraicInduction/GenericityDevice.lean`, `Theorem55.lean` or the matrix mirror
`NonsingularInverse.lean` up, did not)
and go to the background: wait for it in-turn (foreground loops of at most two minutes on its log's
exit marker, as `.claude/agents-core/phase-builder.md` says,
`for i in $(seq 1 22); do grep -q '^exit ' LOG && break; sleep 5; done`, the build writing `exit $?`
to its log), and if it is stopped, run it again in the foreground; one build at a time, so finish
every Lean edit, docstrings included, before the gates' build (tasks 38.12 and 38.13 built twice);
check the 100-column limit (Python `len`, `TACTICS-QUIRKS.md` § 55) after the last docstring edit,
before it (task 38.8). The hook that blocks a commit adding a `sorry` also reads the words "sorry"
and "admit" in a `.lean` diff (task 37.4). `check-docstring-labels.py --lean` on a stale cache, and
a `lake lean` of a harness importing an edited module, rebuild the edited modules: give each an
explicit `timeout`, and run a harness once the files are built (tasks 37, 37.7). The screens
(gitignored): `t341/unused_joint.py` (it misses a use written `Name.mp`), `t33/info.py`,
`t321/codecmp.py`, the `Hyps-t*.lean` witnesses (each entry's *Evidence* names its own),
`t38/blockb2.py`, `t38/seq.py`, and `t381/q.py` (a name's pins, liveness and callers) and
`t381/reach.py` (the nodes a re-proof would make a pin reach). Carried in: `F-252`, `F-273`,
`F-276`, `F-277`, `F-301`, `F-323` and `F-324` for the PI. After the round the queue stops before
`RECONCILE-FORMAL`, which is attended.

## Decisions made during this round

- **Settled before task 25** (the messages carry each): 39 tasks, code before the docstring sweep;
  the footprint read from the Lean (block (a)); L9 only with every caller, transitively, unpinned
  and dead (`F-265`); `F-088` as L8's repeated derivation (task 14); the rename `_starForest`
  (task 7, `F-061`); one search threading a marked set (tasks 16–17, `F-276`); the witnesses as
  `CombinatorialRigidity.<name>_witness` in `Nonvacuity.lean` (tasks 21–24); a running time only as
  measured (task 20).
- **The label check's own node** (task 2): a pin's docstring names its node in its lead; an unpinned
  declaration's own node is its lead parenthetical's first item when that is a bare label of its
  kind, so the sweep says there how a helper serves its node (`a step of <label>`), or names none.
  Section headers and line comments are read for absent labels only.
- **A deletion's screen covers what it orphans** (tasks 3, 9, 12): a declaration a deletion or a
  signature change leaves without a caller goes with it, after block (b) and the trial deletion, and
  so does a consumer the change leaves a pass-through (`F-266`, `F-267`). A definition's `rfl`
  lemma, which the screens leave out, is no caller: block (b) runs with it among the names (task
  38.9).
- **A caller's binder the change leaves unused goes with it** (task 8): `lake lint` runs to a fixed
  point (`notes/ToolchainBumps.md`: the linter cascades).
- **A pin more general than its node's setting** (task 10): the node is restated, except where a
  definition node fixes the setting (`def:graph-operations`).
- **A forward missing edge** (task 11): an `E` entry and a cure task right after (round 2's rule).
- **`F-097`'s `hD`** (task 15): `3 ≤ D` stays, one condition with `2 ≤ D` (`F-273`).
- **A `\uses` removed can strand an implied edge** (task 15): *Expected* models the summary on the
  cache (`t15-model.py`).
- **The sweep's form** (task 25): a header's process narration becomes one sentence naming the
  blueprint section that presents the file; a credit is the chapter's, one kept beyond it checked in
  `.refs/`; a docstring claim the body contradicts is fixed in the same pass; a hypothesis found
  derivable or unneeded, or a declaration nothing uses, is a new `L` entry for task 38 (25.1, 25.2).
- **A docstring the open moved whole** (task 36): kept but for its lead's label; a line comment in
  its declaration's body loses its codes (task 36.2).
- **What the deletions leave** (task 38): a declaration that a chapter names as the Lean form of its
  prose, or that witnesses a chapter's claim, stays though nothing calls it; so does the vendored
  port's code (`DESIGN.md`: the rebased port stays whole for an upstream offer). Such a witness is
  `coe_pairingDualEquiv` (task 38.8): `def:meet-pairing-dual` pins a `Basis.equiv` and states that
  the determinant map is an isomorphism, and only it proves the two are one map. Suppressions follow
  `TACTICS-QUIRKS.md` §115, a main result's binder going to the phase (`F-323`), and with it a
  callee's to which it passes that binder alone (task 38.10).
- **A file nothing uses** (task 32.2): swept like any other, its header saying so (task 38.5).
- **A disposition whose direction cannot hold** (task 38.16): `F-291` asked for the bound on a set
  `s` through the `V(G)` form, which cannot bound the motions of a framework rigid on another set;
  the derivation runs the other way, the `V(G)` form through the bound on `s`, and the entry says
  so.
- **The entries' verdicts** (task 38.1): an unused hypothesis, `have` or step goes; a derivable one
  goes, derived where it was used, unless a later hypothesis's type reads it or a main result passes
  it on (`F-324`); an over-strong one is weakened only where a binder or a step goes or a chapter
  states the weak form, a change of form alone left (as `F-273`); a repeated derivation goes where
  an existing lemma, or one new lemma with a statement of its own, replaces two or more copies at a
  real saving, unless its re-proof adds a forward `\uses` (gate 7). A repetition inside one proof,
  or one that threads a proof's locals, stays (§C's calibration); so does a generalization needing a
  new proof (a lemma at any number of bodies).
