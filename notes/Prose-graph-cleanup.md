# PROSE round 5/5 — `prose-graph`, graph repairs and the findings report (work log)

**Status:** in progress (opened 2026-10-13). Round 5 of **PROSE**'s five rounds; their plan and
the PI's decisions are in `notes/Prose.md`, and `.claude/autopilot/queue.toml` is the authority for
which rounds are done. The round acts on the 97 `E`, `N`, `T` and `U` entries of the ledger
`notes/Prose-findings.md` (40, 45, 7 and 5) under the expected-diff gate, sets every entry's
disposition, and reports its `S`, `L` and `M` entries to the PI. The open (task 1, docs only)
re-ran the audit script, reproduced round 4's gate values and triaged the entries into 31
one-commit tasks; task 2 added each node's `\uses` to the gate's dump, tasks 3.1–3.14 (task 3)
gave every node the ledger names its shape, and tasks 4.1–4.9 (task 4) added the missing edges of
every chapter, so the graph has none. Task 5, the node order, split by entry, is done: task 5.1
moved `F-019`'s theorem to the end of `sparsity.tex`, tasks 5.2–5.3 thirteen nodes after the nodes
they use, so that no edge of `deficiency.tex` or `molecular-induction.tex` points at a later
chapter, task 5.4 four blocks of the algebraic induction (`F-119`), and task 5.5 left `pencil.tex`'s
order, which only a regrouping would change. Task 6 aligned the terminology and notation of
`pencil.tex`, `main-component.tex`, `jacobs.tex` and `meet.tex`, and task 7 `README.md`, the home
page and `formalization.yaml` with the chapters. Task 8 wrote the findings report,
`notes/Prose-report.md`, which proposes the follow-up program RECONCILE (unqueued, in ROADMAP), so
every ledger entry has its disposition. No task edits the Lean or changes a statement's strength.
**Next concrete task:** task 9, the close (*Hand-off*). Round manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop: Stop 1 was the program's only one, in round 1 (`notes/Prose.md` §1). The
findings report (tasks 8.1–8.2) is not a stop; ORIGAMI is attended, so the driver stops after the
close, where the PI reads it. An unplanned `NEEDS_PI` entry goes here, newest first, and the PI
answers in an entry that starts `**PI, <date>:**`. No entries yet.

## Current state

**Task 8.2 has landed** (this commit; docs only, no TeX and no Lean): the report's Part 2, the 76
`L` entries in twelve items (L1–L12), the 6 `M` in five (M1–M5), the 19 `E` and `N` entries left
for a merge, a retirement, a pin change or a Lean change in six (G1–G6, with `F-012`'s liveness),
and a stale example in `blueprint/CLAUDE.md`'s honesty gate with a replacement (§2.6); Part 3, the
follow-up program RECONCILE, which ROADMAP lists unqueued for the PI. The ledger: `reported` on
the 82 `L` and `M` entries, and `F-012` `left`, so every entry has a disposition. Nothing is
mid-stream; the next task is task 9, the close.

**The gate's baseline, at task 8.2** (2026-10-15; the same as task 4.9's):
- `python3 scripts/blueprint-deps.py --dump` after `verify.sh`: **3 588 lines**, sha256 prefix
  **`2e4cbc2acd13d193`**, kept as `scratch/prose-graph/dump-<this commit's sha>.txt` (gitignored;
  regenerate it on this commit), byte-identical to task 4.9's, as at tasks 5.1–8.1. Task 9 keeps
  it byte-identical.
- `lint.sh` green; `verify.sh` green, `checkdecls` silent, 9 `WARNING:` lines; **`1501 edges
  11033da1dbaa0fae`** and **`8cdc1b9723e22064`**; `print.log` 0 `LaTeX Warning` lines and 31
  overfull boxes, the open's count; `--summary` exits 0, both consistency checks OK: 692 nodes,
  1 009 pins (999 distinct; `lean_decls` 1 010), **0 missing** in every chapter, 2 417 implied,
  84 + 145 unbacked, 177 dead, 12 nodes with four or more pins. Task 5 moved nodes between the
  chapter rows (task 5.4: `case-i` 24 nodes, 36 pins, 156 implied; `panel-layer` 39, 55, 203; the
  `case-ii` row after `genericity-and-count`'s). No node is drawn `#9CEC8B` (`F-007`).
- **The forward screen at task 5's end**, unchanged at tasks 6–8.2 (*Scope*; task 9 re-runs it
  beside the open's table):
  `rigidity-matroid` 2/2 0/0, `rigidity-matrix` 3/2 0/0, `molecular-induction` 0/0 2/2,
  `panel-layer` 10/4 1/1, `case-i` 14/6 0/0, `case-ii` 1/1 0/0 and `pencil` 3/2 1/1: 33 edges to a
  later file and 4 within a file, from task 4.9's 58 and 8. Each stays with its sentence and its
  reason: `F-029`'s two (task 5.1), `rigidity-matrix`'s three (task 5.2), `molecular-induction`'s
  two (task 5.3), `F-119`'s 26 (task 5.4) and `pencil`'s four (task 5.5).
  `scratch/prose-graph/t55/screen-after.txt` lists them (`t42/screen.py <tex-root> v`).

**Verified at the open** (2026-10-13, at `216e0702`, round 4's close tree):
- Whole-project `lake build` green: 2 996 jobs, 0 `warning:` and 0 `error:` lines (re-run, all
  cached; the coordinator's gave the same). **The no-Lean-edit base is `216e0702`**: the close
  checks that `git diff --stat 216e0702.. -- CombinatorialRigidity/ lakefile.toml
  lake-manifest.json lean-toolchain` is empty. The axioms check runs at the close (§2).
- Round 4's close values, reproduced exactly: `lint.sh` green; `verify.sh` green, `checkdecls`
  silent, **9** `WARNING:` lines; the invariance check **`1292 edges 673e3178d1b3145e`** and
  **`b53eb8b1cf78cb06`** (1 030 pins, 1 020 distinct); `print.log` **0** `LaTeX Warning` lines
  (31 overfull boxes, counted at the open and close, not gated); 657 nodes, 653 green and 4
  unfilled (`F-008`).
- **The baseline dump** (`--dump` after `verify.sh`): 2 614 lines, **`00604279e922bb0f`**; the
  open (`44e09c12`) changed no TeX, and its dump, regenerated at task 2, is the same bytes.
- **The script's report** (a fresh `--no-cache` run, 75 s, equal line for line to the cached
  one; both consistency checks OK): every count equals round 1's (`F-001`–`F-012`), since rounds
  1–4 changed no edge or pin. Per group, with the forward-`\uses` screen (*Scope*):

| Group | Chapters | Nodes | Pins | Missing | Implied | Unbacked (through a node / none) | Dead pins | 4+ pins | Forward `\uses` (later file / same file) |
|---|---|---|---|---|---|---|---|---|---|
| 1 | `sparsity` → `executable` (12) | 153 | 181 | 83 | 293 | 5 / 19 | 33 | 4 | 3/3 / 0 |
| 2 | `matroid-union` → `meet` (8) | 151 | 272 | 99 | 279 | 11 / 88 | 48 | 7 | 14/11 / 4/4 |
| 3 | `algebraic-induction`'s five sections | 106 | 152 | 164 | 473 | 32 / 120 | 80 | 2 | 18/10 / 6/4 |
| 4 | `bar-joint-3d` → `generic-lift` (5) | 95 | 152 | 76 | 267 | 22 / 21 | 22 | 6 | 0 / 0 |
| 5 | `pencil`, `main-component` | 152 | 272 | 114 | 710 | 17 / 62 | 19 | 9 | 3/2 / 1/1 |
| **total** | 32 files | 657 | 1 029 | 536 | 2 022 | 87 / 310 | 202 | 28 | 38/26 / 11/9 |

  The forward column counts `\uses` edges (node, target) to a later file, then to a later node of
  the same file, as edges/nodes. Three nodes have no pin (`F-008`), and one example pins a
  declaration (`F-007`), which is why `lean_decls` has one pin more than the nodes.

## Scope and standing rules

From `notes/Prose.md` §2–§4, restated as far as a builder needs them.

- **Surface.** Every chapter's `\uses` edges, `\lean{…}` pins, `\leanok` and node environments,
  `pencil.tex` and `main-component.tex` included (`retrospective.tex` is out); the prose a repair
  needs (a lead-in, a `\cref`, a note, a role map) and task 6's terms; `README.md`,
  `home_page/index.md` and `formalization.yaml` (task 7); the ledger's disposition lines; the
  report (tasks 8.1–8.2); `scripts/blueprint-deps.py` (task 2 only).
- **No Lean edits** (§2): `CombinatorialRigidity/`, `lakefile.toml`, `lake-manifest.json` and
  `lean-toolchain` stay untouched. A Lean docstring that names a moved label is an `L` finding.
- **The hygiene rule.** No task changes a headline statement or the strength of a blueprint
  statement; rounds 2–4's readings bind (`notes/Prose-applications-cleanup.md` *Scope*). A split
  moves each clause with the pin that proves it, at its strength. A node of a main result in
  `formalization.yaml` keeps its pins. A fix that needs a statement change is filed as a new `S`
  entry (from `F-230`), with its line under *Candidates for the PI*, and the finding is `left`.
- **Dispositions.** Each task adds the line `*Disposition:* done (task N) | left (<reason>) |
  reported` to every ledger entry it acts on (`notes/Prose-findings.md` *Format*); the close
  replaces task numbers by shas. An entry several tasks share is `done` at the last of them.
- **Gates for every commit**, each in the foreground with an explicit `timeout`:
  1. `blueprint/lint.sh` green.
  2. `blueprint/verify.sh` green: `checkdecls` silent, 9 `WARNING:` lines.
  3. **The expected-diff gate** (§3; it replaces the invariance check). (a) On the parent, after
     `verify.sh`: `python3 scripts/blueprint-deps.py --dump > scratch/prose-graph/dump-<parent>.txt`
     (the previous task's after-dump serves). (b) Before editing, write the expected diff in the
     task's checklist line: nodes added; `\uses` added, moved and removed; pins moved, added and
     removed; whether the `lean_decls` hash changes (a move keeps it; an added or removed pin
     changes it). (c) After: `verify.sh`, the dump again, and `diff` the two: the diff is exactly
     the listed changes, with the drawn edges those changes imply (the graph is a transitive
     reduction); the `## uses:` section (task 2) shows every `\uses` change, drawn or not, a line
     per changed node. (d) `python3 scripts/blueprint-deps.py --summary` exits 0, both consistency
     checks OK. Tasks 5–9 change no edge or pin: their dump is byte-identical.
  4. `blueprint/print/print.log` has 0 `LaTeX Warning` lines.
  5. `python3 notes/check-phase-note.py` green; it gates this log by its title.

  Every commit also updates this log: its checklist line, *Current state* and *Hand-off*.
- **The honesty gate for a new, split, repinned or newly filled node** (§3 *N*). It carries
  `\leanok` only if (i) every pin resolves (`checkdecls`) and its statement claims what its pins
  prove, each clause beside the pin that proves it; (ii) `blueprint/CLAUDE.md`'s honesty gate
  holds: each non-ambient hypothesis of each pin is discharged in its body or is the conclusion of
  a node it `\uses`, read from the pin's statement, and its `--label` report shows no missing
  statement edge; (iii) a definition node passes the definition-faithfulness gate (the cheapest
  witness); (iv) the node it came from still passes (i)–(ii) for what it keeps, and `\uses` the new
  node where its proof needs the moved clause. A split or a new node that fails is not made (the
  finding is `left`, with the reason); an unfilled node that fails stays unfilled.
- **Retargeting by the reach report** (§3 *N*). After a split or a pin move, every node that
  `\uses` the old node is re-read with `--label`: its edge goes to the node whose pins its own pins
  reach (on the statement if reached through the type); the edge to the old node stays if its pins
  still reach a pin left there, or its statement or proof prose uses a claim left there. Every
  `\cref` of the old label (`grep` over `blueprint/src/` and `notes/BlueprintExposition.md`) is read
  and pointed at the node whose claim its sentence cites. A new node gets a `\uses` for every node
  its pins reach that is not implied; other nodes' newly missing edges are the E tasks'.
- **The node-shape policy** (principle D, one choice per node, recorded in the task's line).
  - A pin that proves a clause of the node's statement, or defines the object it introduces, is
    not a helper. If the clauses are the parts of one source result (its enumerated parts and "in
    particular" restatements), the node is one result: *leave* it, with a role map in its note.
    If they are separate results (separate source numbers, or results that other nodes use
    separately), *split* it along them.
  - A pin that is neither (a proof step, an accessor, a generic helper) is *unpinned*, and the
    proof names it as an address (principle C). A definition pinned beside a claim moves to a
    definition node, existing or new, where the reader's term is defined (principle E).
  - Deadness (`F-012`) alone is no reason to unpin or retire. A dead node stays as exposition; one
    whose claim a live general form states is repinned on it. Merging or retiring nodes is not
    among principle D's fixes: such candidates are `left`, and task 8.2 lists them.
  - "A load-bearing unpinned lemma gets a node where the ledger recommends it" (§3): where the
    entry names the node as a candidate. Elsewhere the proof names the declaration as an address.
- **The edge policy** (§3 *E*).
  - Add every edge that the parent's report lists as *missing* in the task's chapters: on the
    statement if tagged *statement*, on the proof if tagged *proof* (a definition's body reach goes
    on its statement). Not an *implied* edge, nor one that would close a cycle.
  - Add an edge to a node that the statement or the proof prose cites for a step the argument
    uses: the ledger's "cites without an edge" lists, rechecked against the current text. A node
    cited for a comparison, or as an argument followed, gets none (`F-175`).
  - Move a statement edge that only the proof uses to the proof (`F-089`, `F-095`, `F-105`).
  - Remove an *unbacked* edge only when neither the statement, the proof prose nor the pins use
    it, and record each removal's reason in the commit message.
  - An edge that points forward stays, for task 5.
- **The forward-`\uses` screen** (the table's last column; re-run by tasks 5 and 9). It is round
  4's second screen over every file that `chapter/main.tex` inputs:
  ```sh
  python3 - <<'PY'
  import re
  R='blueprint/src/'; C=lambda f: f.split('/')[-1].removesuffix('.tex')
  def ex(f): return sum(([g]+ex(g) for g in (m+'.tex'*(not m.endswith('.tex')) for m in re.findall(r'^\s*\\input\{([^}]*)\}',open(R+f).read(),re.M))),[])
  F=ex('chapter/main.tex'); T={f:re.sub(r'(?<!\\)%.*','',open(R+f).read()) for f in F}
  W={m.group(1):(i,m.start()) for i,f in enumerate(F) for m in re.finditer(r'\\label\{([^}]*)\}',T[f])}
  for f in F:
      i=F.index(f); X=[set(),set()]
      for s in re.split(r'\\begin\{(?:definition|lemma|theorem|corollary|proposition)\}',T[f])[1:]:
          s=re.split(r'\\begin\{(?:remark|example|fmlnote)\}',s)[0]; m=re.search(r'\\label\{([^}]*)\}',s)
          if not m: continue
          for u in (u.strip() for x in re.findall(r'\\uses\{([^}]*)\}',s) for u in x.split(',')):
              j,p=W.get(u,(-1,0)); k=0 if j>i else 1 if j==i and p>W[m.group(1)][1] else -1
              if k>=0: X[k].add((m.group(1),u))
      if X[0] or X[1]: print(C(f),*(f'{len(x)}/{len({n for n,_ in x})}' for x in X))
  PY
  ```
- **Evidence.** Claims about the Lean come from declarations' statements and bodies, never from
  docstrings, and from `scripts/blueprint-deps.py --label` or `--chapter` for what a pin reaches.
- **Rungs** (§2): every task at Opus, a fresh agent per task; the close may run at Sonnet.

## Lemma checklist (the round's task list)

One commit per task, in this order. Each line gets its commit's sha; the commit, with this log as
of that commit, carries the task's exact list. A task's findings are named by ID; "leave" means
the disposition `left`, with the reason given here. "Expected" gives the open's estimate of the
gate's diff, which each task makes exact before editing.

- [x] **1. Open** (`44e09c12`; docs only): this log, the baselines, the triage.
- [x] **2. G — the gate's tooling** (`18400dc9`; `scripts/blueprint-deps.py`): `--dump` gains the
  `## uses:` section, each node's `\uses` read from the TeX, statement and proof apart; no TeX,
  edge or pin change (its *Expected* is in its commit).
- [x] **3. N — node shape**, chapter by chapter, before E (an N fix changes what the report calls
  missing). Each commit carries its task's exact list, and its title the nodes it added: 3.1
  round 1's chapters `7b2a8272`; 3.2 `matroid-union` → `meet` `56fb8b8c`; 3.3 `rigidity-matrix`
  `a7b8ea35`; 3.4 `deficiency`, operations `8e6786d3`; 3.5 KT Lemmas 4.4–4.9 `20d62426`; 3.6
  `panel-layer` `1d35d435`; 3.7 `case-i` `d851de0f`; 3.8 `case-ii`, `genericity-and-count`
  `657f3483`; 3.9–3.10 `case-iii` `24f04215`, `258e9e73`; 3.11 `molecule-modelling` →
  `generic-lift` `dd34a61e`; 3.12 `jacobs` `ae31af3e`; 3.13–3.14 `pencil`, `main-component`
  `24251386`, `0f9c275c`.
- [x] **4. E — edges**, one commit per chapter group, each listing the `\uses` it adds, moves and
  removes, pins and `lean_decls` unchanged: 4.1 round 1's chapters `9eb2c776`; 4.2
  `matroid-union` → `deficiency` `3575835c`; 4.3 `molecular-induction`, `meet` `eaba775e`; 4.4
  `panel-layer`, `case-i` `6af43988`; 4.5 `case-ii`, `genericity-and-count` `1096d2d9`; 4.6
  `case-iii` `e1b16939`; 4.7 round 4's chapters `e9d59672`; 4.8–4.9 `pencil`, `main-component`
  `23bf8244`, `60c88e44`.
- [x] **5. N — node order** (`F-019`, `F-029`, `F-050`, `F-076`, `F-119`; one commit per entry):
  5.1 `76c3c4d4` (`F-019` done, `F-029` left), 5.2 `9a7e56b1`, 5.3 `90b68fd1` (`F-050`, `F-076`
  done; `F-250` new), 5.4 `2ecbd37d` (`F-119` done), 5.5 `b384225a` (`pencil.tex`'s order left).
  Each commit's log carries its moves and the edges it left; 33 edges to a later file and 4 within
  a file stay (*Current state*). The dump byte-identical throughout.
- [x] **6. T — terminology and notation** (`04ed99ec`, follow-up `34f61fd9`; `F-056`, `F-067`,
  `F-072`, `F-073`, `F-127`, `F-203`, `F-227`, all done): KT's $d$ and $\vee$ in `pencil.tex` and
  `main-component.tex`, the two cores told apart, `meet.tex`'s items plain. The dump byte-identical.
- [x] **7. U — status surfaces** (`30c4b950`; `F-099`, `F-173`, `F-204`, `F-226`, `F-229`,
  `F-231`, all done): `formalization.yaml`, `README.md` and `home_page/index.md` aligned with the
  chapters they name, `F-229`'s phrases on all three, Jacobs 1998's DOI (Crossref); no
  `declaration:` changed, `F-025`'s lines left for task 8.2; the dispositions carry the rest. The
  dump byte-identical to `34f61fd9`'s, the screen unchanged.
- [x] **8. R — the findings report** (`notes/Prose.md` §3 *R*), `notes/Prose-report.md`; not a
  stop. 8.1 `f6ddebb5`: Part 1, the 67 `S` entries in eight kinds and 42 items, 65 `reported`
  (`F-137`, `F-142` stay `done`). 8.2 (this commit; 76 `L` and 6 `M`, recounted): Part 2, twelve
  `L` items, five `M` items, the 19 graph findings left (G1–G6, `F-012` given `left`) and §2.6's
  honesty-gate example with a replacement (`lem:case-III`; no agent manual edited); Part 3 and an
  unqueued ROADMAP bullet, RECONCILE; 82 `reported`. No TeX: the dump byte-identical.
- [ ] **9. X — close** (`CLEANUP.md` *Workflow* 5; docs only; Sonnet allowed). The axioms check
  on `formalization.yaml`'s main results (`[propext, Classical.choice, Quot.sound]`, byte-identical
  to round 1's open); the no-Lean-edit check from `216e0702`; every ledger entry has its
  disposition, task numbers replaced by shas; the script's report and the forward screen re-run
  beside the open's table; `notes/BlueprintExposition.md`'s pointers to moved or split nodes
  checked; the queue row `done = true`; the ROADMAP row ✓; ROADMAP's PROSE bullet and
  `notes/Prose.md`'s **Status**.

## Candidates for the PI

`S` and `M` findings this round makes, one line each naming the ledger ID. The ledger's earlier
`S` and `M` entries are task 8's.

- `F-234` (task 3.4): `lem:forest-surgery-unsplit` states a forest form that no declaration
  proves, and it fails at $D = 1$.
- `F-239` (task 3.8): `lem:case-II-placement-old-rows-extract` and
  `lem:case-II-placement-block-independent` state special cases of pins cited in general.

## Moved to a later round

`L` findings this round makes (a later Lean round), one line each naming the ledger ID. The
ledger's earlier `L` entries are task 8.2's. Task 8.2 mirrored all of them into the follow-up's
plan: `notes/Prose-report.md` L9 and L11, and Part 3's Lean round (RECONCILE).

- `F-230` (task 3.1): three pebble-game docstrings name the nodes their pins left.
- `F-232` (task 3.2): docstrings of moved or unpinned declarations, and the dead code among them.
- `F-233` (task 3.3): the same for `rigidity-matrix.tex`'s moved pins, and a stale docstring claim.
- `F-235` (task 3.4): the same for task 3.4's moved and unpinned pins, and `inducedSpan`'s.
- `F-236` (task 3.5): the same for task 3.5's moved pins, and `CycleData.vertexSet_ncard`'s.
- `F-237` (task 3.6): the five dead $d = 3$ base wrappers task 3.6 unpinned, and three docstrings.
- `F-238` (task 3.7): the dead cycle forms and $d = 3$ wrapper task 3.7 unpinned, and docstrings.
- `F-240` (task 3.8): docstrings of task 3.8's pins, and a stale one of
  `splitOff_simple_of_noRigid`.
- `F-241` (task 3.9): docstrings of task 3.9's pins name no node, or a label the blueprint lacks.
- `F-242` (task 3.10): docstrings of task 3.10's pins, a stale "dead", and the unpinned $d = 3$
  wrapper.
- `F-243` (task 3.11): docstrings and module headers that name the nodes task 3.11's pins left.
- `F-244` (task 3.12): docstrings of task 3.12's moved pins name the lemmas they left, a label
  the blueprint lacks, and "this commit".
- `F-245` (task 3.13): a `Pencil/Chart.lean` docstring names `lem:pencil-nondegenerate`, a label
  the blueprint lacks.
- `F-246` (task 3.14): the docstring of `Graph.embedEdges` names the lemma its pin left, and a
  module header lists a pin task 3.14 unpinned.
- `F-250` (task 5.3): two docstrings place the moved KT Lemma 6.1 and tight-partition nodes in
  their old chapters.

## Blockers / open questions

None.

## Hand-off / next phase

**Next concrete task: task 9, the close** (docs only; Sonnet allowed; one commit), as its
checklist line lists: the axioms check of `formalization.yaml`'s main results against round 1's
open; `git diff --stat 216e0702.. -- CombinatorialRigidity/ lakefile.toml lake-manifest.json
lean-toolchain` empty; every ledger entry's disposition with its task numbers replaced by shas
(the ledger's *Format*; `F-247`–`F-249`'s "task 8.2 lists it" names this commit), and none
missing (task 8.2 left none); the script's report and the forward screen re-run beside the
open's table; `notes/BlueprintExposition.md`'s pointers to moved or split nodes checked; the
queue row `done = true` (not RECONCILE's: the PI queues it); the ROADMAP row ✓, ROADMAP's PROSE
bullet and `notes/Prose.md`'s **Status**. No TeX: the dump stays byte-identical to task 7's.

## Decisions made during this round

- **The slicing** (the open): 31 tasks; the order is the tooling, N, E, the node order, T, U, R, X.
  Task 5 is split by entry into 5.1–5.5 (tasks 5.1–5.2), as task 4 was by chapter group.
- **The `## uses:` section** (task 2): every labelled environment with a `\uses`, parts sorted.
- **The report's home** is `notes/Prose-report.md`; the ledger keeps each finding. Parts 1–2 rank
  the entries in kinds and items, and each `S`, `L` and `M` disposition names its item; Part 2's
  graph items (G1–G6) list the `left` entries, and `F-012`'s disposition points at G6. The
  follow-up, RECONCILE, is a ROADMAP bullet and the report's Part 3, not a queue row (task 8.2).
- **Try each change on a scratch copy, and predict the whole dump** (tasks 3.1–3.2). Edit a copy
  of `blueprint/src`, read its `--tex-root` report, and predict the after-dump with
  `predict-dump.sh` (the script's `ancestors_map` and `transitive_reduction` and leanblueprint's
  colorizers; exact since task 3.2). An edge is dashed when its source is in the user's statement
  `\uses`; a node with a remark among its `\uses` ancestors is drawn `#9CEC8B` (task 4.3 ended it).
- **Task 3's node-shape verdicts** (done): each commit has its entry; *Scope* states the rules.
- **A pin two nodes share leaves an edge the script cannot back** (task 3.14). The script skips a
  node's own pins, so an edge to a node whose pin the user shares reads as unbacked. It stays, as
  the user's clause is the other node's claim (`thm:pencil-x0-main-component`'s three, task 4.8;
  `thm:pencil-x0-generic-attains` -> `lem:pencil-x0-distinct-statement`, task 4.9;
  `lem:reduction-step` -> `lem:contraction-minimality`); a merge (task 8.2) would remove the double.
- **The edge policy's mechanics** (tasks 4.1–4.9). A missing edge that the task's other additions
  imply is not added (the report's *implied*, applied after the task); the split rule counts
  missing edges. An edge a removal leaves missing is added at its node, in any chapter, and
  `t43/cites.py` (with the ledger's lists, the source of cited steps) is re-run on the copy: a
  citation a removal leaves with no ancestor takes an edge. A definition's well-definedness
  paragraph is its proof prose; a definition with a proof takes a pin's body reach there. A missing
  edge drawn by a pinned proof step, or a definition pinned on another's node, is added and the pin
  filed (`F-247`–`F-249`). A remark in a node's `\uses` becomes a `\cref` in its proof (`F-007`).
- **What keeps an unbacked edge** (tasks 4.1–4.9): a use by the pins, transitive ones included, or
  by the text (a symbol, object or conclusion the statement takes, a step the proof cites); the
  commits `9eb2c776`–`60c88e44` carry each case.
- **What is no use** (tasks 4.1–4.9): a citation in a lead-in, remark or note, an argument followed
  ("as in", `F-175`), a comparison, or one after a proof's conclusion; the same commits.
- **`def:rank-hypothesis`, repoints and moves** (tasks 4.3–4.9): no edge where no realization at a
  target rank enters; a removed edge's `\cref` points at the node defining the sentence's object;
  an unbacked statement edge only the proof cites moves to it, or goes if it names it (`F-105`).
- **The node order** (tasks 5.1–5.5). A forward edge's target moves, with its subsection or its
  group, ordered so its edges point back, to the chapter that defines its objects, before its
  first user; a moved block changes only a sentence that would point forward. A move that leaves a
  KT-numbered group or splits a subsection is a regrouping (principle E), so its edge stays. The
  commits carry the rest (`t52/verbatim.py` checks a moved block byte-identical).
- **The notation** (task 6). KT's $d$ for the dimension, with the formalization's $n$ named once,
  in a formalization note; $\vee$ for every join of vectors and $\bigwedge$ for an exterior power,
  as from `extensor.tex` on, so that $\wedge$ is only the meet (`meet.tex`) and the algebra's
  product in a basis; a local letter that the change makes clash is renamed or reworded. A list's
  items are plain `\item`s, cited as part (1), part (2), as the web build numbers them.
- **The status surfaces** (task 7). A surface follows its chapter as it now stands, and a finding's
  phrase follows to the surfaces its entry does not name; an `M` entry's lines stay for the report.
