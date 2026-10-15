# PROSE round 5/5 — `prose-graph`, graph repairs and the findings report (work log)

**Status:** in progress (opened 2026-10-13). Round 5 of **PROSE**'s five rounds; their plan and
the PI's decisions are in `notes/Prose.md`, and `.claude/autopilot/queue.toml` is the authority for
which rounds are done. The round acts on the 97 `E`, `N`, `T` and `U` entries of the ledger
`notes/Prose-findings.md` (40, 45, 7 and 5) under the expected-diff gate, sets every entry's
disposition, and reports its `S`, `L` and `M` entries to the PI. The open (task 1, docs only)
re-ran the audit script, reproduced round 4's gate values and triaged the entries into 31
one-commit tasks; task 2 added each node's `\uses` to the gate's dump, tasks 3.1–3.14 (task 3)
gave every node the ledger names its shape, and tasks 4.1–4.5 added the missing edges of rounds
1 and 2's chapters and of `panel-layer.tex` through `genericity-and-count.tex`. No task edits the
Lean or changes a statement's strength. **Next concrete task:** task 4.6, the edges of
`case-iii.tex` (*Hand-off*). Round manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop: Stop 1 was the program's only one, in round 1 (`notes/Prose.md` §1). The
findings report (tasks 8.1–8.2) is not a stop; ORIGAMI is attended, so the driver stops after the
close, where the PI reads it. An unplanned `NEEDS_PI` entry goes here, newest first, and the PI
answers in an entry that starts `**PI, <date>:**`. No entries yet.

## Current state

**Task 4.5 has landed** (this commit; the `\uses` of `case-ii.tex` and
`genericity-and-count.tex`, the dispositions of `F-062`, `F-146` and `F-151`, the docs, no Lean).
Nothing is mid-stream; the next task is task 4.6.

**The gate's baseline, at task 4.5** (2026-10-15):
- `python3 scripts/blueprint-deps.py --dump` after `verify.sh`: **3 526 lines**, sha256 prefix
  **`0fc2ebeb43de52b3`**, kept as `scratch/prose-graph/dump-<this commit's sha>.txt` (gitignored;
  regenerate it on this commit), the same bytes under `PYTHONHASHSEED` 0, 1 and 12345 and as
  `predict-dump.sh` gave for the copy. Its diff against task 4.4's (3 517 lines,
  `33600b0b62a0a65b`) is task 4.5's *Expected*, its 131 lines.
- `lint.sh` green; `verify.sh` green, `checkdecls` silent, 9 `WARNING:` lines; **`1439 edges
  c7669ccff3e6ec34`** and **`8cdc1b9723e22064`**; `print.log` 0 `LaTeX Warning` lines and 31
  overfull boxes, the open's count; `--summary` exits 0, both consistency checks OK: 692 nodes,
  1 009 pins (999 distinct; `lean_decls` 1 010), 195 missing, 2 336 implied, 84 + 195
  unbacked, 177 dead, 12 nodes with four or more pins, no cycle-closing missing edge (`F-011`
  done). Tasks 4.1–4.5's chapters: 0 missing; unbacked 5 / 2, 4 / 12, 8 / 12, 18 / 27 and 1 / 9.
  No node is drawn `#9CEC8B` (`F-007`). The forward screen gives the open's table but `case-i`
  14/5, `case-ii` 3/1, `panel-layer` 11/5 5/3, `rigidity-matrix` 15/9 0/0, `deficiency` 2/2 0/0
  and `molecular-induction` 7/4 2/2 (tasks 3.2–3.7's commits and 4.2–4.5's lines say why).
- Implied now, through tasks 4.1–4.5's edges: the missing in-edges of `def:edge-multiply` (35 ->
  0; four added, the rest through `def:matroid-MG`'s statement); `lem:case-III`'s and
  `cor:molecule-generic-square-packing`'s to `lem:deficiency-zero-connected` (through
  `lem:chain-cycle-dichotomy`); three of `jacobs.tex`'s (34 -> 31); 11 in `case-ii.tex` (1),
  `case-iii.tex` (7), `pencil.tex` (2) and `main-component.tex` (1), through task 4.4's edges;
  6 more in `case-iii.tex`, four to `lem:rows-polynomial-in-normals` and two to
  `lem:independent-rows-of-rank`, through task 4.5's; and, through edges a later task reads,
  `lem:endpoint-witness`'s to
  `lem:k-frame-specialize-li` (via its unbacked edge to `prop:tay-witness-exists`, `F-213`, task
  4.7) and `thm:pencil-x0-cycle`'s to `lem:pencil-lifting-restrict` (via `lem:block-rank-path`,
  `F-247`, task 4.9).
- Missing in-edges that tasks 3.2–3.14 drew or moved (task 4's; the report lists them, the
  commits name them; counted at task 4.5): to `lem:generic-realization-of-rigid` 3,
  `def:screw-space` 8, `def:trivial-motions-rigid` 2, `lem:edge-rows-independent` 2,
  `def:induced-span` 1, `lem:panel-support-extensor-join` 2, `lem:rows-polynomial-in-normals` 0,
  `lem:independent-rows-of-rank` 1, `def:case-III-candidate` 2,
  `lem:case-III-rank-certification` 2, `lem:case-III-redundant-combination` 2,
  `lem:case-III-chain-relabel-rows` 1, `lem:case-III-chain-eq666` 1, `def:induced-screw-map` 7,
  `def:tight-partition` 3 (`F-193`'s and `F-196`'s, and `lem:deficiency-merge-rigid`, which reaches
  `lem:exists-tight-partition` too), `def:rooted-cross-edges` 5 (`F-196`'s),
  `lem:normal-cross-count-rooted` 1 (the theorem's proof, through `rootedAt_inj`),
  `lem:two-core-degree-one` 1, `def:pencil-lifting-system` 3 (moved from the witness lemma); task
  3.5's `lem:reduction-measure` -> `lem:pencil-contraction-deficiency`.
- Unbacked edges that task 3.14 made, which task 4.8 or 4.9 reads: `thm:pencil-x0-main-component`
  -> `lem:pencil-x0-one-witness` (no Lean basis, as the two share their one pin; the theorem's
  third clause is the lemma's claim, so it stays, *Decisions*), and `def:pencil-two-ear-graph` ->
  `def:pencil-embed-edges` (moved from the lemma; its note cites the relabelling for a comparison).
- Nodes that cite a node without an edge, as they cited the node it left or the step it now states:
  a proof in `molecule-modelling.tex` (`def:trivial-motions-rigid`); the $d = 3$ dispatch's proof
  `def:case-III-candidate`, the chain dispatch's proof task 3.10's two nodes (task 4.6),
  `lem:hinge-point-witness`'s proof `def:induced-screw-map`, `lem:normal-cross-count`'s statement
  and `thm:laman-square-count`'s proof `def:rooted-cross-edges`, and `thm:degree-one-rank`'s proof
  `lem:two-core-degree-one` (task 4.7), missing edges.

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
- [x] **3. N — node shape**, chapter by chapter. N before E: an N fix changes what the report calls
  missing (`F-010`'s six helpers alone draw 97 missing in-edges). Each commit, with this log as of
  it, carries its task's exact list; the nodes each added are in its title.
  - [x] **3.1** round 1's chapters (`7b2a8272`): two nodes split off; four choices *revised*.
  - [x] **3.2** `matroid-union` → `meet` (`56fb8b8c`): three nodes added; `F-110` *revised*.
  - [x] **3.3** `rigidity-matrix.tex` (`a7b8ea35`): five nodes added; two choices *revised*.
  - [x] **3.4** `deficiency.tex`, operations (`8e6786d3`): two split off; `F-091` left (`F-234`).
  - [x] **3.5** KT Lemmas 4.4–4.9, `F-098` (`20d62426`): two split off; KT Lemma 3.5's graph moved.
  - [x] **3.6** `panel-layer.tex` (`1d35d435`): KT Theorem 5.6 reversed, base cases repinned.
  - [x] **3.7** `case-i.tex` (`d851de0f`): two nodes added, two repinned, the cycle forms unpinned.
  - [x] **3.8** `case-ii.tex`, `genericity-and-count.tex` (`657f3483`): two added; `F-152` left.
  - [x] **3.9** `case-iii.tex` to KT eq. (6.29) (`24f04215`): three nodes added.
  - [x] **3.10** `case-iii.tex`, $d = 3$ and every $d$ (`258e9e73`): two added, one repinned.
  - [x] **3.11** `molecule-modelling` → `generic-lift` (`dd34a61e`): three added; two *revised*.
  - [x] **3.12** `jacobs.tex` (`ae31af3e`): five added; `squareCutPairs` to `def:g-cut-edges`.
  - [x] **3.13** `pencil`, `main-component`: helpers and doubles (`24251386`): five unpinned.
  - [x] **3.14** `main-component.tex`: `c8a`'s splits (`0f9c275c`): three added, `F-009`'s last.
- [ ] **4. E — edges**, one commit per chapter group, split where a group has more than about 90
  edges to add or review. *Expected* (each): the `\uses` the edge policy adds, moves and removes,
  listed in the commit before editing; pins and the `lean_decls` hash unchanged. The open's
  counts (missing; unbacked through a node / none) are estimates, since task 3 changes them.
  - [x] **4.1 Round 1's chapters** (`9eb2c776`; `F-001` done, `F-006`'s part): 40 of the parent's
    71 missing edges added, 31 implied by them; 17 unbacked edges removed, and the 5 edges their
    removal left missing added; the 5 unbacked through a node and 2 that the text uses kept.
  - [x] **4.2 `matroid-union` → `deficiency`** (`3575835c`; `F-066`, `F-071`, `F-076`, `F-078` done,
    `F-247` new): 14 of the parent's 26 missing edges added, 12 implied by them; 34 unbacked edges
    removed, and the 15 they left missing added (three in tasks 4.3–4.4's chapters).
  - [x] **4.3 `molecular-induction`, `meet`** (`eaba775e`; `F-002`, `F-007`, `F-082`, `F-089`,
    `F-093`, `F-095`, `F-100`, `F-105`, `F-109` done): 9 of the parent's 17 missing edges added, 8
    implied by them; 39 unbacked edges removed, the 18 they left missing added; 15 statement edges
    moved to proofs, 6 cited steps added; `rem:kt-lemma-41` cited instead of used.
  - [x] **4.4 `panel-layer`, `case-i`** (`6af43988`; `F-129` left): 27 of the parent's 44 missing
    edges added, 17 implied by them; 27 unbacked edges removed, the 8 they left missing added.
  - [x] **4.5 `case-ii`, `genericity-and-count`** (this commit; `F-003`'s part, `F-006`'s part,
    `F-062`, `F-146`, `F-151` done). The parent's report: 19 missing, 1 / 21 unbacked, so one
    commit. Tried on a scratch copy (`t45/edit.py`). *Expected* (exact, before editing the tree; the
    copy's predicted after-dump): no node or pin changes, `lean_decls` `8cdc1b9723e22064`;
    `## uses:` 13 lines changed, 19 entries added and 24 removed (S statement, P proof). *Removed*
    (15 unbacked edges with no Lean basis that neither the statement, the proof prose nor the pins
    use, 21 entries; reasons in the commit): `lem:case-II-rank-lift` S `def:rank-hypothesis`;
    `lem:case-II` S `def:rank-hypothesis`, `lem:reduction-step-pos` and S, P
    `lem:exists-independent-panel-extensor`; `lem:case-II-realization` P `lem:genericity-device`;
    `lem:relative-screw-split` S `def:rank-hypothesis`; `lem:relative-device-count` S
    `lem:relative-screw-split`; `lem:case-II-placement-new-rows` S, P `lem:rank-delete-vertex`;
    `lem:case-II-placement-old-rows-extract` S `def:rank-hypothesis`;
    `lem:case-II-placement-old-rows` S, P `lem:case-II` and S `lem:case-II-placement-old-rows-extract`;
    `lem:case-II-placement-block-independent` S, P `lem:rank-delete-vertex`;
    `lem:case-II-realization-placement` S, P `lem:case-II`, `lem:exists-independent-panel-extensor`
    and S `lem:genericity-device`. 3 statement entries whose proof names the target: `lem:case-II` S
    `lem:splitoff-edge-substitution` (the proof's edge, unbacked, stays: it cites two steps) and
    `F-146`'s `lem:case-II-realization` S `lem:reduction-step-pos`, `lem:rank-polynomial-of-le-finrank`.
    *Added* (19): 15 of the parent's 19 missing, the other 4 implied by the task's additions:
    `lem:splitoff-edge-substitution` S `def:graph-operations`; `lem:case-II` P
    `lem:pinned-motions-on-mono` (implies `def:framework-with-graph`, `def:pinned-motions-on` and
    the cited `lem:motions-mono-of-graph-le`); `lem:case-II-realization` S
    `def:genuine-hinge-realization` and P `lem:case-II-placement-new-rows`,
    `lem:case-III-transport-collapse` (both forward, task 5), `lem:general-position-support-nonzero`,
    `lem:reducible-vertex` (implies `def:cut-edges-2ec`), `lem:relative-deficiency-rank-bound`,
    `lem:rigidityRows-pinned-placement-rank-add`, `lem:simple-minimal-noRigid`,
    `lem:span-rigidityRows-eq-of-motions-eq`; `lem:rank-polynomial-of-le-finrank` P
    `lem:independent-rows-of-rank` (implies `lem:case-II-realization`'s);
    `lem:case-II-placement-new-rows` and `-old-rows-extract` P `lem:rows-polynomial-in-normals`;
    `lem:case-II-realization-placement` P `lem:independent-rows-of-rank`. 2 for a citation of a
    step: `lem:genericity-device` P `lem:rows-polynomial-in-normals`;
    `lem:case-II-placement-old-rows-extract` S `def:graph-operations` (its $G_v^{ab}$). 2 that the
    removals left missing or left a citation without: `lem:case-II-realization-placement` P
    `lem:with-normal-preserves`, `lem:splitoff-edge-substitution`. *Kept:* the 1 unbacked through a
    node, and 6 with no Lean basis that the text uses. Drawn edges 1 430 -> 1 439
    (`c7669ccff3e6ec34`), 19 gone and 28 drawn, no fill changed; 3 526 lines (`0fc2ebeb43de52b3`),
    the diff 131 lines. Missing 220 -> 195 (these chapters 0; 6 in `case-iii.tex` implied now),
    unbacked 84 + 207 -> 84 + 195. The tree's after-dump is the predicted bytes.
  - [ ] **4.6 `case-iii`** (`F-003`'s part, `F-006`'s part, `F-155`, `F-160`, `F-162`, `F-166`,
    `F-170`; 70; 9 / 50).
  - [ ] **4.7 Round 4's chapters** (`F-004`, `F-006`'s part, `F-175`, `F-181`, `F-185`, `F-189`,
    `F-193`, `F-196`, `F-199`, `F-201`, `F-208`, `F-213`, `F-218`, `F-223`; 76; 22 / 21).
  - [ ] **4.8 `pencil`, and `main-component` through *Ears and cycles*** (`F-005`'s part, `F-006`'s
    part; 53; 46 in all).
  - [ ] **4.9 `main-component` from *Open ears with two, three or four interior bodies*** (`F-005`,
    `F-006`; 61; 33 in all).
- [ ] **5. N — node order** (`F-019`, `F-029`, `F-050`, `F-119`; the forward screen re-run after
  task 4; `F-071`'s move was round 2's, task 4.2). Move a node where the move cures a forward
  `\uses` without creating one: within a chapter (principle E, *Node order*), or across chapters or
  sections where the ledger names the move (`F-019`'s theorem to the end of `sparsity.tex`;
  `F-050`'s and `F-119`'s groups). A reference that stays forward keeps its sentence
  (left). `F-029`: leave (the swap would make `count-matroid.tex`'s opening refer forward).
  *Expected:* the dump byte-identical.
- [ ] **6. T — terminology and notation** (`F-056`, `F-067`, `F-072`, `F-073`, `F-127`, `F-203`,
  `F-227`). `F-056`, `F-067`, `F-072`: done by rounds 2–4 (checked at the open: no $n(n+1)/2$
  outside `body-bar.tex`'s gloss, `prop:rigidity-matrix-prop11` titled KT Proposition 2.3, no
  "boundary regime"); the task names the commits (`git log -S`). `F-073`: KT's $d$ for the
  dimension in `pencil.tex` and `main-component.tex` (about 48 lines; $\operatorname{def}_2$ and
  $\operatorname{def}_3$ stay). `F-127`: $\vee$ for the join of vectors (`molecular-induction.tex`
  twice; each of `main-component.tex`'s 92 `\wedge` read, such as $p_u \wedge p_v$). `F-203`: a
  different word for `main-component.tex`'s contracted "core", or a sentence there that
  distinguishes it from JJ's. `F-227`: `meet.tex`'s `\item[(i)]`. *Expected:* the dump
  byte-identical.
- [ ] **7. U — status surfaces** (`F-099`, `F-173`, `F-204`, `F-226`, `F-229`, `F-231`).
  `formalization.yaml`: `F-099`'s three places (the PI, 2026-10-12), `F-173`'s (2) and `F-204`'s
  (2), Jacobs 1998's DOI, and `F-231`'s declaration name in an alignment row's `lean:`.
  `README.md` and `home_page/index.md`: `F-173`'s (1), `F-204`'s (1), `F-226` and `F-229`. Each is
  aligned with the chapter it names; no main result's `declaration:` changes. *Expected:* the dump
  byte-identical.
- [ ] **8. R — the findings report** (`notes/Prose.md` §3 *R*), in `notes/Prose-report.md`. Each
  `S`, `L` and `M` entry gets the disposition `reported`; the report is not a stop.
  - [ ] **8.1 The `S` group** (65 entries): grouped by the kind of divergence, deduplicated and
    ranked, each with its evidence, a suggested disposition and a commit estimate. It is presented
    as one group, statements whose blueprint and formal texts disagreed after the formalization
    was declared complete, for what they show about the limits of autoformalization (the PI,
    2026-10-12, §1). It lists `F-137` and `F-142` in the group as resolved in passing by task 3.7's
    repins; their dispositions stay `done`.
  - [ ] **8.2 The `L` and `M` groups, the left graph findings, and the follow-up** (61 `L`, 6
    `M`; the `E` and `N` entries left for a merge, a retirement or a Lean change). The report's
    rest, and an unqueued ROADMAP bullet proposing the follow-up program, which the PI queues.
    One more item for the PI: a stale example in `blueprint/CLAUDE.md`'s honesty gate, which
    gives `lem:case-I` as case (b), a hypothesis that is the conclusion of a `\uses`'d node
    (`lem:genericity-device`); the node's pins take no such hypothesis, and task 4.4 removed the
    edge, which no text used. The report suggests a replacement, found then; the round edits no
    agent manual.
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
ledger's earlier `L` entries are task 8.2's.

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

## Blockers / open questions

None.

## Hand-off / next phase

**Next concrete task: task 4.6, the edges of `case-iii.tex`** (`F-003`'s part, `F-006`'s part,
`F-155`, `F-160`, `F-162`, `F-166`, `F-170`; Opus, a fresh agent). The parent's dump is task 4.5's
(3 526 lines, `0fc2ebeb43de52b3`; *Current state*): regenerate it on the parent after `verify.sh`
if the scratch copy is gone. The parent's report gives 67 missing and 8 / 52 unbacked, so one
commit by the split rule, the largest of task 4's; if it will not fit one sitting, land the
chapter up to its $d = 3$ subsubsection (task 3.9's nodes) first and say so in 4.6's line. Read
the chapter's report (`--chapter case-iii`; `--label` takes every node at once) and the ledger
entries, and apply *Scope*'s edge policy as tasks 4.1–4.5 read it (*Decisions*): each *missing*
edge on the statement or the proof as tagged, unless the task's other additions imply it; an edge
for each citation of a step that the ledger lists or `t43/cites.py` finds (and those *Current
state* names for task 4.6); the ledger's statement-to-proof moves; an unbacked edge that nothing uses
removed, with its reason; then re-run until nothing is missing, adding in any chapter the edges a
removal leaves missing, and re-run `t43/cites.py` for citations a removal leaves with no ancestor.
Write the `\uses` changes, node by node, in 4.6's line before editing (gate 3 (b)). Tools
(gitignored): `t45/edit.py` reads `t45/ops.py` (removals and moves), then `t45/adds.py` with
`PHASE=2` and an optional `reflow.py` (aligns continuation lines under the first target) and
`txt.py` beside it, and asserts each op, on the copy and then on the tree; `t42/missdiff.py`
diffs the missing and unbacked sets of two full reports over every chapter; `t41/redund.py` checks
that no added edge is implied; `t43/cites.py <tex-root> <chapter>...` lists the `\cref`s with no
edge; `t42/screen.py <tex-root> v` lists the forward edges; `predict-dump.sh` gives the
after-dump. Tasks 4.4–4.5 already added `lem:triangle-realization`'s statement edge to
`def:rank-hypothesis`, and edges into `case-iii.tex` from `case-i.tex` and `case-ii.tex`. Then
task 4.7.

## Decisions made during this round

- **The slicing** (the open): 31 tasks; the order is the tooling, N, E, the node order, T, U, R, X.
- **The `## uses:` section** (task 2): every labelled environment with a `\uses`, parts sorted.
- **The report's home** is `notes/Prose-report.md`; the ledger keeps each finding.
- **Try each change on a scratch copy, and predict the whole dump** (tasks 3.1–3.2). Edit a copy
  of `blueprint/src`, read its `--tex-root` report, and predict the after-dump with
  `predict-dump.sh` (the script's `ancestors_map` and `transitive_reduction` and leanblueprint's
  colorizers; exact since task 3.2). An edge is dashed when its source is in the user's statement
  `\uses`; a node with a remark among its `\uses` ancestors is drawn `#9CEC8B` (task 4.3 ended it).
- **Task 3's node-shape verdicts** (done): each commit has its entry; *Scope* states the rules.
- **A pin two nodes share leaves an edge the script cannot back** (task 3.14). The script skips a
  node's own pins, so an edge to a node whose pin the user shares reads as unbacked. It stays, as
  the user's clause is the other node's claim (`thm:pencil-x0-main-component` ->
  `lem:pencil-x0-one-witness`, `lem:reduction-step` -> `lem:contraction-minimality`); a merge
  (task 8.2) would remove the double.
- **The edge policy, as task 4.1 read it.** A missing edge that the task's other additions imply
  is not added (the report's *implied*, applied after the task). An unbacked edge reached through
  another node is a use by the pins and stays; one with no Lean basis goes when the statement does
  not state it and the proof cites it at most "as in the proof of" (an argument followed,
  `F-175`), and an edge a removal leaves missing is added in the same task. A definition's
  well-definedness paragraph is its proof prose. Task 4's split rule counts missing edges.
- **The edge policy, as task 4.2 read it.** An unbacked edge with no Lean basis also stays when
  the statement names a symbol the target defines or states its object without its name; a
  citation in a lead-in or a remark is no use. A definition with a proof takes a theorem pin's
  body reach on its proof. A missing edge that a pinned proof step draws is added and the step
  filed (`F-247`). An edge a removal leaves missing is added at its node, in any chapter.
- **The edge policy, as task 4.3 read it.** A proof that follows another node's argument ("as
  for", "we reverse the argument of") takes no edge to it, though the ledger put the edge on the
  proof (`F-089`); a statement edge that the proof already names is removed, not moved (`F-105`).
  Citations of a step come from the ledger's lists and from `t43/cites.py`, a scan of the
  chapters' `\cref`s. A remark in a node's `\uses` becomes a `\cref` in its proof (`F-007`).
- **The edge policy, as task 4.4 read it.** A pin that states the target's object through an
  unpinned declaration uses it (`def:pinned-motions-on`'s $\operatorname{pinned}(v)$), so the edge
  stays. Citations after a proof's conclusion ("This proves the lemma"), for how Katoh and Tanigawa
  attain a claim, or of a general form ("the general form of this argument is") are no use. A
  removal can leave a cited node with no ancestor path: re-run `t43/cites.py` on the copy, and add
  the edge. A transitive unbacked edge stays even where its ledger entry finds the text does not
  use it (`F-129`, left).
- **The edge policy, as task 4.5 read it.** A statement on $\dim Z = D + k'$ for any $k'$, or on
  motions constant on a set, takes no edge to `def:rank-hypothesis`, as no realization at a target
  rank enters (task 4.4's five nodes too); one that takes a panel-hinge framework keeps its edge to
  `def:panel-hinge-framework`, though its pin holds for body-hinge frameworks. An example after a
  proof's argument ("For instance"), and "Hence, as in" a lemma whose count the proof repeats, are
  no use.
