# PROSE round 5/5 — `prose-graph`, graph repairs and the findings report (work log)

**Status:** in progress (opened 2026-10-13). Round 5 of **PROSE**'s five rounds; their plan and
the PI's decisions are in `notes/Prose.md`, and `.claude/autopilot/queue.toml` is the authority for
which rounds are done. The round acts on the 97 `E`, `N`, `T` and `U` entries of the ledger
`notes/Prose-findings.md` (40, 45, 7 and 5) under the expected-diff gate, sets every entry's
disposition, and reports its `S`, `L` and `M` entries to the PI. The open (task 1, docs only)
re-ran the audit script, reproduced round 4's gate values and triaged the entries into 31
one-commit tasks; task 2 added each node's `\uses` to the gate's dump, tasks 3.1–3.14 (task 3)
gave every node the ledger names its shape, and tasks 4.1–4.2 added the missing edges of round
1's chapters and of `matroid-union.tex` through `deficiency.tex`. No task edits the Lean or
changes a statement's strength. **Next concrete task:** task 4.3, the edges of
`molecular-induction.tex` and `meet.tex` (*Hand-off*). Round manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop: Stop 1 was the program's only one, in round 1 (`notes/Prose.md` §1). The
findings report (tasks 8.1–8.2) is not a stop; ORIGAMI is attended, so the driver stops after the
close, where the PI reads it. An unplanned `NEEDS_PI` entry goes here, newest first, and the PI
answers in an entry that starts `**PI, <date>:**`. No entries yet.

## Current state

**Task 4.2 has landed** (this commit; the `\uses` of `matroid-union.tex` through
`deficiency.tex` and three edges their removals left missing in `case-i.tex`, `meet.tex` and
`molecular-induction.tex`, the ledger and docs, no Lean). Nothing is mid-stream; the next task is
task 4.3.

**The gate's baseline, at task 4.2** (2026-10-15):
- `python3 scripts/blueprint-deps.py --dump` after `verify.sh`: **3 485 lines**, sha256 prefix
  **`9ea23de1679c49e6`**, kept as `scratch/prose-graph/dump-<this commit's sha>.txt` (gitignored;
  regenerate it on this commit), the same bytes under `PYTHONHASHSEED` 0, 1 and 12345 and as
  `predict-dump.sh` gave for the copy. Its diff against task 4.1's (3 495 lines,
  `933f0e6f077a3f81`) is task 4.2's *Expected*, its 366 lines.
- `lint.sh` green; `verify.sh` green, `checkdecls` silent, 9 `WARNING:` lines; **`1398 edges
  5dc35f55add46678`** and **`8cdc1b9723e22064`**; `print.log` 0 `LaTeX Warning` lines and 31
  overfull boxes, the open's count; `--summary` exits 0, both consistency checks OK: 692 nodes,
  1 009 pins (999 distinct; `lean_decls` 1 010), 294 missing, 2 310 implied, 84 + 255
  unbacked, 177 dead, 12 nodes with four or more pins, no cycle-closing missing edge (`F-011`
  done). Tasks 4.1–4.2's chapters: 0 missing; unbacked 5 / 2 and 4 / 12. The forward screen gives
  the open's table but `case-i` 7/5, `rigidity-matrix` 15/9 0/0, `deficiency` 2/2 0/0 and
  `molecular-induction` 5/3 3/3 (tasks 3.2–3.7's commits and 4.2's line say why).
- Implied now, through task 4.2's edges: the missing in-edges of `def:edge-multiply` (35 -> 0;
  two added, the rest through `def:matroid-MG`'s statement, among them 19 of
  `molecular-induction.tex`'s 32, three of `case-iii.tex`'s and two of `pencil.tex`'s);
  `case-i.tex`'s two of `lem:case-I-realization`; and, through edges a later task reads,
  `lem:endpoint-witness`'s to `lem:k-frame-specialize-li` (via its unbacked edge to
  `prop:tay-witness-exists`, `F-213`, task 4.7) and `thm:pencil-x0-cycle`'s to
  `lem:pencil-lifting-restrict` (via `lem:block-rank-path`, `F-247`, task 4.9). Task 4.1's edges
  imply three of `jacobs.tex`'s (34 -> 31).
- Missing in-edges that tasks 3.2–3.14 drew or moved (task 4's; the report lists them, the
  commits name them): to `lem:generic-realization-of-rigid` 4, `def:screw-space` 9,
  `def:trivial-motions-rigid` 2, `lem:edge-rows-independent` 2, `lem:two-edge-connected-degree`
  3, `def:induced-span` 1, `lem:panel-support-extensor-join` 3, `lem:rows-polynomial-in-normals`
  8, `lem:independent-rows-of-rank` 10 (four point forward, task 5), `lem:splitoff-simple` 1,
  `def:case-III-candidate` 2, `lem:case-III-rank-certification` 2,
  `lem:case-III-redundant-combination` 2, `lem:case-III-chain-relabel-rows` 1,
  `lem:case-III-chain-eq666` 1, `def:induced-screw-map` 7, `def:tight-partition` 3 (`F-193`'s
  and `F-196`'s, and `lem:deficiency-merge-rigid`, which reaches `lem:exists-tight-partition`
  too), `def:rooted-cross-edges` 5 (`F-196`'s), `lem:normal-cross-count-rooted` 1 (the theorem's
  proof, through `rootedAt_inj`), `lem:two-core-degree-one` 1, `def:pencil-lifting-system` 3
  (moved from the witness lemma); task 3.5's `lem:reduction-measure` ->
  `lem:pencil-contraction-deficiency`.
- Unbacked edges that task 3.14 made, which task 4.8 or 4.9 reads: `thm:pencil-x0-main-component`
  -> `lem:pencil-x0-one-witness` (no Lean basis, as the two share their one pin; the theorem's
  third clause is the lemma's claim, so it stays, *Decisions*), and `def:pencil-two-ear-graph` ->
  `def:pencil-embed-edges` (moved from the lemma; its note cites the relabelling for a comparison).
- Nodes that cite a node without an edge, as they cited the node it left or the step it now
  states: two proofs in `case-i.tex` and one in `molecule-modelling.tex`
  (`def:trivial-motions-rigid`), `lem:reducible-vertex` and `thm:minimal-kdof-reduction`
  (`lem:two-edge-connected-degree`), `lem:adjacent-degree-two-pair`
  (`lem:deficiency-zero-connected`), `lem:generic-yields-genuine-hinge`
  (`lem:panel-support-extensor-join`); `thm:minimal-kdof-reduction`'s proof also cites
  `lem:rigidContract-isMinimalKDof`, from earlier in its file (task 4.3), the $d = 3$ dispatch's
  proof `def:case-III-candidate`, the chain dispatch's proof task 3.10's two nodes (task 4.6),
  `lem:hinge-point-witness`'s proof `def:induced-screw-map`, `lem:normal-cross-count`'s statement
  and `thm:laman-square-count`'s proof `def:rooted-cross-edges`, and `thm:degree-one-rank`'s
  proof `lem:two-core-degree-one` (task 4.7), missing edges.

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
  - [x] **4.2 `matroid-union` → `deficiency`** (this commit; `F-002`'s part, `F-006`'s part,
    `F-066`, `F-071`, `F-076`, `F-078`, done; `F-247` new). The parent's report: 26 missing, 4 / 46 unbacked, so one commit. Tried on a
    scratch copy (`scratch/prose-graph/t42/edit.py`). *Expected* (exact, before editing the tree;
    the copy's predicted after-dump): no node or pin changes, `lean_decls` `8cdc1b9723e22064`;
    `## uses:` 40 lines changed (S statement, P proof). *Removed* (34 unbacked edges with no Lean
    basis that neither the statement nor the proof prose uses, 40 entries; reasons in the commit):
    `def:matroid-union` S `def:ofPolymatroidFn`, `lem:polymatroid-rank`; `lem:rado` S and P
    `lem:polymatroid-rank`; `lem:union-indep-iff` from `thm:matroid-partition-rank` S and
    `thm:unionPow-cycle-indep-iff-sparse` S and P; `def:k-frame-matroid` S `def:matroid-union`;
    `lem:k-frame-pi-finrank` S `lem:k-frame-span-le-pi`; `lem:k-frame-specialize-identity` S
    `lem:k-frame-specialize-li`; `lem:tay-isSparse-of-independent` S `def:k-frame-matroid`, P
    `lem:k-frame-nonzero-monomial-forest`; `cor:k-spanning-trees` from `thm:tay-witness` S and
    `thm:body-hinge-tay` S and P; `def:edge-multiply` S `def:graph-sparse`; `def:join` S
    `def:extensor`; `def:plucker-coords` S `def:extensor`, `def:join`; `lem:extensor-independence` S
    `def:plucker-coords`; `lem:relative-deficiency-rank-bound` P `lem:deficiency-rank-bound`;
    `lem:rank-parallel-full` S `lem:extensor-independence`; `lem:rank-rotation-semicont` S
    `def:dof-generic`; `def:relative-screws` S `def:hinge-row-block`;
    `lem:extProj-preserves-rank-of-inter` S `lem:claim-6-4`, S and P `lem:rank-delete-vertex`;
    `lem:rank-transport-relabel-of-le-finrank` S `def:genuine-hinge-realization`, and
    `lem:rank-polynomial-proj-eval` and `lem:rank-polynomial-IH-relabel-proj` S and P
    `lem:rank-polynomial-of-le-finrank` (`F-066`); `def:matroid-MG` S `thm:tay-witness`,
    `def:D-deficiency` S `def:matroid-MG`, `lem:deficiency-antitone` P `lem:rk-within-parts` and
    `lem:cut-edge-decomposition` P `thm:def-eq-corank` (`F-071`); `lem:rk-within-parts` S
    `def:matroid-MG`, `def:D-deficiency` and `thm:def-eq-corank` S `lem:rank-matroidMG-le`
    (`F-078`); `lem:circuit-rigid` S `def:rigid-subgraph` (`F-076`). *Moved* (`F-076`):
    `lem:two-vertex-trichotomy`'s S `lem:matroid-restrict-subgraph`, `thm:def-eq-corank`, which
    only its proof uses and already names, removed. *Added* (29): 14 of the parent's missing, the
    other 12 implied by them (9 to `def:edge-multiply`): `prop:tay-witness-exists` P
    `lem:k-frame-specialize-li`; `def:affine-subspace-extensor` S `lem:affine-indep-iff`;
    `lem:block-rank-path` P `thm:pencil-x0-bridge` (forward; `F-247`);
    `lem:rank-transport-relabel-of-le-finrank` S `def:panel-general-position`;
    `lem:rank-polynomial-IH-relabel-proj` P `lem:general-position-support-nonzero`,
    `lem:independent-rows-of-rank`, `lem:rank-polynomial-proj-eval`, and
    `lem:rank-polynomial-IH-relabel` P the first (`F-066`); `def:matroid-MG` and
    `lem:rk-within-parts` S `def:edge-multiply`; `lem:deficiency-zero-iff-tree-packing` P
    `def:k-dof` (`F-078`); `lem:cut-edge-decomposition` P `lem:subgraph-minimality` (`F-071`);
    `lem:deficiency-ear` P `lem:exists-tight-partition` and `lem:two-vertex-trichotomy` P
    `lem:two-vertex-zero-dof` (`F-076`, forward). 15 that the removals left missing:
    `lem:rado` P `def:submodular`; `lem:k-frame-forest-packing-of-sparse` P `lem:union-indep-iff`;
    `lem:tay-isSparse-of-independent` P `lem:k-frame-pi-finrank`,
    `lem:k-frame-incidence-finrank-rk`; `lem:rank-transport-relabel-of-le-finrank` S
    `def:rank-hypothesis`; `lem:rank-polynomial-proj-eval` S `def:panel-hinge-framework`, P
    `lem:rows-polynomial-in-normals`; `lem:rank-polynomial-IH-relabel-proj` S
    `def:rigid-contraction`; `def:matroid-MG` S `def:body-bar-framework`, P
    `thm:unionPow-cycle-indep-iff-sparse`; `def:D-deficiency` and `lem:rk-within-parts` S
    `def:body-bar-framework`; in other chapters, `lem:case-I-realization` S
    `def:genuine-hinge-realization`, `lem:meet-two-hyperplanes` S `def:extensor` and
    `lem:forest-packing-decomp` P `lem:union-indep-iff`. *Kept:* the 4 unbacked through a node, and
    12 with no Lean basis that the statement names or the proof cites: `def:k-frame-matroid` from
    seven $k$-frame lemmas (its $K$, $R$ or $\rho_e$), `def:affine-subspace-extensor`'s
    `def:join`, `def:hinge-constraint`'s and `lem:extensor-independence`'s
    `def:affine-subspace-extensor`, `lem:rank-parallel-full`'s `def:rigidity-matrix` and
    `lem:block-rank-cut`'s `lem:edge-rows-independent`. Drawn edges 1 408 -> 1 398
    (`5dc35f55add46678`), 66 gone and 56 drawn; 3 485 lines (`9ea23de1679c49e6`), the diff 366
    lines. Missing 348 -> 294 (these chapters 0; 28 elsewhere implied now, 19 of them in
    `molecular-induction`), unbacked 84 + 289 -> 84 + 255.
  - [ ] **4.3 `molecular-induction`, `meet`** (`F-002`'s part, `F-006`'s part, `F-007`, `F-082`,
    `F-089`, `F-093`, `F-095`, `F-100`, `F-105`, `F-109`; 66; 7 / 44). `F-007`: the three `\uses` of
    `rem:kt-lemma-41`, which the graph cannot draw, become edges to the node the remark discusses or
    a `\cref` in the proof; the example's pin stays (`checkdecls` checks it).
  - [ ] **4.4 `panel-layer`, `case-i`** (`F-003`'s part, `F-006`'s part, `F-129`; 78; 21 / 48).
  - [ ] **4.5 `case-ii`, `genericity-and-count`** (`F-003`'s part, `F-006`'s part, `F-062`, `F-146`,
    `F-151`; 16; 2 / 22).
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

- None.

## Hand-off / next phase

**Next concrete task: task 4.3, the edges of `molecular-induction.tex` and `meet.tex`** (`F-002`'s
last part, so its disposition; `F-006`'s part, `F-007`, `F-082`, `F-089`, `F-093`, `F-095`,
`F-100`, `F-105`, `F-109`; Opus, a fresh agent). The parent's dump is task 4.2's (3 485 lines,
`9ea23de1679c49e6`; *Current state*): regenerate it on the parent after `verify.sh` if the
scratch copy is gone. The parent's report gives 17 missing (`molecular-induction` 13, `meet` 4;
the open's 66 fell with task 3 and task 4.2's `def:matroid-MG` edge) and 8 / 45 unbacked, so one
commit. Read the two chapters' reports (`--chapter`) and the ledger entries, and apply *Scope*'s
edge policy as tasks 4.1–4.2 read it (*Decisions*): each *missing* edge on the statement or the
proof as tagged, unless the task's other additions imply it; an edge for each "cites without an
edge" the ledger lists and the text still makes; the ledger's statement-to-proof moves (`F-089`,
`F-095`, `F-105`); an unbacked edge that nothing uses removed, with its reason; then re-run until
nothing is missing, adding in any chapter the edges a removal leaves missing. `F-007`: the three
`\uses` of `rem:kt-lemma-41` become edges to the node it discusses or a `\cref` (the checklist
line). Write the `\uses` changes, node by node, in 4.3's line before editing (gate 3 (b)). Tools
(gitignored): `t42/edit.py` takes the op list (removals, then `t42/adds.py` with `PHASE=2`) and
asserts each op, on the copy and then on the tree; `t42/missdiff.py` diffs the missing and
unbacked sets of two full reports over every chapter; `t41/redund.py` checks that no added edge is
implied; `t42/screen.py <tex-root> v` lists the forward edges; `predict-dump.sh` gives the
after-dump. Task 4.2 already added `lem:forest-packing-decomp`'s proof edge to
`lem:union-indep-iff` and `lem:meet-two-hyperplanes`'s statement edge to `def:extensor`. Then
task 4.4.

## Decisions made during this round

- **The slicing** (the open): 31 tasks, not §3's ~15 (it predates the script's 536 missing and
  397 unbacked edges): N by chapter (14), E by chapter group (9), the report in two commits.
- **The honesty gate for a new node, the retargeting rule, and the node-shape and edge
  policies** (§3 *N*, *E*): settled at the open, under *Scope*.
- **The order:** the tooling (task 2: the drawn graph is a transitive reduction, so the dump
  alone hides removals), N, E, the node order, then T, U, R and X; N changes what is missing.
- **The `## uses:` section's lines** (task 2): every node and every other labelled environment
  with a `\uses` (task 4.3's `F-007`); targets raw, each part sorted, `-` for an empty part.
- **`pathVertex`** (task 3.13, done): a path's vertex sequence is notation, not a result, so it
  is unpinned (`40-simplify`'s `c8` had left it; `F-010`'s 30 missing in-edges through it).
- **The report's home** is `notes/Prose-report.md`: the ledger keeps each finding, and the report
  ranks them for the PI (`notes/CLAUDE.md` *One canonical home*).
- **Try each N fix on a scratch copy first** (task 3.1). Copy `blueprint/src`, edit the copy, and
  read its `--tex-root` report: an unpin that leaves a `\uses` of the node or of its users with no
  Lean basis strands a clause the pin states, so the pin is not a helper (task 3.1 kept
  `Reachable.out_le` and `newOrient` so). The drawn edges follow from the copy's `\uses` by the
  script's `ancestors_map` and `transitive_reduction`; an edge is dashed when its source is in the
  user's statement `\uses`. On the parent this reproduced the built graph's 1 292 edges exactly.
- **Predict the whole dump** (task 3.2). A probe applying those two functions and leanblueprint's
  colorizers to the copy's TeX reproduces the after-dump exactly (tasks 3.2, 3.3; measured,
  `scratch/prose-graph/predict.py` and `predict-dump.sh`, gitignored). A node with a remark among
  its `\uses` ancestors (`rem:kt-lemma-41`) is not fully proved, so it is drawn `#9CEC8B`.
- **A new node's `\uses`** (task 3.2): every node its pins reach, less those implied by its other
  `\uses`; the statement takes those whose terms it states. A node whose prose follows an argument
  its pins do not reach gets no edge to it (`lem:generic-realization-of-rigid`,
  `lem:genericity-device`).
- **Retargets beyond reach** (task 3.3). A proof whose edge to the old node backed its citation of
  a claim that moved gains an edge to the new node (`lem:block-rank-cut` cites the rows of an
  edge). A removed edge that a downstream node's reach went through is restored at that node
  (`lem:motions-mono-of-graph-le`). Diffing the copy's `--tex-root` report against the parent's,
  node by node, lists every missing or unbacked edge a move changes (*Current state*).
- **Node-shape verdicts** (tasks 3.4–3.12, settled; each commit's log has the full entry). A
  pinned step that other nodes' proofs cite splits off as a node (3.4,
  `lem:separated-partition-value`); a doubled pin that states a clause stays (3.5, `F-120`); a
  reversed derivation moves the argument and its edges together (3.6, `F-011`); a claim no clause
  states gets a node, not a second pin (3.7, `lem:case-I-all-k`); a new node goes after the nodes
  it uses and before its users (3.8), in the source's setting (3.9); a numbered source step that a
  dispatch derives gets a node (3.10, KT eq. (6.66)); a definition goes first to the node that
  already describes its object, and a new node's statement takes no edge its proof implies (3.12).
- **A retarget keeps the edge's place** (task 3.11). A retargeted `\uses` stays on the statement
  or the proof, where the old one was; moving it to where its pins reach (`F-089`'s rule) is task
  4's. A reach that went through the old node to a third node is restored at the retargeted node,
  by task 3.3's rule (`lem:pencil-config-point-join-rank` -> `thm:projective-invariance`).
- **A pin two nodes share leaves an edge the script cannot back** (task 3.14). The script skips a
  node's own pins, so when a node `\uses` another whose only pin it shares (`F-120`'s doubles), the
  edge reads as unbacked with no Lean basis (`thm:pencil-x0-main-component` ->
  `lem:pencil-x0-one-witness`, once the witness kept only `x0Attains_of_exists`). The edge stays:
  the user's clause is the other node's claim, on the same pin. Task 4 keeps it; a merge (task
  8.2) would remove the double.
- **The edge policy, as task 4.1 read it.** A missing edge that the task's other additions imply
  is not added (the report's *implied*, applied after the task: 31 of round 1's 71). An unbacked
  edge reached through another node is a use by the pins and stays; one with no Lean basis goes
  when the statement does not state it and the proof cites it at most "as in the proof of" (an
  argument followed, `F-175`), and an edge a removal leaves missing is added in the same task. A
  definition's well-definedness paragraph is its proof prose (`def:runPebbleGameExec` keeps
  `thm:pebble-game-correct`). Task 4's split rule counts missing edges, as the open's slicing did.

- **The edge policy, as task 4.2 read it.** An unbacked edge with no Lean basis also stays when
  the statement names a symbol the target defines or states its object without its name
  (`def:k-frame-matroid`'s $K$, $R$, $\rho_e$; $C(p_1, \dots, p_k)$ written as a join); a citation
  in a lead-in or a remark is no use. A definition with a proof takes a theorem pin's body reach
  on its proof (`def:matroid-MG`). A missing edge that a pinned proof step draws is added and the
  step filed (`F-247`). An edge a removal leaves missing is added in its own chapter (three here).
