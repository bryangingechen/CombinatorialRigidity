# PROSE round 5/5 — `prose-graph`, graph repairs and the findings report (work log)

**Status:** in progress (opened 2026-10-13). Round 5 of **PROSE**'s five rounds; their plan and
the PI's decisions are in `notes/Prose.md`, and `.claude/autopilot/queue.toml` is the authority for
which rounds are done. The round acts on the 97 `E`, `N`, `T` and `U` entries of the ledger
`notes/Prose-findings.md` (40, 45, 7 and 5) under the expected-diff gate, sets every entry's
disposition, and reports its 132 `S`, `L` and `M` entries to the PI. The open (task 1, docs only)
re-ran the audit script, reproduced round 4's gate values and triaged the entries into 31
one-commit tasks; task 2 added each node's `\uses` to the gate's dump, and task 3.1 reshaped round
1's chapters' nodes. No task edits the Lean or changes a statement's strength. **Next concrete
task:** task 3.2, the node shapes of `matroid-union`, `body-bar`, `extensor` and `meet`
(*Hand-off*). Round manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop: Stop 1 was the program's only one, in round 1 (`notes/Prose.md` §1). The
findings report (tasks 8.1–8.2) is not a stop; ORIGAMI is attended, so the driver stops after the
close, where the PI reads it. An unplanned `NEEDS_PI` entry goes here, newest first, and the PI
answers in an entry that starts `**PI, <date>:**`. No entries yet.

## Current state

**Task 3.1 has landed** (this commit; four chapters, the ledger and docs, no Lean). Nothing is
mid-stream; the next task is task 3.2.

**The gate's baseline, at task 3.1** (2026-10-13):
- `python3 scripts/blueprint-deps.py --dump` after `verify.sh`: **3 286 lines**, sha256 prefix
  **`1df3c3a7996203cf`**, kept as `scratch/prose-graph/dump-<this commit's sha>.txt` (gitignored;
  regenerate it on this commit), the same bytes under `PYTHONHASHSEED` 0, 1 and 12345. Its diff
  against task 2's (3 274 lines, `4015eeb0fed12738`) is task 3.1's *Expected*, its 36 lines.
- `lint.sh` green; `verify.sh` green, `checkdecls` silent, 9 `WARNING:` lines; **`1298 edges
  8c15c9f272b4319a`** and **`256c6105b5132fbb`**; `print.log` 0 `LaTeX Warning` lines and 31
  overfull boxes, the open's count; `--summary` exits 0, both consistency checks OK: 659 nodes,
  1 028 pins (1 018 distinct; `lean_decls` 1 029), 524 missing, 2 059 implied, 87 + 310
  unbacked, 202 dead, 27 nodes with four or more pins. The forward screen gives the open's table.
- Task 2's acceptance test is in its commit message (`18400dc9`).

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
- **The baseline dump.** `python3 scripts/blueprint-deps.py --dump` after `verify.sh`: 2 614
  lines, sha256 prefix **`00604279e922bb0f`**, kept as `scratch/prose-graph/dump-216e0702.txt`
  (gitignored; generated, so not committed). The open (`44e09c12`) changed no TeX: its dump,
  regenerated at task 2, is the same bytes.
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
- [ ] **3. N — node shape**, chapter by chapter. N before E: an N fix changes what the report calls
  missing (`F-010`'s six helpers alone draw 97 missing in-edges).
  - [x] **3.1 Round 1's chapters** (this commit; `F-009`'s four, `F-011`'s three pebble-game edges,
    `F-014`, `F-016`, `F-043`, `F-044`; `F-008`'s `def:blockingWitness`). The open's choices, four
    *revised* after reading, each tried on a scratch copy of the TeX with `--tex-root`.
    `def:pebble-counts`, `lem:edgesIn-corners`: leave, with a one-line role map in a note.
    `lem:pebble-game-invariants`: leave all five pins, with a role map (*revised*: by the definition
    of $\mathrm{peb}$, part (1) is equivalent to `Reachable.out_le`'s bound; unpinned, the bound
    left `lem:runPebbleGame-underline-eq`'s edge with no Lean basis and vanished from
    `def:tryAddEdge`, whose prose cites it). `def:tryReachPebble`: unpin only the result record
    `TryReachPebbleResult`, with a role map (*revised*: `newOrient` is the statement's "returns ...
    the orientation obtained by reversing $p$"; unpinned, it left `def:path-reversal` with no Lean
    basis). `F-011` (*revised* from leave: the three are the proofs the formal game's verdict
    carries, not termination lemmas): `def:runPebbleGame`'s pin `runPebbleGame` moves to a new
    `def:runPebbleGame-verdict` after `def:pebbleGameResult`, as `def:runPebbleGameExec` follows the
    correctness results; the game on a list and on $G$ keep their node and statement. `F-043`:
    `thm:runPebbleGameExec-isAccept-iff`, after `fmlnote:executable-computable-core`'s paragraph,
    takes `runPebbleGameExec_isAccept_iff` with the statement's last sentence. `F-014`, `F-016`,
    `F-044`: no node; the proofs of `thm:isSparse-exists-typeI-or-typeII-reverse` and
    `thm:pebble-game-correct` now name the six and the one declarations (*revised*: they did not).
    `def:blockingWitness`: left unfilled (no declaration defines it). Retargets by reach:
    `cor:pebble-game-countMatroid-indep` and `thm:pebbleGameResult-isAccept-iff` to the new
    definition, `def:isSparse-decidable` to the new theorem; of the old labels' 15 `\cref`s, eight
    repointed or rewritten and seven kept. New: `F-230`.
    *Expected* (exact, before editing; the drawn edges by the script's reduction, measured, script
    not retained): +2 nodes; pins 1 030 → 1 029, two moved and `TryReachPebbleResult` gone (hash
    changes); `## uses:` +2 lines (`def:runPebbleGame-verdict`: statement `def:pebbleGameResult`,
    `def:reachClosureComputable`, `def:runPebbleGame`, `lem:mem-reachClosureComputable`,
    `lem:runPebbleGame-underline-eq`, `lem:workhorseWitness-certifies`;
    `thm:runPebbleGameExec-isAccept-iff`: statement `def:runPebbleGameExec`, proof
    `def:reachClosureComputable`, `lem:mem-edgeListSorted`, `lem:mem-outListSorted`,
    `lem:mem-reachClosureComputable`, `thm:pebble-game-correct`) and three changed (the retargets);
    1 292 → 1 298 drawn edges: −3 (`def:pebbleGameResult` → `thm:pebbleGameResult-isAccept-iff`;
    `def:runPebbleGameExec`, `thm:pebbleGameResult-isAccept-iff` → `def:isSparse-decidable`), +9
    (`def:pebbleGameResult`, `lem:mem-reachClosureComputable`, `lem:workhorseWitness-certifies` →
    `def:runPebbleGame-verdict` → `thm:pebbleGameResult-isAccept-iff`; `def:runPebbleGameExec`, the
    three `lem:mem-…` → `thm:runPebbleGameExec-isAccept-iff` → `def:isSparse-decidable`); +2 node
    lines; 3 286 lines.
  - [ ] **3.2 `matroid-union`, `body-bar`, `extensor`, `meet`** (`F-052`, `F-054`, `F-059`,
    `F-110`, `F-111`). `F-052`: a lemma node for `Matroid.Union_pow_indep_iff_count` (independence
    in $k$ copies of one matroid); Welsh's theorem and Oxley's Lemma 11.2.13 stay addresses.
    `F-054`: repin `lem:k-frame-span-le-pi` on the per-set forms that the proof of
    `lem:k-frame-nonzero-monomial-forest` uses (`blockPiSpanOn` and its lemmas, at most three
    pins), unpinning the dead forms for all bars. `F-059`: leave (the expansion is not
    formalized; a Lean round's). `F-110`: split `lem:case-III-claim612-line-in-panel-union` (12
    pins). The lemma keeps its three. A node
    after `def:meet` takes the form for every $d$ (`extensor_join_proportional_complementIso_meet`,
    `complementIso_extensor_mem_range_map_subtype`, `complementIso_map_contragredient_eq`), and
    `lem:case-III-chain-discriminator`'s "general duality" cites it. The upgrade
    `hasGenericFullRankRealization_of_rigidOn_ofNormals` (KT's use of Lemma 5.2) goes to a node
    beside its user `lem:cycle-realization`. The eight dead realization pins go to a node whose
    statement states them, or are unpinned (no clause of the lemma states them). `F-111`: leave
    (the steps of a route the formal proof does not take; the live ones are addresses).
    *Expected:* +3 nodes; pins +1, a repin, moves, and up to −8 (hash changes); new edges.
  - [ ] **3.3 `rigidity-matrix.tex`** (`F-009`'s two, `F-010`'s `ScrewSpace` and
    `finrank_screwAssignment`, `F-011`'s three, `F-008`'s `def:dof-generic`, `F-065`, `F-068`).
    `def:rigidity-matrix` (14): the screw space (`ScrewSpace`, `screwDim`,
    `screwSpace_finrank`) moves to `def:hinge-constraint`, which introduces it (two cycles of
    `F-011` go); the two facts that the prose after it proves, the independence of an edge's rows
    and of the rows of edges with ends of their own (five pins), split into a lemma; the motions
    and rows stay; a pin no clause states is unpinned.
    `lem:trivial-motions-rank-bound` (9) with `def:dof-generic`: a definition node before the
    lemma for trivial motions and infinitesimal rigidity takes `IsTrivialMotion`, `trivialMotions`
    and `def:dof-generic`'s `IsInfinitesimallyRigid` with their sentences (the third cycle goes);
    `def:dof-generic` keeps the degree of freedom and genericity, unpinned and unfilled (left: no
    declaration defines them as stated); `finrank_screwAssignment` is unpinned; the deficiency
    bound splits off if KT state it separately. `F-065`, `F-068`: leave (exposition of the
    induced case and of KT eq. (6.29)). *Expected:* +2 or +3 nodes; pins moved, about −3 (hash
    changes); new edges; the screw space's in-edges become `def:hinge-constraint`'s.
  - [ ] **3.4 `deficiency.tex`; `molecular-induction.tex`'s operations, induced subgraph and
    forest surgery** (`F-009`'s four, `F-010`'s `endsOf`, `F-082`, `F-087`, `F-090`, `F-091`;
    `F-008`'s two). `def:cut-edges-2ec` (7): its two claims (a $0$-dof-graph is
    $2$-edge-connected; then every vertex has degree at least two) split into a lemma, and the
    three `cutLabeling` helpers are unpinned. `lem:cut-edge-decomposition` (7): the four
    `partitionDef` helpers unpinned, one pin per part remaining. `lem:two-vertex-trichotomy` (4):
    the three steps unpinned if the trichotomy's pin states the values of $k$.
    `def:graph-operations`: `endsOf` unpinned. `F-082`: `def:induced-span` pinned on
    `Graph.fiberSpan` and `Graph.inducedSpan`. `F-091`: `lem:forest-surgery-unsplit` pinned on
    `splitOff_indep_extend_of_fiber_lt`, with a note. Both get `\leanok` by the gate. `F-087`,
    `F-090`: leave (exposition of the move; a merge). *Expected:* +1 node; pins about −11 and +3
    (hash changes); two nodes filled; the retargets of `def:cut-edges-2ec`'s in-edges.
  - [ ] **3.5 `molecular-induction.tex`, KT Lemmas 4.4–4.9, and the carry-in `F-098`** (`F-096`,
    `F-098`, `F-103`, `F-106`). `F-096`: split `lem:removal-deficiency-strict` into KT Lemma 4.4's
    second assertion and KT Lemma 4.7, one pin each; unpin `Graph.contraction_isMinimalKDof` from
    `lem:reduction-step` if no clause states KT Lemma 3.5 (one of `F-120`'s doubles). `F-098`
    (the PI, 2026-10-12): first re-home `Graph.rigidContract_vertexSet_ncard` from
    `lem:pencil-contract-standing` to `lem:reduction-measure` or `def:rigid-contraction`; then move
    `lem:rigidContract-isMinimalKDof` from `case-i.tex` to follow `lem:contraction-minimality`. Its
    statement edge to `lem:reduction-step` becomes `lem:reduction-measure`'s (`F-095`), and its
    `\cref`s keep their label. `F-103`: mark `lem:adjacent-degree-two-pair` superseded (the
    supersession gate). `F-106`: the dichotomy's third pin `isKDof_zero_of_cycle` goes to a node
    that the dichotomy and `lem:chain-data-extract` use; `CycleData.vertexSet_ncard` is unpinned.
    *Expected:* +2 nodes; pins moved, −1 or −2 (hash changes); new edges and `F-098`'s retargets.
  - [ ] **3.6 `panel-layer.tex`** (`F-011`'s last, `F-131`, `F-224`'s meet decomposition).
    `F-011`: the Lean proves `thm:theorem-55-6` from `thm:theorem-55-6-genuine`, and the blueprint
    derives the second from the first; reverse the derivation, in node order and in both proofs
    (the headline's pin and statement stay). `F-131`: repin the three base cases on their `_gen`
    forms; `lem:extensor-pair-in-panel` is left ($K^4$, as its pin). `F-224`: a lemma node after
    `def:panel-support-extensor` for `exists_extensor_eq_panelSupportExtensor_gen`, now the
    remark's. *Expected:* +1 node; five repins and +1 pin (hash changes); the reversed edges.
  - [ ] **3.7 `case-i.tex`** (`F-134`, `F-139`, `F-143`; `F-009`'s `lem:cycle-realization-rigid`).
    `F-134`: leave the six dead nodes (exposition; merging is not a D fix); unpin
    `lem:cycle-realization-rigid`'s three `Fin m`-body forms if `theorem_55_cycle` states its
    claim. `F-139`: repin `lem:rows-polynomial-in-normals` on `annihRowPoly` and
    `annihRowPoly_eval` (`F-137`, `F-209`); `lem:claim-6-4` is left. `F-143`: repin
    `lem:case-I-realization-nonsimple` on `case_I_realization_nonsimple_gen`; a node for KT Claim
    6.6 (`exists_degree_two_removeVertex_of_no_simple_contraction`, with its first assertion); the
    case split for every $k$ (`case_I_hcontract_gen`) as a second pin of `lem:case-I-dispatch` or a
    node. *Expected:* +1 or +2 nodes; repins, −3 (hash changes); new edges.
  - [ ] **3.8 `case-ii.tex`, `genericity-and-count.tex`** (`F-147`, `F-152`, `F-209`'s
    extraction). `F-147`: a node for KT Lemma 6.7 (`splitOff_simple_of_noRigid`,
    `triangle_isProperRigidSubgraph`, `isKDof_zero_of_triangle`), which `lem:case-II-realization`
    and `lem:chain-data-extract` use; the three dead nodes are left. `F-152`: leave (retiring and
    joining nodes are not D fixes; stating the two lemmas generally is a statement change, for the
    report). `F-209`: a node for the rank form of the row extraction, for every framework
    (`exists_independent_panelRow_subfamily_of_le_finrank`), which `generic-lift.tex`'s two witness
    lemmas, Case II and Case III use. *Expected:* +2 nodes, +4 pins (hash changes); new edges.
  - [ ] **3.9 `case-iii.tex`, KT Claim 6.11 to KT eq. (6.29)** (`F-120`'s two, `F-157`, `F-159`;
    `F-009`'s `lem:case-III-claim612-eq644`). `F-120`: leave both doubles (each pair states one
    claim twice, and a merge is not a D fix). `F-157`: a node for the step from KT Claim 6.11 to
    the redundancy at the chosen normals (`exists_redundant_panelRow_ab_lam_of_rigidOn`). `F-159`:
    nodes for KT's $(G, p_1)$ of eq. (6.12) (`caseIIICandidate`) and for the rank bound of KT eq.
    (6.29) in its live form (`case_III_rank_certification`); the dead nodes are left (`F-158` is
    the report's), and `lem:case-III-transport-collapse` too (three pins).
    `lem:case-III-claim612-eq644`: the two `acolumn` steps unpinned. *Expected:* +3 nodes; pins
    +3, −2 (hash changes); new edges.
  - [ ] **3.10 `case-iii.tex`, the case $d = 3$ and the general case** (`F-163`, `F-167`,
    `F-171`). `F-163`: repin `lem:case-III-claim612-points-affineIndep-real-normals` on the general
    form `exists_homogeneousIncidence_of_normals_gen` (a note if the statement stays at $d = 3$);
    the four affine nodes are left. `F-167`: leave (the dispatch is dead by design, as its lead
    says). `F-171`: nodes for KT eq. (6.66) and the renaming (`interior_hρe₀_of_baseWidening`,
    `chainData_relabel_arm_hρGv`, `chainData_bottom_relabel`), or the two relabel nodes repinned
    on their general forms, whichever states what the dispatch's proof cites. *Expected:* +1 or +2
    nodes, or repins (hash changes); new edges.
  - [ ] **3.11 `molecule-modelling`, `molecule-application`, `generic-lift`** (`F-009`'s three,
    `F-010`'s `shadowGraph`, `F-214`, `F-219`, `F-224`'s screw map). `thm:projective-invariance`
    (7): leave (Crapo and Whiteley's transformation, with its three parts and (1)'s consequences;
    a role map). `lem:panel-hinge-dual-molecular` (8): its (1), the polarity on joins
    (`screwComplementIso` and its two extensor identities), splits into a node; the citations of
    the polarity in `pencil.tex` and `main-component.tex` are retargeted to it by the rule above;
    (2) keeps five pins, one result. `F-224`: a definition node before
    `thm:projective-invariance` for the screw map of a linear map of $K^{d+1}$
    (`screwEquivOfLinearEquiv`, `screwEquivOfLinearEquiv_mk_extensor`).
    `lem:molecule-graph-carrier` (5): leave (the construction and its clauses; `F-187` keeps the
    label bound's pin); its ten in-edges are task 4.7's. `F-214`: `def:two-extensor` pins
    `twoExtensor` alone (`pairIdxEquiv` unpinned; `twoExtensorPoly` with `twoExtensorPoly_eval` to
    `lem:generic-endpoints-abundance` or a lemma node); `lem:coordinate-extensor-basis` and
    `lem:extensor-map-rows` unpin `coordPoint` and `mapPlacement`. `F-219`:
    `def:generic-hinge-points` keeps `hingePointRow` and `IsGenericHingePoints`;
    `lem:hinge-rows-polynomial-in-points` keeps `hingeExtensorPoly_eval`. *Expected:* +2 or +3
    nodes; pins moved, about −5, +3 (hash changes); new edges and retargets.
  - [ ] **3.12 `jacobs.tex`** (`F-009`'s three, `F-192`, `F-197`, `F-202`). `F-192`: definition
    nodes for a tight partition and for $e_G(Q)$ take `IsTightPartition` and
    `crossingEdgesWithin` from their lemmas. `F-197`: a definition node for the normal and special
    cross edges rooted at a part takes `squareNormalCrossEdgesRootedAt` and, from
    `lem:normal-cross-count-partition` (4), `squareCutPairs`. `lem:singleton-part-converse` is
    repinned on `IsSquareTightPartition.squareSpecialCrossEdgesRootedAt_eq_edgesIn_neighborSet`
    if its statement states that form, else left. `F-202`: `def:two-core` pins `twoCore` alone; its three
    consequences and the three facts the degree-one rank uses go to lemma nodes, at most three pins
    each. `lem:square-cross-classification` (9): leave (one classification's conjuncts; a role
    map). *Expected:* +3 to +5 nodes; pins moved, perhaps +3 (hash changes if so); new edges, and
    `F-193`'s and `F-196`'s missing edges become edges to the definition nodes (task 4.7).
  - [ ] **3.13 `pencil.tex`, `main-component.tex`: helpers and doubles** (`F-010`'s `pathVertex`
    and `closedNbhd_subset_vertexSet`, `F-120`'s seven doubles, and of `F-009`
    `def:pencil-nondegenerate`, `thm:pencil-x0-main-component`, `lem:pencil-chain-span-certificates`,
    `lem:pencil-x0-main-picture-open` and `lem:pencil-bridge-fibre`). `lem:pencil-bridge-fibre`:
    `pathVertex` and its two lemmas unpinned (*Decisions*). `thm:pencil-jj-equality`:
    `closedNbhd_subset_vertexSet` unpinned. `F-120`: each doubled pin keeps one home, the node
    whose statement it proves, and a main result's node keeps its pin.
    `thm:pencil-x0-main-component`, all four of whose pins are doubles, keeps those that state its
    claim and `\uses` the rest. `def:pencil-nondegenerate`: leave, one pin per defined term, with
    `Graph.closedNbhd` unpinned unless the statement defines it. `lem:pencil-chain-span-certificates`:
    leave (four corner cases). `lem:pencil-x0-main-picture-open`: leave, after its double.
    *Expected:* no node; pins −4 to −11 (hash changes); retargets.
  - [ ] **3.14 `main-component.tex`: `c8a`'s splits** (`lem:pencil-x0-one-witness`,
    `lem:pencil-jj-embed-edges`, `lem:pencil-jj-rescale`; `notes/Phase40-simplify.md` *Moved to a
    later round*). `lem:pencil-x0-one-witness` (7) splits along its proof: the polynomial section
    (`Matrix.exists_mvPolynomial_section_mulVec_eq_zero`) to a node of its own, as the contraction
    step uses it too; the lifting matrix and its two kernel facts to a definition node; the claim
    keeps `x0Attains_of_exists`, and the two admissible-picture helpers are unpinned.
    `lem:pencil-jj-embed-edges` (11): a definition node for the embedding, with its structural facts
    unpinned, and the lemma keeping the invariance clauses (the lifting space, the pictures, the
    deficiency) with a role map. `lem:pencil-jj-rescale`: leave (one pin per clause). *Expected:*
    +3 nodes; pins moved, about −7 (hash changes); new edges.
- [ ] **4. E — edges**, one commit per chapter group, split where a group has more than about 90
  edges to add or review. *Expected* (each): the `\uses` the edge policy adds, moves and removes,
  listed in the commit before editing; pins and the `lean_decls` hash unchanged. The open's
  counts (missing; unbacked through a node / none) are estimates, since task 3 changes them.
  - [ ] **4.1 Round 1's chapters** (`F-001`, `F-006`'s part; 83; 5 / 19).
  - [ ] **4.2 `matroid-union` → `deficiency`** (`F-002`'s part, `F-006`'s part, `F-066`, `F-071`,
    `F-076`, `F-078`; 33; 4 / 44).
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
- [ ] **5. N — node order** (`F-019`, `F-029`, `F-050`, `F-071`, `F-119`; the forward screen re-run
  after task 4). Move a node where the move cures a forward `\uses` without creating one: within a
  chapter (principle E, *Node order*), or across chapters or sections where the ledger names the
  move (`F-019`'s theorem to the end of `sparsity.tex`; `F-071`'s KT Lemma 3.3 nodes before KT
  Lemma 3.6; `F-050`'s and `F-119`'s groups). A reference that stays forward keeps its sentence
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
- [ ] **7. U — status surfaces** (`F-099`, `F-173`, `F-204`, `F-226`, `F-229`). `formalization.yaml`:
  `F-099`'s three places (the PI, 2026-10-12), `F-173`'s (2) and `F-204`'s (2), Jacobs 1998's DOI.
  `README.md` and `home_page/index.md`: `F-173`'s (1), `F-204`'s (1), `F-226` and `F-229`. Each is
  aligned with the chapter it names; no main result's `declaration:` changes. *Expected:* the dump
  byte-identical.
- [ ] **8. R — the findings report** (`notes/Prose.md` §3 *R*), in `notes/Prose-report.md`. Each
  `S`, `L` and `M` entry gets the disposition `reported`; the report is not a stop.
  - [ ] **8.1 The `S` group** (65 entries): grouped by the kind of divergence, deduplicated and
    ranked, each with its evidence, a suggested disposition and a commit estimate. It is presented
    as one group, statements whose blueprint and formal texts disagreed after the formalization
    was declared complete, for what they show about the limits of autoformalization (the PI,
    2026-10-12, §1).
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

- None yet.

## Moved to a later round

`L` findings this round makes (a later Lean round), one line each naming the ledger ID. The
ledger's earlier `L` entries are task 8.2's.

- `F-230` (task 3.1): three pebble-game docstrings name the nodes their pins left.

## Blockers / open questions

- None.

## Hand-off / next phase

**Next concrete task: task 3.2, the node shapes of `matroid-union`, `body-bar`, `extensor` and
`meet`** (Opus, a fresh agent). The parent's dump is task 3.1's (3 286 lines, `1df3c3a7996203cf`;
*Current state*): regenerate it on the parent after `verify.sh` if the scratch copy is gone.
Before editing, read each named node, its pins' statements and its `--label` report, try the
change on a scratch copy of the TeX (*Decisions*, task 3.1), and make 3.2's *Expected* exact in
its line, its `## uses:` lines included (gate 3 (b)); then edit, and diff the after-dump against
it. Then task 3.3.

## Decisions made during this round

- **The slicing** (the open): 31 tasks against §3's ~15, which predates the script's counts. The
  ledger holds 536 missing and 397 unbacked edges, and an E task reads the prose of each unbacked
  one. It has 45 `N` entries, most of which propose a new node, a split, a move or a change of
  pins. N goes by chapter (14 tasks) and E by chapter group (9, split where a group has more than
  about 90 edges); the report takes two commits, since it ranks 132 entries.
- **The honesty gate for a new node, the retargeting rule, and the node-shape and edge
  policies** (§3 *N*, *E*): settled at the open, under *Scope*.
- **The order:** N, then E, then the node order, then T, U, R and X. An N fix changes what the
  report calls missing; E's additions and removals change which `\uses` point forward.
- **The tooling first** (task 2): the drawn graph is a transitive reduction, so the open's dump
  cannot show a removal or an implied addition, and the gate would not be exact without it.
- **The `## uses:` section's lines** (task 2): every node, and every other labelled environment
  with a `\uses` (the example and `rem:kt-lemma-44`), as the pins section lists the example, so
  an edit of either's `\uses` (task 4.3's `F-007`) shows too. Targets are raw: each part sorted,
  duplicates kept, a non-node target included, `-` for an empty part.
- **`pathVertex`** (task 3.13): `40-simplify`'s `c8` unpinned the bridge step's four `pathVertex`
  lemmas and left `lem:pencil-bridge-fibre`'s `pathVertex` (`notes/Phase40-simplify-verdicts.md`).
  `F-010` measures 30 missing in-edges through it, five of them forward from `rigidity-matrix.tex`
  and `deficiency.tex`. A path's vertex sequence is notation, not a result, so it is unpinned.
- **The report's home** is `notes/Prose-report.md`: the ledger keeps each finding, and the report
  ranks them for the PI (`notes/CLAUDE.md` *One canonical home*).
- **Try each N fix on a scratch copy first** (task 3.1). Copy `blueprint/src`, edit the copy, and
  read its `--tex-root` report: an unpin that leaves a `\uses` of the node or of its users with no
  Lean basis strands a clause the pin states, so the pin is not a helper (task 3.1 kept
  `Reachable.out_le` and `newOrient` so). The drawn edges follow from the copy's `\uses` by the
  script's `ancestors_map` and `transitive_reduction`; an edge is dashed when its source is in the
  user's statement `\uses`. On the parent this reproduced the built graph's 1 292 edges exactly.
