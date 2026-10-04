# Phase 40 cleanup round 4/5 — `40-simplify`, the deep simplification recon (work log)

**Status:** in progress (opened 2026-10-04); Stop 2 answered 2026-10-04, the landings next.
Round 4 of the five post-Phase-40 cleanup rounds. Their order, stops and the PI's decisions are in
`notes/Cleanup40.md`, and `.claude/autopilot/queue.toml` is the authority for which rounds are
done. The round is a read-only Opus recon over the pencil surface, looking for bigger
simplifications (`notes/Cleanup40.md` §2 *Round 4*), then the items the PI sanctions. Tasks 1–7
wrote 63 verdicts (`notes/Phase40-simplify-verdicts.md`). At Stop 2 the PI sanctioned the
recommended package with `7d`'s chapter restated (*Autopilot: for the PI*), and task 9 sliced it
into 18 landings, 10a–10r (8 Opus). Then task 11 closes.
**Next concrete task:** 10a (Sonnet, TeX): task 3's batch, which unpins what 10b deletes. Round
manual: `CLEANUP.md`.

## Autopilot: for the PI

### 2026-10-04 — `NEEDS_PI`: Stop 2, the round's verdicts (planned stop, `notes/Cleanup40.md` §2)

**What happened.** Task 8 wrote Stop 2 from the 63 verdicts; the full entry is at `aae919cf`: the
findings, the rung corrections (Opus for a ⚠Z proof rewrite), eight decisions, the table, round 3's
`r1`–`r8`, and two landing orders. Its default: "Sanction every GO as recommended: `1a` retire, `r1`
delete, decision 4's statement moves, `a2` last, `7d` (i), `c3a` NO-GO, `a7` kept, and round 3's
`r2`–`r8` as written (`r7`'s node built)." Decision 5 asked whether the chapter keeps CONTRACT-R's
own proof by KT's Lemma 6.3, (i), or states it as CONTRACT-A's corollary, (ii).

**PI, 2026-10-04:** (transcribed verbatim from the attended session that reviewed Stop 2)
- On the eight decisions, after a summary that agreed with every recommendation: "Let's approve
  your recommendations above except 5. For 5, I think we should restate if it simplifies the
  exposition."
- Then, given the session's reading that (ii) does simplify (*Decisions*), and its proposal to
  record this answer in `notes/pencil/adjudications.md`: "OK, ii looks good and let's update the
  adjudications."

**What follows.** Stop 2 is closed. The sanction is the default with `7d` (ii): 18 landings, 8 of
them Opus, about −7 770 Lean lines net (task 10's 10a–10r). The answer is archived in
`notes/pencil/adjudications.md` (2026-10-04), whose entry supersedes the 2026-09-29 record's
"stays, untouched".

## Current state

**Stop 2 is answered and the landings are sliced** (task 9, 2026-10-04, docs only). The PI
sanctioned the recommended package with `7d`'s chapter restated (*Autopilot: for the PI*;
*Decisions*). Task 10 lists 18 landings, 10a–10r, in dependency order, each with its rung and
gates; the NO-GOs and the items not sanctioned are one-line verdicts under *Decisions*. Nothing is
mid-stream. Next is 10a, then each landing in turn, then task 11 closes.

**Verified at the open** (the Lean tree is `0b260626`'s and the blueprint `30e79461`'s; neither has
changed since round 3's close):
- Whole-project `lake build` green, 3003 jobs: 0 `warning:`, 0 `error:` and 0 `failed to cache
  artifact` lines. `lake lint` green.
- `#print axioms` on all 19 `formalization.yaml` main results gives `[propext, Classical.choice,
  Quot.sound]`. Round 3's harness was diffed against the yaml's `declaration:` and `file:` fields
  (19 names in order, 14 imports: identical), copied to `scratch/40-simplify/Axioms.lean`
  (gitignored) and run with `lake lean`. Its output is round 3's close's, byte for byte apart from
  the harness's own path. Re-run it the same way at the close.

**The surface**, as round 1 set it (`notes/Cleanup40.md` §2 *Round 1*):
- the Lean: `Molecular/Molecule/Pencil/**`, now 42 files and 33 691 lines; Phase 40's edits in 26
  Lean files outside it (`git diff --stat c9d26ef9^ 91fcd24a -- CombinatorialRigidity/`), with
  rounds 1–2's moves and additions; and, for task 1, every declaration the two chapters pin
  (Phase 39 put some in `Induction/ForestSurgery/`, e.g. `Graph.pencil_reduction`);
- the blueprint: `pencil.tex` (1 589 lines) and `main-component.tex` (5 696), plus Phase 40's nodes
  in `deficiency.tex`, `rigidity-matrix.tex`, `molecular-induction.tex` and `panel-layer.tex`
  (`notes/Phase40-cleanup.md` *Scope*).

## Scope and standing rules

From `notes/Cleanup40.md` §1–§2, restated only as far as a task needs them.

- **Read-only recon.** Tasks 1–9 are docs commits. Each edits this log, its verdicts file
  (`notes/Phase40-simplify-verdicts.md`, which these rules bind), and the next-task pointer
  in ROADMAP's queued-rounds bullet and `notes/Cleanup40.md`'s header (`CLAUDE.md`, F17); tasks 8
  and 9 also the other status surfaces. No Lean, no blueprint TeX, no `formalization.yaml`,
  no `queue.toml`. A probe or spike goes in `scratch/40-simplify/<task>/` (gitignored) and runs
  with `lake lean <file>`, never `lake env lean`. `git status` is clean apart from the commit's
  own files.
- **Route questions get compiler-checked spikes** (`notes/coordinate-phase-rescue.md` §6). Build
  the candidate composition with `sorry` at each gap, and record the exact kernel-checked residual
  goals, not a prose verdict.
- **Evidence.** A claim about a declaration comes from its statement and body, never its docstring
  (`CLAUDE.md` *Docstrings are not evidence*). Liveness is the Lean call chain (`CLEANUP.md`
  *Liveness*): task 1's closure here, and trial deletion with a whole-project build at landing;
  never grep or `\uses` alone.
- **No statement moves in the recon.** A verdict may propose a headline signature change, or a
  change to a blueprint statement's strength. Only the PI's sanction at Stop 2 lets one land
  (`notes/Cleanup40.md` §2, *All five rounds*).
- **Prior evidence stands unless a task brings a new argument.** Round 1's task 17 (a
  `Fin.succAbove`-general split-off ear nets no shorter) and task 24 (no `_three`/`_four`
  unification); round 2's residual shared tail (about 13 lines a hub, left); round 3's eight
  recommendations, which task 8 presents as written unless a task here changes a premise.
- **A verdict** is one entry in its task's subsection of the verdicts file, at most five lines:
  `**<id>, <name>: GO**` (or NO-GO); one sentence of why; the commit estimate (commits, rung, ⚠Z
  for the fragility zone); what it changes (a headline signature, a blueprint statement's strength,
  the dependency graph, or nothing a reader sees); any verdict it depends on; its evidence (read,
  measured, or a spike's residual). The detail goes in the task's commit message.
- **Gates for tasks 1–9.** `git diff --stat` shows docs only. This log stays under ~500 lines,
  forward-weighted, with a **Status:** header under 300 words and *Decisions* entries of at most 8
  lines. `notes/check-phase-note.py`'s name pattern skips `Phase40-*.md`, so run its `parse` and
  `offenders` on this file directly, as the open did. No local machine paths in the diff or the
  message.
- **Rungs.** The recon tasks are Opus (`notes/Cleanup40.md` §2 *Round 4*). A landing's rung is
  its verdict's: Opus in the fragility zone (`.claude/commands/coordinate-phase.md` *Fragility
  zone*), otherwise rung-mapped.

## Input IDs

`notes/Cleanup40.md` §2 *Round 4* lists the round's inputs, one line each, and this log names them
by their position there. Each input has one owner task, which writes its verdict; other tasks may
read it. Round 3's `r1`–`r8` are recommendations already: task 8 presents them, and task 1 answers
the one question `r1` left open, whether to delete its 29 off-headline names.

- `a1`–`a7`, round 1's candidates: `a1` the one-ended chain-side degree pin; `a2` the six
  `[DecidableEq β]` binders; `a3` the finsum rewrite; `a4` `pencilPair_of_habitat_ncard_eq_four`;
  `a5` `Pair2.lean`'s #4/#6 tails; `a6` `Arms.lean`'s `|C| = 0`/`|C| = 1` split; `a7`
  `Graph.X0Attains.of_closedEar`.
- `b1`–`b2`, round 2's: `b1` `.compl` against `ᶜ` in the two hubs; `b2` the merged hub's `hne`.
- `m1`–`m7`, round 3's *Moved* lines: the six missing `\uses` edges and the unfilled pair node, in
  that list's order.
- `c1`–`c9`, round 3's structural candidates, in that list's order (`c4` is the "…and its
  statement" line, `c8` the four-pin nodes, `c9` the caller-less toolkit halves).
- `r1`–`r8`, round 3's build-or-leave recommendations, as numbered there.
- `q1`–`q3`, the coordinator's starting questions: `q1` the open ears, `q2` `Pencil/` against
  `AlgebraicInduction/`, `q3` the Lean that feeds neither headline.
- Added by the tasks: `1a`, `1b`, `1c-i` and `1c-ii` are task 1's hand-ons (a)–(c) to task 2. A
  new finding takes the ID of the input it bears on, with a letter (`q3a`, `c3a`). Task 7's findings
  on no listed input are `7a`–`7i`.

## Lemma checklist (the round's task list)

One commit per task, in this order. Each line names the inputs it owns; its commit names its
verdicts.

- [x] **1. L — the liveness map** (`q3`, `b2`, and `r1`'s deletion question; Opus, docs). The
  closure of the 19 main results, the off-closure clusters, the verdicts and the hand-ons are in
  the verdicts file, *Task 1*.
- [x] **2. R — `pencil.tex`'s reduction layer** (`a2`, `a4`, `m1`–`m5`, `c2`–`c4`, design §6,
  task 1's hand-ons; Opus, docs). The shape and the verdicts are in the verdicts file, *Task 2*.
- [x] **3. N — node shapes outside the reduction layer** (`a1`, `m6`, `m7`, `c1`, `c5`–`c8`, task
  1's hand-ons; Opus, docs). Which side moves where a node and its pins disagree, or a node bundles
  results: the verdicts are in the verdicts file, *Task 3*.
- [x] **4. E — the open ears** (`q1`, `a7`, `c9`, with task 1's sizes; Opus, docs; two spikes).
  One argument or several, and if one, what shared statement: the reading and the verdicts are in
  the verdicts file, *Task 4*.
- [x] **5. A — where `Pencil/` re-proves** (`q2`, `b1`, `a3`; Opus, docs; five spikes). What
  `Pencil/` re-proves of `Theorem55.lean`, `Meet.lean` and the project's mathlib mirrors, with the
  hubs' `ᶜ` and the degree-sum pair: the reading and the verdicts are in the verdicts file,
  *Task 5*.
- [x] **6. P — Phase 39's producers** (`a5`, `a6`, and task 5's `q2d`; Opus, docs; four spikes).
  Whether a recorded cross-proof duplication admits a shared lemma that nets shorter: the reading
  and the verdicts are in the verdicts file, *Task 6*.
- [x] **7. G — the remaining long proofs** (round 1's §C screen, now structural, and task 6's
  hand-on; Opus, docs; five spikes). Is any long proof longer than its argument: the re-rank and
  the verdicts are in the verdicts file, *Task 7*.
- [x] **8. W — Stop 2, the write-up** (`r1`–`r8`, and every verdict; Opus, docs; `NEEDS_PI`). The
  entry is under *Autopilot: for the PI*; the round waits on the PI.
- [x] **9. S — slice the sanctioned items** (Opus, docs). The PI's answer is under *Autopilot*
  and *Decisions*, and archived in `notes/pencil/adjudications.md`; `c8a` moved to **PROSE**.
- [ ] **10. B — the sanctioned items land.** One commit each, in this order, green at every
  commit: whole-project `lake build` warning-clean and `lake lint` green; the blueprint gates
  (`blueprint/CLAUDE.md` *Static checks before commit*) on any TeX edit; and
  `CombinatorialRigidity/CLAUDE.md` *Forward-mode slices* on a changed statement, an additive
  successor or a deletion. A deletion is confirmed by trial deletion and a whole-project build. A
  commit that touches a headline re-runs the axioms harness (*Current state*). The rungs are Stop
  2's, corrected: Opus for a ⚠Z proof rewrite, even where a spike exists. The spikes for `a5`,
  `a6`, `a6a` and `7a`–`7d` are in `scratch/40-simplify/6/` and `7/` (gitignored). Each item's
  wording and evidence is in the verdicts file; lines are net Lean lines.
  - [ ] **10a. Task 3's TeX batch** (Sonnet). `m6`, `m7`, `1c-i`, `c1`, the two-hubs edge, `c8`'s
    four, `c9`'s clauses, `c5`'s node, the polynomial's pins. It unpins first, so 10b strands no
    pin.
  - [ ] **10b. `r1`'s deletion** (Sonnet, ⚠Z files). `TwoCut.lean` and 20 more of D5's names, with
    `q3b` and the Lean 10a unpinned (the polynomial, `c5`, `c8`'s standing pin, `c9`): −1 159.
  - [ ] **10c. `c6` + `c7`** (Sonnet). Restate `lem:pencil-condition-linear` and pin the iff;
    `IsMainPicture.exists_mvPolynomial`, the open pin its corollary: +19.
  - [ ] **10d. `q2b` + `q2c` + `a3`** (Sonnet, not ⚠Z). One perp-dimension lemma, the mirror's
    common non-root, `two_mul_ncard_le_ncard_edgeSet` by `finsum_mem_const`: −70.
  - [ ] **10e. `q1a`** (Sonnet, not ⚠Z). `Graph.X0Attains.of_openEar_of_cert`: −43.
  - [ ] **10f. `r7`'s node** (Sonnet, TeX). `Graph.exists_isMinimalKDof_spanning_subgraph` in
    `deficiency.tex`, beside `lem:subgraph-minimality`; four proofs gain a `\cref`.
  - [ ] **10g. `c3`'s Lean** (Opus; axioms harness). `_of_arms_pair` over every nonempty graph,
    `pencilPair_of_nonempty` from it, and the new lemma for the pair's three leaves: about −21.
  - [ ] **10h. `c3`'s TeX** (Opus). The split node, with `c2`, `c4`(b), `m2`, `m4`, `m5` and `1b`'s
    node; the kernel statement leaves (`1a`).
  - [ ] **10i. `1a`'s deletion** (Sonnet, ⚠Z files). `_of_card`'s cluster with `q3a`, `1b`,
    `1c-ii`, and the girth chain with its eight nodes; ROADMAP §40's verbatim "stays as conditional
    theorems" goes: −3 636.
  - [ ] **10j. `m3` + `7c`** (Opus, ⚠Z). `_three` from `G.Simple` by
    `linearIndependent_pointJoin_triangle`, moved into `MainComponent/`; two nodes go: −171.
  - [ ] **10k. `a6` + `a6a`** (Opus, ⚠Z; axioms harness, as `a6a` is in 10 of the 19 closures).
    One assembly for each cut case's two branches; the two crossing lemmas to `Deficiency.lean`:
    −264.
  - [ ] **10l. `a5`** (Opus, ⚠Z). One tail for `Pair2.lean`'s #4 and #6: −295.
  - [ ] **10m. `7a`** (Opus, ⚠Z). The pendant cut by `lem:pencil-generic-steer`, one route for
    every degree (the larger form): −1 470.
  - [ ] **10n. `7b`** (Opus, ⚠Z). One glue for a cut's two sides, four sites: −213 (about −280).
  - [ ] **10o. `q2a` + `b1`** (Sonnet, ⚠Z, mechanical). Theorem55's cut-edge bricks published
    under Arms' names; the PanelLayer hub's `ᶜ`: −105.
  - [ ] **10p. `7d`'s chapter, (ii)** (Opus, TeX). CONTRACT-R as CONTRACT-A's corollary, the two
    contraction sections merged; `-core-plane`, `-core-rank`, `-limit`'s clause (1) and a clause of
    `cor:pencil-flat-x0` retire, unpinned. The overview's list of steps where no two open
    conditions meet, and the roadmaps, follow.
  - [ ] **10q. `7d`'s Lean** (Sonnet, not ⚠Z). `Graph.X0Attains.of_rigidContract` from
    `of_additiveContract`, 238 → 22 lines, and the 122 lines 10p unpinned: −338.
  - [ ] **10r. `a2`** (Sonnet, last; axioms harness). `[DecidableEq β]` off `pencil_conjecture`
    and the pinned theorems, by `classical`: the two sites left after 10g–10i.
- [ ] **11. X — close the round** (`CLEANUP.md` *Workflow* rule 5; docs). Whole-project
  `lake build` and `lake lint` green. The axioms harness re-diffed against `formalization.yaml`
  and re-run with `lake lean`: 19 of 19 at the three standard axioms. The ROADMAP row reads ✓, and
  `40-simplify`'s row in `.claude/autopilot/queue.toml` gets `done = true` (nothing else there
  changes). The status surfaces name round 5, `40-docs`, as next. *Moved to a later round* is
  mirrored into `notes/Cleanup40.md` §2 *Round 5*, or ROADMAP's **PROSE** bullet.

## Verdicts (Stop 2's inputs)

In their own file, `notes/Phase40-simplify-verdicts.md` (moved at task 4; *Decisions*). Each recon
task adds a subsection there, `### Task N (X)`, with one entry per input it owns, in the format
under *Scope*.

## Moved to a later round

Each line gives the task, its target (round 5, `40-docs`, or **PROSE** in ROADMAP's queue) and a
one-line reason. The same line goes into the target's plan section in the same commit.

- **Task 3's `c8a` → PROSE** (sanctioned at Stop 2). Seven nodes here with four or more pins
  (`def:pencil-nondegenerate`, `lem:pencil-x0-one-witness`, `thm:pencil-x0-main-component`,
  `lem:pencil-jj-rescale`, `lem:pencil-jj-embed-edges`, `thm:pencil-jj-equality`,
  `lem:pencil-chain-span-certificates`), mostly one pin per clause: for PROSE's audit of bundled
  nodes (principle D), not this round's.

## Blockers / open questions

- None. Stop 2 is answered (*Autopilot: for the PI*).

## Hand-off / next phase

**Stop 2 is answered; the landings run.** The smallest next commit is **10a** (Sonnet, TeX): task
3's batch (`m6`, `m7`, `1c-i`, `c1`, the two-hubs edge, `c8`'s four, `c9`'s clauses, `c5`'s node,
the polynomial's pins), which unpins what 10b's deletion removes; the blueprint gates. Then 10b–10r
in order (task 10), one commit each at its listed rung. 10i is the first to touch ROADMAP §40 (its
"stays as conditional theorems", marked verbatim). After 10r, task 11 closes the round.

## Decisions made during this round

- **2026-10-04, the open: the granularity.** Seven recon tasks, each one coherent question over a
  bounded reading surface. The mechanical map comes first, since three tasks' verdicts rest on it.
  Then come the two blueprint regions whose inputs are statement-against-pin questions, and then
  the three deeper questions. The write-up is its own commit because it is the stop. A task per
  input would re-pay a dispatch's reading for each of 36 inputs; fewer tasks would put two of the
  spike-bearing tasks 4–6, or task 7's long reading, into one sitting. The landings are sliced
  after Stop 2, once the PI has chosen them.
- **Probes stay in scratch.** No recon task commits a script. Its figures are tagged *measured,
  script not retained* (`HARNESS.md` *Reproducibility*), as rounds 1 and 3 did for liveness. No
  deletion rests on such a figure: a sanctioned retirement is re-verified at landing by trial
  deletion and a whole-project build (`CLEANUP.md` *Liveness*).
- **The landing order is set at task 9, not now.** It depends on what the PI sanctions, and on
  task 1's map: a retired cluster can moot another verdict, as retiring `TwoCut.lean` would moot
  `b2` and half of `b1`.
- **2026-10-04, task 1: a pinned cluster goes to the task that reads its node.** The checklist
  named hand-ons to tasks 2 and 4 only; the map found pinned dead nodes in sections neither reads.
  Task 2 takes those the reduction layer `\uses`; task 3, which already owns `c5`, `c6`, `c8` and
  the girth chain's `a1`, takes the rest outside the ears, as one-line verdicts where prior
  evidence stands (round 3 kept the unused parts the chapter's opening names).
- **2026-10-04, task 4: the verdicts move to their own file** (the coordinator's decision). At 440
  lines, with tasks 4–8 still to write, the log would pass its ~500-line tripwire. *Verdicts*,
  tasks 1–3 verbatim, moved to `notes/Phase40-simplify-verdicts.md`, as round 3 moved its exemplar
  to `notes/Phase40-exposition-exemplar.md`; *Verdicts* here points there, *Scope* binds it, and
  each task from 4 on writes its subsection there.

- **2026-10-04, Stop 2: the PI's sanction** (verbatim under *Autopilot*): "Let's approve your
  recommendations above except 5. For 5, I think we should restate if it simplifies the
  exposition." Then: "OK, ii looks good and let's update the adjudications." So the default stands
  with `7d` (ii): `1a` retired, `r1` deleted, decision 4's statement moves, `a2` last, `c3a`
  NO-GO, `a7` kept, round 3's `r2`–`r8` as written (`r7` built), at the corrected rungs. Archived
  in `notes/pencil/adjudications.md`, superseding the 2026-09-29 record's "stays, untouched".
- **`7d` (ii): restating simplifies** (the reading the PI accepted). KT's Lemma 6.3 is one lemma,
  for any proper rigid subgraph; its proof takes realizations of the rigid piece (KT Lemma 3.5) and
  of the contracted graph (KT (6.1)) independently and joins them by the block bound (pp. 673–675):
  CONTRACT-A's shape. The chapter runs the curve-and-kernel argument twice, A's section as R's
  variant. As A's corollary R needs `cor:pencil-flat-x0` at `H`, `def₃ ≤ def₂ = 0` and `def₂`'s
  conservation. Stop 2's "(i) keeps KT's order" undersold (ii).

### Not sanctioned, or NO-GO (one line each; wording and evidence in the verdicts file)

- `b2`: moot, as `TwoCut.lean` goes with `r1`.
- `a4`, `c4`(a), `a1`: moot, as `1a`'s cluster and the girth chain retire.
- `c3a`: NO-GO; the PI's 2026-09-28 proof term for `pencil_conjecture` stands.
- `a7`, `Graph.X0Attains.of_closedEar`: kept, the PI's own call (Phase 40g decision 2).
- `q3c`: kept; API beside its definitions, and one design witness (255 lines).
- `m1`: NO-GO; the hub threshold is motivation, and the edge would put `sec:pencil-cycle` under
  the headline.
- `sec:pencil-duality`, `sec:pencil-cycle`, and task 1's (b) and (c): kept (prior evidence; clauses).
- `lem:pencil-x0-two-hubs-obstruction`: kept as a design witness; only its edge goes (10a).
- `q1`, `q1b`, `q2d`, `a6b`: NO-GO; four arguments, or a shared lemma nets too little.
- `7e`–`7i`: NO-GO; each proof is as long as its argument.
- `c8a`: NO-GO here; moved to **PROSE** (*Moved to a later round*).
- Round 3's `r2`–`r6` and `r8`: left unbuilt or unpinned, as round 3 wrote.
