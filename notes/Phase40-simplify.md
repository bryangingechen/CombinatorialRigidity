# Phase 40 cleanup round 4/5 — `40-simplify`, the deep simplification recon (work log)

**Status:** in progress (opened 2026-10-04); Stop 2 answered 2026-10-04, the landings next.
Round 4 of the five post-Phase-40 cleanup rounds. Their order, stops and the PI's decisions are in
`notes/Cleanup40.md`, and `.claude/autopilot/queue.toml` is the authority for which rounds are
done. The round is a read-only Opus recon over the pencil surface, looking for bigger
simplifications (`notes/Cleanup40.md` §2 *Round 4*), then the items the PI sanctions. Tasks 1–7
wrote 63 verdicts (`notes/Phase40-simplify-verdicts.md`). At Stop 2 the PI sanctioned the
recommended package with `7d`'s chapter restated (*Autopilot: for the PI*), and task 9 sliced it
into 18 landings, 10a–10r (8 Opus). 10a–10n landed 2026-10-04. Then task 11 closes.
**Next concrete task:** 10o (Sonnet, ⚠Z, mechanical): `q2a` + `b1`, Theorem55's cut-edge bricks
under Arms' names and the PanelLayer hub's `ᶜ`, with 10m's caller-less lemma deleted. Round
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
gates; the NO-GOs and the items not sanctioned are one-line verdicts under *Decisions*.

**Landed so far** (one line each; the detail is in each commit's message):
- **10a** `f53dace5`, TeX: task 3's batch. Of the declarations it unpinned, the eight dead ones went
  in 10b; the rest are live helpers and stay unpinned (`Graph.liftingRestrict`, `restrictPoly`, the
  `pathVertex_*` lemmas, the steering helper and others; the coordinator's split, `eb333e0c`).
- **10b** `c48d323e`, Lean: `r1`'s deletion, `q3b` and 10a's eight dead declarations, 38 in all;
  −1 340 Lean lines against the estimate's −1 159 (the difference is `TwoCut.lean`'s header and the
  docstrings). No listed name had a live caller. Kept of D5's list: the paid names, the two B5/B6
  pins and four live helpers (`bddAbove_range_partitionDef_merged`,
  `span_jointRows_eq_map_dualAnnihilator`, `finrank_span_jointRows`, `map_screwDiff_comm`).
- **10c**, Lean + TeX: `lem:pencil-condition-linear` restated to the iff
  `Graph.IsAdmissiblePicture.mem_liftingSpace_iff_coplanar` (dropping its pencil-realization
  clause, `lem:pencil-config-distinct-realization`'s statement), and
  `Graph.IsMainPicture.exists_mvPolynomial` added before `Graph.exists_mvPolynomial_isMainPicture`,
  now its 4-line corollary; +23 net Lean lines (task 9 estimated +19).
- **10d**, Lean only: `Meet.lean`'s new `finrank_toDualPerp_add_finrank_span` feeds the five
  existing perp-dimension lemmas (`q2b`); `Engine.lean`'s common-non-root lemma by the project
  mirror `MvPolynomial.exists_eval_ne_zero_of_forall_ne_zero` (`q2c`); `CoverageTheoremS.lean`'s
  `two_mul_ncard_le_ncard_edgeSet` by `Set.Finite.ncard_biUnion` + `finsum_mem_const` (`a3`); no
  statement changed. −64 net Lean lines (task 9 estimated about −70).
- **10e**, Lean only: `Ear.lean`'s new `Graph.X0Attains.of_openEar_of_cert` (`q1a`) is the shared
  certificate step; `Chain.lean`'s `of_openEar` (`k ≥ 5`) and `Short.lean`'s `of_openEar_two`
  (`k = 2`) now call it, statements unchanged. `span_supportExtensor_eq_top_of_linearIndependent`
  loses its only Lean caller but stays (`lem:pencil-ear-hinge-span`'s pin; no TeX in this commit).
  −38 net Lean lines (task 9 estimated about −43).
- **10f**, TeX only: `lem:minimal-kdof-spanning-subgraph` in `deficiency.tex` beside
  `lem:subgraph-minimality` (`r7`), pinning `Graph.exists_isMinimalKDof_spanning_subgraph`; its
  three callers (`thm:theorem-55-6-genuine`, `-rows`, `-multigraph`) gain the `\uses` edge, and
  `-rows`'s `\texttt` mention becomes a `\cref`; `Deficiency.lean`'s docstring reworded to name
  the node.
- **10g**, Lean + one TeX clause: `pencil_conjecture_of_arms_pair` over every nonempty graph, its
  first part the new `pencilPair_loop_base_cut` (unpinned until 10h); `pencilPair_of_nonempty`
  through it; −31 net Lean lines (task 9 estimated about −21); axioms harness 19 of 19.
- **10h**, TeX + four Lean docstrings: the pair theorem restated to `_of_arms_pair` alone, the new
  `lem:pencil-pair-loop-base-cut` pinning `pencilPair_loop_base_cut`; the kernels and
  `thm:pencil-conditional-realization` left, so no `\lean{}` names 10i's deletions.
- **10i**, Lean + TeX: `1a`'s deletion — design §6's `_of_card` cluster with `q3a`, `1b`,
  `1c-ii` and the girth chain's eight nodes gone; ROADMAP §40's "stays as conditional theorems"
  reworded. −4286 net Lean lines (task 9 estimated −3636).
- **10j**, Lean + TeX: `pencilPair_of_simple_ncard_eq_three` (from `G.Simple`, hinges by
  `linearIndependent_pointJoin_triangle`) in `GenericTriangle.lean`; `Base.lean`, two pins and
  two nodes gone. −226 net Lean lines (task 9 estimated −171).
- **10k**, Lean only: each cut case's two branches as one assembly (`a6`, `a6a`), the crossing
  lemmas to `Deficiency.lean`; −261 net Lean lines (task 9 estimated −264); axioms 19 of 19.
- **10l**, Lean only: #4 and #6 through one shared tail, `..._induce_pendant_of_hubLI` (`a5`, the
  spike's name and statement); −339 net Lean lines (task 9 estimated −295).
- **10m**, Lean + TeX: `hasGenericPencilRealization_pendant_of_IH`, the pendant cut by
  `lem:pencil-generic-steer` at every degree; `dead7aB`'s 11 names gone, and #4's callee
  `Graph.pencilHub_iff_induce_of_degree_ne` (`Motive.lean`) left caller-less, kept per the
  scope-pin; −1593 net Lean lines (task 9 estimated −1 470); axioms 19 of 19.
- **10n**, Lean only: one glue, `exists_hasPencilPanelRealization_glue` with
  `HasPencilPanelRealization.restrict` (`Arms.lean`), at all four sites, 10l's pendant tail too;
  −298 net Lean lines (task 9 estimated about −280); axioms 19 of 19.

Next is 10o, then each landing in turn, then task 11 closes.

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
  - [x] **10a. Task 3's TeX batch** (Sonnet). `m6`, `m7`, `1c-i`, `c1`, the two-hubs edge, `c8`'s
    four, `c9`'s clauses, `c5`'s node, the polynomial's pins. It unpins first, so 10b strands no
    pin. Landed 2026-10-04; the exact unpinned declarations are in *Current state*.
  - [x] **10b. `r1`'s deletion** (Sonnet, ⚠Z files). `TwoCut.lean` and 20 more of D5's names, with
    `q3b` and the Lean 10a unpinned (the polynomial, `c5`, `c8`'s standing pin, `c9`). Landed
    2026-10-04: −1 340 net Lean lines (task 9 estimated −1 159).
  - [x] **10c. `c6` + `c7`** (Sonnet). Restate `lem:pencil-condition-linear` and pin the iff;
    `IsMainPicture.exists_mvPolynomial`, the open pin its corollary: +19. Landed 2026-10-04: +23
    net Lean lines.
  - [x] **10d. `q2b` + `q2c` + `a3`** (Sonnet, not ⚠Z). One perp-dimension lemma, the mirror's
    common non-root, `two_mul_ncard_le_ncard_edgeSet` by `finsum_mem_const`. Landed 2026-10-04:
    −64 net Lean lines (task 9 estimated −70).
  - [x] **10e. `q1a`** (Sonnet, not ⚠Z). `Graph.X0Attains.of_openEar_of_cert`: −38 (estimate −43).
    Landed 2026-10-04.
  - [x] **10f. `r7`'s node** (Sonnet, TeX). `Graph.exists_isMinimalKDof_spanning_subgraph` in
    `deficiency.tex`, beside `lem:subgraph-minimality`; four proofs gain a `\cref`. Landed
    2026-10-04: the node's statement/proof as written; of the four Lean callers, three distinct
    TeX nodes gain the `\uses` edge (two callers share `thm:theorem-55-6-genuine`), and the one
    that named the step by `\texttt` (`thm:theorem-55-6-rows`) gets the `\cref` in place of it.
  - [x] **10g. `c3`'s Lean** (Opus; axioms harness). `_of_arms_pair` over every nonempty graph,
    `pencilPair_of_nonempty` from it, and the new lemma for the pair's three leaves: about −21.
    Landed 2026-10-04: −31; the lemma is `pencilPair_loop_base_cut`, a conjunction of
    `Graph.pencil_reduction`'s three arm hypotheses at `PencilPair K 3`.
  - [x] **10h. `c3`'s TeX** (Opus). The split node, with `c2`, `c4`(b), `m2`, `m4`, `m5` and `1b`'s
    node; the kernel statement leaves (`1a`). The new node pins `pencilPair_loop_base_cut` (10g);
    10g's clause in `fmlnote:pencil-conditional-realization-pair-kernels` (the first pin concludes
    at every multigraph with a body) goes with the rewrite. Landed 2026-10-04: both fmlnotes went.
  - [x] **10i. `1a`'s deletion** (Sonnet, ⚠Z files). `_of_card`'s cluster with `q3a`, `1b`,
    `1c-ii`, and the girth chain with its eight nodes; ROADMAP §40's verbatim "stays as conditional
    theorems" goes. With the girth chain's nodes go the chapter opening's sentence on
    `sec:pencil-girth-chain` ("Three parts" becomes two) and, with `1c-ii`'s node,
    `lem:pencil-base-case`'s edge to it (re-aimed per `1c-ii`'s verdict). Landed 2026-10-04:
    −4286 net Lean lines (task 9 estimated −3636).
  - [x] **10j. `m3` + `7c`** (Opus, ⚠Z). `_three` from `G.Simple` by
    `linearIndependent_pointJoin_triangle`, moved into `MainComponent/`; two nodes go: −171.
    Landed 2026-10-04: −226 net Lean lines.
  - [x] **10k. `a6` + `a6a`** (Opus, ⚠Z; axioms harness, as `a6a` is in 10 of the 19 closures).
    One assembly for each cut case's two branches; the two crossing lemmas to `Deficiency.lean`:
    −264. Landed 2026-10-04: −261 net Lean lines.
  - [x] **10l. `a5`** (Opus, ⚠Z). One tail for `Pair2.lean`'s #4 and #6: −295. Landed
    2026-10-04: −339 net Lean lines; 10m keeps the tail as the one pendant route.
  - [x] **10m. `7a`** (Opus, ⚠Z). The pendant cut by `lem:pencil-generic-steer`, one route for
    every degree (the larger form): −1 470. Landed 2026-10-04: −1593 net Lean lines.
  - [x] **10n. `7b`** (Opus, ⚠Z). One glue for a cut's two sides, four sites: −213 (about −280).
    Landed 2026-10-04: −298 net Lean lines, all four sites.
  - [ ] **10o. `q2a` + `b1`** (Sonnet, ⚠Z, mechanical). Theorem55's cut-edge bricks published
    under Arms' names; the PanelLayer hub's `ᶜ`: −105.
    Also delete `Graph.pencilHub_iff_induce_of_degree_ne` (`Motive.lean`), which 10m left with no
    caller (10l had removed its other use); trial deletion confirms (the coordinator's addition).
  - [ ] **10p. `7d`'s chapter, (ii)** (Opus, TeX). CONTRACT-R as CONTRACT-A's corollary, the two
    contraction sections merged; `-core-plane`, `-core-rank`, `-limit`'s clause (1) and a clause of
    `cor:pencil-flat-x0` retire, unpinned. The overview's list of steps where no two open
    conditions meet, and the roadmaps, follow.
  - [ ] **10q. `7d`'s Lean** (Sonnet, not ⚠Z). `Graph.X0Attains.of_rigidContract` from
    `of_additiveContract`, 238 → 22 lines, and the 122 lines 10p unpinned: −338.
  - [ ] **10r. `a2`** (Sonnet, last; axioms harness). `[DecidableEq β]` off `pencil_conjecture`
    and the pinned theorems, by `classical`: the two sites left after 10g–10i. At
    `pencil_conjecture_of_X0` this deletes 10g's `@[nolint unusedArguments]` too (*Decisions*).
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

**10a–10n landed; the rest of the landings run.** The smallest next commit is **10o** (Sonnet, ⚠Z,
mechanical): `q2a` + `b1`, `Theorem55.lean`'s four private cut-edge bricks published under Arms'
names (Arms' copies deleted) and the PanelLayer hub's `ᶜ` (verdicts `q2a`, `b1`), with
`Graph.pencilHub_iff_induce_of_degree_ne` (`Motive.lean`), caller-less since 10m, deleted (task
10's entry). Since 10n, `finrank_span_rigidityRows_cutEdge_eq` has one caller, the glue
`exists_hasPencilPanelRealization_glue`. Then 10p–10r in order, one commit each at its listed
rung; after 10r, task 11 closes the round.

## Decisions made during this round

- **2026-10-04, the open: the granularity.** Seven recon tasks (the mechanical map first, then the
  two blueprint-region questions, then the three deeper ones), the write-up its own commit; the
  landings sliced after Stop 2. Rationale: a task per input over-pays the per-dispatch reading cost.
- **Probes stay in scratch.** No recon task commits a script. Its figures are tagged *measured,
  script not retained* (`HARNESS.md` *Reproducibility*), as rounds 1 and 3 did for liveness. No
  deletion rests on such a figure: a sanctioned retirement is re-verified at landing by trial
  deletion and a whole-project build (`CLEANUP.md` *Liveness*).
- **The landing order is set at task 9, not now.** It depends on what the PI sanctions, and on
  task 1's map: a retired cluster can moot another verdict, as retiring `TwoCut.lean` would moot
  `b2` and half of `b1`.
- **2026-10-04, task 1: a pinned cluster goes to the task that reads its node.** Task 2 takes those
  the reduction layer `\uses`; task 3 takes the rest outside the ears.
- **2026-10-04, task 4: the verdicts move to their own file** (the coordinator's decision), to stay
  under the ~500-line tripwire: `notes/Phase40-simplify-verdicts.md`, as round 3 moved its exemplar.

- **2026-10-04, Stop 2: the PI's sanction** (verbatim): "Let's approve your recommendations above
  except 5. For 5, I think we should restate if it simplifies the exposition." Then: "OK, ii looks
  good and let's update the adjudications." The default stands with `7d` (ii), at the corrected
  rungs; archived in `notes/pencil/adjudications.md`.
- **`7d` (ii): restating simplifies** (the reading the PI accepted). KT's Lemma 6.3 is one lemma,
  for any proper rigid subgraph; its proof takes realizations of the rigid piece (KT Lemma 3.5) and
  of the contracted graph (KT (6.1)) independently and joins them by the block bound (pp. 673–675):
  CONTRACT-A's shape. The chapter runs the curve-and-kernel argument twice, A's section as R's
  variant. As A's corollary R needs `cor:pencil-flat-x0` at `H`, `def₃ ≤ def₂ = 0` and `def₂`'s
  conservation. Stop 2's "(i) keeps KT's order" undersold (ii).

- **2026-10-04, 10e: `span_supportExtensor_eq_top_of_linearIndependent` stays pinned, now with
  no caller** (the coordinator's call), on task 1's (b) precedent that a caller-less clause pin
  stays; the `k ≥ 5` proof still cites the clause it pins.

- **2026-10-04, 10g: two `@[nolint unusedArguments]`, deferred by sequencing.** Once
  `_of_arms_pair` dropped `[DecidableEq β]`, the binder became unused in the proofs of
  `pencil_conjecture_of_X0` and `_hcontract_hK_hbareSplit`, each marked with a comment naming the
  item that deletes it: 10r at `_of_X0`; the other left with `Escape.lean` in 10i's deletion.

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
