# Phase 40 cleanup round 4/5 — `40-simplify`, the deep simplification recon (work log)

**Status:** ✓ closed 2026-10-04 (opened 2026-10-04). Round 4 of the five post-Phase-40 cleanup
rounds. Their order, stops and the PI's decisions are in `notes/Cleanup40.md`, and
`.claude/autopilot/queue.toml` is the authority for which rounds are done. A read-only Opus recon
over the pencil surface (`notes/Cleanup40.md` §2 *Round 4*) wrote 63 verdicts in seven tasks
(`notes/Phase40-simplify-verdicts.md`). At Stop 2 the PI sanctioned the recommended package with
`7d`'s chapter restated (*Autopilot: for the PI*). Its 18 landings, 10a–10r, are all in: −8 930
net Lean lines under `CombinatorialRigidity/`, all 19 main results' axioms unchanged. **Next
concrete task:** none in this round; what comes next is in `notes/Cleanup40.md`'s **Status**.
Round manual: `CLEANUP.md`.

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

**Round 4 is closed** (task 11, docs only). All eleven tasks landed, task 10 as 18 landings, and
each has one line under *Lemma checklist* naming its commit. Nothing is mid-stream. What carried
over: task 3's `c8a`, already in ROADMAP's **PROSE** bullet (*Moved to a later round*), and the
report for the PI under *Hand-off*. `notes/Phase40-design.md` §7's index of carried items now marks
each one paid, with its round and commit, or left at this close.

**Verified at the close** (task 11; the Lean tree is `654bae8a`'s, the blueprint `993b9e74`'s):
- Whole-project `lake build` green, 2996 jobs: 0 `warning:`, 0 `error:` and 0 `failed to cache
  artifact` lines. `lake lint` green.
- `#print axioms` on all 19 `formalization.yaml` main results gives `[propext, Classical.choice,
  Quot.sound]`. The harness `scratch/40-simplify/Axioms.lean` (gitignored) was run with `lake lean`
  after its 19 names (in order) and 14 imports were diffed against `formalization.yaml`'s
  `declaration:` and `file:` fields: identical.
- The blueprint: `lint.sh` and `verify.sh` green (`checkdecls` silent, 9 `WARNING:` lines, all
  plasTeX notices), 0 `LaTeX Warning` lines. Round 3's invariance check
  (`notes/Phase40-exposition.md` *Scope*) now reads 1 029 pins, hash `8225e0a2bc15ccdb`, and 657
  nodes and 1 292 edges, fingerprint `7c7ef987ce81e090` (the open's: 1 062 pins, 668 nodes, 1 308
  edges). Overfull boxes went from 181 to 176.
- The surface shrank. `Pencil/` went from 42 files and 33 691 lines to 37 and 26 897; `pencil.tex`
  from 1 589 lines to 1 186, `main-component.tex` from 5 696 to 5 517. `git diff --shortstat
  4039ba02 654bae8a -- CombinatorialRigidity/`: +1 498, −10 428, so **−8 930 net Lean lines**; with
  the library root's six import lines, −8 936, the landings' sum below (Stop 2 estimated −7 770).

**Verified at the open** (`4039ba02`; the Lean tree `0b260626`'s, the blueprint `30e79461`'s): the
same build (3003 jobs, 0 `warning:` lines) and the same 19 axioms, through round 3's harness copied
to `scratch/40-simplify/Axioms.lean`, its output round 3's close's byte for byte.

## Scope and standing rules

From `notes/Cleanup40.md` §1–§2. How each task applied them is in its commit.

- **A read-only recon, then the sanctioned landings.** Tasks 1–9 were docs commits; probes and
  spikes went in `scratch/40-simplify/<task>/` (gitignored), run with `lake lean`. Route questions
  got compiler-checked spikes (`notes/coordinate-phase-rescue.md` §6), recording the residual
  goals. No statement moved without the PI's sanction at Stop 2 (`notes/Cleanup40.md` §2).
- **Evidence.** A claim about a declaration came from its statement and body, never its docstring.
  Liveness is the Lean call chain (`CLEANUP.md` *Liveness*): task 1's closure, then trial deletion
  with a whole-project build at landing. Prior evidence (rounds 1–3) stood unless a task brought a
  new argument.
- **A verdict** is one entry in its task's subsection of the verdicts file, at most five lines:
  `**<id>, <name>: GO**` (or NO-GO); one sentence of why; the commit estimate (commits, rung, ⚠Z
  for the fragility zone); what it changes (a headline signature, a blueprint statement's strength,
  the dependency graph, or nothing a reader sees); any verdict it depends on; its evidence (read,
  measured, or a spike's residual). The detail goes in the task's commit message.
- **Rungs.** The recon tasks were Opus. A landing's rung was its verdict's, as Stop 2 corrected
  it: Opus for a ⚠Z proof rewrite (`.claude/commands/coordinate-phase.md` *Fragility zone*).
- **This log** is not matched by `notes/check-phase-note.py`'s name pattern, so its `parse` and
  `offenders` run on it directly.

## Input IDs

`notes/Cleanup40.md` §2 *Round 4* lists the round's inputs, one line each, and the verdicts name
them by their position there. Each input had one owner task, which wrote its verdict.

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

One commit per task, in this order; each line names its commit, which carries the detail. A
landing's lines are its net Lean lines (`git diff --numstat` over `CombinatorialRigidity/` and the
library root).

- [x] **1. L — the liveness map** (`6108f1ca`; `q3`, `b2`, `r1`'s deletion question).
- [x] **2. R — `pencil.tex`'s reduction layer** (`bd1e1282`).
- [x] **3. N — node shapes outside the reduction layer** (`22227e7b`).
- [x] **4. E — the open ears** (`0cc633ef`, the verdicts moved to their own file; fixup `5e91fbd3`).
- [x] **5. A — where `Pencil/` re-proves** (`075d34db`).
- [x] **6. P — Phase 39's producers** (`e2d364e2`).
- [x] **7. G — the remaining long proofs** (`40b36fda`).
- [x] **8. W — Stop 2, the write-up** (`aae919cf`; `NEEDS_PI`).
- [x] **9. S — slice the sanctioned items** (`6e24eeaa`; the PI's answer, `c8a` to **PROSE**).
- [x] **10. B — the sanctioned items land**, green at every commit (`lake build` warning-clean,
  `lake lint`, the blueprint gates on TeX, *Forward-mode slices*, the axioms harness at a headline).
  - [x] **10a.** Task 3's TeX batch (`f53dace5`, Sonnet): `m6`, `m7`, `1c-i`, `c1`, `c5`, `c8`,
    `c9`, the polynomial's pins and the two-hubs edge. Its unpins split into the dead, deleted in
    10b, and live helpers left unpinned (`eb333e0c`).
  - [x] **10b.** `r1`'s deletion (`c48d323e`, Sonnet, ⚠Z files): `TwoCut.lean`, `q3b` and 10a's
    dead names, 38 declarations; −1 340.
  - [x] **10c.** `c6` + `c7` (`cab5da0d`, Sonnet): the iff pinned at `lem:pencil-condition-linear`;
    `Graph.IsMainPicture.exists_mvPolynomial`, the open pin its corollary; +23.
  - [x] **10d.** `q2b` + `q2c` + `a3` (`eff50a5d`, Sonnet): one perp-dimension lemma, the mirror's
    common non-root, the finsum degree sum; −64.
  - [x] **10e.** `q1a` (`84848e5b`, Sonnet): `Graph.X0Attains.of_openEar_of_cert`; −38.
  - [x] **10f.** `r7`'s node (`f93e54b1`, Sonnet, TeX): `lem:minimal-kdof-spanning-subgraph`; 0.
  - [x] **10g.** `c3`'s Lean (`f8c6b0d4`, Opus): `pencil_conjecture_of_arms_pair` over every
    nonempty graph, with `pencilPair_loop_base_cut`; −31.
  - [x] **10h.** `c3`'s TeX (`528381ef`, Opus): the pair theorem split,
    `lem:pencil-pair-loop-base-cut`, the kernel statement gone, with `c2`, `c4`(b), `m2`, `m4`,
    `m5` and `1b`; −2 (docstrings).
  - [x] **10i.** `1a`'s deletion (`1e7d78a9`, Sonnet, ⚠Z files): `_of_card`'s cluster with `q3a`,
    `1b` and `1c-ii`, and the girth chain with its eight nodes; −4 286.
  - [x] **10j.** `m3` + `7c` (`8f297c7d`, Opus, ⚠Z): `pencilPair_of_simple_ncard_eq_three`;
    `Base.lean` and two nodes gone; −226.
  - [x] **10k.** `a6` + `a6a` (`8b4a9120`, Opus, ⚠Z): one assembly for each cut case's two
    branches; −261.
  - [x] **10l.** `a5` (`bce29f77`, Opus, ⚠Z): one tail for `Pair2.lean`'s #4 and #6; −339.
  - [x] **10m.** `7a` (`8bf05cd7`, Opus, ⚠Z): the pendant cut by `lem:pencil-generic-steer` at
    every degree; −1 593.
  - [x] **10n.** `7b` (`472eeded`, Opus, ⚠Z): one glue for a cut's two sides, four sites; −298.
  - [x] **10o.** `q2a` + `b1` (`919486d3`, Sonnet, ⚠Z): Theorem55's cut-edge bricks under Arms'
    names, the hub's `ᶜ`, and the caller-less `Graph.pencilHub_iff_induce_of_degree_ne`; −116.
  - [x] **10p.** `7d`'s chapter, (ii) (`993b9e74`, Opus, TeX): one section,
    `sec:main-component-contract`, CONTRACT-R its corollary `cor:pencil-x0-contract-rigid`, four
    pins retired; 0 (docstrings).
  - [x] **10q.** `7d`'s Lean (`91755996`, Sonnet): `Graph.X0Attains.of_rigidContract` an 18-line
    corollary of `of_additiveContract`, 10p's four unpinned names deleted; −354.
  - [x] **10r.** `a2` (`654bae8a`, Sonnet): `[DecidableEq β]` off `pencil_conjecture` and
    `pencil_conjecture_of_X0`; −11 (its message's −13 counts the deletions).
- [x] **11. X — close the round** (this commit; what it verified and carried over is under
  *Current state* and *Hand-off*).

## Verdicts (Stop 2's inputs)

In their own file, `notes/Phase40-simplify-verdicts.md` (moved at task 4; *Decisions*): one
subsection per recon task, `### Task N (X)`, one entry per input it owns, in the format under
*Scope*.

## Moved to a later round

Each line gives the task, its target (round 5, `40-docs`, or **PROSE** in ROADMAP's queue) and a
one-line reason. The same line went into the target's plan in the same commit; the close checked
that ROADMAP's **PROSE** bullet carries it.

- **Task 3's `c8a` → PROSE** (sanctioned at Stop 2). Seven nodes here with four or more pins
  (`def:pencil-nondegenerate`, `lem:pencil-x0-one-witness`, `thm:pencil-x0-main-component`,
  `lem:pencil-jj-rescale`, `lem:pencil-jj-embed-edges`, `thm:pencil-jj-equality`,
  `lem:pencil-chain-span-certificates`), mostly one pin per clause: for PROSE's audit of bundled
  nodes (principle D), not this round's.

## Blockers / open questions

- None.

## Hand-off / next phase

**Round 4 is closed; there is no next step in it.** The next round was round 5, `40-docs` (project
organization), which opened 2026-10-04 and closed 2026-10-05 (work log `notes/Phase40-docs.md`);
`notes/Cleanup40.md`'s **Status** says what follows. What carried over: task 3's `c8a`, in
ROADMAP's **PROSE** bullet. No task of this round is left open.

**For the PI** (a report, not a stop):
- **Two pinned items are kept with no caller** (*Decisions*). `cor:pencil-flat-x0`'s pin
  `Graph.x0Attains_of_finrank_liftingSpace_eq_three` has no Lean caller, and since 10p the node has
  no in-edge. `span_supportExtensor_eq_top_of_linearIndependent` (`lem:pencil-ear-hinge-span`)
  lost its only Lean caller at 10e. Retiring either would go past the retirements Stop 2 named.
- **`notes/Phase40-design.md` §7's items left at this close**, each by round 3's recorded call,
  sanctioned at Stop 2: A6 and item 6's other laws, whose build-when-consumed conditions never
  fired (`r2`); the edge-restricted, non-spanning generic-normals row rank (§3 BRIDGE, `r4`); and
  the "only if" halves of (MC-52)/(MC-53) (`r3`). Every other item there is paid.
- **One headline signature changed:** `pencil_conjecture` no longer takes `[DecidableEq β]` (10r,
  `a2`, sanctioned at Stop 2), so it is strictly more general, as is `pencil_conjecture_of_X0`.
  Its axioms are unchanged.

For round 5: `.claude/autopilot/system-prompt.md` still sends a cleanup round's statement-changing
finding to "a candidate for `40-simplify`", which is now closed. (Round 5 left the file as it is
and reported the line to the PI: `notes/Phase40-docs.md` task 16.)

## Decisions made during this round

- **The granularity** (the open): seven recon tasks, the write-up its own commit, the landings
  sliced after Stop 2; a task per input over-pays the per-dispatch reading cost.
- **Probes stay in scratch**, tagged *measured, script not retained* (`HARNESS.md`
  *Reproducibility*); every sanctioned retirement was re-verified at landing by trial deletion and
  a whole-project build (`CLEANUP.md` *Liveness*).
- **A pinned cluster went to the task that reads its node** (task 1). **The verdicts moved to
  their own file** at task 4 (the coordinator's decision), to stay under the ~500-line tripwire.
- **The landing order** was set at task 9 from the sanction and task 1's map: a retired cluster
  moots another verdict, as retiring `TwoCut.lean` mooted `b2` and half of `b1`.
- **Stop 2, the PI's sanction** (2026-10-04, verbatim under *Autopilot*): the default with `7d`
  (ii), at the corrected rungs; archived in `notes/pencil/adjudications.md`.
- **`7d` (ii): restating simplifies** (the reading the PI accepted). KT's Lemma 6.3 takes
  realizations of the rigid piece (KT Lemma 3.5) and of the contracted graph (KT (6.1))
  independently and joins them by the block bound (pp. 673–675) — CONTRACT-A's shape, which the
  old chapter ran twice. As A's corollary, R needs `cor:pencil-jj-flat` at `H`
  (`Graph.x0Attains_of_deficiency_two_eq_three`, as 10p and 10q landed it; the reading said
  `cor:pencil-flat-x0`), `def₃ ≤ def₂ = 0` and `def₂`'s conservation.
- **Two pins kept with no caller** (the coordinator's calls, on task 1's (b) precedent):
  `span_supportExtensor_eq_top_of_linearIndependent` (10e; the `k ≥ 5` proof still cites the
  clause it pins) and `cor:pencil-flat-x0`'s `Graph.x0Attains_of_finrank_liftingSpace_eq_three`
  (10p; CONTRACT-R reads `cor:pencil-jj-flat`). The close lists both for the PI.
- **10g's two `@[nolint unusedArguments]`** went by sequencing: `Escape.lean`'s with 10i,
  `pencil_conjecture_of_X0`'s with 10r.

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
