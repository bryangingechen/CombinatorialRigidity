# Dispatch log — exceptions only

Coordinator-owned record for `/coordinate-phase` sessions. **Routine
clean dispatches are NOT logged** — git history is the record. Log a
row only for an **exception**:

- an **escalation** (BLOCKED return or failed verification →
  re-dispatched one rung up) — log both halves' cost;
- a deliberate **probe** below the mapped rung, and its outcome;
- a **BLOCKED / killed / salvaged** dispatch (what stranded, what was
  recovered, resume-vs-relaunch);
- a **gate-invisible defect caught in verification** (shape
  deviation, additive-repin miss, deletion-hygiene miss, faithfulness
  defect, unsatisfiable deferred hypothesis) — the catch *and* which
  check caught it;
- a **playbook deviation** (rung substitution beyond the session
  config, an off-map rung choice) and its outcome.

Provenance: this replaces the per-dispatch model-tier experiment log
(concluded 2026-07-09 across CombinatorialRigidity + enharmonic, ~890
rows; the frozen log is `notes/model-experiment-archive.md`, findings
promoted into the coordinator command's *Dispatch playbook*). The
experiment's own history showed per-dispatch logging re-bloats — rows
recapping math the commit message already carries — so the schema below
keeps only what git cannot show.

## Row discipline

- **Notes ≤ ~600 chars** — the exception's cause and lesson, never a
  recap of the mathematics (the commit message is the recap). If a
  sentence restates what the *commit* did rather than how the
  *dispatch* went wrong, cut it. This is the same ~600-char cap the
  concluded experiment enforced, and `notes/check-log-rows.py` gates it
  on this log (the rows changed vs HEAD by default; `--all` audits the
  whole table). Gate on its exit code with an `if`-guard, never a pipe
  or `;`-chain.
- **Append by matching the previous row's tail only** — an edit span
  that includes the following section header silently deletes that
  header (this clobbered a log's Findings heading three times in one
  ancestor session).
- An A/B or rung row names the model id each arm resolved to, read from the
  subagent transcript, not the variant's alias (the 40b CARRIER "opus" arm
  ran on Opus 4.8 — `notes/harness/incidents.md` 2026-09-26).
- Write the row only after the verification pass completes in full;
  correct a committed row by a follow-up edit, not a
  history-rewriting amend.

## Log

| Date | Task (short + sha) | Rung | Exception | Notes |
|---|---|---|---|---|
| 2026-10-24 | 41b item 3 `b2d0839a` | sonnet | coordinator artifact refuted (F19) | My scope-pin predicted that `rankHypothesis_genuine_of_theorem_55_gen`, the rows form and `theorem_55_6_multigraph_of_two_le` would lose `hD` to `unusedArguments`; they already derived `3 ≤ D` locally (round 3's `F-298`), so none changed. The builder checked instead of obeying. The prediction was read off the call sites' `hD` argument without opening the callers' binders. Also: the ledger dispositions said "item 3's commit", not a sha; item 4a filled it in. |
| 2026-10-25 | 41b item 4c `4960364d` | sonnet | phase-note gate red at landing | The return attested the module builds, `checkdecls` and `blueprint/lint.sh`, but neither `lake lint` nor `check-phase-note.py`; the note failed forward-weighting (finished 70 ≥ forward 68), as items 2–4c each kept its full spec beside a "Done:" paragraph. The coordinator re-ran the whole build and `lake lint` (green) and compressed the done items to one-line verdicts in a fixup, with the design doc's and `Reconcile.md`'s stale next-task pointers. |
| 2026-10-25 | 41b item 7 `6d261725` | sonnet | gate-invisible defects caught in verification | Two Lean docstrings cited "the coordinator's adjudication": process text, and one misattributed the PI's §1.4 to the coordinator. The return also said dispositions live in commit messages and skipped the ledger (`notes/Reconcile.md` §2). Caught by the full-diff read and a grep; fixed as neighbouring edits at item 8. From item 8 on, prompts say Lean docstrings describe mathematics, never process. |
| 2026-10-25 | 41b item 8 `8c2d4475` | sonnet | design pin refuted before dispatch | The checklist's "`_hSimple` dropped" (the open's recon, design doc §2) would have made the restated corollary false: deriving it from `theorem_55_d3` needs simplicity, and the double edge on two bodies is a minimal 0-dof-graph at d = 3 whose meet-model hinges coincide. Caught by the pre-dispatch derivation guard against the recon's own banana witness; the prompt pinned a used `hSimple`. |
| 2026-10-25 | 41b item 9 recon `418803bc` | opus | coordinator artifact refuted (F19) | My prompt listed `HingeGeneric`, three pencil files and `BodyBar/GenericLift` as consumers of `PanelGeneric`'s declarations, from a `grep -w`; every hit was a docstring (only the root module imports the file). The recon checked Lean uses apart from mentions and refuted the list. Lesson: a consumer list from grep separates code uses from docstring mentions; item 10's prompt asked for that. |
| 2026-10-25 | 41b item 11 `c26edc57` | opus | faithfulness defect caught by the PI's question | `prop:rigidity-matrix-prop11` stated KT Prop. 2.3 for panel-hinge realizations of multigraphs, false in the meet model at the double edge; KT (p. 655) state it for body-hinge frameworks, credited to Jackson–Jordán (`F-331`). The PI's "Is this node one from KT?" sent the coordinator to the PDF; PROSE's S18 and the open's recon had read only the pin's conditionality. Lesson: an S finding on a pin also checks the node's statement against the source. |
| 2026-10-28 | 41c item 1 `e348a3e8` | sonnet | gate-invisible defect caught in verification | The new ledger entry `F-332` justified "false without `hC`" with the direction reversed: a zero hinge "removes the D − 1 equations", where `isInfinitesimalMotion_iff`'s span of a zero extensor forces `S u = S v`, D equations. Caught by the tier's read of new prose against the definitions; the coordinator first mis-derived it too, from `annihRow`'s zero rows, before opening `infinitesimalMotions`. Fixed in a coordinator commit. Lesson: a counting claim about a degenerate case is checked against the carrier's definition body. |
| 2026-10-28 | 41c item 2 `aeac5f6e` | sonnet | gate-invisible defect caught in verification | Widening the body-hinge theorem to multigraphs, the builder deleted "simple" from README's and the home page's joint 41b sentence about the body-hinge theorem *and* its panel-hinge companion, so both now "held for every graph" since 41b, false for the companion and for 41b; the yaml note said 41b and 41c both made them hold for every multigraph. Caught by the tier's read of new prose; fixed in a coordinator commit. Lesson: a sentence naming two results is narrowed per result, never by deleting a shared qualifier. |
| 2026-10-29 | 41d item B1 `c6bc7762` | sonnet | gate-invisible defect caught in verification | The new node `lem:embed-edges-minimal` `\uses` a remark, not a node, and missed three proof edges; `verify.sh` was green, `blueprint-deps.py --label` caught them. B1 also left `Simple.embedEdges` and `deficiency_embedEdges` pinned on the pencil chapter's `lem:pencil-jj-embed-edges`, though the witness's Theorem 5.5/5.6 transports call both: after B2, KT 5.5's closure would have reached the pencil chapter. Fixed by an opus corrective (this commit) moving the two pins to a panel-layer node. Lesson: a move-up item moves its blueprint pins with its Lean, and new nodes get the deps audit. |

**Phases 29–34 rows, 2026-07-09 → 07-18: 17 pruned at the 41a grooming
(2026-10-24); the full rows are in git history at `3a627b3d`.** Those phases
closed without a grooming, and three of the rows were past the 600-char cap
(`check-log-rows.py --all`). Profile (a row can match several classes): 6
F6-family gate-mechanics rows (a builder parked on its own backgrounded or
Monitor-watched build, twice with three whole-project builds running, once
with an F5 rung drift on the resume); 4 kills (three org spend limits, one
stream idle timeout), each recovered by a same-agent resume (rescue §3, F4); 2
pre-build recons that refuted a statement or a route claim before any Lean
consumed it; 2 gate-invisible defects caught in verification (a restate
confined to the slice's named chapter, a false inference in sketch prose); a
recon's anchor undercount (F1), one scope-to-fit across three slices, and a
nested spawn the hook denied. Each lesson is in a manual: F1, F4–F6, the
playbook's per-section pre-build recon, `CombinatorialRigidity/CLAUDE.md`'s
restate grep over all of `blueprint/src/`, `block-nested-agent.sh`.

**Phase 39 (PENCIL) rows, 2026-07-24 → 09-17: 150 pruned at the phase close
(2026-09-25); the full rows are in git history at `e316891f`.** Profile, by
the exception column's own wording (a row can match several classes): 26 gate-
invisible defects caught in coordinator verification (aggregator orphans ×2,
an unsatisfiable carried hypothesis, a citation overclaim; twelve rows naming
a stale status surface — F17); 60 rows naming a coordinator-authored defect or
premise (F14, F19, F22, F38); 16 refuted predictions, pins or landed clauses
(F9, F10 and the research-arc F26–F38); 11 kills or resumes (spend limits, the
64k output cap, an API timeout — every one recovered by a same-agent resume,
rescue §3); 9 F6-family gate-mechanics instances (auto-background, Monitor
park, shell `timeout`/`| tail`, concurrent builds); 6 rung / trailer /
substitution drifts (F5); 6 playbook deviations (three user-adjudicated
parallel fan-outs, two rung substitutions — one user-adjudicated, one forced
by availability — and one declined resume). Every recurring class has a
Finding below; the one-off shapes (a subjectless commit message, a `git stash
-u` under live sibling drafts, a keepalive cron left armed) live only in the
pruned rows.

**Phase 40 (PENCIL-X0) and cleanup rounds 1–5 rows, 2026-09-25 → 10-04: 48
pruned at `40-docs` task 15 (2026-10-05); the full rows are in git history at
`e5b8eaee`.** Profile, by the exception column's own wording (a row can match
several classes, and the counts are approximate): 26 gate-invisible defects
caught in verification, nine of them in prose written around verified Lean
(F44), five stale claims about the tree's state (F45), two missing proof-level
`\leanok`s (F48), two names surviving a deletion or a moved pin (the
playbook's `hygiene` block) and eight one-offs (a restate check that read only
a statement, a dropped scope-pin deliverable, a spike's `#print axioms` lines,
a `lake env lean` count, `TACTICS-QUIRKS` §55); 12 coordinator-authored spec
or plan defects, each caught by the dispatch or a pre-dispatch read (F19); 16
playbook deviations: three user-requested opus ∥ fable A/Bs (the evidence for
Fable leaving the map, 2026-09-26), seven arcs on F43's fresh-builder
alternative (F46), three "follow precedent" settlements (F47), two sub-phase
splits or folds put to the PI, and one Opus-for-prose rung change; 4
escalations; 4 kills or auto-backgrounds, all recovered (rescue §3, F6); 3
tool defects or gaps (the MCP's `lean_local_search`, `phasenote.py`'s
`NEXT_RE`, F48's two missing gates). Every recurring class has a Finding below
or a rule already in a manual.

**`40-docs`, PROSE rounds 1–5, RECONCILE rounds 1–3 and Phase 41a rows,
2026-10-05 → 10-24: 20 pruned at the 41a grooming (2026-10-24); the
full rows are in git history at `3a627b3d`.** The multi-commit trial's two arc
rows followed when the PI dropped the trial (F53). Profile, by the exception
column's own wording (a row can match several classes, and the counts are
approximate): 7 hygiene-rule readings the coordinator accepted (F51); 9
gate-invisible defects caught in verification, by a later dispatch or at a
close: two compressions that paraphrased the PI's words (F50), two close
summaries that contradicted the round's own record and item 5b's docstrings
(F44), a deleted name surviving in brace and suffix forms (F52), a notation
clash, an anchor check that read only the grep hit line, and a `\uses` edge
kept after it lost its Lean backing; 3 coordinator artifacts, refuted by the
dispatch they primed or by the coordinator's own read (F19; the third was F50
again: a compression prompt that did not carry the rule); 1 kill resumed
(rescue §3); 1 gate-mechanics row under memory pressure (F49); 1 stale trailer
pin (`phase-builder-sonnet.md`, fixed at `022dd016`).



## Findings

(Distill recurring lessons here — one entry per lesson, rows cite it.
At phase close, promote stable entries into the coordinator command's
*Dispatch playbook* / CLAUDE.md and prune.)

**Phase-39 close grooming (2026-09-25).** The phase's 150 rows are pruned to
git history (profile under *Log*). Findings whose rule now lives in a manual
are stubbed below with the pointer, the F2–F4 shape: F5–F15, F17–F21, F26–F28,
F30, F39, F41, F42 — seven of them (F8, F9, F12, F14, F19, F41, F42) promoted
into the `/coordinate-phase` *Dispatch playbook* at this close. Kept in full:
F1 (a conditional promotion), F40 (an open tooling item, `check-roadmap-
cells.py`), and the research-arc findings F16, F22–F25, F29, F31–F38, whose
promotion target is `HARNESS.md`, which changes only in `/harness-review`
(due).

**Phase-40 grooming (2026-10-05, `40-docs` task 15).** The phase's and its
cleanup rounds' 48 rows are pruned to git history (profile under *Log*). New
findings: F44–F48. Promoted now: F44 and F45 into the playbook (*Verification
tiers*, the docs-only P calibration, the `hygiene` block), F45 also into
`CLEANUP.md` §D, F46 into step 3 *Resume and land*, and F1 into
`notes/CLAUDE.md`. Kept open: F47 (it would change when the PI is asked) and
F48 (two missing gates), both in `notes/Phase40-docs.md`'s close report to the
PI, and F40.

**41a grooming (2026-10-24, after the 41a close).** 37 rows are pruned to git
history (profiles under *Log*): the 17 of Phases 29–34, which closed
ungroomed, and RECONCILE's and 41a's 20. The trial's two arc rows followed
when the PI dropped it (F53). New findings: F50–F52. Promoted now: F50 into
`notes/CLAUDE.md` *Phase notes* and the playbook's shaping paragraph, F51
into the shaping paragraph, F52 into the `hygiene` block and
`CombinatorialRigidity/CLAUDE.md`'s deletion gate, and F44's close-summary
recurrence into *Verification tiers*.

- **F1 — re-derive inventories at build time.** Promoted to
  `notes/CLAUDE.md` *One canonical home* (count again in the compressing
  commit) at `40-docs` task 15, 2026-10-05: the third `*-design.md`
  compression (`40-docs` tasks 8–9) re-derived its anchor inventory per commit
  as mandated, found the open's figures close and repointed nothing. Pruned
  (the Phase-29 undercount is in git history).
- **F2 — pinned exemplar = the prose S=1.** Promoted to the playbook
  (*Raising S* + the shaping-block list) 2026-07-09; pruned at the
  Phase-34 close (details in git history).
- **F3 — verification-mandate cost signature.** Promoted to the
  playbook (the cost-outlier bullet's benign-shape carve-out)
  2026-07-09; pruned at the Phase-34 close (details in git history).
- **F4 — continuation dispatch (same-arc resume).** Promoted to the
  playbook (step-3 *Continuation dispatch* note) 2026-07-10; pruned at
  the Phase-34 close (details in git history).
- **F5 — SendMessage-resume runs at the session model, not the dispatched
  rung.** Promoted: the command's *Pick the rung* (typed variants; resumes
  rung-stable) and steps 2/5, `notes/coordinate-phase-rescue.md` §3,
  `HARNESS.md` *Reproducibility*. Pruned at the Phase-39 close (the
  controlled-probe matrix is in git history at `e316891f`).
- **F6 — harness auto-backgrounding strands gate runs.** Promoted: both agent
  cores (foreground gates with the Bash `timeout` parameter; no
  `run_in_background`/Monitor; no shell `timeout` or pipe), rescue §2, the
  command's step-3 reminder line, `HARNESS.md` *Reproducibility*. Pruned at
  the Phase-39 close (instances in git history).
- **F7 — the internals tactic-golf phase runs clean at low rungs (Phase 36
  AUTOMATE).** Promoted: the tactic lessons to `TACTICS-GOLF.md` §7; the
  AUTOMATE-Z template ran as Phase 37. Pruned at the Phase-39 close.
- **F8 — a chart/WF-style predicate's conjuncts are unverified until something
  INSTANTIATES them (Phase 39 W5).** Promoted to the command's step-4
  satisfiability bullet (a new conditioning / well-formedness predicate is
  unverified until something instantiates it at the common graph shapes) at
  the Phase-39 close; pruned (details in git history).
- **F9 — a design pass's per-arm obligation verdicts ("free", "vacuous",
  "mirrors landed X") are unverified until a builder confronts them; prompt
  the confrontation explicitly (Phase 39 W5).** Promoted to the playbook
  (*Rate the task*: an arm re-derivation against a conditioned motive is P ≥
  2; the derivation guard's re-derive-and-return-the-refutation line) at the
  Phase-39 close; pruned.
- **F10 — diff a design PIN against the phase's OWN recorded Blockers at
  pin/dispatch time (Phase 39 W5-L6 habitat arc).** Promoted to the command's
  step-2 derivation guard (its third face: a design PIN vs the phase's
  recorded *Blockers*). Pruned at the Phase-39 close.
- **F11 — in an informal-research arc, the corrective mechanism is the NEXT
  pass, not coordinator scrutiny (Phase 39 kernel-(K) arc).** Promoted to
  `RESEARCH-ARC.md` §4 (*A driver per headline sentence*). Pruned at the
  Phase-39 close (the incident record is in git history).
- **F12 — when a return flags a stale claim in a named cell, grep the whole
  file: the same claim usually also sits in the body prose that the cell
  summarizes (Phase 39 fan-out landing).** Promoted to `RESEARCH-ARC.md` §6
  and, at the Phase-39 close, to the playbook's `hygiene` shaping block (every
  file kind, Lean docstrings included; a summary's correction is presumptively
  a body paragraph's too). Pruned.
- **F13 — a guard is not verified by existing; a sampler defect that *implies*
  the measured quantity is invisible to every downstream check (Phase 39,
  2026-08-06).** Promoted to `HARNESS.md` *Evidence* (blind axes; a guard
  needs its own adversarial test). Pruned at the Phase-39 close.
- **F14 — coordinator premises are as unverified as a subagent's, and the
  cheap check is measurement (Phase 39, 2026-08-06).** Promoted to the
  playbook's shaping-block paragraph (mark a coordinator hypothesis as a
  hypothesis; a truncated search is *at least N*, not an enumeration) at the
  Phase-39 close; pruned.
- **F15 — the 600 s foreground ceiling has no carve-out in the foreground-
  gates mandate, and a subagent's background job dies with its turn (Phase 39,
  2026-08-06).** Promoted to `HARNESS.md` *Reproducibility* and
  `notes/scripts/README.md` (start the over-ceiling invocation first; collect
  it before the turn ends). Pruned at the Phase-39 close.
- **F16 — a present check is not a guard: test whether it CAN fire (Phase
  39, 2026-08-06).** Auditing the `meet_line` call sites, a neighbouring
  `rank([hat(M0), hat(M0+Md), hat(pt b)]) == 2` assert was read as the guard
  covering an unguarded call — but at `Md = 0`, precisely the input in
  question, its second entry equals its first, so it passes **vacuously** and
  can never fire there. This is F13 one level down: F13 is a guard that fires
  on the wrong condition; this is a check that cannot fire at all on the
  input it appears to cover, and it was mistaken for a guard **inside the
  commit repairing the first instance**. The mechanical version of the check:
  substitute the degenerate value into the assert by hand and ask whether
  anything is still constrained. Corollary, and the reason this one was
  caught: a coordinator's site list is a starting point the builder
  re-derives, not a checklist it executes.
- **F17 — a document's own header is a status surface, and it is exactly what
  a section-scoped edit does not re-read (Phase 39, 2026-08-13…15).** Promoted
  to `CLAUDE.md` *Before each commit* (the note's `**Status:**` header is a
  surface), `notes/phasenote.py --surfaces`, `notes/check-phase-note.py` and
  `HARNESS.md`. Pruned at the Phase-39 close.

- **F18 — a parallel fan-out surfaces findings no single agent can see (Phase
  39, 2026-08-19).** Promoted to `RESEARCH-ARC.md` *Candidates* (budget a
  cross-return pass; choose directions in different sections). Pruned at the
  Phase-39 close.

- **F19 — coordinator-authored artifacts need the same verification tier as
  subagent returns (Phase 39, 2026-08-19).** Promoted to `RESEARCH-ARC.md`
  and, at the Phase-39 close, to the playbook's *Verification tiers* (the
  coordinator's own artifacts get the same tier; a coordinator commit runs the
  F17 sweep). Pruned.

- **F20 — label reservations prevent collisions, not duplication; two checks
  are missing (Phase 39, 2026-08-19).** Promoted to `RESEARCH-ARC.md`
  *Candidates* (the two missing duplication checks: against landed Lean,
  across concurrent siblings). Pruned at the Phase-39 close.

- **F21 — a mechanical cap catches overflow, not purposeless compliance (Phase
  39, 2026-08-19).** Promoted to `RESEARCH-ARC.md` §7 and `notes/check-gapmap-
  cells.py`'s docstring (a cap bounds growth, not purpose; recompute with a
  target; verify labels by a scripted set-diff). Pruned at the Phase-39 close.

- **F22 — a fan-out multiplies the coordinator's spec errors, and
  inherited clauses are the main vector (Phase 39, 2026-08-19).** Four of
  the eighth fan-out's five directions corrected a defective clause in
  their own spec — five clauses in all, and not one of them a
  mathematical mistake by the direction: every one was the coordinator
  asserting more than the source supported. **Three were inherited** —
  transcribed verbatim from a *landed* hand-off (AGLU's "is it
  fully-good?", BALB's "min-cost flow, hence polynomial", ZNEQ's
  "equivalently the Schubert non-jump") and therefore already
  twice-read, which is precisely why they survived a re-read. **Two were
  written at prep.** The lesson is not "read the hand-off harder": a
  landed hand-off clause carries the authority of a landed result and
  gets copied with it. The lesson is that **a hand-off's
  forward-looking clauses are conjectures, not results** — so a spec
  should quote them *as* the previous direction's recommendation rather
  than restate them as fact, letting the reader attack the clause
  instead of inheriting it. Pair this with the seventh fan-out's row
  (three coordinator premises refuted): across two waves **eight**
  coordinator premises have been refuted by the directions they primed,
  and **none** by a gate.

- **F23 — an unescaped pipe silently downgrades the gap-map cap gate,
  so a passing run proves nothing (Phase 39, 2026-08-19).**
  `check-gapmap-cells.py` falls back to capping columns 3+4 *combined*
  when a row's pipe count does not resolve to four columns — a
  deliberate, documented choice (it will not guess a split point). What
  is not documented is the consequence, which bit **twice in two
  landings**: writing `|W|`-style cardinality notation unescaped inside
  the row makes the gate pass on the *combined* cap while the status
  cell alone sits 31, then 121, words over its own. Escaping restored
  `split` parsing and exposed both overruns. **Check the parse mode, not
  just the exit code** — if a row parses as `combined`, its per-cell
  caps are not being enforced at all. Cheap standing fix for a
  successor: have the script *warn* when a row it was asked to check
  parses as `combined`.

- **F24 — a dispatch's criticism of coordinator work needs the same
  verification as its mathematics (Phase 39, 2026-08-19).** OSCHU
  returned a confident, specific, numbered claim that a sibling landing
  had skipped a mandated recompute. Checked against the commit it was
  wrong: the recompute had over-delivered (34 % off the pre-existing
  content), and the figure OSCHU quoted was the cell's *end* state after
  the sibling's own content went in. Two lessons, pointing opposite
  ways. **For the coordinator:** apply the reasoning-scrutiny tier to a
  dispatch's *process* claims too, not only its theorems — taking this
  one at face value would have produced a corrective commit repairing
  nothing. **Against the coordinator:** the misreading was *invited*,
  because one obligation was written two ways in one spec — "recompute …
  before adding its own content" for one section, a bare word-count for
  the other. State a repeated obligation **identically** at every site,
  or the weaker wording becomes the one a careful reader enforces.

- **F25 — the verification-bar sentence is itself a headline claim, and it
  is the one F11 is most likely to miss.** GHWIT (2026-08-26) shipped a
  correct, four-times-checked refutation whose *description of its own
  checking* was wrong: "four independent exact models" plus a pinned
  `max|R|` figure, against a driver implementing three — its own docstring
  saying so. Every gate passed, the mathematics was sound, and the three
  shipped models already met the project's (GR-83)/(GR-113) bar, so nothing
  failed except the sentence claiming more. The mechanism is specific and
  repeatable: a model written as a **scratchpad probe**, run, believed, then
  written up from memory of the *session* rather than a re-read of the
  *deliverable* — which is also how the draft's own "probes promoted"
  paragraph came to assert five promotions where three had happened. The
  agent's diagnosis is the rule: **write that sentence by re-reading the
  driver, never by recalling the session.** Coordinator-side the catch is
  cheap and mechanical — grep the driver for the claimed model count and for
  any figure the prose pins, before accepting a refutation. F11 says every
  headline claim needs a driver testing that sentence; this is the reminder
  that *"we checked it N ways"* is one of them, and on a refutation it is
  the load-bearing one.

- **F26 — a residual can be *correct* and still be the wrong target; check
  what the consumer actually consumes before spending a direction on it.**
  Promoted to `HARNESS.md` *Evidence* (open the consumer before dispatching at
  a residual). Pruned at the Phase-39 close.

- **F27 — one draw is a lower bound, not a measurement, whenever the statistic
  is semicontinuous.** Promoted to `HARNESS.md` *Evidence* (one draw of a
  semicontinuous statistic is a bound; an exhibited certificate is a proof).
  Pruned at the Phase-39 close.

- **F28 — a listed fence is not an acted-on fence.** Promoted to `HARNESS.md`
  *Evidence* (name the listed axis the direction is to OPEN). Pruned at the
  Phase-39 close.
- **F29 — *"where I expect to be wrong"* names the REGION reliably
  and the INSTANCE never.** Across this round's three specs the field
  pointed at the right region 3 of 3 — GOWNHALF's *"the partition,
  not the attribution"* **was** the answer; BWHOLEH's *"a fence, not
  a theorem"* was the right class; GTRIFREE's *"the quantifier is a
  statement about two drivers"* was the right suspect. It named the
  right instance **0 of 3**: BWHOLEH's two named literals both turned
  out inert (un-fencing `xy` changes nothing, all twelve pairs kill),
  and GTRIFREE's predicted *third move family* was never needed. So
  the field's value is **locating where to look**, and its named
  candidates should be written as *"start here, expect to discard"*
  rather than as the expected answer — the same discipline §7 already
  imposes on the MECHANISM field, now earned by a second field.

- **F30 — a PREFIX is not a SAMPLE, and the generator's emission ORDER is a
  population fence.** Promoted to `HARNESS.md` *Evidence* (a prefix is not a
  sample; sweep exhaustively or aim where the mechanism predicts, and say
  which). Pruned at the Phase-39 close.
- **F31 — a TELL must sample a quantity whose SEMICONTINUITY runs the
  way the verdict needs.** The tell check had three parts — not
  already satisfied, satisfiable at all, could the verdict differ
  inside the region. This round shows a fourth, and it decided two of
  three specs. BGOODEMPTY: the tell sampled `dim(ρ̄₁+ρ̄₂)`, which is
  **lower** semicontinuous, while the verdict needed an **upper**
  bound — so it *could not have settled the question* however it came
  out, and the direction said so. GCOLTRANS: the tell was posed at
  whole-shape existence, where a hit would have **refuted (GR-15)**
  rather than answering the question asked; it fired only once
  re-pointed at the shared datum. Both passed all three existing
  checks. **Add the fourth: name the quantity the tell measures and
  the direction the verdict needs it to move; if a draw can only
  bound it the wrong way, the tell is a pointer and must be labelled
  one.** Note this is the same family as the two unsatisfiable tells
  of 2026-09-10, now recurring with a diagnosable cause rather than
  as a pair of one-offs.
- **F32 — for a predicate built as a DIFFERENCE of two semicontinuous
  quantities, NEITHER verdict is cap-free**, and a landed `100 %` can
  be capped in the direction that would destroy it. F31 says a tell
  must sample a quantity whose semicontinuity runs the way the verdict
  needs. GSECOND (2026-09-12) shows the sharper form on the corpus's
  own transport predicate: the weak lift is `cg ⊆ pg`, an inclusion
  between two sets that are **both lower bounds** (deeper draws only
  add GOOD colourings to each side), so raising the draw count can
  **break a holding triple** as well as repair a failing one. The
  coordinator's spec asserted the one-way reading — *"the failure side
  is capped and the success side is not"* — which is true of a single
  colouring's GOOD verdict and **false of the predicate built from
  it**, and (GR-232)(ii)'s headline `15 304/15 304 = 100 %` is a
  HOLDING figure. Three controls found 0 movement at a 200-shape
  prefix, so it does not bite here; the reading was still wrong.
  Operationally: before quoting a cap direction, write the predicate
  out and ask which way EACH of its arguments moves — a cap inherited
  from a component is not a cap on the composite.
- **F33 — a driver's own DOCSTRING is an unguarded status surface, and
  the only gate on it is re-running the mode at its documented
  default.** `ledger.py --lint` does not run drivers;
  `check-driver-refs.py` checks that a cited mode EXISTS, never what
  it claims; nothing re-runs a docstring. GSECOND (2026-09-12) ran
  `gcoltrans.py --lift --shapes 400` — the default its own caps block
  and its own `--lift` mode description both describe as showing **0**
  lift failures — and got **125**; the coordinator reproduced it
  independently before the sentence was touched. The companion clause
  was separately wrong in the same two places (for a PREFIX cap the
  capped and full runs ARE bit-identical on the first N shapes, the
  stream being in the same state throughout). This is the same
  gate-invisible class as BGOODEMPTY's drifted defaults (2026-09-12,
  cross-return pass), one level up: there the PROSE was right and the
  driver had drifted, here the DRIVER is right and its own prose is
  wrong. Operationally: when a spec names a driver's documented
  default as a fence, re-run it at that default before quoting it —
  which is what the F26 consumer check produced here as a side effect.
- **F34 — a tell can be ALREADY SATISFIED IN THE LANDED CORPUS without
  anyone having read it that way**, and the standing *"is it already
  satisfied?"* check does not catch that. BPROPCL (2026-09-12) was
  dispatched with a tell — *one chart point where `U ⊄ ρ̄_i`* — and the
  spec recorded *"not reported anywhere: the corpus has measured
  `c_i(U)` but has not reported the containment as a chart-level
  condition"*. It was reported, twice: (BE-258)(iii)'s `dist = 6`
  column (16 rows at `c(Π_x) ≤ 1`) and (BE-273)(i)'s same 16 rows at
  `c(⟨M⟩) = 0` **are** the tell, and neither clause read them as
  containment. The check as written asks whether the corpus contains
  the **claim**; it must ask whether the corpus contains the
  **answer**, which is a different grep and usually a different
  vocabulary. Operationally: before calling a tell unsatisfied,
  ask what a landed measurement of the tell's quantity would LOOK
  like under a different name, and grep for that.
- **F35 — the anti-duplication fence can PRODUCE a convergence rather
  than merely prevent a collision**, when a fenced direction treats
  the sibling's landed work as an external input to TEST. The
  2026-09-12 round told BSIXTEEN not to attempt BPROPCL's properness
  lemma and BPROPCL not to close a block. BSIXTEEN landed mid-run
  proposing a repair — state the lemma relative to `⟨P₀⟩` — and
  BPROPCL, whose own headline through six steps was *"the two
  residues are NOT one question"*, **tested the proposal instead of
  arguing against it**: asserted at 1 281/1 281, which refutes the
  sibling sentence in its own frame and confirms it in the new one.
  Two directions fenced off each other's lemma converged on one from
  opposite ends of the same axis. **The mechanism is the concurrency
  rule** — diff against `HEAD`, never against the dispatch baseline —
  so that rule earns its keep as a discovery device and not only as a
  hazard control. F20 says reservations prevent naming collisions and
  not duplicated derivation; this is the other half: a PROSE fence
  plus a live `HEAD` can turn the overlap into a joint result.

- **F36 — a landed workbook can be INVISIBLE to the ledger, and every
  gate stays green.** `ledger.py`'s opener regex requires the `> `
  blockquote marker; a direction that writes its clause blocks as plain
  paragraphs produces a file with **zero** indexed claims, and because
  `--lint` reads the same index, the landing gate certifies nothing.
  BSIXTEEN (111) shipped 29 such openers and the defect survived a
  landing, a cross-return pass and a strategy pass before `--brief`
  returned empty on the lane §8 ranked first. **The check is one call** —
  `ledger.py --list | grep <FILE>` at landing, against the file's own
  opener count — and it belongs in the landing sweep, not in a cleanup
  round. Corollary: a direction's draft must be linted **while the
  coordinator can still see it**, since a green `--lint` on an unindexed
  file is vacuous.
- **F37 — a spec that QUOTES a tally manufactures agreement between
  independent returns.** `RESEARCH-ARC.md` §2 says never have a direction
  re-derive a shared monotone counter; the sharper form is that **citing
  the counter is the same hazard as asking for one**. Three concurrent
  directions, each handed *"record: 0 of 6"* and asked to score its own
  mechanism against it, each refuted its mechanism and each wrote
  *"0 of 7"* — three copies of a wrong value that **agree with each
  other**, which is precisely the signal a coordinator is otherwise
  entitled to trust, and which no per-return check can see because each
  draft is internally consistent. Two things were wrong: §7's figure is a
  **fixed unselected sample** whose value depends on not being
  incremented, and three refutations move the arc tally by three. **Fix:**
  cite a tally as a fixed, dated value with *"do not increment — the
  coordinator updates this at the cross-return pass"*, or omit the number
  and ask only for the direction's own verdict. Recorded after the
  coordinator propagated the same error into two coordinator-authored
  surfaces.

- **F38 — the errors cluster in ONE spec, not across the round.** Two
  consecutive rounds now show the same shape: the coordinator's mistakes are not
  spread evenly but concentrated in whichever entry was written last or fastest
  (round five: bar *(p)*'s premise; round six: **four** in rank 3 alone, three of
  them refutable with no computation). The operative lesson is not *"check
  harder"* but *"the last spec written is the one to re-read"* — and in both
  rounds the refuting evidence was **in an artifact the coordinator had already
  run or already cited**: `bgplaw.py`'s own in-band print, `bsixteen.py`'s
  dispatch table, `bsixteen.py:637`'s second `forced` call site. **A generated
  list, a single grep, or a definition read without its use sites is evidence
  about syntax, never about dispatch.**
- **F39 — a committed driver whose landed figure cannot be re-run from the
  command line is not reproducible** Promoted to `HARNESS.md`
  *Reproducibility* (every cap a landed figure varies is a CLI argument).
  Pruned at the Phase-39 close.

- **F40 — a status surface with no script behind it drifts on a per-landing
  cadence, and prose rules do not hold it.** Two instances in one session:
  `notes/Phase39.md` blew its 580-line cap (618, with a 17-line *Decisions
  made* entry) on one landing, and the ROADMAP Phase-39 Status cell grew
  623 -> 1325 chars over three. Both surfaces had a written rule forbidding
  exactly the growth, and both had been repaired by hand before — the note at
  `35e9ce6e`, the cell at doc-round slice 7. The note's cap now holds because
  `check-phase-note.py` exists; the cell's does not, because nothing reads it.
  The asymmetry IS the finding, and it is the same one
  `check-gapmap-cells.py`'s own source records ("two prose-only repairs were
  abandoned in favour of this mechanical cap"). **Actionable:** the four
  maintained "next concrete task" surfaces (the note's `**Status:**` header,
  *Current state*, *Hand-off*, the ROADMAP row) are one artifact class with one
  gate covering one member; a `check-roadmap-cells.py` on the Status table's
  per-cell char count is the cheap missing half. Until it exists, the
  coordinator re-thins the cell at verification — a landing agent updating "its"
  row will not, because appending one clause always looks proportionate from
  inside a single slice.

- **F41 — a coordinator spike raises S, and its every wrong turn is a defect
  the dispatch would otherwise have absorbed; but its ABSENCES are not
  verified.** Promoted to the playbook *Raising S* (spike discipline:
  positives to the `route` block, absences only as "check before hand-
  rolling"; search by bare declaration name) at the Phase-39 close; pruned.

- **F42 — a spike whose conclusion is about a CONSUMER must reproduce the
  consumer's file kind, or it measures the wrong thing twice.** Promoted to
  the playbook *Raising S* (a spike about a consumer reproduces the consumer's
  file kind; run both cases) at the Phase-39 close; pruned.

- **F43 — a complete sorry-free recon spike IS the build; slice it only if it is not.**
  Promoted to the playbook (step 3 *Resume and land*) at the 2026-09-26 harness
  review, alongside Fable leaving the rung map (*Pick the rung*); the evidence is
  the Phase 40c rows above and `notes/harness/incidents.md` 2026-09-26.

- **F44 — on a transcription slice the prose is the part no gate checks
  (Phase 40, nine rows).** The compiler checks the Lean copied from a spike.
  Nothing checks the docstrings, module docs, commissioned rewordings,
  second-reader repair texts or connective blueprint prose written around it,
  and that is where Phase 40's defects were: a docstring with hypothesis and
  conclusion swapped, a lemma credited to the wrong parent or to
  Katoh–Tanigawa, a rewording that dropped "nonempty" and "proper", a repair
  calling pictures "admissible" that its spike never proves, a copied comment
  naming another site's callee, a KT lemma glossed with a case it lacks, a
  definition's degree conditions misstated. Each was caught only by reading the
  new prose against the statement it describes. Prose a recon or a second
  reader wrote and the coordinator passed on is a coordinator artifact (F19).
  In a prose round whose connective text makes cross-section claims, rate P by
  those claims: two Sonnet slices of `40-exposition` needed Opus correctives,
  then 22 Opus slices ran clean. Promoted to the playbook (*Verification
  tiers*; the docs-only P calibration). **Recurred in RECONCILE and 41a
  (three rows):** two closes' summaries contradicted the round's own record
  (every statement's strength "as it was", against `F-084`'s two recorded
  narrowings; a credit `reconcile-texts` task 6 had superseded), and item
  5b's docstrings had mid-sentence line breaks and a false "no declaration
  uses it". Promoted at the 41a grooming: *Verification tiers* reads a
  close's summary sentences against the round's recorded exceptions and
  superseding verdicts.
- **F45 — a claim about the tree's state is checked per name at HEAD, never
  inherited (five rows, three in one round).** A FRICTION entry or note written
  before a later round, an open's task text, a sibling commit's deletion list,
  and a one-line grep for a multi-line `\lean{…}` each handed a builder a claim
  ("deleted by X", "unpinned", "stays", "all N in commit Y") that was false at
  HEAD. Ten of 18 names "unpinned for deletion" were live helpers
  (`40-simplify` 10a); two pinned sites read as unpinned (`40-cleanup` task 2);
  `40-docs` tasks 2, 7 and 14 each copied or compressed a multi-commit outcome
  wrongly, under a `hygiene` block that asked for greps, applied per sha cited
  rather than per declaration counted. The check is `git log -S'<name>'` per
  declaration and `git show --stat --diff-filter=D <sha>` per cited deletion; a
  multi-commit outcome cites each commit, and a deletion prompt names the keep
  list beside the delete list. Promoted to the playbook (*Verification tiers*,
  the `hygiene` block) and `CLEANUP.md` §D.
- **F46 — F43's alternative is validated: a fresh builder handed the spike
  (Phase 40, seven arcs).** After F43, the remaining recons' contexts stood at
  460–750k when their spikes came back sorry-free, so the opens and builds went
  to fresh agents handed the spike file, with the verdict and the PI's
  decisions in a scratch file from 40g on: 40e build 1, 40f, 40g, 40i, 40j, 40k
  and 40m. Zero Lean rework across them, at 240–440k per build, against 627k
  and 225 tool calls for 40c's one resumed build. Promoted to step 3 *Resume
  and land*: past about 400k of recon context, hand off.
- **F47 — under a user's "follow precedent" answer the coordinator settled
  recon-flagged calls, and none was reversed (40i–40k).** Fifteen calls (a
  hypothesis form, "no new mathematics", a placement against a PI convention,
  twelve re-homings), each checked against its source before it was settled,
  and each recorded as the coordinator's, not the PI's, with its reversal cost.
  None was reversed through Phase 40's close. Not promoted: it changes when the
  PI is asked, which is the PI's to decide (`notes/Phase40-docs.md`, the
  close's report).
- **F48 — two recurring checks have no gate.** (a) A green node whose statement
  carries `\leanok` and whose proof environment does not (40i B2, 40l B3):
  `blueprint/lint.sh` checks a statement's `\leanok` against its `\lean{…}`,
  never against the proof's, and the tree carries no `sorry`, so every such
  node is a defect a lint guard would catch. (b) `notes/check-phase-note.py`'s
  `NOTE_RE` matches `PhaseN.md` and `PhaseN<letter>.md` only, so each cleanup
  round's log is checked by hand (flagged at `40-exposition`'s open; every
  `40-docs` task did it). F40's lesson again: a written rule does not hold a
  surface no script reads. **Closed 2026-10-05** at the PI's request: (a) is
  `blueprint/lint.sh` check 8, whose first run found two more missed proof
  markers, Phase 34's `thm:bodyhinge-generic-rank` and
  `cor:bodyhinge-generic-rigid`, fixed in the same commit; (b) is
  `check-phase-note.py` *Which files* (a suffixed note titled "work log").
- **F49 — the harness stops what it backgrounds, and a session may not see
  processes (RECONCILE 3/3 task 38.2, 2026-10-22).** A Bash call past its
  `timeout` is backgrounded and stopped ten minutes later (`killed`). The
  stop kills the whole process tree (a heartbeat child of a stopped task
  died with it) and Lake keeps the modules the run finished, so a re-run
  resumes; the notice reaches an agent only between tool calls. A session
  that cannot list processes reads an empty `ps | grep` as "no build", and
  cannot see a shell-`&` build at all. The memory pressure that day came
  from other processes, but two whole-project builds ran into it before the
  PI rebooted. Promoted: `CombinatorialRigidity/CLAUDE.md` (an empty
  process listing is not evidence; a memory-pressure denial is a stop), the
  phase-builder core (waiting out a backgrounded gate), the command's steps
  5 and 7, and the autopilot prompt's stop table.
- **F50 — a compression erases the PI's words unless the prompt says they
  are not compressible (three rows: `prose-laman` 5.7, `reconcile-lean` 35.1
  and 38.4).** Told to bring a work log under its line cap, three builders
  shortened a verbatim PI answer: to a pointer, as a "duplicate"; to a
  paraphrase beside the builder's own entry; to one line under the entry's
  bold. `check-phase-note.py` cannot see it; each time the coordinator's read
  of the PI section caught it and a fixup restored it. The third came after
  the second's row was written: the lesson lived only here, so the next
  compression prompt did not carry it. Promoted: `notes/CLAUDE.md` *Phase
  notes* (a PI entry is never edited, shortened or paraphrased) and the
  playbook's shaping paragraph (a compression prompt says so).
- **F51 — under a rule that bars a class of edit, builders made neighbouring
  edits, and the coordinator accepted every one (seven rows: PROSE rounds 2–4
  and `reconcile-lean` task 14).** RECONCILE's hygiene rule (`notes/Reconcile.md`
  §2, still binding in Phase 41) records a statement change as `S` and does
  not act on it. Builders anchored a pin's own hypothesis in its node, dropped
  a false gloss, moved a sentence that is not the claim out of a statement,
  narrowed a node to its pin's form, and strengthened a callee's conclusion so
  that it could be called. Each was checked against the source and
  accepted. The rows' own lessons agree: a slice's precedent outweighed the
  prompt's restated rule (2.15 followed 2.11), and
  the readings a prompt named in advance came back flagged and checkable
  (2.3, 2.12). Promoted to the shaping paragraph: a prompt that bars a class
  of edit names the neighbouring edits it allows, and each exception the
  coordinator accepts is written where the next builder reads.
- **F52 — a deleted-name sweep also greps each name's distinctive stem
  (`reconcile-lean` task 4).** Task 4 deleted
  `linearIndependent_sum_{augment,p2,p3}_candidateRow`, and six docstring
  mentions survived in brace and suffix forms (`…_{p2,p3}_…`,
  `_p3_candidateRow`): the builder's deletion gate and the coordinator's
  re-check both ran `grep -w` per exact name, and the next dispatch found
  them. One row, but both checks shared the gap, and so did
  `CombinatorialRigidity/CLAUDE.md`'s deletion gate. Promoted: the `hygiene`
  block and that gate.
- **F53 — the multi-commit trial is dropped (Phase 41a, two arcs; PI,
  2026-10-24).** Two arcs ran, items 2–3 and 6–7. Per landed commit
  (`session-usage.py` at the commits' times), the two continuation commits,
  items 3 and 7, wrote less cache than a fresh single-commit build but read
  2.4–4.4× as much (10.7M and 17.4M against items 1 and 3a's 3.96M and
  4.45M), since every turn re-reads ~300k of context. At cache reads a tenth
  of the base input price and writes 1.25×, a continuation commit cost about
  1.2M and 1.85M input-token equivalents against 0.6M and 0.8M. Wall time
  per commit was not lower (arc 2: 15.9 and 9.3 min, against 9.5 and 10.3).
  The coordinator-side saving the trial was for (fewer launches and
  re-orientations) was never measured. The PI dropped the trial on this
  evidence. Removed: the playbook's *Multi-commit arcs* section (now a
  one-paragraph pointer here) and steps 2, 4 and 5's arc sentences, the
  builder core's bullet, the four builder definitions' line, and the
  autopilot's "arcs: on". Kept: `session-usage.py`'s `--since`/`--until`
  bounds and cache columns. The two arc rows are in git history at
  `78c3f1e4`.
