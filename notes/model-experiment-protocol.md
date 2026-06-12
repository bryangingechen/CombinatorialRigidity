# Model-tier experiment — protocol (portable)

**This file is repo-agnostic by design**: copy it verbatim into any
formalization repo running the same experiment. Repo-local state
(which phase is under test, the log, local pointers) lives in a
sibling `notes/model-experiment.md`; this file carries only the
protocol. Protocol improvements are encouraged — when one lands, fix
it immediately in the repo where the lesson surfaced, then propagate
the same edit to the other participating repos (note the date of the
last sync in the sibling log file). The sync step is cheap; never let
it deter or delay getting the process right.

**Question.** Coordinator sessions (e.g. a `/coordinate-phase` loop)
dispatch one subagent per commit. When do cheaper / faster models
suffice for formalization tasks, and what predicts it?

**Design stance.** Dispatches are *observational* data — each task
runs once, so cross-dispatch model comparisons are confounded by
task. The protocol therefore (a) rates every task a priori on a
small set of axes so results can be stratified by task profile,
within and across repos; and (b) manufactures the few genuinely
paired comparisons available: escalation pairs (a cheap failure
redone by a stronger model on the *same* task) and deliberate
boundary pairs (below).

## Task rating: three axes, scored before dispatch

The coordinator reads the active hand-off pointer (and whatever
design docs it cites) and scores, *before* dispatching:

- **S — spec precision.** How completely the written hand-off pins
  down the target.
  1 = exact target signatures / file edits already written down;
  2 = shape known, proof route or template named;
  3 = requires design decisions ("decide X", novel API shape).
- **P — proof novelty.** How much proof discovery the commit needs.
  1 = mechanical (doc edits, restates, bridges, `rfl`-adjacent);
  2 = real proof assembly along a known route with named grounding;
  3 = novel proof route, search, or no informal proof written.
  *Docs-only is not automatically P=1:* a deliverable that *describes
  an unbuilt argument* (red-node prose, deferred-route accounts)
  takes its P from the math content, **P ≥ 2** — "mechanical" covers
  only edits checkable against existing artifacts. (Calibration: a
  2/1/1-rated blueprint-honesty commit's one failure was precisely
  its prose describing the deferred KT-6.5 route.)
- **B — blast radius.** Integration breadth.
  1 = one file, additive (nothing existing breaks);
  2 = few files, bounded caller repair through known bridges;
  3 = cross-cutting cascade, open-ended repair.

Rate from the *written* hand-off, not from optimism about the task;
if the hand-off is too thin to rate, that is itself an S=3 signal
(or a sign the previous commit's hand-off violated the contract).

## Model assignment map

Published function of the profile, so assignment is reproducible:

| Profile | Rung |
|---|---|
| S=1, P=1, B=1 | haiku |
| max(S,P,B) = 2 | sonnet |
| P=3 or B=3 | opus |
| S=3, or phase-open / phase-close / design-settle commits | fable (top rung; never delegated down) |

- **The map covers commit-producing dispatches.** Read-only recon /
  research dispatches (no commit deliverable) fall outside the axes:
  log them with Mode `recon` and pick the rung by stakes — default
  opus; fable when the verdict re-routes a phase or adjudicates a
  carried-hypothesis / motive change. (Rating a postmortem recon
  1/1/1 maps to haiku — absurd; the axes measure commit risk, not
  question difficulty.)
- **Optimistic ladder.** When torn between two scores on an axis,
  score lower (cheaper). The capability boundary is the experiment's
  main product; the per-commit verification gate bounds the damage.
- **Probes.** Occasionally dispatch one rung *below* the mapped one,
  marked `probe` in the log — deliberate failure-data collection.
- **Boundary pairs.** Occasionally (~1 in 4–5 dispatches whose
  profile sits at an assignment boundary), additionally dispatch the
  *same task* to the adjacent rung in an **isolated worktree**; keep
  the primary's commit, log both outcomes, discard the duplicate's
  tree. This is the only true same-task comparison in the design.
  *Worktree build caveat (Lean repos):* a fresh worktree has no
  `.lake/` — a bare `lake build` there recompiles mathlib from
  source (expensive; on shared machines a known OOM risk). Have the
  duplicate run `lake exe cache get` in the worktree first so its
  build reuses the mathlib olean cache; if the cache step fails,
  abort the duplicate rather than building through.
  **The caveat makes pairs safe to run — don't skip them out of
  OOM/cost caution** (that caution is what the caveat exists to
  retire; a coordinator deferring pairs "until later" is how a whole
  phase closes with zero, the 22h gap). Procedure:
  - **Pin the task first.** If the hand-off offers a free choice of
    next slice, the coordinator pins it to one slice (a hand-off
    edit committed with the log row) before dispatching, so both
    members run the same task.
  - **Sequential, primary first.** Verify the primary fully (its
    gates finish) before launching the duplicate — one build at a
    time per machine.
  - **Worktree gate limitation.** Repo gates that need untracked
    tooling (e.g. a gitignored blueprint venv → `verify.sh` /
    `checkdecls`) can't run in a worktree; the duplicate runs the
    Lean gates + the static lint and discloses the rest, graded `—`.
  - **Fixed duplicate prompt.** Prepend this prologue to the
    standard dispatch prompt verbatim (and substitute the branch
    name for `master` in its commit instruction); change nothing
    else:

    > Boundary-pair duplicate dispatch (model-experiment protocol):
    > you are working in the isolated git worktree at `<path>`
    > (branch `<branch>`), NOT the main checkout. Do all reading,
    > editing, building, and committing inside that directory.
    > Before any `lake build` or `lake lint`, first run
    > `lake exe cache get` in the worktree so the build reuses the
    > mathlib olean cache; if the cache step fails, do not build
    > through — return BLOCKED instead. Never run `lake update`.
- **Escalation.** BLOCKED return or failed verification → re-dispatch
  the same task one rung up; log the pair (wasted cost included).

## Constant factors

Everything except the `model` parameter is held fixed: the verbatim
dispatch prompt, the per-commit verification gate, the repo's own
CLAUDE.md discipline. Do not pad the prompt differently per model.
Extra gate for below-top-rung dispatches: the coordinator reads the
full diff (not just `--stat`) before the next dispatch.

## Per-dispatch record (log schema)

One row per dispatch in the sibling log file. **Write and commit the
row only after the coordinator's verification pass has completed in
full** — gates, the full-diff read (mandatory below top rung), and
the re-read of the updated hand-off — never between gates: a
prematurely-scored row silently inflates the rubric and forces a
history-visible correction once pushed. Correct a committed row by a
follow-up edit, not a history-rewriting amend. When appending a row
by string-edit, match the previous row's tail only — an edit whose
match spans the following section header silently deletes that header
(this clobbered a log's `## Findings` heading three times in one
coordinator session before being caught).

| Field | Meaning |
|---|---|
| # | dispatch ordinal |
| Task | short name + final commit sha (post-amend) |
| S/P/B | the a-priori axis scores |
| Model | rung actually dispatched |
| Mode | normal / probe / boundary-pair-primary / boundary-pair-duplicate / escalation-retry / recon (read-only, no commit) / resume (the same killed agent continued via SendMessage to its agentId — context and read phase intact, not a fresh dispatch; rate it as the original task, same rung) |
| Outcome | clean / repaired (note cost) / escalated / BLOCKED / killed (harness or usage-limit death mid-dispatch, no agent fault — log the wasted cost; **prefer resuming the same agent** via SendMessage to its agentId where the harness supports it [agent teams], preserving the full context and read phase; only if resume is unavailable or fails, salvage the transcript read map into a fresh relaunch prompt) |
| Rubric | 6-bit quality vector, below |
| Cost | tokens + tool uses + wall time, as reported by the Agent tool |
| Notes | anything load-bearing |

**Cost caveat.** The reported token figure is noisy across runs (it
does not obviously track tool-use count or wall time); record all
three cost numbers and prefer wall time + tool uses for comparisons
until the token metric is understood.

**Quality rubric** — scored by the coordinator during the
verification pass, each item pass/fail:

1. **Gates** — build / lint / blueprint checks green after the commit.
2. **Scope** — diff matches the hand-off pointer; no unrelated edits.
3. **Lean quality** — idiomatic per repo conventions; proofs not
   bloated; API shaped as the design docs specify (judged on the
   full diff read).
4. **Blueprint sync** — nodes/pins updated correctly with the Lean.
5. **Notes discipline** — hand-off updated and honest; work-log
   entries within the repo's length discipline.
6. **Commit message** — accurate, well-scoped, follows repo style.

Failed rubric items the coordinator fixes (amend or follow-up
commit) get noted with their repair cost; the fix itself does not
retroactively flip the bit.

**Attribution hygiene (not graded).** If a subagent mis-attributes
the commit (wrong author email, co-author trailer naming the wrong
model), the coordinator amends before logging the final sha. These
are prompt-discipline artifacts, addressed at the source (the repo's
CLAUDE.md commit-attribution rule); track recurrences in Notes but
don't count them against the model's outcome grade.

## Analysis discipline

- **Never compare cost or quality across different tasks directly**
  — only within escalation pairs, boundary pairs, or stratified by
  identical (S,P,B) profile with n large enough to mean something.
- Per-repo n will be small (a phase ≈ 15–40 dispatches); the schema
  is shared across repos precisely so logs can be pooled.
- At each phase close, write a *Findings* section in the sibling log:
  observed success/repair rates per profile × rung, escalation-pair
  outcomes, boundary-pair outcomes, and any proposed change to the
  assignment map (apply protocol changes in all participating repos
  together).

## Concluding the experiment

When enough data has accumulated, distill the pooled findings into a
standing guideline (e.g. an assignment map promoted into the
coordinator skill / command file), flip the sibling log's Status to
concluded, and point the coordinator hook at the guideline.
