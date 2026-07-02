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
  *A "needs the [X]-variant of [landed lemma Y]" flag is P ≥ 2, usually
  P = 3:* when a design pass or hand-off says a step "just needs the GP /
  general-rank / deficiency-aware variant of" a landed lemma, it is
  naming a **genuinely-new sibling**, not a mechanical restate — *unless*
  that variant demonstrably already exists. Grep for it before rating; a
  missing variant is a new leaf (often its own slice or a
  decompose-recon). Calibration: a "buildable GP variant" flag rated
  P≈2 BLOCKED at the build, and the follow-up design pass re-rated the
  leaf P≈3.
  *Likewise, an "instantiation / bookkeeping — wire landed brick B into
  consumer C's slot" flag is P = 1 only when B's **conclusion** sits at
  C's slot's **same object / framework level**, not merely the same type
  and not merely that B exists:* a brick at the wrong level (e.g. a
  `splitOff`-level transport for a `removeVertex`-level slot) does **not**
  fill the slot, so the "instantiation" hides a genuinely-new leaf (P=3).
  Read the consumer's slot binding *and* B's landed conclusion before
  rating. Calibration: an arm flagged "pure instantiation, all transport
  math landed" was rated P≈2; the build BLOCKED on a graph-level mismatch,
  a recon confirmed it, and a de-risk re-rated the real leaf P≈3.
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
| P=3 with S=1 and B≤2 (exact pinned signatures + a named route) | sonnet (boundary cell — pair-eligible, see below) |
| P=3 (with S≥2) or B=3 | opus |
| S=3, or phase-open / phase-close / design-settle commits | fable (top rung; never delegated down) |

- **Fragility-zone modifier (map v2, adopted 2026-07-01).** Each repo's
  sibling log maintains a short **fragility-zone list** — the files /
  subsystems with known heavy-elaboration / defeq-fragile behavior
  (heavy-`whnf` carrier zones and the like). A **producer build**
  touching the zone runs at **opus minimum** regardless of profile;
  mechanical edits and refactors in the same files stay mapped.
  (Calibration: sonnet wedged ~2 h on a heavy-zone producer that opus
  then landed by decomposition, while a later sonnet *refactor* in the
  same file ran clean — the wedge risk attaches to producer builds,
  not mechanical work.) This modifier replaces phase-wide standing
  rung overrides as the default control for fragile zones: it prices
  the zone per-dispatch instead of freezing a whole phase at one rung.
- **The S=1/P=3 sonnet boundary cell** is deliberate cost
  optimization: its backing is one boundary pair in which a sonnet
  duplicate matched opus on a P=3 brick carrying an exact-signature
  pin — n=1, so dispatches landing in this cell are the *priority*
  boundary-pair targets, and the below-top-rung extra gates apply in
  full. The cell routes only *exactly-pinned* bricks away from opus:
  if the pin's exactness is in any doubt, the spec isn't S=1 and the
  task maps to opus as before.
- **Raising S is the coordinator's cost lever.** To move a task
  down-rung, sharpen the *committed* hand-off — paste the exact
  target signatures, file pointers, and route into the phase note /
  design doc — so S genuinely drops to 1. Never compensate with
  per-dispatch prompt padding (*Constant factors + prompt shaping*
  below): a hand-off edit raises S for every rung, is visible in git,
  and keeps rows comparable.

- **The map covers commit-producing dispatches.** Read-only recon /
  research dispatches (no commit deliverable) fall outside the axes:
  log them with Mode `recon` and pick the rung by stakes — default
  opus; fable when the verdict re-routes a phase or adjudicates a
  carried-hypothesis / motive change. (Rating a postmortem recon
  1/1/1 maps to haiku — absurd; the axes measure commit risk, not
  question difficulty.) The fable-vs-opus value question on the
  *harder* design passes (re-routes, new-gap recons) remains open:
  when fable is reachable, actually route those to fable per this
  rule, and occasionally run an **opus-vs-fable diverse-lens recon
  pair** on a hard design seam to collect the missing comparison.
- **Session-start availability check (before the first dispatch).**
  Rungs come and go between sessions (model-availability outages, plan
  caps). At session start the coordinator determines which rungs the
  Agent tool's `model` parameter can actually reach this session and
  records the available set — with an expiry — in the repo-local
  config, *then* fixes each unavailable rung's substitute up front per
  the next bullet. Establishing the substitution once, at the top,
  keeps assignment reproducible and the decision visible in one place
  rather than rediscovered per-dispatch (a coordinator that learns
  fable is gone only when its first fable-mapped pass comes due has to
  reconstruct the substitution mid-loop). A fresh coordinator re-runs
  the check and reverts to the full map as rungs return.
- **Unavailable rung → substitute the nearest available, log the
  substitution.** When the session-start check (above) finds a mapped
  rung's model unavailable (e.g. fable unavailable), substitute the
  nearest available rung and record it in the row's Model column +
  Notes. For the fable-mapped commits
  (design-settle / phase-boundary / S=3) the substitute is **opus**
  (the next-most-capable). This is *not* a map change — the map is
  what would run with all rungs present; a session-local config note
  records the constraint and its expiry, and a fresh coordinator
  reverts to the map. Precedent (2026-06-12, rows 84–86): fable-mapped
  design pins ran at opus cleanly, incl. one carries-table-correction
  pin that caught two design errors. Open question this leaves: does
  fable add value over opus on the *harder* design passes (re-routes,
  new-gap recons), not just the correction-shaped ones?
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
  **A pair has a second value beyond model-comparison: it is an
  adversarial audit of the *pin/hand-off* the primary builds against.**
  A duplicate that returns BLOCKED with a design-error diagnosis
  (rather than a build) is a **high-value outcome, not a failed pair** —
  the fresh adversarial read caught what the pin's author and the
  coordinator's scrutiny both missed. So a pair is especially worth
  running when the build's pin is recent or not yet deeply verified;
  grade such a BLOCK on the *correctness of its diagnosis*, and the
  primary's faithful-but-wrong commit is **not** a model failure (it
  implemented the pin). Verify the diagnosis against the landed source,
  then correct the pin (precedent: a pin error a pair caught *after* the
  coordinator had approved it).
  **Caveat — a pair audits the leaf's pin, not its fitness for a not-yet-
  built consumer.** Both members build the leaf in isolation; if the leaf's
  *route choice* hinges on a downstream consumer's obligations (interface
  hyps not yet in tree), the pair can both pass — validating the leaf *as a
  lemma* — and still be the *wrong route*, surfaced only when the consumer
  is built. Precedent: a route-2 leaf passed a boundary pair, then its
  producer BLOCKED on a containment route 2 structurally couldn't supply
  (→ re-route + a dead leaf). When a leaf's route hinges on an unbuilt
  consumer, settle the route against the consumer first — a pair does not
  substitute for that.
  **Variant — a diverse-lens RECON pair for a recurring-mis-pin DESIGN seam
  (read-only, no worktree).** When a *design/architecture* seam has resisted
  several builds + single-pass recons (single reads are wrong ~half the time in
  a fragile zone), run two read-only recons concurrently with **distinct lenses**
  — one *constructive* (settle the route + leaf plan), one *adversarial-refute*
  (try to break it / find the wall / hunt the unsatisfiable hypothesis). The
  refute member often **adjudicates what the constructive member flags as
  "open"**: the two may disagree on the verdict *label* yet converge on the
  substance, and the disagreement narrows exactly the one fact the coordinator
  must source-verify. No commit / no worktree (both read the shared tree; the
  coordinator source-verifies the pivotal claim, then authors or dispatches the
  resolution). Precedent: the 23c `±r`-seam — A (constructive) returned
  NEEDS-REVIEW, B (refute) returned LIKELY-SOUND by distinguishing two rows; the
  coordinator's source check confirmed B and resolved a seam that had survived 4
  builds + 2 single-pass recons.
  *Worktree build caveat (Lean repos):* a fresh worktree has no
  `.lake/` — a bare `lake build` there recompiles mathlib from
  source (expensive; on shared machines a known OOM risk). **The
  robust fix is coordinator-side: seed the worktree's `.lake` from
  the main checkout before dispatching the duplicate** — e.g. on
  APFS `cp -Rc .lake <worktree>/.lake` (copy-on-write clone, fast
  and disk-cheap; the target must not already exist, else BSD `cp`
  nests the copy inside it — `ls -a` to check). Seeding beats
  having the duplicate run `lake exe cache get` for two reasons
  found on first contact (2026-06-12): (1) sandboxed agent
  environments may deny access to the out-of-tree cache dir
  (`~/.cache/mathlib` → `cache get` dies with *"already exists
  (error code: 17)"* / *"Operation not permitted"* — environmental,
  not recoverable agent-side); (2) the clone carries the *project*
  oleans too, so the duplicate's build is incremental rather than
  cache-restore + full project rebuild. Where seeding isn't
  possible, fall back to the duplicate running `lake exe cache get`
  first; if that fails, the duplicate aborts rather than building
  through.
  **The caveat makes pairs safe to run — don't skip them out of
  OOM/cost caution** (that caution is what the caveat exists to
  retire; a coordinator deferring pairs "until later" is how a whole
  phase closes with zero, the 22h gap). Procedure:
  - **Pin the task first.** If the hand-off offers a free choice of
    next slice, the coordinator pins it to one slice (a hand-off
    edit committed with the log row) before dispatching, so both
    members run the same task.
  - **Parallel dispatch is sanctioned** (2026-06-12, user-approved;
    previously "sequential, primary first"). The worktree isolates
    the trees, and the cache-get caveat retires the mathlib-rebuild
    risk, so the two members may run concurrently — the duplicate
    launched alongside (or in the background of) the primary. The
    residual concurrency is two *project* builds on one machine:
    acceptable on a dedicated box; fall back to sequential when the
    machine is shared, already under memory pressure, or the slice
    sits in a known heavy-elaboration zone. Verification order is
    unchanged: the primary's gates run and finish before either row
    is graded (write-after-verification).
  - **Harvest the duplicate before discarding it.** "Discard the
    duplicate's tree" applies *after* both rows are logged. At that
    point the coordinator MAY port concrete superior elements of the
    duplicate's commit (a cleaner proof, richer docstrings, blueprint
    prose) into the primary branch as a coordinator-authored
    follow-up commit that names the duplicate rung as the source —
    the comparison data is already recorded, so incorporation costs
    nothing scientifically and recovers value from the duplicate's
    spend. Grades do not retro-change; note the incorporation (and
    its cost) in the duplicate row's Notes. Harvest (diff/cherry-pick)
    before pruning the worktree.
  - **Worktree gate limitation.** Repo gates that need untracked
    tooling (e.g. a gitignored blueprint venv → `verify.sh` /
    `checkdecls`) can't run in a worktree; the duplicate runs the
    Lean gates + the static lint and discloses the rest, graded `—`.
  - **Fixed duplicate prompt.** Prepend this prologue to the
    standard dispatch prompt verbatim (and substitute the branch
    name for `master` in its commit instruction); change nothing
    else. Seeded-worktree form (the default — see the build caveat
    above):

    > Boundary-pair duplicate dispatch (model-experiment protocol):
    > you are working in the isolated git worktree at `<path>`
    > (branch `<branch>`), NOT the main checkout. Do all reading,
    > editing, building, and committing inside that directory. The
    > coordinator has pre-seeded the worktree's `.lake` build cache
    > from the main checkout — do NOT run `lake exe cache get` (it
    > can fail under the sandbox and is not needed); `lake build` /
    > `lake lint` run incrementally against the seeded cache. If a
    > build nevertheless starts compiling thousands of mathlib
    > files, stop immediately and return BLOCKED. Never run
    > `lake update`.

    Unseeded fallback form: replace the seeded-cache sentences with
    "Before any `lake build` or `lake lint`, first run `lake exe
    cache get` in the worktree so the build reuses the mathlib olean
    cache; if the cache step fails, do not build through — return
    BLOCKED instead."
- **Escalation.** BLOCKED return or failed verification → re-dispatch
  the same task one rung up; log the pair (wasted cost included).

## Constant factors + prompt shaping (versioned rung addenda)

Everything except the `model` parameter and the rung's **versioned
addendum** (below) is held fixed: the dispatch prompt body, the
per-commit verification gate, the repo's own CLAUDE.md discipline.
Extra gate for below-top-rung dispatches: the coordinator reads the
full diff (not just `--stat`) before the next dispatch.

**Rung addenda — prompt shaping as a versioned, logged treatment
(adopted 2026-07-01).** The original design forbade per-model prompt
deltas to keep comparisons unconfounded. With the failure-mode data
in — cheap-rung failures concentrate in the discipline / attestation
layer, essentially never in the mathematics — the experiment now
deliberately treats a short prompt addendum as part of the *rung*,
under three rules that keep rows interpretable:

1. **Versioned library, not free-form.** Each below-top rung has one
   short addendum with a version tag (`haiku-a1`, `sonnet-a1`, …),
   appended verbatim to the fixed prompt. Changing an addendum bumps
   the version; the sibling log's config records the versions in
   effect, so any row's exact prompt is reconstructible.
2. **Discipline layer only.** An addendum targets the rung's
   *observed failure layer* (attestation honesty, checklist
   fidelity, wedge bail-out). It must NOT carry task content —
   signatures, routes, design pointers. Task-content sharpening is a
   coordinator hand-off edit committed to the repo (*Raising S is
   the coordinator's cost lever*, above), never a prompt delta.
3. **The addendum's effect is itself data.** Whether a version
   retires its target failure mode is a *Findings* item — compare
   the rung's rubric-bit failure rates before/after the version.

Current library:

- `haiku-a1` (rails): "Do exactly the named edit and nothing else.
  If anything unexpected appears — a build failure, a missing
  declaration, a surprising diff — STOP and return BLOCKED rather
  than improvising a fix. Never modify the toolchain, lakefile, or
  manifest. Report gate results by pasting the actual command
  output, not a summary."
- `sonnet-a2` (discipline guard; supersedes `sonnet-a1` 2026-07-01 —
  two of the first three `a1` dispatches ended their turn parked on a
  background `lake build` despite the fixed prompt's own clause, so
  the rail is now concrete and mechanism-level): "Before committing:
  re-read the pinned checklist / design section VERBATIM and confirm
  every pinned sub-clause is either delivered in this commit or
  explicitly re-flagged in the hand-off — never rewrite a checklist
  or hand-off item to match what landed. Run your build/lint gates in
  the FOREGROUND — never launch `lake build` or `lake lint` as a
  background task, and never end your turn while any command you
  started is still running: an ended turn strands the work
  uncommitted. Attest gates only from the final run's actual output
  (a warning-bearing build is not clean). If elaboration wedges
  (~15+ min without progress on one goal), stop and return BLOCKED
  with the goal state rather than pushing through."
- opus / fable: no addendum (observed failures at these rungs were
  upstream plan / pin errors, which prompt text cannot fix).

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
| Mode | normal / probe / boundary-pair-primary / boundary-pair-duplicate / escalation-retry / recon (read-only, no commit) / resume (the same killed **or user-interrupted** agent continued via SendMessage to its agentId — context and read phase intact, not a fresh dispatch; rate it as the original task, same rung; when a user interrupt returns an error with no agentId, recover it from the local subagent logs. **Also covers the spike→resume-to-build pattern** — a *completed* read-only recon/spike agent continued via SendMessage to execute the build it de-risked (coordinate-phase step-1 / rescue §6): reuses the spike's sorry-free work instead of re-deriving. Log the spike itself as a prior `recon` row; rate the resume row by the **build's** S/P/B, not the recon's) |
| Outcome | clean / repaired (note cost) / escalated / BLOCKED / killed (harness or usage-limit death mid-dispatch, no agent fault — log the wasted cost; **prefer resuming the same agent** via SendMessage to its agentId where the harness supports it [agent teams], preserving the full context and read phase; only if resume is unavailable or fails, salvage the transcript read map into a fresh relaunch prompt) / salvaged (a **user interrupt** stopped the dispatch mid-flight but the agent had already produced **complete, gate-passing work** — unlike `killed`, the deliverable exists, so the coordinator does NOT resume or relaunch: verify it in full [build/lint/sorry-grep + the shape check against the pinned design], finalize the notes/hand-off/commit the interrupt pre-empted, and commit the salvage; grade the agent's delivered artifact, with Notes/Commit `—` since those phases were coordinator-supplied. Not an agent fault) |
| Rubric | 6-bit quality vector, below |
| Cost | tokens + tool uses + wall time, as reported by the Agent tool |
| Notes | the experiment-relevant signal only — see *Notes discipline* |

**Notes discipline — the column is the experiment-meta *delta*, not a recap,
and a length gate enforces it.** The Notes field records only what the
*experiment* needs and is found *nowhere else*: the outcome's cause, which
rubric bit failed and why, confounds / cost anomalies that qualify the data
point, and the escalation- / boundary-pair *verdict*. It is **not** a recap of
the mathematics, the proof route, or the design verdict that landed — **the
commit message is the recap** (`git show`), alongside the design § the row
cites and `notes/PhaseN.md`'s *Decisions made*. The test: if a sentence
restates what the *commit* did rather than how the *model* did, cut it.

**Enforced cap: ~600 chars (~4 lines) per Notes cell.** A repo-local commit
gate checks every row a commit touches and *rejects* an over-cap row (in this
repo, `notes/check-log-rows.py`, run in the coordinator's per-commit step;
`--all` audits the whole table). The cap is a hard limit, not a target:
strengthening the prose alone failed three times — rows 84–93, then 96–100, then
191–194 each re-bloated by recapping the math or re-narrating an episode — so the
gate, not exhortation, is the control. Two corollaries it makes mechanical:

- **Episode lessons live in *Findings*, written once.** A multi-row episode (a
  boundary pair, an escalation, a re-route later caught wrong) yields one durable
  lesson; write it in *Findings* and have each participating row *cite* it ("→
  Findings <date>") rather than restate it. A row pushing over the cap is usually
  a row trying to re-narrate its episode's shared lesson.
- **Write each row to the cap on its own, never to its neighbors.** A
  grandfathered bloated row above is not a template — a new row that reads
  conspicuously terser than its neighbors is *correct*. (Compressing the
  grandfathered backlog is a separate `--all` cleanup pass, not a license to
  match it.)

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
**The dispatch prompt names the rung's model explicitly** for the
Co-Authored-By trailer (e.g. "you are a Sonnet agent, so the trailer
is `Co-Authored-By: Claude Sonnet 5 <noreply@anthropic.com>`") — the
coordinator knows the rung at dispatch time, so this is free. A
generic "name the model you actually are / don't copy from git log"
clause failed three times across two rungs before explicit naming
fixed it (23g rows 639/651/658 vs 659/660).

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
