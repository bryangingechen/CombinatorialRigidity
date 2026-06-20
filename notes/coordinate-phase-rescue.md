# coordinate-phase-rescue.md — coordinator rescue reference

Symptom-indexed detail for the `/coordinate-phase` loop. The command
body (`.claude/commands/coordinate-phase.md`) carries the
**every-iteration core** — the loop steps, the verification scrutiny
that fires on each commit, the fixed dispatch prompt. **This file
carries the rare / explicit-trigger patterns** it points at: consult the
matching § when its trigger fires. (Same model as `../TACTICS-QUIRKS.md`
for Lean build failures — a reference read on demand, not session-start
orientation.) Row numbers cite `model-experiment.md`.

## Index (symptom → §)

- Wrong branch / author / co-author trailer on a landed commit → §1
- Return shows **neither** LANDED nor BLOCKED; named/async dispatch idles instead of returning → §2
- Dispatch **killed** by a session/usage limit, **or user-interrupted** mid-task → §3
- Plan-label deviation (destructive→additive, slice re-size) → §4
- BLOCKED return — which resolutions stay in-workflow → §5
- Non-build dispatch shapes (cleanup round; coordinator-authored; source-verification recon) → §6
- Subagent wedged for hours on a proof timeout (elaboration wall) → §7

## §1 — Mechanical fixups (a fixup, never a stop)

Pre-authorizable at session start. Apply, then log the sha.

- **Wrong branch** → `git checkout master && git merge --ff-only
  <branch> && git branch -d <branch>`.
- **Wrong author** → `git commit --amend --author='Bryan Gin-ge Chen
  <bryangingechen@gmail.com>'`.
- **Wrong co-author trailer** — a subagent naming a model it didn't run
  on (rows 21/26, both times the dominant trailer from recent `git log`
  instead of the dispatched model), or the model-id form
  (`claude-sonnet-4-6`) instead of display form (`Claude Sonnet 4.6`;
  sonnet does this persistently even with the CLAUDE.md rule) → amend the
  trailer before logging the sha. Attribution-hygiene (protocol); **not**
  counted against the outcome grade — track recurrences in Notes.
- **Spurious `Claude-Session:` trailer** — a subagent appends a
  `Claude-Session: https://claude.ai/code/session_…` line the project
  convention omits (every prior commit has *only* `Co-Authored-By:`; the
  harness's default-commit-trailer instruction leaks through, recurred 3×
  in session #12 and ~half the build dispatches in session #13). **Now
  auto-stripped pre-commit by the `.githooks/commit-msg` hook** (added
  2026-06-19; fires for main-session *and* subagent commits, no amend / no
  SHA churn). Activate once per clone: `git config core.hooksPath .githooks`
  (repo-local config, not committed — a fresh clone must re-set it; the hook
  script itself is version-controlled). **Manual-strip fallback** (when the
  hook isn't active — fresh clone before setup): `git log -1 --format='%B'
  HEAD | grep -v '^Claude-Session:' | git -c user.name='Bryan Gin-ge Chen'
  -c user.email=bryangingechen@gmail.com commit --amend -F - --author='Bryan
  Gin-ge Chen <bryangingechen@gmail.com>'` before logging the sha (fold any
  same-commit note-trim into the same amend). Buried earlier commits with
  the trailer are cleanable in one filter at push, not worth a mid-loop
  rebase — flag them.

## §2 — Return shows neither LANDED nor BLOCKED

Usually the subagent parked on a background gate with
finished-but-uncommitted work (twice on 22h's G5). **Don't
blind-redispatch** (a fresh "continue" agent re-reads everything and may
park the same way): verify the tree diff against the hand-off yourself,
run the gates, commit with the project identity.

**Named/async dispatches surface as an idle notification, not a tool
result** (this session, rows 153–158: every named Agent dispatch emitted
`{type: idle_notification, idleReason: available}` instead of returning
`LANDED <sha>`/cost). Treat that notification as "the agent finished its
turn but delivered no return" — verify via git as above. Two
consequences for the loop: **(a) cost figures (tokens / tool-uses) are
unavailable** — wall time from commit timestamps is the only metric; to
get a synchronous `LANDED`+cost return, dispatch the agent **un-named**
(naming it routes it to the async mailbox). **(b) A running named agent
does not read your `SendMessage` until it is interrupted** — to stop or
steer one, have the *user* interrupt it so the queued message lands
(rows 157–158: the stop and the WIP-recovery messages took effect only
on the user's interrupt). Reserve named dispatches for boundary-pair
duplicates / cases that need an addressable resume.

## §3 — Killed dispatch (session/usage limit) or user-interrupt → resume-first

A kill returns neither LANDED nor BLOCKED (the return is the limit error
itself); a **user interrupt** mid-dispatch is the same shape (the return is
`[Request interrupted by user…]`). Check `git status` for stranded work, log
it as outcome `killed` (the wasted cost), then:

> **Interrupt vs. `salvaged`.** A user interrupt that catches **complete,
> gate-passing** work → `salvaged` (verify + finalize the commit yourself, no
> resume — protocol *Outcome*). An interrupt that catches **incomplete** work
> (a half-built leaf) is `killed`-shaped → resume-first below.

1. **First try resuming the same agent** — `SendMessage` to the
   `agentId`, naming where it died and what remains. Available under agent
   teams (`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS`); the harness resumes from
   the transcript, full context + read phase intact (rows 64→65: re-emitted
   an unwritten design block with zero re-reading; **row 220**: a
   user-interrupted leaf resumed and completed cleanly — confirmed working
   in this environment, contra the row-202 "unavailable" data point). Log the
   resume as its own row, Mode `resume`.
   - **No agentId in the return?** A user interrupt / cancellation returns an
     *error*, not the Agent tool's normal result, so you won't have the
     `agentId`. Recover it from the **local subagent logs**: the most-recently-
     modified `…/projects/<proj-slug>/<session>/subagents/agent-<id>.jsonl`
     (+ `.meta.json`, which confirms the dispatch `description`); the `.jsonl`
     tail shows where it died. (Reference the dir generically in any commit —
     never paste the machine-absolute path, per top-level CLAUDE.md.)
   - **Re-apply any fragment you reverted.** If you reverted the agent's
     uncommitted edit while cleaning the tree during the interrupt, **re-apply
     it before resuming** — the resumed agent's context believes its edit
     landed (and may have built it), so a tree missing that decl makes its next
     build fail (row 220: re-applied a built-but-uncommitted brick, then
     resumed). Don't tell the agent about the revert/re-apply; just restore the
     tree to match its context.
   - If the tree was genuinely clean at the kill, say so explicitly so the
     agent re-emits rather than assumes its edits survived.
2. **Only if resume is unavailable or fails, relaunch fresh** — salvage
   the dead agent's read map (its transcript, at the path in the Agent
   tool result / task notification, e.g. `…/tasks/<agentId>.output`;
   extract the tool-call file paths) into the relaunch prompt. A coherent
   stranded *edit* can be left in tree for the relaunch to
   review-and-extend rather than reverted (rows 28→29; 54→55, where the
   relaunch kept and completed the predecessor's partial blueprint edit).

## §4 — Plan-label deviations (destructive→additive, slice re-size)

A normal, usually-correct self-redirect in migration phases — four
consecutive "destructive" slices rightly landed additively in one run
(enharmonic Phase 17). Verify the stated reason against the source once
(the first occurrence sets the pattern), confirm the deferred obligation
(legacy retirement, follow-up sub-slice) is recorded in the phase notes
with a slice pointer, and **fix the drift at the authoritative plan doc
when pausing** — a plan doc that says "destructive" while reality went
additive is a trap for the next coordinator.

## §5 — BLOCKED resolution (in-workflow vs stop)

Stop on a BLOCKED **without** a clear within-workflow resolution. The
in-workflow exception: a **sizing-shaped BLOCKED** (deliverable judged
un-carvable, tree untouched, usually because the design doc pins no
concrete signatures below the named slot) is the step-1 design-pass
trigger — dispatch a decomposition design-pass at the design-settle rung
rather than re-dispatching the build one rung up (rows 27→29: the §1.51
seven-leaf cut un-blocked what brute escalation would have re-hit).

**Whatever the resolution, salvage the return first.** A BLOCKED return
often carries the dead attempt's route findings (verified tactic steps,
confirmed-nonexistent APIs); copy them into the phase note's hand-off in
the same stop/escalation commit — stranded in the agent return they are
invisible to the next session (row 72: a reverted L1g attempt left a
5-step verified route map that survived only because the coordinator
moved it into the hand-off).

## §6 — Non-build dispatch shapes

- **Cleanup rounds** (per `../CLEANUP.md`): a scoped no-git editor —
  "Edit ONLY <file>. Touch no other file. Do NOT run git / commit /
  `inv` / `verify.sh` / `lake`" — with the coordinator reviewing and
  committing the result itself.
- **No dispatch at all**: decision records, adjudication outcomes, and
  postmortem syntheses born in the coordinator's own conversation with
  the user are coordinator-authored commits — a subagent would have to
  reconstruct that context from a prompt, lossily. Same per-commit
  checklists, project author identity, and the coordinator's *actual*
  model in the trailer (the §1.55 + postmortem commits).
- **Source-verification recon** (read-only, no commit): when the open question is a
  route's *faithfulness to the source* — typically a design-pass verdict that
  re-routes against KT's construction, which the design pass cannot self-certify —
  dispatch a read-only agent to read the load-bearing primary-source equations (the
  `.refs/` PDF) and return a verdict, **framed adversarially** ("try to *refute* the
  proposed reading; a refutation is more valuable than a confirmation"). It leaves
  the tree untouched (a verify, not a build); the coordinator acts on the verdict and
  locks the route. Used 2026-06-18 (row 242) to confirm route β's single-`v₁`-base
  reading against KT eqs. (6.46)–(6.67) and **refute** the per-`i`-splits alternative
  *before* committing the build — the highest-confidence way to settle a
  "which route is KT-faithful" fork.

## §7 — Subagent wedged for hours on a proof timeout (elaboration wall)

A dispatch running far past the norm on a proof that won't compile (rows
157–158: ~2 h vs the ~15–25 min L8 norm) is usually an **elaboration-cost
wall**, distinct from proof-discovery: the proof is *logically complete*
(every goal closes — the agent can confirm via `lean_goal`) but the term
is too heavy to elaborate within the heartbeat budget. The cost-outlier
is itself the intervention trigger — don't wait it out (the rows-115/118
degradation-signal lesson); surface to the user early.

Procedure:
1. **Interrupt and recover the WIP before reverting.** Interrupting needs
   the user (per §2 — a running named agent won't read messages
   otherwise). Have the agent dump its in-progress proof to
   `/tmp/<name>-wip.lean` (NOT the repo — a replacement agent may already
   be editing it) and report a diagnostic: which decl/step, the verbatim
   timeout, and discovery-vs-elaboration read. The recovered proof is
   both the diagnostic *and* a head-start for the retry.
2. **Don't just escalate to a stronger model or crank `maxHeartbeats`.**
   A heartbeat wall is largely model-independent — a bigger model writes
   a similarly-heavy term. (Sonnet's L8c-2 attempt extracted one helper,
   then tried 4M→8M heartbeats, and still wedged.)
3. **Escalate one rung up with a decompose-don't-crank mandate, seeded
   with the recovered WIP.** The fix is to *break the elaboration*:
   extract heavy steps as standalone helper lemmas (TACTICS-QUIRKS §38),
   AND — the sharper lesson — **hunt the dominant `whnf` term, which is
   often a manual `∃`-witness / structure assembly over a heavy motive**,
   and route it through a landed keystone instead. (22k L8c-2: the manual
   `⟨Q,…⟩` assembly of `HasGenericFullRankRealization` was the dominant
   cost — it failed even at 6M heartbeats; routing the final step through
   the keystone `hasGenericFullRankRealization_of_rigidOn_ofNormals` +
   four extracted helpers fit at 800000.)
