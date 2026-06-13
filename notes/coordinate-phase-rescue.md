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
- Return shows **neither** LANDED nor BLOCKED → §2
- Dispatch **killed** by a session/usage limit → §3
- Plan-label deviation (destructive→additive, slice re-size) → §4
- BLOCKED return — which resolutions stay in-workflow → §5
- Non-build dispatch shapes (cleanup round; coordinator-authored) → §6

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

## §2 — Return shows neither LANDED nor BLOCKED

Usually the subagent parked on a background gate with
finished-but-uncommitted work (twice on 22h's G5). **Don't
blind-redispatch** (a fresh "continue" agent re-reads everything and may
park the same way): verify the tree diff against the hand-off yourself,
run the gates, commit with the project identity.

## §3 — Killed dispatch (session/usage limit) → resume-first

A kill also returns neither LANDED nor BLOCKED (the return is the limit
error itself). Check `git status` for stranded work, log it as outcome
`killed` (the wasted cost), then:

1. **First try resuming the same agent** — `SendMessage` to the
   `agentId` from the Agent tool result, naming where it died and what
   remains. Available under agent teams
   (`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS`); the harness resumes from the
   transcript, full context + read phase intact (rows 64→65: the resume
   re-emitted an unwritten design block from context with zero
   re-reading). If the tree was clean at the kill, say so explicitly so
   the agent re-emits rather than assumes its edits survived. Log the
   resume as its own row, Mode `resume`.
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
