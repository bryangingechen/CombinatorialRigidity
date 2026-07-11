# phase-builder core discipline

This is the **shared core** for the `phase-builder` agent family
(`.claude/agents/phase-builder*.md` — the rung-pinned variants and the
unpinned base). Those definitions are thin: role, return contract, and
a pointer here. This file carries the loop discipline they share; edit
it once, and every variant follows. A dispatched agent reads this file
as its FIRST action and follows it as if it were part of its system
prompt.

Discipline (the project's CLAUDE.md and its subdirectory auto-loads
carry the full detail — follow the reading order, friction review, and
pre-commit checklists; this file pins the loop contract):

- **Commit directly on the current default branch** — do not create a
  new branch — and match the git author identity of the project's
  existing commits. (Your `Co-Authored-By:` trailer name is pinned in
  your agent definition; if your own environment block identifies a
  different model, your environment wins — use its name and flag the
  mismatch in your return.)
- **Scope to fit one sitting.** Land the smallest complete deliverable
  that moves the hand-off forward — if the named deliverable won't
  fit, shrink the deliverable (a smaller complete lemma / sub-step),
  never the completeness: no sorry/admit placeholders, no
  warning-carrying commits, no deferred-work stubs.
- **Compaction bailout.** If your context gets compacted/summarized
  mid-task, or you notice earlier session context has been lost, do
  not push on degraded: bring the tree to a clean state (commit only
  what is complete and gate-verified, revert the rest) and return
  BLOCKED with a progress summary.
- **Foreground gates, then commit, then stop.** Run your build/lint
  gates in the FOREGROUND (blocking) — never launch `lake build` /
  `lake lint` as a background task, and never end your turn while any
  command you started is still running: an ended turn strands the
  work uncommitted. If a long gate (e.g. the blueprint `verify.sh`)
  is still running as you approach the end of your turn, wait for it —
  do not end the turn early, and do not pre-claim its result in the
  notes (attestation-before-evidence is the same offense class as a
  fabricated gate claim). Attest gates only from the final run's
  actual output — a warning-bearing build is not clean; paste real
  output, not a summary.
- **Before committing, re-read the pinned checklist / design section
  VERBATIM** and confirm every pinned sub-clause is either delivered
  in this commit or explicitly re-flagged in the hand-off — never
  rewrite a checklist or hand-off item to match what landed.
- **If elaboration wedges** (~15+ minutes without progress on one
  goal), stop and return BLOCKED with the goal state rather than
  pushing through (don't crank `maxHeartbeats`; the fix is
  decomposition, which the coordinator will re-dispatch).
- **If anything unexpected appears** — a surprising build failure, a
  missing declaration, a diff touching files the hand-off didn't name
  — prefer BLOCKED over improvising a workaround. Never modify the
  toolchain, lakefile, or manifest; never run `lake update`.
- **Do all the work yourself, in this conversation** — never launch
  subagents (the Agent tool; a hook also blocks it). If the task
  won't fit, shrink the deliverable or return BLOCKED and let the
  coordinator decompose.
- **Do not edit the coordinator-owned dispatch log**
  (`notes/dispatch-log.md`).
