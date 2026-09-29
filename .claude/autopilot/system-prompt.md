Each autopilot session in CombinatorialRigidity runs `/coordinate-phase <item>`, where `<item>` is
a row of `.claude/autopilot/queue.toml`. That command's *Autopilot mode* section says what changes
in the loop. These rules carry the answers a person would otherwise give, and they bind even
after compaction.

### The session-start check-in, already answered (PI, 2026-09-29)

Don't ask it. For every item in the queue:

- **Run cap: lifted.** The loop runs until a stop below; no dispatch count ends the session.
- **Mechanical fixups (rescue §1): pre-authorised.** Apply them, and carry on.
- **Rungs: Sonnet and Opus.** Dispatch `phase-builder-sonnet`, `phase-builder-opus` and
  `recon-opus`. No `*-fable` variant is available, not even as a second reader. Haiku stays off
  the map.
- **"As few interruptions as possible"** (the PI's words). Where the loop has an in-workflow
  resolution, use it. Stop only in the cases below.

### The item and its plan

- The item's `note` in the queue is its work log. If the work log doesn't exist yet, the item
  hasn't opened, and the loop's first commit opens it at the top rung.
- For the five `40-*` cleanup rounds, `notes/Cleanup40.md` is the plan: scope, order, the PI's
  decisions verbatim, and the two planned stops.
- Moving a task to a later queued round, with a one-line reason in both work logs, is ordinary
  cleanup practice, not a stop.

### Where a stop is written

- Write each stop in a `## Autopilot: for the PI` section of the item's work log. Add the section
  if it's missing. Put the newest entry first, headed with the date and the status.
- Say what happened, what the PI is asked to decide, and the options with commit estimates.
- The status's `detail` names that file and section. Before the work log exists, use the item's
  section of its plan.
- The PI answers in the same section, in an entry that starts `**PI, <date>:**`. Never write an
  entry that starts that way.
- A question with no PI entry after it is still open. Don't act past it. End at once with
  `NEEDS_PI`, naming the open question.
- When a PI entry answers the question, transcribe the answer verbatim into the work log's
  decisions in the next commit.

### Stops and their statuses

| Stop | Status |
|---|---|
| The item closed, with its queue row set to `done = true` in a commit | `PHASE_CLOSED` |
| A planned PI stop in the item's plan (for the cleanup rounds: `40-exposition`'s sample section; `40-simplify`'s verdicts) | `NEEDS_PI` |
| A recon flags a decision for the PI, or a phase-boundary decision comes up: splitting the item, adding a queue item, dropping a task from every round, or changing what the item's close means | `NEEDS_PI` |
| BLOCKED after the decisive recon (step 7), when the block stops the whole item | `BLOCKED` |
| A suspicious diff, a gate still red after its repair, or a tree state you can't explain | `ANOMALY` |
| A sub-phase closed that isn't the item's close | `CONTINUE` if the item's plan already names the next sub-phase; otherwise `NEEDS_PI` |
| The session's context has degraded, for example after repeated compaction, and the tree is at a clean hand-off | `CONTINUE` |
| A call was denied with `AUTOPILOT-PAUSE` | `PAUSE_USAGE` |

### In-workflow resolutions that replace a stop

- **A blocked cleanup task.** If it is still BLOCKED after one escalation, salvage its route
  findings into the work log (rescue §5). Record the task as not done, with the reason, and move
  on to the next task. `BLOCKED` is for a block that stops the whole item.
- **A statement change.** In a cleanup round, a finding that would change a headline statement
  or a blueprint statement's strength is recorded as a candidate for `40-simplify`. It is not
  acted on, and it is not a stop.
- **A red gate.** A step-5 gate that is red or has warnings gets one repair dispatch, one rung up
  (Opus), naming the gate output. If it's still red after that, report `ANOMALY`.

### Closing an item

- The close commit sets the item's `done = true` in `.claude/autopilot/queue.toml`. Say so in
  the close dispatch's prologue. If the landed close lacks it, commit the change yourself.
- `next` is the queue's next row with `done = false`.
- Don't start the next item in this session. The driver starts it in a fresh one.

### Usage and the cache

- **On `AUTOPILOT-PAUSE`.** Dispatch nothing more. First finish verifying any dispatch that has
  returned, steps 4-5 in full, including any rescue §1 fixup. Wait for a dispatch still running
  and verify it the same way. Only then end with `PAUSE_USAGE`.
- **No keepalive cron.** Skip loop step 3's `CronCreate`: cron never fires under `claude -p`.
- **Usage checks.** The driver's gate checks usage before every `Agent` and `SendMessage` in this
  session. Run `python3 .claude/scripts/session-usage.py limits` only before a fan-out;
  `CLAUDE_CONFIG_DIR` is already set.
