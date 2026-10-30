Coordinate tracks $ARGUMENTS (a research sub-phase, e.g. `42d`). One central
session runs the sub-phase's parallel tracks: it dispatches each track's next
session as a background subagent in its own isolated git worktree, merges what
lands, runs the checks, and brings every decision to the PI. **You do no
mathematics and no writing for a track yourself.** `HARNESS.md` binds every
track; `CLAUDE.md` binds your commits.

Why so thin: the retired `/coordinate-research` (`notes/harness/archive/`)
spent over half its tool calls on process. The hub dispatches, merges, checks
and relays; everything else belongs to a track or to the PI.

**Setup, once.**
1. Read `notes/Phase$ARGUMENTS.md`: its *Tracks* table is the registry (track,
   kind, home, agent, status). Read nothing else up front: not the briefs, not
   the state files' bodies.
2. `git status` clean on `master`. `git worktree list`: a leftover
   `.claude/worktrees/agent-*` from an earlier session is merged by *Merge* if
   its branch has commits not on `master`, else removed with its branch.
3. For each attack-kind track: `python3 notes/harness/check.py --state
   notes/attacks/<name>/state.md` (absent before session 1), and the state
   file's first line, which counts its sessions and reviews. A brief headed
   **DRAFT** runs only after the PI has read it.
4. Ask the PI once, and wait for the answer: which tracks run, and the cap on
   track sessions this sitting (default: one round of every ready track).

**Dispatch.** All ready tracks in one message, one background `Agent` call
each, every one except a *lean* commit with `isolation: "worktree"`
(`.claude/settings.json` sets `worktree.baseRef: head`, so the worktree starts
at local `HEAD`). By kind:
- *attack* (a lemma, or a question run on the attack machinery): agent
  `attack-opus`; prompt `Attack <name>, dispatched by /coordinate-tracks.`
  plus the preamble below.
- *write-up* (red blueprint nodes): agent `writeup-opus`; prompt names the
  slice from the phase note's write-up checklist, plus the preamble.
- *lean* (one Lean commit the phase note specifies): agent
  `phase-builder-opus`, **without** isolation (builds need the main
  checkout's `.lake`), prompt `Land Phase $ARGUMENTS's next Lean commit as
  notes/Phase$ARGUMENTS.md specifies it, then stop.` plus `/coordinate-phase`
  step 3's F6 reminder line, and no preamble. At most one in flight. While it
  runs you merge and commit nothing (it shares your working tree), and no
  other dispatch may edit the blueprint chapter it edits.
- *review*, instead of a track's next session when one is due (`HARNESS.md`
  *Attack track*: every three sessions, or a proposed route change; or the
  state's signals show a stuck route): agent `general-purpose` with `model:
  opus`; prompt `Follow .claude/commands/review-attack.md for <name>; your
  report goes to the coordinator, who relays it to the PI; commit nothing.`
  plus the preamble.

The preamble, verbatim in every dispatch:
> You run in your own git worktree, dispatched by the central session
> (`/coordinate-tracks`). First run `git merge --ff-only master`. Do not run
> `lake build`, a Lean server or `blueprint/verify.sh` here (no `.lake`, no
> blueprint venv; the machine takes one build at a time). Nested subagents are
> blocked (`block-nested-agent.sh`): run sweeps yourself, in the background,
> each writing to its own new output file. Commit on this worktree's branch
> only, with `git commit -F` from a heredoc; never touch `master` or another
> worktree; do not push. Write nothing outside your track's home: a line for
> `notes/harness/incidents.md` goes in your report, and the coordinator adds
> it. Your last
> message is your report to the coordinator: the commit sha, where the track
> stands, whether a review is due, and any question for the PI (verbatim,
> with its options).

**Merge, on each completion notification.**
1. Read the report. A `BLOCKED: memory pressure` (or a dispatch the memory
   hook denied) stops the hub: tell the PI.
2. In the agent's worktree: `git rebase master` (`master` may have moved). A
   conflict: `git rebase --abort`, leave the worktree, tell the PI.
3. In the main checkout: `git merge --ff-only <branch>`, then
   `git worktree remove <path>` and `git branch -d <branch>`. A worktree with
   no commits was removed by the harness already.
4. Check: an attack, `python3 notes/harness/check.py --state <state.md>`; a
   write-up, `blueprint/lint.sh` then `blueprint/verify.sh`; a *lean* commit
   (no merge: it landed on `master`), the checks of `/coordinate-phase`
   *Verification tiers* at the top rung, and merges that waited on it now go
   ahead. A failure goes
   back to the track's next session as its first task, and to the PI.
5. If the track's status changed (held, review due, closed), edit its row
   (count-free, `HARNESS.md` *Attack track*) and commit that alone.
6. Re-dispatch the track if it is ready and the cap allows.

**The PI.** Bring each track's question to the PI as it arrives
(`AskUserQuestion`, the track's own options), and hold that track until the
answer. Record the answer verbatim where it binds: a ruling on a track in its
brief's header blockquote, dated, "on the PI's word"; a phase-level decision in
the design doc's decisions section. Route and brief changes are the PI's; the
mathematics is the track's; the hub decides neither.

**Stop** when every track is closed or held, at the cap, or before your
context runs long; never idle-poll, wait on notifications. On stopping: no
agent left running (wait for it, then merge); the phase note's *Current state*
and *Tracks* table current; one commit; the hand-off sentence (`CLAUDE.md`).
Ask the PI before pushing: a push to `master` publishes the site.

If this command or `HARNESS.md` cost the session time, add one line to
`notes/harness/incidents.md`; do not change the harness inside the session.
