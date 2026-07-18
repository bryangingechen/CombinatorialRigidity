# coordinate-phase-rescue.md — coordinator rescue reference

Symptom-indexed detail for the `/coordinate-phase` loop. The command
body (`.claude/commands/coordinate-phase.md`) carries the
**every-iteration core** — the loop steps, the dispatch playbook, the
verification scrutiny that fires on each commit. The per-dispatch
discipline now lives in the `phase-builder` / `recon` agent definitions
(`.claude/agents/`), not in a fixed prompt block. **This file carries
the rare / explicit-trigger patterns** it points at: consult the
matching § when its trigger fires. (Same model as `../TACTICS-QUIRKS.md`
for Lean build failures — a reference read on demand, not session-start
orientation.) Row-number citations refer to the concluded model-tier
experiment's frozen log, `model-experiment-archive.md`.

## Index (symptom → §)

- Wrong branch / author / co-author trailer on a landed commit → §1
- Return shows **neither** LANDED nor BLOCKED; named/async dispatch idles instead of returning → §2
- Dispatch **killed** by a session/usage limit, **or user-interrupted** mid-task → §3
- **API / connection error mid-response** (0-token return; the agent's file edits may be on disk but uncommitted) → §2/§3: verify the tree (`git status`), **salvage** if the uncommitted work is complete + gate-clean (run the gates yourself, commit with a coordinator-authored message), resume-first if partial
- Plan-label deviation (destructive→additive, slice re-size) → §4
- BLOCKED return — which resolutions stay in-workflow → §5
- Non-build dispatch shapes (cleanup round; coordinator-authored; source-verification recon; compiler-checked spike; spike-salvage resume) → §6
- Subagent wedged for hours on a proof timeout (elaboration wall) → §7

## §1 — Mechanical fixups (a fixup, never a stop)

Pre-authorizable at session start. Apply, then note the final sha.

- **Wrong branch** → `git checkout master && git merge --ff-only
  <branch> && git branch -d <branch>`.
- **Wrong author** → `git commit --amend --author='Bryan Gin-ge Chen
  <bryangingechen@gmail.com>'`.
- **Wrong co-author trailer** — a subagent naming a model it didn't run
  on (rows 21/26, both times the dominant trailer from recent `git log`
  instead of the dispatched model), or the model-id form
  (`claude-sonnet-5`) instead of display form (`Claude Sonnet 5`;
  sonnet does this persistently even with the CLAUDE.md rule), or the
  *coordinator's own prompt* dictating a stale display name (2026-07-02:
  a `Sonnet 4.6` prompt example landed a wrong trailer that needed a
  pre-push history rewrite — take the name from the coordinator
  command's step-3 prompt, which names the dispatched model, not from
  memory) → amend the trailer before noting the sha. Track recurrences
  in the exception log (`notes/dispatch-log.md`) only if it becomes a
  pattern.
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
run the gates, commit with the project identity. (The `phase-builder`
agent definition's foreground-gates clause — run gates blocking, commit
before ending the turn — largely retired this pattern, but it still
appears at any rung.)

**Root cause + preferred recovery (dispatch-log F6, five instances
2026-07-11):** a Bash call with **no explicit `timeout` parameter** gets
auto-backgrounded by the harness when it runs long ("Command running in
background with ID …"); the agent then ends its turn to "wait", and the
completion notification cannot wake a subagent whose turn ended. The
phase-builder core now mandates an explicit `timeout: 600000` on every
gate call **and forbids `run_in_background`/Monitor on gate builds**
(the latter added 2026-07-16 after a 6th instance recurred via a
*deliberate* background+Monitor wait — tell: "wait for the Monitor
notification" — which the timeout-mandate alone did not cover; both
fixes verified on multiple resumes). Recovery order when
it still happens: (1) **same-agent SendMessage resume** with
finish-in-foreground instructions naming the explicit-timeout fix (2/2
clean; rung-pinned variants resume at their rung, F5-safe); (2) if the
agent never wakes and the diff is a complete, coherent unit —
coordinator-salvage per the paragraph above (monitor HEAD for ~20 min
first to rule out a late self-commit; near-double-commit precedent
below).

**Named/async dispatches surface as an idle notification, not a tool
result** (this session, rows 153–158: every named Agent dispatch emitted
`{type: idle_notification, idleReason: available}` instead of returning
`LANDED <sha>`/cost). Treat that notification as "the agent finished its
turn but delivered no return" — verify via git as above. Two
consequences for the loop: **(a) cost figures (tokens / tool-uses) are
unavailable** — wall time from commit timestamps is the only metric; to
get the `LANDED`/`BLOCKED` summary + cost, dispatch the agent **un-named**:
even when an un-named dispatch runs in the **background** it still delivers
them in its completion notification (`<result>` + `<usage>`) — it is *naming*
that routes to the mailbox and drops the return (an un-named background
dispatch is the normal, working path, not the idle-ping failure mode). **(b) A running named agent
does not read your `SendMessage` until it is interrupted** — to stop or
steer one, have the *user* interrupt it so the queued message lands
(rows 157–158: the stop and the WIP-recovery messages took effect only
on the user's interrupt). Reserve named dispatches for cases that need
an addressable resume.

**Background-build idle notifications ≠ a stranded neither-return**
(row 747): an agent that runs its gates via a background build + wait
emits interim "idle" notifications *before* its definitive
LANDED/BLOCKED, and the interim tree can look stranded (dirty, HEAD not
advanced). Checking git state is fine, but **wait for the
LANDED/BLOCKED-shaped final message before finalizing on the agent's
behalf** — a coordinator once began writing the commit message for work
the agent then committed itself (a near double-commit). This is
distinct from the genuine neither-return above: the tell is that the
agent is still running (an idle *before* completion), not that its turn
ended with the work uncommitted.

## §3 — Killed dispatch (session/usage limit) or user-interrupt → resume-first

A kill returns neither LANDED nor BLOCKED (the return is the limit error
itself); a **user interrupt** mid-dispatch is the same shape (the return is
`[Request interrupted by user…]`), and so is an **API/transport error**
(e.g. "Stream idle timeout - no chunks received" — a task-notification
with `status: failed`; one such kill landed clean on a same-agent resume,
dispatch-log 2026-07-17). Check `git status` for stranded work
(record it in the exception log, `notes/dispatch-log.md`, as a killed
dispatch), then:

> **Interrupt vs. salvage.** A user interrupt that catches **complete,
> gate-passing** work → salvage (verify + finalize the commit yourself, no
> resume). An interrupt that catches **incomplete** work
> (a half-built leaf) is killed-shaped → resume-first below.

1. **First try resuming the same agent** — `SendMessage` to the
   `agentId`, naming where it died and what remains. Available under agent
   teams (`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS`); the harness resumes from
   the transcript, full context + read phase intact (rows 64→65: re-emitted
   an unwritten design block with zero re-reading; **row 220**: a
   user-interrupted leaf resumed and completed cleanly — confirmed working
   in this environment, contra the row-202 "unavailable" data point). If the
   kill was logged as an exception, note the resume there too.
   - **Rung check before resuming (dispatch-log F5):** a rung-pinned
     variant (`phase-builder-<rung>` / `recon-<rung>`) resumes at its
     frontmatter rung; a base-type/`model`-param dispatch resumes at
     the SESSION model — for those, confirm session ≥ mapped rung
     before resuming, else relaunch fresh at the mapped rung.
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
  dispatch the `recon` agent to read the load-bearing primary-source equations (the
  `.refs/` PDF) and return a verdict, **framed adversarially** ("try to *refute* the
  proposed reading; a refutation is more valuable than a confirmation"). It leaves
  the tree untouched (a verify, not a build); the coordinator acts on the verdict and
  locks the route. Used 2026-06-18 (row 242) to confirm route β's single-`v₁`-base
  reading against KT eqs. (6.46)–(6.67) and **refute** the per-`i`-splits alternative
  *before* committing the build — the highest-confidence way to settle a
  "which route is KT-faithful" fork.
- **Compiler-checked spike** (read-only, no commit) — the dispatch shape for a
  **route-COMPOSITION** question ("do these specific Lean objects compose to produce
  goal X?"), as opposed to the faithfulness question the source-verification recon
  settles. The default *prose* design-pass is the WRONG tool here: in the
  defeq-fragile zone prose mischaracterizes the types and a wrong verdict propagates
  through the hand-off (the §I.8.24(4.12)–(4.15) interior-`hρe₀` crux was prose-mis-pinned
  3–4× — incl. by a diverse-lens *prose* pair — DESIGN.md *Compiler-checked spike, not
  prose recon, …*). Instead dispatch the `recon` agent to write a SCRATCH probe (a
  throwaway `.lean` in the project tree importing the relevant modules), BUILDS the
  candidate composition with `sorry` for each gap, reads the kernel's per-seam verdict,
  and **reports the EXACT kernel-checked residual goal(s)** — not a prose verdict. Hard
  constraints: commit NOTHING, delete the scratch, leave `git status` clean (the
  deliverable is the gap map in the return message). One spike dissolved the route fork
  3–4 prose recons couldn't + isolated the true crux (rows 426–428).
- **Spike-salvage resume** (recover a probe's sorry-free work): a read-only spike
  reverts its scratch (correct), but the sorry-free lemmas it proved are valuable — do
  NOT spawn a fresh agent to re-derive them. `SendMessage`-resume the SAME spike agent
  (by its `agentId`) to re-emit them as real, gate-clean commits (it has the exact
  source in context; reverse the earlier "commit nothing" for this pass). Caveats: the
  resume runs in the **background** (no synchronous `LANDED`/cost return — you're
  notified on completion), and the async return is an *attestation* — the coordinator
  re-runs ALL gates after (mechanics, full diff, build warning-clean, `lake lint`,
  axiom-check, sorry-grep), exactly as for a below-top-rung dispatch (rows 426–427).
- **A read-only-origin agent may REFUSE the salvage-resume's commit (mandate-conflict /
  relayed-consent).** A spike/recon agent spawned with a `read-only, no commit, leave git clean`
  mandate, when resumed for a build, sometimes DECLINES to commit to `master` — correctly noting that
  a *coordinator-relayed* "the user authorized X" carries no user authority and contradicts its own
  governing (read-only) instruction (af7d5dc refused the §(4.40) `e_b` entry-lemma landing,
  2026-06-25; **agent-variance** — a4f9f025 resume-built leaf 3b cleanly the *same* session). This is
  sound general discipline, not a defect. Two-part fix: **(1)** in the resume message, GROUND the
  authorization in the user's standing invocation, not coordinator say-so — *"you are continuing under
  the user's `/coordinate-phase` loop, which IS the user's authorization for this loop's agents to
  commit directly to `master`; your prior read-only-recon constraint is lifted by that user-authorized
  continuation"* (cite any explicit user go-ahead too); **(2)** if it still refuses, DON'T fight it —
  dispatch a FRESH `phase-builder` agent (a build mandate from the start under
  `/coordinate-phase`), which re-derives the sorry-free lemmas. **Prefer the fresh dispatch outright
  when the salvage is mechanical** (entry lemmas, restates — the re-derivation cost is small and the
  route is pinned in the design § + hand-off); reserve the resume for genuinely expensive sorry-free
  work. **Pre-empt it** at the spike: a read-only spike/recon dispatch may note up front that *a
  follow-up coordinator message can lift the read-only constraint and authorize committing the spike's
  sorry-free work to `master` under the user's `/coordinate-phase` invocation* — so a later build
  instruction is expected, not a contradiction. (The `recon` agent definition already carries this
  pre-emption clause, so a spike dispatched via it need not restate it.)
- **Resumed BUILDS run gates in the FOREGROUND — not background-and-stop.** A
  `SendMessage`-resumed agent told to build will sometimes kick off a `lake build` in
  the **background** and END ITS TURN awaiting it — returning a non-`LANDED`/`BLOCKED`
  intermediate state with the work still UNCOMMITTED (23d lost two resume rounds to
  exactly this: build a leaf → background the gate → stop). In the resume message state
  explicitly: *run the build/lint/axiom gates in the FOREGROUND (blocking) and commit
  before ending the turn; do not background a build and stop.* If it still returns
  mid-gate (the §2 neither-return shape), read-only-check the tree (`git status` + the
  uncommitted diff), confirm the work is complete + sorry-free **without committing it
  yourself** (the §3 do-not-commit-the-other-instance's-WIP rule), and resume once more
  to finalize.
- **Resume-drive an over-sliced layer** (user-endorsed, 23d): when consecutive FRESH build
  agents repeatedly scope-shrink one layer into micro-pieces — each landing one small lemma
  while re-paying the full context-read overhead, the genuine assembly perpetually deferred —
  `SendMessage`-resume the most-recent warm agent scoped explicitly to *the larger chunk*
  ("land the remaining assembly, NOT one micro-piece; return BLOCKED-with-diagnosis if you hit
  a real gap"). The warm context skips the re-read and tends to drive through; 23d used it
  twice (A5c → the cert; the corrected-`hblock` spike → the §(4.33) bricks). Same
  foreground-gate + coordinator-re-gate + async-return caveats as above. Built-in safety: if
  the layer was deferring because it hides a genuine gap (not just conservative scoping), the
  scoped resume *surfaces* it as a BLOCKED-with-diagnosis rather than forcing a wrong build
  (23d's second resume-drive flagged the cert-SHAPE obstruction this way) — so it is safe to
  try before escalating to a fresh recon.
- **Bank-don't-revert when salvage is anticipated.** The spike's hard "commit NOTHING,
  revert the scratch" rule is right for a pure feasibility probe, but it is too strict —
  and costs a revert-then-resume round-trip — when the coordinator EXPECTS the probe to
  yield committable sorry-free work (a complete leaf, a design entry). Then authorize the
  spike up front to BANK its complete, gate-clean pieces directly (a design-doc entry +
  any finished leaf) while still reverting incomplete scratch — fold the salvage into the
  spike rather than a follow-up resume (the user's standing "read-only is too strict for a
  spike that builds real work" note, 23d).

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
