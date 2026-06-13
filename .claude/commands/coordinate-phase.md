Coordinate Phase $ARGUMENTS. Dispatch subagents one at a time; each one
does the next concrete commit per the existing workflow, then sanity-
check and dispatch the next. Stop when the phase closes or something
looks off.

Setup: follow CLAUDE.md reading order (CLAUDE.md, ROADMAP.md,
notes/Phase$ARGUMENTS.md). Confirm `git status` is clean and the
leftmost active phase file builds green (per *Starting a Lean-touching
session* in CombinatorialRigidity/CLAUDE.md). While the model-experiment
is running, also run the protocol's **session-start availability check**
(`notes/model-experiment-protocol.md`, *Model assignment map*): determine
which rungs the Agent tool's `model` parameter can reach this session and
record the available set + any substitution in the repo-local config
before the first dispatch. Run the loop in the
foreground of this session only — never backgrounded or forked: two
instances sharing one working tree have ended with one committing the
other's half-validated uncommitted work.

Before the first dispatch, ask the user once whether this run modifies
these instructions — in practice users customize at session start,
typically lifting the 10-run cap and pre-authorizing the step-4
mechanical fixups.

Loop:

1. Note HEAD and re-read notes/Phase$ARGUMENTS.md "Hand-off / next
   phase" — that's what the next commit should accomplish. If that
   step is **research-shaped** — the hand-off flags recon-before-build,
   OR 2+ consecutive leaf commits have fed a hard core that is itself
   not yet built, OR 3+ consecutive commits are thin wrappers aliasing
   existing facts — the next commit is a **recon / design-pass**, not a
   build: dispatch a read-only Plan-agent recon, or a docs/blueprint
   design-pass commit that decomposes the core into buildable leaves
   with exact signatures. Recon is this workflow's highest-leverage
   move; trigger it **early**, before the next leaf (22g burned ~4
   leaf commits on an undischargeable core; 22h's §1.50 recon, fired
   at exactly the 2-leaf trigger, re-routed the whole discharge and
   surfaced GAP 6 before anything was built on the dead route).
2. **Model-tier experiment (only while `notes/model-experiment.md`
   says Status: running):** rate S/P/B and pick the rung per
   `notes/model-experiment-protocol.md` (the single source of truth —
   don't duplicate it here); pass it as the Agent tool's `model`
   parameter, prompt held fixed. Honor any **standing rung override**
   in the log's repo-local config. Log rows follow the protocol's
   *Per-dispatch record* rules (write-after-verification timing,
   tail-only edit matching). If Status says concluded, follow the
   promoted guideline instead. **Run boundary pairs when due** — when
   the log's findings name an open pair need and the profile fits,
   launch one without asking; the protocol's worktree procedure
   (cache-get caveat, parallel dispatch with the sequential fallback,
   the harvest-before-discard option, the fixed duplicate
   prologue) already neutralizes the OOM/cost concerns that have made
   coordinators hesitate (rows 70–71 ran clean under it). Pin a
   free-choice hand-off to one slice first so both members run the
   same task.
3. Dispatch Agent (subagent_type: general-purpose) with exactly the
   prompt below. Two exceptions adapt it: a **recon / design-pass**
   step names that deliverable in the first line; a **phase-open /
   phase-close** step gets a short prologue stating what is
   sanctioned (e.g. a user-adjudicated close shape — "closing now is
   sanctioned; do not re-litigate it") and what is out of scope
   ("the successor phase is NOT opened by this commit") — without it
   the agent must re-derive both, and either re-asking or
   over-reaching is bad (L5e′, 2026-06-11):

       Continue Phase $ARGUMENTS — do the next concrete commit per
       notes/Phase$ARGUMENTS.md "Hand-off / next phase", then stop.
       Commit directly on the current `master` branch — do not
       create a new branch — and match the git author identity of
       the existing commits. Follow the project's reading order,
       friction review, and pre-commit checklist (CLAUDE.md and its
       subdirectory auto-loads carry the discipline). Scope to fit
       one sitting: land the smallest complete deliverable that
       moves the hand-off forward — if the named deliverable won't
       fit, shrink the deliverable (a smaller complete lemma /
       sub-step), never the completeness (no sorry/admit
       placeholders, no warning-carrying commits, no deferred-work
       stubs). If your context gets compacted/summarized mid-task,
       or you notice earlier session context has been lost, do not
       push on degraded: bring the tree to a clean state (commit
       only what is complete and gate-verified, revert the rest)
       and return BLOCKED with a progress summary. Run your
       build/lint gates to completion and commit before ending your
       turn — never end the turn with finished-but-uncommitted work
       while a background gate is still running. Do all the work
       yourself, in this conversation — never launch subagents (the
       Agent tool; a hook also blocks it): if the task won't fit,
       shrink the deliverable or return BLOCKED, and let the
       coordinator decompose. Do not edit
       notes/model-experiment.md — the dispatch log is
       coordinator-owned. After committing,
       return a final message of exactly the form:
         LANDED <sha>: <one-line summary>
       or
         BLOCKED: <one-paragraph reason and what would unblock>.

4. Verify the return:
   - **Mechanics:** `git log --oneline -3`, `git show --stat HEAD`,
     `git branch --show-current`. HEAD advanced past the noted sha;
     still on `master`; author bryangingechen@gmail.com; diff matches
     what the hand-off pointed at. A docs/blueprint-only commit
     (recon, design pass, decomposition, re-scope) is normal in a
     research-shaped phase — judge against the hand-off, not against
     "must touch Lean".
   - **"Gates green" is an attestation, not evidence.** The step-5
     gate always runs; for below-top-rung dispatches also re-run
     `lake lint` and read the **full diff** (protocol rule); for
     haiku, re-run every gate the return names (a haiku once
     fabricated all three gates green — enharmonic 2026-06-10,
     model-experiment row 12).
   - **Sorry-grep the touched `.lean` files after every
     below-top-rung dispatch**, regardless of what the return says —
     a LANDED return can omit a `sorry` that the commit message
     discloses (enharmonic row 13: the commit message was honest,
     the return was not). Read the commit message body, not just the
     summary line. The converse also happens — **judge completeness
     from the diff, not the prose**: a post-compaction commit message
     can mis-describe *finished* work as partial (row 74's "partial
     stub, pending L4" over a complete proof), and the same false
     belief can propagate into the notes and the blueprint pin (the
     "stub" decl was left off its node's `\lean` list) — when message
     and diff disagree, trust the diff and repair the prose. A landed sorry is a failed verification →
     escalation per the protocol: re-dispatch one rung up with the
     route named in the prompt, keep the landed commit, close the
     sorry in the follow-up (enharmonic rows 7–8 and 13–14
     precedent).
   - **Shape check:** when the hand-off pins the deliverable to a
     design verdict (a §1.NN pointer or named verdict), diff the
     landed statement against that section — motive strength,
     transport direction, consumed-vs-carried hypotheses.
     Mechanically clean commits landed design-excluded shapes twice
     in one 22h session (rows 11, 14); only the section re-read
     caught them. A shape deviation = corrective dispatch one rung
     up with a tailored prompt naming the verdict, never a
     discharge-on-top. Diff against the **pre-commit** text of the
     checklist item / design section (`git show <noted-sha>:notes/…`),
     not the post-commit one — the builder edits the notes too, and a
     partially-delivered item can be rewritten to match what landed,
     silently dropping pinned sub-clauses (row 46: a checklist item's
     wiring + blueprint-node sub-clauses vanished in the same commit
     that marked it Done). The same check covers **prose routes**: a
     commit that authors red-node / deferred-route prose gets that
     route diffed against the canonical design § exactly like a Lean
     statement — a mechanically clean TeX commit described the 6.5
     arm via the wrong argument (contraction-splice vs the §1.54(a3)
     vertex-removal; row 50), and only the design-§ re-read caught a
     red node mis-describing its deferred proof (the rot the
     red-node consistency gate would otherwise meet phases later).
   - **Mechanical fixups, not stops:** wrong branch → `git checkout
     master && git merge --ff-only <branch> && git branch -d
     <branch>`; wrong author → `git commit --amend --author=…`;
     wrong co-author trailer — a subagent naming a model it didn't
     run on (twice in one 22h session, rows 21/26, both times the
     dominant trailer from recent `git log` instead of the dispatched
     model), or the model name in model-id form (`claude-sonnet-4-6`)
     instead of display form (`Claude Sonnet 4.6`; sonnet does this
     persistently even with the rule in CLAUDE.md) → amend the
     trailer before logging the sha (the protocol's
     attribution-hygiene rule; not counted against the outcome
     grade). A return with **neither LANDED nor BLOCKED** usually
     means the subagent parked on a background gate with
     finished-but-uncommitted work (twice on 22h's G5) — don't
     blind-redispatch (a fresh "continue" agent re-reads everything
     and may park the same way); verify the tree diff against the
     hand-off yourself, run the gates, commit with the project
     identity. A dispatch **killed by a session/usage limit** also
     returns neither (the return is the limit error itself): check
     `git status` for stranded work, log it as outcome `killed`,
     then **first try resuming the same agent** — `SendMessage` to
     the `agentId` from the Agent tool result, with a short message
     naming where it died and what remains (available when agent
     teams are enabled, `CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS`; the
     harness resumes it from its transcript, full context + read
     phase intact — rows 64→65, where the resume re-emitted an
     unwritten design block from context with zero re-reading; if
     the tree was clean at the kill, say so explicitly so the agent
     re-emits rather than assumes its edits survived). Log the
     resume as its own row, Mode `resume`. Only if resume is
     unavailable or fails, relaunch fresh — salvaging the dead
     agent's read map (its transcript, at the path named in the
     Agent tool result / task notification — e.g.
     `…/tasks/<agentId>.output`; extract the tool-call file paths)
     into the relaunch prompt recovers most of the lost reading
     phase, and a coherent stranded *edit* can be left in tree for
     the relaunch to review-and-extend rather than reverted (rows
     28→29; rows 54→55, where the relaunch kept and completed the
     predecessor's partial blueprint edit).
   - **Recon verdicts get reasoning scrutiny, not just commit
     mechanics** — a mechanically clean recon can still be wrong, and
     building on it re-incurs the churn it was meant to end.
     Scrutinize hardest a recon that **dissolves or re-routes** a
     gap: confirm every *other* carried obligation still closes under
     the new route (a re-route can orphan a hypothesis the discarded
     route silently supplied — 22g §1.46 orphaned `hgab`). A recon
     that surfaces a **new gap** is usually cheaply verifiable —
     check it against the primary source (`.refs/` PDFs, REFS.md)
     and/or a one-line Lean witness (`lean_run_code`) *before*
     re-planning on it (22g GAPs 4/5 settled in minutes; 22h GAP 6
     confirmed against KT p. 684 + the Lean motive in one sitting).
     Build-dispatched
     agents sometimes self-redirect to a recon — often rightly; same
     scrutiny, especially when one overturns a prior finding. A
     **route claim recorded in the hand-off by a build agent** (a
     "the next step must …" finding it didn't itself build) is a
     recon verdict in disguise: verify it before dispatching a build
     on it, and check it against what the design doc *actually
     proposed* — a true premise can carry a wrong conclusion that
     attacks a configuration nobody planned (22h rows 38–39: "W9
     must re-derive W7's chain" was overturned by the §1.52 design
     pass; the design's own `Gv`-slot made W9 a 3-leaf
     instantiation). When the canonical design doc itself defers the
     shapes ("pin at the X design moment"), the design moment IS the
     next dispatch — a design-settle pass, not a build.
   - **Plan-label deviations (destructive→additive, slice re-size)
     are a normal, usually-correct self-redirect in migration
     phases** — four consecutive "destructive" slices rightly landed
     additively in one run (enharmonic Phase 17). Verify the stated
     reason against the source once (the first occurrence sets the
     pattern), confirm the deferred obligation (legacy retirement,
     follow-up sub-slice) is recorded in the phase notes with a
     slice pointer, and fix the drift at the authoritative plan doc
     when pausing — a plan doc that says "destructive" while reality
     went additive is a trap for the next coordinator.
   - Re-read the updated "Hand-off / next phase".
5. If the commit changed any `.lean` file: `touch` the changed file
   (cached modules don't re-emit warnings), then `lake build
   <leftmost active module> 2>&1 | grep -E 'warning:|error:'` —
   **warning-clean, not merely green** (a sorry'd skeleton once rode
   a green-but-warning build onto master, row 17). Red or
   warning-bearing → stop and surface. Skip for docs-only commits.
6. One sentence to the user: clean handoff, or the specific concern.
   Surface **phase-boundary decisions** — early close, sub-phase
   split, a green-modulo-X change to what "phase close" means — with
   a concrete commit-count estimate rather than deciding unilaterally.
7. Stop and surface on any of:
   - ROADMAP Status shows Phase $ARGUMENTS ✓ (the subagent ran the
     phase-close checklist). After a user-approved mid-session
     close-and-split, confirm with the user before resuming the loop
     on the successor phase.
   - BLOCKED return; or HEAD didn't advance. Exception — a
     **sizing-shaped BLOCKED** (deliverable judged un-carvable, tree
     untouched, usually because the design doc pins no concrete
     signatures below the named slot) is the step-1 design-pass
     trigger, resolvable in-session: dispatch a decomposition
     design-pass at the design-settle rung rather than re-dispatching
     the build one rung up (rows 27→29: the §1.51 seven-leaf cut
     un-blocked what brute escalation would have re-hit). Stop on a
     BLOCKED without a clear within-workflow resolution. **Whatever
     the resolution, salvage the return first:** a BLOCKED return
     often carries the dead attempt's route findings (verified
     tactic steps, confirmed-nonexistent APIs); copy them into the
     phase note's hand-off in the same stop/escalation commit —
     stranded in the agent return they are invisible to the next
     session (row 72: a reverted L1g attempt left a 5-step verified
     route map that only survived because the coordinator moved it
     into the hand-off).
   - A recon flags a decision for **user adjudication** (e.g. a
     carried hypothesis or motive change) — present the options with
     estimates; don't pick unilaterally.
   - Suspicious diff: unexpectedly large, unrelated files, or the
     step-5 gate red.
   - The agreed run cap (default 10) reached since the user last
     checked in.

Don't pad the **routine build** prompt or pre-load files — the
CLAUDE.md auto-loads carry the discipline, and duplication invites
drift. (The scope-to-fit / compaction-bailout clause *is* part of the
fixed prompt: prompt-level discipline doesn't survive compaction —
row 17's 2.7 h dispatch — so the clause shapes scope while context is
intact and the `block-sorry-commit.sh` hook backstops after it
degrades. Post-amendment evidence it works: rows 18–19 self-shrank to
complete sub-lemmas.) A **recon / design-pass** dispatch is the
exception: give it a tailored prompt naming what to recon, the
coordinator's verified findings motivating it, and the deliverable
(a design-doc entry + re-pointed hand-off).

For **cleanup rounds** (per CLEANUP.md) a third dispatch shape works
well: a scoped no-git editor — "Edit ONLY <file>. Touch no other
file. Do NOT run git / commit / `inv` / `verify.sh` / `lake`" — with
the coordinator reviewing and committing the result itself.

A fourth shape is **no dispatch at all**: decision records,
adjudication outcomes, and postmortem syntheses born in the
coordinator's own conversation with the user are coordinator-authored
commits — a subagent would have to reconstruct that context from a
prompt, lossily. Same per-commit checklists, project author identity,
and the coordinator's *actual* model in the trailer (the §1.55 +
postmortem commits, 2026-06-11).
