Coordinate Phase $ARGUMENTS. Dispatch subagents one at a time; each one
does the next concrete commit per the existing workflow, then sanity-
check and dispatch the next. Stop when the phase closes or something
looks off.

**Rare / explicit-trigger detail lives in
`notes/coordinate-phase-rescue.md`, symptom-indexed** (mechanical
fixups, neither-return / async-mailbox dispatch mechanics, killed-dispatch
resume, plan-label deviations, BLOCKED resolution, non-build dispatch
shapes, hours-long elaboration-wall wedge). Consult it when a trigger
below points there (`→ rescue §N`); this body carries the every-iteration
core.

Setup: follow CLAUDE.md reading order (CLAUDE.md, ROADMAP.md,
notes/Phase$ARGUMENTS.md). Confirm `git status` is clean and the
leftmost active phase file builds green (per *Starting a Lean-touching
session* in CombinatorialRigidity/CLAUDE.md). While the model-experiment
is running, also run the protocol's **session-start availability check**
(`notes/model-experiment-protocol.md`, *Model assignment map*): determine
which rungs the Agent tool's `model` parameter can reach this session and
record the available set + any substitution in the repo-local config
before the first dispatch. Run the loop in the foreground of this session
only — never backgrounded or forked: two instances sharing one working
tree have ended with one committing the other's half-validated
uncommitted work.

Before the first dispatch, ask the user once whether this run modifies
these instructions — in practice users customize at session start,
typically lifting the 10-run cap and pre-authorizing the mechanical
fixups (rescue §1).

Loop:

1. Note HEAD and re-read notes/Phase$ARGUMENTS.md "Hand-off / next
   phase" — that's what the next commit should accomplish. If that step
   is **research-shaped** — the hand-off flags recon-before-build, OR 2+
   consecutive leaf commits have fed a hard core not yet built, OR 3+
   consecutive commits are thin wrappers aliasing existing facts, OR the
   hand-off flags a step as "needs the [GP / general-rank /
   deficiency-aware] variant of [a landed lemma]" and you cannot confirm
   that variant already exists in tree (grep it — a missing variant is a
   hidden genuinely-new prerequisite, a P≈3 leaf, NOT a P=2 "mechanical
   restate"; the L5b sizing-BLOCKED then design-decomposed, rows 104–105),
   OR the hand-off says "re-express / re-prove an existing decl X
   *through* a landed lemma/brick Y" and you have not confirmed Y's
   **conclusion shape** can produce X's (read X's landed conclusion
   *before* dispatching — a `finrank`-*bound* brick cannot yield an
   ∃-*literal-subfamily* decl; the 22j S5 §1.68(f) shape error, where a
   design verdict named a route between two mismatched conclusion shapes
   and a build would have faithfully implemented the wrong one — a
   mismatch is a design error to settle by recon, not a build),
   OR the hand-off calls an arm/assembly **"pure instantiation / bookkeeping —
   wire landed brick(s) B into consumer C's slots"** and you have not confirmed
   each B's *conclusion* sits at the **same graph / framework level** as the
   slot it fills (not merely the same Lean type, and not merely that B *exists*):
   a brick at the *wrong level* — e.g. a `splitOff`-level transport for a
   `removeVertex`-level `hwmem` slot — does **not** fill the slot, and the
   "instantiation" framing hides a genuinely-new leaf. Grep-and-read the
   **consumer's actual slot binding** *and* each brick's landed conclusion
   before rating it P=1 (23b: rows 288/291 landed split-level bricks pinned as
   the genuine-row `hwmem` disjunct, but the engine binds `hwmem` at removeVertex
   level — a build BLOCKED, recon confirmed, a de-risk re-derived the real leaf as
   a per-row case analysis; the prior coordinator grep-confirmed the bricks
   *existed* but not their *level*, which is what let the mis-pin through),
   OR a **build agent's own hand-off flags the *next* piece as genuinely-new**
   ("the real new lemma", "not a verbatim lift", "the genuine open design
   call") — that flag IS the recon trigger: recon the **route** before
   dispatching the dependency-chain prerequisites the flag names, because the
   chain a build extrapolates from a special-case (e.g. `d=3`) body can itself
   be the wrong route, and those prerequisites may serve a route the recon then
   dissolves (rows 195–198: two leaves lifted dead-`Φ̃`-route machinery before
   the recon re-routed to the `⋀^{d−1}W`-line argument, leaving the dead lemmas
   as green-`d=3`-wrappers)
   — the next commit is a **recon / design-pass**, not a build: dispatch a
   read-only Plan-agent recon, or a docs/blueprint design-pass commit
   that decomposes the core into buildable leaves with exact signatures.
   Recon is this workflow's highest-leverage move; trigger it **early**,
   before the next leaf (22g burned ~4 leaf commits on an undischargeable
   core; the 2-leaf trigger is the floor).
2. **Model-tier experiment (only while `notes/model-experiment.md` says
   Status: running):** rate S/P/B and pick the rung per
   `notes/model-experiment-protocol.md` (the single source of truth —
   don't duplicate it here); pass it as the Agent tool's `model`
   parameter, prompt held fixed. Honor any **standing rung override** in
   the log's repo-local config. Log rows follow the protocol's
   *Per-dispatch record* rules (write-after-verification timing,
   tail-only edit matching); before committing a log row, run `python3
   notes/check-log-rows.py` — it enforces the ~600-char Notes cap on the
   rows this commit touches; compress to pass (the commit message carries
   the recap), never commit a row it rejects. If Status says concluded,
   follow the promoted guideline. **Run boundary pairs when due** — when the log's
   findings name an open pair need and the profile fits, launch one
   without asking (the protocol's worktree procedure neutralizes the
   OOM/cost concern); pin a free-choice hand-off to one slice first so
   both members run the same task. A pair also audits the pin the primary
   builds against — a duplicate's BLOCKED-with-diagnosis is a win, not a
   failed pair (protocol *Boundary pairs*).
3. Dispatch Agent (subagent_type: general-purpose) with exactly the
   prompt below. Two exceptions adapt it: a **recon / design-pass** step
   names that deliverable in the first line (and carries the design-pass
   clauses — see end); a **phase-open / phase-close** step gets a short
   prologue stating what is sanctioned (e.g. a user-adjudicated close
   shape — "closing now is sanctioned; do not re-litigate it") and what
   is out of scope ("the successor phase is NOT opened by this commit") —
   without it the agent must re-derive both, and either re-asking or
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
     `git branch --show-current`. HEAD advanced past the noted sha; still
     on `master`; author bryangingechen@gmail.com; diff matches what the
     hand-off pointed at. A docs/blueprint-only commit (recon, design
     pass, decomposition, re-scope) is normal in a research-shaped phase —
     judge against the hand-off, not against "must touch Lean". (Wrong
     branch / author / trailer → rescue §1: a fixup, not a stop.)
   - **"Gates green" is an attestation, not evidence.** The step-5 gate
     always runs; for below-top-rung dispatches also re-run `lake lint`
     and read the **full diff** (protocol rule); for haiku, re-run every
     gate the return names (a haiku once fabricated all three gates green,
     row 12).
   - **Sorry-grep the touched `.lean` files after every below-top-rung
     dispatch**, regardless of what the return says — a LANDED return can
     omit a `sorry` the commit message discloses (row 13). Read the commit
     message body, not just the summary line. The converse also happens —
     **judge completeness from the diff, not the prose**: a post-compaction
     commit message can mis-describe *finished* work as partial (row 74),
     and the false belief propagates into the notes/blueprint pin; when
     message and diff disagree, trust the diff and repair the prose. A
     landed sorry is a failed verification → escalate one rung up with the
     route named, keep the commit, close the sorry in the follow-up.
   - **Shape check:** when the hand-off pins the deliverable to a design
     verdict (a §1.NN pointer or named verdict), diff the landed statement
     against that section — motive strength, transport direction,
     consumed-vs-carried hypotheses. Mechanically clean commits have
     landed design-excluded shapes (rows 11/14); only the section re-read
     caught them. A shape deviation = corrective dispatch one rung up with
     a tailored prompt naming the verdict, never a discharge-on-top. Diff
     against the **pre-commit** design text (`git show <noted-sha>:notes/…`),
     not the post-commit one — the builder edits the notes too, and a
     partially-delivered item can be rewritten to match what landed,
     silently dropping pinned sub-clauses (row 46). Same for **prose
     routes**: a red-node / deferred-route commit gets its route diffed
     against the canonical design § exactly like a Lean statement (row 50).
   - **Supersession-deletion check (the shape check's blind spot):** when the
     pinned verdict mandates **deleting or superseding** a decl (not just
     restating it), the shape check is incomplete until you confirm the decl
     is actually **gone** — grep it. A build that adds the replacement but
     leaves the superseded decl orphaned passes gates *and* the
     statement-shape check (the new decl IS correct) yet violates the design,
     because the deviation is an *absence*, not a wrong shape. 22k L9 created
     the zero-carry spine `theorem_55_all_k` but left the superseded
     `theorem_55` / `theorem_55_generic` in tree, co-pinning the dead
     `theorem_55` on the just-greened node — caught only by re-reading the
     design's "superseded and deleted" verdict (row 160 cleanup). The tell:
     a "restate X, delete superseded Y" verdict where the diff shows the
     restate but no deletion (the legacy decl often survives because deleting
     it would break a blueprint `\lean{}` pin the builder leaves dual-pinned).
     Fix with a follow-up cleanup (delete + re-pin + reword stale prose), not
     a discharge-on-top.
   - **Recon verdicts get reasoning scrutiny, not just mechanics** — a
     mechanically clean recon can be wrong, and building on it re-incurs
     the churn it was meant to end. Scrutinize hardest a recon that
     **dissolves or re-routes** a gap: confirm every *other* carried
     obligation still closes under the new route (a re-route can orphan a
     hypothesis the old route silently supplied — 22g §1.46 orphaned
     `hgab`). A **new gap** is usually cheaply verifiable — check it
     against the primary source (`.refs/` PDFs, REFS.md) and/or a one-line
     Lean witness (`lean_run_code`) *before* re-planning. **Scrutinize a
     pin's named OBJECTS, not just its cited API names** — a design-pass
     can name the right *vertex set* but the wrong *construction* (22i
     §1.63 pinned a splice leg as `induce ((V∖V(H))∪{r})` when the
     contraction `rigidContract` *collapses* V(H)→r, keeping the crossing
     edges `induce` drops → a strictly weaker, wrong bound). Confirming
     only that the cited APIs exist misses this: open the landed
     `def`/`theorem` of every graph construction
     (`induce`/contraction/`collapseTo`/`map`) the pin references and
     confirm the pinned object **is** that construction — else a build
     faithfully implements the wrong pin and gates green (only a
     boundary-pair duplicate caught it, rows 96–99; first-pass scrutiny of
     just the *named* APIs did not). A **route claim a build agent records
     in the hand-off** ("the next step must …") is a recon verdict in
     disguise — verify it against what the design doc *actually proposed*
     before dispatching a build on it (22h rows 38–39; 23b row 284, where a
     build that landed a clean leaf wrote a NEXT-step route into its hand-off
     that *re-proposed a design-rejected route* — the per-body block carry
     §(o‴) had killed as the 4×-mis-pin trap — and a fresh coordinator who
     trusted the hand-off would have re-walked it: diff the build's hand-off
     route against the authoritative design verdict, not just the prior pin). When the design
     doc itself defers a shape ("pin at the X moment"), that moment IS the
     next dispatch — a design-settle pass, not a build. **This holds even
     when the design pass says "resolve at the build, soft-rec X":** if the
     deferred route's correctness depends on a *not-yet-built downstream
     consumer*'s obligations (interface hyps the leaf can't see), the leaf
     build — and a boundary pair on the leaf — validate the route *as a
     lemma*, not its *fitness for the consumer*. Settle such a route against
     the consumer (a design pass that reads the consumer's hyps), or pin it
     at the consumer's build, not the leaf's. The L5b episode (22i): §1.65
     deferred route-1-vs-2 "to the build, soft-rec route 2"; the leaf + a
     boundary pair both took route 2 clean, then the producer BLOCKED because
     route 2 couldn't supply its `hFc_surv_le` containment — forcing a §1.66
     re-route to route 1 and a dead leaf (the churn a consumer-grounded
     design-settle would have avoided). **Same for a leaf's carried
     PRECONDITIONS, not just its route (L6, rows 115/118):** the §1.67 pin
     split L6 into a brick + a producer-that-calls-it, but the brick (a mirror
     of its rigid sibling) demanded `hGv : Gv ≤ G`, incompatible with the
     producer's `Gv = G.splitOff …` (`splitOff ⋬ G`) — so the producer had to
     inline the brick (dead leaf, ~1010-line bloat). A design-pass flag that
     *names* but *defers* a precondition ("confirm the `Gv` wiring") is not a
     resolved one; before building a pinned leaf+consumer split, confirm the
     leaf's carried hypotheses actually hold for the consumer's graph objects.
   - **An abstraction that defers the crux as a hypothesis is not progress
     on the crux.** When a build *abstracts* a pinned lemma — taking a
     genuinely-new fact as a hypothesis rather than proving it (22i L5a-i
     landed the splice brick taking the Lemma-5.1 injectivity `hInj` as a
     hypothesis, proving only the easy block-triangular rank-nullity) —
     the hard step is **relocated to the caller, not done**. Often a
     legitimate slice (the design doc may sanction the split), but the
     genuinely-new obligation now lives in the next leaf, and a builder
     tends to re-frame that leaf as "plumbing + interface", re-burying the
     crux. Re-flag the relocated obligation in the hand-off and **rate the
     next dispatch by the deferred math, not the plumbing** (rows 99–100).
     The tell: a fact the design doc called "genuinely-new" appearing as a
     `h…` argument of a landed lemma — grep it, confirm where it is
     discharged.
   - **A large cost/size outlier is an early degradation signal.** A dispatch
     whose wall-time / tool-uses / diff-size runs far past the norm (L6b:
     10.8 h / 1884 tools / a ~1010-line proof for a P=2 producer, row 118) has
     usually *forced* a too-big task through — bloat, mid-proof `maxHeartbeats`
     resets, inlining instead of decomposing — rather than bailing per
     scope-to-fit (the clause shapes scope but can't guarantee it; it fails as
     *bloat-not-bailout*). Scrutinize hardest (full warning scan, bloat/inline
     check) even when the agent attests green — a "green, only long-line
     warnings" attestation understated a warning-bearing, deprecation-carrying
     commit. For a correct-but-degraded artifact (compiles, axiom-clean,
     matches the pin), **repair the warnings + flag a refactor: keep the
     correct math, don't accept the warnings, don't revert correct work.**
   - Re-read the updated "Hand-off / next phase". (Returns with neither
     LANDED nor BLOCKED, killed dispatches, plan-label deviations →
     rescue §§2–4.)
5. If the commit changed any `.lean` file: `touch` the changed file(s)
   (cached modules don't re-emit warnings), then `lake build
   <the changed module(s)> 2>&1 | grep -E 'warning:|error:'` — build
   the module(s) the commit *touched* (the leftmost active phase file,
   **or a new file the commit added** — a new downstream file is rightmost,
   not "leftmost"), so warnings re-emit. **Warning-clean, not merely green**
   (a sorry'd skeleton once rode a green-but-warning build onto master, row
   17). Red or warning-bearing → stop and surface. Skip for docs-only
   commits. (Run the gate in the foreground, or — if backgrounded to read
   the diff in parallel — **wait for its completion notification**; re-reading
   an unchanged background-output file is a wasted call, a recurring drain
   across a long loop.)
6. One sentence to the user: clean handoff, or the specific concern.
   Surface **phase-boundary decisions** — early close, sub-phase
   split, a green-modulo-X change to what "phase close" means — with
   a concrete commit-count estimate rather than deciding unilaterally.
7. Stop and surface on any of:
   - ROADMAP Status shows Phase $ARGUMENTS ✓ (the subagent ran the
     phase-close checklist). After a user-approved mid-session
     close-and-split, confirm with the user before resuming the loop
     on the successor phase.
   - BLOCKED return; or HEAD didn't advance — **but salvage the return's
     route findings into the hand-off first** (row 72), and check for a
     within-workflow resolution before stopping (a sizing-shaped BLOCKED
     is the step-1 design-pass trigger, not a stop — rescue §5).
   - A recon flags a decision for **user adjudication** (e.g. a carried
     hypothesis or motive change) — present the options with estimates;
     don't pick unilaterally.
   - Suspicious diff: unexpectedly large, unrelated files, or the step-5
     gate red.
   - The agreed run cap (default 10) reached since the user last checked in.

Don't pad the **routine build** prompt or pre-load files — the CLAUDE.md
auto-loads carry the discipline, and duplication invites drift. (The
scope-to-fit / compaction-bailout clause *is* part of the fixed prompt:
prompt-level discipline doesn't survive compaction — row 17's 2.7 h
dispatch — so the clause shapes scope while context is intact and the
`block-sorry-commit.sh` hook backstops after it degrades. Post-amendment
evidence it works: rows 18–19 self-shrank to complete sub-lemmas.)

A **recon / design-pass** dispatch is the exception: give it a tailored
prompt naming what to recon, the coordinator's verified findings
motivating it, and the deliverable (a design-doc entry + re-pointed
hand-off). **Two clauses earn their place in every design-pass prompt**
(rows 96 vs 99: the same opus rung pinned §1.63 *wrong* unprimed, then
§1.64 *right* when primed): (i) *verify every load-bearing claim against
the landed source* — the actual `def`/`theorem`, not the prior pin's
prose; (ii) an explicit *flag-don't-force* mandate — "if the corrected
route needs a motive/IH-level change or genuinely-new math, say so and
stop; a pin that honestly names an open decision beats a confident wrong
one (that is exactly what cost a revert)." Single-pass design output is
fallible even at the top rung; the grounding + the honesty mandate, not
the rung, is what made the re-pin sound.

Other dispatch shapes — the **cleanup-round** scoped no-git editor and
the **no-dispatch** coordinator-authored commit (decision records,
adjudications, postmortems) — are in rescue §6.
