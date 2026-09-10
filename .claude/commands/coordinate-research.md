Coordinate research phase $ARGUMENTS. Dispatch **directions** —
read-only research passes — singly or in a deliberate fan-out; verify
each return yourself; land each one **serially, one commit per
direction**. Stop when the phase closes or something looks off.

**Use this command, not `/coordinate-phase`, when the phase is
research-shaped** — no Lean landing, no blueprint dep-graph
(`RESEARCH-ARC.md`'s definition). They are split because **84% of
`/coordinate-phase`'s paragraph blocks reference Lean or blueprint
machinery** a research phase cannot use (measured 2026-09-09,
`notes/Harness-structure.md` D4), and a dispatch under the wrong command
pays for it twice: in the coordinator's prefix, and again in the
`recon`/`phase-builder` cores. If a research phase needs one Lean
commit, dispatch it with `/coordinate-phase`'s machinery and come back.

**`RESEARCH-ARC.md` is the manual this command drives** — label
reservations (§1), serial landing and the concurrent-read hazards (§2),
the gap-map-as-status-object pattern (§3), a driver per headline
sentence (§4), cap disclosure (§5), kill conditions on forward-looking
items (§8), and §7's prediction-labelling rule live there in full. Read
it once at session start; this body carries only what a coordinator
needs *in the loop*, and points rather than restates.

**FIRST ACTION OF THE SESSION, before any reading**, ask the user once
whether this run modifies these instructions, and fold the
**rung-availability confirmation** into the same check-in (which rungs
are dispatchable; fix each unavailable rung's substitute up front — do NOT spend dispatches probing). **This
check BLOCKS the loop:** wait for an actual user response — a timed-out
question is not an answer (a 60 s timeout once had a coordinator carry
over a prior session's config, which the user's late answer partly
reversed, 2026-07-02).

It goes first because **neither question depends on any of the setup
below**, so asking after the reads inserts a serialization point at zero
benefit — and the rung answer can change what the reading is *for*
(`notes/Harness-structure.md` D6.6).

Setup: follow CLAUDE.md reading order, but read **only ROADMAP.md's
*Status* table plus the active phase's §N** — closed phases' roadmap
prose is archival detail no coordinator needs pre-dispatch. Read
`notes/Phase$ARGUMENTS.md` **with its own reader** — `python3
notes/phasenote.py $ARGUMENTS --next` (the next concrete task, in ~2
units instead of a 1 300-word paragraph), then `--surfaces` before any
landing sweep and `--status`/`--handoff` as needed; a full-file pass is
the fallback, not the default, because the note is read BEFORE the first
dispatch and therefore costs ~20x (D7.2). Fix §N in passing if it
contradicts the Status row (unread, §39 drifted a week and ~20 directions stale,
2026-08-26). Read the phase's **status object** with its own reader —
`python3 notes/gapmap.py` (`--list` / `--row … --cell status` /
`--label '(GR-15)'`), never `sed`/`grep`: one row is one
22 000-character line, up to 20% of a coordinator session's peak
context. Confirm `git status` is clean, and run the loop in the
**foreground of this session only** — never backgrounded or forked.

## The claim ledger — how to answer "what is already proved"

`python3 notes/ledger.py` is the way. **Read its module docstring once**
— long and authoritative (schema, identity key, parsing traps, the
no-check-in argument) — and note that the corpus's own subtree
`CLAUDE.md` (e.g. `notes/pencil/CLAUDE.md`) is canonical for that
corpus's layout and canonical homes, and auto-loads on first touch.
What binds the loop:

| call | answers |
|---|---|
| `--label '(BE-189)'` | one label's clauses, full text, with section, step, status, citations, live line number |
| `--brief L1 L2 …` | the briefing block for a label set, **statements quoted verbatim** |
| `--status OPEN --section '…'` | what is unclosed, where (`--file` also narrows) |
| `--frontier` | unclosed claims whose every citation IS closed — the cheapest live leaves |
| `--cited-by '(BE-216)'` | what breaks if this claim falls |
| `--delta <ref>` | the status change-set against a git ref |
| `--lint` | GATE: the status vocabulary on what this commit adds or changes (`--all`, `--strict`) |
| `--selftest` / `--list` / `--stats` | parser audit; per-file counts; the status census |

- **It is an index, not a check.** `PROVED` is a claim by whoever wrote
  that clause; regeneration guarantees the ledger matches the prose and
  nothing about whether the prose is right. Open the owning section
  before building on a row.
- **`UNTAGGED` is a first-class status and half the corpus** (666 of
  1 308 at slice 8's census) — it names exactly which claims a direction
  must read prose for, which the spec should say rather than let the
  direction discover.
- **`--delta <ref>`'s output goes in the landing's commit message.** The
  ledger is deliberately not checked in, so git history is the progress
  record, and a generated change-set cannot overstate what moved.
- **`--lint` and the other two docs gates (`notes/check-phase-note.py`,
  `notes/check-gapmap-cells.py`) inspect files changed vs `HEAD`**, so a
  run *after* the commit reports `0 checked` and certifies **nothing** —
  which is what a post-landing verification does by default. **Run them
  BEFORE committing, or with `--all`.** Second recorded blind spot:
  `check-gapmap-cells.py` detects a changed row by **word count**, so a
  recompute landing at its pre-edit count is invisible — there,
  `notes/scripts/gapdiff.py` is the gate that sees content.

## Writing the spec

**A spec quotes claim statements from `--brief`, never retyped from a
summary surface.** The one non-negotiable mechanic, and it is BGENUINE's
(2026-09-01): a coordinator prep quoted a criterion **without its
both-pieces-attain hypothesis** — copied from a gap-map row that had
dropped it, not from the lemma — so at **100 of 392** witnesses the rows
read as violations against the wrong denominator. That coordinator had
quoted it correctly two preps earlier, so this is drift inside one
session and the fix must be mechanical. BDECOR's proviso dropping on
**six** summary surfaces while the body prose stayed correct is the same
pathology one level up.

Beyond the generated block, a spec carries:

- **The question** in one sentence, and what a decision either way buys.
- **The prediction — but PRICE ITS PARTS SEPARATELY, because they have
  very different records** (§7's 2026-09-10 amendment, measured over the
  arc's first *unselected* sample of six). §7's tally is **selected on
  failure by construction**, so it is a catalogue of failure modes and
  **never** evidence about a base rate: **cite it, never re-derive it**
  (three concurrent directions once each read a different baseline).
  - **Verdict** (4 of 6) and **evidence stratum** — always. Label it a
    HYPOTHESIS, *to be tested, not inherited*, and name the stratum
    ("read from the gap-map row and the return message; I have NOT
    opened the proof"). Keep the reason **separate from the verdict** so
    a direction can refute one without the other.
  - **Where you expect to be wrong** — the spec's **highest-yield
    sentence**, deciding three of five consecutive instances. Never omit it.
  - **The MECHANISM — state it as a candidate to ELIMINATE, not as the
    reason the verdict holds.** 0 of 6, failing as *tautology* and as
    *inapplicable-by-definition*, and it is not inert: it steers the first
    slice and the tell. Write *"here is the mechanism I could not rule
    out; refute it cheaply first"*, and let **nothing** in the ranking or
    the first slice rest on it. `strategy.md` §8's board entries carry the
    same defect at the same rate, so re-derive an entry's stated mechanism
    before its cost.
  - **The TELL — derive it from the QUESTION's region, never from your
    predicted mechanism, and state that region.** Checking that it is not
    *already satisfied* (one grep, BGTWOA) catches only half: two tells in
    one session were **unsatisfiable** and passed that check — one built
    from the residue when the refutation lived in the over-strength
    region, one at `Δn = 2` which is empty on lengths alone. The check is
    a question, not a grep: **could the verdict differ inside the region
    this tell samples?**
- **The reserved label prefix and section name**, verified **0-hit**
  across the tree (§1) — a reservation protects a dispatch from its
  siblings, not from the corpus.
- **The blind-axis list** — the axes the harness makes it *impossible*
  to vary (§4; grep the generator for hardcoded constants). Not merely a
  disclosure: un-fencing one at BNONUNI cost **one defaulted parameter,
  12 insertions** and refuted a clause that had survived an exhaustive
  6 400-tuple sweep of the fenced population, against **five**
  directions spent on that population. It belongs in the *ranking*.
- **The concurrency warning when siblings are in flight** (§2): `HEAD`
  may advance under a running direction, the scratchpad is **shared**,
  diff against `HEAD` and never the working tree, re-take doc-cap
  figures at landing time with the baseline sha, and never have a
  direction re-derive a shared monotone counter.
- **Before dispatching at a residual, open its CONSUMER** and confirm
  the exact statement it takes (F26): five consecutive directions ran at
  one residual, every one sound, and it turned out never to be
  consumed — three pairwise-inequivalent readings, the consumers on the
  third. No gate catches a wrong choice of target.

## Picking the rung

**There is no S/P/B here, and copying it would be dishonest:** those
axes were calibrated on ~890 *build* dispatches and each scored commit
risk — blast radius, proof novelty, spec precision against a target
signature. A direction commits nothing, so two of the three have no
referent. `/coordinate-phase`'s playbook says as much — research
dispatches "fall outside the axes (they measure question stakes, not
commit risk): default opus; top rung when the verdict re-routes a phase,
adjudicates a carried-hypothesis / motive change, or settles new mirror
math."

Observed practice, recorded so that mapping is not mistaken for a
calibration: **PENCIL ran its directions at the top rung throughout**,
nearly every one meeting the new-mirror-math trigger, with
`research-direction-opus` substituted from 2026-09-01 when fable went
missing from the account's model selector — **the substitution held**
(both returned HITs, one refuting a landed clause the previous direction
*and* the coordinator had accepted) and **no dispatch was spent
probing**. Sonnet and haiku are **unmapped** here, so treat a low-rung
research dispatch as a deliberate probe with every claim re-verified;
and whether the "compute-licensed vs derivation-first" tier split tracks
real dispatch risk is **explicitly unsettled** — do not rung off it.
Rungs dispatch as **typed variants** (`research-direction-{opus,fable}`),
thin shells over `.claude/agents-core/research-direction.md` whose
`model` frontmatter makes a `SendMessage` resume rung-stable (F5); an
unavailable rung goes to the nearest available at or above the mapped
one, fixed once at the check-in.

## Loop

1. **Note HEAD.** Re-read `notes/Phase$ARGUMENTS.md` *Current state* —
   when it and *Hand-off* both carry a "next concrete task" pointer,
   *Current state* is authoritative (the Hand-off copy drifts stale);
   reconcile, and collapse the duplicate so it cannot drift again. Pick
   the direction against the status object and the recommendation
   surfaces, **re-checking each candidate against its own kill condition
   and deciding row** (§8: a coordinator tried three times in one
   session to pick from those surfaces and was misled every time; the
   item dead longest was the one described as *cheap*). A kill condition
   naming a **number** is usable only with that number's
   **derivation** — a threshold derived for `X` is not one for `X′`.
2. **Build the briefing block:** `--brief` over every in-scope label,
   plus `--frontier`/`--cited-by` for what the answer unlocks or breaks.
   A question standing on `UNTAGGED` prose, or on a `MEASURED` claim
   whose driver names no support, has re-deriving its own premises as
   its first job — say so in the spec.
3. **Dispatch `research-direction-<rung>`, UN-NAMED.** An un-named
   dispatch delivers its verdict and cost figures in the return or its
   completion notification; a *named* one routes to the async mailbox
   and surfaces only an idle notification — reserve names for an
   addressable resume. The agent definition and the CLAUDE.md auto-loads
   carry the discipline; the prompt carries the spec and nothing else.

   **Cache keepalive.** In the SAME turn as the dispatch, arm
   `CronCreate({cron: "17,47 * * * *", prompt: "KEEPALIVE — if a
   dispatched direction has RETURNED and is not yet verified, start
   verifying it (loop step 4). Otherwise this is cache warm-up only: do
   NOT read files, run commands, or dispatch — reply with exactly:
   keepalive"})`; `CronDelete` its id at step 4. The conditional clause
   is what makes the cron a **loop restart** and not only a ping: it
   fires while the REPL is idle, which is exactly the state a
   step-6 yield leaves it in, so it self-heals the stall D7.3 records
   without a user turn. The cheap path is unchanged — nothing returned,
   one word out. A dispatch
   past ~1 h expires the session's prompt cache and the next turn
   rewrites the whole prefix at 2× base input, where a ping is a 0.1×
   cache read that refreshes the timer. Cron fires only while the REPL
   is idle; skip it in overage (TTL drops to 5 min there).

   **Continuation dispatch.** When the next task continues the arc just
   delivered, `SendMessage` the returned agentId rather than launching
   fresh; run the full step-4 verification on each returned commit
   *before* the next continuation, and cut over when the arc changes or
   the agent degrades. A killed dispatch resumes the same way with its
   cause named (a 64k output-token kill was recovered on one added
   instruction: work incrementally, never emit one very long response).
4. **Verify the return** (`CronDelete` the keepalive first). "Gates
   green" is an attestation, not evidence, and **coordinator-authored
   artifacts get the same tier as a subagent's** (F19 — four of four
   coordinator contributions in one wave needed correction, three caught
   by the directions).
   - **Re-run every driver the draft cites, plus its headline FIGURES**,
     not just `--validate` modes; then, per "proven piece", ask **which
     driver tests THIS sentence?** (F11 — three consecutive passes each
     corrected a predecessor's claim, every one surviving a scrutiny
     pass that reproduced the drivers faithfully, because the defect sat
     in a claim no driver tested.)
   - **Price an assertion by its population, not its existence:** an
     `assert` says the claim held wherever the sampler went and nothing
     about where it could not go — name the sampler's support, ask which
     of the claim's own variables it varies, then grep the generator for
     hardcoded constants (§4).
   - **"Not found under cap C", never "does not exist"**, and the
     disclosure travels with the figure wherever it is quoted (§5).
     **One draw is a lower bound, not a measurement**, for a
     semicontinuous statistic (F27); the positive direction needs one,
     since an exhibited certificate is a proof.
   - **A dispatch's criticism of coordinator work gets the same scrutiny
     as its mathematics** (F24): one confident, numbered process claim
     was wrong, and acting on it would have produced a corrective commit
     repairing nothing.
   - **On a fan-out, budget an explicit CROSS-RETURN pass** separate
     from the per-return checks — where a fan-out's compounding value is
     realized, and what caught all three concurrent-read hazards in one
     round (F18/F19). Check **duplication** there too: reservations
     prevent naming collisions, not two directions deriving one identity
     (F20).
5. **Land it serially — one commit per direction.** Merge the draft into
   the owning section, update the status object's row, and:
   - **Strip the draft's closing "Coordinator actions at landing"
     block** — execute it, audit each named action in tree, then delete
     it; merged, it reads as an outstanding to-do list for work already
     done (four consecutive landings merged it verbatim).
   - **Sweep the status surfaces as one deliberate pass**, not as a side
     effect of editing the prose around them: the phase note's
     `**Status:**` header (roster, counts, next-task sentence), the
     *Hand-off* next-task slot (**re-aim it, never delete it**),
     *Current state*, the ROADMAP Status cell, and the dispatch-scoping
     file's own header. Three consecutive landings each left a
     **different** one stale (F17). Verify the surfaces the landing did
     **not** touch — a return listing seven correct updates reads as
     complete precisely when the eighth is missing.
   - **A correction to a summary row is presumptively a correction to
     body prose too** — grep the tree for the same stale claim, and use
     `git show --unified=0` to answer *did the correction reach the
     originating prose?* in one call (F12).
   - Run the three docs gates **before** committing, and paste
     `--delta <noted-sha>` into the commit message.
6. **One sentence to the user** after each commit: clean handoff and the
   next direction, or the specific concern. **It is a sentence, not a
   yield** — before ending the turn, check whether any other dispatch
   has already returned, and if one has, go straight to step 4 for it.
   In the first `/coordinate-research` session this was missed three
   times: a landing report was posted with a returned direction sitting
   unverified (GCOIND 2.8 min, GSIMUL 1.7 min — and the coordinator had
   already *written* that it knew GSIMUL was back), and each stall cost
   a user turn to clear (D7.3). Yielding is correct only when nothing
   has returned; waiting for the *first* return of a fan-out is not
   fillable work and should not be filled. Surface phase-boundary
   decisions with a concrete estimate rather than deciding unilaterally.
7. **Stop and surface** on: a verdict that re-routes the phase or
   demands user adjudication (present options with estimates; don't pick
   unilaterally); a direction returning BLOCKED or with nothing landed —
   salvage its route findings into the hand-off first, since a reverted
   pass's verified map survives only if the coordinator moves it; a
   suspicious diff; ROADMAP Status showing the phase closed; or the
   agreed run cap (default 10) since the user last checked in.

## Session budget, and the exception log

Before a fan-out and between landings: `python3
.claude/scripts/session-usage.py limits` (`--config-dir` when the local
Claude config dir is non-default) prints 5-hour and weekly utilization
with reset times; above ~80% on either, stagger instead of fanning out.
**A near reset is a reason to PROCEED, not to pause:** under ~1 h to the
5-hour reset, dispatch anyway — the window refills well inside the
1-hour cache TTL, so waiting buys no headroom and costs a turn plus a
cold prefix (user call, 2026-09-02). Wait only when the reset is far off
*and* the dispatch would likely throttle mid-flight. `session-usage.py
tokens` sums per-model usage from the local transcripts (subagents
included, deduped) — calibrate a planned fan-out against a comparable
past round with it. Optimal fan-out width is **unsettled** (three and
five both ran successfully, never systematically varied); never present
a width as calibrated.

`notes/dispatch-log.md` records **exceptions only** — escalations,
probes, BLOCKED/killed/salvaged dispatches, gate-invisible defects
caught in verification, playbook deviations and their outcomes. Routine
clean landings are NOT logged (git history is the record; per-dispatch
logging cost more than it returned). Distill recurring lessons into its
*Findings* section and promote stable ones into `RESEARCH-ARC.md` —
whose three-tier rule binds the promotion: **one wave of evidence is a
Candidate, not a Ready item**, and a second research-shaped phase's
independent use is what promotes a pattern.
