# RESEARCH-ARC.md — running a research-shaped phase

**Read-on-demand reference, not session-start orientation.** Most phases in
this project land in Lean against a blueprint dep-graph, so `PHASE-BOUNDARIES.md`'s
checklists and the forward-mode workflow in `CLAUDE.md` cover them. A
**research-shaped phase** is different in kind, not just in content: it has
**no Lean landing** (the result is informal mathematics, staged for eventual
transcription, not a `\leanok` node), **no blueprint dep-graph** (there is no
red/green node index to drive the to-do list — see *The gap map* below for
what replaces it), and its working discipline gets **invented inside the
phase**, because none of the standing manuals anticipated it. That last fact
is *why this file exists*: a phase's own docs are not read-on-load by other
phases, so a discipline invented and only ever written down in
`notes/PhaseN*.md` rots there, unread, the next time a research-shaped phase
opens. Read this file when scoping such a phase — most concretely, right
where `.claude/commands/coordinate-phase.md`'s loop step recognizes the next
commit as **research-shaped**.

**Provenance.** Every item below is distilled from **Phase 39 (PENCIL)**'s
kernel-(K) research arc — the hinge-pencil molecular conjecture's open
kernel, run as **66 docs+script-only dispatches** across roughly four weeks
(2026-08-02 → 08-26; the figure was 49 to 2026-08-19, when this file was
written), including **three** multidispatch fan-outs of five concurrent
directions each and a long tail of single directions and coordinator-picked
pairs. `notes/Phase39.md`, `notes/Pencil-fanout.md`,
`notes/Pencil-labels.md`, `notes/Pencil-informal.md` and
`notes/dispatch-log.md` are the canonical homes for that phase's own
detail; this file distills the **general** lesson and points back at them
for the worked example, rather than duplicating it. It is written to
generalize past PENCIL, but has (so far) exactly one phase's worth of
evidence behind its generalization — treat a claim here that turns out
PENCIL-specific as a bug in this file, not a reason to distrust it wholesale.

## Read this alongside

- `CLEANUP.md` — the between-phases audit-round manual. A research-shaped
  phase is not a cleanup round (it has a mathematical target), but the two
  share the same *cheap-verification, forward-weighted note* instincts.
- `PHASE-BOUNDARIES.md` — the phase open/close checklists. They still apply
  in full to a research-shaped phase; nothing here replaces them, it adds
  what they don't cover (there is no dep-graph node to flip green).
- `notes/CLAUDE.md` — the phase-notes discipline (forward-weighted note,
  one canonical home per content type, lift-on-promotion). This file *is*
  a lift-on-promotion instance: it exists because that rule triggers at
  two references and PENCIL's discipline had reached six.

## Three tiers, not one list

The temptation with a distillation round is to write everything the phase
learned as a flat list of rules. That would be worse than not writing this
file at all: a reader cannot tell a load-bearing rule from a one-off
observation, and the next research-shaped phase would either over-apply a
fragile finding or, worse, distrust the whole file once one item turns out
wrong. So every item below carries an explicit **tier**, and the tier is
part of the content, not a formatting nicety:

- **Ready** — promoted discipline. Each item below has **three or more
  independent waves of evidence** (three-plus separate dispatches or
  incidents where the same lesson recurred, in this project's *lift on
  promotion* sense). Apply these as standing rules in any research-shaped
  phase.
- **Candidates, not yet promoted** — one wave of evidence so far. Real,
  specific, worth watching for a second occurrence — but this project's own
  standard is to promote *stable* (repeatedly-recurring) findings, not
  first observations. Treat these as things to **watch for a second
  instance**, not as rules to apply on faith. They stay recorded in
  `notes/dispatch-log.md` *Findings*, not restated here in full.
- **Genuinely unsettled** — deferred, with the open question stated
  explicitly. PENCIL's own multidispatch fan-outs raised these questions
  without answering them; inventing an answer here would be worse than
  leaving them open, because a fabricated rule reads as settled the moment
  it is written down.

## Ready — promoted discipline

### 1. Label reservations and the minting rule

A **reserved prefix** and a **reserved section name**, one pair per
concurrent direction, each verified **0-hit** as a raw substring across
`*.md`/`*.tex`/`*.lean`/`*.py`/`*.m2` before dispatch. This is the
document-side analogue of the tree-side non-collision mechanics (§2
below): those stop concurrent dispatches from contending for *files*; this
stops them from minting the **same label**.

**Why a reservation, and why it must be checked against the whole corpus,
not just the siblings in flight:** a reserved prefix protects a dispatch
from its *siblings* — the other directions running concurrently — but not
from the *existing corpus*, which is why the check is a 0-hit grep against
everything, not a coordination protocol between the directions themselves.
PENCIL's own registry states this precisely, and it is the line to quote:
"*A reserved prefix protects a dispatch from its siblings, not from the
existing corpus; clause L1 still binds inside a reservation*"
(`notes/Pencil-labels.md`, the direction-A landing incident that forced the
point home — a reserved dispatch still hit a three-way collision on a bare
label it reached for from inside its own reservation).

**Canonical detail — read there, not here:** `notes/Pencil-labels.md` is
the worked example: its four-clause minting rule (grep the registry before
minting; never label a *step*, only a claim; qualify every cross-section
citation with its owning section; never rename an existing label — new
collisions are resolved by qualification, not renumbering), its measured
diagnosis of *why* bare single-letter label families collide while
topic-tagged multi-letter ones never have (checked across 7,438+ lines of
two workbooks), and the live *Reserved namespaces* table for in-flight
dispatches.

### 2. Serial coordinator landing; agents draft outside the tree

Concurrent research dispatches are **read-only with respect to every shared
file** and **commit nothing**. Each writes its full argument to an
**untracked draft** outside the coordinator's staging area (PENCIL's own
convention moved from a session-scratchpad path to an untracked
`notes/Pencil-draft-<CODE>.md`, both work equally). The coordinator verifies
and **lands each return serially, one commit per direction** — never a
batch commit, never a parallel commit race.

**The non-obvious finding: worktrees were deliberately NOT used, and that
was the right call.** The instinct when running N concurrent agents is to
give each its own git worktree so they cannot collide on the working tree.
PENCIL's fan-outs ran a single working tree throughout, on purpose, because
**the contention is over shared *documents*** — the gap map, the phase
note's status header, the label registry — **not over the tree**. A
worktree solves a problem PENCIL didn't have (tree-level file contention)
and creates one it did have worse (N branches all editing the same
document sections, now requiring an N-way *merge* instead of N sequential
*edits*). Serial coordinator landing is what actually resolves document
contention, and it is unaffected by where the agents physically ran.
Validated at both five-direction fan-outs with zero collisions each time.

### 3. The gap map as the phase's status object

With no blueprint dep-graph, a research-shaped phase needs **one table
that is the authoritative current state** — the thing a blueprint's
red/green node coloring would otherwise be. PENCIL's is
`notes/Pencil-informal.md`'s **State of (K)** map: one row per named gap, each row
derived from that gap's own section's confidence-verdict block, and
**the artifact a new pass updates in place** rather than a changelog a new
pass appends to. Its own header states the discipline precisely: *"This
map is the artifact a new pass updates — edit these rows... rather than
writing a fresh summary of the arc beside it."*

The corollary that matters for landing checklists: a correction to the map
is presumptively a correction to at least one paragraph of body prose too,
since the map is a *summary* of that prose (dispatch-log F12) — grep the
whole file for the same stale claim, don't just fix the row.

### 4. A driver per headline sentence (dispatch-log F11)

**Every headline claim needs a driver that tests that exact sentence** —
not a driver that tests a neighboring proposition and is *believed* to
cover it. And **"exhaustive" / "forced" / "the only" are their own claim
class**: an exhaustiveness or uniqueness assertion needs a driver that
actually *enumerates*, not one that merely asserts per-instance. Never
state a claim more strongly than the driver that tests it.

This is the single most load-bearing item in this file — it recurred
across three consecutive corrective passes in PENCIL's arc (a degenerate
sampler contamination, an acyclic-vs-proper colouring conflation, and a
"forced" dictionary entry backed only by per-instance asserts), and every
one of the three survived a coordinator reasoning-scrutiny pass that
reproduced the drivers faithfully — because *the defect sat in a claim no
driver tested*, not in a driver that ran wrong. **The corrective mechanism
in an informal-research arc is the next pass, not coordinator scrutiny**:
price each pass as including a correction to the one before it, and prefer
commissioning the next pass over building on the current pass's optimistic
residue. Full incident record: `notes/dispatch-log.md` **F11**.

### 5. Cap disclosure

**An exhausted cap is not a proof of nonexistence.** If a search, sample,
or sweep is capped — a shape count, a stride, a bounded search depth — the
return reports **"not found under cap C"**, never **"does not exist"**, and
that disclosure travels with the figure everywhere it is quoted, not just
in the driver's own output. This bit the PENCIL arc twice, in two different
mechanisms — a driver-level capped sweep (`outer.py --patterns`'s 4-of-8
reading, actually an artifact of a `cap=400` argument that never left split
index 0) and a *documentation*-level cap (a gap-map cell silently
approaching its character limit is the same hazard one level up) — which is
why it is a standing, harness-wide rule and not a one-off fix. **Canonical
home:** `notes/scripts/README.md` §4 convention 8, which carries both
incidents in full.

### 6. Mechanical word caps on status cells, with recompute-not-bump

**Any single status summary** — a gap-map cell, a phase note's own
`**Status:**` header block, any other one-object status paragraph — gets a
**hard, machine-checked word cap**, gated by a small script run before any
commit that edits it (PENCIL's `notes/check-gapmap-cells.py` for the gap-map
row, `notes/check-phase-note.py` for the phase-note header). The
point of the cap is not merely to bound length — it exists because, left
unchecked, a status cell reliably regresses from a *current-state*
paragraph into a *changelog* one landing at a time, via one specific,
now-named construction: **"Since Steps X–Y (direction Z), W changed" —
appended to the row rather than folded into it.** PENCIL's own worst row hit
this shape **five times** before the cap replaced ad hoc prose reminders, and
the phase note's `**Status:**` header — the same object with no cap on it —
did the same thing at one appended paragraph per landing, reaching 155 lines.

**The refinement a fifth regression forced (dispatch-log F21), stated as
its own clause because a cap alone does not catch it:** a cap bounds
*growth*, but it cannot express *purpose* — a recompute that lands one word
under the cap is gate-compliant and can still be pointless, if the room it
freed gets consumed by the very next landing already known to be queued.
So **dispatch a recompute with an explicit target** — a word count that
leaves headroom for landings already queued into that row, not merely
"under the cap" — and **verify label preservation by a scripted set-diff,
never by eye**: the coordinator's own hand-recompute dropped a live label,
and only a script caught it.

**Cap the cell, but also ship a READER for it (2026-08-26).** One row per gap
means one *physical line* per gap, so a compliant cell is still unreadable in
slices: `sed -n '<row>p'`, `grep '(GR-15)'` and every other line-oriented tool
deliver the whole 22 000-character row, measured at up to 20% of a
coordinator session's peak context for a single row. The fix is a read-only
slice reader beside the gate, not a reshaped table (the one-row-per-gap shape
is what §3 makes load-bearing): PENCIL's `notes/gapmap.py` answers *which rows
exist and what do they cost* (`--list`), *one cell, windowed by sentence*
(`--row … --cell status --head N`) and *only the sentences mentioning one
label* (`--label '(GR-15)'`) for 3–13% of the row's cost.

### 7. A coordinator prediction is a hypothesis — flag it as one, with its evidence stratum named

**Promoted 2026-08-26** from the *Candidates* tier at a fourth independent
instance. A coordinator authoring a dispatch spec is the party with the least
time on the question and the most authority over its framing, which is exactly
the combination that produces confident wrong predictions. In PENCIL's arc a
coordinator-authored prediction was refuted by the very direction it primed
**four times**: twice in the 2026-08-19 fan-out (an obstruction's location, an
obstruction's consequence), once at GHWIT (a `route` block's reduction clause,
false at a landed witness), and once at BZAVOID — where a two-part geometric
reading **split**, its dimension-count half refuted structurally and its
"deform off the canonical point" half surviving and getting priced. ZSHEAR then
made it four-for-four in the same session by deciding a coordinator-offered
*repair* negative.

**The rule, and it is about the framing rather than the accuracy.** A prediction
written into a spec must be labelled as **to be tested, not inherited**, and
must **name the stratum its evidence actually comes from**. That labelling is
what converts a wrong prediction from a silent contaminant into a legible
finding: BZAVOID's split was reportable *as a split* precisely because the spec
said which measurements the reading rested on, and every one of the four
dispatches tested rather than assumed the claim. The corollary already carried
here in §4 applies with full force — the corrective mechanism is the **next
pass**, not coordinator scrutiny — so the cheap move is to write the prediction
down *with its provenance* and let the dispatch kill it.

**The second half of the same finding: coordinator artifacts need the same
verification tier as a subagent's.** A coordinator-authored prep commit has
carried its own status-surface defects, caught only by a landing agent. Nothing
about authoring a spec exempts it from the checks a return gets. Full incident
record: `notes/dispatch-log.md` **F19** and the BZAVOID/ZSHEAR rows.

## Candidates, not yet promoted

One wave of evidence each, both from the 2026-08-19 fan-out (a third item, the
coordinator-predicted-obstruction category, was **promoted to *Ready* §7 on
2026-08-26** at a fourth instance and is no longer listed here). Watch for a
second instance before treating either of these as a standing rule; full
record in `notes/dispatch-log.md` *Findings* (do not duplicate that text
here — read it there):

- **The duplicate check, against landed Lean and against concurrent
  siblings.** A claim statable in the project's own idiom may already be a
  green theorem elsewhere in the tree, and two directions in one fan-out
  can independently derive the *same* identity in disjoint label ranges —
  label reservations (item 1 above) prevent a naming *collision*, not a
  mathematical *duplication*, which no gate, checker, or registry currently
  catches. `notes/dispatch-log.md` **F20**.
- **Cross-direction convergence as corroboration, not waste.** A parallel
  fan-out surfaces findings visible only in the *comparison* of independent
  returns — three of them in one PENCIL wave alone (two directions
  independently discovering they attack the same underlying inequality;
  two others independently landing on the same load-bearing lemma; a
  cap-exhaustion hazard recognized as harness-wide only because it hit
  twice in one week). The corollary this suggests, not yet re-tested: budget
  an explicit **cross-return pass** in verification, separate from each
  individual return's check, and choose directions in *different* sections
  so independence stays real. `notes/dispatch-log.md` **F18**/**F19**.

## Genuinely unsettled — deferred, question stated

These are open questions PENCIL's fan-outs raised without resolving.
Recording them here as *questions*, not as guesses dressed up as
guidance — inventing an answer would read as settled the moment it is
written down, which is worse than leaving the gap visible.

- **Optimal fan-out width.** PENCIL ran fan-outs of three and of five
  concurrent directions, both successfully, but never systematically
  varied the width against a fixed research budget. Is five near a
  ceiling (coordinator verification-pass cost, or independence quality,
  degrading past some N), or would a wider fan-out have paid off further?
  No data point in either direction yet.
- **The compute-licensed / derivation-first tier split.** PENCIL's
  fan-outs split concurrent directions into a "compute-licensed" tier
  (numerics-driver-heavy) and a "derivation-first" tier (prose-argument-
  heavy) for rung and framing purposes. Whether this split tracks a real
  difference in dispatch risk (and should inform rung choice generally) or
  is an artifact of how these five particular directions happened to be
  phrased is untested.
- **When a prose recon beats a compiler-checked spike.** For a Lean-facing
  route-composition question, `.claude/commands/coordinate-phase.md`
  already has a rule (dispatch a compiler-checked spike, not a prose
  recon). PENCIL's arc has no Lean at all, so the analogous question — when
  is a purely mathematical claim better settled by a prose derivation
  versus a from-scratch numerical/symbolic driver — never got a comparable
  answer. Left open.

## What this file is not

Not a checklist to run through mechanically at every commit of a research
phase — most of its items are properties of the *dispatch shape*
(fan-out mechanics, label discipline, status-object maintenance), decided
a handful of times per phase, not per commit. Not a substitute for reading
the active phase's own notes (`notes/PhaseN.md` *Hand-off*) for what to do
*next* — this file is about *how* to run the dispatches, not *which*
mathematics to attack.
