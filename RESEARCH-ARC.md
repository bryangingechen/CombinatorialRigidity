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

**What the read-only rule does NOT cover — three hazards, all from one round
(2026-09-02, the first three-wide concurrent round outside a prepared
fan-out).** "Read-only with respect to every shared file" protects the *writer*
from a concurrent *writer*. It says nothing about what a concurrent **reader**
sees, and all three of these bit in a single round. Recorded as one wave of
evidence, not yet promoted — but each is a mechanical fact about the harness
rather than a judgement call, so treat them as binding on the next concurrent
round and confirm rather than re-discover them:

- **Diff against `HEAD`, never the working tree.** A committing sibling leaves
  the tree dirty for its whole run, so a draft-only dispatch that measures a
  shared document measures an *uncommitted, mid-edit* state. One direction did
  this correctly for the gap map (`gapdiff.py <row> HEAD`) and incorrectly for
  the phase note in the same pass, and reported budget figures that were never
  a landed state.
- **The session scratchpad is SHARED.** Concurrent dispatches writing scratch
  files under default names overwrite each other mid-edit — verified by byte
  count, not inferred. Prefix every scratch file with the direction code, and
  re-verify any scratch input against `HEAD` before consuming it.
- **A shared monotone counter cannot be concurrently incremented.** Any
  "Nth instance" tally (§7's is the live example) is read-modify-write: three
  directions each read a baseline and added one, two of them claiming the same
  slot while the third read a stale source. The coordinator must reconcile such
  a counter *after* the round, in its own commit — and no direction should
  re-derive it.

- **`HEAD` itself moves mid-run when the coordinator lands serially inside a
  live round** *(added 2026-09-08, direction BSERIES; a **fourth** shape, and the
  only one the coordinator causes rather than the harness)*. Serial landing is
  what §2 prescribes, so a round of three where the first return lands while two
  siblings still run is the *recommended* procedure — and it silently invalidates
  every figure a still-running sibling measured against the old `HEAD`. It bit
  twice in one round, both times on a document cap: the second lander's
  gap-map-row delta and the third's whole recompute were computed against a
  baseline that had already moved. **The remedy is cheap and belongs in the
  spec:** tell each dispatch that `HEAD` may advance under it, and have every
  proposed doc-cap figure **re-taken at landing time** rather than at draft time.
  A sibling that reports its baseline sha (as BSERIES did) makes the staleness
  visible in one line; one that does not hands the coordinator a number that was
  true when it was written and is false when it lands. **The alternative — hold
  all landings until the round closes — trades this hazard for a worse one**
  (a session boundary losing every unlanded draft), so prefer re-taking figures.

**The general shape:** a concurrent round's defects concentrate in what the
dispatches **read**, not in what they write, and none of them is visible to any
gate or to any single return. Budget the **cross-return pass** (*Candidates*,
below) as the check that catches them — it is what caught all three here.

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

**THE SHARPENING A FIFTH PASS FORCED (2026-09-02, direction BSATUR), and it inverts
a test the coordinator had been using as REASSURANCE.** §4 says a claim needs a driver
that tests that exact sentence. The refinement: **a driver that ASSERTS a claim is only
as strong as the distribution it runs under.** PENCIL's own case, verified at source: a
clause of the form *"`c ≥ 2` never happens below `ρ = 6`"* was carried by a real
`assert` in a landed driver — `assert not (cuv >= 2 and r1 < 6)` — and it was a true
statement about **every draw that run made**. It was still false, because the sampler
drew the relevant plane **at random** and never ranged over the quantifier the clause
was about: the run varied the *configuration* and never the *flag*. The counterexample
sat one quantifier away from everything the driver could see.

**Why this is worth its own paragraph rather than a footnote to §4.** The coordinator's
dispatch spec for that very direction had cited *"the driver **asserts** the clause
rather than reporting it, so the run is a real assertion, not a silent pass"* as a
reason to weight the clause **higher** — and that reasoning was exactly backwards. An
assertion tells you the claim held wherever the sampler went; it tells you nothing about
where the sampler could not go, and it *feels* like stronger evidence precisely because
it would have halted the run. So: **when a claim's strength rests on an in-driver
assertion, name the sampler's support and ask which of the claim's own variables it
varies.** A claim quantified over an object the sampler holds fixed (or draws from one
fixed distribution) is untested in that direction, however many times the assert passed.
This is distinct from §4's original shape — there, *no* driver tested the sentence; here
a driver did, correctly, and the population was blind.

**A SECOND INSTANCE, 2026-09-03 (direction RPOOL), sharpening the rule for GENERATED
families.** A prior direction proved its claim per-shape on a witness `W19` and varied the
shape *family* around it. The refutation was `family_g(`**5**`, …)` where `W19` is
`family_g(`**4**`, …)` — **the same generator, one parameter along** (the core cycle one edge
longer) — and it had been sitting in that direction's **own recorded pool** since the day it
was built. So: **when a claim is proved per-shape over a family produced by a generator,
enumerate the generator's parameters and state which ones the evidence varied.** *"We tried
many shapes"* is not support; *"we varied `n` and the leg profile, never the core length"* is.
The counterexample is likeliest to sit one step along the axis nobody moved.

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

### 8. Kill conditions on forward-looking items — §6's blind spot

**§6 caps and gates every *status* surface. Nothing gates a *recommendation*
surface, and recommendations are what a coordinator actually reads to choose the
next dispatch.** That asymmetry is this file's newest promoted item, and it is a
mechanism rather than an empirical finding: it is justified by the failure it
prevents, which is demonstrated below.

**The failure mode, named.** A ranked list, option board, candidate menu, or
"highest-value remaining item" entry goes stale **silently**, because the thing
that kills it is a landing *somewhere else*. No author is in a position to
notice: the person who lands the killing result is not editing the list, and the
person reading the list has no signal that it moved. Status objects do not have
this problem — the gap map is *the artifact a new pass updates in place* (§3), so
a landing touches it by construction.

**The rule.** Every forward-looking entry carries, in the entry itself, two
clauses:

- **its kill condition** — *what result would retire this*; and
- **the status row that decides it** — the gap-map row (or workbook §) a reader
  checks to see whether that has happened.

Both are cheap at write time and impossible to reconstruct later: whoever
records a recommendation knows what would kill it, and today has nowhere to say
so. A **liveness sweep** — walk the lists, re-check each entry against its named
row — then becomes mechanical instead of a research task, and belongs in every
doc round.

**The evidence, stated honestly: three instances in one session (2026-09-03),
which is one wave, plus the structural argument that this is §6 applied to the
half of the documentation §6 never covered.** In PENCIL: `Pencil-strategy.md`
§5.3's item (i) was listed as the CAS layer's highest-value unrun item and had
been **dead since the day it was written** — the result that killed it, (D4),
landed the same day — surviving four weeks and costing a dispatch; §8's option
board, the file's designated *"every live route priced in one place"*, carried a
rank-3 row still naming a route refuted the previous day; and §8.2 and §8.6
contradicted each other on whether two shortlist entries were live. In the same
session a coordinator tried **three times** to pick a direction from those
surfaces and was misled every time, each item looking live where it is
*recommended* and spent one layer down. If this turns out PENCIL-specific,
that is a bug in this file per the tiering caveat above — but the mechanism is
general and the cost of the rule is one clause per entry.

**Two amendments the round's own sweeps forced, both earned rather than predicted.**

- **A do-not-re-run list needs a BACK-LINK to the lists still recommending its entries.**
  Forward kill clauses alone would not have caught PENCIL's worst instance: §8.6 *already*
  recorded §5.3's item (i) as ruled out, in the same file, while §5.3 four sections earlier
  offered it as the highest-value unrun item — and no reader of either could see the other.
  (§8.6's stated *cause* was wrong too, which is a second reason a back-link beats a
  duplicated verdict: one of the two copies will drift.)
- **Name the last ordinal, not an integer.** *"Unmoved since BSIGMA (ordinal 67)"* beats
  *"unmoved in sixteen landings"*: the first is checkable against the record and **decays
  visibly**, the second silently becomes wrong every time anything lands, and nobody is
  positioned to bump it. PENCIL had four such counters drift simultaneously, and two copies
  of one sentence reading *"sixteen"* and *"fifteen"*. Applies to any monotone count in a
  recommendation surface.

**The load-bearing evidence, and it is the round's real finding: the STATUS objects were
clean throughout.** Three sweeps flagged two suspected gap-map defects between them and
**neither survived coordinator scrutiny** — the map already stated the price inline in one
case, and was merely uncited (not miscited) in the other. Meanwhile the gap map had said
*"U1 is half delivered"* since the day after the shortlist calling U1 unrun was written. So
the rot was **entirely** in the recommendation layer, which is exactly what §6-plus-this-item
predicts: gate a surface and it stays correct; leave it ungated and it does not.

**Corollary — a gate that reports zero is not a gate that passes.**
`notes/check-log-rows.py` printed `OK: 0 row(s) checked` for weeks: it targeted
a log whose rows had been archived, and was hard-coded to that log's column
count. Both were invisible because the output said OK. When a gate's *scope* is
configuration, assert the scope, not just the verdict — the fix here derives the
column count from the table's own header and defaults to the live log.

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

**A FOURTH KIND of outcome, at the fifth instance: MOOT (2026-09-01,
direction BSPREAD).** The four instances above are three kinds — *refuted*,
*split*, *reframed*. BSPREAD's returned a fourth: the coordinator's route hypothesis
(restrict an over-claiming closure operator so a residual case disappears) was
**neither confirmed nor refuted — it was made unnecessary**, because the
direction proved the statement outright for the *unrestricted* operator and
three widenings of it. The hypothesis had priced its own cost honestly (a scope
change across every surface citing the statement); that cost was simply never
paid. Two things generalize. **The labelling is what made "moot" reportable
at all** — a prediction written down as *to be tested* can come back as *not
needed*, which an unlabelled assumption silently absorbs instead. And **a
hypothesis that proposes RETREATING to a weaker object is the shape most likely
to go moot**: it concedes the strong form before anyone has tried to prove it.
Where the coordinator's item did earn its keep was the *"where I expect to be
wrong"* clause — one of its three sub-items was right, and the direction cited
it as the reason the over-claiming operator was the better object to prove a
theorem about. Write the expectation down; let the dispatch decide which of the
four kinds it gets.

**A FIFTH AND SIXTH KIND, at the sixth and seventh instances (2026-09-01,
directions BONEONE and BGENUINE) — and the tally is repaired here, because it
had drifted.** BONEONE's landing recorded the tally as *six instances and five
kinds* while this file still said *fifth instance, four instances, three kinds*;
that drift is exactly the F12 shape §6 exists to catch, and it is fixed in this
paragraph rather than left to the next reader. The **fifth kind** is *refuted
with its own named escape clause vindicated* (BONEONE): the coordinator's route
hypothesis was wrong, and its own *"where I expect to be wrong"* item — *test
whether the disjointness is a generator artifact first* — is what produced the
landing. The **sixth kind** is subtler and is the one to watch for: *the framing
was right and load-bearing, and the stated TEST carried a dropped proviso*
(BGENUINE). The spec's asymmetry — a clause proved FOR an over-claiming operator
holds a fortiori, a witness exhibited AGAINST it is weaker — was correct and the
direction turned on it. But the spec's quoted criterion, *"does the coincidence
drop `dim(ρ̄₁+ρ̄₂)` below `min(δ₁+δ₂,6)`"*, had inherited a **proviso drop from a
summary surface** (a gap-map row quoting a lemma without its hypothesis), and
measured against that denominator a third of the witnesses read as violations.
**The lesson generalizes past this arc:** when a prep quotes a criterion, quote
it *with its hypotheses* or say which surface it was copied from — a prediction
can be right in shape and still hand the dispatch the wrong yardstick, and the
dispatch will not notice unless it re-derives the criterion from the lemma
rather than from the prep.

**A SEVENTH KIND, at the eighth instance (2026-09-02, direction BBASE):
*INAPPLICABLE* — a prediction that cites a landed theorem about a DIFFERENT
OBJECT.** All three of BBASE's readings were wrong, in three different ways, and
the middle one is the new kind. Readings (1) and (3) were *refuted* and
*corrected* — familiar shapes. Reading (2) said a landed theorem *"already
settles the cycles of length `≥ 4` verbatim"*; the theorem is true, the cycles
are real, and it **does not apply**, because its ambient carries structure only
at vertices of degree `≥ 3` while the object in question carries it at *every*
vertex. Nothing was false; the citation simply pointed at a neighbouring
variety. **Why this is worth its own kind:** a *refuted* reading fails a test the
dispatch runs, and a *reframed* one fails on inspection — but an **inapplicable**
one passes every check that stays inside the cited section, and is caught only by
opening the cited theorem's own **ambient definition** and asking whether the new
object is in it. It is the §4 *docstrings-are-not-evidence* rule one level up:
the hypothesis list of a cited theorem is not evidence about the object you are
citing it for. The practical instruction: when a prep says *"result X already
covers case Y"*, name the **ambient** X is stated over, not only X's hypotheses.
**AN EIGHTH KIND, at the seventeenth instance (2026-09-02, direction BLINE):
*UNDERSHOT* — the prediction was right in direction and WEAKER than the truth.**
The coordinator predicted that a `91/91` certification was no evidence, because
its population lay entirely inside the regime an older, weaker criterion already
covered. Premise confirmed at source; **middle inference refuted** (the two
criteria have *different loci* — `Σ_x` against the strictly larger `Π_x` — so the
newer one did prove something there); **conclusion confirmed for a stronger
reason** than the one given: on that population `(∗)` is a **theorem**, so the
certification is a *corollary*, not weak evidence. **Why this is a kind and not a
shade of *split*:** every kind above describes a prediction wrong in a way that
could mislead **upward** — a spec that over-claims contaminates the dispatch it
primes. UNDERSHOT misleads **downward**: inherited rather than tested, it would
have *understated* the finding, and the cost is not a false result but a real one
left unclaimed. It is therefore an argument for §7's labelling discipline from
the opposite side — write the prediction down not only so a wrong one can be
killed, but so a **timid** one can be beaten. The tell to watch for: a prediction
whose reasoning is *"X is already covered by the weaker Y"*, where the honest
answer turns out to be *"X is outright true here"*.

**RECONCILED 2026-09-08 AFTER THE CONCURRENT ROUND OF THREE: the tally runs to
TWENTY-SIX instances and STILL NINE KINDS — and declining to mint a tenth is itself
the decision.** All three directions of a three-wide round corrected the coordinator
prediction that primed them, which with the previous round makes it **eight for eight
across two rounds**. The classifications, and the reason none is new:

- **BSERIES** — **kind 6** (framing right, stated test carrying a dropped proviso), which
  the direction self-classified and the coordinator confirmed: *"run BWIN's machine at one
  peel"* was the right frame and never asked **which pieces have a series end at all**, which
  is precisely the case split the direction found.
- **BFOUR** — **kind 5** (refuted, with its own named clause vindicated), in a variant worth
  recording: the vindicated clause was not a *"where I expect to be wrong"* item but the
  spec's **value** clause — *"the value lies in what the chart population cannot reach"* —
  and following it to **why** the population could not reach is what produced the witness
  that killed the prediction. A prediction can be wrong and its stated *reason for asking*
  still be the thing that decides the question.
- **BINSERT** — **kind 2 (split), sub-shape *the mirror of UNDERSHOT***, and the direction
  offered a tenth kind here which the coordinator **declined**. Its structure mirrors kind 8
  exactly — premise confirmed and sharpened, middle inference refuted, conclusion
  **inverted** rather than confirmed-stronger — so it misleads **upward** where UNDERSHOT
  misleads downward. That is a new *direction* for an existing structure, not a new
  structure, and the last reconciliation's own closing lesson applies: *"the taxonomy is a
  diagnosis of one habit, not a checklist"*. Minting a kind per round would inflate the
  taxonomy's authority faster than its evidence. **The transferable instruction is the same
  one UNDERSHOT earns from the other side: say which clause of a three-part prediction is
  load-bearing**, because when the middle inference is the load-bearing one, the conclusion
  can invert while the premise stays true.

**Corrections ran both ways here too, and the coordinator's share grew.** Against those
three, landing-time verification caught the **same species in all three** returns — an
under-qualified summary on an authoritative status object — while the directions caught
**two coordinator defects**, one of them an *arithmetically impossible* instruction (a
compression target of 1,250 words against 219 undroppable labels). Three and two.
Full round record: `notes/Pencil-fanout.md`'s round-of-three state block.

**RECONCILED 2026-09-03 AFTER THE CONCURRENT ROUND OF FOUR: the tally runs to
TWENTY-THREE instances and NINE kinds.** The five new ones are one round's worth, which is
itself the finding — a four-direction round primed by one coordinator produced a
coordinator-prediction correction in **every** direction:

- **BSCOND** — *the ninth kind, and a new shape: **the dichotomy was too narrow**.* The spec
  framed the outcome as prove-or-refute and priced a refutation as *"it costs the window's
  class theorem its carrier and re-routes (β)"*. Reality took a **third** branch neither
  named: refutation and proof were the **same object**, and (BE-57)(i) came out **stronger
  with a hypothesis deleted**. The tell to watch: a spec offering two outcomes that *look*
  exhaustive because they are each other's negation, when the live possibility is that the
  question dissolves.
- **BARCH** — kind 1, **refuted**: the spec asked whether the `p_x`-free method class dies
  at `k ≥ 2` and primed death (*"if what made `A` `p_x`-free is gone by construction"*). It
  does not die; it **changes ambient**, and (BE-139)(iv)'s universal quantifier is what
  fails.
- **OBAR** — kind 1, **refuted**, on a mechanism the coordinator guessed: the spec named
  degree-`1` vertices as a likely second obstruction to (OC-35)-admissibility. A bar only
  **raises** degrees; the real obstruction is (σ7), one level up.
- **DSAT** — a **split**: the spec's *"say which stratum you trace on"* was right that the
  stratification decides the answer and **inverted** about which one — no `k`-stratum is the
  frame, the invariant is `def₃(G − a)`, and one object mixes `k = 3…9`.
- **GLEAF** — a **split**, and the useful kind: the board's rank-3 rationale was **right on
  reach and wrong on value**. Its own strike records the generalizable defect — *the entry
  priced a candidate by the machinery it reaches and never asked whether the statement
  reached is necessary or sufficient for its row.*

**And the round ran corrections in BOTH directions, which §7's second half predicts but had
not measured.** Against those five, the coordinator's landing-time verification caught four
direction-side defects that no gate could see, each an under-qualified summary on the
authoritative status object: BARCH's *"14 → 12 SURVIVES"* with (E4) unproved, OBAR's
chart-wide negative not naming (σ7)'s own 39/39 basis, DSAT's kill not separating its
**proved** (K-res) half from its **measured** class half, and GLEAF listing a **landed**
theorem (`Union_rank_eq`, heterogeneous at the very line it cited) among its owed bridges.
**Five and four, one round.** Neither party is the reliable one; the pairing is.

The tally previously ran to **eighteen instances and eight kinds** — the eighteenth
(2026-09-03, direction GELIM) a plain **refuted**, kind 1, and instructive for
*where* the refutation was found: the spec's own evidence-stratum clause said
the coordinator had **not opened §(K-dom)**, and §(K-dom) *Step D4* is exactly
where the prediction died. Naming the stratum did not make the prediction right;
it told the dispatch which section to open first, and it was refuted in one read
before any computation. That is the cheapest possible outcome for a wrong
prediction, and it is what §7 is for. Reconciled
2026-09-02, when this line was found **stale by six**. That staleness is
itself the finding: three concurrent directions landing the same day each
read a different baseline for it (two claimed the same slot, one read the
stale figure here), so the count is now maintained here and cited, never
re-derived per direction. See §2's *What the read-only rule does not
cover*, and `notes/dispatch-log.md`.

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
