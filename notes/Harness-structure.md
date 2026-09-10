# Harness + PENCIL doc-set structural round (work log)

**Status: ALL SEVEN SLICES (8–14) LANDED 2026-09-09, plus a defect-fix pass an
adversarial review forced — three CRITICAL bugs in the shipped ledger, all
reproduced and fixed (see *The review pass* at the end). The round is COMPLETE.** Slice 8 — `notes/ledger.py`, 1 308
claims across five files, ~0.2 s regeneration, cache gitignored. Slice 9 — the
bracketed status vocabulary and `--lint`, gating the new form only. Slice 12 —
`notes/Pencil-informal.md` split into 62 files under `notes/pencil/workbook/`,
content byte-identical, 1 308 claims before and after. Slice 13 — the rest of
the corpus moved under `notes/pencil/`, a subtree `CLAUDE.md` added, and
`notes/CLAUDE.md` trimmed 425 → 321 lines. Slice 11 — `--round` emits a generated
briefing packet and `--reserve` mechanizes the 0-hit label check. Slice 14 — `/coordinate-research`
and the `research-direction` agent family. Slice 10 — **re-scoped by
measurement** from a batch conversion to a ranked reading worklist
(`--backlog`), which is the honest shape; see its entry. Promotion to
`RESEARCH-ARC.md` is the remaining work and waits on a second research-shaped
phase, per that file's own three-tier rule. Opened 2026-09-09 at the user's
request after Phase 39's dispatch costs were measured. Slices are numbered
8–14, continuing `notes/pencil/structure.md`'s slice numbering; this is a
separate file because the round's deliverables are **cross-phase** (a
derived-ledger layer, a split coordinator command, a new agent core, a
status vocabulary with a gate) rather than PENCIL file layout alone, which
is what slices 1–7 were. `notes/pencil/structure.md` carries the pointer.**

Round discipline is `CLEANUP.md`'s, per the slice-3 precedent: a
*structural* round (layout / navigability / cross-phase promotion), not a
defect-cleanup round.

## Why this round — the measured diagnosis

Not a hunch. Every number below is from the local session transcripts for
the four `/coordinate-phase 39` sessions of 2026-09-02 → 2026-09-09, or
from a census of the corpus itself. They are recorded here because the
round's slices are each justified by one of them, and a later reader
should be able to check whether the slice paid.

### D1 — the coordinator spends 120–190k tokens before its first dispatch

| session | context at start | context at first dispatch | dispatches | context at end |
|---|---|---|---|---|
| 2026-09-09 | 61k | **180k** | 4 | 400k |
| 2026-09-08 | 61k | **230k** | 7 | 565k |
| 2026-09-03a | 61k | **196k** | 7 | 546k |
| 2026-09-03b | 61k | **253k** | 5 | 503k |

The 61k floor is the system prompt + tool schemas + the auto-loaded root
`CLAUDE.md` + the 635-line `/coordinate-phase` body. Everything above it is
orientation the coordinator re-derives every session.

### D2 — each direction agent spends ~175k tokens before writing a line

Start 36k → first file write at 147k–358k (median ≈ 210k) across eleven
sampled dispatches. Tracing one (direction BNONUNI, 2026-09-09) call by
call:

- calls 3–6 — **`RESEARCH-ARC.md` read end-to-end**, ~15k tokens of
  *process* doc;
- calls 7–13 — `notes/Phase39.md` + `notes/pencil/strategy.md` §8, ~14k;
- calls 25–28 — `notes/scripts/README.md` conventions, ~7k;
- calls 14–56 — **~35 `grep`→`sed` probes** into the 41 343-line workbook,
  recovering the statements of ~18 prior `(BE-·)` claims.

The last block read only ~11k tokens of *content* but grew context by
**137k**, because each probe carries its own reasoning turn. Output tokens
(200–400k per dispatch) dominate input. **The cost is turns, not bytes** —
which is why "read less" is the wrong prescription and "answer it in one
call" is the right one.

### D3 — half the corpus's claims carry no machine-readable status

Census of the `> **(LABEL)(clause)**` openers across the doc set:

| file | openers | distinct labels |
|---|---|---|
| `Pencil-informal.md` | 1 019 | 415 |
| `pencil/workbook/grid.md` | 232 | 165 |
| `pencil/workbook/W4.md` | 22 | 22 |
| `pencil/strategy.md` | 7 | 7 |
| `pencil/fanout.md` | 14 | 12 |

In the main workbook: only **543 of 1 019 openers (53%)** carry any
parenthetical status tag at all, and those 543 use **188 distinct
tag-heads**, of which only ~300 occurrences begin with a status word. One
concept has four spellings — `PROVEN` (129), `PROVED` (61), `PROVED by
exhaustion` (9), `proven-informally` (35) — beside a freeform editorial
tail (`the board`, `the price`, `the reading`, `the E-rider`, `what did
not move`).

**This is the direct cause of "agents get confused about what is proved."**
An agent asking whether `(BE-189)` is proved has no retrieval method except
reading the surrounding prose, because for 47% of claims there is nothing
else to read. D2's archaeology is not carelessness; it is the only
mechanism available.

### D4 — the coordinator command is formalization-shaped

`.claude/commands/coordinate-phase.md` is 635 lines / ~10k tokens. **84% of
its paragraph blocks reference Lean or blueprint machinery** — S/P/B rating
calibrated on proof novelty, the rung map's fragility zone (a list of
`.lean` directories), `lake build` / `lake lint` / sorry-grep verification
tiers, the additive-successor and supersession-deletion blueprint checks,
`checkdecls`, `\leanok` flipping. Phase 39 has **no Lean and no blueprint**.
Its research content is a handful of paragraphs inside step 1 that mostly
delegate to `RESEARCH-ARC.md`.

Every dispatch pays for this twice: once in the coordinator's own prefix,
and again in the `recon` / `phase-builder` cores, which carry build
discipline (`lean_run_code` witnesses, compiler-checked spikes, gate
mechanics) a read-only research direction cannot use.

### D5 — the split axis is already there

`Pencil-informal.md`'s 70 `##` sections divide cleanly:

- **37 sections / 21 743 lines (53% of the file)** are
  `§(K-bare-ext) — continuation (direction XXXX)` — an append log, one
  section per direction, 650–900 lines each;
- **33 sections** are the topical gaps (`§(K-out)` 4 508 lines, `§(K-mech)`
  1 890, `§(K-frame)` 1 683, `§(K-ann)` 1 528, `§(K-Λ)` 1 350, …), almost
  all one section per gap;
- the *State of (K)* gap map is 29 rows on 29 physical lines totalling
  110 503 characters — one row is one 22 000-character line, which is why
  it needs `notes/gapmap.py` and cannot be `sed`'d.

A direction reads its own section and the gap map. It reads the other 36
directions' sections only because they share a file.

## What this round does NOT do

Stated first, because a structural round's failure mode is scope drift.

- **No mathematics changes.** No claim is restated, strengthened, weakened,
  retired or re-derived. A slice that finds itself arguing about `(K)` has
  left its scope.
- **No status verdict changes.** Slice 10's backfill *records* the status a
  claim already has, read from its own prose. Where the prose does not
  determine a status, the ledger says `UNTAGGED` and the claim is left
  alone — inventing a verdict is the one unrecoverable error available to
  this round.
- **No figure moves.** `notes/scripts/README.md` *Hard rule — figures do
  not move* binds every slice; slices that touch `notes/scripts/` discharge
  it in the commit message as usual.
- **No phase close, no phase open.** Phase 39 stays in progress throughout.
- **No new mathematics tooling.** The ledger indexes claims; it does not
  check them. Drivers remain the only evidence for `ASSERTED` / `MEASURED`.

## Target layout

```
notes/pencil/                     PENCIL asset root
  CLAUDE.md                       ~60 lines: ledger CLI, canonical homes, round map
  README.md                       navigation index (generated section + prose)
  workbook/
    gapmap.md                     the State of (K) table, lifted out
    K-out.md K-mech.md K-frame.md …        33 topical gap sections
    bare-ext/BEFOURP.md BEARFULL.md …      37 direction continuations
    grid.md                       was pencil/workbook/grid.md
    W4.md                         was pencil/workbook/W4.md
  strategy.md labels.md fanout.md fanout-archive.md
  adjudications.md structure.md cleanup.md
  (no ledger file — the cache is gitignored, see slice 8)
  rounds/NNN-<DIRECTION>.md       generated briefing packets
notes/ledger.py                   generator + query CLI
notes/gapmap.py                   retargeted at notes/pencil/workbook/gapmap.md
.claude/commands/coordinate-research.md
.claude/agents-core/research-direction.md
.claude/agents/research-direction-{opus,fable}.md
```

The split is only safe **because** the ledger exists: retrieval stops
depending on everything sharing one file. Hence the slice order below —
ledger before split, never the reverse.

## Slices

Each slice is one commit unless stated. Every slice runs the standing
per-commit checklists (`CLAUDE.md` *Before each commit*) plus the gates in
`notes/pencil/structure.md` *Gates for any continuation*.

### Slice 8 — the claim ledger and its query CLI  *(LANDED 2026-09-09)*

**What landed.** `notes/ledger.py` — 1 308 claims across the five source
files (`Pencil-informal` 1 038, `-grid` 232, `W4` 22, `strategy` 7, `fanout`
9), regenerating in ~0.2 s into a gitignored `notes/.ledger-cache/`. Measured
against the traced BNONUNI dispatch it replaces: **14 labels briefed in one
call for ~7 600 tokens**, against the ~137k that dispatch spent on ~35 probes
for ~18 labels.

The status census it produced is the slice-10 backfill's worklist:
**UNTAGGED 666 (50.9%)**, PROVED 447, MEASURED 109, INFORMAL 56, CONSTRUCTED
12, REFUTED 11, OPEN 5, ASSERTED 1, CONJECTURED 1. Of the 666 untagged, 441
*do* carry a parenthetical whose leading token simply is not a status word
(`the board`, `the price`, `classification`, `the E-rider`); the other 225
carry no parenthetical at all.

**Four corpus shapes the implementation found, each of which would have
produced a wrong ledger** — recorded because three of them bear on later
slices:

1. **Bolded prose is not an opener.** `> **(CH-1)'s girth ≥ 4 excludes**`
   looks like a label opener; 158 lines do. Requiring the bold to close
   immediately after the label cuts 1 177 candidates to 942 real openers.
2. **Bare `(i)`/`(ii)`/`(c)` openers are sub-clauses**, not labels (96
   occurrences). A parser that takes them at face value invents an `ii`
   family. Five in the fan-out write-ups have no parent label at all — those
   are narrative bullets and are correctly dropped; `--selftest` counts them
   so the arithmetic still closes.
3. **41% of tag parentheticals do not close on their opening line** (378 of
   921). The tag needs a balanced-paren scan with inline code masked; the
   throwaway prototype used in the plan's diagnosis truncated all 378, which
   is why that census over-reported freeform tag-heads.
4. **Section headings are themselves status surfaces** — see slice 12, where
   this changes the argument.

**Status is read from the tag's LEADING TOKEN only.** `*(proven; and
enumerated …)*` is PROVED; `*(two NEGATIVE CONTROLS, both asserted)*` is
UNTAGGED, because a claim's status is not to be guessed from a word appearing
somewhere inside its editorial gloss. This is the plan's *no invented verdict*
rule made mechanical, and it is why the UNTAGGED share (51%) is slightly
higher than the plan's estimate (47%).

### Slice 8 — as originally specified  *(retained for the record)*

**Deliverable.** `notes/ledger.py` — a generator + query CLI. **The ledger
itself is NOT checked in**; it is regenerated into a gitignored cache
(`notes/.ledger-cache/`) whenever the CLI notices a source file is newer than
the cache. Generation over the whole 2.8 MB workbook measures **0.2 s**, so
"regenerate" is the cheap path and there is no reason to store the result.

One row per label-clause opener: `label`, `clause`, `status`,
`evidence` (driver name / witness / cited label, when the tag carries one),
`file`, `section`, `step`, `claim` (the opener's first sentence, truncated),
`cites` (labels appearing in the clause body).

**No `line` column — this was measured, and it is the schema's one real
trap.** A stored line number shifts for every row below any mid-file edit.
Regenerating the ledger at HEAD and at a commit twenty workbook landings back:
with a `line` column, **165% of rows change** (the whole file is rewritten
each landing); without it, **36%** — of which 35 points are *genuinely new
rows* (673 → 1 038), leaving real churn at roughly **six rows**. Locations are
resolved at *query* time instead: the CLI greps the opener's exact string, so
`--label` output carries a live, always-correct line number that no artifact
has to keep in sync.

**Why not check it in — three reasons, in order of weight.**

1. **It would be one more summary surface.** This corpus's documented
   pathology is a summary disagreeing with the body prose it summarizes —
   dispatch-log F12, and the BDECOR incident where a product theorem's proviso
   dropped on **six** summary surfaces at once while the body prose stayed
   correct, so no gate could fire. A ledger that is always regenerated from
   the prose **cannot** drift from it; a checked-in one can, and would need a
   gate to police a hazard that only exists because it was checked in.
2. **It matches the project's own precedent.** No derived artifact is checked
   in today: `notes/scripts/README.md` records a driver command and its
   runtime, and the *figure* lives in workbook prose. `.gitignore` carries
   build artifacts and local PDFs, nothing generated from the corpus. The
   ledger is a driver output like any other.
3. **Storage, which is the smallest reason.** Twenty committed revisions pack
   to 35.9 KiB without the `line` column (59.8 KiB with it). At the measured
   107 workbook landings per month that is ~190 KiB/month, ~2.3 MB/year
   against today's 22.9 MiB pack — real but not a blow-up. It is listed third
   because it would be worth paying if reasons 1 and 2 went the other way.

**Reviewability is kept without the file.** `notes/ledger.py --delta <ref>`
prints the status change-set against a git ref —
`(BE-216)(i) UNTAGGED → PROVED`, `(BE-215)(i) OPEN → REFUTED (BE-214 witness)`
— and the landing agent pastes it into its commit message. The progress record
then lives in git history, where this phase already keeps its landing
narratives, and it is *generated*, so it cannot overstate what moved.

Queries, each a single call answering what D2 spent 35 calls on:

| query | answers |
|---|---|
| `--label '(BE-189)'` | every clause of one label, full text |
| `--status OPEN --section '(K-bare-ext)'` | what is unproved, where |
| `--frontier` | open claims whose every citation is `PROVED` |
| `--cited-by '(BE-216)'` | what breaks if this claim falls |
| `--since <sha>` | what moved since a commit |
| `--brief '(BE-216)' '(BE-207)' …` | briefing-packet block for a label set |

**`UNTAGGED` is a first-class status from day one.** The ledger is useful
before any backfill: it tells a direction exactly which claims it must read
prose for, which is strictly better than today's "all of them."

**No `--verify` gate, because there is nothing to verify.** A cache that is
regenerated whenever its source is newer cannot disagree with the source. The
only gate this slice adds is slice 9's tag lint, which checks the *prose*, not
an artifact. That is one fewer gate than the plan originally carried, and the
one it drops was self-inflicted.

**Why first.** It is additive, reversible, unblocks slices 9/11/12, and pays
on the very next dispatch with nothing else in place.

### Slice 9 — the status vocabulary  *(LANDED 2026-09-09)*

**What landed.** The bracketed form, parsed ahead of the gloss so editorial
voice survives (`> **(BE-216)(i)** `[PROVED]` *(the sum is hypothesis-free)*`),
plus `notes/ledger.py --lint`. Verified against seven fixtures: a well-formed
`[PROVED]` passes; `[MEASURED]` without a driver fails; `[MEASURED]` naming one
passes; `[PROVEN]` fails as out-of-vocabulary with the legal set printed;
`[REFUTED]` without a witness fails; `[REFUTED]` naming one passes; a legacy
freeform tag is reported UNTAGGED and does not fail.

**The gate binds the BRACKETED FORM ONLY**, decided by measurement rather than
taste: only **42%** of the corpus's existing MEASURED claims name a driver
anywhere in their clause (15% name one in the tag). A retroactive rule would
fail correct prose and be switched off rather than obeyed — the failure mode
the original spec below already warned about. An author who opts into
`[MEASURED]` opts into naming the driver; legacy tags stay ungated until
slice 10 converts them, and conversion is where the naming gets added.

**Two defects in slice 8 were found and fixed here**, both by building the
gate rather than by review:

- **`--brief` was truncating at 400 characters** while the median clause is
  785, so **970 of 1 141 clauses** were quoted mid-sentence. A briefing packet
  that silently drops the tail of a claim drops exactly the provisos it exists
  to preserve — the BGENUINE failure, reintroduced by the tool built to
  prevent it. The full clause is now stored; truncation is a display concern,
  applies only to scanning views, and says `…[+N chars; --full]` when it fires.
- **The identity key was not unique.** Five label-clauses are stated twice
  inside one section (mostly a claim restated in the section's own
  *Verification* block), so a colliding key silently dropped one row from
  `--delta` and reported the other as changed on every run. Rows now carry an
  occurrence ordinal, assigned in document order and stable under appends.

A third, subtler one was caught by the fixtures: the `[REFUTED] must name a
witness` check was satisfied by the **status bracket's own backticks**, so a
clause naming nothing passed. The bracket is now stripped before the
obligation is checked.

### Slice 9 — as originally specified  *(retained for the record)*

A closed vocabulary, written as a bracketed tag **before** the existing
parenthetical, so editorial voice survives:

```
> **(BE-216)(i)** `[PROVED]` *(the sum is hypothesis-free)* At a firing side …
```

| tag | means | must name |
|---|---|---|
| `PROVED` | complete argument in the workbook | — |
| `PROVED-MOD` | complete modulo a named cited claim | the label |
| `INFORMAL` | argued, gap acknowledged (today's `proven-informally`) | the gap |
| `ASSERTED` | checked by a driver at named instances | the driver |
| `MEASURED` | a census/figure a driver produced; no generality claimed | the driver |
| `CONSTRUCTED` | an object exhibited | the driver or the construction |
| `CONJECTURED` | stated, no evidence | — |
| `REFUTED` | killed | the witness |
| `MOOT` / `RETIRED` | superseded or made unnecessary | the successor |
| `OPEN` | live, unattempted or unfinished | — |

This is not a new discipline; it **mechanizes three the phase already
promoted**: `RESEARCH-ARC.md` §4 (a driver per headline sentence), §7 (name
the evidence stratum the claim rests on), and the 2026-09-09 sharpening that
*a kill condition naming a number must carry its derivation* (commit
`483f9787`). The obligation columns are those rules made checkable.

**Gate.** `notes/ledger.py --lint` rejects a **new or edited** opener whose
tag is outside the vocabulary or omits a required name. It reads the workbook
prose directly — there is no stored artifact in the loop. Pre-existing openers
are grandfathered as `UNTAGGED`: the gate must not fail the tree on day one,
or it will be disabled instead of obeyed. Like the other two docs gates it
inspects changed-vs-`HEAD` files by default and so must be **run before
committing, or with `--all`** (`pencil/structure.md` *Gates for any
continuation*, blind spot 1).

### Slice 10 — the tagging backlog  *(RE-SCOPED, then LANDED 2026-09-09)*

**The original plan was to convert the legacy tags in bulk. A measurement
retired that.** **642 claims already classify correctly from their legacy
freeform tag** (`*(proven)*`, `*(measured)*`, `*(PROVED by exhaustion)*`),
because the leading-token rule reads them — 453 of those at obligation-free
statuses. Converting them to the bracketed form would have edited hundreds of
mathematical claims and changed **no tool output whatsoever**: same status,
same `--brief`, same `--frontier`. The entire value sits in the **645 claims
with no recognizable status**, and those need *reading*, not rewriting.

So slice 10 ships as a **worklist, not a batch**: `ledger.py --backlog` ranks
the untagged claims by how many other claims cite their label, so the reading
starts where the corpus leans hardest — `(BE-22)(v)` at 45 citations,
`(BE-101)(ii)` at 44, `(CH-1)` at 37. Tagging happens **per landing, by the
direction that touches the claim**, with the standing rule that a claim is
tagged only when its own prose is decisive and `UNTAGGED` is a legitimate
terminal state. `--lint` already stops the untagged share from growing, which
is what made the batch unnecessary.

**A parser defect surfaced while assessing this slice, and is fixed here.**
`(BE-14)` — the corpus's most-cited label — showed **two** rows under
`--label`, one of them a fragment beginning mid-sentence with a comma. The
source is a bolded label opening a **prose list**
(`> **(BE-14)**, \`hbareSplit\`, the 2-cut composition lemma … are untouched`),
which passes the opener test because the bold does close right after the
label. **21 rows across the corpus were this shape.** They were harmless in
the way that matters — every one came out `UNTAGGED`, because the
leading-token rule refuses to guess a status — but they inflated the count and
put a phantom row beside a real claim. A genuine claim never opens with list
punctuation or a lowercase continuation, and a *tagged* opener is a claim
whatever follows, so the filter applies only to untagged ones. `--selftest`
now reconciles them per file, as it already did for unattached sub-items.
Corpus count: 1 308 → **1 287**.

### Slice 10 — as originally specified  *(retained for the record)*

Mechanical where the prose is decisive (`**PROVED**` → `[PROVED]`,
`proven-informally` → `[INFORMAL]`), by reading where it is not. **Any
opener whose own prose does not determine a status stays `UNTAGGED`** and is
listed in the slice's commit message. This slice may run in the background
across several sessions; it blocks nothing.

Not a dispatch target for a research direction — a direction backfilling
tags is a direction not doing mathematics.

### Slice 11 — generated briefing packets  *(LANDED 2026-09-09)*

**What landed.** `ledger.py --round N --direction D --labels …` emits a packet
whose IN SCOPE claims are quoted **in full, from the claims' own prose**, with
their tags, citations and live line numbers; everything the coordinator must
supply is an ALL-CAPS placeholder (the question, the reservation, the harness
entry points, the prediction, the deliverable). A two-label packet measures
**5 683 characters (~1 420 tokens)** against the ~36k of orientation prose a
dispatch reads today.

The generated-not-retyped property is the point, not the formatting: §7's
BGENUINE incident was a criterion quoted **without its hypotheses** from a
summary surface, which handed the dispatch the wrong yardstick. Quoting from
the ledger makes that failure unavailable by construction. The packet also
carries §7's requirement that the coordinator's prediction be labelled *to be
tested, not inherited*, with the stratum of its evidence named, and lists all
seven outcome kinds §7 has recorded.

**`--reserve` mechanizes a discipline that was manual.** `RESEARCH-ARC.md` §1
requires a proposed label prefix be verified 0-hit as a raw substring across
the **whole corpus** — not just against the siblings in flight, because a
reservation protects a dispatch from its siblings and not from what is already
written. `--reserve 'QZX-'` checks 495 files and reports clean or names the
colliding files with counts.

**A side effect of slice 12 shows up here.** The packet's line pointers now
land in small files — `bare-ext/BEFOURP.md:703` where the same claim was
`Pencil-informal.md:40323` — so a reader who does open the source opens 900
lines, not 41 343.

### Slice 11 — as originally specified  *(retained for the record)*

`notes/ledger.py --brief` emits `notes/pencil/rounds/NNN-<DIR>.md`, ≤5k
tokens: the question; **the in-scope claims' statements pasted verbatim from
the ledger, with their hypotheses and line pointers**; the reserved
namespace; the harness entry points (which drivers, which functions); the
deliverable and gates; and an explicit *"this is your context — do not read
the workbook or `RESEARCH-ARC.md` end-to-end."*

This also attacks spec quality, which is the round's second motivation and
is measured too. `RESEARCH-ARC.md` §7 records **eight** coordinator
predictions refuted across seven kinds, and BGENUINE's was precisely *a
criterion quoted without its hypotheses, copied from a summary surface*.
When the statements are **generated from the ledger** rather than retyped by
a coordinator, that failure mode is unavailable by construction, and the
coordinator's freeform prose shrinks to the question plus a prediction block
that §7 already requires be labelled *to be tested, not inherited*.

### Slice 12 — split the workbook  *(LANDED 2026-09-09)*

**What landed.** `notes/Pencil-informal.md` (41 343 lines, 2.8 MB) is now 62
files under `notes/pencil/workbook/`: 20 topical gap sections, the base
`K-bare-ext.md`, **36** direction continuations under `bare-ext/` named by
direction code, plus `gapmap.md`, `dictionary.md` and a generated `README.md`.

*(Correction to D5, which this slice's own measurement fixes: the file has
**36** `§(K-bare-ext)` direction continuations plus **one base section**, not
37 continuations. The 37 was a count of headings, not of continuations.)*

**Content integrity, checked three ways and all three green:**

- **Byte-identical reconstruction.** Concatenating the 62 parts in document
  order reproduces the source exactly (verified before any rewriting).
- **Byte-identical after the intended rewrites.** Applying the same path
  rewrites to the pre-split original and comparing against the concatenated
  split gives an exact match at **2 749 129 characters** — so the ONLY textual
  change is the path repointing.
- **1 308 claims before, 1 308 after**, and `notes/scripts/gapdiff.py` reports
  **294 gap-map labels in, 294 out, 0 dropped** across the move.

**A structural finding that changed the split.** Nine `##` headings are not
sections at all — six `TERMINATION check (E1/E2/E3)` plus `Riders`,
`Shelf effect` and `Secondary deliverable` are sub-parts of the direction
write-up they sit inside, written as `##` instead of `###`. A first pass split
on every `##` and produced 71 parts including six files with colliding names
and three orphans torn from their context. The splitter now breaks only at
`## §(…)` (plus the three head sections), which is why it is 62 and not 71.

**The stale index, which is a fourth argument for this slice.** The file
carried a hand-maintained *Section index* with line ranges, and **19 of its 20
rows had a wrong start line** — drifting +10 on sixteen rows and +200, +200,
+493 on the last three. The index's own header conceded the problem (*"Line
ranges are as of this commit — if one looks wrong, grep the `## §(…)`
heading"*). `README.md` replaces that column with file paths, which cannot
drift, and the status and tag columns move over verbatim.

**Reference repair: 230 rewrites across 42 files.** Resolution was not
guessed — a step→file and section→file map built from the split itself
resolved **166 (72%)** to an exact file (78 via a `*Step X*` citation, 88 via
a `§(…)` qualifier); the remaining 64 generic mentions and 17 ambiguous
`§(K-bare-ext)` references point at the workbook directory, which is honest
rather than precise.

**A live tool was broken by the move and is fixed here.**
`notes/scripts/gapdiff.py` — the gate `notes/pencil/structure.md` names as
*"the one that actually looks at content"* — hard-coded the workbook path and
died with a traceback. It now falls back to the pre-split path when a ref
predates the move, so the one gate that compares gap-map content still works
*across* the boundary rather than failing exactly when asked to span it.
`check-gapmap-cells.py`, `gapmap.py` and `ledger.py` were retargeted too;
`ledger.py`'s source list is now a glob, so a new direction's file is indexed
with no edit.

**40 references used a bare `Pencil-informal.md` without the `notes/` prefix**
and so were missed by the path rewriter. They were sorted by hand: the live
ones (in `notes/CLAUDE.md`, `notes/scripts/README.md`, `pencil/labels.md`,
four drivers and three Macaulay2 files) are repointed; the ones in
`pencil/cleanup.md`, `pencil/structure.md` and this file's own measurement
tables are **retirement history** and correctly keep the old name.

**The discipline that genuinely changed, repaired in the same commit.**
`RESEARCH-ARC.md` §3's corollary and `notes/dispatch-log.md` F12 both said
*"grep the whole file for the same stale claim"*. After the split that is a
TREE, and both now say so — with the cheaper form named
(`ledger.py --cited-by`, one call, corpus-wide). A rule that silently becomes
weaker at a file move is worse than one that is deleted.

**Figure invariance discharged**: the 27 touched `.py`/`.m2` files are
docstring/comment-only path repairs, verified line by line — no driver's
computation changed and no recorded figure moved.

### Slice 12 — as originally specified  *(retained for the record)*

**Slice 8 turned up a new and stronger argument for this slice, from an
unexpected direction: claim IDENTITY.** Building `--delta` forced the question
*what makes two claims the same claim across two revisions?*, and the
single-file layout makes that genuinely hard in three compounding ways.

- A section's identity cannot be its heading, because **headings are rewritten
  in place as directions land** — `§(K-dom)`'s grew an entire new clause when
  DSAT landed, and `§(K-ins)`'s was rewritten when INSJOINT landed. Keying on
  heading text produced **500+ phantom add/removes**.
- It cannot be the label alone either: **20 labels are claimed in more than
  one section** (`(BE-41)` in four, `(CH-1)` in three), so a label-keyed diff
  collapses them and **invented three status transitions on claims whose
  status never moved**.
- What works is a synthetic key — the gap token plus the direction code,
  `§(K-bare-ext)/BEFOURP` — reconstructed by regex from prose on every run,
  plus a relocation pass to stop a section move (RESGRID's six `(RS-·)`
  claims) reading as six deletions.

**Every line of that machinery exists to reconstruct what a file path would
have given for free.** If each direction continuation and each topical gap
were its own file, the path *is* the stable identity: no synthetic key, no
heading-rewrite fragility, no collision ambiguity, and `locate()` collapses to
a grep of one small file. The split does not merely make retrieval cheaper —
**it removes a class of identity bug the single-file layout creates.**

This is now the second independent argument for slice 12 (the first being
D2/D5's retrieval cost), and it is the better one, because it is about
correctness rather than tokens.

Per D5: 37 direction sections to `workbook/bare-ext/<DIR>.md`, 33 topical
sections to `workbook/<gap>.md`, the gap map to `workbook/gapmap.md`.
Content moves **verbatim** — a slice that edits prose while moving it cannot
be reviewed.

**Cross-reference repair, in the same commit.** 1 236 inbound mentions
across the doc set to the moving files:

| file | mentions | files |
|---|---|---|
| `Pencil-informal.md` | 265 | 47 |
| `pencil/strategy.md` | 224 | 35 |
| `pencil/fanout.md` | 217 | 33 |
| `pencil/labels.md` | 166 | 38 |
| `pencil/workbook/grid.md` | 109 | 29 |
| `pencil/fanout-archive.md` | 106 | 17 |
| `pencil/workbook/W4.md` | 63 | 16 |
| `pencil/structure.md` | 50 | 12 |
| `pencil/adjudications.md` | 30 | 7 |
| `gapmap.py` | 16 | 11 |
| `pencil/cleanup.md` | 4 | 2 |

Path repair is `sed`-mechanical; **section citations (`§(K-out)`, step
names, label tokens) survive the split unchanged**, which is what makes this
affordable. Retarget `notes/gapmap.py` (its `PATH` default and docstring),
`notes/check-gapmap-cells.py` (`PATH` at line 143 and its two message
strings), and `notes/scripts/scriptpath.py`'s docstring.

**One discipline genuinely changes, and it must be rewritten in the same
commit.** Several rules say *"grep the whole file for the same stale
claim"* — dispatch-log F12 and `RESEARCH-ARC.md` §3's corollary most
importantly. After the split that is **grep the tree**. A rule that silently
becomes weaker is worse than one that is deleted.

**Verification.** Byte-identical content: `cat` the split files in order and
diff against the pre-split original, modulo the inserted per-file headers.
Zero remaining hits for the old paths outside a retirement-history note.

### Slice 13 — move the rest, add `notes/pencil/CLAUDE.md`  *(LANDED 2026-09-09)*

**What landed.** Ten files moved into `notes/pencil/`, with **1 005 reference
rewrites across 134 files**. `notes/pencil/CLAUDE.md` (92 lines) is the
subtree manual and auto-loads only when the corpus is touched;
`notes/CLAUDE.md` drops **425 → 321 lines** as its 119-line PENCIL catalogue
becomes a pointer — so a session that never opens the corpus stops paying for
its file list on every `notes/` touch.

**`grid.md` and `W4.md` moved unsplit**, deliberately: `grid.md` is 97% a
single `§(K-grid)` section and `W4.md`'s arc is closed and parked, so splitting
them further would restructure sections rather than move them — outside a
structural round's scope. One-file-per-section earns its keep where 62 sections
share a file and concurrent directions append to it, which is the case slice 12
addressed.

**Three defects the verification pass caught**, and the pass is the finding
worth keeping. Checking that all **5 248** path references in the tree resolve
turned up:

- **A line-wrapped reference.** `notes/scripts/w4/dominance.py` cited
  ``` `notes/Pencil-
informal.md` ``` broken across a line, so no
  path-substitution rewriter could see it. This is the failure mode a
  `grep`-and-replace move cannot catch by construction — only a
  does-every-path-resolve check finds it.
- **A path I broke while repairing paths.** The Macaulay2 drivers spell the
  section ASCII-style (`S(K-Lambda)`), and repointing them produced
  `K-Lambda.md` against an actual file named `K-Λ.md`.
- **A stale forward reference in this plan**, to a `notes/INDEX.md` that slice
  13 decided not to create.

Every `notes/pencil/…` reference now resolves. The 122 remaining unresolved
paths tree-wide are pre-existing and out of scope: 68 are template
placeholders (`notes/PhaseN.md`), 7 are GitHub URLs, and the rest — including
a dangling `notes/scripts/w4/fres.py` cited from three files — predate this
round.

### Slice 13 — as originally specified  *(retained for the record)*

The remaining PENCIL assets to `notes/pencil/`. A thin subtree `CLAUDE.md`
(~60 lines: the ledger CLI, canonical homes, the round map) auto-loads for
work under it. Trim `notes/CLAUDE.md`'s file catalogue — the part
that auto-loads on every `notes/` touch — to a pointer at the subtree manual.

Smallest measured win of the round (~4% of a dispatch's ramp-up). It is here
because it is cheap once slice 12 has moved the bulk, not because it matters
on its own.

### Slice 14 — split the coordinator command and the agent core  *(LANDED 2026-09-09)*

**What landed**, drafted by a subagent under the round's own serial-landing
discipline (it wrote only under `.claude/` while the coordinator held `notes/`,
and committed nothing):

- `.claude/commands/coordinate-research.md` (293 lines) — the research loop:
  the ledger as the way to answer *what is proved*, the spec-writing rules,
  rung guidance, the 7-step loop, session budget and exception log.
- `.claude/agents-core/research-direction.md` (158 lines) — the shared core,
  with build-gate and compiler-spike discipline deliberately absent and
  everything about verifying-rather-than-assuming restated for a corpus.
- `.claude/agents/research-direction-{opus,fable}.md` — rung-pinned thin
  shells matching the existing `recon-*` pattern.
- `coordinate-phase.md` gains a pointer at the top and loses its
  research-fan-out paragraph, which now says *switch commands*.

**Two things it got right that are worth recording as precedent.** It
**refused to copy S/P/B**, on the ground that those axes were calibrated on
~890 *build* dispatches and score commit risk — and a direction commits
nothing, so two of the three have no referent. And it marked genuinely
unsettled things as unsettled rather than inventing a calibration (optimal
fan-out width; whether the compute-licensed/derivation-first tier split tracks
real risk). Both are the `RESEARCH-ARC.md` three-tier discipline applied to
the harness itself.

**Every citation was spot-checked against the primary record** — F5, F11, F12,
F17, F18/F19, F20, F24, F26, F27, the 64k-output kill, the BGTWOA
already-satisfied tell — and all resolve.

**And checking one of them corrected a drifted figure in `RESEARCH-ARC.md`
itself.** §7 said BGENUINE's wrong denominator made *"a third of the
witnesses"* read as violations; the dispatch-log's own BGENUINE row says
**100 of 392**, which is a quarter. A summary overstating its body — the exact
pathology §6 and F12 exist for — found only because the draft was written
against the primary record instead of against the summary. Corrected in this
commit, with the drift noted in place rather than silently fixed.

### Slice 14 — as originally specified  *(retained for the record)*

`.claude/commands/coordinate-research.md` (~150 lines): rounds and
reservations, serial coordinator landing, drafts outside the tree, the
ledger gates, briefing-packet generation, the §7 prediction-labelling
requirement. `.claude/commands/coordinate-phase.md` keeps the Lean/blueprint
machinery and loses the research paragraphs it currently carries in step 1,
which become a pointer.

`.claude/agents-core/research-direction.md` replaces `recon.md` +
`phase-builder.md` for this phase's dispatches, with rung-pinned variants
`research-direction-{opus,fable}.md` following the existing thin-shell
pattern (dispatch-log F5 — frontmatter `model`, so a `SendMessage` resume is
rung-stable). It drops compiler-spike and build-gate discipline and keeps
the three recon clauses (verify against source, flag don't force, trace
invariants to ground), restated for a corpus rather than a Lean tree.

**Do not delete anything from `coordinate-phase.md` that the research
command does not re-home.** The formalization phases resume after PENCIL.

## Risk register

- **The backfill invents a verdict.** The round's one unrecoverable error.
  Mitigated by `UNTAGGED` being a legitimate terminal state and by slice 10
  listing every claim it left alone. If a slice is tempted to adjudicate,
  it stops and hands the claim to a direction.
- **The ledger is trusted past its evidence.** It is an *index*, exactly as
  `pencil/labels.md` says of itself: the owning section stays authoritative
  for what a claim means. Regeneration guarantees the index *matches* the
  prose; it guarantees nothing about whether the prose is right, and a
  `[PROVED]` tag is a claim by whoever wrote it, not a check. Slice 9's lint
  enforces vocabulary and required names — never correctness.
  `notes/pencil/CLAUDE.md` must say this in its first paragraph.
- **The split breaks a grep-based discipline silently.** Addressed in slice
  12, and the reason that slice repairs prose rules and not just paths.
- **The move breaks a Lean doc-comment anchor.** `notes/CLAUDE.md`'s anchor
  test was run for this plan: `grep -rc '<name>.md' --include='*.lean' .` is
  **0 for all five moving workbooks**, and PENCIL has no blueprint pins. So
  this risk is measured at zero today — but re-run the test at slice 12, since
  the Lean side is only parked, not closed.
- **`gapdiff.py` / `check-gapmap-cells.py` regressions.** Both read the
  workbook by path and by table geometry. Slice 12 re-runs both plus
  `notes/scripts/gapdiff.py` against the split tree before committing.
- **The round outruns the phase.** Slices 10 and 13 are the droppable ones.
  8, 9, 11, 12, 14 are the round.

## What gets promoted at close

Round-close obligation, per `CLAUDE.md` *Lift on promotion*:

- the **derived-ledger pattern** (a status object that is generated, a
  closed vocabulary with obligation columns, `UNTAGGED` as a first-class
  state, and **regenerated rather than stored** so it cannot become one more
  drifting summary surface — with reviewability kept via a generated `--delta`
  pasted into the commit message) → `RESEARCH-ARC.md` as a *Ready* item
  **only if** a second research-shaped phase uses it; on this round's evidence
  alone it is a **Candidate**, and the file's own three-tier rule says so;
- the **generated-briefing-packet** rule (a spec quotes claims from the
  index, never retyped from a summary surface) → `RESEARCH-ARC.md` §7,
  where BGENUINE's incident already argues for it;
- the **turns-not-bytes** finding (D2 — retrieval cost is dominated by
  reasoning turns, so the fix is one high-yield call, not less reading) →
  `RESEARCH-ARC.md`, as the rationale future rounds will need;
- the command/agent split → `CLAUDE.md`'s reading order and
  `PHASE-BOUNDARIES.md`'s phase-open checklist, so a future research-shaped
  phase opens against `coordinate-research` by default.

## Hand-off / next phase

Slice 8 is LANDED. Next concrete commit: **slice 9** — the status vocabulary
and `notes/ledger.py --lint`, which turns the 666 UNTAGGED claims from a census
into a gate on new ones. Slice 12 (the split) is the alternative next step and
now carries the stronger argument; it needs slice 9 first only so the backfill
is not done twice.

*(Slice 8's original spec, for the record: `notes/ledger.py`, with `--label`,
`--status`, `--frontier`, `--cited-by`, `--brief` and `--delta`, generating
into a gitignored `notes/.ledger-cache/` and run against the corpus in its
*current* location (`notes/Pencil-*.md`). No `line` column, no checked-in
artifact, no `--verify`. Additive; no file moves; no mathematics touched. The
commit adds the cache path to `.gitignore` and records the three measurements
that decided the no-check-in call (0.2 s generation; 165% vs 36% row churn per
twenty landings; 35.9 KiB per twenty revisions had it been stored). Slice 12
retargets its paths.)*

## The review pass — three critical defects, found by a read-only reviewer

Slices 8–14 shipped with `--selftest` green throughout. A read-only adversarial
review, dispatched in parallel with slices 12–13, found **three critical
defects** the gate could not see. All were reproduced before being fixed.

**C1 — `--delta` fabricated status transitions, including *into* `PROVED`.**
`--delta HEAD` on a byte-identical tree reported `(OC-40) PROVED → UNTAGGED`
plus three phantom new claims. Cause: slice 9 added an occurrence ordinal to
the identity key and fixed `cmd_lint`'s before-side but **not `cmd_delta`'s**,
which called `parse()` directly and defaulted every old row to `occ="1"`,
collapsing the five duplicate label-clauses. `--delta`'s stated purpose is
pasting into a landing's commit message, so this wrote invented verdicts into
permanent history. Fixed at the root: `parse()` now assigns the ordinal, so
every caller gets it.

**C2 — the ledger served a STALE verdict while a superseding one existed.**
`--label '(FR-R1)'` answered a flat `[OPEN]` for a claim the corpus declares
`**(FR-R1) — PROVEN.**` with an exhaustive 1976-site certificate; `(E-loc)`
answered `UNTAGGED`, its `**(E-loc) is REFUTED … witness T32**` line absent.
An agent picking work from `--frontier` or `--status OPEN` would have taken a
solved problem as an open research target — the exact failure the tool exists
to prevent, inverted. Two-part fix: index the shape, **and** flag the
disagreement, because the corpus genuinely holds both and picking a side
silently is the wrong behaviour. A `CONTESTED` banner now leads `--label`, and
`--status`/`--frontier` mark such rows; 21 label-clauses are flagged.

**C3 — 87 claim lines, and ~490 titled sub-clauses, had no row at all.**
`(BE-E4′)` (193 corpus mentions), `(PENCIL-SATURATES)` (128) and `(E4)` had
**zero** rows. The opener regex required the bold to close immediately after
the label, so titled openers (`**(OC-8) what (OUT) now reduces to, exactly.**`),
assertions (`**(ANH-R1) is discharged …**`), list-prefixed openers and every
titled sub-clause (`**(iii) A twin-plane pair forces a 3-cycle.**`) were
invisible. Corpus count 1 287 → **1 783**, and **no new row received a status
the tool inferred** — every one is `UNTAGGED` unless its own prose carries a
tag, so the count of `PROVED` did not move.

**The gate was checking a circular invariant.** `--selftest` asked *did every
line the regex matched become a row?* — self-consistent, and green while a
third of the corpus was unindexed. It now also asks the independent question:
*which heavily-cited labels have no row?* That check reports 11 labels
mentioned 20+ times without one, and reports rather than fails, because a
status stated in a section's verdict block (`(S1)`) is out of scope by design.

**Three further defects surfaced while fixing these**, each caught by testing
rather than reasoning: the fragment filter from slice 10 ate legitimate wide
openers beginning `is …` — discarding the very `(E-loc)` refutation the fix
targeted; `locate()`'s fixed needle returned the wrong line for wide openers
(both `(FR-R1)` rows reported `:253`); and `contested()` keyed on the label
rather than the label-clause, reporting 39 phantom conflicts where different
clauses legitimately hold different statuses.

**The lesson for the round.** Every defect found this session — three by the
coordinator, three by the reviewer, three more while fixing — was invisible to
the gates and visible immediately on use. A green `--selftest` certified a
tool that was missing a third of its corpus and answering `OPEN` for a proved
claim. Independent adversarial review of a new tool is not optional, and the
review must run against the tool's OUTPUT, not its code.

## Follow-up: `--frontier` was presenting "unknown" as "open"

Found by tracing what the tool actually does with an `UNTAGGED` claim, after
the round closed. `--frontier`'s filter is `if r["status"] in CLOSED:
continue`, so untagged claims were listed as live leaves — and **289 of its
347 entries (83%) are untagged**. Since `UNTAGGED` means *no machine-readable
status* rather than *unproved*, the command was offering claims that may
already be settled in prose the tag never recorded. `(FR-R1)` is the worked
example: an exhaustive 1976-site certificate the tag never carried.

Not a wrong verdict — a wrong *presentation*, which wastes a dispatch rather
than corrupting a record. Fixed by splitting the output into **KNOWN-OPEN**
(58; status recorded and not closed — these are work) and **STATUS-UNKNOWN**
(289; the next action is a tagging decision, not mathematics), with
`--frontier --known` hiding the second group.

The opposite asymmetry was already correct and is left alone: an untagged
*citation* keeps a dependent claim off the frontier entirely (212 labels are
untagged-only and count as not-closed), so the tool never says "ready" on the
strength of an unknown premise.

**This is the same failure family as C2, one notch milder** — the tool
answering with more confidence than its evidence supports — and it is the
third time this round that the defect was in what the tool *presented* rather
than in what it computed.

## The tagging pass, and the three defects it found by DOING the work

Dispatched over `--backlog --decisive`'s 356 "transcription" claims. It read
**122** and tagged **21** — leaving **83% alone**. That is the headline, and it
**refutes the scoping hypothesis** the dispatch was built on.

**`--decisive` does not mean transcription at the top of the ranking.** The
premise was that a clause containing a status word merely failed to record it
in its tag. False where it matters most: the corpus's most-cited claims are
exactly the ones that have been corrected, split or re-quantified in place, so
a status word in the body is as often a *neighbour's* verdict or a superseded
half. Four recurring shapes — superseded-in-place, split stratum (`(BE-45)(iv)`
is "a theorem on 8 of 11 and a measurement on 3"), an obligation the clause
cannot meet, and prose citations that were never claims. The ranking put the
hardest cases first precisely because citation count tracks how much a claim
has been revisited.

**Three defects in the tool, all found by using it, none visible to a gate:**

1. **`--lint` skipped the exact operation the pass performs.** Its
   changed-vs-`HEAD` test compared `tag` and `claim` — and adding `[MEASURED]`
   changes neither. Of the first 15 tags the default gate checked **one**. So
   the obligations (`[MEASURED]` names a driver, `[REFUTED]` a witness) went
   unchecked on the commits that introduced them. Fixed by including the
   bracket in the change test; verified by injecting a `[MEASURED]` with no
   driver and confirming the default gate now fails it.
2. **A WIDE opener could not be tagged at all** — 93 of the 356. Its bold's
   inner text is prepended to the claim, so `BRACKET.match` never fired: a
   bracket after the bold parsed as `UNTAGGED`, and before it destroyed the
   row. The bracket is now read off the post-bold remainder too.
3. **40 rows are mid-sentence prose citations**, where a bold happens to start
   a WRAPPED line — `"…and by\n> **(BE-22)(vi)** a rigid side collapses…"`.
   `(BE-22)(vi)` was the worklist's **#1 entry by citations**. They are flagged
   and dropped from `--backlog`, but **kept in the index**: the class is not
   cleanly separable (`> **(A)** v* is a hub` after "So exactly one of" is a
   genuine enumerated alternative), so the fix filters the WORKLIST, not the
   ledger.

**Verification of the landing** (not taken on attestation): the diff is 21
insertions / 21 deletions across 14 files, every added line an opener gaining a
bracket; `--delta` over both commits shows **21 transitions, every one
`UNTAGGED → X`**, so no existing status was rewritten; `--lint --all` and
`--selftest` green; and a spot-check of `(BE-41)(ii)` `[RETIRED]` found its
prose saying *"this clause is RETIRED, not repaired"* and naming successor
`(BE-74)` — tag and obligation both correct.

**Three CONTESTED cases were reported and deliberately not resolved**, all the
F12 shape (the correction landed at the citing surface, never at the claim):
`(GR-108)`, `(BE-139)(iv)`, `(BE-187)(iii)`, plus a weaker fourth at
`(BE-134)(i)`. Adjudicating them is research, not tagging.

## The taxonomy pass — the 799 are mostly not independent unknowns

A read-only analysis of the judgement-untagged population, dispatched in
parallel with the tagging pass against a pinned baseline. Its headline finding
is structural and was not on the plan's map.

**The coordinator's hypothesis was half right, and the labelled half is what
made that legible.** The spec stated it as a hypothesis *to be tested*, named
its evidence stratum (the 200 glossed rows, a quarter of the population), and
named where it expected to be wrong (the 599 no-gloss rows). Both halves
resolved: **confirmed** on the glossed 200 — 58% are *role* glosses (cap
disclosure, dispatch verdict, editorial reading, board/price) rather than
evidence glosses — and **refuted** on the no-gloss 599, where 95% carry maths
notation and a seeded draw came out ~30 of 34 ordinary mathematical
assertions. Those need reading; there is no shortcut. Running the cheap
refutation first is what §7 asks for and it paid.

**The finding that matters is orthogonal to the tag question.** A large
majority of the 799 are **non-head clauses of a label group whose head is
already tagged**, and for a big share of those the head is a bare hypothesis
STEM. `(GR-61)`'s head is `[PROVED]`, its claim body is *"Let `z` be
admissible and `S` a chunk. Then"*, and its tag reads *"proven; EVERY CLAUSE
machine-asserted at 31 047 708 pairs"* — while its five clauses each sat in
the backlog as separate unknowns. That is one theorem counted as six
unknowns. Measured here at **295 untagged clauses under a tagged stem head**.

**And the tool was already inheriting in one direction only.** `closed()`
treats a *cited* label as closed if ANY of its clauses is closed, while the
subject side keeps every clause independently unknown. That asymmetry
generates much of the 799 — and it was the coordinator's, not the corpus's.

Resolved by **surfacing, never asserting**, the same rule the CONTESTED banner
and the verdict hints follow. Auto-inheritance would invent verdicts:
`(BE-43)` has (i) and (ii) `PROVED` and (iii) reading *"GAP (i) is NOT soft"*.
So: an untagged clause now prints `GROUP HEAD (L) is [PROVED] — this clause
may be covered by it; read the head, do not assume`, and `--backlog` drops
stem-headed clauses, which are not independent tagging decisions.

**Four further parser defects, found by the taxonomy's sampling:**

1. **`OPENER` accepted any parenthetical as a label** — `'legality,
   placement-free'`, `'plane, point-on-plane'`, `'2,3'` were indexed as
   claims. A `LABELISH` shape test now gates it.
2. **A possessive after a STRICT opener was parsed as a claim** — `(AV-7)`'s
   entire claim text was `'s open arm`. The wide opener had a possessive
   guard; the strict one did not.
3. **`flush()` does not clear `pending`**, an invariant the original code held
   only because it always reassigned immediately after. The new `LABELISH`
   `continue` broke it and emitted the previous claim **twice** — caught by
   the selftest reporting *more rows than openers*, which is exactly the
   independent check added after C3.
4. **34% of rows had NO line pointer** — every one a sub-clause, because
   `locate()` matched on the row's label while the source line reads
   `> **(i)**`. `--brief`'s whole job is pointing at the source, so a third of
   its output was unusable. `locate()` now tracks the inherited label as
   `parse()` does; the sampled failure rate is 0.

**Worklist effect:** `--backlog` 1 155 → **784**, `--decisive` 356 → **298**,
with nothing deleted from the index — every filter narrows the WORKLIST, and
`--label` still returns every row.

## D6 — the next round's diagnosis, measured at the first `/coordinate-research` session after slices 8–14 (2026-09-09)

This section is a **second wave of evidence on D1** (*the coordinator spends
120–190k tokens before its first dispatch*), taken from the first coordinator
session to run the finished harness end to end: three concurrent directions
(BCORNER / GISLAND / GCOIND, ordinals 93–95) dispatched from baseline
`c8efb227`. It is written for a **future harness-adjusting session**, so every
forward-looking item below carries its **kill condition** and the surface that
decides it, per `RESEARCH-ARC.md` §8.

**The measurement, and its honest provenance.** ~55 tool calls preceded the
first dispatch — my own count from the session transcript, not an instrumented
figure. Roughly: **14** orientation reads of manuals, **12** driver-source reads
hunting blind axes, **10** label-reservation mechanics, **8** ledger/gap-map
queries, **6** caps/gates/budget, **5** miscellaneous. The three big blocks are
the first, second and third; the ledger queries — the thing slices 8–11 built —
were the *cheapest* line in the table and are not the problem.

**What is already working, and should not be "improved".** `--brief`/`--round`
produced three dispatch packets with statements quoted verbatim, **one call
each** (BCORNER's 17 labels, ~9 800 words); `--reserve` cleared three direction
codes in one call; `gapmap.py` kept a 23 876-character row readable at a few
percent of its cost. That is why the prep was ~55 calls rather than the
~35-probes-per-18-claims the ledger docstring measures for the grep era. **The
residue is exactly two shapes: a surface that got a GATE but no READER (D6.1),
and a reading a RULE asks for but no script performs (D6.4).**

### D6.1 — the phase note has a gate and no reader; the gap map has both

§6's promoted lesson is *cap the cell, **but also ship a READER for it***. It was
applied to the gap map (`check-gapmap-cells.py` + `gapmap.py`) and **not** to the
phase note, which has `check-phase-note.py` and nothing to read it with.
Measured at `c8efb227` (`wc`, and `awk` over the paragraph): `notes/Phase39.md`
is ~579 lines / ~7 167 words, and the one sentence a coordinator needs — the next
concrete task — is the *Hand-off* section's next-task paragraph, **a single
physical line of ~580 words / ~3 700 characters**. No line number is recorded
here on purpose: the ledger's own *NO LINE COLUMN* finding is that a stored line
number shifts for every edit above it. That is the same one-physical-line-per-object
shape `gapmap.py` exists for, and reading it cost a full-file pass because
nothing points at it.

**Suggestion:** `notes/phasenote.py`, `gapmap.py` retargeted — `--next` (the
next-task paragraph, sentence-windowed), `--status` (the header block),
`--handoff`, and `--surfaces` (print every status surface an F17 sweep must
touch: the `**Status:**` header, the *Hand-off* next-task slot, *Current state*,
the ROADMAP Status cell, the dispatch-scoping file's header). The last mode is
the one that pays twice — F17 is three consecutive landings each leaving a
*different* surface stale.
*Kill condition: `notes/phasenote.py --next` shipped and used by one coordinator
session, or a measurement showing the full-file read is cheaper than the reader.
Decided by: the file's existence and this section.*

### D6.2 — `RESEARCH-ARC.md` §7 is 48% of the file, and the loop says to cite it, never re-derive it

Measured at `c8efb227` (`awk '/^### 7\. A coordinator prediction/,/^## /'`):
§7 (the prediction-kind tally) is **414 of 957 lines / 5 111 of 10 674 words** —
**~48% of the file**. The ratio is the durable half of that; re-take the
absolutes rather than trusting them. The command's own instruction is *"§7 keeps the running tally … **cite
it, never re-derive it**"* — so what a coordinator needs in the loop is §7's
**rule** (three clauses: state the reason separately from the verdict; write down
where you expect to be wrong; make the tell falsifiable against the corpus you
already have) plus a pointer. The twenty-seven-instance / ten-kind provenance is
real and worth keeping, but it is below the read-line. §4 has the same shape: the
rule is four sentences, the evidence is ~90 lines.

**Suggestion:** split each Ready item into a short **binding head** and a
**provenance tail**, and move the tails to `notes/dispatch-log.md` *Findings* or a
`RESEARCH-ARC-provenance.md` behind one-line pointers. This is the file's own
*lift on promotion* rule turned on itself, and the CLAUDE.md suite's stated
policy — *extract to read-on-demand references rather than deleting content*.
*Kill condition: `RESEARCH-ARC.md` under ~500 lines with every Ready item's rule
stated in its first paragraph. Decided by: `wc -l RESEARCH-ARC.md` and the file's
tier headers.*

### D6.3 — three pre-dispatch checks are mechanical and were done by hand

- **(a) The (L7) per-token range enumeration.** `ledger.py --reserve` checks
  *tokens*, not *ranges*, so the range check was an ad-hoc shell loop written
  twice, once per label family. **Suggestion:** `--reserve-range 'BE-231..BE-238'
  --steps 'BE230..BE237'`, emitting the (L7) table in the shape `labels.md`
  blocks already use — and, the part that actually took judgement,
  **classifying each hit as declaration-vs-consumption** by testing whether the
  hit line is a previous reservation's tail declaration. Every non-zero cell in
  this round's three reservations was a declaration; *"0-hit except the
  declaration"* is the only true form of the claim and a script can say it.
  **The gap is not hypothetical — it fired on this very round.** The
  coordinator's ad-hoc loop ran `grep -e "BE-$n" -e "BE$((n-1))"`, **collapsing
  the label token and the step token into one invocation**, so a hit could not be
  attributed to the token carrying it; the spec reported three non-zero tokens
  and direction BCORNER's own (L7) pass found a **fourth** (`BE237`). Nothing was
  consumed, so the reservation stood — but (L7) says report hits and files
  *separately*, and **a combined grep structurally cannot**. That is the concrete
  acceptance test for `--reserve-range`: one row per token, never per range.
- **(b) Live-tail discovery.** Learning that the (GR-) family's declared tail is
  `(GR-153) / Step G173` took a grep plus two `labels.md` blocks.
  **Suggestion:** `--tail GR` printing the declared tail and the line declaring it.
- **(c) Doc-cap headroom.** Learning that `(K-bare)` had **28** words free and
  `(K-grid)` **23 / 9** (at `c8efb227` — these move at every landing and are not
  maintained here) required reading `SPECIAL_CAPS` out of the gate's source.
  **Suggestion:** `check-gapmap-cells.py --headroom` (used / cap / free per row),
  and a free-words column on `gapmap.py --list`. Headroom decides whether a
  landing is an append or a recompute, so it belongs in the dispatch spec.
*Kill condition for all three: each shipped, or one coordinator session that does
the check in a single call. Decided by: the flags' presence in `--help`.*

### D6.4 — the blind-axis grep is the loop's highest-yield prep step and has no tool

`RESEARCH-ARC.md` §4 instructs *grep the generator for hardcoded constants*. That
instruction produced **both** of this session's decisive prep findings, at a cost
of ~12 source-reading calls:

- `cflank.LAM6_PLAN = ((6, 9, 1),)` fences the `Λ ≠ ∅` sweep at `|Λ| ≤ 1` —
  **24 846 of 142 740** length tuples, **82.6% unswept** — while
  `length_tuples(M, tgt, lamcap=99)` already takes the parameter, and the unswept
  stratum is exactly where the derived merge condition lives. Re-derive, do not
  trust: `len(cflank.length_tuples(9, 24, lamcap=c))` for `c` in `1, 99`.
- `gridcol.collapse_search(…, want=1)` returns at the first certificate, so
  `strategy.md` §8 rank 2's quoted *"257 co-independent 4-partitions of 20 967"*
  is a truncation artifact. Un-fenced (`want=∞`, **9 s**, no harness edit): **3 128
  of 175 275, with 1 536 certifying** — turning that entry's first slice from one
  labelled partition into a near-balanced 1 536/1 592 dataset. Re-derive, do not
  trust: `gridcol.collapse_search(bd, 4, rng, want=10**9, budget=600.0)` at
  `EXEMPLAR`.

Both are the BNONUNI shape — *a hardcoded constant reads like harness
architecture and is usually a keyword argument away from being an axis* — and
neither is visible to any gate. **Suggestion:** `notes/scripts/blindaxes.py
<driver>`, an AST pass listing, for a named driver and its read-only imports:
module-level constants, keyword parameters with literal defaults, and
early-return guards on a counter. Even a dumb lister surfaces `want=1` and
`lamcap=1` in one call instead of twelve. Note the asymmetry that makes this
worth automating: the *rule* is promoted and the *reading* is manual, so the rule
is obeyed exactly as often as a coordinator remembers to spend twelve calls.
*Kill condition: the script shipped and one spec's blind-axis list generated by
it; or two consecutive rounds where the hand grep finds nothing the spec did not
already name. Decided by: this section plus `notes/dispatch-log.md` Findings.*

### D6.5 — the recommendation surface cites driver modes in prose, and one was wrong

`strategy.md` §8 rank 2 names `packmm.py --hier`; the mode lives in
`gridcol.py`. §8 is *the* surface a fresh session reads to choose a direction —
RESEARCH-ARC §8's whole thesis — and a prose driver-mode citation is a
**mechanically checkable** class of error that no gate covers.
**Suggestion:** `notes/check-driver-refs.py` — extract every `<name>.py --<flag>`
string from `notes/pencil/**` and `notes/*.md`, resolve against each driver's own
argparse flags, fail on a mismatch. This is §8's *gate a surface and it stays
correct* applied to the one part of a recommendation that is machine-decidable.
*Kill condition: the gate shipped and green, or a measured hit count low enough
not to matter. Decided by: the gate's presence and its first run.*

### D6.6 — the blocking check-in is serialized behind reads it does not need

`.claude/commands/coordinate-research.md` puts the setup reads first and the
**blocking** user check-in after them. The check-in asks two questions — does this
run modify the instructions, and which rungs are dispatchable — and **neither
depends on any of the reading**. Moving it to the session's first action removes
a serialization point at zero cost, and the rung answer can change what the
reading is for.
*Kill condition: the command body reordered. Decided by: that file's setup
paragraph.*

### D6.7 — `check-phase-note.py --all` is RED at baseline, so the documented fallback does not exist for it

The loop says the three docs gates inspect files changed vs `HEAD`, so *"run them
BEFORE committing, or with `--all`"*. Measured at `c8efb227`:
`check-phase-note.py --all` exits **1**, every failing note a closed one
predating the caps (count omitted deliberately — run it). So `--all` is **not** a usable fallback for that
gate — only the changed-vs-`HEAD` mode is, and a post-commit run certifies
nothing with no alternative. **Suggestion:** default to `ACTIVE` notes and make
the archive an opt-in scope, or amend the loop's sentence to name the exception.
This is the promoted corollary's sibling: *a gate that reports zero is not a gate
that passes*, and **a gate that is red at baseline cannot be a fallback**.
*Kill condition: `--all` green, or the loop's sentence amended. Decided by:
`python3 notes/check-phase-note.py --all; echo $?`.*

### D6.8 — a derived count written into prose is a summary surface; cite the command, not the number

Found while auditing this section, and it is the round's own thesis turned on
the round's own documentation. **The claim count drifted `1 783` → `1 764`
*without the corpus changing*** — the taxonomy pass's four parser fixes
(`LABELISH` gating, the possessive guard, `flush()` not clearing `pending`,
the sub-clause `locate()`) re-partitioned what counts as a claim. Two live
surfaces were left asserting the old figure: `notes/Phase39.md`'s *Hand-off*
and `notes/pencil/CLAUDE.md`'s opening sentence. Neither is *wrong about
anything mathematical*; both are a number that no gate maintains, in a document
whose whole purpose is to be trusted on first read.

**The obvious repair is the wrong one.** Updating `1 783` to `1 764` buys one
correct day and re-arms the same trap — this is exactly slice 8's own recorded
reason for **not checking the ledger in**: *"a stored ledger would be one more
SUMMARY SURFACE, and this corpus's documented pathology is a summary disagreeing
with the body prose it summarizes"*. A count in prose is a stored ledger of size
one. So the repair is to **delete the number and name the command**:
`python3 notes/ledger.py --stats` costs one call and cannot drift.

**The distinction to hold, because it is not "never write a number down".**

- A **historical measurement** — *"~55 tool calls before the first dispatch in the
  2026-09-09 session"*, *"generation over the 2.8 MB workbook measures ~0.2 s"* —
  is dated, describes an event, and is correct forever. Write it, date it, keep it.
- A **live figure** — a corpus count, a row's free words, a gate's failure count,
  a backlog size — describes the tree *now*. It is a summary surface. Do not write
  it into prose that will be read later as current; write the command that
  produces it, or anchor it to a baseline sha **and say it is not maintained**.

The tell that separates them in one question: *if this number changes tomorrow,
is the sentence wrong, or merely old?* Wrong ⇒ it is a live figure, cite the
command. Merely old ⇒ it is history, date it and leave it.

*Kill condition: a grep for live counts across the status surfaces
(`notes/Phase39.md`, `notes/pencil/CLAUDE.md`, `ROADMAP.md` §39) returning only
dated or command-cited figures. Decided by: this section and the next liveness
sweep.*

### D6.9 — the round's own answer to D6: what the harness gated, and the one artifact it did not

Recorded after the 2026-09-10 round of three landed (`f34759e1`, `1faf7cee`,
`32e9b0f3`), because a diagnosis section that never reports its own follow-up is
the rot §8 names.

**What the built harness did well, measured on a real round.** `--brief`/`--round`
produced three dispatch packets at one call each; `--reserve` cleared three
direction codes in one call; `gapmap.py` kept two 20 000+-character rows readable
at a few percent of their cost; and `--lint` **caught a real defect before the
commit** — a direction had written `[UNTAGGED]` as a bracketed tag on three
clauses, where `UNTAGGED` means *no bracket*. That last one is D6.7 vindicated
from the other side: the gate fired only because it was run **before** the commit;
run after, it certifies nothing.

**What no gate covered, and it is the same artifact twice.** Two of the three
directions proposed a defective **gap-map cell**, and both proposals passed every
gate — one costing words out of a status-cell structure that does not exist, one
writing unescaped pipes that silently flipped the row from `split` to `combined`
while `check-gapmap-cells.py` reported OK (its ambiguous-split fallback caps the
*sum*). The shape regression was caught by `gapmap.py --list` — **a reader, not a
gate**. Full record: `notes/dispatch-log.md`, 2026-09-10.

**The generalizable form, and it sharpens D6.1 rather than adding to it.** D6.1
says the phase note has a gate and no reader. This round says the converse also
bites: **the gap-map row has both, and the reader is what caught the defect the
gate could not.** So the pairing is not redundancy — the gate bounds a *measure*
(words, labels, vocabulary) and the reader exposes *shape*, and only the second
notices when a row stops being a row. Any object worth gating is worth a reader,
and the landing checklist should call the reader, not only the gate.

*Kill condition: a round in which the gap-map cell proposals land clean, or a gate
that checks row shape. Decided by: `notes/dispatch-log.md`'s Findings and this
section.*
