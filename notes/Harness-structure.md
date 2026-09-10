# Harness + PENCIL doc-set structural round (work log)

**Status: SLICES 8–9 LANDED 2026-09-09.** Slice 8 — `notes/ledger.py`, 1 308
claims across five files, ~0.2 s regeneration, cache gitignored. Slice 9 — the
bracketed status vocabulary and `--lint`, gating the new form only. Slices
10–14 remain plan; the next concrete task is **slice 12** (the split), for which
slice 8 turned up a claim-identity argument stronger than the token one, with
slice 11 (generated round packets) and slice 10 (the backfill) after it. Opened 2026-09-09 at the user's
request after Phase 39's dispatch costs were measured. Slices are numbered
8–14, continuing `notes/Pencil-structure.md`'s slice numbering; this is a
separate file because the round's deliverables are **cross-phase** (a
derived-ledger layer, a split coordinator command, a new agent core, a
status vocabulary with a gate) rather than PENCIL file layout alone, which
is what slices 1–7 were. `notes/Pencil-structure.md` carries the pointer.**

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
- calls 7–13 — `notes/Phase39.md` + `notes/Pencil-strategy.md` §8, ~14k;
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
| `Pencil-informal-grid.md` | 232 | 165 |
| `Pencil-W4-informal.md` | 22 | 22 |
| `Pencil-strategy.md` | 7 | 7 |
| `Pencil-fanout.md` | 14 | 12 |

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
    grid.md                       was Pencil-informal-grid.md
    W4.md                         was Pencil-W4-informal.md
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
`notes/Pencil-structure.md` *Gates for any continuation*.

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
committing, or with `--all`** (`Pencil-structure.md` *Gates for any
continuation*, blind spot 1).

### Slice 10 — backfill the 476 untagged openers  *(N commits, incremental)*

Mechanical where the prose is decisive (`**PROVED**` → `[PROVED]`,
`proven-informally` → `[INFORMAL]`), by reading where it is not. **Any
opener whose own prose does not determine a status stays `UNTAGGED`** and is
listed in the slice's commit message. This slice may run in the background
across several sessions; it blocks nothing.

Not a dispatch target for a research direction — a direction backfilling
tags is a direction not doing mathematics.

### Slice 11 — generated briefing packets  *(replaces "go read the docs")*

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

### Slice 12 — split the workbook  *(the move; needs slices 8–9 landed)*

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
| `Pencil-strategy.md` | 224 | 35 |
| `Pencil-fanout.md` | 217 | 33 |
| `Pencil-labels.md` | 166 | 38 |
| `Pencil-informal-grid.md` | 109 | 29 |
| `Pencil-fanout-archive.md` | 106 | 17 |
| `Pencil-W4-informal.md` | 63 | 16 |
| `Pencil-structure.md` | 50 | 12 |
| `Pencil-adjudications.md` | 30 | 7 |
| `gapmap.py` | 16 | 11 |
| `Pencil-cleanup.md` | 4 | 2 |

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

### Slice 13 — move the rest, add `notes/pencil/CLAUDE.md`

The remaining PENCIL assets to `notes/pencil/`. A thin subtree `CLAUDE.md`
(~60 lines: the ledger CLI, canonical homes, the round map) auto-loads for
work under it. Trim `notes/CLAUDE.md`'s 230-line file catalogue — the part
that today auto-loads 6.6k tokens on every `notes/` touch — to a pointer at
a generated `notes/INDEX.md`.

Smallest measured win of the round (~4% of a dispatch's ramp-up). It is here
because it is cheap once slice 12 has moved the bulk, not because it matters
on its own.

### Slice 14 — split the coordinator command and the agent core

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
  `Pencil-labels.md` says of itself: the owning section stays authoritative
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
