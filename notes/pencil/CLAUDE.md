# notes/pencil/CLAUDE.md — operating manual for the PENCIL corpus

Auto-loads when a session touches anything under `notes/pencil/`. It carries
only what is specific to this corpus; `notes/CLAUDE.md` still governs notes
generally, and `HARNESS.md` carries the research-side rules (`RESEARCH-ARC.md`
is its retired predecessor, kept as history).

## Ask the ledger; do not grep the workbook

`python3 notes/ledger.py` indexes **every label-clause in this corpus** (`--stats`
for the live count; it is not quoted here, and it moves on parser fixes as well
as on landings) and reports the evidence status the claim's own prose states.

```
--label '(BE-216)'     every clause of one label: status, section, live line, citations
--brief L1 L2 ...      a briefing block, statements quoted VERBATIM with hypotheses
--frontier             claims whose every known citation is closed, SPLIT into
                       KNOWN-OPEN (work) and STATUS-UNKNOWN (tag it first)
--frontier --known     only the KNOWN-OPEN group
--cited-by '(BE-210)'  what breaks if this claim falls
--status PROVED        everything at a status (--section / --file narrow)
--delta <ref>          the status change-set, for the landing's commit message
--round N --direction D --labels L1 L2 ... --out
                       a dispatch briefing packet, statements GENERATED not retyped
--backlog              UNTAGGED claims ranked by citations -- the tagging worklist
--reserve 'PFX-'       0-hit check a label prefix corpus-wide before minting
--lint                 GATE: the status vocabulary on what this commit changes
--list / --stats / --selftest
```

This exists because retrieval by `grep`+`sed` was measured at **~35 probes and
~137k tokens of context growth** for ~18 claims in one traced dispatch — the
cost being *reasoning turns*, not bytes. `--brief` answers the same question
for 14 labels in **one call, ~7 600 tokens**. Reach for it first.

**`UNTAGGED` means "no machine-readable status", NOT "unproved".** The
distinction is load-bearing: `--frontier` therefore splits its output, because
**83% of it is untagged** and an undifferentiated list presents *I don't know*
as *ready to attack*. A STATUS-UNKNOWN claim may already be settled in prose the
tag never recorded — `(FR-R1)` is the worked example — so its next action is a
tagging decision, not an attack on the mathematics. On the citation side the
tool is conservative the other way: an untagged citation keeps a dependent claim
OFF the frontier entirely.

**A CONTESTED banner means read every row.** A label-clause can carry a stale
row and a superseding one — `(FR-R1)` has an early `open` tag and a later
`**(FR-R1) — PROVEN.**`; `(E-loc)` has a positive statement with its refutation
three lines below. The ledger surfaces the disagreement and refuses to pick a
side. A verdict word found inside a bold is reported as a HINT, never assigned
as a status: `**(BE-44)(ii)** is **PROVED in the `dim⟨P⟩ = 6` direction only**`
is why — reading `PROVED` off it would drop the scope that makes it true.

**Not everything is indexed.** A status stated in a section's own VERDICT BLOCK
rather than a `> **(LABEL)**` blockquote has no row — `(S1)` is the example.
`--selftest` lists labels mentioned 20+ times with no row so the boundary stays
visible.

**It is an INDEX, not an authority.** Regeneration guarantees it matches the
prose; it guarantees nothing about whether the prose is right. A `PROVED` row
is a claim by whoever wrote that clause, never a check of it — **read the
owning section before building on a row.** The ledger is regenerated into a
gitignored cache whenever a source file changes (~0.2 s); it is never checked
in, so it cannot drift from the prose (`notes/Harness-structure.md` slice 8).

## Layout

**Live status surfaces:** `X0-formalization.md` and `W4-reopen.md` (the `X₀` line), and
`notes/attacks/<name>/state.md` (each attack). The gap map, `fanout.md` and
`strategy.md` belong to the coordinator loop retired on 2026-09-15 and have not
moved since 2026-09-13. Read them as the arc's record, not as current status.

| what | where |
|---|---|
| the (K) workbook, **one file per section** | `workbook/`: 20 topical gaps, `K-bare-ext.md`, 36 direction continuations in `bare-ext/`, `grid.md`, `W4.md`, and **`K-main.md`**, §(K-main), the live `X₀` programme (tag `MC-`) |
| **the `X₀` formalization plan** (target, the index of done work, blueprint layers, open calls) | `X0-formalization.md` |
| **W4 reopened**: the live hand-off (status, next tasks, PI calls, constraints) | `W4-reopen.md`; its frozen earlier text (P1–P5, T0–T4) is `W4-reopen-archive.md`, not read on load |
| *State of (K)* gap map, the retired loop's status object | `workbook/gapmap.md`; read with `python3 notes/gapmap.py`, **never `sed`/`grep`** (one row is one 22 000-character line) |
| shared dictionary + test shapes `W19`/`S29` | `workbook/dictionary.md` |
| section index (paths, not line numbers) | `workbook/README.md` |
| option board §8, the §9 Zheng shelf (retired loop) | `strategy.md` |
| label registry + the minting rule | `labels.md` — **read before minting any label** |
| the retired loop's dispatch specs and landing write-ups | `fanout.md` (ordinals 1–19: `fanout-archive.md`) |
| archived verbatim user calls | `adjudications.md` |
| the retired loop's final work log, verbatim (2026-09-15) | `arc-worklog.md`, not maintained |
| structural-round work logs | `structure.md`, `cleanup.md` |

`grid.md` and `W4.md` keep several sections each rather than one: `grid.md` is
97% a single `§(K-grid)` section, and `W4.md`'s arc is closed as argument (the build
reopened 2026-09-23, `W4-reopen.md`), so
splitting them further would restructure sections rather than move them.

## Writing a claim

The status vocabulary is **bracketed, before the gloss**, so editorial voice
survives:

```
> **(BE-216)(i)** `[PROVED]` *(the sum is hypothesis-free)* At a firing side …
```

`PROVED` · `PROVED-MOD <label>` · `INFORMAL <gap>` · `ASSERTED <driver>` ·
`MEASURED <driver>` · `CONSTRUCTED <driver>` · `CONJECTURED` ·
`REFUTED <witness>` · `MOOT`/`RETIRED <successor>` · `OPEN`

The trailing obligations are checked by `ledger.py --lint`, which binds the
**bracketed form only**. Legacy freeform tags are NOT converted in bulk and do
not need to be: 642 of them already classify correctly from their leading token,
so rewriting them would change no tool output. Tagging happens **per landing,
by the direction that touches the claim** — `--backlog` ranks what is left by
how much of the corpus cites it. Tag only where the claim's own prose is
decisive; `UNTAGGED` is a terminal state, not a defect. Like the other docs gates it inspects
changed-vs-`HEAD` files, so **run it before committing**, or with `--all`.

**If a row is not an evidence claim at all** — a board, a price, a scope note,
a "what did not move" report — there is currently **no tag for that**, and
`UNTAGGED` is the right answer. A *kind* axis (`[PLAN]`/`[NOTE]`/`[TARGET]`)
was proposed and **deliberately deferred**: see `RESEARCH-ARC.md` *Genuinely
unsettled*, which states the revisit trigger. Do not invent a kind token in the
meantime.

Three sharp rules this corpus paid for:

- **A driver per headline sentence**, and *exhaustive* / *forced* / *the only*
  are their own claim class needing their own driver (`HARNESS.md` *Evidence*).
- **A kill condition that names a NUMBER must carry its DERIVATION.**
- **Quote a criterion WITH its hypotheses**, or say which surface it came
  from. A spec once quoted one without its proviso, copied from a summary
  surface, and handed the dispatch the wrong yardstick (§7, BGENUINE). This
  is why a dispatch spec takes statements from `--brief` rather than retyping
  them.

## When you correct a claim

A correction to the gap map is presumptively a correction to body prose too
(dispatch-log F12). Since the 2026-09-09 split that search is a **tree, not a
file**: `python3 notes/ledger.py --cited-by '(LABEL)'` lists every claim that
cites the one you are fixing, corpus-wide, in one call — cheaper and more
complete than `grep -r workbook/`.

Before any gap-map edit run `python3 notes/check-gapmap-cells.py`; for a
recompute trust `python3 notes/scripts/gapdiff.py`, which compares **label
sets** rather than word counts and is the gate that actually reads content.
