# HARNESS.md — binding rules for research-side agent work

**Budget: 150 lines.** Adding a rule to a full file means removing one.
A rule is one or two sentences tagged `[date, standing]` or `[date, trial]`,
followed by `←` and the incident that earned it. Evidence, measurement and
history live in `notes/harness/` and in the two `RETIRED` files named at the
end; this file does not explain itself at length, on purpose.

**How this file changes.** Never inside a research or attack session. An
incident is one line in `notes/harness/incidents.md`. A rule enters as
`trial`, is promoted to `standing` on a second independent incident, and is
deleted after three attack sessions otherwise. `/harness-review` (every five
attack sessions or monthly, with the PI) applies those defaults and runs
`python3 notes/harness/check.py`. Commit rules — attribution, `-F` for
backticks, no local paths — are `CLAUDE.md`'s and are not repeated here.

## Evidence

- [2026-09-15, standing] Verify a load-bearing claim against the section
  that owns it, never a summary (gap-map row, header, board, return
  message). Quote a criterion with its hypotheses, or name the surface it
  came from. ← dropped provisos: BGENUINE 2026-09-01, BDECOR (six surfaces),
  (BE-22)(iv)/(vi) 2026-09-13.
- [2026-09-15, standing] A `PROVED` tag is a claim by its author. Read the
  proof before building on it; an unconvinced reading is reported as
  "claimed proved; the argument is X; I could not verify step Y".
  ← (BE-77)(ii) fell at 372 rows; (BE-66)(iv) refuted.
- [2026-09-15, standing] "Exhaustive", "forced", "the only" and every count
  name the population searched and its caps; a capped search reports "not
  found under cap C", and the cap travels with the figure wherever it is
  quoted. ← RESEARCH-ARC §5; dispatch-log F30.
- [2026-09-15, standing] For a semicontinuous statistic one draw is a bound,
  not a measurement; say which direction. An exhibited certificate is a
  proof. ← dispatch-log F27; the inverted gloss caught at BNEST 2026-09-13.
- [2026-09-15, standing] An in-driver assert is evidence about its sampler's
  support. Name the support and which variables of the claim it varies, and
  list the generator's fenced constants with `python3
  notes/scripts/blindaxes.py --imports --population`. ← BNONUNI; F13; F28.
- [2026-09-15, standing] Before attacking a statement, open what consumes it
  and confirm the exact form consumed. A reformulation that is the target at
  one end is not a reduction. ← F26 (five directions at an unconsumed
  residual); the vacuous existential forms in §(K-grid).
- [2026-09-15, standing] Retrieve claims with `python3 notes/ledger.py
  --label | --brief | --cited-by`; read the gap map with `notes/gapmap.py`,
  never `sed`/`grep`. ← D2: ~137k tokens on ~35 grep probes for 18 claims.

## Reproducibility

- [2026-08-05, standing] Every script that produced a figure, verdict or
  decision is committed, seeded, in exact arithmetic, with a command-line
  path that reproduces the landed figure. A throwaway probe is recorded as
  "attempted, no figure; script not retained". ← user directive 2026-08-05; F39.
- [2026-07-11, standing] Every foreground command carries an explicit
  timeout; a run that cannot finish inside it starts in the background first
  and is collected before the turn ends; never mask an exit status through
  `head`/`tail`. ← F6; F15.
- [2026-07-10, standing] Pin an agent's rung in its definition's frontmatter;
  a resume re-resolves the model from there, not from the spawn parameter.
  ← F5, three controlled spawn/resume probes.

## Attack track — `/attack <name>`, files under `notes/attacks/<name>/`

- [2026-09-15, trial] One agent owns one lemma. At start it reads
  `brief.md` and `state.md` and nothing else unless the state file points
  there. ← evaluation 2026-09-15: directions were 30–90-minute amnesiac
  bursts; six consecutive rounds spent ranks 1–3 and minted successors.
- [2026-09-15, trial] `state.md` is rewritten from
  `notes/attacks/TEMPLATE-state.md` at the end of every session, inside its
  section budgets; "where it breaks" is non-empty while the lemma is open.
  Overflow goes to `log.md` as one line per attempt stating what it rules
  out; an attempt that cannot say what it rules out gets no line.
  ← the phase note at 580/580 lines; gap-map rows grown by appending.
- [2026-09-15, trial] Two signal lines close `state.md`: sessions since
  "where it breaks" last changed, and the open-obligation count with its
  trend. Three unchanged sessions flag the route for review. ← the (K-grid)
  lead sentence byte-identical 2026-08-20 → 09-13, unread as a signal.
- [2026-09-15, trial] A session ends before automatic compaction, and no
  cache is kept warm across days. Continuity within a day is the
  conversation; across days it is `state.md`. ← cache arithmetic: resident
  context × turns dominates; a 300k transcript costs ~7× a 40k one per turn.
- [2026-09-15, trial] An attack writes only inside its own directory, its
  own workbook file and its own driver directory, minting labels only in its
  own prefix. Shared surfaces get a two-line pointer edited by the PI.
  ← RESEARCH-ARC §2 concurrent-read hazards; F17 stale headers.
- [2026-09-15, trial] Helpers (sweeps, literature reads, Lean checks) are
  spawned as subagents, return summaries, and write only to scratch. Sweeps
  are controls; the deliverable is a proof attempt. ← 27 of 27 recent
  directions used a CAS, 0 opened a reference PDF.
- [2026-09-15, trial] `/review-attack` runs every three sessions or on a
  flag. The agent proposes, the reviewer checks, the PI decides route
  changes; neither agent has the final call. ← routes declared spent on
  false premises and dead routes pushed, both observed in the arc.
- [2026-09-15, trial] Parallel attacks run one per worktree on their own
  branch, merged at milestones; the PI supervises at most three. ← review
  bandwidth is the bound that kept the corpus unread.

## Retired

The coordinator loop and its machinery — prediction/mechanism/tell,
label-range reservations, the six-surface status sweep, keepalive crons,
cross-return passes, per-landing docs gates — are retired with
`/coordinate-research` (archive: `notes/harness/archive/`, 2026-09-15).
`RESEARCH-ARC.md` and `notes/Harness-structure.md` stay in place under a
`RETIRED` banner as historical record; no command reads them. The Lean
loop `/coordinate-phase` is unchanged.
