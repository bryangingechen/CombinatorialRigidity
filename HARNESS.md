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
backticks, no local paths — are `CLAUDE.md`'s; the attack ritual is
`.claude/commands/attack.md` and `review-attack.md`, the state file's
sections and budgets `notes/attacks/TEMPLATE-state.md`. None is repeated here.

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
- [2026-09-15, standing] Before attacking a statement, open the declaration
  that consumes it and diff the brief against it hypothesis by hypothesis,
  both sides of the implication, following its definitions wherever they
  live — then diff the brief's case decomposition against the domain those
  hypotheses admit: every case is in the sketch or is an obligation. This
  binds the brief's author, the attack at session 1 and the reviewer first.
  A reformulation that is the target at one end is not a reduction. ← F26;
  §(K-grid); smark's brief paraphrased the consumer three times (a dropped
  disjunct, sessions 1–2; the antecedent read as `G − x`, sessions 1–4,
  surviving review 1; case (ii) sent to a cut-vertex arm the Lean does not
  have, surviving reviews 1–2 and a CHECKED pass — review 3).
- [2026-09-15, standing] Retrieve claims with `python3 notes/ledger.py
  --label | --brief | --cited-by`; read the gap map with `notes/gapmap.py`,
  never `sed`/`grep`. ← D2: ~137k tokens on ~35 grep probes for 18 claims.
- [2026-09-17, trial] A measured nonzero gets its witness — which vector,
  which motion — exhibited before any mechanism for it is written. ← smark
  s3's mechanism for `c′(Π_w) = 1`; s4's witness was an ear hinge; withdrawn.
- [2026-09-17, trial] Cite Lean and the blueprint by declaration name or
  `\label`; a line number travels only with the HEAD sha it was read at.
  ← both briefs' `file:line` pointers drifted in two days (check 2026-09-17).

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

- [2026-09-17, standing] `state.md` is the lemma's only status surface,
  rewritten from the template every session inside its budgets. Every open
  obligation names the consumer hypothesis that makes it necessary; every
  target hypothesis the route does not use gets a one-line reason. The
  obligation count is the progress signal — a renamed obligation is not a
  moved break — and three flat sessions flag the route for review.
  ← the phase note at 580/580 lines; smark sessions 1–4: O4 → O4′ → O4″ reset
  the "changed" line each session while the count sat at 3, and (O4′), (O4″)
  were consumed by nothing.
- [2026-09-17, standing] An attack writes only inside its own directory and
  its workbook file, where results are numbered (S1, S2, …) and cited by
  number; it mints no corpus labels. Shared surfaces get a two-line pointer
  edited by the PI. ← RESEARCH-ARC §2; F17; smark s1 spent ~10 min on a
  labels rule it could not satisfy, then numbered; 5 of 5 sessions in scope.
- [2026-09-17, standing] `/review-attack` runs every three sessions or when a
  route change is proposed. The attack proposes, the reviewer checks, the PI
  alone decides route and brief changes. ← routes declared spent on false
  premises in the arc; smark reviews 1 and 2 (after sessions 2 and 5) each
  re-aimed the brief only on the PI's word.
- [2026-09-23, trial] A derivation that is not in a file does not exist:
  before a case analysis of more than three branches, and first thing on a
  resume after an output-cap cut, write what is established so far to a
  scratch file with a tool call, then reason on. ← smark s7: twelve
  consecutive thinking turns cut at the output cap (73k–160k characters
  each, no tool call between them), ~4.1h, ≈$66, nothing committed; s6 was
  cut twice and the recovery session once more; `report.py --attack`'s
  `cap` column counts these.

## Retired

The coordinator loop and its machinery are retired with
`/coordinate-research` (archive: `notes/harness/archive/`, 2026-09-15);
`RESEARCH-ARC.md` and `notes/Harness-structure.md` stay under a `RETIRED`
banner as history, read by no command. `/coordinate-phase` is unchanged.
