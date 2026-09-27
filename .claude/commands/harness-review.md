Harness review. Runs in its own session with the PI, never inside research
or attack work. Its job is to keep `HARNESS.md` small and true.

**Inputs.**
- `HARNESS.md`, and `python3 notes/harness/check.py` (budget, tags, the last
  review's date, and each trial rule's age in research sessions).
- `notes/harness/incidents.md` since the last `## review` line.
- `git log --since=<last review> -- HARNESS.md .claude/commands/{attack,review-attack,harness-review}.md .claude/agents/attack-*.md`
  — any edit made outside a harness-review session is itself an incident;
  log it. (`/coordinate-phase` and its agents change by their own
  phase-close promotions.)
- The instrumentation over the research sessions since the last review:
  the attack track, plus free-form sessions and other sessions' subagents
  that write under `notes/pencil/` or `notes/attacks/` (`--select research`).
  `python3 notes/harness/instrument/sessions.py --since-review` lists them
  with the logs root it read (`--logs-root` or `CLAUDE_LOGS_ROOT` override
  it); then
  `python3 notes/harness/instrument/analyze.py $(python3 notes/harness/instrument/sessions.py --since-review --select research --ids) > all.json`
  and `python3 notes/harness/instrument/report.py --attack all.json` — one
  row per session: process against mathematics, thinking share, compactions,
  peak context, PDFs opened, Lean read, helpers and their fate, cost at
  per-model rates.
- The status of the crux statements at the head of each attack's `state.md`,
  and their history:
  `python3 notes/harness/check.py --state notes/attacks/<name>/state.md --history`
  prints, per commit, the obligation count and whether "Where it breaks"
  changed — a break that moves every session over a flat count is a rename
  treadmill, not progress.

**Defaults, applied in this order.**
1. A `trial` rule past three research sessions is deleted unless a second,
   independent incident supports it; then it becomes `standing`.
2. A `standing` rule no incident has touched in three months is proposed
   for deletion.
3. A rule stated in two files is deduplicated to one home.
4. An incident's candidate rule enters as `trial` only if the file has room
   or something is removed to make room; the budget is not raised.
5. Every change is a diff the PI accepts; nothing lands without them.

**Report in one page:** whether each crux statement moved; the share of
turns that were process against mathematics; the line count of binding
text; rules added and removed, each with its incident. Then append a
`## review YYYY-MM-DD` line to `incidents.md`, so the next review knows
where to start. If the numbers say the binding text grew while the target
sat still, the review's output is a cut, not a section.
