Harness review. Runs in its own session with the PI, never inside research
or attack work. Its job is to keep `HARNESS.md` small and true.

**Inputs.**
- `HARNESS.md`, and `python3 notes/harness/check.py` (budget, tags, trial age).
- `notes/harness/incidents.md` since the last `## review` line.
- `git log --since=<last review> -- HARNESS.md .claude/` — any edit made
  outside a harness-review session is itself an incident; log it.
- The instrumentation over the attack sessions since the last review:
  `python3 notes/harness/instrument/analyze.py <session-id> … > all.json`
  then `python3 notes/harness/instrument/report.py all.json`
  (`--logs-root` or `CLAUDE_LOGS_ROOT` if the transcripts are not under the
  default config dir).
- The status of the crux statements at the head of each attack's `state.md`.

**Defaults, applied in this order.**
1. A `trial` rule past three attack sessions is deleted unless a second,
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
