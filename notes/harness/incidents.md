# Harness incidents — one line each, append-only

Format: `YYYY-MM-DD | where | what happened | cost | candidate rule or "none"`.
Write the line when it happens; do not write an essay and do not edit
`HARNESS.md` in the same session. `/harness-review` reads everything since
the last `## review` line and decides which candidates become trial rules.

2026-09-10 | coordinate-research session | the coordinator edited the harness inside the session it was running; RESEARCH-ARC.md grew 957 → 1 137 lines in the session whose diagnosis set a sub-500 target | 19% growth of the manual in one session | research sessions do not edit the harness (adopted as governance, HARNESS.md header)
2026-09-13 | coordinate-research session | ~90 min idle at the session tail with only keepalive crons firing, no direction running | ~90 min wall, cache reads at 0.1× on a ~200k prefix | none (loop retired)
2026-09-15 | evaluation | `.claude/scripts/session-usage.py tokens` reads usage from the first block of each request; subagent usage is cumulative across blocks, so it undercounts subagent output ~4.4× (GBASE: 74 857 reported vs 217 308 actual) | cost figures in Harness-structure D7 understate the subagent share | fix: take the max across a request id's blocks (as notes/harness/instrument/analyze.py does)
2026-09-15 | evaluation | 13 of the 20 costliest coordinator rules rested on a single incident or session, against the manual's own three-wave promotion bar; ~158 imperatives in force, 22 of 25 sampled phrases duplicated across ≥ 2 files | ~55% of coordinator tool calls were process | trial/standing tags with expiry and a line budget (HARNESS.md header)
