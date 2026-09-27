# notes/attacks/ — one directory per lemma under attack

Layout for `notes/attacks/<name>/`:

| file | discipline | reader |
|---|---|---|
| `brief.md` | the one-page problem statement in plain mathematics, label-free in the body; its statement section transcribes the consuming declaration's hypotheses one per line, both sides, cited by declaration name (a line number only with the HEAD sha it was read at); rewritten only at milestones | the attack at start, the reviewer, the PI |
| `state.md` | rewritten from `TEMPLATE-state.md` every session (`HARNESS.md` *Attack track*) | the attack at start, the reviewer, the PI |
| `log.md` | append-only; one line per retired attempt: date, route, what was tried, why it failed, what it rules out, commit | the reviewer, when checking for premature kills |
| `drivers/` | the attack's scripts (`HARNESS.md` *Reproducibility*) | whoever re-runs a figure |

Rules are `HARNESS.md` *Attack track*; the session ritual is
`.claude/commands/attack.md`; the milestone review is
`.claude/commands/review-attack.md`. Proved lemmas with full statements go to
the attack's own workbook file under `notes/pencil/workbook/`, which is the one
place appending is right. Parallel attacks run one worktree each (`attack.md`
*Start*), merged at milestones.

Briefs marked **DRAFT** were written by an agent from owning sections and
await the PI's reading before an attack starts on them.
