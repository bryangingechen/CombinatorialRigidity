Attack $ARGUMENTS. You own one lemma for as long as it takes; this session
is one working day on it. Rules: `HARNESS.md` (*Evidence*,
*Reproducibility*, *Attack track*). Files: `notes/attacks/$ARGUMENTS/`.

**Start.** Work in the attack's own worktree on branch `attack-$ARGUMENTS`
(`git worktree list`; if none exists, `git worktree add` one from `HEAD`),
never in the main checkout, where another attack may be running.
Read `HARNESS.md`, then `notes/attacks/$ARGUMENTS/brief.md` and
`notes/attacks/$ARGUMENTS/state.md`. Then run the consumer diff of
`HARNESS.md` *Evidence* on the brief, in the Lean; a mismatch is reported
to the PI before any route work. Read nothing else unless the state file
points you there. If `state.md` is absent this is session 1: choose a route
from the brief, enumerate its obligations — each with the consumer
hypothesis that makes it necessary — and write `state.md` from
`notes/attacks/TEMPLATE-state.md` before doing anything else.

**Work.** Attempt a proof of the brief's statement along the current
route. Drivers and sweeps are controls that test one step of the argument;
they are not the deliverable. You may read the reference PDFs (`REFS.md`)
and the Lean of the consuming declaration and every definition it names,
wherever it lives.
Spawn helpers (`general-purpose` agents) for sweeps, literature reads or
Lean checks; give each one question, take back a summary, and let them
write only to scratch. A script that produced a figure follows
`HARNESS.md` *Reproducibility* and lives in `notes/attacks/$ARGUMENTS/drivers/`.

**Write** only under `notes/attacks/$ARGUMENTS/` and in your own workbook
file (`HARNESS.md` *Attack track*); a pointer anywhere else that needs
changing goes in your closing sentence, and the PI changes it.

**End the day before context runs long**, and always before stopping:
1. Rewrite `state.md` from the template — every section, inside its
   budget; "Where it breaks" specific enough to attack; each open
   obligation with its "consumed because"; the two signal lines updated
   (renaming an obligation does not reset the first).
2. Move retired attempts to `log.md`, one line each, stating what the
   attempt rules out; an attempt that rules out nothing gets no line.
3. `python3 notes/harness/check.py --state notes/attacks/$ARGUMENTS/state.md`.
4. Commit everything under your directory and your workbook file with the
   attribution rules in `CLAUDE.md` *Working* (author identity, `-F` for a
   message with backticks, no local paths).
5. One sentence to the PI: where the lemma stands, and whether a review is
   due by `HARNESS.md` *Attack track*.

If something in these instructions or in `HARNESS.md` cost you time, add
one line to `notes/harness/incidents.md`; do not fix the harness yourself.
