Attack $ARGUMENTS. You own one lemma for as long as it takes; this session
is one working day on it. Rules: `HARNESS.md` (*Evidence*,
*Reproducibility*, *Attack track*). Files: `notes/attacks/$ARGUMENTS/`.

**Start.** Read `HARNESS.md`, then `notes/attacks/$ARGUMENTS/brief.md` and
`notes/attacks/$ARGUMENTS/state.md`. Read nothing else unless the state
file points you there; retrieve claims with `python3 notes/ledger.py
--label | --brief | --cited-by` and read the gap map only through
`notes/gapmap.py`. If `state.md` is absent this is session 1: choose a
route from the brief, enumerate its obligations, and write `state.md` from
`notes/attacks/TEMPLATE-state.md` before doing anything else.

**Work.** Attempt a proof of the brief's statement along the current
route. Drivers and sweeps are controls that test one step of the argument;
they are not the deliverable. You may read the reference PDFs (`REFS.md`)
and the Lean under `CombinatorialRigidity/Molecular/Molecule/Pencil/`.
Spawn helpers (`general-purpose` agents) for sweeps, literature reads or
Lean checks; give each one question, take back a summary, and let them
write only to scratch. A script that produced a figure follows
`HARNESS.md` *Reproducibility* and lives in `notes/attacks/$ARGUMENTS/drivers/`.
Mint labels only in the prefix the brief assigns.

**Write** only under `notes/attacks/$ARGUMENTS/` and in your own workbook
file. Never edit `HARNESS.md`, `.claude/`, `notes/Phase39.md`, `ROADMAP.md`
or the gap map; if one of them needs a pointer changed, say so in your
closing sentence and the PI does it.

**End the day before context runs long**, and always before stopping:
1. Rewrite `state.md` from the template — every section, inside its
   budget; "Where it breaks" specific enough to attack; the two signal
   lines updated.
2. Move retired attempts to `log.md`, one line each, stating what the
   attempt rules out; an attempt that rules out nothing gets no line.
3. `python3 notes/harness/check.py --state notes/attacks/$ARGUMENTS/state.md`.
4. Commit everything under your directory and your workbook file with the
   attribution rules in `CLAUDE.md` *Working* (author identity, `-F` for a
   message with backticks, no local paths).
5. One sentence to the PI: where the lemma stands, and whether a review is
   due (three sessions since the break moved, or a route change proposed).

If something in these instructions or in `HARNESS.md` cost you time, add
one line to `notes/harness/incidents.md`; do not fix the harness yourself.
