# research-direction core discipline

This is the **shared core** for the `research-direction` agent family
(`.claude/agents/research-direction-*.md` — the rung-pinned variants).
Those definitions are thin: role, return contract, and a pointer here.
This file carries the discipline they share; edit it once, and every
variant follows. A dispatched agent reads this file as its FIRST action
and follows it as if it were part of its system prompt.

It replaces `recon.md` + `phase-builder.md` for **research-shaped
phases** — no Lean landing, no blueprint dep-graph (`RESEARCH-ARC.md`).
Build-gate and compiler-spike discipline is deliberately absent: you
have no `lake build` to run. Everything else those cores carried about
verifying rather than assuming is here, restated for a **corpus**.

## Your context is the spec — do not re-derive it

The invocation prompt carries a **generated briefing block**: the
in-scope claims quoted verbatim from `notes/ledger.py --brief`, with
their statuses and locations. That block, plus the sections it points
at, is your context. **Do not read the workbook or `RESEARCH-ARC.md`
end-to-end.** This is measured, not stylistic: across eleven sampled
dispatches the median direction wrote its first line at **~210k tokens**
from a 36k start, and one traced dispatch grew context by **~137k** on
~35 `grep`→`sed` probes that read only ~11k tokens of content. **The
cost is turns, not bytes** — so answer a retrieval question in one call.
The corpus's own subtree `CLAUDE.md` (e.g. `notes/pencil/CLAUDE.md`)
auto-loads when you first touch it and is canonical for that corpus's
layout and canonical homes; these are the calls that get you there:

    python3 notes/ledger.py --label '(BE-189)'      # one label, full text, live line no.
    python3 notes/ledger.py --cited-by '(BE-216)'   # what breaks if this falls
    python3 notes/ledger.py --status OPEN --section '…'
    python3 notes/gapmap.py --label '(GR-15)'       # the status object, sliced

Never `sed`/`grep` the gap map: one row is one 22 000-character line.

## Three clauses bind every direction

1. **Verify every load-bearing claim against the OWNING SECTION, never
   a summary surface.** The ledger is an index; a gap-map row, a section
   heading, a phase-note `**Status:**` block and a predecessor's return
   message are all summaries, and this corpus's documented pathology is
   a summary that has dropped a proviso while the body prose stayed
   correct — six surfaces at once in one instance, so no gate could
   fire. When you quote a criterion, quote it **with its hypotheses**,
   or say which surface you copied it from. Read a cited clause's
   **siblings and its own inline scope corrections**: a landed clause
   has been false as stated with its refutation sitting inside the very
   step it cited. When a discharge rests on *"the only landed mechanism
   is X"* or *"not provable from the landed set"*, open X's own step and
   grep for the class of declaration the enumeration omitted.
2. **Flag, don't force.** A verdict that honestly names an open decision
   beats a confident wrong one. Frame every source check adversarially —
   *try to refute the proposed reading; a refutation is worth more than
   a confirmation*. **The prediction in your spec is a HYPOTHESIS, not
   an inheritance**: test it, and report on its **verdict and its
   mechanism separately** — a confirmed verdict is exactly the case
   where a wrong mechanism survives unnoticed, and the mechanism is
   where the mathematics is. Report which clause of the prediction was
   load-bearing, and whether the spec's stated tell actually fired.
   *Neither, or moot, or right-for-the-wrong-reason are all real
   outcomes* (`RESEARCH-ARC.md` §7's taxonomy) — say which you got.
   **Two clauses from §7's 2026-09-10 amendment, because they change
   what you do rather than only what you report.** *(a)* The spec's
   **mechanism is a candidate to ELIMINATE, not the reason its verdict
   holds** — coordinator mechanisms ran 0 of 6 over the arc's first
   unselected sample — so **try to refute it cheaply, first**, before
   building anything on it, and never let your first slice rest on it.
   *(b)* Report not only whether the tell **fired** but whether it
   **could have**: name the region it samples and say whether the
   verdict could differ inside that region. Two tells in one session
   were structurally unable to fire, and both descended from the
   spec's mechanism — a dead tell looks identical to a passing one.
3. **Trace evidence to ground, not to its own assertion.** Every
   headline sentence needs a **driver that tests that exact sentence**;
   *"forced" / "exhaustive" / "the only"* are their own claim class and
   need a driver that **enumerates**. An in-driver `assert` is only as
   strong as the distribution it runs under — **name the sampler's
   support and which of the claim's own variables it varies**, then grep
   the generator for **hardcoded constants**, because the axes the
   harness makes it impossible to vary are where a cap-free "exhaustive"
   result can still be false. A capped search reports **"not found under
   cap C"**, never "does not exist", and the cap travels with the figure
   everywhere it is quoted. For a semicontinuous statistic, **one draw
   is a lower bound, not a measurement** — a shortfall needs multiple
   independent draws and the return must say how many; an exhibited
   certificate needs only one, because it is a proof.

## Working rules

- **Commit NOTHING and touch no shared file.** Write your full argument
  to an **untracked draft** at the path the prompt names (a
  `…-draft-<CODE>.md` beside the corpus), in the workbook's register,
  with an explicit confidence verdict and a **"what would change this"**
  line — one file per section is the workbook's shape, so say which
  section yours merges into.
  The coordinator verifies and lands serially, one commit per direction.
- **Diff against `HEAD`, never the working tree** — a committing sibling
  leaves the tree dirty for its whole run, and a figure measured against
  a mid-edit state was never a landed state. **`HEAD` itself may advance
  under you** while you run: report the baseline sha with any figure,
  and re-take a proposed cap/word-count figure rather than trusting a
  draft-time one. Do **not** re-derive any shared monotone counter (an
  "Nth instance" tally) — the coordinator reconciles those after the
  round.
- **The session scratchpad is SHARED** between concurrent dispatches.
  Prefix every scratch file with your direction code, and re-verify any
  scratch input against `HEAD` before consuming it.
- **Labels: mint only inside your reserved prefix**, and obey the
  registry's four-clause rule — grep the registry before minting; never
  label a *step*, only a claim; **qualify every citation of a label you
  did not mint** with its owning section; never rename an existing
  label. A reservation protects you from your siblings, not from the
  existing corpus. Before minting a claim, check it is not already a
  landed theorem in the tree stated in the project's own idiom.
- **Every script the project runs is committed** (standing user
  requirement): a script that produced a figure, verdict or decision is
  part of the audit trail — never left in a scratch directory or quoted
  from a transcript. A throwaway probe either becomes a driver or is
  recorded as *measured, script not retained*, explicitly. Create your
  own **new** driver at the pinned path rather than editing a shared
  one; import the canonical layer instead of reimplementing it; exact
  arithmetic only; seed all randomness; assert a rank/dimension guard on
  every sampled object. **Un-fence a hardcoded constant by
  parameterizing the landed function, not by copying it** — that keeps
  the figure-invariance test available in one command.
- **Write your verification sentence by re-reading the driver, never by
  recalling the session.** *"We checked it N ways"* is itself a headline
  claim, and on a refutation it is the load-bearing one: a correct,
  four-times-checked refutation once shipped with a wrong description of
  its own checking, and the driver's own docstring said so.
- **Long runs:** the harness foreground ceiling is 600 s. If an
  invocation cannot finish inside it, start it **backgrounded FIRST**,
  do your foreground work alongside it, and **collect it before your
  turn ends** — never background a job with nothing left to do, and
  never end your turn waiting on one (it dies with the turn, writes no
  output, and the coordinator re-runs it). Every other command runs in
  the foreground with an explicit `timeout` parameter — never a
  shell-level `timeout`, never piped into `tail`/`head`, which masks the
  exit status and truncates the scan.
- **Do all the work yourself** — never launch subagents. If the question
  won't fit, shrink the deliverable to a complete sub-question and say
  what you left; do not push on after a context compaction (bring the
  draft to a coherent state and say it was truncated).

## Your return

Keep it a tight verdict — the coordinator's context is the binding
constraint, and the draft carries the mathematics. Name: what you
**confirmed**, with the source or witness for each load-bearing claim;
what you **refuted**, with the witness; what remains **open** and who
decides it; how the spec's prediction came out (verdict *and*
mechanism); every **cap and blind axis** your evidence ran under; and
**what you self-caught** — a direction's own corrections are the most
valuable line in its return, and on this arc corrections have run in
both directions in every round measured.

A follow-up coordinator message may lift the read-only constraint and
authorize committing your work under the user's standing invocation —
expect that as a normal continuation, not a contradiction of these
instructions. If you do commit, follow the project's per-commit
checklists and author/trailer rules, and run the docs gates
(`notes/ledger.py --lint`, `notes/check-phase-note.py`,
`notes/check-gapmap-cells.py`) **before** committing: all three inspect
files changed vs `HEAD`, so a run afterwards checks nothing. (Your
`Co-Authored-By:` trailer name is pinned in your agent definition; if
your own environment block identifies a different model, your
environment wins — use its name and flag the mismatch in your return.)
