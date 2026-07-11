# Dispatch log — exceptions only

Coordinator-owned record for `/coordinate-phase` sessions. **Routine
clean dispatches are NOT logged** — git history is the record. Log a
row only for an **exception**:

- an **escalation** (BLOCKED return or failed verification →
  re-dispatched one rung up) — log both halves' cost;
- a deliberate **probe** below the mapped rung, and its outcome;
- a **BLOCKED / killed / salvaged** dispatch (what stranded, what was
  recovered, resume-vs-relaunch);
- a **gate-invisible defect caught in verification** (shape
  deviation, additive-repin miss, deletion-hygiene miss, faithfulness
  defect, unsatisfiable deferred hypothesis) — the catch *and* which
  check caught it;
- a **playbook deviation** (rung substitution beyond the session
  config, an off-map rung choice) and its outcome.

Provenance: this replaces the per-dispatch model-tier experiment log
(concluded 2026-07-09 across CombinatorialRigidity + enharmonic, ~890
rows; the frozen log is `notes/model-experiment-archive.md`, findings
promoted into the coordinator command's *Dispatch playbook*). The
experiment's own history showed per-dispatch logging re-bloats — rows
recapping math the commit message already carries — so the schema below
keeps only what git cannot show.

## Row discipline

- **Notes ≤ ~600 chars** — the exception's cause and lesson, never a
  recap of the mathematics (the commit message is the recap). If a
  sentence restates what the *commit* did rather than how the
  *dispatch* went wrong, cut it. This is the same ~600-char cap the
  concluded experiment enforced with `notes/check-log-rows.py`; that
  script is still in the tree (pointed at the archived
  `model-experiment.md`) and can be adapted to audit this log's Notes
  cells — retarget its `PATH` to `notes/dispatch-log.md` and adjust the
  column count for this file's 5-column schema. Gate on its exit code
  with an `if`-guard, never a pipe or `;`-chain.
- **Append by matching the previous row's tail only** — an edit span
  that includes the following section header silently deletes that
  header (this clobbered a log's Findings heading three times in one
  ancestor session).
- Write the row only after the verification pass completes in full;
  correct a committed row by a follow-up edit, not a
  history-rewriting amend.

## Log

| Date | Task (short + sha) | Rung | Exception | Notes |
|---|---|---|---|---|
| 2026-07-09 | Phase29 W2 slice-plan recon (`30b8af27`) | opus | recon-estimate defect caught downstream | The recon's anchor inventory ("5 live-Lean anchors, section granularity") was right for §0–§1.49 of `Phase22-realization-design.md` but badly undercounted §1.50+ (letter-granularity citations from ~15 Lean files). Caught by the per-slice re-derivation the dispatch prompts mandated, before any anchor broke; the builder corrected the plan-of-record in place. See Findings F1. |
| 2026-07-09 | Phase29 W2-7 compression slices (`1ed2ff41`, `ca60cfdf`, `f38a7ac2`) | sonnet | plan-label deviation ×3, honest partial returns | Pre-planned W2-7a/b boundary mismatched the file's real density (96% of bulk in §1.34+); each slice re-drew its boundary at build time, returned honestly partial, and advanced the hand-off. Outcome good ×3 — scope-to-fit working as designed; no escalation needed. |
| 2026-07-10 | Phase30 slice (c) conjunct deletion (`462d73ec`) | opus | killed mid-dispatch (org spend limit), resumed same-agent | External API kill (org monthly spend limit) landed mid-slice with the atomic def change uncommitted across 9 Lean files + 1 tex. On limit reset the coordinator resumed the same agent (SendMessage) with a re-orient-from-`git diff` instruction and an explicit revert-if-incoherent escape; the agent found the Lean repairs complete and pre-kill gate-verified, finished the blueprint prose sweep, re-ran ALL gates post-resume, landed clean. Kill cause external, not task-shaped; no escalation. See F4. |
| 2026-07-10 | Phase31 S3 staleness repair (`170fddbd`) | sonnet→fable | neither-return + model drift on resume | The sonnet dispatch ended its turn mid-slice ("standing by" for its own backgrounded `lake build`) instead of waiting — a neither-LANDED-nor-BLOCKED return with the diff uncommitted. Coordinator resumed same-agent (SendMessage); the resume ran at the *session* model (fable), not the dispatched rung — the agent caught it and set the trailer to Fable 5 per CLAUDE.md. Landed clean; all gates re-run by coordinator. Upward drift is safe, but see F5. |

## Findings

(Distill recurring lessons here — one entry per lesson, rows cite it.
At phase close, promote stable entries into the coordinator command's
*Dispatch playbook* / CLAUDE.md and prune.)

- **F1 — re-derive inventories at build time.** A recon's size/anchor
  estimate made before reading a file is a scheduling input, not a
  per-slice contract; mandating that each slice re-derive its own
  inventory (tree-wide grep, letter granularity) is what caught the
  Phase-29 undercount before anything broke. Flagged in
  `notes/Phase29.md` for promotion to `notes/CLAUDE.md` if a third
  `*-design.md` compression hits the same trap.
- **F2 — pinned exemplar = the prose S=1.** A verbatim user-approved
  exemplar section plus verbatim `adjudication` shaping blocks let
  sonnet run 6/6 Phase-29 episode-writing slices clean. Promoted to the
  playbook (*Raising S* + the shaping-block list) 2026-07-09.
- **F3 — verification-mandate cost signature.** All six Phase-29 prose
  slices were 250–330k-token outliers AND clean; the cost was the
  mandated per-fact git re-verification + PDF render inspection (which
  also caught two real `alltt` rendering bugs no gate reads). Promoted
  to the playbook (the cost-outlier bullet's benign-shape carve-out)
  2026-07-09.
- **F4 — continuation dispatch (same-arc resume).** Resuming the prior
  dispatch's agent via SendMessage for the next slice of the same arc
  (recon → record-its-verdict commit → next recon; builder template →
  its mirrors → the dependent deletion slice) ran 7/7 clean across
  Phase 30's two arcs with no re-orientation cost, and doubled as the
  recovery path for the externally-killed slice-(c) dispatch. The
  verification tier is unchanged — each returned commit is verified in
  full before the next continuation message. Promoted to the playbook
  (step-3 *Continuation dispatch* note) 2026-07-10.
- **F5 — SendMessage-resume runs at the session model, not the
  dispatched rung.** A same-agent resume (F4's mechanism) does not
  carry the original Agent-tool `model` parameter: the Phase31-S3
  resume promoted a sonnet dispatch to fable mid-slice. Upward drift is
  harmless (and the agent's trailer self-check caught it), but the
  symmetric case demotes: a coordinator session running at a rung
  *below* the mapped one would silently continue an opus/fable dispatch
  at the weaker rung. Before any resume, check the session model is
  at-or-above the task's mapped rung; if not, relaunch fresh at the
  mapped rung instead of resuming.
  *Verified by controlled probes (2026-07-10, three spawn/resume
  pairs):* SendMessage resume re-renders the system prompt and
  **re-resolves the model from the agent definition's `model`
  frontmatter, else the session default — the Agent-tool `model`
  parameter is spawn-only and dropped on resume.** Matrix: (A) no
  frontmatter + param `sonnet` → spawn sonnet, resume **fable**
  (session); (B) frontmatter `sonnet` + no param → spawn sonnet, resume
  **sonnet**; (C) frontmatter `sonnet` + param `opus` → spawn opus[1m],
  resume **sonnet** (falls to frontmatter, not param, not session).
  So **frontmatter pinning makes resumes rung-stable** (and keeps the
  transcript prefix prompt-cache-valid, since the re-rendered system
  prompt is identical when resolution lands on the same model) — the
  mitigation if same-rung resume matters: per-rung definition variants
  (e.g. `phase-builder-sonnet.md`). *Mitigation implemented
  2026-07-10:* rung-pinned variants `phase-builder-{sonnet,opus,fable}`
  / `recon-{opus,fable}` as thin shells over shared cores in
  `.claude/agents-core/` (@-imports are CLAUDE.md-only — confirmed by
  docs AND an empirical probe that saw the literal unexpanded `@…`
  line — so the shells instruct a first-action Read of the core); the
  coordinator command's step 2/3 + playbook now dispatch rungs by
  type, base types retained for off-map param dispatches.
  *Acceptance-tested on the shipped definitions:*
  `phase-builder-sonnet` read `claude-sonnet-5` at spawn AND after a
  SendMessage resume inside a fable session. Caveats: definitions are snapshotted
  per session (an edit to an existing definition did not apply to a
  spawn seconds later; a NEW definition file did register after a few
  minutes); the [1m] suffix seen at param-spawn may not survive
  frontmatter re-resolution. Not covered by official docs — the
  resolution hierarchy is documented for *spawn* only; adjacent
  re-resolution bugs upstream (anthropics/claude-code #34421, #45169,
  #31069). Two corollaries: a resumed agent cannot self-detect the
  drift from its transcript (both probes blamed their own earlier
  "misreport"), and the trailer self-check catches it only when the
  invocation prompt names the dispatched model — keep naming it.
