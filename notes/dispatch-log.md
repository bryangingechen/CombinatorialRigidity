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
| 2026-07-11 | Phase32 tight-partition subfamily slice (`ed7f6274`) | sonnet | neither-return, coordinator-salvaged | Agent scoped down (3 lemmas → 1, legitimate scope-to-fit), completed the diff + notes, then ended its turn parked on its backgrounded full `lake build` ("no further polling") and never woke on the build's completion. Coordinator monitored HEAD 25 min, then salvaged per rescue §2: verified the diff against the hand-off, re-ran all gates (build/lint/blueprint), committed with both co-author trailers. Second instance of the parked-on-background-build shape (cf. Phase31 S3 row); salvage over resume since the work was complete and gate-ready. |
| 2026-07-11 | Phase32 tight-partition parts slice (`d87cc216`) | sonnet | neither-return, same-agent resume recovered | Third parked-on-background-build instance — despite an explicit foreground-gates prompt note. Diff complete but uncommitted; coordinator resumed same-agent (rung-pinned variant, no F5 drift) with finish-in-foreground instructions; agent re-ran all four gates blocking (explicit `timeout` set — the actual fix, see F6) and landed clean. Root cause identified: harness auto-backgrounds long Bash calls lacking an explicit `timeout`; mitigation folded into the phase-builder core same day. |
| 2026-07-11 | Phase32 chapter-open false node (`b7a09e95`; repaired `8750729e`) | fable | false red node caught by pre-build recon | The chapter-open's own inline "correction" of the accepted L1-recon 0-extension signature (unconditional `min(3,d)` rank form) over-generalized past JJ, whose argument carries an implicit clique-neighborhood hypothesis; refuted by K₁,₄. Rode red/unpinned through ~20 clean slices — no gate can catch a false red node — until the scheduled pre-build recon on the section refuted it and re-derived the corrected route (design pass `8750729e`). Lesson: a chapter-open's statement-level corrections are themselves transcription risk; the per-section pre-build recon is the only check that fires before Lean consumes the node. |
| 2026-07-16 | Phase32 S3 zero-extension deg-≤3 corollary (`4698ce4e`) | sonnet | neither-return via deliberate Monitor, same-agent resume recovered | 6th parked-on-background instance, but the first via a *deliberate* `run_in_background`+Monitor wait (tell: "wait for the Monitor notification"), not the harness auto-background the F6 timeout-mandate targets — so it recurred 5 days after that mitigation. Coordinator resumed same-agent (rung-pinned sonnet, no F5 drift) with finish-in-foreground instructions; agent finished gates foreground, landed clean. Mitigation extended: both cores now forbid `run_in_background`/Monitor on gates; the next dispatch (opus S4), pre-reminded in-prompt, ran clean. See F6. |
| 2026-07-16 | Phase32 L2 pre-build recon (`bd7565f9`) | fable | killed mid-dispatch (org spend limit), resumed same-agent | Second org-spend-limit kill (cf. 2026-07-10 Phase30 row); hit the recon mid-deliverable with its jacobs.tex + Phase32.md edits uncommitted, cut off right before the Decisions-made entry. On limit reset the coordinator resumed same-agent (SendMessage; rung-pinned fable, no F5 drift) naming the cut point and the intact tree; the agent completed the notes entry, re-ran both blueprint gates, landed clean with the full verdict. Resume-over-relaunch per rescue §3 worked unchanged for a recon-shaped dispatch; no doc gap. |
| 2026-07-16 | Phase32 T5 phase-close build (`0ce07da3`) | fable | killed mid-dispatch (org spend limit), resumed same-agent | Third org-spend-limit kill (cf. the L2-recon row above); hit the T5 builder just after its pre-write name checks, with only a 4-line docstring edit uncommitted. On limit reset the coordinator verified the tree state (git diff: docstring-only), then resumed same-agent (SendMessage; rung-pinned fable, no F5 drift) naming the intact tree; the agent completed T5 + the full phase-close pass and landed clean. Coordinator re-ran all gates incl. `#print axioms` — all green. Kill-early resumes are as clean as kill-late ones. |
| 2026-07-16 | Phase33 Slice 2 Extensor ℝ→K (`1d40880a`) | sonnet | neither-return via Monitor + build-contention swap spiral, same-agent resume recovered | 7th parked-on-background instance, despite the F6 core mitigation landing the same day — agent ended its turn "waiting for the Monitor's completion notification". New twist: timeout auto-backgrounding had spawned THREE concurrent full `lake build`s, driving swap to ~97%; on resume the agent SIGTERM'd two, let one finish, then re-ran all gates foreground and landed clean. Resume-over-salvage since the diff was complete but ungated. Concurrent-build contention is a new failure surface: F6's foreground mandate also prevents it (one build at a time). |
| 2026-07-16 | Phase33 Slice 4 ScrewSpace pivot (`52232967`; repaired `0cda3b7b`) | opus | gate-invisible restate miss, caught by next slice's grep | The pivot generalized a Basic decl but restated only the slice's named chapter (`rigidity-matrix.tex`); a Basic-backed node in `case-iii.tex` kept the `\R` statement. No gate fails on a stale-but-name-valid node (checkdecls only resolves `\lean{}` names). Caught by Slice 5's per-slice statement-restate grep, which correctly greps by DECL, not by chapter; coordinator follow-up restated the line. Lesson: a slice's "expected chapter" hint is a floor, not the restate scope — the grep must sweep all of `blueprint/src/` for every touched decl. |
| 2026-07-17 | Phase34 abundance lemma (`c89eea77`) | sonnet | F6 recurrence (8th) — concurrent builds despite the in-prompt reminder; self-flagged, landed clean | First gate `lake build` lacked the mandated explicit `timeout` → auto-backgrounded; agent then fired a second explicit-timeout build without waiting, ending at three concurrent full builds (all exit 0, no corruption). Unlike instances 1–7 it did NOT park: it recovered inline, finished gates foreground, landed, and self-flagged the deviation in its return. The in-prompt F6 line reduces but does not eliminate the shape at sonnet. Also a cost outlier (~287k tok, 84 tool uses, ~40 min) — judged legitimate: the slice grew a new mirror helper (`…linearIndependent_at_reindex`) + eval bridge; diff read clean, no bloat, all gates re-run by coordinator. |
| 2026-07-17 | Phase34 packing corollary (`0a8a9efc`; prose fixed `2061c6d6`) | sonnet | gate-invisible prose defect caught in coordinator diff-read | The rewritten blueprint sketch's degree step said "every vertex of 5·G has degree ≥ 2, hence every vertex of G" — a false inference as written (÷5 gives only ≥ 1); the Lean is correct (the 0-dof degree lemma concludes on the unmultiplied shadow). No gate reads sketch prose; caught only by the full-diff read against the landed lemma's actual conclusion. Coordinator reworded (`2061c6d6`). Second consecutive cost outlier (~370k tok, 175 tool uses) — judged legitimate-heavy: the slice picked the packing-hypothesis Lean shape and verified two flagged proof steps; diff clean, no bloat, route deviation (min-degree from def=0 via KT 4.6) sound and recorded. |

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
- **F6 — harness auto-backgrounding strands gate runs.** A Bash call
  with no explicit `timeout` parameter gets AUTO-BACKGROUNDED by the
  harness when it runs long ("Command running in background with ID
  …"); the agent then ends its turn to "wait", and the completion
  notification cannot wake a subagent whose turn ended — the finished
  diff strands uncommitted. Four sonnet dispatches in one session
  (2026-07-11) failed this exact way, two of them *after* explicit
  foreground-gates prompt notes (the notes said "foreground" but not
  *how*). Root cause is the missing `timeout`, not agent
  disobedience: an explicit `timeout: 600000` keeps the call blocking
  (verified on two resumes). *Mitigation implemented 2026-07-11:* the
  `phase-builder` core's foreground-gates clause now mandates the
  explicit timeout and names the auto-background message as the tell
  (mirrored into the recon core's design-pass clause and rescue §2,
  2026-07-11).
  Recovery path when it still happens: same-agent SendMessage resume
  with finish-in-foreground instructions (2/2 clean), or
  coordinator-salvage per rescue §2 when the agent never wakes.
  *Recurrence 2026-07-16 (sonnet S3, `4698ce4e`):* a 6th instance, but
  via a **different path** the timeout-mandate did not cover — the agent
  *deliberately* backgrounded its gate (`run_in_background`) and set a
  **Monitor** to wait on it, then ended its turn (tell: "wait for the
  Monitor notification"). The missing-`timeout` mitigation only blocks
  the *auto*-background path; a deliberate background+Monitor strands
  identically. *Mitigation extended 2026-07-16:* the phase-builder and
  recon cores now also explicitly forbid `run_in_background`/Monitor on
  gate builds (not just mandate the timeout). Same-agent resume clean
  again (3/3); the next dispatch (opus S4), pre-reminded in its prompt,
  ran its gates foreground with no pause — so a one-line explicit-timeout
  /no-Monitor reminder in the build prompt is a cheap coordinator-side
  backstop worth adding when the prior slice hit F6.
  *Recurrence + promotion 2026-07-17 (Phase 33):* a 7th instance
  (Slice 2, with a new twist — timeout auto-backgrounding spawned three
  concurrent full builds, swap ~97%). The coordinator then carried the
  one-line reminder in every subsequent build prompt; all 14 later
  Phase-33 dispatches ran gates foreground (two still auto-backgrounded
  a >10-min full build mid-run and recovered inline without stranding).
  **Promoted to the coordinator command** (step-3 invocation-prompt
  bullet, 2026-07-17): every build dispatch now carries the F6 line.
